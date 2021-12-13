module Main

import Compiler.Common

import Core.Case.CaseTree
import Core.Context
import Core.Context.Context
import Core.Context.Log
import Core.Core
import Core.Directory
import Core.Env
import Core.FC
import Core.InitPrimitives
import Core.Metadata
import Core.Name
import Core.Normalise
import Core.TT
import Core.UnifyState
import Core.Value

import Data.List
import Data.Nat
import Data.SnocList
import Data.String

import Idris.Desugar
import Idris.Doc.String
import Idris.Env
import Idris.Error
import Idris.IDEMode.Holes
import Idris.Parser
import Idris.Pretty
import Idris.ProcessIdr
import Idris.REPL
import Idris.REPL.Opts
import Idris.Resugar
import Idris.SetOptions
import Idris.Syntax

import Parser.Rule.Source
import Parser.Source

import TTImp.Elab
import TTImp.Elab.Check
import TTImp.PartialEval
import TTImp.TTImp
import TTImp.Unelab

import Libraries.Text.PrettyPrint.Prettyprinter.Util

import System
import System.File

import Util

%default covering

die : String -> IO ()
die msg =
  do putStrLn msg
     exitFailure

ambiguousName : List (Name, Int, GlobalDef) -> Core ()
ambiguousName xs = throw $ AmbiguousName EmptyFC (fst <$> xs)

record TermWithType where
  constructor WithType
  termOf : Term []
  typeOf : Term []

getItDecls :
    {auto o : Ref ROpts REPLOpts} ->
    Core (List ImpDecl)
getItDecls
    = do opts <- get ROpts
         case evalResultName opts of
            Nothing => pure []
            Just n =>
              let it = UN $ Basic "it" in
              pure [ IClaim replFC top Private [] (MkImpTy replFC EmptyFC it (Implicit replFC False))
                  , IDef replFC it [PatClause replFC (IVar replFC it) (IVar replFC n)]]

||| Produce the elaboration of a PTerm, along with its inferred type
inferAndElab : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto m : Ref MD Metadata} ->
               {auto o : Ref ROpts REPLOpts} ->
               ElabMode ->
               PTerm ->
               Core TermWithType
inferAndElab emode itm
  = do ttimp <- desugar AnyExpr [] itm
       let ttimpWithIt = ILocal replFC !getItDecls ttimp
       inidx <- resolveName (UN $ Basic "[input]")
       -- a TMP HACK to prioritise list syntax for List: hide
       -- foreign argument lists. TODO: once the new FFI is fully
       -- up and running we won't need this. Also, if we add
       -- 'with' disambiguation we can use that instead.
       catch (do hide replFC (NS primIONS (UN $ Basic "::"))
                 hide replFC (NS primIONS (UN $ Basic "Nil")))
             (\err => pure ())
       (tm , gty) <- elabTerm inidx emode [] (MkNested [])
                   [] ttimpWithIt Nothing
       ty <- getTerm gty
       pure (tm `WithType` ty)

covering
evalOneStep : {auto c : Ref Ctxt Defs} -> {vars : _} -> Defs -> Env Term vars -> Term vars -> Core (Term vars)
evalOneStep = normaliseOpts ({ fuel := Just 1, strategy := CBV } withAll)

Interpolation Nat where
  interpolate k = show k

||| Evaluate for the given number of steps returning the intermediate
||| results.
||| Stops early if a term becomes neutral or normal.
||| Returns each step as a resugared term and the final result as a term.
covering
evalN : {auto c : Ref Ctxt Defs} ->
        {auto u : Ref UST UState} ->
        {auto s : Ref Syn SyntaxInfo} ->
        {auto m : Ref MD Metadata} ->
        {auto o : Ref ROpts REPLOpts} ->
        {vars : _} ->
        Fuel ->
        (acc : SnocList IPTerm) ->
        Env Term vars ->
        Term vars ->
        Core (List IPTerm, Term vars)
evalN Dry acc env tm = pure (cast acc, tm)
evalN (More fuel) acc env tm =
  do defs <- get Ctxt
     tm'' <- evalOneStep defs env tm
     if tm == tm''
        then pure (cast acc, tm)
        else do fullTm'' <- resugar env =<< toFullNames tm''
                evalN fuel (acc :< fullTm'') env tm''

||| Take a list of evaluation steps and document them line by line
||| with index numbers prefixed to them and the given indentation.
docSteps : (indent : Nat) -> List IPTerm -> Doc IdrisAnn
docSteps indent [] = emptyDoc
docSteps indent (x :: xs) = snd $ foldl1By docStep (document 1) (x ::: xs)
  where
    document : Nat -> IPTerm -> (Nat, Doc IdrisAnn)
    document k tm =
      let prfx = pretty $ padLeft indent ' ' "\{k}: " 
      in  (k, prfx <+> (Syntax <$> prettyTerm tm))

    docStep : (Nat, Doc IdrisAnn) -> IPTerm -> (Nat, Doc IdrisAnn)
    docStep (idx, doc) tm =
      let step = document (S idx) tm
      in  mapSnd (doc <+> hardline <+>) step

-- TODO: probably could be a nice traditional view of Term
-- allowing with pattern matching below to turn tm in an App.
||| get the next fn application and its args as a tuple or else Nothing.
digFnArgs : {vars : _} -> (depth : Nat) -> Term vars -> Maybe (NonZero depth, FC, Term vars, Term vars)
digFnArgs 0 _ = Nothing
digFnArgs d@(S k) (App fc fn arg) = Just (SIsNonZero, fc, fn, arg)
-- digFnArgs (Bind fc x b scope) = ?h_3
digFnArgs _ _ = Nothing

prettyTmTy : {auto c : Ref Ctxt Defs} ->
         {auto s : Ref Syn SyntaxInfo} ->
         {vars : _} ->
         Env Term vars ->
         Term vars ->
         (type : Maybe (Term vars)) ->
         Core (Doc IdrisAnn)
prettyTmTy env tm type =
  do fullTm <- resugar env =<< toFullNames tm
     maybeFullTy <- traverseOpt (resugar env <=< toFullNames) type
     let fullTy = maybe emptyDoc ((pretty ":" <++>) . prettyTerm) maybeFullTy
     pure $ Syntax <$> prettyTerm fullTm <++> fullTy

startAndEnd : FC -> (Int, Int)
startAndEnd = maybe (0,0) (bimap startCol endCol . dup) . isNonEmptyFC

evalSubexpressions : {auto c : Ref Ctxt Defs} ->
                     {auto u : Ref UST UState} ->
                     {auto s : Ref Syn SyntaxInfo} ->
                     {auto m : Ref MD Metadata} ->
                     {auto o : Ref ROpts REPLOpts} ->
                     {vars : _} ->
                     Fuel ->
                     (top : Bool) ->
                     (depth : Nat) ->
                     Env Term vars ->
                     Term vars ->
                     Core (Nat, Term vars)
evalSubexpressions Dry _ _ _ tm = pure (0, tm)
evalSubexpressions (More fuel) top depth env tm with (digFnArgs depth tm)
  evalSubexpressions (More fuel) top (S k) env tm | (Just (SIsNonZero, fc, fn, arg)) =
    do (n, arg') <- evalSubexpressions fuel top k env arg
       -- TODO: update the FC to account for a shorter drop in replacement
       --       (arg' where arg used to be).
       let (start, _) = startAndEnd fc
       prettyTm <- prettyTmTy env (App fc fn arg') Nothing
       iputStrLn . indent start . fileCtxt $ pretty "~~~~"
       iputStrLn . indent start $ prettyTm
       mapFst (n +) <$> evalSubexpressions fuel False 0 env (App fc fn arg')
  evalSubexpressions (More fuel) top _ env tm | _ =
    do (intermediates, final) <- evalN fuel [<] env tm
       let (start, end) = mapHom cast $ startAndEnd (getLoc tm)
       when top $ do
         coreLift . putStrLn $ (String.replicate start ' ') ++ (String.replicate (end `minus` start) '^')
       iputStrLn $ docSteps start intermediates
       pure (length intermediates, final)

-- 1. dig
--   if Nothing, regular eval loop.
--   else, eval on args and plop in place.
-- 2. ?

trace : (entryFile : String) -> (depth : Nat) -> PTerm -> Core ()
trace entryFile depth pterm =
  do _ <- setupCore entryFile
     (tm `WithType` ty) <- inferAndElab InExpr pterm

     iputStrLn =<< prettyTmTy [] tm (Just ty)

     (n, final) <- evalSubexpressions (limit 30) True depth [] tm
     pure ()

parsePTerm : String -> Either Error (List Warning, State, PTerm)
parsePTerm term = runParser (Virtual Interactive) Nothing term (expr plhs (Virtual Interactive) init)

main : IO ()
main =
  do (entryFile :: depth :: term) <- drop 1 <$> getArgs
       | _ => die "Expected filename, depth, and term as arguments."
     let Just depth' = parsePositive depth
       | Nothing => die "The second argument must be a non-negative number."
     let term' = unwords term
     let Right (_, _, pterm) = parsePTerm term'
       | Left err => die $ show err
     coreRun (trace entryFile depth' pterm)
             (\err => die (show err))
             (\res => pure ())
     pure ()


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

import Libraries.Text.PrettyPrint.Prettyprinter.Util

import System
import System.File

import Util

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

evalOneStep : {auto c : Ref Ctxt Defs} -> {vars : _} -> Defs -> Env Term vars -> Term vars -> Core (Term vars)
evalOneStep = normaliseOpts ({ fuel := Just 1, strategy := CBV } withAll)

Interpolation Nat where
  interpolate k = show k

||| Evaluate for the given number of steps printing the intermediate
||| results.
||| Stops early if a term becomes neutral or normal.
||| Return the number of steps evaluated and the final result.
evalN : {auto c : Ref Ctxt Defs} ->
  {auto u : Ref UST UState} ->
  {auto s : Ref Syn SyntaxInfo} ->
  {auto m : Ref MD Metadata} ->
  {auto o : Ref ROpts REPLOpts} ->
  Fuel ->
  (idx : Nat) ->
  ClosedTerm ->
  Core (Nat, ClosedTerm)
evalN Dry k tm = pure (k, tm)
evalN (More fuel) k tm =
  do defs <- get Ctxt
     tm' <- evalOneStep defs [] tm
     let outIdx = (S k)
     if tm == tm'
        then pure (k, tm)
        else do fullTm' <- resugar [] =<< toFullNames tm'
                iputStrLn $ pretty "\{outIdx}:" <++> (Syntax <$> prettyTerm fullTm')
                evalN fuel outIdx tm'

trace : (entryFile : String) -> PTerm -> Core ()
trace entryFile pterm =
  do _ <- setupCore entryFile
     (tm `WithType` ty) <- inferAndElab InExpr pterm
     defs <- get Ctxt
     fullTm <- resugar [] =<< toFullNames tm
     fullTy <- resugar [] =<< toFullNames ty
     iputStrLn $ Syntax <$> prettyTerm fullTm <++> pretty ":" <++> prettyTerm fullTy
     -- TODO: instead of an arbitrary limit of 30 steps, do chunks and then stop to
     --       ask the user if we should continue.
     (i, final) <- evalN (limit 30) 0 tm
     when (i == 0) $
       iputStrLn $ pretty "Nothing to evaluate."
     pure ()

main : IO ()
main =
  do (entryFile :: term) <- drop 1 <$> getArgs
       | _ => die "Expected filename and definition name as only arguments."
     let term' = unwords term
     let Right (_, _, pterm) = runParser (Virtual Interactive) Nothing term' (expr plhs (Virtual Interactive) init)
       | Left err => die $ show err
     coreRun (trace entryFile pterm)
             (\err => die (show err))
             (\res => pure ())
     pure ()


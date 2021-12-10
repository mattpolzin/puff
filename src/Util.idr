module Util


import Compiler.Common

import Core.Context
import Core.Context.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.FC
import Core.Name
import Core.Normalise
import Core.TT
import Core.Value

import Data.List
import Data.String

import Idris.Doc.String
import Idris.Desugar
import Idris.Env
import Idris.Error
import Idris.IDEMode.Holes
import Idris.Package.Types
import Idris.Pretty
import Idris.REPL
import Idris.REPL.Opts
import Idris.Resugar
import Idris.SetOptions
import Idris.Syntax
import Idris.Version

import Parser.Rule.Source
import Parser.Source

import Libraries.Data.Version
import Libraries.Text.PrettyPrint.Prettyprinter.Util
import Libraries.Utils.Path

import IdrisPaths

import System
import System.Directory

prettyTerm : IPTerm -> Doc IdrisAnn
prettyTerm = reAnnotate Syntax . Idris.Pretty.prettyTerm

displayClause : {auto c : Ref Ctxt Defs} ->
                {auto s : Ref Syn SyntaxInfo} ->
                Defs -> (vs ** (Env Term vs, Term vs, Term vs)) ->
                Core (Doc IdrisAnn)
displayClause defs (vs ** (env, lhs, rhs))
    = do lhstm <- resugar env !(normaliseHoles defs env lhs)
         rhstm <- resugar env !(normaliseHoles defs env rhs)
         pure (prettyTerm lhstm <++> equals <++> prettyTerm rhstm)

displayType : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Defs -> (Name, Int, GlobalDef) ->
              Core (Doc IdrisAnn)
displayType defs (n, i, gdef)
    = maybe (do tm <- resugar [] !(normaliseHoles defs [] (type gdef))
                nm <- aliasName (fullname gdef)
                let ann = showCategory Syntax gdef
                pure (ann (pretty nm) <++> colon <++> prettyTerm tm))
            (\num => reAnnotate Syntax <$> prettyHole defs [] n num (type gdef))
            (isHole gdef)

export
displayPats : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Defs -> (Name, Int, GlobalDef) ->
              Core (Doc IdrisAnn)
displayPats defs (n, idx, gdef)
    = case definition gdef of
           PMDef _ _ _ _ pats
               => do ty <- displayType defs (n, idx, gdef)
                     ps <- traverse (displayClause defs) pats
                     pure (vsep (ty :: ps))
           _ => pure (pretty n <++> reflow "is not a pattern matching definition")

loadEnvVars : {auto c : Ref Ctxt Defs} -> Core ()
loadEnvVars =
  do defs <- get Ctxt
     bprefix <- coreLift $ idrisGetEnv "IDRIS2_PREFIX"
     the (Core ()) $ case bprefix of
          Just p => setPrefix p
          Nothing => setPrefix yprefix
     bpath <- coreLift $ idrisGetEnv "IDRIS2_PATH"
     the (Core ()) $ case bpath of
          Just path => do traverseList1_ addExtraDir (map trim (split (==pathSeparator) path))
          Nothing => pure ()
     bdata <- coreLift $ idrisGetEnv "IDRIS2_DATA"
     the (Core ()) $ case bdata of
          Just path => do traverseList1_ addDataDir (map trim (split (==pathSeparator) path))
          Nothing => pure ()
     blibs <- coreLift $ idrisGetEnv "IDRIS2_LIBS"
     the (Core ()) $ case blibs of
          Just path => do traverseList1_ addLibDir (map trim (split (==pathSeparator) path))
          Nothing => pure ()
     pdirs <- coreLift $ idrisGetEnv "IDRIS2_PACKAGE_PATH"
     the (Core ()) $ case pdirs of
          Just path => do traverseList1_ addPackageDir (map trim (split (==pathSeparator) path))
          Nothing => pure ()
     cg <- coreLift $ idrisGetEnv "IDRIS2_CG"
     the (Core ()) $ case cg of
          Just e => case getCG (options defs) e of
                         Just cg => setCG cg
                         Nothing => throw (InternalError ("Unknown code generator " ++ show e))
          Nothing => pure ()

export
setupEnv : {auto c : Ref Ctxt Defs} -> Core ()
setupEnv =
  do loadEnvVars
     defs <- get Ctxt
     addPkgDir "prelude" anyBounds
     addPkgDir "base" anyBounds
     addDataDir (prefix_dir (dirs (options defs)) </>
                    ("idris2-" ++ showVersion False version) </> "support")
     addLibDir (prefix_dir (dirs (options defs)) </>
                    ("idris2-" ++ showVersion False version) </> "lib")
     Just cwd <- coreLift $ currentDir
          | Nothing => throw (InternalError "Can't get current directory")
     addLibDir cwd


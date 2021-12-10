module Main

import Compiler.Common

import Core.Context
import Core.Context.Context
import Core.Context.Log
import Core.Core
import Core.Directory
import Core.Env
import Core.FC
import Core.InitPrimitives
import Core.Name
import Core.Metadata
import Core.Normalise
import Core.TT
import Core.UnifyState
import Core.Value

import Data.List

import Idris.Doc.String
import Idris.Desugar
import Idris.Env
import Idris.Error
import Idris.IDEMode.Holes
import Idris.Pretty
import Idris.ProcessIdr
import Idris.REPL
import Idris.REPL.Opts
import Idris.Resugar
import Idris.SetOptions
import Idris.Syntax

import Parser.Rule.Source
import Parser.Source

import Libraries.Text.PrettyPrint.Prettyprinter.Util

import System
import System.File

import Util

die : String -> IO ()
die msg =
  do putStrLn msg
     exitFailure

-- toString : Doc IdrisAnn -> String
-- toString = show

trace : (entryFile : String) -> Name -> Core ()
trace entryFile n =
  do _ <- newRef Ctxt (!initDefs)
     _ <- newRef Syn initSyntax
     setupEnv
     addPrimitives
     _ <- newRef UST initUState
     _ <- newRef ROpts (defaultOpts (Just entryFile) (REPL InfoLvl) [])
     setWorkingDir "."
     origin <- ctxtPathToNS entryFile
     _ <- newRef MD (initMetadata $ PhysicalIdrSrc origin)
     FileLoaded f <- loadMainFile entryFile
       | REPLError err => coreLift . printLn $ err
       | ErrorLoadingFile f err => throw $ GenericMsg EmptyFC $ show err
       | ErrorsBuildingFile f errs => throw $ GenericMsg EmptyFC $ show errs
       | _ => throw $ GenericMsg EmptyFC "Failed to load main file."
     defs <- get Ctxt
     case !(lookupCtxtName n defs.gamma) of
          [] => undefinedName replFC n
          ts => do defs <- traverse (displayPats defs) ts
                   coreLift . printLn $ vsep defs

main : IO ()
main =
  do [entryFile, strName] <- drop 1 <$> getArgs
       | _ => die "Expected filename and definition name as only arguments."
     let Right (_, s, n) = runParser (Virtual Interactive) Nothing strName Source.name
       | Left err => die $ show err
     coreRun (trace entryFile n)
             (\err => die (show err))
             (\res => pure ())
     pure ()

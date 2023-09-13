/-
Copyright (c) 2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Logan Murphy
-/

import Smt.Data.Sexp
import Smt.Commands
import Lean 
open Lean 

def TestFile : String := "/home/logan/lean4/lean-smt/Test/Smtlib/system-e.smt2"

def quickTest : IO Unit := do 
  let s ← IO.FS.readFile TestFile
  let ts := Sexp.parseMany s 
  match ts with 
  | .ok s => dbg_trace s 
  | .error e => dbg_trace e 
  return () 


def atomicCommand : String → Option Smt.Command
| "check-sat" => Smt.Command.checkSat
| "get-model" => Smt.Command.getModel
| "get-proof" => Smt.Command.getProof
| "exit" => Smt.Command.exit
| _ => none 

inductive CmdType 
| setLogic
| setOption
| declSort 
| defSort 
| declareFun
| defFun 
| assert
 

def getCommandType : List Sexp → MetaM CmdType 
| [] => failure 
| x::_ => 
  match x with 
  | .atom "set-logic" => return CmdType.setLogic 
  | .atom "set-option" => return CmdType.setOption 
  | .atom "declare-sort" => return CmdType.declSort 
  | .atom "declare-fun" => return CmdType.declareFun
  | .atom "assert" => return CmdType.assert 
  | .atom "declare-const" => return CmdType.declSort
  | _ => failure 

def forceAtom : Sexp → MetaM String 
| .atom s => return s 
| _ => failure 

def forceListAtom : Sexp → MetaM (List String)
| .expr l => l.mapM (forceAtom)
| _ => failure

def asString : Sexp → String := toString

def getAppCommand (s : List Sexp) : MetaM Smt.Command := do 
  let τ ← getCommandType s 
  match τ with 
  | .setLogic => return Smt.Command.setLogic (← forceAtom s[1]!)
  | .setOption => return Smt.Command.setOption (← forceAtom s[1]!) (← forceAtom s[2]!)
  | .declSort => return Smt.Command.declareSort (← forceAtom s[1]!) 0 -- TODO!
  | .declareFun => return Smt.Command.declareFun (← forceAtom s[1]!) ( (Smt.Term.symbolT) <$> (← forceListAtom s[2]!)) (Smt.Term.symbolT (← forceAtom s[3]!))
  | .assert => return Smt.Command.assert (Smt.Term.literalT s[1]!.serialize)
  | .defFun => failure  -- TODO
  | .defSort => failure  -- TODO

def smtlibToCommands (fname : System.FilePath) : MetaM (List (Smt.Command)) := do 
  match Sexp.parseMany (← IO.FS.readFile fname) with 
  | .error e => 
    dbg_trace "(Smt.Smtlib) Could not parse file to Sexp "
    failure
  | .ok s => 
    s.mapM (getCommand)
  where getCommand x : MetaM (Smt.Command) := 
    match x with 
    | .atom s => match atomicCommand s with | .some x => return x | _ => failure
    | .expr l => getAppCommand l 
   
-- #eval smtlibToCommands TestFile -- need to add patterns.
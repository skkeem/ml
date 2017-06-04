(*
 * SNU 4541.664A Program Analysis 2017 Spring
 * DongKwon Lee (dklee@ropas.snu.ac.kr)
 *)


(*
 * hell analyzer
 *)
 
open Program 
open DomITV

exception Error of string
 
type result =
    | YES
    | NO
    | DONTKNOW

let result_to_str : result -> string = fun a -> match a with
    | YES -> "Yes"
    | NO -> "No"
    | DONTKNOW -> "I don't know"
  
include K2

(* davinci analysis *)
let rec hellAnalyzer : program -> result = fun pgm ->
    let mem = analysis (Memory.bot, pgm) in
    let ((i, _), _) = Memory.image mem "liberation" in
    (*
    let x = (match i with
    | Intv.BOT -> (0, 0)
    | Intv.ELT (Intv.Ninfty, Intv.Pinfty) -> (-100, 100)
    | Intv.ELT (Intv.Ninfty, Intv.Z z) -> (-100, z)
    | Intv.ELT (Intv.Z z, Intv.Pinfty) -> (z, 100)
    | Intv.ELT (Intv.Z z1, Intv.Z z2) -> (z1, z2)) in
    print_int (fst x);
    print_int (snd x);
    *)
    if Intv.isIn 1 i then YES
    else NO

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
    let x = (match i with
    | Intv.BOT -> (0, 0)
    | Intv.ELT (Ninfty, Pinfty) -> (-100, 100)
    | Intv.ELT (Ninfty, Z z) -> (-100, z)
    | Intv.ELT (Z z, Pinfty) -> (z, 100)
    | Intv.ELT (Z z1, Z z2) -> (z1, z2)) in
    print_int (fst x);
    print_int (snd x);
    DONTKNOW
    (*
    let analysis = K.analyze pgm in
    let liberation = analysis "liberation" in
    if liberation = TOP then DONTKNOW
    else if 1 in liberation then YES
    else NO
    *)

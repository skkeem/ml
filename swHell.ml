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
    let memT = analysis (Memory.bot, pgm) true in
    let ((iT, _), _) = Memory.image memT "liberation" in
    let bT = Intv.isIn 1 iT in

    (*
    if bT then print_string "T:true" else print_string "T:false";
    print_newline();
    *)
    
    let memF = analysis (Memory.bot, pgm) false in
    let ((iF, _), _) = Memory.image memF "liberation" in
    let bF = Intv.isIn 1 iF in

    (*
    if bF then print_string "F:true" else print_string "F:false";
    print_newline();
    *)

    if bT && bF then DONTKNOW
    else if bT then YES
    else NO

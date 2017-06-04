(*
 * SNU 4541.664A Program Analysis 2017 Spring
 * DongKwon Lee (dklee@ropas.snu.ac.kr)
 *)


(*
 * davinvi analyzer
 *)
 
open Program 

exception Error of string
 
type result =
    | YES
    | NO
    | DONTKNOW

let result_to_str : result -> string =
    fun r -> match r with
             | YES -> "Yes, it is davinci code"
             | NO -> "No, it is not davinci code"
             | DONTKNOW -> "I don't know"
  
module K =
struct
    let collect pgm = []
end

let used_varlist pgm = []

(* davinci analysis *)
let rec davinciAnalyzer : program -> result =
    fun pgm -> let varlist = used_varlist pgm in
               let states = K.collect pgm in (* (K.collect pgm) returns list of abstract memory, which are abstract memories in pgm points *)
               let rec check mem varlist = (match varlist with
                                            | [] -> YES
                                            | hd::tl -> if (mem hd) = YES then check mem tl else (mem hd)) in
               let rec checkall states = (match states with
                                          | [] -> YES
                                          | hd::tl -> if check hd varlist = YES then checkall tl else check hd varlist) in
               checkall states; DONTKNOW

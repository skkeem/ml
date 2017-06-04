(*
 * SNU 4541.664A Program Analysis 2017 Spring
 * DongKwon Lee (dklee@ropas.snu.ac.kr)
 *)


(*
 * hell analyzer
 *)
 
open Program 
open DomFunctor

(* integer -> Interval *)
module Intv =
struct
    type bound = Ninfty | Z of int | Pinfty
    type t = BOT | ELT of bound * bound
  
    let bot = BOT
    let top = ELT (Ninfty, Pinfty)
    let bound_leq a b = 
        match a,b with
        | (Ninfty, _) -> true
        | (_, Pinfty) -> true
        | (_, Ninfty) -> false
        | (Pinfty, _) -> false
        | (Z i1, Z i2) -> i1 <= i2
    let bound_add a b =
        match a,b with
        | (Ninfty, _) -> Ninfty
        | (_, Ninfty) -> Ninfty
        | (Pinfty, _) -> Pinfty
        | (_, Pinfty) -> Pinfty
        | (Z i1, Z i2) -> Z (i1 + i2)
    let bound_minus x =
        match x with
        | Ninfty -> Pinfty
        | Pinfty -> Ninfty
        | Z i -> Z (-i)

    let smaller a b = if bound_leq a b then a else b
    let bigger a b = if bound_leq a b then b else a

    let add a b =
        match a,b with
        | (BOT, _) -> bot
        | (_, BOT) -> bot
        | (ELT (l1, u1), ELT (l2, u2)) -> ELT (bound_add l1 l2, bound_add u1 u2)
    let minus x =
        match x with
        | BOT -> bot
        | ELT (l, u) -> ELT (bound_minus u, bound_minus l)
    let less x y =
        match x,y with
        | (BOT, _) | (_, BOT) -> 0
        | (ELT (l1, u1), ELT (l2, u2)) -> (if bound_leq u2 l1 then 1
                                           else if bound_leq u1 l2 then 2
                                           else 3)
    let isIn e i =
        match i with
        | BOT -> false
        | ELT(Ninfty, Pinfty) -> true
        | ELT(Ninfty, Z u) -> e <= u
        | ELT(Z l, Pinfty) -> l <= e
        | ELT(Z l, Z u) -> l <= e && e <= u
        | _ -> false

    let join x y = 
        match x,y with
        | (BOT, _) -> y
        | (_, BOT) -> x
        | (ELT (l1, u1), ELT (l2, u2)) -> ELT (smaller l1 l2, bigger u1 u2)
  
    let leq x y =
        match x,y with
        | (BOT, _) -> true
        | (_, BOT) -> false
        | (ELT (l1, u1), ELT (l2, u2)) -> bound_leq l2 l1 && bound_leq u1 u2
  
    let widen x y =
        match x,y with
        | (BOT, _) -> top
        | (_, BOT) -> print_string "widen error"; BOT
        | (ELT (l1, u1), ELT (l2, u2)) ->
                let l = if l1 <> l2 && bound_leq l2 l1 then Ninfty else l1
                and u = if u1 <> u2 && bound_leq u1 u2 then Pinfty else u1 in
                ELT (l, u)

    let narrow x y =
        match x,y with
        | (BOT, _) -> print_string "narrow error"; BOT
        | (_, BOT) -> BOT
        | (ELT (l1, u1), ELT (l2, u2)) ->
                ELT (bigger l1 l2, smaller u1 u2)

    let make low upper = ELT (low, upper)
end

(* bool -> Bool *)
module Bool =
struct
    type t = BOT | T | F | TOP

    let bot = BOT
    let top = TOP

    let nd x y =
        match x,y with
        | (BOT, _) | (_, BOT) -> BOT
        | (F, _) | (_, F) -> F
        | (T, _) -> y
        | (_, T) -> x
        | (_, _) -> TOP

    let orr x y =
        match x,y with
        | (BOT, _) | (_, BOT) -> BOT
        | (T, _) | (_, T) -> T
        | (F, _) -> y
        | (_, F) -> x
        | (_, _) -> TOP

    let nt x =
        match x with
        | BOT -> BOT
        | T -> F
        | F -> T
        | TOP -> TOP

    let join x y =
        match x,y with
        | (BOT, _) -> y
        | (_, BOT) -> x
        | (T, T) -> T
        | (F, F) -> F
        | _ -> TOP

    let leq x y =
        match x,y with
        | (BOT, _) -> true
        | (_, TOP) -> true
        | (TOP, _) -> false
        | (_, BOT) -> false
        | _ -> true

    let widen = join
    let narrow = join
end

(* location powerset -> LocPowSet *)
module Var = 
struct
    type t = string
    let compare = compare
end
module Loc = Var
module LocSet = PrimitiveSet(Loc)
module Locc = PowerSetDomain(LocSet)
module Loc' = struct
    include Locc

    let widen = join
    let narrow = join
end

(* Value & Memory *)
module Valuee = ProductDomain(ProductDomain(Intv)(Bool))(Loc')
module Value =
struct
    include Valuee

    let widen x y =
        let ((a, b), c) = x
        and ((a', b'), c') = y in
        (Intv.widen a a', Bool.widen b b'), Loc'.widen c c'

    let narrow x y =
        let ((a, b), c) = x 
        and ((a', b'), c') = y in
        (Intv.narrow a a', Bool.narrow b b'), Loc'.narrow c c'
end
module Memoryy = FunDomain(Loc)(Value)
module Memory =
struct
    include Memoryy

    exception NoPath

    type tb = BOT | MEM of t

    let bot = MEM bot
    let bott = BOT
    let top = MEM top

    let join x y =
        match x,y with
        | (BOT, _) -> y
        | (_, BOT) -> x
        | (MEM m1, MEM m2) -> MEM (join m1 m2)

    let leq x y =
        match x,y with
        | (BOT, m) -> if m = bot then false else true
        | (m, BOT) -> if m = bot then true else false
        | (MEM m1, MEM m2) -> leq m1 m2

    let image x l =
        match x with
        | BOT -> Value.bot
        | MEM s -> image s l

    let update x l r =
        match x with
        | BOT -> BOT
        | MEM s -> MEM (update s l r)

    let weakupdate x l r =
        match x with
        | BOT -> BOT
        | MEM s -> MEM (weakupdate s l r)

    let map f x =
        match x with
        | BOT -> raise NoPath
        | MEM s -> map f s

    let fold f x acc =
        match x with
        | BOT -> raise NoPath
        | MEM s -> fold f s acc

    let to_list x =
        match x with
        | BOT -> []
        | MEM s -> to_list s

    let make l =
        MEM (make l)

    let widen_ x y =
        match x,y with
        | (TOP, _) -> TOP
        | (_, TOP) -> TOP
        | (ELT m1, ELT m2) ->
                ELT (Map.fold
                        (fun k v acc_m ->
                            if Map.mem k acc_m then
                                Map.add k (Value.widen v (Map.find k acc_m)) acc_m
                            else Map.add k v acc_m
                        ) m1 m2)
    let widen x y =
        match x,y with
        | (BOT, _) -> raise NoPath
        | (_, BOT) -> raise NoPath
        | (MEM m1, MEM m2) -> MEM (widen_ m1 m2)

    let narrow_ x y =
        match x,y with
        | (TOP, _) -> y
        | (_, TOP) -> x
        | (ELT m1, ELT m2) ->
                ELT (Map.fold
                        (fun k v acc_m ->
                            if Map.mem k acc_m then
                                Map.add k (Value.narrow v (Map.find k acc_m)) acc_m
                            else Map.add k v acc_m
                        ) m1 m2)
    let narrow x y =
        match x,y with
        | (BOT, _) -> raise NoPath
        | (_, BOT) -> raise NoPath
        | (MEM m1, MEM m2) -> MEM (narrow_ m1 m2)
end

exception Error of string
 
type result =
    | YES
    | NO
    | DONTKNOW

let result_to_str : result -> string = fun a -> match a with
    | YES -> "Yes"
    | NO -> "No"
    | DONTKNOW -> "I don't know"
  
let rec compare_mem m1 m2 varlist =
  match varlist with
  | [] -> true
  | hd::tl -> ((Memory.image m1 hd) = (Memory.image m2 hd)) && (compare_mem m1 m2 tl)

(* list operation *)
let rec list_trim l =
  match l with
  | [] -> []
  | hd::tl -> if (List.mem hd tl) then list_trim tl else hd::(list_trim tl)

(* let widen_mem m1 m2 = fun x -> (Value.widen (image m1 x) (image m2 x)) *)

(* let narrow_mem m1 m2 = fun x -> (narrow_val (m1 x) (m2 x)) *)

(* var list gathering : "do not" change here *)
let rec used_vars_exp exp =
    (match exp with
    | NUM i -> []
    | TRUE -> []
    | FALSE -> []
    | READ -> []
    | VAR id | DEREF id | AT id -> [id]
    | ADD (e1, e2) -> (used_vars_exp e1) @ (used_vars_exp e2)
    | MINUS e -> used_vars_exp e
    | ANDALSO (e1, e2) -> (used_vars_exp e1) @ (used_vars_exp e2)
    | ORELSE (e1, e2) -> (used_vars_exp e1) @ (used_vars_exp e2)
    | NOT e -> used_vars_exp e
    | LESS (e1, e2) -> (used_vars_exp e1) @ (used_vars_exp e2)
    )

let rec used_vars cmd =
  match cmd with
  | SKIP -> []
  | ASSIGN (id, e) -> id::(used_vars_exp e)
  | PTRASSIGN (id, e) -> id::(used_vars_exp e)
  | SEQ (cmd1, cmd2) -> (used_vars cmd1) @ (used_vars cmd2)
  | IF (e, cmd1, cmd2) -> (used_vars_exp e) @ (used_vars cmd1) @ (used_vars cmd2)
  | WHILE (e, cmd) -> (used_vars_exp e) @ (used_vars cmd)

let used_varlist cmd = list_trim (used_vars cmd)

(* exp evaluation *)
let rec eval : (Memory.tb * exp) -> bool -> Value.t  = fun (mem, e) lib ->
  match e with
  | NUM z -> (Intv.make (Intv.Z z) (Intv.Z z), Bool.bot), Loc'.bot
  | TRUE -> (Intv.bot, Bool.T), Loc'.bot
  | FALSE -> (Intv.bot, Bool.F), Loc'.bot
  | READ -> if lib then ((Intv.make (Intv.Z 100) Intv.Pinfty), Bool.bot), Loc'.bot 
            else ((Intv.make Intv.Ninfty (Intv.Z 99)), Bool.bot), Loc'.bot 
  | VAR x -> Memory.image mem x
  | DEREF x -> let ((_,_), l) = Memory.image mem x in
               Loc'.fold (fun y v -> Value.join (Memory.image mem y) v) l Value.bot
  | AT x -> (Intv.bot, Bool.bot), Loc'.make [x]
  | ADD (e1, e2) -> let ((i1, _), _) = eval (mem, e1) lib
                    and ((i2, _), _) = eval (mem, e2) lib in
                    (Intv.add i1 i2, Bool.bot), Loc'.bot
  | MINUS e -> let ((i, _), _) = eval (mem, e) lib in 
               (Intv.minus i, Bool.bot), Loc'.bot 
  | ANDALSO (e1, e2) -> let ((_, b1), _) = eval (mem, e1) lib
                        and ((_, b2), _) = eval (mem, e2) lib in
                        (Intv.bot, Bool.nd b1 b2), Loc'.bot
  | ORELSE (e1, e2) -> let ((_, b1), _) = eval (mem, e1) lib
                       and ((_, b2), _) = eval (mem, e2) lib in
                       (Intv.bot, Bool.orr b1 b2), Loc'.bot
  | NOT e -> let ((_, b), _) = eval (mem, e) lib in
             (Intv.bot, Bool.nt b), Loc'.bot
  | LESS (e1, e2) -> let ((i1, _), _) = eval (mem, e1) lib
                     and ((i2, _), _) = eval (mem, e2) lib in
                     let t = Intv.less i1 i2 in
                     let b = (if t = 0 then Bool.BOT
                              else if t = 1 then Bool.F
                              else if t = 2 then Bool.T
                              else Bool.TOP) in
                     (Intv.bot, b), Loc'.bot

(* memory filtering by boolean expression *)
let rec assume : (Memory.tb * exp) -> bool -> Memory.tb = fun (mem, e) lib ->
  match e with
  | TRUE -> mem
  | FALSE -> Memory.bott
  | VAR id -> 
          let ((_, b), _) = Memory.image mem id in 
          (match b with
          | Bool.BOT -> Memory.bott
          | Bool.T -> mem
          | Bool.F -> Memory.bott
          | Bool.TOP -> Memory.update mem id ((Intv.bot, Bool.T), Loc'.bot))
  | DEREF id ->
          let ((_, _), l) = Memory.image mem id in
          let v = Loc'.make (List.filter (fun x -> (snd (fst (Memory.image mem x))) = Bool.T || (snd (fst (Memory.image mem x))) = Bool.TOP) (Loc'.to_list l)) in
          Memory.update mem id ((Intv.bot, Bool.bot), v)
  | ANDALSO (e1, e2) -> assume (assume (mem, e1) lib, e2) lib
  | ORELSE (e1, e2) -> Memory.join (assume (mem, e1) lib) (assume (mem, e2) lib)
  | NOT e -> assumeNot (mem, e) lib
  | LESS (e1, e2) -> 
          (match e1,e2 with
          | (VAR x, NUM z) ->
                  let ((i, _), _) = eval (mem, e1) lib in
                  let ni = (match i with
                           | Intv.BOT -> Intv.bot
                           | Intv.ELT (l, u) ->
                                   if Intv.bound_leq (Intv.Z z) l then Intv.bot
                                   else if Intv.bound_leq u (Intv.Z (z-1)) then Intv.make l u
                                   else Intv.make l (Intv.Z (z-1))) in
                  if ni = Intv.bot then Memory.bott
                  else Memory.update mem x ((ni, Bool.bot), Loc'.bot)
          | (NUM z, VAR x) ->
                  let ((i, _), _) = eval (mem, e2) lib in
                  let ni = (match i with
                           | Intv.BOT -> Intv.bot
                           | Intv.ELT (l, u) ->
                                   if Intv.bound_leq u (Intv.Z z) then Intv.bot
                                   else if Intv.bound_leq (Intv.Z (z+1)) l then Intv.make l u
                                   else Intv.make (Intv.Z (z+1)) u) in
                  if ni = Intv.bot then Memory.bott
                  else Memory.update mem x ((ni, Bool.bot), Loc'.bot)
          | _ ->
                  let ((_, b), _) = eval (mem, e) lib in
                  (match b with
                  | Bool.BOT -> Memory.bott
                  | Bool.T -> mem
                  | Bool.F -> Memory.bott
                  | Bool.TOP -> mem))
  | _ -> Memory.bott
and
assumeNot : (Memory.tb * exp) -> bool -> Memory.tb = fun (mem, e) lib ->
  match e with
  | TRUE -> Memory.bott
  | FALSE -> mem
  | VAR id -> 
          let ((_, b), _) = Memory.image mem id in 
          (match b with
          | Bool.BOT -> Memory.bott
          | Bool.T -> Memory.bott
          | Bool.F -> mem
          | Bool.TOP -> Memory.update mem id ((Intv.bot, Bool.F), Loc'.bot))
  | DEREF id ->
          let ((_, _), l) = Memory.image mem id in
          let v = Loc'.make (List.filter (fun x -> (snd (fst (Memory.image mem x))) = Bool.F || (snd (fst (Memory.image mem x))) = Bool.TOP) (Loc'.to_list l)) in
          Memory.update mem id ((Intv.bot, Bool.bot), v)
  | ANDALSO (e1, e2) -> Memory.join (assumeNot (mem, e1) lib) (assumeNot (mem, e2) lib)
  | ORELSE (e1, e2) -> assumeNot (assumeNot (mem, e1) lib, e2) lib
  | NOT e -> assume (mem, e) lib
  | LESS (e1, e2) -> 
          (match e1,e2 with
          | (VAR x, NUM z) ->
                  let ((i, _), _) = eval (mem, e1) lib in
                  let ni = (match i with
                           | Intv.BOT -> Intv.bot
                           | Intv.ELT (l, u) ->
                                   if Intv.bound_leq (Intv.Z z) l then Intv.make l u
                                   else if Intv.bound_leq u (Intv.Z (z-1)) then Intv.bot
                                   else Intv.make (Intv.Z z) u) in
                  if ni = Intv.bot then Memory.bott
                  else Memory.update mem x ((ni, Bool.bot), Loc'.bot)
          | (NUM z, VAR x) ->
                  let ((i, _), _) = eval (mem, e2) lib in
                  let ni = (match i with
                           | Intv.BOT -> Intv.bot
                           | Intv.ELT (l, u) ->
                                   if Intv.bound_leq u (Intv.Z z) then Intv.make l u
                                   else if Intv.bound_leq (Intv.Z (z+1)) l then Intv.bot
                                   else Intv.make l (Intv.Z z)) in
                  if ni = Intv.bot then Memory.bott
                  else Memory.update mem x ((ni, Bool.bot), Loc'.bot)
          | _ ->
                  let ((_, b), _) = eval (mem, e) lib in
                  (match b with
                  | Bool.BOT -> Memory.bott
                  | Bool.T -> Memory.bott
                  | Bool.F -> mem
                  | Bool.TOP -> mem))
  | _ -> Memory.bott

(* interval analysis for K- *)
let rec analysis : (Memory.tb * program) -> bool -> Memory.tb = fun (mem, pgm) lib ->
  let varlist = used_varlist pgm in
  match pgm with
  | SKIP -> mem
  | ASSIGN(id, e) -> Memory.update mem id (eval (mem, e) lib)
  | PTRASSIGN(id, e) -> 
          let v = eval (mem, e) lib in
          let ((_, _), l) = Memory.image mem id in
          Loc'.fold (fun y m -> Memory.weakupdate m y v) l mem
  | SEQ(cmd1, cmd2) ->
          let mem1 = analysis (mem, cmd1) lib in
          analysis (mem1, cmd2) lib
  | IF(e, cmd1, cmd2) -> 
          let mem1 = analysis (assume (mem, e) lib, cmd1) lib
          and mem2 = analysis (assumeNot (mem, e) lib, cmd2) lib in 
          Memory.join mem1 mem2
  | WHILE(e, cmd) ->
          let ff x = Memory.join mem (analysis (assume (x, e) lib, cmd) lib) in
          let rec widener y = (* Yi *)
              if compare_mem y (Memory.widen y (ff y)) varlist then y (* Stop condition *)
              else widener (Memory.widen y (ff y)) in (* Next *)
          let rec narrower z = (* Zi *)
              if compare_mem z (Memory.narrow z (ff z)) varlist then z (* Stop condition *)
              else narrower (Memory.narrow z (ff z)) in (* Next *)
          assumeNot (narrower (widener Memory.bot), e) lib

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

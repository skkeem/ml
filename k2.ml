(*
exception Error of string
type id = Program.id
type exp = Program.exp
type cmd = Program.cmd
type program = Program.program
*)
open Program
open DomITV

(* memory operation *)
(* image mem id *)
(* update mem id v *)
(* weakupdate mem id v 얜 join을 함 *)

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
let rec eval : (Memory.t * exp) -> bool -> Value.t  = fun (mem, e) lib ->
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
let rec assume : (Memory.t * exp) -> bool -> Memory.t = fun (mem, e) lib ->
  match e with
  | TRUE -> mem
  | FALSE -> Memory.bot
  | VAR id -> 
          let ((_, b), _) = Memory.image mem id in 
          (match b with
          | Bool.BOT -> Memory.bot
          | Bool.T -> mem
          | Bool.F -> Memory.bot
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
                                   else if Intv.bound_leq u (Intv.Z z) then Intv.make l u
                                   else Intv.make l (Intv.Z (z-1))) in
                  if ni = Intv.bot then Memory.bot
                  else Memory.update mem x ((ni, Bool.bot), Loc'.bot)
          | (NUM z, VAR x) ->
                  let ((i, _), _) = eval (mem, e2) lib in
                  let ni = (match i with
                           | Intv.BOT -> Intv.bot
                           | Intv.ELT (l, u) ->
                                   if Intv.bound_leq u (Intv.Z z) then Intv.bot
                                   else if Intv.bound_leq (Intv.Z z) l then Intv.make l u
                                   else Intv.make (Intv.Z (z+1)) u) in
                  if ni = Intv.bot then Memory.bot
                  else Memory.update mem x ((ni, Bool.bot), Loc'.bot)
          | _ ->
                  let ((_, b), _) = eval (mem, e) lib in
                  (match b with
                  | Bool.BOT -> Memory.bot
                  | Bool.T -> mem
                  | Bool.F -> Memory.bot
                  | Bool.TOP -> mem))
  | _ -> Memory.bot
and
assumeNot : (Memory.t * exp) -> bool -> Memory.t = fun (mem, e) lib ->
  match e with
  | TRUE -> Memory.bot
  | FALSE -> mem
  | VAR id -> 
          let ((_, b), _) = Memory.image mem id in 
          (match b with
          | Bool.BOT -> Memory.bot
          | Bool.T -> Memory.bot
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
                                   else if Intv.bound_leq u (Intv.Z z) then Intv.bot
                                   else Intv.make (Intv.Z z) u) in
                  if ni = Intv.bot then Memory.bot
                  else Memory.update mem x ((ni, Bool.bot), Loc'.bot)
          | (NUM z, VAR x) ->
                  let ((i, _), _) = eval (mem, e2) lib in
                  let ni = (match i with
                           | Intv.BOT -> Intv.bot
                           | Intv.ELT (l, u) ->
                                   if Intv.bound_leq u (Intv.Z z) then Intv.make l u
                                   else if Intv.bound_leq (Intv.Z z) l then Intv.bot
                                   else Intv.make l (Intv.Z z)) in
                  if ni = Intv.bot then Memory.bot
                  else Memory.update mem x ((ni, Bool.bot), Loc'.bot)
          | _ ->
                  let ((_, b), _) = eval (mem, e) lib in
                  (match b with
                  | Bool.BOT -> Memory.bot
                  | Bool.T -> Memory.bot
                  | Bool.F -> mem
                  | Bool.TOP -> mem))
  | _ -> Memory.bot

(*
(* memory pretty print : "do not" change here *)
let pp_bound : bound -> unit = fun bnd ->
  match bnd with
  | MIN -> print_string("MIN")
  | Z i -> print_int(i)
  | MAX -> print_string("MAX")

let pp_itv : itv -> unit = fun itv ->
  match itv with
  | BOT_ITV -> print_string("bottom")
  | ITV (bnd1, bnd2) -> 
    let _ = print_string("[") in
    let _ = pp_bound(bnd1) in
    let _ = print_string(", ") in
    let _ = pp_bound(bnd2) in
    print_string("]")
    
let pp_bool : bool_hat -> unit = fun b ->
  match b with
  | BOT_BOOL -> print_string("bottom") 
  | T -> print_string("T")
  | F -> print_string("F")
  | TOP_BOOL -> print_string("T, F")

let rec pp_loc : loc_hat -> unit = fun loc ->
  match loc with
  | LSET [] -> ()
  | LSET (hd::tl) -> print_string (hd ^ ", ") ; pp_loc (LSET tl)

let rec pp_memory : memory -> id list -> unit = fun mem -> (fun varlist ->
  match varlist with
  | [] -> ()
  | hd::tl ->
    let (i, b, l) = mem(hd) in
    let _ = print_string(hd ^ " -> interval : ") in
    let _ = pp_itv(i) in
    let _ = print_string(" bool : ") in
    let _ = pp_bool(b) in
    let _ = print_newline() in
    let _ = print_string(" loc : [ ") in
    let _ = pp_loc(l) in
    let _ = print_string("]") in
    let _ = print_newline() in
    pp_memory mem tl
    )
*)

(* interval analysis for K- *)
let rec analysis : (Memory.t * program) -> bool -> Memory.t = fun (mem, pgm) lib ->
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

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
        | ELT (l, u) -> ELT (bound_minus l, bound_minus u)
    let less x y =
        match x,y with
        | (BOT, _) | (_, BOT) -> 0
        | (ELT (l1, u1), ELT (l2, u2)) -> (if bound_leq u2 l1 then 1
                                           else if bound_leq u1 l2 then 2
                                           else 3)

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
        | (BOT, _) -> y
        | (_, BOT) -> print_string "widen error"; BOT
        | (ELT (l1, u1), ELT (l2, u2)) ->
                let l = if bound_leq l2 l1 then Ninfty else l1
                and u = if bound_leq u1 u2 then Pinfty else u1 in
                ELT (l, u)

    let narrow x y =
        match x,y with
        | (BOT, _) -> BOT
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

    let widen x y =
        match x,y with
        | (TOP, _) -> TOP
        | (_, TOP) -> TOP
        | (ELT m1, ELT m2) ->
                ELT (Map.fold
                        (fun k v acc_m ->
                            if Map.mem k acc_m then
                                Map.add k (Value.join v (Map.find k acc_m)) acc_m
                            else Map.add k v acc_m
                        ) m1 m2)
end

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

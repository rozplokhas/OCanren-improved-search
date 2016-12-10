(*
 * MiniKanren: miniKanren implementation.
 * Copyright (C) 2015-2016
 * Dmitri Boulytchev, Dmitry Kosarev, Alexey Syomin, 
 * St.Petersburg State University, JetBrains Research
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Library General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU Library General Public License version 2 for more details
 * (enclosed in the file COPYING).
 *)

module Stream =
  struct

    type 'a t = Nil | Cons of 'a * 'a t | Lazy of 'a t Lazy.t

    let from_fun (f: unit -> 'a t) : 'a t = Lazy (Lazy.lazy_from_fun f)

    let nil = Nil

    let cons h t = Cons (h, t)

    let rec is_empty = function
    | Nil    -> true
    | Lazy s -> is_empty @@ Lazy.force s
    | _ -> false

    let rec retrieve ?(n=(-1)) s =
      if n = 0
      then [], s
      else match s with
           | Nil          -> [], s
           | Cons (x, xs) -> let xs', s' = retrieve ~n:(n-1) xs in x::xs', s'
           | Lazy  z      -> retrieve ~n:n (Lazy.force z)

    let take ?(n=(-1)) s = fst @@ retrieve ~n:n s

    let hd s = List.hd @@ take ~n:1 s
    let tl s = snd @@ retrieve ~n:1 s

    let rec mplus fs gs =
      from_fun (fun () ->
         match fs with
         | Nil           -> gs
         | Cons (hd, tl) -> cons hd (mplus gs tl) 
         | Lazy z        -> mplus gs (Lazy.force z)
      )

    let rec bind xs f =
      from_fun (fun () ->
        match xs with
        | Cons (x, xs) -> mplus (f x) (bind xs f)
        | Nil          -> nil
        | Lazy z       -> bind (Lazy.force z) f
     )

    let rec map f = function
    | Nil -> Nil
    | Cons (x, xs) -> Cons (f x, map f xs)
    | Lazy s -> Lazy (Lazy.lazy_from_fun (fun () -> map f @@ Lazy.force s))

    let rec iter f = function
    | Nil -> ()
    | Cons (x, xs) -> f x; iter f xs
    | Lazy s -> iter f @@ Lazy.force s

  end

let (!!!) = Obj.magic;;

@type 'a logic = Ident of GT.int GT.list * GT.int | Var of GT.int GT.list * GT.int * 'a logic GT.list | Value of 'a with show, html, eq, compare, foldl, foldr, gmap

let logic = {logic with 
  gcata = (); 
  plugins = 
    object 
      method html    = logic.plugins#html
      method eq      = logic.plugins#eq
      method compare = logic.plugins#compare
      method foldr   = logic.plugins#foldr
      method foldl   = logic.plugins#foldl
      method gmap    = logic.plugins#gmap    
      method show fa x = 
        GT.transform(logic) 
           (GT.lift fa) 
           (object inherit ['a] @logic[show]              
              method c_Var _ s _ i cs = 
                let c =
                  match cs with 
                  | [] -> ""
                  | _  -> Printf.sprintf " %s" (GT.show(GT.list) (fun l -> "=/= " ^ s.GT.f () l) cs)
                in
                Printf.sprintf "_.%d%s" i c
                
              method c_Value _ _ x = x.GT.fx ()
            end) 
           () 
           x
    end
};;

@type 'a unlogic = [`Var of GT.int * 'a logic GT.list | `Value of 'a] with show, html, eq, compare, foldl, foldr (*, gmap*)

let destruct = function
| Var (_, i, c) -> `Var (i, c)
| Value x       -> `Value x

exception Not_a_value 

let (!!) x = Value x
let inj = (!!)

let prj_k k = function Value x -> x | Var (_, i, c) -> k i c
let prj x = prj_k (fun _ -> raise Not_a_value) x

let (!?) = prj

exception Occurs_check

type w = Unboxed of Obj.t | Boxed of int * int * (int -> Obj.t) | Invalid of int

let rec wrap (x : Obj.t) =
  Obj.(
    let is_valid_tag =
      List.fold_left
      (fun f t tag -> tag <> t && f tag)
      (fun _ -> true)
      [lazy_tag   ; closure_tag  ; object_tag  ; infix_tag ;
       forward_tag; no_scan_tag  ; abstract_tag; custom_tag;
       final_tag  ; unaligned_tag; out_of_heap_tag
      ]
    in
    let is_unboxed obj =
      is_int obj ||
      (fun t -> t = string_tag || t = double_tag) (tag obj)
    in
    if is_unboxed x
    then Unboxed x
    else
      let t = tag x in
      if is_valid_tag t
      then
        let f = if t = double_array_tag then !!! double_field else field in
        Boxed (t, size x, f x)
      else Invalid t
    )

let generic_show x =
  let x = Obj.repr x in
  let b = Buffer.create 1024 in
  let rec inner o =
    match wrap o with
    | Invalid n             -> Buffer.add_string b (Printf.sprintf "<invalid %d>" n)
    | Unboxed n when !!!n=0 -> Buffer.add_string b "[]"
    | Unboxed n             -> Buffer.add_string b (Printf.sprintf "int<%d>" (!!!n))
    | Boxed (t,l,f) when t=0 && l=1 && (match wrap (f 0) with Unboxed i when !!!i >=10 -> true | _ -> false) ->
       Printf.bprintf b "var%d" (match wrap (f 0) with Unboxed i -> !!!i | _ -> failwith "shit")

    | Boxed   (t, l, f) ->
        Buffer.add_string b (Printf.sprintf "boxed %d <" t);
        for i = 0 to l - 1 do (inner (f i); if i<l-1 then Buffer.add_string b " ") done;
        Buffer.add_string b ">"
  in
  inner x;
  Buffer.contents b

module Env :
  sig
    type t

    val empty  : unit -> t
    val fresh  : t -> 'a logic * t
    val var    : t -> 'a logic -> int option
  end = 
  struct
    type t = GT.int GT.list * int 

    let empty () = ([0], 10)

    let fresh (a, current) =
      let v = Var (a, current, []) in
      (!!!v, (a, current+1))

    let var_tag, var_size =
      let v = Var ([], 0, []) in
      Obj.tag (!!! v), Obj.size (!!! v)

    let var (a, _) x =
      let t = !!! x in
      if Obj.tag  t = var_tag  &&
         Obj.size t = var_size &&
         (let q = Obj.field t 0 in
          not (Obj.is_int q) && q == (!!!a)
         )
      then let Var (_, i, _) = !!! x in Some i
      else None

  end

type term = Obj.t

let term_of_logic = (!!!)
let logic_of_term = (!!!)

let (^~) hd tl =  term_of_logic hd :: tl
let (^.) a  b  = [term_of_logic a; term_of_logic b]
let (!^) a     = [term_of_logic a]

module IdentSet =
  struct
    module M = Map.Make (struct type t = int let compare = Pervasives.compare end)

    type t = GT.int GT.list * term M.t

    let empty () = ([0], M.empty)

    let new_ident (a, m) id = Ident (a, id)

    let id : t -> term -> int option = fun (a, _) t ->
      let tag, size =
        let v = Ident ([], 0)
        in Obj.tag (!!! v), Obj.size (!!! v)
      in
      if Obj.tag  t = tag  &&
         Obj.size t = size &&
         (let q = Obj.field t 0 in
          not (Obj.is_int q) && q == (!!!a)
         )
      then let Ident (_, i) = !!! t in Some i
      else None

    let bind_ident : term -> term -> t -> t = fun x t ((a, m) as iset) ->
      let Some i = id iset x
      in (a, M.add i t m)

    let rec refine : Env.t -> t -> term -> term = fun env ((a, m) as iset) term ->
      match id iset term with
      | Some i -> M.find i m
      | None ->
        (match Env.var env (!!! term) with
         | Some _ -> term
         | None   ->
            (match wrap (Obj.repr term) with
             | Unboxed _       -> term
             | Boxed (t, s, f) ->
                let term = Obj.dup (Obj.repr term) in
                let sf =
                  if t = Obj.double_array_tag
                  then !!! Obj.set_double_field
                  else Obj.set_field
                in
                for i = 0 to s - 1 do
                  sf term i (refine env iset (!!! (f i)))
                done;
                term
             | Invalid _       -> invalid_arg ""
            )
        )

    let rec idents : t -> term -> int list = fun iset term ->
      match id iset term with
      | Some i -> [i]
      | None ->
        (match wrap (Obj.repr term) with
         | Unboxed _       -> []
         | Boxed (t, s, f) ->
            let rec inner i acc =
              if i < s
              then inner (i+1) (idents iset (!!! (f i)) @ acc)
              else acc
            in inner 0 []
         | Invalid _       -> invalid_arg ""
        )

  end

module Subst :
  sig
    type t

    val empty   : t

    val of_list : (int * Obj.t * Obj.t) list -> t 
    val split   : t -> Obj.t list * Obj.t list 
    val walk    : Env.t -> 'a logic -> t -> 'a logic
    val unify   : Env.t -> 'a logic -> 'a logic -> t option -> (int * Obj.t * Obj.t) list * t option
    val show    : t -> string
  end =
  struct
    module M = Map.Make (struct type t = int let compare = Pervasives.compare end)

    type t = (Obj.t * Obj.t) M.t

    let show m = (M.fold (fun i (_, x) s -> s ^ Printf.sprintf "%d -> %s; " i (generic_show x)) m "subst {") ^ "}"

    let empty = M.empty

    let of_list l = List.fold_left (fun s (i, v, t) -> M.add i (v, t) s) empty l

    let split s = M.fold (fun _ (x, t) (xs, ts) -> x::xs, t::ts) s ([], []) 

    let rec walk env var subst =
      match Env.var env var with
      | None   -> var
      | Some i ->
          try walk env (snd (M.find i (!!! subst))) subst with Not_found -> var

    let rec occurs env xi term subst =
      let y = walk env term subst in
      match Env.var env y with
      | Some yi -> xi = yi
      | None -> 
         let wy = wrap (Obj.repr y) in
         match wy with
         | Unboxed _ -> false
         | Invalid n -> invalid_arg (Printf.sprintf "Invalid value in occurs check (%d)" n)
         | Boxed (_, s, f) ->
            let rec inner i =
              if i >= s then false
              else occurs env xi (!!!(f i)) subst || inner (i+1)
            in
            inner 0

    let unify env x y subst =
      let rec unify x y (delta, subst) = 
        let extend xi x term delta subst =
          if occurs env xi term subst then raise Occurs_check
          else (xi, !!!x, !!!term)::delta, Some (!!! (M.add xi (!!!x, term) (!!! subst)))
        in
        match subst with
        | None -> delta, None
        | (Some subst) as s ->
            let x, y = walk env x subst, walk env y subst in
            match Env.var env x, Env.var env y with
            | Some xi, Some yi -> if xi = yi then delta, s else extend xi x y delta subst 
            | Some xi, _       -> extend xi x y delta subst 
            | _      , Some yi -> extend yi y x delta subst 
            | _ ->
                let wx, wy = wrap (Obj.repr x), wrap (Obj.repr y) in
                (match wx, wy with
                 | Unboxed vx, Unboxed vy -> if vx = vy then delta, s else delta, None
                 | Boxed (tx, sx, fx), Boxed (ty, sy, fy) ->
                    if tx = ty && sx = sy
                    then
                      let rec inner i (delta, subst) = 
                        match subst with
                        | None -> delta, None
                        | Some _ ->
                           if i < sx
                           then inner (i+1) (unify (!!!(fx i)) (!!!(fy i)) (delta, subst))
                           else delta, subst
                      in
                      inner 0 (delta, s)
                    else delta, None
                 | Invalid n, _
                 | _, Invalid n -> invalid_arg (Printf.sprintf "Invalid values for unification (%d)" n)
                 | _ -> delta, None
                )
      in
      unify x y ([], subst)

  end

module State =
  struct  
    type t = Env.t * Subst.t * Subst.t list
    let empty () = (Env.empty (), Subst.empty, [])
    let env   (env, _, _) = env
    let show  (env, subst, constr) = Printf.sprintf "st {%s, %s}" (Subst.show subst) (GT.show(GT.list) Subst.show constr)
  end


exception Disequality_violated

let run_unification x y (env, subst, constr) =
  try
    let prefix, subst' = Subst.unify env x y (Some subst) in
    begin match subst' with
    | None -> Stream.nil
    | Some s -> 
        try
          (* TODO: only apply constraints with the relevant vars *)
          let constr' =
            List.fold_left (fun css' cs -> 
              let x, t  = Subst.split cs in
              try
                let p, s' = Subst.unify env (!!!x) (!!!t) subst' in
                match s' with
                | None -> css'
                | Some _ ->
                    match p with
                    | [] -> raise Disequality_violated
                    | _  -> (Subst.of_list p)::css'
              with Occurs_check -> css'
            ) 
            []
            constr
          in
          Stream.cons (env, s, constr') Stream.nil
        with Disequality_violated -> Stream.nil
    end
  with Occurs_check -> Stream.nil

let run_disequality x y ((env, subst, constr) as st) =
  let normalize_store prefix constr =
    let subst  = Subst.of_list prefix in
    let prefix = List.split (List.map (fun (_, x, t) -> (x, t)) prefix) in
    let subsumes subst (vs, ts) = 
      try 
        match Subst.unify env !!!vs !!!ts (Some subst) with
        | [], Some _ -> true
        | _ -> false
      with Occurs_check -> false
    in
    let rec traverse = function
    | [] -> [subst]
    | (c::cs) as ccs -> 
        if subsumes subst (Subst.split c)
        then ccs
        else if subsumes c prefix
             then traverse cs
             else c :: traverse cs
    in
    traverse constr
  in
  try 
    let prefix, subst' = Subst.unify env x y (Some subst) in
    match subst' with
    | None -> Stream.cons st Stream.nil
    | Some s -> 
        (match prefix with
        | [] -> Stream.nil
        | _  -> Stream.cons (env, subst, normalize_store prefix constr) Stream.nil
        )
  with Occurs_check -> Stream.cons st Stream.nil

type goal = 
| Unification of term * term
| Disequality of term * term
| Conjunction of goal list
| Disjunction of goal list
| Fresh       of term * goal
| Invoke      of string * term list

let (===) x y = Unification (term_of_logic x, term_of_logic y)

let (=/=) x y = Disequality (term_of_logic x, term_of_logic y)

let conj g1 g2 = Conjunction [g1; g2]

let (&&&) = conj

let disj g1 g2 = Disjunction [g1; g2]

let (|||) = disj

let rec (?|) gs = Disjunction gs 

let rec (?&) gs = Conjunction gs

let conde = (?|)

let fresh is gs = List.fold_left (fun g i -> Fresh (i, g)) (?& gs) is

let invoke name args = Invoke (name, args)

type definition = string * (term list * goal)

let def name args body = name, (args, body)

type program = IdentSet.t * definition list * goal

let prog iset defs g = (iset, defs, g)

let call_fresh f (env, subst, constr) =
  let x, env' = Env.fresh env in
  f x (env', subst, constr)

(*
let stream_conj_two f g st = Stream.bind (f st) g

let rec stream_conj = function
| [h]  -> h
| h::t -> stream_conj_two h (stream_conj t)

let stream_disj_two f g st = Stream.mplus (f st) (g st)

let rec stream_disj = function
| [h]  -> h
| h::t -> stream_disj_two h (stream_disj t)
*)

(* module Fresh =
  struct

    let succ prev f = call_fresh (fun x -> prev (f x)) 
 
    let zero  f = f 
    let one   f = succ zero f
    let two   f = succ one f
    let three f = succ two f
    let four  f = succ three f
    let five  f = succ four f
 
    let q     = one
    let qr    = two
    let qrs   = three
    let qrst  = four
    let pqrst = five

  end *)

let success = (!!true === !!true)
let failure = (!!true === !!false)
 
let eqo x y t =
  conde [
    (x === y) &&& (t === !!true);
    (x =/= y) &&& (t === !!false);
  ]

let neqo x y t =
  conde [
    (x =/= y) &&& (t === !!true);
    (x === y) &&& (t === !!false);
  ];;

@type ('a, 'l) llist = Nil | Cons of 'a * 'l with show, html, eq, compare, foldl, foldr, gmap
@type 'a lnat = O | S of 'a with show, html, eq, compare, foldl, foldr, gmap

module Bool =
  struct

    type 'a logic' = 'a logic 
    let logic' = logic

    type ground = bool

    let ground = {
      GT.gcata = ();
      GT.plugins = 
        object(this) 
          method html    n   = GT.html   (GT.bool) n
          method eq      n m = GT.eq     (GT.bool) n m
          method compare n m = GT.compare(GT.bool) n m
          method foldr   n   = GT.foldr  (GT.bool) n
          method foldl   n   = GT.foldl  (GT.bool) n
          method gmap    n   = GT.gmap   (GT.bool) n
          method show    n   = GT.show   (GT.bool) n
        end
    }

    type logic = bool logic'

    let logic = {
      GT.gcata = ();
      GT.plugins = 
        object(this) 
          method html    n   = GT.html   (logic') (GT.html   (ground)) n
          method eq      n m = GT.eq     (logic') (GT.eq     (ground)) n m
          method compare n m = GT.compare(logic') (GT.compare(ground)) n m
          method foldr   a n = GT.foldr  (logic') (GT.foldr  (ground)) a n
          method foldl   a n = GT.foldl  (logic') (GT.foldl  (ground)) a n
          method gmap    n   = GT.gmap   (logic') (GT.gmap   (ground)) n
          method show    n   = GT.show   (logic') (GT.show   (ground)) n
        end
    }

    let (!) = (!!)

    (* let (|^) a b c =
      conde [
        (a === !false) &&& (b === !false) &&& (c === !true);
        (a === !false) &&& (b === !true)  &&& (c === !true);
        (a === !true)  &&& (b === !false) &&& (c === !true);
        (a === !true)  &&& (b === !true)  &&& (c === !false);
      ]

    let noto' a na = (a |^ a) na

    let noto a = noto' a !true

    let oro a b c = 
      Fresh.two (fun aa bb ->      
        ((a  |^ a) aa) &&&
        ((b  |^ b) bb) &&&
        ((aa |^ bb) c)
      )

    let ando a b c = 
      Fresh.one (fun ab ->
        ((a  |^ b) ab) &&&
        ((ab |^ ab) c)
      )

    let (&&) a b = ando a b !true
    let (||) a b = oro  a b !true *)

  end

module Nat =
  struct

    type 'a logic' = 'a logic
    let logic' = logic

    type 'a t = 'a lnat

    type ground = ground t

    let ground = {
      GT.gcata = ();
      GT.plugins = 
        object(this) 
          method html    n = GT.html   (lnat) this#html    n
          method eq      n = GT.eq     (lnat) this#eq      n
          method compare n = GT.compare(lnat) this#compare n
          method foldr   n = GT.foldr  (lnat) this#foldr   n
          method foldl   n = GT.foldl  (lnat) this#foldl   n
          method gmap    n = GT.gmap   (lnat) this#gmap    n
          method show    n = GT.show   (lnat) this#show    n
        end
    }

    type logic  = logic t logic'

    let logic = {
      GT.gcata = ();
      GT.plugins = 
        object(this) 
          method html    n   = GT.html   (logic') (GT.html   (lnat) this#html   ) n
          method eq      n m = GT.eq     (logic') (GT.eq     (lnat) this#eq     ) n m
          method compare n m = GT.compare(logic') (GT.compare(lnat) this#compare) n m
          method foldr   a n = GT.foldr  (logic') (GT.foldr  (lnat) this#foldr  ) a n
          method foldl   a n = GT.foldl  (logic') (GT.foldl  (lnat) this#foldl  ) a n
          method gmap    n   = GT.gmap   (logic') (GT.gmap   (lnat) this#gmap   ) n
          method show    n   = GT.show   (logic') (GT.show   (lnat) this#show   ) n
        end
    }

    let rec of_int n = if n <= 0 then O else S (of_int (n-1))
    let rec to_int   = function O -> 0 | S n -> 1 + to_int n

    let (!) = (!!)
    
    let rec inj n = ! (GT.gmap(lnat) inj n)

    let prj_k k n =
      let rec inner n =
        GT.gmap(lnat) inner (prj_k k n)
      in
      inner n

    let prj n = prj_k (fun _ -> raise Not_a_value) n

    (* let rec addo x y z =
      conde [
        (x === !O) &&& (z === y);
        Fresh.two (fun x' z' ->
           (x === !(S x')) &&&
           (z === !(S z')) &&&
           (addo x' y z')
        )
      ]

    let (+) = addo

    let rec mulo x y z =
      conde [
        (x === !O) &&& (z === !O);
        Fresh.two (fun x' z' ->
          (x === !(S x')) &&&
          (addo y z' z) &&&
          (mulo x' y z')
        )
      ]

    let ( * ) = mulo

    let rec leo x y b =
      conde [
        (x === !O) &&& (b === !true);
        Fresh.two (fun x' y' -> 
          conde [
            (x === !(S x')) &&& (y === !(S y')) &&& (leo x' y' b)           
          ]
        )        
      ]

    let geo x y b = leo y x b

    let (<=) x y = leo x y !true
    let (>=) x y = geo x y !true

    let gto x y b = conde [(x >= y) &&& (x =/= y) &&& (b === !true)]
    let lto x y b = gto y x b

    let (>) x y = gto x y !true
    let (<) x y = lto x y !true *)
    
  end

let rec inj_nat n = 
  if n <= 0 then inj O
  else inj (S (inj_nat @@ n-1))

let rec prj_nat n = 
  match prj n with
  | O   -> 0
  | S n -> 1 + prj_nat n

module List =
  struct

    include List

    type 'a logic' = 'a logic

    let logic' = logic

    type ('a, 'l) t = ('a, 'l) llist

    type 'a ground = ('a, 'a ground) t
    type 'a logic  = ('a, 'a logic)  t logic'

    let rec of_list = function [] -> Nil | x::xs -> Cons (x, of_list xs)
    let rec to_list = function Nil -> [] | Cons (x, xs) -> x::to_list xs

    let (%)  x y = !!(Cons (x, y))
    let (%<) x y = !!(Cons (x, !!(Cons (y, !!Nil))))
    let (!<) x   = !!(Cons (x, !!Nil))

    let nil = inj Nil

    let rec inj fa l = !! (GT.gmap(llist) fa (inj fa) l)
    
    let prj_k fa k l =
      let rec inner l =
        GT.gmap(llist) fa inner (prj_k k l)
      in
      inner l

    let prj fa l = prj_k fa (fun _ -> raise Not_a_value) l

    let ground = {
      GT.gcata = ();
      GT.plugins = 
        object(this) 
          method html    fa l = GT.html   (llist) fa (this#html    fa) l
          method eq      fa l = GT.eq     (llist) fa (this#eq      fa) l
          method compare fa l = GT.compare(llist) fa (this#compare fa) l
          method foldr   fa l = GT.foldr  (llist) fa (this#foldr   fa) l
          method foldl   fa l = GT.foldl  (llist) fa (this#foldl   fa) l
          method gmap    fa l = GT.gmap   (llist) fa (this#gmap    fa) l
          method show    fa l = "[" ^
            let rec inner l =
              (GT.transform(llist) 
                 (GT.lift fa)
                 (GT.lift inner)
                 (object inherit ['a,'a ground] @llist[show]
                    method c_Nil   _ _      = ""
                    method c_Cons  i s x xs = x.GT.fx () ^ (match xs.GT.x with Nil -> "" | _ -> "; " ^ xs.GT.fx ())
                  end) 
                 () 
                 l
              ) 
            in inner l ^ "]"
        end
    }

    let logic = {
      GT.gcata = ();
      GT.plugins = 
        object(this) 
          method html    fa l   = GT.html   (logic') (GT.html   (llist) fa (this#html    fa)) l
          method eq      fa a b = GT.eq     (logic') (GT.eq     (llist) fa (this#eq      fa)) a b
          method compare fa a b = GT.compare(logic') (GT.compare(llist) fa (this#compare fa)) a b
          method foldr   fa a l = GT.foldr  (logic') (GT.foldr  (llist) fa (this#foldr   fa)) a l 
          method foldl   fa a l = GT.foldl  (logic') (GT.foldl  (llist) fa (this#foldl   fa)) a l 
          method gmap    fa l   = GT.gmap   (logic') (GT.gmap   (llist) fa (this#gmap    fa)) l 
          method show    fa l = 
            GT.show(logic')
              (fun l -> "[" ^            
                 let rec inner l =
                   (GT.transform(llist) 
                      (GT.lift fa)
                      (GT.lift (GT.show(logic) inner))
                      (object inherit ['a,'a logic] @llist[show]
                         method c_Nil   _ _      = ""
                         method c_Cons  i s x xs = x.GT.fx () ^ (match xs.GT.x with Value Nil -> "" | _ -> "; " ^ xs.GT.fx ())
                       end) 
                      () 
                      l
                   ) 
                 in inner l ^ "]"
              ) 
              l
        end
    }

    let (!) = (!!)

    (* let rec foldro f a xs r =
      conde [
        (xs === !Nil) &&& (a === r);
        Fresh.three (
          fun h t a'->
            (xs === h % t) &&&
            (f h a' r) &&&
            (foldro f a t a')
        )
      ]

    let rec mapo f xs ys =
      conde [
        (xs === !Nil) &&& (ys === !Nil);
        Fresh.two (
          fun z zs ->
            (xs === z % zs) &&&
            (Fresh.two (
               fun a1 a2 ->
                  (ys === a1 % a2) &&&
                 (f z a1) &&&
                 (mapo f zs a2)
            ))
        )
      ]

    let filtero p xs ys =
      let folder x a a' =
        conde [
          (p x !true) &&& (x % a === a');
          (p x !false) &&& (a === a')
        ]
      in
      foldro folder !Nil xs ys

    let rec lookupo p xs mx =
      conde [
        (xs === !Nil) &&& (mx === !None);
        Fresh.two (
          fun h t ->
             (h % t === xs) &&&
             (conde [
                (p h !true) &&& (mx === !(Some h));
                (p h !false) &&& (lookupo p t mx)
             ])
        )
      ]

    let anyo = foldro Bool.oro !false

    let allo = foldro Bool.ando !true

    let rec lengtho l n =
      conde [
        (l === !Nil) &&& (n === !O);
        Fresh.three (fun x xs n' ->
          (l === x % xs)  &&& 
          (n === !(S n')) &&&
          (lengtho xs n')
        )
      ]
        
    let rec appendo a b ab =
      conde [
        (a === !Nil) &&& (b === ab);
        Fresh.three (fun h t ab' ->
          (a === h%t) &&&
          (h%ab' === ab) &&&
          (appendo t b ab') 
        )   
      ]
  
    let rec reverso a b = 
      conde [
        (a === !Nil) &&& (b === !Nil);
        Fresh.three (fun h t a' ->
          (a === h%t) &&&
          (appendo a' !<h b) &&&
          (reverso t a')
        )
      ]

    let rec membero l a =
      Fresh.two (fun x xs ->
        (l === x % xs) &&&
        (conde [
           x === a;
           (x =/= a) &&& (membero xs a)
         ])
      ) *)
  end

let rec inj_list = function
| []    -> inj Nil
| x::xs -> inj (Cons (inj x, inj_list xs))

let rec prj_list l =
  match prj l with
  | Nil -> []
  | Cons (x, xs) -> prj x :: prj_list xs

let (%)  = List.(%)
let (%<) = List.(%<)
let (!<) = List.(!<)
let nil  = List.nil

let rec inj_nat_list = function
| []    -> !!Nil
| x::xs -> inj_nat x % inj_nat_list xs

let rec prj_nat_list l =
  match prj l with
  | Nil -> []
  | Cons (x, xs) -> prj_nat x :: prj_nat_list xs


(*** Interpretation ***)

module Cash = Map.Make (struct type t = string * bool list let compare = Pervasives.compare end)

module IntSet = Set.Make (struct type t = int let compare = Pervasives.compare end)

let rec known_list : bool list Cash.t ref -> IdentSet.t -> definition list -> string -> bool list -> bool list =
  fun cash iset defs f_name known ->
    try
      let res = Cash.find (f_name, known) (!cash)
      in res
    with
    | Not_found ->
        let args, body = List.assoc f_name defs in
        let start_set = IntSet.of_list @@ List.map (fun (_, t) -> let Some i = IdentSet.id iset t in i) @@ List.filter fst 
                            @@ List.map2 (fun x y -> (x, y)) known args in
        let res_set = known_set cash iset defs f_name body start_set in
        let res = List.map (fun a -> let Some i = IdentSet.id iset a in IntSet.mem i res_set) args in
        (*Printf.printf "from %d " (Cash.cardinal (!cash));*)
        cash := Cash.add (f_name, known) res (!cash);
        (*Printf.printf "to %d\n\n" (Cash.cardinal (!cash));*)
        res
and     known_set         : bool list Cash.t ref -> IdentSet.t -> definition list -> string -> goal -> IntSet.t -> IntSet.t =
  fun cash iset defs f_name goal known ->
    let known_set' g ks = known_set cash iset defs f_name g ks in
    match goal with
    | Unification (t1, t2) ->
        let fv t = IntSet.of_list @@ IdentSet.idents iset t in
        let fv1, fv2 = fv t1, fv t2 in
        if   IntSet.subset fv1 known
        then IntSet.union  fv2 known
        else 
          if   IntSet.subset fv2 known
          then IntSet.union  fv1 known
          else known
    | Disequality _     -> known
    | Disjunction (g::gs) -> List.fold_left IntSet.inter (known_set' g known) (List.map (fun g -> known_set' g known) gs)
    | Fresh (_, g) -> known_set' g known
    | Invoke (name, args) when name = f_name -> IntSet.union known @@ IntSet.of_list @@ List.map (fun (Some x) -> x) 
                                                    @@ List.filter (function None -> false | Some _ -> true) @@ List.map (IdentSet.id iset) args
    | Invoke (name, args) -> 
        let terms = List.map (IdentSet.id iset) args
        in IntSet.union known @@ IntSet.of_list @@ List.map (fun (Some x) -> x) @@ List.filter (function None -> false | Some _ -> true) @@ 
              List.map2 (fun ot f -> if f then ot else None) terms @@ known_list cash iset defs name @@ 
              List.map (function None -> true | Some i -> IntSet.mem i known) terms 
    | Conjunction gs ->
        let walk gs known = List.fold_left (fun ks g -> IntSet.union ks (known_set' g ks)) known gs
        in
        let rec cycle_walk gs known =
          let new_known = walk gs known
          in if IntSet.equal known new_known
             then known
             else cycle_walk gs new_known
        in
        cycle_walk gs known


let rec check_termination : bool list Cash.t ref -> IdentSet.t -> definition list -> string -> bool list -> bool =
  fun cash iset defs f_name known -> 
    let sc = Cash.cardinal (! cash) in
    let res = List.for_all (fun x -> x) @@ known_list cash iset defs f_name known
    in
    (*
      if Cash.cardinal (! cash) <> sc
      then  
      (
        Printf.printf "Cash update:\n";
        Cash.iter (fun (name, bs) ks -> Printf.printf "%s, %s -> %s\n" name ((GT.show(GT.list) (GT.show(GT.bool))) bs) ((GT.show(GT.list) (GT.show(GT.bool))) ks)) (!cash);
        Printf.printf "\n"
      )
      else
        ()
    ); *)
    res

let rec pre_opt goal =
  let rec expand_conj = function
  | []                   -> []
  | Conjunction gs :: tl -> gs @ expand_conj tl
  | hd :: tl             -> hd :: expand_conj tl
  in
  (*let bubble_rec gs =
    let rec helper = function
    | [] -> [], []
    | Invoke (name, ts) :: tl when name = f_name -> let xs, ys = helper tl in       xs, Invoke (name, ts) :: ys
    | hd :: tl                                   -> let xs, ys = helper tl in hd :: xs,                      ys
    in
    let xs, ys = helper gs in xs @ ys 
  in*)
  match goal with
  | Unification _     -> goal
  | Disequality _     -> goal
  | Invoke      _     -> goal
  | Disjunction gs    -> Disjunction (List.map pre_opt gs)
  | Fresh      (x, g) -> Fresh (x, pre_opt g)
  | Conjunction gs    -> Conjunction (expand_conj @@ List.map pre_opt gs)

let rec is_closed_term : State.t -> term -> bool = fun ((env, subst, _) as st) term ->
  let term = Subst.walk env (!!! term) subst in
    match Env.var env term with
    | Some i -> false
    | None ->
        (match wrap (Obj.repr term) with
         | Unboxed _ -> true
         | Boxed (t, s, f) ->
            let rec inner i =
              if i < s
              then (if is_closed_term st (!!! (f i)) then inner (i+1) else false)
              else true
            in inner 0
         | Invalid n -> invalid_arg (Printf.sprintf "Invalid value for reconstruction (%d)" n)
        )

let run_prog (iset, defs, goal) =
  let defs, goal = List.map (fun (name, (args, body)) -> (name, (args, pre_opt body))) defs, pre_opt goal in
  let cash = ref Cash.empty in
  let rec run_goal : IdentSet.t -> goal -> State.t -> State.t Stream.t = fun iset goal ((env, subst, constr) as st) ->
    match goal with
    | Unification (x, y)  -> run_unification (logic_of_term @@ IdentSet.refine env iset x) (logic_of_term @@ IdentSet.refine env iset y) st
    | Disequality (x, y)  -> run_disequality (logic_of_term @@ IdentSet.refine env iset x) (logic_of_term @@ IdentSet.refine env iset y) st
    | Conjunction gs -> 
        let rec run_conj : goal list -> goal list -> bool -> bool -> State.t -> State.t Stream.t = 
          fun goals defer_goals final_flag change_flag st ->
            match goals, defer_goals with
            | [],                        [] -> Stream.cons st Stream.nil
            | [],                        _  -> run_conj (List.rev defer_goals) [] (not change_flag) false st
            | Invoke (name, args) :: gs, _  -> let bs = List.map (fun a -> is_closed_term st @@ IdentSet.refine env iset a) args in
                                               if final_flag || check_termination cash iset defs name bs
                                               then Stream.bind (run_goal iset (Invoke (name, args)) st) (run_conj gs defer_goals final_flag true)
                                               else run_conj gs (Invoke (name, args) :: defer_goals) final_flag change_flag st
            | g::gs                    , _  -> Stream.bind (run_goal iset g st) (run_conj gs defer_goals final_flag true)
        in
        run_conj gs [] false false st
    | Disjunction (g::gs) -> List.fold_left Stream.mplus (run_goal iset g st) (List.map (fun g -> run_goal iset g st) gs)
    | Fresh       (x, g)  -> let var, env' = Env.fresh env in
                             run_goal (IdentSet.bind_ident x (term_of_logic var) iset) g (env', subst, constr)
    | Invoke (name, arg_vals) -> let args, g = List.assoc name defs in
                                 let iset' = List.fold_left2 (fun is a av -> IdentSet.bind_ident a (IdentSet.refine env iset av) is) iset args arg_vals in
                                 Stream.from_fun (fun () -> run_goal iset' g st)
  in
  run_goal iset goal

let rec refine : State.t -> 'a logic -> 'a logic = fun ((e, s, c) as st) x ->  
  let rec walk' recursive env var subst =
    let var = Subst.walk env var subst in
    match Env.var env var with
    | None ->
        (match wrap (Obj.repr var) with
         | Unboxed _ -> !!!var
         | Boxed (t, s, f) ->
            let var = Obj.dup (Obj.repr var) in
            let sf =
              if t = Obj.double_array_tag
              then !!! Obj.set_double_field
              else Obj.set_field
            in
            for i = 0 to s - 1 do
              sf var i (!!!(walk' true env (!!!(f i)) subst))
           done;
           !!!var
         | Invalid n -> invalid_arg (Printf.sprintf "Invalid value for reconstruction (%d)" n)
        )
    | Some i when recursive ->        
        (match var with
         | Var (a, i, _) -> 
            let cs = 
              List.fold_left 
                (fun acc s -> 
                   match walk' false env (!!!var) s with
                   | Var (_, j, _) when i = j -> acc
                   | t -> (refine st t) :: acc
                )       
                []
                c
            in
            Var (a, i, cs)
        )
    | _ -> var
  in
  walk' true e (!!!x) s

module ExtractDeepest = 
  struct
    let ext2 x = x 

    let succ prev (a, z) =
      let foo, base = prev z in
      ((a, foo), base)
  end

module ApplyTuple = 
  struct
    let one arg x = x arg

    let succ prev = fun arg (x, y) -> (x arg, prev arg y)
  end

module ApplyLatest = 
  struct
    let two = (ApplyTuple.one, ExtractDeepest.ext2)

    let apply (appf, extf) tup =
      let x, base = extf tup in
      appf base x

    let succ (appf, extf) = (ApplyTuple.succ appf, ExtractDeepest.succ extf) 
  end

module Uncurry = 
  struct
    let succ k f (x,y) = k (f x) y
  end

type 'a refiner = State.t Stream.t -> 'a logic Stream.t

let refiner : 'a logic -> 'a refiner = fun x ans ->
  Stream.map (fun st -> refine st x) ans

module LogicAdder = 
  struct
    let zero f = run_prog f
 
    let succ (prev: 'a -> State.t -> 'b) (f: 'c logic -> 'a) : State.t -> 'c refiner * 'b =
      call_fresh (fun logic st -> (refiner logic, prev (f logic) st))
  end

let one () = (fun x -> LogicAdder.(succ zero) x), (@@), ApplyLatest.two

let succ n () = 
  let adder, currier, app = n () in
  (LogicAdder.succ adder, Uncurry.succ currier, ApplyLatest.succ app)

let two   () = succ one   ()
let three () = succ two   ()
let four  () = succ three ()
let five  () = succ four  ()

let q     = one
let qr    = two
let qrs   = three
let qrst  = four
let pqrst = five

let run n goalish f =
  let adder, currier, app_num = n () in
  let run f = f (State.empty ()) in
  run (adder goalish) |> ApplyLatest.apply app_num |> (currier f)

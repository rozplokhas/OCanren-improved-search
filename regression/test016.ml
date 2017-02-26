open GT
open MiniKanren
open Tester



(*** Just goals ***)

let id_set0 = IdentSet.empty ()

let a   : int logic = IdentSet.new_ident id_set0 0
let b   : int logic = IdentSet.new_ident id_set0 1
let c   : int logic = IdentSet.new_ident id_set0 2


let just_a = def "just_a" (!^ a)
  (a === !5)

let a_and_b = def "a_and_b" (!^ a) (
  fresh (!^ b) [
    (a === !7);
    (disj (b === !6) (b === !5))
  ]
)

let a_and_b' = def "a_and_b'" (!^ b) (
  fresh (!^ a) [
    (a === !7);
    (disj (b === !6) (b === !5))
  ]
)


(*** Lists ***)

let id_set1 = IdentSet.empty ()

let a   : int logic List.logic = IdentSet.new_ident id_set1 0
let b   : int logic List.logic = IdentSet.new_ident id_set1 1
let ab  : int logic List.logic = IdentSet.new_ident id_set1 2
let h   : int logic            = IdentSet.new_ident id_set1 3
let t   : int logic List.logic = IdentSet.new_ident id_set1 4
let a'  : int logic List.logic = IdentSet.new_ident id_set1 5
let ab' : int logic List.logic = IdentSet.new_ident id_set1 6
let hs  : int logic List.logic = IdentSet.new_ident id_set1 7


let appendo = def "appendo" (a ^~ b ^. ab) (
  conde [
    (a === !Nil) &&& (b === ab);
    fresh (h ^. t) [
      (a === h % t);
      fresh (!^ ab') [(invoke "appendo" (t ^~ b ^. ab')) &&& (h % ab' === ab)]
    ]
  ]
)

let reverso = def "reverso" (a ^. b) (
  disj
    (conj (a === !Nil) (b === !Nil))
    (fresh (h ^. t) [
        conj (a === h % t)
             (fresh (hs ^. a') [
                   (hs === (!< h));
                   (invoke "reverso" (t ^. a'));
                   (invoke "appendo" (a' ^~ hs ^. b))
              ])
    ])
)


(*** Sorting ***)

let id_set2 = IdentSet.empty ()

let x   : Nat.logic            = IdentSet.new_ident id_set2 0
let y   : Nat.logic            = IdentSet.new_ident id_set2 1
let x'  : Nat.logic            = IdentSet.new_ident id_set2 2
let y'  : Nat.logic            = IdentSet.new_ident id_set2 3
let min : Nat.logic            = IdentSet.new_ident id_set2 4
let max : Nat.logic            = IdentSet.new_ident id_set2 5
let l   : Nat.logic List.logic = IdentSet.new_ident id_set2 6
let s   : Nat.logic            = IdentSet.new_ident id_set2 7
let l'  : Nat.logic List.logic = IdentSet.new_ident id_set2 8
let h   : Nat.logic            = IdentSet.new_ident id_set2 9
let t   : Nat.logic List.logic = IdentSet.new_ident id_set2 10
let s'  : Nat.logic            = IdentSet.new_ident id_set2 11
let t'  : Nat.logic List.logic = IdentSet.new_ident id_set2 12
let xs  : Nat.logic List.logic = IdentSet.new_ident id_set2 13
let ys  : Nat.logic List.logic = IdentSet.new_ident id_set2 14
let xs' : Nat.logic List.logic = IdentSet.new_ident id_set2 15
let ys' : Nat.logic List.logic = IdentSet.new_ident id_set2 16
let m   : Nat.logic            = IdentSet.new_ident id_set2 17
let zs  : Nat.logic List.logic = IdentSet.new_ident id_set2 18
let z   : Nat.logic            = IdentSet.new_ident id_set2 19
let z'  : Nat.logic            = IdentSet.new_ident id_set2 20

let lto = def "lto" (x ^. y) (
  conde [
    fresh (!^ y') [(x === !O) &&& (y === !(S y'))];
    fresh (x' ^. y') [
      (x === !(S x'));
      (y === !(S y'));
      (invoke "lto" (x' ^. y'))
    ]
  ]
)

let geo = def "geo" (x ^. y) (
  (x === y) ||| (invoke "lto" (y ^. x))
)

let minimumo = def "minimumo" (xs ^. m) (
  conde [
    (xs === !< m);
    fresh (x ^~ t ^. y) [
      (xs === x % t);
      (invoke "minimumo" (t ^. y));
      (conde [
        (invoke "lto" (x ^. y)) &&& (x === m);
        (invoke "geo" (x ^. y)) &&& (y === m) 
      ])
    ]
  ]
)

let minmaxo = def "minmaxo" (x ^~ y ^~ min ^. max) (
  conde [
    (x === min) &&& (y === max) &&& (invoke "lto" (x ^. y));
    (y === min) &&& (x === max) &&& (invoke "geo" (x ^. y))
  ]
)

let smallesto = def "smallesto" (l ^~ s ^. l') (
  conde [       
    (l === !< s) &&& (l' === !Nil);
    fresh (h ^~ t ^~ s' ^~ t' ^. max) [
      (l' === max % t');
      (l === h % t);
      (invoke "smallesto" (t ^~ s' ^. t'));
      (invoke "minmaxo" (h ^~ s' ^~ s ^. max))
    ]
  ]
)

let sorto = def "sorto" (xs ^. ys) (
  conde [
    (xs === !Nil) &&& (ys === !Nil);
    fresh (s ^~ xs' ^. ys') [
      (invoke "smallesto" (xs ^~ s ^. xs'));
      (ys === s % ys');
      (invoke "sorto" (xs' ^. ys'))
    ]
  ]
)


(*** Peano arithmetic ***)

let pluso = def "pluso" (x ^~ y ^. z) (
  conde [
    (x === !O) &&& (y === z);
    fresh (x' ^. z') [
      (x === !(S x'));
      (z === !(S z'));
      (invoke "pluso" (x' ^~ y ^. z'))
    ]
  ]
)

let mulo = def "mulo" (x ^~ y ^. z) (
  conde [
    (x === !O) &&& (z === !O);
    fresh (!^ x') [(x === !(S x')) &&& (y === !O) &&& (z === !O)];
    fresh (x' ^~ z' ^. y') [
      (x === !(S x'));
      (y === !(S y'));
      (invoke "mulo"  (x' ^~ y ^. z'));
      (invoke "pluso" (z' ^~ y ^. z))
    ]
  ]
)

let map_succ = def "map_succ" (xs ^. ys) (
  conde [
    (xs === !Nil) &&& (ys === !Nil);
    fresh (x ^~ xs' ^~ y ^. ys') [
      (xs === x % xs');
      (y === !(S x));
      (invoke "map_succ" (xs' ^. ys'));
      (ys === y % ys')
    ]
  ]
)


(*** Binary arithmetic ***)

let id_set3 = IdentSet.empty ()

let x   : int logic List.logic = IdentSet.new_ident id_set3 0
let y   : int logic List.logic = IdentSet.new_ident id_set3 1
let r   : int logic List.logic = IdentSet.new_ident id_set3 2
let x'  : int logic List.logic = IdentSet.new_ident id_set3 3
let y'  : int logic List.logic = IdentSet.new_ident id_set3 4
let r'  : int logic List.logic = IdentSet.new_ident id_set3 5
let h   : int logic            = IdentSet.new_ident id_set3 6
let t   : int logic List.logic = IdentSet.new_ident id_set3 7
let r'' : int logic List.logic = IdentSet.new_ident id_set3 8
let d   : int logic List.logic = IdentSet.new_ident id_set3 9
let q'  : int logic List.logic = IdentSet.new_ident id_set3 9
let n   : int logic List.logic = IdentSet.new_ident id_set3 10
let n'  : int logic List.logic = IdentSet.new_ident id_set3 11


let rec to_bin = (function
| 0 -> !Nil
| n when n mod 2 = 0 -> !0 % to_bin (n / 2)
| n                  -> !1 % to_bin (n / 2)
)

let poso = def "poso" (!^ x) (
  fresh (h ^. t) [
    (x === h % t)
  ]
)

let bin_pluso = def "bin_pluso" (x ^~ y ^. r) (
  conde [
    (y === !Nil) &&& (x === r);
    (x === !Nil) &&& (invoke "poso" (!^ y)) &&& (y === r);
    (fresh (x' ^~ y' ^. r') [
      (x === !0 % x');
      (y === !0 % y');
      (r === !0 % r');
      (invoke "poso" (!^ x'));
      (invoke "poso" (!^ y'));
      (invoke "bin_pluso" (x' ^~ y' ^. r'))
    ]);
    (fresh (x' ^~ y' ^. r') [
      (x === !0 % x');
      (y === !1 % y');
      (r === !1 % r');
      (invoke "poso" (!^ x'));
      (invoke "bin_pluso" (x' ^~ y' ^. r'))
    ]);
    (fresh (x' ^~ y' ^. r') [
      (x === !1 % x');
      (y === !0 % y');
      (r === !1 % r');
      (invoke "poso" (!^ y'));
      (invoke "bin_pluso" (x' ^~ y' ^. r'))
    ]);
    (fresh (x' ^~ y' ^~ r' ^. r'') [
      (x === !1 % x');
      (y === !1 % y');
      (r === !0 % r');
      (invoke "bin_pluso" (x' ^~ y' ^. r''));
      (invoke "bin_pluso" (r'' ^~ (!< (!1)) ^. r'))
    ])
  ]
)

let bin_multo = def "bin_multo" (x ^~ y ^. r) (
  conde [
    (x === !Nil) &&& (r === !Nil);
    (invoke "poso" (!^ x)) &&& (y === !Nil) &&& (r === !Nil);
    (invoke "poso" (!^ x)) &&& (y === !< !1) &&& (r === x);
    (fresh (y' ^. r') [
      (invoke "poso" (!^ x));
      (y === !0 % y');
      (invoke "poso" (!^ y'));
      (invoke "bin_multo" (x ^~ y' ^. r'));
      (r === !0 % r')
    ]);
    (fresh (y' ^~ r' ^. r'') [
      (invoke "poso" (!^ x));
      (y === !1 % y');
      (invoke "poso" (!^ y'));
      (invoke "bin_multo" (x ^~ y' ^. r'));
      (r'' === !0 % r');
      (invoke "bin_pluso" (r'' ^~ x ^. r))
    ])
  ]  
)

let bin_lto = def "bin_lto" (x ^. y) (
  fresh (!^ d) [
    (invoke "poso" (!^ d));
    (invoke "bin_pluso" (x ^~ d ^. y))
  ]
)

let bin_divo = def "bin_divo" (x ^~ y ^~ q' ^. r) (
  fresh (!^ z) [
    (invoke "bin_lto"   (r ^. y));
    (invoke "bin_multo" (q' ^~ y ^. z));
    (invoke "bin_pluso" (z ^~ r ^. x))
  ]
)

let bin_powo = def "bin_powo" (x ^~ n ^. r) (
  conde [
    (n === !Nil) &&& (r === !< !1);
    fresh (n' ^. r') [
      (invoke "bin_pluso" (n' ^~ (!< !1) ^. n));
      (invoke "bin_powo"  (x ^~ n' ^. r'));
      (invoke "bin_multo" (r' ^~ x ^. r))
    ]
  ]
)

let show_int           = show (logic) (show int)
let show_int_list      = show (List.logic) show_int
let show_nat           = show (Nat.logic)
let show_nat_list      = show (List.logic) show_nat
let show_nat_gr      n = show int @@ prj_nat n
let show_nat_list_gr l = show list (show int) @@ prj_nat_list l

let reverso_list   = [appendo; reverso]
let minimumo_list  = [geo; lto; minimumo]
let sorto_list     = [lto; geo; minmaxo; smallesto; sorto]
let bin_pluso_list = [poso; bin_pluso]
let bin_multo_list = [poso; bin_pluso; bin_multo]
let bin_lto_list   = [poso; bin_pluso; bin_lto]
let bin_divo_list  = [poso; bin_pluso; bin_lto; bin_multo; bin_divo]
let bin_powo_list  = [poso; bin_pluso; bin_multo; bin_powo]

let _ =
  run show_int         (-1) q   (REPR (fun q     -> prog id_set0 [just_a  ]     (invoke "just_a"    (!^ q))                                               )) qh;
  run show_int         (-1) q   (REPR (fun q     -> prog id_set0 [a_and_b ]     (invoke "a_and_b"   (!^ q))                                               )) qh;
  run show_int         (-1) q   (REPR (fun q     -> prog id_set0 [a_and_b']     (invoke "a_and_b'"  (!^ q))                                               )) qh;

  run show_int_list    (-1) q   (REPR (fun q     -> prog id_set0 [appendo ]     (invoke "appendo"   (inj_list [1; 2] ^~ inj_list [3; 4]  ^. q))           )) qh;
  run show_int_list    (-1) q   (REPR (fun q     -> prog id_set0 [appendo ]     (invoke "appendo"   (q ^~ inj_list [3; 4]  ^. inj_list [1; 2; 3; 4]))     )) qh;
  
  run show_int_list    (-1) q   (REPR (fun q     -> prog id_set1 reverso_list   (invoke "reverso"   (q ^. inj_list [5; 4; 3; 2; 1]))                      )) qh;
  run show_int_list    (-1) q   (REPR (fun q     -> prog id_set1 reverso_list   (invoke "reverso"   (inj_list [1; 2; 3; 4; 5] ^. q))                      )) qh;
  run show_int_list    (-1) q   (REPR (fun q     -> prog id_set1 reverso_list   (invoke "reverso"   (inj_list [1; 2; 3] ^. inj_list [3; 2; 1]))           )) qh;
  run show_int_list    (-1) q   (REPR (fun q     -> prog id_set1 reverso_list   (invoke "reverso"   (inj_list [1; 2; 1] ^. inj_list [3; 2; 1]))           )) qh;

  run show_nat_gr      (-1) q   (REPR (fun q     -> prog id_set2 minimumo_list  (invoke "minimumo"  (inj_nat_list [6; 5; 4; 1; 2] ^. q))                  )) qh;
  run show_nat_gr      (-1) q   (REPR (fun q     -> prog id_set2 minimumo_list  (invoke "minimumo"  (inj_nat_list [] ^. q))                               )) qh;

  run show_nat_list_gr (-1) q   (REPR (fun q     -> prog id_set2 sorto_list     (invoke "sorto"     (inj_nat_list [8; 9; 10; 7; 6; 5; 4; 1; 2; 3] ^. q))  )) qh;
  run show_nat_list_gr (-1) q   (REPR (fun q     -> prog id_set2 sorto_list     (invoke "sorto"     (q ^. inj_nat_list [1; 2; 3; 4; 5; 6]))               )) qh;
  
  run show_nat_gr      (-1) q   (REPR (fun q     -> prog id_set2 [pluso]        (invoke "pluso"     (inj_nat 6 ^~ inj_nat 4 ^. q))                        )) qh;
  run show_nat_gr      (-1) qr  (REPR (fun q r   -> prog id_set2 [pluso]        (invoke "pluso"     (q ^~ r ^. inj_nat 10))                               )) qrh;
  run show_nat_gr      (-1) q   (REPR (fun q     -> prog id_set2 [pluso; mulo]  (invoke "mulo"      (inj_nat 3 ^~ inj_nat 5 ^. q))                        )) qh;
  run show_nat_gr      (-1) qr  (REPR (fun q r   -> prog id_set2 [pluso; mulo]  (invoke "mulo"      (q ^~ r ^. inj_nat 16))                               )) qrh;
  
  run show_nat_list_gr (-1) q   (REPR (fun q     -> prog id_set2 [map_succ]     (invoke "map_succ"  (inj_nat_list [1; 2; 3; 4; 5; 6; 7; 8; 9; 10] ^. q))  )) qh;
  run show_nat_list_gr (-1) q   (REPR (fun q     -> prog id_set2 [map_succ]     (invoke "map_succ"  (q ^. inj_nat_list [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]))  )) qh;

  run show_int_list    (-1) q   (REPR (fun q     -> prog id_set3 bin_pluso_list (invoke "bin_pluso" ((to_bin 3) ^~ (to_bin 6) ^. q))                      )) qh;
  run show_int_list    (-1) q   (REPR (fun q     -> prog id_set3 bin_pluso_list (invoke "bin_pluso" ((to_bin 2) ^~ q ^. (to_bin 5)))                      )) qh;
  run show_int_list    (-1) q   (REPR (fun q     -> prog id_set3 bin_pluso_list (invoke "bin_pluso" ((to_bin 8) ^~ q ^. (to_bin 6)))                      )) qh;
  run show_int_list    (-1) q   (REPR (fun q     -> prog id_set3 bin_pluso_list (invoke "bin_pluso" (q ^~ (to_bin 5) ^. (to_bin 8)))                      )) qh;
  run show_int_list    (-1) qr  (REPR (fun q r   -> prog id_set3 bin_pluso_list (invoke "bin_pluso" (q ^~ r  ^. (to_bin 5)))                              )) qrh;
  
  run show_int_list    (-1) q   (REPR (fun q     -> prog id_set3 bin_multo_list (invoke "bin_multo" ((to_bin 5) ^~ (to_bin 3) ^. q))                      )) qh;
  run show_int_list    (-1) q   (REPR (fun q     -> prog id_set3 bin_multo_list (invoke "bin_multo" (q ^~ (to_bin 3) ^. (to_bin 12)))                     )) qh;
  run show_int_list    (-1) q   (REPR (fun q     -> prog id_set3 bin_multo_list (invoke "bin_multo" ((to_bin 3) ^~ q ^. (to_bin 12)))                     )) qh;
  run show_int_list    (-1) qr  (REPR (fun q r   -> prog id_set3 bin_multo_list (invoke "bin_multo" (q ^~ r ^. (to_bin 24)))                              )) qrh;

  run show_int_list    (-1) q   (REPR (fun q     -> prog id_set3 bin_lto_list   (invoke "bin_lto"   ((to_bin 5) ^. (to_bin 10)))                          )) qh;
  run show_int_list    (-1) q   (REPR (fun q     -> prog id_set3 bin_lto_list   (invoke "bin_lto"   ((to_bin 6) ^. (to_bin 6) ))                          )) qh;
  run show_int_list    (-1) q   (REPR (fun q     -> prog id_set3 bin_lto_list   (invoke "bin_lto"   ((to_bin 15) ^. (to_bin 4) ))                         )) qh;
  run show_int_list    (-1) q   (REPR (fun q     -> prog id_set3 bin_lto_list   (invoke "bin_lto"   (q          ^. (to_bin 13)))                          )) qh;

  run show_int_list    (-1) qr  (REPR (fun q r   -> prog id_set3 bin_divo_list  (invoke "bin_divo"  ((to_bin 21) ^~ (to_bin 7) ^~ q ^. r))                )) qrh;
  run show_int_list    (-1) qr  (REPR (fun q r   -> prog id_set3 bin_divo_list  (invoke "bin_divo"  ((to_bin 23) ^~ (to_bin 5) ^~ q ^. r))                )) qrh;
  run show_int_list    (-1) qrs (REPR (fun q r s -> prog id_set3 bin_divo_list ((invoke "bin_lto"   ((to_bin 0) ^. r)) &&& 
                                                                                                        (invoke "bin_divo" ((to_bin 5) ^~ q ^~ r ^. s)))  )) qrsh;

  run show_int_list    (-1) q   (REPR (fun q     -> prog id_set3 bin_powo_list  (invoke "bin_powo"  ((to_bin 3) ^~ (to_bin 4) ^. q))                      )) qh;
  run show_int_list    (-1) q   (REPR (fun q     -> prog id_set3 bin_powo_list  (invoke "bin_powo"  (q          ^~ (to_bin 3) ^. (to_bin 125)))           )) qh;

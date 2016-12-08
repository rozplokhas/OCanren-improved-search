open GT
open MiniKanren
open Tester



(*** Just goals ***)

let a   : int logic = new_ident 0
let b   : int logic = new_ident 1
let c   : int logic = new_ident 2


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

let fives = def "fives" (!^ c) (
  disj (c === !5)
       (invoke "fives" (!^ c))
)


(*** Lists ***)

let a   : int logic List.logic = new_ident 0
let b   : int logic List.logic = new_ident 1
let ab  : int logic List.logic = new_ident 2
let h   : int logic            = new_ident 3
let t   : int logic List.logic = new_ident 4
let a'  : int logic List.logic = new_ident 5
let ab' : int logic List.logic = new_ident 6


let appendo = def "appendo" (a ^~ b ^. ab) (
  conde [
    (a === !Nil) &&& (b === ab);
    fresh (h ^. t) [
      (a === h % t);
      fresh (!^ ab') [(h % ab' === ab) &&& (invoke "appendo" (t ^~ b ^. ab'))]
    ]
  ]
)

let reverso = def "reverso" (a ^. b) (
  disj
    (conj (a === !Nil) (b === !Nil))
    (fresh (h ^. t) [
        conj (a === h % t)
             (fresh (!^ a') [
                   conj 
                   (invoke "appendo" (a' ^~ (!< h) ^. b)) 
                   (invoke "reverso" (t ^. a'))
                        
                        
              ])
    ])
)


(*** Sorting ***)

let x   : Nat.logic            = new_ident 0
let y   : Nat.logic            = new_ident 1
let x'  : Nat.logic            = new_ident 2
let y'  : Nat.logic            = new_ident 3
let min : Nat.logic            = new_ident 4
let max : Nat.logic            = new_ident 5
let l   : Nat.logic List.logic = new_ident 6
let s   : Nat.logic            = new_ident 7
let l'  : Nat.logic List.logic = new_ident 8
let h   : Nat.logic            = new_ident 9
let t   : Nat.logic List.logic = new_ident 10
let s'  : Nat.logic            = new_ident 11
let t'  : Nat.logic List.logic = new_ident 12
let xs  : Nat.logic List.logic = new_ident 13
let ys  : Nat.logic List.logic = new_ident 14
let xs' : Nat.logic List.logic = new_ident 15
let ys' : Nat.logic List.logic = new_ident 16
let m   : Nat.logic            = new_ident 17
let zs  : Nat.logic List.logic = new_ident 18
let z   : Nat.logic            = new_ident 19
let z'  : Nat.logic            = new_ident 20


let leo = def "leo" (x ^. y) (
  conde [
    (x === !O);
    fresh (x' ^. y') [
      (x === !(S x'));
      (y === !(S y'));
      (invoke "leo" (x' ^. y'))
    ]
  ]
)

let gto = def "gto" (x ^. y) (
  (x =/= y) &&& (invoke "leo" (y ^. x))
)

let minimumo = def "minimumo" (xs ^. m) (
  conde [
    (xs === !< m);
    fresh (x ^~ t ^. y) [
      (xs === x % t);
      (conde [
        (invoke "leo" (x ^. y)) &&& (x === m);
        (invoke "gto" (x ^. y)) &&& (y === m) 
      ]);
      (invoke "minimumo" (t ^. y))
    ]
  ]
)

let minmaxo = def "minmaxo" (x ^~ y ^~ min ^. max) (
  conde [
    (x === min) &&& (y === max) &&& (invoke "leo" (x ^. y));
    (y === min) &&& (x === max) &&& (invoke "gto" (x ^. y))
  ]
)

let smallesto = def "smallesto" (l ^~ s ^. l') (
  conde [       
    (l === !< s) &&& (l' === !Nil);
    fresh (h ^~ t ^~ s' ^~ t' ^. max) [
      (l' === max % t');
      (l === h % t);
      (invoke "minmaxo" (h ^~ s' ^~ s ^. max));
      (invoke "smallesto" (t ^~ s' ^. t'))
    ]
  ]
)

let sorto = def "sorto" (xs ^. ys) (
  conde [
    (xs === !Nil) &&& (ys === !Nil);
    fresh (s ^~ xs' ^. ys') [
      (ys === s % ys');
      (invoke "sorto" (xs' ^. ys'));
      (invoke "smallesto" (xs ^~ s ^. xs'))
    ]
  ]
)

let perm = def "perm" (xs ^. ys) (
  fresh (!^ zs) [(invoke "sorto" (xs ^. zs)) &&& (invoke "sorto" (ys ^. zs))]
)


(*** Arithmetic ***)

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
    fresh (x' ^. z') [
      (x === !(S x'));
      (invoke "pluso" (z' ^~ y ^. z));
      (invoke "mulo"  (x' ^~ y ^. z'))
      
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


let show_int           = show (logic) (show int)
let show_int_list      = show (List.logic) show_int
let show_nat           = show (Nat.logic)
let show_nat_list      = show (List.logic) show_nat
let show_nat_gr      n = show int @@ prj_nat n
let show_nat_list_gr l = show list (show int) @@ prj_nat_list l

let _ =
  run show_int         (-1) q  (REPR (fun q   -> prog [just_a          ]   (invoke "just_a"    (!^ q))                                            )) qh;
  run show_int         (-1) q  (REPR (fun q   -> prog [a_and_b         ]   (invoke "a_and_b"   (!^ q))                                            )) qh;
  run show_int         (-1) q  (REPR (fun q   -> prog [a_and_b'        ]   (invoke "a_and_b'"  (!^ q))                                            )) qh;
  run show_int          10  q  (REPR (fun q   -> prog [fives           ]   (invoke "fives"     (!^ q))                                            )) qh;

  run show_int_list    (-1) q  (REPR (fun q   -> prog [appendo         ]   (invoke "appendo"   (q ^~ inj_list [3; 4]  ^. inj_list [1; 2; 3; 4]))  )) qh;
  run show_int_list      4  qr (REPR (fun q r -> prog [appendo         ]   (invoke "appendo"   (q ^~ inj_list []      ^. r))                      )) qrh;
  
  run show_int_list      1  q  (REPR (fun q   -> prog [appendo; reverso]   (invoke "reverso"   (q ^. inj_list [1; 2; 3; 4]))                      )) qh;
  run show_int_list    (-1) q  (REPR (fun q   -> prog [appendo; reverso]   (invoke "reverso"   (inj_list [] ^. inj_list []))                      )) qh;
  run show_int_list      1  q  (REPR (fun q   -> prog [appendo; reverso]   (invoke "reverso"   (inj_list [1; 2; 3; 4] ^. q))                      )) qh;
  run show_int_list      1  q  (REPR (fun q   -> prog [appendo; reverso]   (invoke "reverso"   (q ^. q))                                          )) qh;
  run show_int_list      2  q  (REPR (fun q   -> prog [appendo; reverso]   (invoke "reverso"   (q ^. q))                                          )) qh;
  run show_int_list      3  q  (REPR (fun q   -> prog [appendo; reverso]   (invoke "reverso"   (q ^. q))                                          )) qh;
  run show_int_list     10  q  (REPR (fun q   -> prog [appendo; reverso]   (invoke "reverso"   (q ^. q))                                          )) qh;
  run show_int_list   (-1)  q  (REPR (fun q   -> prog [appendo; reverso]   (invoke "reverso"   (q ^. inj_list [1]))                               )) qh;
  run show_int_list      1  q  (REPR (fun q   -> prog [appendo; reverso]   (invoke "reverso"   (inj_list [1] ^. q))                               )) qh;

  run show_nat         (-1) q  (REPR (fun q   -> prog [gto; leo; minimumo] (invoke "minimumo"  (inj_nat_list [6; 5; 4; 1; 2] ^. q))               )) qh;
  run show_nat_list      5  q  (REPR (fun q   -> prog [gto; leo; minimumo] (invoke "minimumo"  (q ^. inj_nat 4))                                  )) qh;
  
  run show_nat_list_gr   1  q  (REPR (fun q   -> prog [leo; gto; minmaxo; smallesto; sorto]
                                                    (invoke "sorto"  (inj_nat_list [3; 1; 4; 2] ^. q))                                            )) qh;
  run show_nat_list_gr (-1) q  (REPR (fun q   -> prog [leo; gto; minmaxo; smallesto; sorto]
                                                    (invoke "sorto"  (q ^. inj_nat_list [1; 2; 3; 4; 5; 6]))                                      )) qh;
  run show_nat_list_gr   6  q  (REPR (fun q   -> prog [leo; gto; minmaxo; smallesto; sorto; perm]
                                                    (invoke "perm"  (q ^. inj_nat_list [2; 3; 1]))                                                )) qh;

  run show_nat_gr      (-1) qr (REPR (fun q r -> prog [pluso]              (invoke "pluso"     (q ^~ r ^. inj_nat 4))                             )) qrh;
  run show_nat_gr        1  q  (REPR (fun q   -> prog [pluso; mulo]        (invoke "mulo"      (inj_nat 3 ^~ inj_nat 5 ^. q))                     )) qh;
  run show_nat_gr        1  q  (REPR (fun q   -> prog [pluso; mulo]        (invoke "mulo"      (q ^~ q ^. inj_nat 16))                            )) qh;
  run show_nat_gr        1  q  (REPR (fun q   -> prog [pluso; mulo]        (invoke "mulo"      (q ^~ q ^. inj_nat 15))                            )) qh;

  run show_nat_list_gr (-1)  q  (REPR (fun q   -> prog [map_succ]           (invoke "map_succ"  (inj_nat_list [1; 2; 3; 4; 5] ^. q))              )) qh;
  run show_nat_list_gr   1  q  (REPR (fun q   -> prog [map_succ]           (invoke "map_succ"  (q ^. inj_nat_list [1; 2; 3; 4; 5]))               )) qh;


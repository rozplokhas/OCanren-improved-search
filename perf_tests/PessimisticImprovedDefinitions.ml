open GT
open MiniKanren

@type tree = Leaf | Node of tree logic * tree logic with show

let show_tree = show(logic) (show tree)

let (!)   = inj
let (!!!) = Obj.magic


(* Relations on lists *)

let rec appendo a b ab = relation "appendo" [!!! a; !!! b; !!! ab] @@
  conde [
    (a === !Nil) &&& (b === ab);
    fresh (h t ab') (?& [
      (a === h % t); 
      (appendo t b ab');
      (h % ab' === ab);
    ])
  ]

let rec reverso a b = relation "reverso" [!!! a; !!! b] @@
  conde [
    (a === !Nil) &&& (b === !Nil);
    fresh (h t a') (?& [
      (a === h % t);
      (reverso t a');
      (appendo a' !<h b);
    ])
  ]


(* Sorting *)

let rec leo a b = relation "leo" [!!! a; !!! b] @@
  conde [
    (a === !O);
    fresh (a' b') ( ?&[
      (a === !(S a'));
      (b === !(S b'));
      (leo a' b')
    ])
  ]

let rec lto a b = relation "lto" [!!! a; !!! b] @@
  conde [
    fresh (b') (?& [
      (a === !O);
      (b === !(S b'))
    ]);
    fresh (a' b') (?& [
      (a === !(S a'));
      (b === !(S b'));
      (lto a' b')
    ])
  ]

let minmaxo a b min max =
    conde [
      (min === a) &&& (max === b) &&& (leo a b);
      (max === a) &&& (min === b) &&& (lto b a)
    ]

let rec smallesto_direct l s l' = relation "smallesto_direct" [!!! l; !!! s; !!! l'] @@
  conde [       
    (l === !< s) &&& (l' === !Nil);
    fresh (h t s' t' max) ( ?&[
      (l === h % t);
      (smallesto_direct t s' t');
      (minmaxo h s' s max);
      (l' === max % t');
    ])
  ]

let rec smallesto_reversed l s l' = relation "smallesto_reversed" [!!! l; !!! s; !!! l'] @@
  conde [       
    (l === !< s) &&& (l' === !Nil);
    fresh (h t s' t' max) ( ?&[
      (l' === max % t');
      (minmaxo h s' s max);
      (smallesto_reversed t s' t');
      (l === h % t);
    ])
  ]

let rec sorto_direct xs ys = relation "sorto_direct" [!!! xs; !!! ys] @@
  conde [
    (xs === !Nil) &&& (ys === !Nil);
    fresh (s xs' ys') (?& [
      (smallesto_direct xs s xs');
      (sorto_direct xs' ys');
      (ys === s % ys');
    ])
  ]

let rec sorto xs ys = relation "sorto" [!!! xs; !!! ys] @@
  conde [
    (xs === !Nil) &&& (ys === !Nil);
    fresh (s xs' ys') (?& [
      (ys === s % ys');
      (sorto xs' ys');
      (smallesto_reversed xs s xs');
    ])
  ]

let permo xs ys =
  fresh (ss)
    ((sorto_direct ys ss) &&& (sorto xs ss))


(* Binary  arithmetic *)

let poso x = fresh (h t) (x === h % t)

let rec pluso x y r = relation "pluso" [!!! x; !!! y; !!! r] @@
  conde [
    (y === !Nil) &&& (x === r);
    (x === !Nil) &&& (poso y) &&& (y === r);
    fresh (x' y' r') (?& [
      (x === !0 % x');
      (y === !0 % y');
      (r === !0 % r');
      (poso x');
      (poso y');
      (pluso x' y' r');
    ]);
    fresh (x' y' r') (?& [
      (x === !0 % x');
      (y === !1 % y');
      (r === !1 % r');
      (poso x');
      (pluso x' y' r');
    ]);
    fresh (x' y' r') (?& [
      (x === !1 % x');
      (y === !0 % y');
      (r === !1 % r');
      (poso y');
      (pluso x' y' r');
    ]);
    fresh (x' y' r' r'') (?& [
      (x === !1 % x');
      (y === !1 % y');
      (r === !0 % r');
      (pluso x' y' r'');
      (pluso r'' (!< (!1)) r');
    ])
  ]

let rec multo x y r = relation "multo" [!!! x; !!! y; !!! r] @@
  conde [
    (x === !Nil) &&& (r === !Nil);
    (poso x) &&& (y === !Nil) &&& (r === !Nil);
    (poso x) &&& (y === !< !1) &&& (r === x);
    fresh (y' r') (?& [
      (poso x);
      (y === !0 % y');
      (poso y');
      (multo x y' r');
      (r === !0 % r');
    ]);
    fresh (y' r' r'') (?& [
      (poso x);
      (y === !1 % y');
      (poso y');
      (multo x y' r');
      (r'' === !0 % r');
      (pluso r'' x r);
    ])
  ]

let rec pluso_reversed x y r = relation "pluso_reversed" [!!! x; !!! y; !!! r] @@
  conde [
    (y === !Nil) &&& (x === r);
    (x === !Nil) &&& (poso y) &&& (y === r);
    fresh (x' y' r') (?& [
      (x === !0 % x');
      (y === !0 % y');
      (r === !0 % r');
      (poso x');
      (poso y');
      (pluso_reversed x' y' r');
    ]);
    fresh (x' y' r') (?& [
      (x === !0 % x');
      (y === !1 % y');
      (r === !1 % r');
      (poso x');
      (pluso_reversed x' y' r');
    ]);
    fresh (x' y' r') (?& [
      (x === !1 % x');
      (y === !0 % y');
      (r === !1 % r');
      (poso y');
      (pluso_reversed x' y' r');
    ]);
    fresh (x' y' r' r'') (?& [
      (x === !1 % x');
      (y === !1 % y');
      (r === !0 % r');
      (pluso_reversed r'' (!< (!1)) r');
      (pluso_reversed x' y' r'');
    ])
  ]

let lto x y = relation "lto" [!!! x; !!! y] @@
  fresh (d) (?& [
    (poso d);
    (pluso_reversed x d y)
  ])

let divo x y q' r = relation "divo" [!!! x; !!! y] @@
  fresh (z) (?& [
    (lto r y);
    (multo q' y z);
    (pluso z r x);
  ])


(*** Binary trees ***)

let rec leaveso t n = relation "leaveso" [!!! t; !!! n] @@
  conde [
    (t === !Leaf) &&& (n === !< (!1));
    fresh (lt ln rt rn) (?& [
      (t === !(Node (lt, rt)));
      (poso ln);
      (poso rn);
      (leaveso lt ln);
      (leaveso rt rn);
      (pluso ln rn n);
    ])
  ]

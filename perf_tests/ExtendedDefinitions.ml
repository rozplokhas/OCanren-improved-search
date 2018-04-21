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

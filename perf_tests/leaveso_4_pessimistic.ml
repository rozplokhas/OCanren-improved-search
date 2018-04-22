open GT
open MiniKanren
open Tester
open PessimisticDefinitions
     
let _ = run show_tree 5 q (REPR (fun q -> leaveso q (inj_list [0; 0; 1]))) qh;

open GT
open MiniKanren
open Tester
open PessimisticDefinitions
     
let _ = run show_tree 14 q (REPR (fun q -> leaveso q (inj_list [1; 0; 1]))) qh;

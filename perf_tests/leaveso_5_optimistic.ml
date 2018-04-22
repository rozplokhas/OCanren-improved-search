open GT
open MiniKanren
open Tester
open OptimisticDefinitions
     
let _ = run show_tree (-1) q (REPR (fun q -> leaveso q (inj_list [1; 0; 1]))) qh;

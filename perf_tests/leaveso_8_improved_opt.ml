open GT
open MiniKanren
open Tester
open OptimisticImprovedDefinitions
     
let _ = run show_tree (-1) q (REPR (fun q -> leaveso q (inj_list [0; 0; 0; 1]))) qh;

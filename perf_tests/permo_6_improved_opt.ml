open GT
open MiniKanren
open Tester
open OptimisticImprovedDefinitions
     
let _ = run show_nat_list (-1) q (REPR (fun q -> permo (inj_nat_list (rnats 6)) q)) qh;

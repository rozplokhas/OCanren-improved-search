open GT
open MiniKanren
open Tester
open OptimisticDefinitions
     
let _ = run show_nat_list (-1) q (REPR (fun q -> sorto (inj_nat_list (rnats 3)) q)) qh

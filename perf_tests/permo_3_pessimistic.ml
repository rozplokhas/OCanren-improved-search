open GT
open MiniKanren
open Tester
open PessimisticDefinitions
     
let _ = run show_nat_list 6 q (REPR (fun q -> permo (inj_nat_list (rnats 3)) q)) qh;

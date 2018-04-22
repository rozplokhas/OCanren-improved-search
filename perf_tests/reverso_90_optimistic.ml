open GT
open MiniKanren
open Tester
open OptimisticDefinitions
     
let _ = run show_int_list (-1) q (REPR (fun q -> reverso q (inj_list (nats 90)))) qh;

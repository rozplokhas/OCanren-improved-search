open GT
open MiniKanren
open Tester
open OptimisticImprovedDefinitions
     
let _ = run show_int_list (-1) qr (REPR (fun q r -> multo q r (inj_list [1; 1; 1; 1; 1]))) qrh;

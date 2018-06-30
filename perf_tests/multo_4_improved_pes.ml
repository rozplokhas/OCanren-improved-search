open GT
open MiniKanren
open Tester
open PessimisticImprovedDefinitions
     
let _ = run show_int_list (-1) qr (REPR (fun q r -> multo q r (inj_list [1; 1; 1; 1]))) qrh;

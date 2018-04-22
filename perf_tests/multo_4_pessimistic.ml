open GT
open MiniKanren
open Tester
open PessimisticDefinitions
     
let _ = run show_int_list 4 qr (REPR (fun q r -> multo q r (inj_list [1; 1; 1; 1]))) qrh;

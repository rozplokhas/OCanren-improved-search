open GT
open MiniKanren
open Tester
open PessimisticDefinitions
     
let _ = run show_int_list 16 qrs (REPR (fun q r s -> poso r &&& divo (inj_list [0; 0; 0; 0; 1]) q r s)) qrsh;

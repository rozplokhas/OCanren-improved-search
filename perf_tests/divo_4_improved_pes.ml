open GT
open MiniKanren
open Tester
open PessimisticImprovedDefinitions
     
let _ = run show_int_list (-1) qrs (REPR (fun q r s -> poso r &&& divo (inj_list [0; 0; 0; 1]) q r s)) qrsh;

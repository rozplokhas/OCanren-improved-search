open GT
open MiniKanren
open Tester
open OptimisticImprovedDefinitions
     
let _ = run show_int_list (-1) qr (REPR (fun q r -> appendo q r (inj_list (nats 200)))) qrh

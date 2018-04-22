open GT
open MiniKanren
open Tester
open PessimisticDefinitions
     
let _ = run show_int_list 101 qr (REPR (fun q r -> appendo q r (inj_list (nats 100)))) qrh

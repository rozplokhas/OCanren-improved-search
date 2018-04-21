open GT
open MiniKanren
open Tester
open ExtendedDefinitions

let _ = run show_int_list (-1) qr (REPR (fun q r -> appendo q r (inj_list (nats 100)))) qrh

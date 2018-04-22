open GT
open MiniKanren

let make_timer () =
  let open Unix in
  let origin = (times ()).tms_utime in
  (fun () ->
    (times ()).tms_utime -. origin
  )

exception Timeout

let empty_reifier _ _ = ""
            
let run printer n num (repr, goal) handler =
  let name = Filename.chop_suffix (Filename.basename (Sys.executable_name)) ".opt" in
  let dump =
    try
      Printf.printf "%s, %s answer%s {\n" 
        repr 
        (if n = (-1) then "all" else string_of_int n) 
        (if n <>  1  then "s" else "");
      let get_time = make_timer () in
      Sys.set_signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Timeout));
      ignore (Unix.alarm 120);    
      let results = run num goal handler in
      let time    = get_time () in
      let table = List.map (fun (name, ans) -> name, Stream.take ~n:n ans) results in
      let rec show = function
      | (_, []) :: _    -> ()
      | table ->
         let table' = 
  	   List.map 
	     (fun (n, x::xs) -> 
	       Printf.printf "%s=%s; " n (printer x); 
	       (n, xs)
	     ) 
	     table 
         in
         Printf.printf "\n";
         show table'
      in
      show table;
      Printf.printf "}\n%!";
      Printf.sprintf "\\def\\%s{%f}\n" name time
    with Timeout -> Printf.sprintf "\\def\\%s{---}\n" name
  in Printf.eprintf "%s" dump
 
let qh   = fun qs       -> ["q", qs]
let qrh  = fun qs rs    -> ["q", qs; "r", rs]
let qrsh = fun qs rs ss -> ["q", qs; "r", rs; "s", ss]

let (!) = (!!)

let rec rnats = function
| 0 -> []
| n -> n :: rnats (n - 1)

let nats n = List.rev (rnats n)

let show_int      = show(logic) (show int)
let show_int_list = show(List.logic) show_int
let show_nat_list = show(List.logic) (show Nat.logic)

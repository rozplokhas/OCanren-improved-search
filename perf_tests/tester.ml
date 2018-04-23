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
  let recode s =
    let b = Buffer.create 1024 in
    for i=0 to String.length s - 1 do
      match s.[i] with
      | '_'             -> Buffer.add_string b "x"
      | ('0'..'9') as c -> Buffer.add_string b ([|"O"; "I"; "S"; "R"; "J"; "B"; "G"; "T"; "X"; "P"|].(Char.code c - Char.code '0'))
      | c               -> Buffer.add_char b c
    done;
    Buffer.contents b
  in
  let name' = Filename.chop_suffix (Filename.basename (Sys.executable_name)) ".opt" in
  let name  = recode name' in
  let dump =
    try
      Printf.printf "%s, %s answer%s {\n" 
        repr 
        (if n = (-1) then "all" else string_of_int n) 
        (if n <>  1  then "s" else "");
      let rec iterate n i acc =
        Printf.printf "Iteration %d...%!" i;
        let get_time = make_timer () in
        if i = 1
        then (
          Sys.set_signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Timeout));
          ignore (Unix.alarm 120);
        );
        Printf.printf "Before run...\n%!";
        let results  = run num goal handler in
        Printf.printf "After run...\n%!";        
        let table    = List.map (fun (name, ans) -> name, Stream.take ~n:n ans) results in
        Printf.printf "After table...\n%!";        
        if i = 1 then Sys.set_signal Sys.sigalrm Sys.Signal_ignore;
        let time     = get_time () in
        Printf.eprintf "%%Current time: %f\n" time;
        Printf.printf "yep\n%!";
        if i = n then table, (acc +. time) /. (float n) else iterate n (i+1) (acc +. time);
      in
      let table, time = iterate 5 1 0.0 in
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
      Printf.sprintf "\\def\\%s{%f}%%%s\n" name time name'
    with Timeout -> Printf.printf "timeout!\n%!"; Printf.sprintf "\\def\\%s{---}%%%s\n" name name'
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

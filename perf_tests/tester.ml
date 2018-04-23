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
  (* Gc.set { (Gc.get()) with Gc.verbose = 3 }; *)
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
      let rec iterate niter i acc =
        if i = 1
        then (
          Sys.set_signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Timeout));
          ignore (Unix.alarm 120);
        );
        let get_time = make_timer () in        
        let table = List.map (fun (name, ans) -> name, Stream.take ~n:n ans) @@ run num goal handler in
        let time = get_time () in        
        if i = 1 then Sys.set_signal Sys.sigalrm Sys.Signal_ignore;
        Printf.eprintf "%%Current time: %.4f\n" time;
        if i = niter then table, (acc +. time) /. (float niter) else iterate niter (i+1) (acc +. time);
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
      Printf.sprintf "\\def\\%s{%.4f}%%%s\n" name time name'
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

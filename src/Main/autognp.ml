(* * Simple batch proof processor with Emacs mode *)

open Engine
open ExprUtils
open Abbrevs
open Util
open CoreRules
open TheoryTypes

module PT = ParserTools


(* ** Logging
 * ----------------------------------------------------------------------- *)

(* let log_buf = Buffer.create 127 *)

let log_file = ref ""

let log_settings = ref ""

let enable_debug = ref false

(*
let no_rotation =
  { Bolt.Output.seconds_elapsed = None; Bolt.Output.signal_caught = None }

let register_buffer_logger () =
  let open Bolt in
  let buffer (_ : string) (_ : Output.rotation) (_ : Bolt.Layout.t lazy_t) =
    object
      method write msg =
        if !enable_debug then (
          Buffer.add_string log_buf msg;
          Buffer.add_string log_buf "\n"
      )
      method close = ()
    end
  in
  Bolt.Output.register "buffer" buffer
*)

let initialize_logging () =
  ()
(*
  let open Bolt in
  register_buffer_logger ();
  let mode = Mode.direct () in
  (* Logger.register "buffer_logger" Level.TRACE "all" "default" mode "buffer"
    ("",no_rotation) *)
  if !log_file<>"" then (
    Logger.register "file_logger" Level.TRACE "all" "default" mode "file"
      (!log_file,no_rotation)
  )
*)

(* ** Emacs mode
 * ----------------------------------------------------------------------- *)

let emacs_mode = ref false

let ps_files = ref []

let theory_states = ref [TheoryState.mk_ts ()]
  (* we will ensure that theory_states will be always non-empty *)

let ts_statenum () = L.length !theory_states - 1

let decode s =
  BatString.nreplace ~str:s ~sub:"\\<^newline>" ~by:"\n"

let eval_emacs () =
  let last_debug = ref "" in
  let exec_instr cmd0 =
    let cmd = decode cmd0 in
    let (ts,msg) =
      if BatString.starts_with cmd "undo " then (
        let cur_statenum = ts_statenum () in
        let (_undo, next_statenum_s) = BatString.split ~by:" " cmd in
        let next_statenum =
          int_of_string (BatString.rchop ~n:1 next_statenum_s)
        in
        if cur_statenum < next_statenum then
          failwith "Invalid undo statenum.";
        let undo_n = cur_statenum - next_statenum in
        begin match BatList.drop undo_n !theory_states with
        | (ts::_) as tss ->
          theory_states := tss;
          (ts,"")
        | [] -> failwith "impossible"
        end
      ) else if cmd = "enable_debug." then (
         let ts = L.hd !theory_states in
         theory_states := ts::!theory_states;
         enable_debug := true;
         (ts,"enabled debugging output")
      ) else if cmd = "disable_debug." then (
         let ts = L.hd !theory_states in
         enable_debug := false;
         theory_states := ts::!theory_states;
         (ts,"disabled debugging output")
      ) else (
        let is = Parse.instruction cmd in
        let ts = L.hd !theory_states in
        let (ts,msg) =
          L.fold_left
            (fun (ts, msg) i ->
              try
                let (ts', msg') = handle_instr true ts i in
                last_debug := get_buffer_log ();
                (ts', if msg = "" then msg' else msg'^"---\n"^msg)
              with
              | e -> 
                last_debug := get_buffer_log ();
                raise e)
            (ts,"")
            is
        in
        theory_states := ts::!theory_states;
        let debug =
          if !enable_debug then
            "\nDEBUG:\n"^(!last_debug)
          else ""
        in
        (ts,msg^debug)
      )
    in
    let g =
      match ts.ts_ps with
      | BeforeProof    -> ""
      | ClosedTheory _ -> ""
      | ActiveProof ({ CoreRules.subgoals = [] },_,_,_) ->
        "Current goal:\nNo remaining goals."
      | ActiveProof (gs,_,_,_) ->
        fsprintf "@[Current goal:@\n%a@.%s@]"
          (pp_jus 1)
          gs.subgoals
          (let rem =
             List.length gs.CoreRules.subgoals - 1 in if rem = 0 then "" else
          string_of_int rem^" other goals")
    in
    (msg,g)
  in
  let print_prompt () = F.printf "[%i]>\n%!" (ts_statenum ()) in
  print_prompt ();
  let outp s = print_endline s in
  while true do
    let s = read_line () in
    (try
       let (msg, g) = exec_instr s in
       print_endline msg;
       print_endline g
     with
       | PT.ParseError pe ->
         outp (fsprintf "[error-%i-%i]%s"
                 pe.PT.pe_char_start pe.PT.pe_char_end
                 (PT.error_string "<emacs>" pe))
       | Invalid_rule es ->
         outp (fsprintf "[error-0-%i]invalid rule application: %s\n%s"
                           (String.length s) es
                           (!last_debug))
       | Expr.TypeError e ->
         outp (fsprintf "[error-0-3]type error: %s"
                 (ExprUtils.typeError_to_string e))
       | e ->
         outp (fsprintf "[error-0-3]unknown error: %s,\n%s"
                 (Printexc.to_string e)
                 (Printexc.get_backtrace ()))
    );
    print_prompt ()
  done


(* ** Argument handlingx
 * ----------------------------------------------------------------------- *)

let main =
  let speclist =
    Arg.align
      [ ("-emacs", Arg.Set emacs_mode,
         "   Use with Emacs")
      ; ("-log_file", Arg.Set_string log_file,
         "   Log information to given file")
      ; ("-log_settings", Arg.Set_string log_settings,
         "   Use given log settings")
      ]
  in
  let usage_msg = "Usage: " ^ Sys.argv.(0) ^ " <file>" in
  let parse_args s = ps_files := !ps_files @ [s] in
  Arg.parse speclist parse_args usage_msg;
  initialize_logging ();
  if not !emacs_mode then (
    match !ps_files with
    | [f] ->
      let szc = input_file f in
      F.printf "File %s\n%!" szc;
      ignore (catch_TypeError (fun () -> eval_theory szc))
    | _ ->
      prerr_endline "Exactly one input file required for non-emacs mode";
      exit (-1)
  ) else (
    if !ps_files <> [] then (
      prerr_endline "Cannot give input files for emacs mode";
      exit (-1)
    );
    eval_emacs ()
  )

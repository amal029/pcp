open Javalib_pack
open Javalib
open JBasics
open JCode
open Sawja_pack
open JBirSSA
module Stack = BatStack
module Array = BatArray
module List = BatList
module JL = JClassLow
module Enum = BatEnum
module File = BatFile
module Hashtbl = BatHashtbl

let (>>) f g x = (f(g x))

exception Internal of string
exception NARGS
exception Not_supported of string
exception Uninitialized of string
exception Cant_handle of string

let bj1 = "com.jopdesign.sys.JVM";;
let bj2 = "com.jopdesign.sys.GC";;
let addmethods = ref false;;

let usage_msg = "Usage: wcma class-path class-name
Note:
1.) Class-name should be given without the .class extension
2.) Should be a fully qualified name, .e.g,: java.lang.Object";;


let get_bytecode_nums pbir (cn, ms) = 
  try
    let first_pp = JControlFlow.PP.get_first_pp pbir cn ms in
    let bir = JControlFlow.PP.get_ir first_pp in
    (* DEBUG *)
    let () = print_endline ((cn_name cn) ^ "." ^ (ms_name ms)) in
    let () = List.iter print_endline (print ~phi_simpl:false bir) in
    (* TODO:  First get the pps for the if branches *)
    let lnums = Array.mapi
      (fun i x ->
	match x with
	| Ifd ((_,_,_),g) -> Some ((pc_ir2bc bir).(i+1), (pc_ir2bc bir).(g))
	| _ -> None) (code bir) in
    (* TODO:  Now get the pps for the loops and add it to lnums *)
    let loop_fbbnums = Array.mapi
			 (fun i x ->
			  if (Array.length x) > 1 then
			    (* This means there are more than 1 predecessor at this point *)
			    if (Array.exists ((>) i) x) && (Array.exists ((<) i) x) then
			      (* XXX:  This means it is the first block of the loop *)
			      if i > 0 then
				Some ((pc_ir2bc bir).(i-1))
			      else
				Some ((pc_ir2bc bir).(i))
			    else
			      None
			  else
			    None) (preds bir) in
    (lnums, loop_fbbnums)
  with
  | Not_found -> raise (Internal ("Cannot find class_method:" ^ (cn_name cn) ^"."^ (ms_name ms)))
  | JControlFlow.PP.NoCode (cn, ms) -> Array.make 1 None, Array.make 1 None

let main = 
  try
    let args = Sys.argv in
    let (cp, cn) =
      if Array.length args <> 3 then let () = print_endline usage_msg in raise NARGS
      else (args.(1),args.(2)) in
    (* Need to build all the other entry points so that other classes are also parsed!! *)
    let (prta,_) = JRTA.parse_program ~instantiated:[] ~other_entrypoints:[make_cms (make_cn "com.jopdesign.sys.Startup")
									      (make_ms "boot" [] None)]
      cp (make_cms (make_cn cn) JProgram.main_signature) in
    (* Convert it into JBIR format *)
    let pbir = JProgram.map_program2
      (fun _ -> transform ~bcv:false ~ch_link:false) 
      (Some (fun code pp -> (pc_ir2bc code).(pp)))
      prta in

    (* TODO: Dump a file with line numbers at bytecode level and the
       places where checkpoints need to be inserted.*)
    let callgraph = JProgram.get_callgraph_from_entries prta [(make_cms (make_cn cn) JProgram.main_signature)] in
    (* Put methods into the methodset *)
    let methods_to_explore = List.fold_left (fun s ((cn1, ms1, _), (cn2, ms2)) ->
      ClassMethodSet.add (make_cms cn2 ms2) (ClassMethodSet.add (make_cms cn1 ms1) s))
      ClassMethodSet.empty callgraph in
    let methods_to_explore = List.map cms_split (ClassMethodSet.elements methods_to_explore) in
    (* TODO: For each of the methods load them and dump the checkpoint
     line number at Bytecode level*)
    let bytecode_nums = List.map (get_bytecode_nums pbir) methods_to_explore in
    let (bytecode_nums, fb_nums) = List.split bytecode_nums in
    (* XXX:  IF OUTGOING EDGE CHECKPOINTS *)
    let () = print_endline "IF CHECKPOINTS" in
    let () =
      List.iter2 (fun a (cn, ms) ->
		  let () = (cn_name cn) ^ "." ^ (ms_name ms) |> print_endline in
		  Array.iter (function
			       | Some (x, y) -> (x |> string_of_int) ^ "," ^ (y |> string_of_int) |> print_endline
			       | None -> ()) a) bytecode_nums methods_to_explore in

    (* XXX:  FIRST BASIC BLOCK OF LOOP CHECKPOINTS*)
    let () = print_endline "FIRST BB OF LOOP CHECKPOINTS" in
    List.iter2 (fun a (cn, ms) ->
      let () = (cn_name cn) ^ "." ^ (ms_name ms) |> print_endline in
      Array.iter (function
      | Some x -> (x |> string_of_int) |> print_endline
      | None -> ()) a) fb_nums methods_to_explore
  with
  | NARGS -> ()
     

open Javalib_pack
open Javalib
open JBasics
open JCode
open Sawja_pack
open JBirSSA
module JL = JClassLow
module Stack = BatStack
module Array = BatArray
module List = BatList
module Enum = BatEnum
module File = BatFile
module Hashtbl = BatHashtbl
module LW = LibWcma

let (>>) f g x = (f(g x))

exception Internal of string
exception NARGS
exception Not_supported of string
exception Uninitialized of string
exception Cant_handle of string

let bj1 = "com.jopdesign.sys.JVM";;
let bj2 = "com.jopdesign.sys.GC";;

let usage_msg = "Usage: checkpoint class-path class-name
Note:
1.) Class-name should be given without the .class extension
2.) Should be a fully qualified name, .e.g,: java.lang.Object";;

let get_bytecode_nums pbir (cn, ms) = 
  try
    let first_pp = JControlFlow.PP.get_first_pp pbir cn ms in
    let bir = JControlFlow.PP.get_ir first_pp in
    (* XXX: DEBUG *)
    (* let () = print_endline ((cn_name cn) ^ "." ^ (ms_name ms)) in *)
    (* let () = List.iter print_endline (print ~phi_simpl:false bir) in *)
    (* TODO:  First get the pps for the if branches *)
    let lnums = Array.mapi
      (fun i x ->
	match x with
	| Ifd ((_,_,_),g) -> Some (pc_ir2bc bir).(g-1)
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
    Array.append lnums loop_fbbnums
  with
  | Not_found -> raise (Internal ("Cannot find class_method:" ^ (cn_name cn) ^"."^ (ms_name ms)))
  | JControlFlow.PP.NoCode (cn, ms) -> Array.make 1 None


let main = 
  try
    let args = DynArray.make 2 in
    let sourcep = ref "" in
    let speclist = [
      ("-sourcepath", Arg.String (fun x -> sourcep := x), "Source path for parsing loop count");
    ] in
    let () = Arg.parse speclist (fun x -> DynArray.add args x) (usage_msg^"\n[OPTION]:") in
    let (cp, cn) = 
      if DynArray.length args <> 2 then let () = print_endline usage_msg; Arg.usage speclist "[OPTION]:" in exit 1
      else (DynArray.get args 0,DynArray.get args 1) in
    (* Need to build all the other entry points so that other classes are also parsed!! *)
    let (prta,_) = JRTA.parse_program
      ~instantiated:[]
      ~other_entrypoints:[make_cms (make_cn "com.jopdesign.sys.Startup")
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
    let () = JProgram.store_callgraph callgraph "/tmp/Callgraph.txt" in
    (* Put methods into the methodset *)
    let methods_to_explore = List.fold_left (fun s ((cn1, ms1, _), (cn2, ms2)) ->
      ClassMethodSet.add (make_cms cn2 ms2) (ClassMethodSet.add (make_cms cn1 ms1) s))
      ClassMethodSet.empty callgraph in
    let methods_to_explore = List.map cms_split (ClassMethodSet.elements methods_to_explore) in
    (* TODO: For each of the methods load them and dump the checkpoint
     line number at Bytecode level*)
    let possible_checkpoints = List.map (get_bytecode_nums pbir) methods_to_explore in
    let possible_checkpoints =
      (* XXX: We need to manually calculate the bytecode offset at the
	 lower level bytecode representation!! *)
      List.map2 (fun a (cn, ms) ->
	Array.map (function
    	| Some x ->
	   let llc = JFile.get_class_low (JFile.class_path cp) cn in
	   let cnn = JLow2High.low2high_class llc in
	   let cpool = get_class (class_path cp) cn |> get_consts in
	   let cpool = DynArray.init (Array.length cpool) (fun i -> cpool.(i)) in
	   let m = JHigh2Low.h2l_acmethod cpool (JClass.get_method cnn ms) in
	   let mcode = List.map
	     (function
	     | JL.AttributeCode x -> Some (Lazy.force x)
	     | _ -> None) m.JL.m_attributes
	|> List.filter (function Some x -> true | _ -> false)
	|> List.hd in
	   let mcode = match mcode with
	     | Some x -> x.JL.c_code
	     | None -> raise (Internal ("Unexpected type")) in
	   Some (x + LW.get_size mcode.(x))
    	| None -> None) a) possible_checkpoints methods_to_explore in

    let () = print_endline "IF AND LOOP FIRST BB CHECKPOINTS" in
    (* XXX:  DEBUG *)
    let () =
      List.iter2 (fun a (cn, ms) ->
	let () = print_endline ((cn_name cn) ^ "." ^ (ms_name ms)) in
	Array.iter(function
	| Some x -> x |> string_of_int |> print_endline
	| None -> ()) a) possible_checkpoints methods_to_explore in

    (* TODO:  Now get the wcet of the various methods *)
    let l = LW.parsewca !sourcep in
    let mm = LW.internal_main cp cn l true in
    ()
  with
  | NARGS -> ()
     

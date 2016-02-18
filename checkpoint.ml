open Javalib_pack
open Javalib
open JBasics
open JCode
module JL = JClassLow
open Sawja_pack
open JBirSSA
module Stack = BatStack
module Array = BatArray
module List = BatList
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

let get_size = function
  | JL.OpNop -> 1
  | JL.OpAConstNull -> 1
  | JL.OpLConst _ -> 1
  | JL.OpIConst _ -> 1
  | JL.OpFConst _ -> 1
  | JL.OpDConst _ -> 1
  | JL.OpBIPush _ -> 2
  | JL.OpSIPush _ -> 3
  | JL.OpLdc1 _ -> 2
  | JL.OpLdc1w _ -> 3
  | JL.OpLdc2w _ -> 3 
  | JL.OpLoad (t,v) -> 
    (match t with
     | `Double 
     | `Long -> if (v <= 3) then 1 else 2
     | _ -> if (v <= 3) then 1 else 2)
  | JL.OpALoad v -> if v<=3 then 1 else 2
  | JL.OpArrayLoad _ -> 1
  | JL.OpAALoad | JL.OpBALoad
  | JL.OpCALoad | JL.OpSALoad -> 1
  | JL.OpAStore _ -> 2
  | JL.OpStore (_,v) -> if v<=3 then 1 else 2
  | JL.OpArrayStore _ -> 1
  | JL.OpAAStore | JL.OpBAStore
  | JL.OpCAStore | JL.OpSAStore -> 1
  | JL.OpPop -> 1
  | JL.OpPop2 -> 1
  | JL.OpDup -> 1
  | JL.OpDupX1 -> 1
  | JL.OpDupX2 -> 1
  | JL.OpDup2 -> 1
  | JL.OpDup2X1 -> 1
  | JL.OpDup2X2 -> 1
  | JL.OpSwap -> 1
  | JL.OpAdd _ -> 1 
  | JL.OpSub _ -> 1 
  | JL.OpMult _ -> 1 
  | JL.OpDiv _ ->  1
  | JL.OpRem _ -> 1
  | JL.OpNeg _ -> 1
  | JL.OpIShl -> 1
  | JL.OpIShr -> 1
  | JL.OpIUShr -> 1
  | JL.OpLShl -> 1
  | JL.OpLShr -> 1
  | JL.OpLUShr -> 1
  | JL.OpIAnd -> 1
  | JL.OpIOr -> 1
  | JL.OpIXor -> 1
  | JL.OpLAnd -> 1
  | JL.OpLOr -> 1
  | JL.OpLXor -> 1
  | JL.OpI2L -> 1
  | JL.OpI2C -> 1
  | JL.OpL2I -> 1
  | JL.OpL2F -> 1
  | JL.OpL2D -> 1
  | JL.OpF2I -> 1
  | JL.OpF2L -> 1
  | JL.OpF2D -> 1
  | JL.OpD2I -> 1
  | JL.OpD2F -> 1
  | JL.OpD2L -> 1
  | JL.OpI2B -> 1
  | JL.OpI2F -> 1 
  | JL.OpI2S -> 1
  | JL.OpI2D -> 1
  | JL.OpIInc _ -> 3
  | JL.OpLCmp -> 1
  | JL.OpFCmpL -> 1
  | JL.OpFCmpG -> 1
  | JL.OpDCmpL -> 1
  | JL.OpIfEq _ | JL.OpIfNe _ 
  | JL.OpIfLt _ | JL.OpIfGe _
  | JL.OpIfLe _ | JL.OpIfGt _ -> 3
  | JL.OpICmpEq _
  | JL.OpICmpNe _
  | JL.OpICmpLt _
  | JL.OpICmpGe _
  | JL.OpICmpGt _
  | JL.OpICmpLe _
  | JL.OpACmpEq _
  | JL.OpACmpNe _ -> 3
  | JL.OpGoto _ -> 3
  | JL.OpJsr _ -> 3
  | JL.OpRet _ -> 2
  | JL.OpTableSwitch (_,_,_,x) -> 4+4+4+(4* Array.length x)
  | JL.OpLookupSwitch (_,x) -> 4+4+(8* List.length x)
  | JL.OpReturn x -> 1
  | JL.OpAReturn -> 1 
  | JL.OpReturnVoid -> 1 
  | JL.OpGetStatic _ -> 3
  | JL.OpPutStatic _ -> 3
  | JL.OpGetField _ -> 3
  | JL.OpPutField _ -> 3
  | JL.OpInvokeVirtual _ -> 3 
  | JL.OpInvokeNonVirtual _ -> 3
  | JL.OpInvokeStatic _ -> 3
  | JL.OpInvokeInterface _ -> 5
  | JL.OpNew _ -> 3
  | JL.OpNewArray _ -> 2
  | JL.OpANewArray _ -> 3
  | JL.OpArrayLength -> 1
  | JL.OpThrow -> 1
  | JL.OpCheckCast _ -> 3
  | JL.OpInstanceOf _ -> 3
  | JL.OpMonitorEnter  -> 1
  | JL.OpMonitorExit -> 1
  | JL.OpAMultiNewArray _ -> 4
  | JL.OpIfNull _ -> 3
  | JL.OpIfNonNull _ -> 3 
  | JL.OpGotoW _ -> 5
  | JL.OpJsrW _ -> 5
  | JL.OpBreakpoint -> 1
  | JL.OpInvalid -> 0
  | JL.OpDCmpG -> 1

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
    let args = Sys.argv in
    let (cp, cn) =
      if Array.length args <> 3 then let () = print_endline usage_msg in raise NARGS
      else (args.(1),args.(2)) in
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
    (* Put methods into the methodset *)
    let methods_to_explore = List.fold_left (fun s ((cn1, ms1, _), (cn2, ms2)) ->
      ClassMethodSet.add (make_cms cn2 ms2) (ClassMethodSet.add (make_cms cn1 ms1) s))
      ClassMethodSet.empty callgraph in
    let methods_to_explore = List.map cms_split (ClassMethodSet.elements methods_to_explore) in
    (* TODO: For each of the methods load them and dump the checkpoint
     line number at Bytecode level*)
    let possible_checkpoints = List.map (get_bytecode_nums pbir) methods_to_explore in

    (* XXX:  DEBUG *)
    let () = List.iter2 (fun a (cn, ms) ->
      let () = print_endline ((cn_name cn) ^ "." ^ (ms_name ms)) in
      Array.iter(function
      | Some x -> x |> string_of_int |> print_endline
      | None -> ()) a) possible_checkpoints methods_to_explore in

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
	   Some (x + get_size mcode.(x))
    	| None -> None) a) possible_checkpoints methods_to_explore in

    let () = print_endline "IF AND LOOP FIRST BB CHECKPOINTS" in
    (* XXX:  DEBUG *)
    List.iter2 (fun a (cn, ms) ->
      let () = print_endline ((cn_name cn) ^ "." ^ (ms_name ms)) in
      Array.iter(function
      | Some x -> x |> string_of_int |> print_endline
      | None -> ()) a) possible_checkpoints methods_to_explore

  with
  | NARGS -> ()
     

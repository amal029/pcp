open Javalib_pack
open Javalib
open JBasics
open JCode
open Sawja_pack
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
      (fun _ -> A3BirSSA.transform ~bcv:false ~ch_link:false) 
      (Some (fun code pp -> (A3BirSSA.pc_ir2bc code).(pp)))
      prta in

    let obj = JProgram.get_node pbir (make_cn cn) in
    (* let mobj = JProgram.get_concrete_method obj JProgram.main_signature in *)
    (* JPrint.print_class (JProgram.to_ioc obj) JBir.print stdout; *)
    (* Let us try using the control-flow graph *)
    try
      let bir_pp = JControlFlow.PP.get_first_pp_wp obj JProgram.main_signature in
      let bir_ir = JControlFlow.PP.get_ir bir_pp in
      (* TODO: Dump a file with line numbers at bytecode level and the
	 places where checkpoints need to be inserted.*)
      List.iter print_endline (A3BirSSA.print ~phi_simpl:false bir_ir)
    with
    | JControlFlow.PP.NoCode (cn, ms) -> print_endline ((cn_name cn) ^ ", " ^ (ms_name ms))
      
    
  with
  | NARGS -> ()
     

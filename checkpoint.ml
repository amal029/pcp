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
open BatPervasives

let (>>) f g x = (f(g x))

exception Internal of string

let bj1 = "com.jopdesign.sys.JVM";;
let bj2 = "com.jopdesign.sys.GC";;
let bj3 = ref "";;
let addmethods = ref false;;
let cpp = ref ""

let usage_msg = "Usage: wcma [-sourcepath <filename>] [OPTION] class-path class-name
Note:
1.) Class-name should be given without the .class extension
2.) Should be a fully qualified name, .e.g,: java.lang.Object";;


let main = 
  let args = DynArray.make 2 in
  let ff = Sys.getcwd () in
  let sourcep = ref "" in
  let speclist = [
    ("-sourcepath", Arg.String (fun x -> sourcep := x), "Source path for parsing loop count");
    ("-m", Arg.Set addmethods, "Add execution times of Java implemented bytecodes")
  ] in
  let () = Arg.parse speclist (fun x -> DynArray.add args x) (usage_msg^"\n[OPTION]:") in
  let (cp, cn) = 
    if DynArray.length args <> 2 then
      let () = print_endline usage_msg; Arg.usage speclist "[OPTION]:" in
      raise (Internal "")
    else (DynArray.get args 0,DynArray.get args 1) in
  cpp := cp;
  let marray = DynArray.make 100 in
  let jfk = Stack.create () in
  bj3 := cn;

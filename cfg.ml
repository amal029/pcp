open Javalib_pack
open Javalib
open JBasics
open JCode
open Sawja_pack
open JBirSSA
open Joplang
module JL = JClassLow
module Stack = BatStack
module Array = BatArray
module List = BatList
module Enum = BatEnum
module File = BatFile
module Hashtbl = BatHashtbl
module LW = LibWcma

type 'a bb = {code:'a list;
	      i: 'a edge list;
	      o: 'a edge list}

and 'a edge = Edge of ('a bb * 'a bb)


let build_method_cfg cn ms pbir = 
  let first_pp = JControlFlow.PP.get_first_pp pbir cn ms in
  let bir = JControlFlow.PP.get_ir first_pp in
  let code = code bir |> Array.to_list in
  (* TODO:  Make the cfg for the method *)
  ()
    

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

type 'a bb = {code: 'a list;
	      pps : int;
	      ppe : int;
	      cn : class_name;
	      ms : method_signature;
	      mutable o: 'a edge list}

and 'a edge = Edge of ('a bb * 'a bb)

let build_method_cfg cn ms pbir = 
  let first_pp = JControlFlow.PP.get_first_pp pbir cn ms in
  let bir = JControlFlow.PP.get_ir first_pp in
  let code = code bir in

  let get_goto_bb g ll =
    List.find (fun x -> g >= x.pps && g <= x.ppe) ll in

  (* TODO:  Make the cfg for the method *)
  let bpps =
    Array.fold_lefti
      (fun ll i x ->
       let bb = List.last ll in
       match x with
       | Ifd ((_,g)) as s ->
	  (* TODO:  Update!! *)
	  let nbb = {code=[];pps=i+1;ppe=i+1;cn=cn;ms=ms;o=[]} in
	  let bb = {bb with code=bb.code @ [s]; ppe=i} in
	  bb.o <- bb.o @ [Edge(bb,nbb)];
	  let ll = (List.take ((List.length ll) - 1) ll) @ [bb;nbb] in
	  (if g <= i then
	     let gbb = get_goto_bb g ll in
	     bb.o <- bb.o @ [Edge(bb,gbb)]);
	  ll
       | Goto g as s ->
	    (* TODO:  Get the bb from the list and add the edge to it! *)
	    let nbb = {code=[];pps=i+1;ppe=i+1;cn=cn;ms=ms;o=[]} in
	    let bb = {bb with code=bb.code @ [s]; ppe=i} in
	    let ll = (List.take ((List.length ll) - 1) ll) @ [bb] in
	    bb.o <- bb.o @ [Edge(bb,nbb)];
	    (if g <= i then
	       let gbb = get_goto_bb g ll in
	       bb.o <- bb.o @ [Edge(bb,gbb)]);
	    ll
       | _  as s -> (List.take ((List.length ll) - 1) ll) @ [{bb with code=bb.code @ [s]; ppe=i}]
      ) [{code=[];pps=0;ppe=0;cn=cn;ms=ms;o=[]}] code in

  (* TODO:  Now build the forward edges *)
  List.iter
    (fun x ->
     List.iter
       (function
	 | Ifd ((_,g)) -> 
	    if g >= x.ppe then
	      x.o <- x.o @ [Edge(x, get_goto_bb g bpps)]
	 | Goto g ->
	    if g >= x.ppe then
	      x.o <- x.o @ [Edge(x, get_goto_bb g bpps)]
	 | _ -> ()) x.code) bpps


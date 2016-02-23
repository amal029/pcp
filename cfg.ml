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

let (>>) f g x = (f(g x))
type 'a bb = {code: 'a list;
	      pps : int;
	      ppe : int;
	      cn : class_name;
	      ms : method_signature;
	      mutable o: 'a edge list}

and 'a edge = Edge of ('a bb * 'a bb)

let rec print_cfg visited cfg =
  let () = print_string ((string_of_int cfg.pps)
			 ^ "--" ^ (string_of_int cfg.ppe)) in
  (* let () = List.iter (print_endline >> print_instr) cfg.code in *)

  let () =
    List.iter (function | Edge (_,d) ->
      let () = print_string "\n|-->" in
      print_string
	((string_of_int d.pps) ^ "--" ^ (string_of_int d.ppe))) cfg.o in
  let () = print_endline "\n" in
  List.iter
    (function | Edge (s,d) ->
      match List.Exceptionless.find ((==) d) visited with
      | Some x -> ()
      | None ->
	 print_cfg (cfg :: visited) d) cfg.o

let build_method_cfg cn ms pbir = 
  let first_pp = JControlFlow.PP.get_first_pp pbir cn ms in
  let bir = JControlFlow.PP.get_ir first_pp in
  let code = code bir in

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
	  let ll = (List.take ((List.length ll) - 1) ll) @ [bb;nbb] in
	  ll
       | Goto g as s ->
	    (* TODO:  Get the bb from the list and add the edge to it! *)
	  let nbb = {code=[];pps=i+1;ppe=i+1;cn=cn;ms=ms;o=[]} in
	  let bb = {bb with code=bb.code @ [s]; ppe=i} in
	  let ll = (List.take ((List.length ll) - 1) ll) @ [bb;nbb] in
	  ll
       | _  as s ->
	  (List.take ((List.length ll) - 1) ll) @ [{bb with code=bb.code @ [s]; ppe=i}]
      ) [{code=[];pps=0;ppe=0;cn=cn;ms=ms;o=[]}] code in

  let get_goto_bb g ll =
    (* let () = (print_endline >> string_of_int) g in *)
    List.find (fun x -> g >= x.pps && g <= x.ppe) ll in

  (* TODO:  Now build the edges *)
  let mpreds = preds bir in
  let () = List.iter
    (fun bb ->
      for i = bb.pps to bb.ppe do
	(* Now build the edges *)
	(* let () = (print_endline >> string_of_int) i in *)
	let pa = mpreds.(i) in
	(* let () = Array.iter (print_endline >> string_of_int) pa in *)
	Array.iter
	  (fun p ->
	    if p>= 0 && not (p >= bb.pps && p <= bb.ppe) then
	      let gbb = get_goto_bb p bpps in
	      gbb.o <- gbb.o @ [Edge(gbb,bb)]) pa
      done) bpps in
  List.hd bpps

    

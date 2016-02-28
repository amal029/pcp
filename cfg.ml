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
type bb = {pps : int;
	      ppe : int;
	      cn : class_name;
	      ms : method_signature;
	      mutable lpps : int option;
	      mutable lppe : int option;
	      mutable wcet : int;
	      mutable o: edge list}

and edge = Edge of (bb * bb * int option * int option)

let rec print_cfg visited cfg =
  let get_lpps_lppe = function
    | Some x -> (string_of_int x)
    | None -> raise (LW.Internal "") in
  let () = print_string ((string_of_int cfg.pps)
			 ^ "--" ^ (string_of_int cfg.ppe) ^ ", ") in
  let () = print_string (get_lpps_lppe cfg.lpps ^ "--" ^ get_lpps_lppe cfg.lppe) in
  (* let () = (print_string >> ((^)" ") >> string_of_int) cfg.wcet in *)

  let () =
    List.iter (function | Edge (_,d,w,chkp) ->
      let () = print_string "\n|-->" in
      let () = print_string ((string_of_int d.pps) ^ "--"
			     ^ (string_of_int d.ppe)) in
      let () =
	print_string (": " ^
			 (match w with | None -> "Back edge"
			 | Some x -> (string_of_int x))) in
      print_string (
	match chkp with
	| None -> ", No checkpoint"
	| Some x -> ", " ^ (string_of_int x))) cfg.o in
  let () = print_endline "\n" in
  List.iter
    (function
      | Edge (s,d,_,_) ->
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
       | Ifd ((_,g)) ->
	  (* TODO:  Update!! *)
	  let nbb = {pps=i+1;ppe=i+1;cn=cn;ms=ms;wcet=0;o=[];lpps=None;lppe=None} in
	  let bb = {bb with ppe=i} in
	  let ll = (List.take ((List.length ll) - 1) ll) @ [bb;nbb] in
	  ll
       | Goto g ->
	    (* TODO:  Get the bb from the list and add the edge to it! *)
	  let nbb = {pps=i+1;ppe=i+1;cn=cn;ms=ms;wcet=0;o=[];lpps=None;lppe=None} in
	  let bb = {bb with ppe=i} in
	  let ll = (List.take ((List.length ll) - 1) ll) @ [bb;nbb] in
	  ll
       | _  ->
	  (List.take ((List.length ll) - 1) ll) @ [{bb with ppe=i}]
      ) [{pps=0;ppe=0;cn=cn;ms=ms;o=[];wcet=0;lpps=None;lppe=None}] code in

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
	      gbb.o <- gbb.o @ [Edge(gbb,bb,None,None)]) pa
      done) bpps in

  (* Add a dummy start node *)
  let dummy = {pps=0;ppe=0;cn=cn;ms=ms;o=[];wcet=0;lpps=None;lppe=None} in
  dummy.o <- [Edge(dummy,(List.hd bpps), None, None)];
  dummy

    

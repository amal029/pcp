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

let get_wcet_method cms mm = 
  let mmc = DynArray.copy mm in
  let () = DynArray.filter (fun (n, _) -> cms_equal cms n) mmc in
  if (DynArray.length mmc) <> 0 then
    let (_, (i, m)) = DynArray.get mmc 0 in
    BatNum.to_int i + BatNum.to_int m
  else
    let (cn, ms) = (cms_split cms) in
    raise (Internal ("Cannot find the cms: " ^ (cn_name cn) ^ "." ^ (ms_name ms) ^ " in method-wcet cache!"))

let get_wcrc cms code mm const_pool = 
  (* TODO:  Now we convert the code into micro-code and then compute the wcrc *)
  Enum.fold (fun x y ->
    match y with
    | JL.OpNop -> x + 1
    | JL.OpAConstNull -> x + 1
    | JL.OpLConst _ -> x + 2
    | JL.OpIConst _ -> x + 1
    | JL.OpFConst _ -> x + 1 	(* Only fconst_0 is supported *)
    | JL.OpDConst _ -> x + 2 (* Only dconst_0 is supported *)
    | JL.OpBIPush _ -> x + 2
    | JL.OpSIPush _ -> x + 3
    | JL.OpLdc1 _ -> x + 4
    | JL.OpLdc1w _ -> x + 8
    | JL.OpLdc2w _ -> x + (Array.length [|Ldm;Nop;Ld_opd_16u;Add;Dup;Stmrac;Ldi;Add;Wait;
					  Wait;Ldmrd;Stm;Stmrac;Ldm;Wait;Wait;Ldmrd|])
    (* We can make this more accurate by checking for the second arg, but it is OK for now! *)
    | JL.OpLoad (t,v) ->
       (match t with
       | `Double | `Long ->  
	  if (v <= 2) then x + Array.length [|Ld;Ld|]
	  else if (v = 3) then 
	    x + (Array.length [|Ldvp;Dup;Ldi;Add;Stvp;Stm;Ld2;Ld3;Ldm;Stvp;Nop|])
	  else
	    x + (Array.length [|Ldvp;Dup;Ld_opd_8u;Add;Stvp;Stm;Ld0;Ld1;Ldm;Stvp;Nop|])
       | _ -> 
	  if (v <= 3) then
	    x + 1
	  else 
	    x + 2)
    | JL.OpALoad v -> if v <=3 then x + 1 else x + 2
    | JL.OpArrayLoad t ->
       (match t with
       | `Double | `Long -> x + (Array.length LW.laload)
       | _ -> x + (Array.length LW.iaload))
    | JL.OpAALoad | JL.OpBALoad
    | JL.OpCALoad | JL.OpSALoad -> x +  (Array.length [|Stald;Pop;Wait;Wait;Ldmrd|])
    | JL.OpAStore _ -> x + 2
    | JL.OpStore (xx,v) ->
       (match xx with
       | `Long | `Double -> if v<=2 then x + 2
	 else if v = 3 then 
	   x + (Array.length [|Ldvp;Dup;Ldi;Add;Stvp;Stm;St3;St2;Ldm;Stvp;Nop|])
	 else x + (Array.length [|Ldvp;Dup;Ld_opd_8u;Add;Stvp;Stm;St1;St0;Ldm;Stvp;Nop|])
       | _ -> if v <=3 then x + 1 else x + 2)
    | JL.OpArrayStore xx -> 
       (match xx with
       | `Double | `Long -> x + (Array.length LW.lastore)
       | _ -> x + (Array.length LW.iastore))
    | JL.OpAAStore | JL.OpBAStore
    | JL.OpCAStore | JL.OpSAStore -> x + (Array.length [|Stast;Pop;Pop;Wait;Wait;Nop|])
    | JL.OpPop -> x + 1
    | JL.OpPop2 -> x + 2
    | JL.OpDup -> x + 1
    | JL.OpDupX1 -> x + (Array.length [|Stm;Stm;Ldm;Ldm;Ldm;|])
    | JL.OpDupX2 -> x + Array.length [|Stm;Stm;Stm;Ldm;Ldm;Ldm;Ldm|]
    | JL.OpDup2 -> x + Array.length [|Stm;Stm;Ldm;Ldm;Ldm;Ldm|]
    | JL.OpDup2X1 -> x + Array.length [|Stm;Stm;Stm;Ldm;Ldm;Ldm;Ldm;Ldm|]
    | JL.OpDup2X2 -> x + Array.length [|Stm;Stm;Stm;Stm;Ldm;Ldm;Ldm;Ldm;Ldm;Ldm|]
    | JL.OpSwap -> x + Array.length [|Stm;Stm;Ldm;Ldm|]
    | JL.OpAdd xx as op ->
       (match xx with
       | `Double -> raise (LW.Opcode_Not_Implemented (JDumpLow.opcode op))
       | `Float -> raise (LW.Opcode_Java_Implemented (JDumpLow.opcode op))
       | `Long -> x + Array.length LW.long_add
       | _ -> x + Array.length [|Add|])
    | JL.OpSub xx as op ->
       (match xx with 
       | `Double -> raise (LW.Opcode_Not_Implemented (JDumpLow.opcode op))
       | `Float -> raise (LW.Opcode_Java_Implemented (JDumpLow.opcode op))
       | `Long -> 
	  x + Array.length [|Ldi;Xor;Stm;Ldi;Xor;Stm;Stm;Stm;Ldm;Ldi;Ushr;Ldm;
			     Ldi;Ushr;Add;Ldm;Ldi;And;Ldm;Ldi;And;Add;Ldi;Add;Ldi;Shr;Add;Ldi;Ushr;Ldm;Add;Ldm;Add;Ldm;Ldm;Add;Ldi;Add|]
       | _ -> x + Array.length [|Sub|])
    | JL.OpMult xx as op->
       (match xx with
       | `Double -> raise (LW.Opcode_Not_Implemented (JDumpLow.opcode op))
       | `Long -> 
	  let mn = make_ms "f_lmul" [(TBasic `Long);(TBasic `Long)] (Some (TBasic `Long)) in
	  let m_wcet = get_wcet_method (make_cms (make_cn LW.bj1) mn) mm in
	 (* XXX:  Should I add the time to load the callee and then load the caller into cache here! *)
	  x + Array.length LW.invokestatic_mc + m_wcet
       | `Float -> raise (LW.Opcode_Java_Implemented (JDumpLow.opcode op))
       | _ -> x + 35) (* Note that imul never accesses external memory!! *)
    | JL.OpDiv xx as op ->
       (match xx with
       | `Double -> raise (LW.Opcode_Not_Implemented (JDumpLow.opcode op))
       | _ -> 
	  let mn = make_ms "f_idiv" [(TBasic `Int);(TBasic `Int)] (Some (TBasic `Int)) in
	  let m_wcet = get_wcet_method (make_cms (make_cn LW.bj1) mn) mm in
	    (* XXX:  Should I add the time to load the callee and then load the caller into cache here! *)
	  x + Array.length LW.invokestatic_mc + m_wcet)
    | JL.OpRem xx as op ->
       (match xx with
       | `Double -> raise (LW.Opcode_Not_Implemented (JDumpLow.opcode op))
       | _ -> 
	  let mn = make_ms "f_irem" [(TBasic `Int);(TBasic `Int)] (Some (TBasic `Int)) in
	  let m_wcet = get_wcet_method (make_cms (make_cn LW.bj1) mn) mm in
	    (* XXX:  Should I add the time to load the callee and then load the caller into cache here! *)
	  x + Array.length LW.invokestatic_mc + m_wcet)
    | JL.OpNeg xx as op ->
       (match xx with 
       | `Long -> x + Array.length (Array.append [|Ldi;Xor;Stm;Ldi;Xor;Ldm;Ldi;Ldi|] LW.long_add)
       | `Double -> raise (LW.Opcode_Not_Implemented (JDumpLow.opcode op))
       | `Float -> raise (LW.Opcode_Java_Implemented (JDumpLow.opcode op))
       | _ -> x + Array.length [|Ldi;Xor;Ldi;Add|]) 
    | JL.OpIShl -> x + 1
    | JL.OpIShr -> x + 1
    | JL.OpIUShr -> x + 1
    | JL.OpLShl -> x + Array.length (Array.append (Array.append LW.lshl LW.lshl_not0) LW.lshl_le31)
    | JL.OpLShr -> x + Array.length (Array.append LW.lshr LW.lshr_le31)
    | JL.OpLUShr -> x + Array.length (Array.append (Array.append LW.lushr LW.lushr_le31) LW.lushr_not0)
    | JL.OpIAnd | JL.OpIOr | JL.OpIXor -> x + 1
    | JL.OpLAnd -> x + Array.length [|Stm;Stm;Stm;Ldm;And;Ldm;Ldm;And|]
    | JL.OpLOr -> x + Array.length [|Stm;Stm;Stm;Ldm;Or;Ldm;Ldm;Or|]
    | JL.OpLXor -> x + Array.length [|Stm;Stm;Stm;Ldm;Xor;Ldm;Ldm;Xor|]
    | JL.OpI2L -> x + Array.length [|Dup;Stm;Ldi;Shr;Ldm|]
    | JL.OpI2C -> x + 2
    | JL.OpL2I -> x + 3
    | JL.OpL2F as op -> raise (LW.Opcode_Not_Implemented (JDumpLow.opcode op))
    | JL.OpL2D as op -> raise (LW.Opcode_Not_Implemented (JDumpLow.opcode op))
    | JL.OpF2I as op -> raise (LW.Opcode_Java_Implemented (JDumpLow.opcode op))
    | JL.OpF2L as op -> raise (LW.Opcode_Not_Implemented (JDumpLow.opcode op))
    | JL.OpF2D as op -> raise (LW.Opcode_Not_Implemented (JDumpLow.opcode op))
    | JL.OpD2I as op -> raise (LW.Opcode_Not_Implemented (JDumpLow.opcode op))
    | JL.OpD2F -> 
       let mn = make_ms "f_d2f" [(TBasic `Long)] (Some (TBasic `Int)) in
       let m_wcet = get_wcet_method (make_cms (make_cn LW.bj1) mn) mm in
	 (* XXX:  Should I add the time to load the callee and then load the caller into cache here! *)
       x + Array.length LW.invokestatic_mc + m_wcet
    | JL.OpD2L as op -> raise (LW.Opcode_Java_Implemented (JDumpLow.opcode op))
    | JL.OpI2B -> 
       let mn = make_ms "f_i2b" [(TBasic `Int)] (Some (TBasic `Int)) in
       let m_wcet = get_wcet_method (make_cms (make_cn LW.bj1) mn) mm in
	 (* XXX:  Should I add the time to load the callee and then load the caller into cache here! *)
       x + Array.length LW.invokestatic_mc + m_wcet
      (* raise (LW.Opcode_Java_Implemented (JDumpLow.opcode op)) *)
    | JL.OpI2F as op -> raise (LW.Opcode_Java_Implemented (JDumpLow.opcode op))
    | JL.OpI2S as op -> raise (LW.Opcode_Java_Implemented (JDumpLow.opcode op))
    | JL.OpI2D as op -> raise (LW.Opcode_Not_Implemented (JDumpLow.opcode op))
    | JL.OpIInc _ -> x + Array.length [|Ldvp;Ld_opd_8u;Add;Star;Ld_opd_8u;Ldmi;Stmi|]
    | JL.OpLCmp -> 
       let mn = make_ms "f_lcmp" [(TBasic `Int);(TBasic `Int);(TBasic `Int);(TBasic `Int)] (Some (TBasic `Int)) in
       let m_wcet = get_wcet_method (make_cms (make_cn LW.bj1) mn) mm in
	 (* XXX:  Should I add the time to load the callee and then load the caller into cache here! *)
       x + Array.length LW.invokestatic_mc + m_wcet
    | JL.OpFCmpL as op -> raise (LW.Opcode_Java_Implemented (JDumpLow.opcode op))
    | JL.OpFCmpG as op -> raise (LW.Opcode_Java_Implemented (JDumpLow.opcode op))
    | JL.OpDCmpL as op -> raise (LW.Opcode_Not_Implemented (JDumpLow.opcode op))
    | JL.OpDCmpG as op -> raise (LW.Opcode_Not_Implemented (JDumpLow.opcode op))
    | JL.OpIfEq _ | JL.OpIfNe _ 
    | JL.OpIfLt _ | JL.OpIfGe _
    | JL.OpIfLe _ | JL.OpIfGt _ -> x + 4
    | JL.OpICmpEq _ | JL.OpICmpNe _
    | JL.OpICmpLt _ | JL.OpICmpGe _
    | JL.OpICmpGt _ | JL.OpICmpLe _
    | JL.OpACmpEq _ | JL.OpACmpNe _ -> x + 4
    | JL.OpGoto _ -> x + 4
    | JL.OpJsr _ | JL.OpRet _ -> x
    | JL.OpTableSwitch _ -> 
       let mn = make_ms "f_tableswitch" [(TBasic `Int)] None in
       let m_wcet = get_wcet_method (make_cms (make_cn LW.bj1) mn) mm in
	 (* XXX:  Should I add the time to load the callee and then load the caller into cache here! *)
       x + Array.length LW.invokestatic_mc + m_wcet
    | JL.OpLookupSwitch (_,xx) -> 
       let mn = make_ms "f_lookupswitch" [(TBasic `Int)] None in
       let m_wcet = get_wcet_method (make_cms (make_cn LW.bj1) mn) mm in
	 (* XXX:  Should I add the time to load the callee and then load the caller into cache here! *)
       x + Array.length LW.invokestatic_mc + m_wcet
    | JL.OpReturn xx ->
       (match xx with
       | `Double | `Long -> 
	  x + Array.length [|Stm;Stm;Dup;Stmrac;Stm;Stm;Stvp;Wait;Wait;
			     Ldmrd; Stbcrd;Stm;Nop;Stsp;Pop;Pop;Ldbcstart;Ldm;Add;
			     Stjpc;Ldm;Ldm;Wait;Wait;Nop|]
       | _ ->
	  x + Array.length [|Stm;Dup;Stmrac;Stm;Stm;Stvp;Wait;Wait;Ldmrd;Stbcrd;Stm;Nop;Stsp;
			     Pop;Pop;Ldbcstart;Ldm;Add;Stjpc;Ldm;Wait;Wait;Nop|])
    | JL.OpAReturn -> 
       x + Array.length [|Stm;Dup;Stmrac;Stm;Stm;Stvp;Wait;Wait;Ldmrd;Stbcrd;Stm;Nop;Stsp;
			  Pop;Pop;Ldbcstart;Ldm;Add;Stjpc;Ldm;Wait;Wait;Nop|] 
    | JL.OpReturnVoid -> 
       x + Array.length [|Dup;Stmrac;Stm;Stm;Stvp;Wait;Wait;Ldmrd;Stbcrd;Stm;Nop;
			  Stsp;Ldbcstart;Ldm;Add;Stjpc;Pop;Pop;Wait;Wait;Nop|]

    | JL.OpGetStatic _ 
    | JL.OpGetField _ 
    | JL.OpPutField _ 
    | JL.OpInvokeStatic _
    | JL.OpInvokeVirtual _
    | JL.OpInvokeNonVirtual _
    | JL.OpInvokeInterface _
    | JL.OpPutStatic _ as op -> 
       (* Better to convert it into high-level instruction and solve it there!! *)
       let hopcode = JInstruction.opcode2instruction const_pool op in
       (match hopcode with
       | OpGetStatic (_,xx) -> 
	  (match (fs_type xx) with
	  | TBasic xx ->
	     (match xx with
	     | `Long -> x + Array.length [|Nop;Nop;Ld_opd_16u;Dup;
					   Stmra;Ldi;Add;Stm;Wait;Wait;
					   Ldmrd;Ldm;Stmra;Wait;Wait;Ldmrd|]
	     | _ -> x + Array.length [|Stgs;Nop;Wait;Wait;Ldmrd|])
	  | _ -> x + Array.length [|Stgs;Nop;Wait;Wait;Ldmrd|])
       | OpGetField (_,xx) ->
	  (match (fs_type xx) with
	  | TBasic xx ->
	     (match xx with
	     | `Long ->
		x + Array.length [|Dup;Nop;Bz;Nop;Nop;Stmraf;Wait;Wait;Ldmrd;Nop;
				   Nop;Ld_opd_16u;Add;Dup;Stmraf;Ldi;Add;Stm;Wait;Wait;Ldmrd;Ldm;Stmraf;Wait;Wait;Ldmrd;
				 |]
	     | _ -> x + Array.length [|Stgf;Nop;Wait;Wait;Ldmrd;|])
	  | _ -> x + Array.length [|Stgf;Nop;Wait;Wait;Ldmrd;|])
       | OpPutField (_,xx) ->
	  (match (fs_type xx) with
	  | TBasic xx ->
	     (match xx with
	     | `Long -> x + Array.length [|Stm;Stm;Dup;Nop;Bz;Nop;Nop;Stmraf;
					   Wait;Wait;Ldmrd;Nop;Nop;Ld_opd_16u;
					   Add;Dup;Stmraf;Ldi;Add;Stm;Wait;Wait;Ldmrd;
					   Ldm;Stmraf;Wait;Wait;Ldmrd|]
	     | _ ->  x + Array.length [|
	       Ldjpc; Ldi; Sub; Stjpc; Nop; Nop; Ldm; Nop;
	       Ld_opd_8u; Ldi; And; Dup; Add; Add; Stm; Nop;
	       Nop; Ld_opd_16u; Ldm; Jmp; Nop; Nop
				      |])
	  | _ -> x + Array.length [|Ldjpc;
				    Ldi;Sub;Stjpc;Nop;Nop;Ldm;Nop;Ld_opd_8u;Ldi;And;Dup;Add;Add;Stm;Nop;Nop;Ld_opd_16u;Ldm;Jmp;Nop;Nop
				  |])
       | OpPutStatic (_,xx) ->
	  (match (fs_type xx) with
	  | TBasic xx ->
	     (match xx with
	     | `Long -> x + Array.length [|Stm;Stm;Ld_opd_16u;Dup;Stmwa;Ldm;Stmwd;Ldi;Add;Wait;Wait;
					   Stmwa;Ldm;Stmwd;Wait;Wait;Nop|]
	     | _ -> x + Array.length [|
	       Ldjpc;Ldi;Sub;Stjpc;Nop;Nop;Ldm;Nop;Ld_opd_8u;Ldi;And;Dup;Add;Add;Stm;Nop;Nop;
	       Ld_opd_16u;Ldm;Jmp;Nop;Nop
				     |])
	  | _ -> x + Array.length [|Ldjpc;Ldi;Sub;
				    Stjpc;Nop;Nop;Ldm;Nop;Ld_opd_8u;Ldi;And;Dup;Add;Add;Stm;Nop;Nop;	Ld_opd_16u;Ldm;Jmp;Nop;Nop
				  |])
       | OpInvoke (xx,ms) as op ->
	  (match xx with
	  | `Interface cn -> 
	     (* Invoke the method itself!! *)
	     let cms = make_cms cn ms in
	     let m_wcet = get_wcet_method cms mm in
	     x + Array.length LW.invokeinterface_mc + m_wcet
	  | `Virtual ot -> 
	     let cn = (match ot with | TClass x -> x | TArray _ -> raise (Internal "This should be TClass")) in
	     let cms = make_cms cn ms in
	     let m_wcet = get_wcet_method cms mm in
	     x + Array.length LW.invokevirtual_mc + m_wcet
	  (* Array.append waits invokevirtual_mc *)
	  | `Special cn -> 
	     let cms = make_cms cn ms in
	     let m_wcet = get_wcet_method cms mm in
	     x + Array.length LW.invokestatic_mc + m_wcet
	  (* Array.append waits invokestatic_mc *)
	  | `Static cn ->
	     let cn1 = cn_simple_name cn in
	     let mn1 = ms_name ms in
	     let cms = make_cms cn ms in
	     if cn1 = "Native" then
	       (match mn1 with
	       | "rd" -> x + Array.length LW.jopsys_rd
	       | "wr" -> x + Array.length LW.jopsys_wr
	       | "wrMem" -> x + Array.length LW.jopsys_wr
	       | "rdMem" -> x + Array.length LW.jopsys_rd
	       | "rdIntMem" -> x + Array.length LW.jopsys_rdint
	       | "wrIntMem" -> x + Array.length LW.jopsys_wrint
	       | "getSP" -> x + Array.length LW.jopsys_getsp
	       | "getVP" -> x + Array.length LW.jopsys_getvp
	       | "setSP" -> x + Array.length LW.jopsys_setsp
	       | "setVP" -> x + Array.length LW.jopsys_setvp
	       | "int2extMem" -> x + Array.length (LW.jopsys_int2ext op)
	       | "ext2intMem" -> x + Array.length (LW.jopsys_ext2int op)
	       | "makeLong" -> x + Array.length LW.jopsys_nop
	       | "invoke" -> x + Array.length LW.invoke_vpsave
	       | "toInt" -> x + Array.length LW.jopsys_nop
	       | "toFloat" -> x + Array.length LW.jopsys_nop
	       | "toObject" -> x + Array.length LW.jopsys_nop
	       | "toIntArray" -> x + Array.length LW.jopsys_nop
	       | "toLong" -> x + Array.length LW.jopsys_nop
	       | "toDouble" -> x + Array.length LW.jopsys_nop
	       | "monitorExit" -> x + Array.length LW.monitorexit
	       | "monitorEnter" -> x + Array.length LW.monitorenter
	       | "condMove" -> x + Array.length LW.jopsys_cond_move
	       | "condMoreRef" -> x + Array.length LW.jopsys_cond_move
	       | "invalidate" -> x + Array.length LW.jopsys_inval
	       | "memCopy" -> x + Array.length LW.jopsys_memcpy
	       | "putStatic" -> x + Array.length LW.jopsys_putstatic
	       | "getStatic" -> x + Array.length LW.jopsys_getstatic
	       | "putField" -> x + Array.length LW.jopsys_putfield
	       | "getField" -> x + Array.length LW.jopsys_getfield
	       | "arrayLoad" -> x + Array.length LW.iaload
	       | "arrayStore" -> x + Array.length LW.iastore
	       | "arrayLength" -> x + Array.length LW.arraylength
	       | "count" -> x + Array.length LW.jopsys_count
	       | "hc" -> x + Array.length LW.jopsys_hc
	       | _ -> 
		  let m_wcet = get_wcet_method cms mm in
		  x + Array.length LW.invokestatic_mc + m_wcet)
	     else
	       let m_wcet = get_wcet_method cms mm in
	       x + Array.length LW.invokestatic_mc + m_wcet)
       | _ -> raise (Internal "Unexpected opcode"))
    | JL.OpMonitorExit -> x + Array.length LW.monitorexit
    | JL.OpMonitorEnter -> x + Array.length LW.monitorenter
    | JL.OpBreakpoint
    | JL.OpInvalid -> x
    | JL.OpGotoW _ as op -> raise (LW.Opcode_Not_Implemented (JDumpLow.opcode op))
    | JL.OpJsrW _ as op -> raise (LW.Opcode_Not_Implemented (JDumpLow.opcode op))
    | JL.OpIfNull _ 
    | JL.OpIfNonNull _ -> x + Array.length [|Nop;Jbr;Pop;Nop|]
    | JL.OpArrayLength -> x + Array.length LW.arraylength
    | JL.OpThrow -> 
       let mn = make_ms "f_athrow" [TObject (TClass (make_cn "java.lang.Throwable"))]
	 (Some (TObject (TClass (make_cn "java.lang.Throwable")))) in
       let m_wcet = get_wcet_method (make_cms (make_cn LW.bj1) mn) mm in
       (* XXX:  Should I add the time to load the callee and then load the caller into cache here! *)
       x + Array.length LW.invokestatic_mc + m_wcet
      (* The new bytecodes!! *)
    | JL.OpNew _ -> 
       let mn = make_ms "f_new" [(TBasic `Int)] (Some (TBasic `Int)) in
       let m_wcet = get_wcet_method (make_cms (make_cn LW.bj1) mn) mm in
       (* XXX:  Should I add the time to load the callee and then load the caller into cache here! *)
       x + Array.length (Array.append LW.newb LW.invokestatic_mc) + m_wcet
    | JL.OpNewArray _ 
    | JL.OpANewArray _ -> 
       let mn = make_ms "f_newarray" [(TBasic `Int);(TBasic `Int)] (Some (TBasic `Int)) in
       let m_wcet = get_wcet_method (make_cms (make_cn LW.bj1) mn) mm in
       (* XXX:  Should I add the time to load the callee and then load the caller into cache here! *)
       x + Array.length (Array.append LW.newb LW.invokestatic_mc) + m_wcet
    | JL.OpAMultiNewArray _ as op -> raise (LW.Opcode_Java_Implemented (JDumpLow.opcode op))
    | JL.OpCheckCast _ -> 
       let mn = make_ms "f_checkcast" [(TBasic `Int);(TBasic `Int)] (Some (TBasic `Int)) in
       let m_wcet = get_wcet_method (make_cms (make_cn LW.bj1) mn) mm in
       (* XXX:  Should I add the time to load the callee and then load the caller into cache here! *)
       x + Array.length (Array.append LW.newb LW.invokestatic_mc) + m_wcet
    | JL.OpInstanceOf _ ->
       let mn = make_ms "f_instanceof" [(TBasic `Int);(TBasic `Int)] (Some (TBasic `Int)) in
       let m_wcet = get_wcet_method (make_cms (make_cn LW.bj1) mn) mm in
       (* XXX:  Should I add the time to load the callee and then load the caller into cache here! *)
       x + Array.length (Array.append LW.newb LW.invokestatic_mc) + m_wcet
  ) 0 code

let get_checkpoint_wcrc (mse, cps) mm cp = 
  List.map2
    (fun chkp (cn, ms) ->
      Array.map (function
      | Some chkp ->
	 (* TODO:  Now do something *)
	 let llc = JFile.get_class_low (JFile.class_path cp) cn in
	 let cnn = JLow2High.low2high_class llc in
	 let cpool = get_class (class_path cp) cn |> get_consts in
	 let cpool1 = DynArray.init (Array.length cpool) (fun i -> cpool.(i)) in
	 let m = JHigh2Low.h2l_acmethod cpool1 (JClass.get_method cnn ms) in
	 let mcode = List.map
	   (function
	   | JL.AttributeCode x -> Some (Lazy.force x)
	   | _ -> None) m.JL.m_attributes
      |> List.filter (function Some x -> true | _ -> false)
      |> List.hd in
	 let mcode = match mcode with
	   | Some x -> x.JL.c_code |> Array.enum |> Enum.skip chkp
	   | None -> raise (Internal ("Unexpected type")) in
	 Some (get_wcrc (make_cms cn ms) mcode mm cpool)
      | _ as s -> s) chkp) cps mse

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
    let callgraph = JProgram.get_callgraph_from_entries
      prta [(make_cms (make_cn cn) JProgram.main_signature)] in
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

    (* FIXME:  We should convert each method to its CFG before we do this! *)
    (* XXX: Note that the WCRC calculated here is only until the end of
       the method from the checkpoint at best!*)
    let cp_wcrc = get_checkpoint_wcrc (methods_to_explore, possible_checkpoints) mm cp in
    ()
  with
  | NARGS -> ()
     

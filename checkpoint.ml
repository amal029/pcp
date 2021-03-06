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
module CFG = Cfg

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
    raise (Internal ("Cannot find the cms: "
                     ^ (cn_name cn) ^ "." ^ (ms_name ms) ^ " in method-wcet cache!"))

let get_wcrc code mm const_pool = 
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
	  x + Array.length [|Ldi;Xor;Stm;Ldi;Xor;Stm;Stm;Stm;
			     Ldm;Ldi;Ushr;Ldm;
			     Ldi;Ushr;
			     Add;Ldm;Ldi;And;Ldm;Ldi;
			     And;Add;Ldi;Add;Ldi;Shr;Add;Ldi;Ushr;Ldm;Add;
			     Ldm;Add;Ldm;Ldm;Add;Ldi;Add|]
       | _ -> x + Array.length [|Sub|])
    | JL.OpMult xx as op->
       (match xx with
       | `Double -> raise (LW.Opcode_Not_Implemented (JDumpLow.opcode op))
       | `Long -> 
	  let mn = make_ms "f_lmul" [(TBasic `Long);(TBasic `Long)] (Some (TBasic `Long)) in
	  let m_wcet = get_wcet_method (make_cms (make_cn LW.bj1) mn) mm in
	 (* XXX:  Should I add the time to load the callee 
            and then load the caller into cache here! *)
	  x + Array.length LW.invokestatic_mc + m_wcet
       | `Float -> raise (LW.Opcode_Java_Implemented (JDumpLow.opcode op))
       | _ -> x + 35) (* Note that imul never accesses external memory!! *)
    | JL.OpDiv xx as op ->
       (match xx with
       | `Double -> raise (LW.Opcode_Not_Implemented (JDumpLow.opcode op))
       | _ -> 
	  let mn = make_ms "f_idiv" [(TBasic `Int);(TBasic `Int)] (Some (TBasic `Int)) in
	  let m_wcet = get_wcet_method (make_cms (make_cn LW.bj1) mn) mm in
	    (* XXX:  Should I add the time to load the callee 
               and then load the caller into cache here! *)
	  x + Array.length LW.invokestatic_mc + m_wcet)
    | JL.OpRem xx as op ->
       (match xx with
       | `Double -> raise (LW.Opcode_Not_Implemented (JDumpLow.opcode op))
       | _ -> 
	  let mn = make_ms "f_irem" [(TBasic `Int);(TBasic `Int)] (Some (TBasic `Int)) in
	  let m_wcet = get_wcet_method (make_cms (make_cn LW.bj1) mn) mm in
	    (* XXX:  Should I add the time to load the 
               callee and then load the caller into cache here! *)
	  x + Array.length LW.invokestatic_mc + m_wcet)
    | JL.OpNeg xx as op ->
       (match xx with 
       | `Long -> x + Array.length
          (Array.append [|Ldi;Xor;Stm;Ldi;Xor;Ldm;Ldi;Ldi|] LW.long_add)
       | `Double -> raise (LW.Opcode_Not_Implemented (JDumpLow.opcode op))
       | `Float -> raise (LW.Opcode_Java_Implemented (JDumpLow.opcode op))
       | _ -> x + Array.length [|Ldi;Xor;Ldi;Add|]) 
    | JL.OpIShl -> x + 1
    | JL.OpIShr -> x + 1
    | JL.OpIUShr -> x + 1
    | JL.OpLShl -> x + Array.length
       (Array.append (Array.append LW.lshl LW.lshl_not0) LW.lshl_le31)
    | JL.OpLShr -> x + Array.length (Array.append LW.lshr LW.lshr_le31)
    | JL.OpLUShr -> x + Array.length
       (Array.append (Array.append LW.lushr LW.lushr_le31) LW.lushr_not0)
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
	 (* XXX:  Should I add the time to 
            load the callee and then load the caller into cache here! *)
       x + Array.length LW.invokestatic_mc + m_wcet
    | JL.OpD2L as op -> raise (LW.Opcode_Java_Implemented (JDumpLow.opcode op))
    | JL.OpI2B -> 
       let mn = make_ms "f_i2b" [(TBasic `Int)] (Some (TBasic `Int)) in
       let m_wcet = get_wcet_method (make_cms (make_cn LW.bj1) mn) mm in
	 (* XXX:  Should I add the time to load 
            the callee and then load the caller into cache here! *)
       x + Array.length LW.invokestatic_mc + m_wcet
      (* raise (LW.Opcode_Java_Implemented (JDumpLow.opcode op)) *)
    | JL.OpI2F as op -> raise (LW.Opcode_Java_Implemented (JDumpLow.opcode op))
    | JL.OpI2S as op -> raise (LW.Opcode_Java_Implemented (JDumpLow.opcode op))
    | JL.OpI2D as op -> raise (LW.Opcode_Not_Implemented (JDumpLow.opcode op))
    | JL.OpIInc _ -> x + Array.length [|Ldvp;Ld_opd_8u;Add;Star;Ld_opd_8u;Ldmi;Stmi|]
    | JL.OpLCmp -> 
       let mn = make_ms "f_lcmp"
         [(TBasic `Int);(TBasic `Int);(TBasic `Int);(TBasic `Int)] (Some (TBasic `Int)) in
       let m_wcet = get_wcet_method (make_cms (make_cn LW.bj1) mn) mm in
	 (* XXX:  Should I add the time to 
            load the callee and then load the caller into cache here! *)
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
				   Nop;Ld_opd_16u;Add;Dup;Stmraf;Ldi;Add;
                                   Stm;Wait;Wait;Ldmrd;Ldm;Stmraf;Wait;Wait;Ldmrd;
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
				    Ldi;Sub;Stjpc;Nop;Nop;Ldm;Nop;Ld_opd_8u;
                                    Ldi;And;Dup;Add;Add;Stm;Nop;Nop;Ld_opd_16u;Ldm;Jmp;Nop;Nop
				  |])
       | OpPutStatic (_,xx) ->
	  (match (fs_type xx) with
	  | TBasic xx ->
	     (match xx with
	     | `Long -> x + Array.length [|Stm;Stm;Ld_opd_16u;Dup;Stmwa;
                                           Ldm;Stmwd;Ldi;Add;Wait;Wait;
					   Stmwa;Ldm;Stmwd;Wait;Wait;Nop|]
	     | _ -> x + Array.length [|
	       Ldjpc;Ldi;Sub;Stjpc;Nop;Nop;Ldm;Nop;Ld_opd_8u;Ldi;And;Dup;Add;Add;Stm;Nop;Nop;
	       Ld_opd_16u;Ldm;Jmp;Nop;Nop
				     |])
	  | _ -> x + Array.length [|Ldjpc;Ldi;Sub;
				    Stjpc;Nop;Nop;Ldm;Nop;Ld_opd_8u;Ldi;And;
                                    Dup;Add;Add;Stm;Nop;Nop;Ld_opd_16u;Ldm;Jmp;Nop;Nop
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
	 Some (get_wcrc mcode mm cpool)
      | _ as s -> s) chkp) cps mse

(* This gives insertion points at the bytecode level *)
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
	| Ifd ((_,_,_),g) -> [Some (pc_ir2bc bir).(g-1); Some (pc_ir2bc bir).(i)]
	| _ -> [None]) (code bir) in
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
    let ret = Array.append (Array.to_list lnums |> List.flatten |> Array.of_list) loop_fbbnums in
    ret |> Array.to_list |> List.unique_hash |> Array.of_list
  with
  | Not_found -> raise (Internal ("Cannot find class_method:" ^ (cn_name cn) ^"."^ (ms_name ms)))
  | JControlFlow.PP.NoCode (cn, ms) -> Array.make 1 None

let rec cfg_wcrc visited cfg = 
  if List.is_empty cfg.CFG.o then
    cfg.CFG.wcet
  else
    let is_back_edge d =
      match List.Exceptionless.find ((==) d) visited with
      | Some x -> true
      | None -> false in
    let edges_not_analyzedp = function
      | CFG.Edge (_,_,Some _,_) -> false
      | _ -> true in
    let analyze_edges = function
      | CFG.Edge (s,d,None,l) as t ->
	 if is_back_edge d then t
	 else CFG.Edge(s,d, Some (cfg_wcrc (d :: visited) d),l)
      | _ as s -> s in
    (if List.exists edges_not_analyzedp cfg.CFG.o then
       let new_edges = List.map analyze_edges cfg.CFG.o in
       cfg.CFG.o <- new_edges);

    let edge_wcrcs =
      List.map
	(function
	  | CFG.Edge (_,_,Some x,_) -> x
	  | CFG.Edge (_,d, None,_) ->
	     if is_back_edge d then 0
	     else raise (Internal "Unexpected type")) cfg.CFG.o in
    cfg.CFG.wcet + List.fold_left max (List.hd edge_wcrcs) (List.tl edge_wcrcs)

let rec method_wcet pbir cp visited mm cfg = 
  let llc = JFile.get_class_low (JFile.class_path cp) cfg.CFG.cn in
  let cnn = JLow2High.low2high_class llc in
  let cpool = get_class (class_path cp) cfg.CFG.cn |> get_consts in
  let cpool1 = DynArray.init (Array.length cpool) (fun i -> cpool.(i)) in
  let m = JHigh2Low.h2l_acmethod cpool1 (JClass.get_method cnn cfg.CFG.ms) in
  let mcode = List.map
		(function
		  | JL.AttributeCode x -> Some (Lazy.force x)
		  | _ -> None) m.JL.m_attributes
	      |> List.filter (function Some x -> true | _ -> false)
	      |> List.hd in
  let mcode = match mcode with
    | Some x -> x.JL.c_code
    | None -> raise (Internal ("Unexpected type")) in

  (* TODO: Now get the program points at the bytecode level for this
  basic block *)
  let bir = JControlFlow.PP.get_first_pp pbir cfg.CFG.cn cfg.CFG.ms
	    |> JControlFlow.PP.get_ir in
  (* FIXME:  Check what happens when pps = 0? *)
  let bytecode_pps = if cfg.CFG.pps = 0 then 0
		     else
		       let bb = (pc_ir2bc bir).(cfg.CFG.pps-1) in
		       bb + LW.get_size mcode.(bb) in
  let bytecode_ppe = (pc_ir2bc bir).(cfg.CFG.ppe) in
  let bytecode_ppe = bytecode_ppe + LW.get_size mcode.(bytecode_ppe) in
  (* print_endline "HUHU"; *)
  (* print_endline ((string_of_int bytecode_pps) ^ " " ^ (string_of_int bytecode_ppe)); *)
  cfg.CFG.lpps <- Some bytecode_pps;
  cfg.CFG.lppe <- Some bytecode_ppe;
  (* XXX: Now I have the program points at the low-level to calculate
  the wcet of this basic block *)
  let mcode = Array.enum mcode
	      |> Enum.skip bytecode_pps
	      |> Enum.take (bytecode_ppe - bytecode_pps) in
  (* Dump the code in mcode *)
  (* let () = Enum.iter (fun x -> print_endline (JDumpLow.opcode x)) (Enum.clone mcode) in *)
  let rr = get_wcrc mcode mm cpool in
  (* print_endline ("wcrc is: " ^ (string_of_int rr)); *)
  cfg.CFG.wcet <- rr;
  List.iter
    (function
      | CFG.Edge (s,d,_,_) ->
	 match List.Exceptionless.find ((==) d) visited with
	 | Some x -> ()
	 | None ->
	    method_wcet pbir cp (cfg :: visited) mm d) cfg.CFG.o
  
let rec get_fbb visited cfg = 
  visited := (cfg :: !visited);
  let is_back_edge d =
    match List.Exceptionless.find ((==) d) !visited with
    | Some x -> true
    | None -> false in

  List.iter
    (function
    | CFG.Edge (_,d,_,_) ->
       if not (is_back_edge d) then
	 get_fbb visited d) cfg.CFG.o

(* This function adds chkpts to the edges of the cfg *)
let rec add_chkpt visited chkpts (cfg, fbb) = 
  visited := cfg :: !visited;
  let is_back_edge d =
    match List.Exceptionless.find ((==) d) !visited with
    | Some x -> true
    | None -> false in

  let edges =
    List.map
      (function
      | CFG.Edge (s,d,w,_) as e ->
	 (* We need to change this part! *)
	 if Array.exists ((=) d.CFG.lpps) chkpts
	 then
	   let reachable = ref (!visited) in
	   let () = get_fbb reachable d in
	   (* DEBUG *)
	   let () = match d.CFG.lpps, d.CFG.lppe with
	     | Some x, Some y -> print_endline (string_of_int x);
				 print_endline (string_of_int y)
	     | _ -> () in
	   let () = print_endline "HULU" in
	   let () = List.iter (function
				| (Some x, Some y) -> print_endline (string_of_int x);
						      print_endline (string_of_int y)
				| _ -> ()) (List.map (fun x -> (x.CFG.lpps, x.CFG.lppe))
							!reachable) in
	   if List.exists ((=) fbb) !reachable then
	     CFG.Edge(s,d,w,d.CFG.lpps)
	   else e
	 else e) cfg.CFG.o in
  cfg.CFG.o <- edges;
  List.iter
    (function
    | CFG.Edge (_,d,_,_) ->
       if not (is_back_edge d) then
	 add_chkpt visited chkpts (d, fbb)) cfg.CFG.o

let get_loops cp l cfg =
  let llc = JFile.get_class_low (JFile.class_path cp) cfg.CFG.cn in
  let cnn = JLow2High.low2high_class llc in
  let cpool = get_class (class_path cp) cfg.CFG.cn |> get_consts in
  let cpool1 = DynArray.init (Array.length cpool) (fun i -> cpool.(i)) in
  let m = JHigh2Low.h2l_acmethod cpool1 (JClass.get_method cnn cfg.CFG.ms) in
  let mcode =
    List.map
      (function
	| JL.AttributeCode x -> Some (Lazy.force x)
	| _ -> None) m.JL.m_attributes
    |> List.filter (function Some x -> true | _ -> false)
    |> List.hd in
  let lnt = match mcode with
    | Some mx ->
       let attr_l = mx.JL.c_attributes in
       let lnt = List.find (function | JL.AttributeLineNumberTable _ -> true | _ -> false) attr_l in
       (match lnt with
	| JClassLow.AttributeLineNumberTable x -> x
	| _ -> raise (Internal "Could not get the line-number-table!"))
    | None -> raise (Internal ("Unexpected type")) in
  let lnt = List.map(fun (x,y) -> (y,x)) lnt in
  (* XXX:  DEBUG *)
  (* let () = print_endline "Printing the line number table: " in *)
  (* let () = List.iter (fun (x,y) -> (string_of_int x) ^ ":" ^ (string_of_int y) |> print_endline) lnt in *)
  (* Get the loop-wcet-bound in terms of low-level byte-code *)
  let bounds =
    try
      Hashtbl.find l (cn_name cfg.CFG.cn)
    with
    | Not_found -> raise (Internal ("class: " ^ (cn_name cfg.CFG.cn)
  				    ^ " does not have loop bounds!")) in
  let bounds = DynArray.to_list bounds |> List.map (fun (x,y) -> ((int_of_string x),(int_of_string y))) in
  (* TODO:  attach the bytecode to the loop-bound *)
  let bounds = List.map (fun (x,y) ->
			 let (_,b) = List.find (fun (s, _) -> x = s) lnt in (b,y)) bounds in
  (* XXX:  DEBUG *)
  (* let () = print_endline "Printing the bounds" in *)
  (* let () = List.iter (fun (x,y) -> (string_of_int x) ^ ":" ^ (string_of_int y) |> print_endline) bounds in *)
  let rec get_bound_list visited cfg = 
    let is_back_edge d =
      match List.Exceptionless.find ((==) d) visited with
      | Some x -> true
      | None -> false in
    if List.is_empty cfg.CFG.o then []
    else
      let blist =
	List.map
	  (function
	    | CFG.Edge (s,d,_,_) ->
	       if is_back_edge d then
		 (* TODO:  Now you do something *)
		 let (_,bound) =
		   let lpps = match d.CFG.lpps with
		     | Some x -> x
		     | None -> raise (Internal "lpps not initialized") in
		   let lppe = match d.CFG.lppe with
		     | Some x -> x
		     | None -> raise (Internal "lppe not initialized") in
		   (* TODO:  There should be exactly one pp in bounds included in lpps and lppe *)
		   let res = List.find_all (fun (x,_) -> x >= lpps && x < lppe) bounds |> List.unique in
		   if List.length res = 1 then
		     List.hd res
		   else
		     (* let () = (string_of_int lpps) ^ "," ^ (string_of_int lppe) |> print_endline in *)
		     (* let () = (print_endline >> string_of_int >> List.length) res in *)
		     (* let () = List.iter (fun (x,y) -> *)
		     (* 			 (print_string >> ((^) " ") >> string_of_int) x; *)
		     (* 			 (print_endline >> ((^) " ") >> string_of_int) y) res in *)
		     raise (Internal "More than one loop bound detected!") in
		 [(d.CFG.lpps, s.CFG.lppe, bound)]
	       else
		 get_bound_list (d :: visited) d) cfg.CFG.o in
      List.flatten blist in
  let bound_list = get_bound_list [] cfg in
  (* XXX:  DEBUG *)
  let () = print_endline "Printing loop bounds" in
  let () =
    List.iter
      (function
  	| (Some x, Some y, z) -> 
	"(" ^ (string_of_int x) ^ ", " ^ (string_of_int y) ^ ", " ^ (string_of_int z) ^ ")"
  				 |> print_endline
  	| _ -> raise (Internal "Cannot find loop bounds!")) bound_list in
  bound_list


(* This function updates the wcet values with the loop bounds *)
let rec update_wcet visited blist cfg =
  visited := (cfg :: !visited);
  let lpps = match cfg.CFG.lpps with
    | Some x -> x
    | None -> raise (Internal "lpps not initialized") in
  let lppe = match cfg.CFG.lppe with
    | Some x -> x
    | None -> raise (Internal "lppe not initialized") in
  let is_back_edge d =
    match List.Exceptionless.find ((==) d) !visited with
    | Some x -> true
    | None -> false in
  (* TODO: First get the bounds that apply to this basic block*)
  let multiplicand =
    print_endline "\n";
    print_endline ("lpps, lppe: " ^ (string_of_int lpps) ^ "," ^ (string_of_int lppe));
    List.fold_left
      (fun v bound ->
       match bound with
       | (s,e,b) ->
	  print_endline ("s, e: " ^ (string_of_int s) ^ "," ^ (string_of_int e));
	  if lpps >= s && lppe <= e then v*b else v) 1 blist in
  print_endline ("Multiplicand: " ^ (string_of_int multiplicand));
  print_endline ("wcet before multiplying: " ^ (string_of_int cfg.CFG.wcet));
  cfg.CFG.wcet <- cfg.CFG.wcet * multiplicand;
  print_endline ("wcet after multiplying: " ^ (string_of_int cfg.CFG.wcet));
  (* XXX: Recurse if this is not a back-edge*)
  List.iter
    (function
      | CFG.Edge (_,d,_,_) ->
	 if not (is_back_edge d) then
           update_wcet visited blist d) cfg.CFG.o
  
let main = 
  try
    let args = DynArray.make 2 in
    let sourcep = ref "" in
    let speclist = [
	("-sourcepath", Arg.String (fun x -> sourcep := x), "Source path for parsing loop count");
      ] in
    let () = Arg.parse speclist (fun x -> DynArray.add args x) (usage_msg^"\n[OPTION]:") in
    let (cp, cn) = 
      if DynArray.length args <> 2 then
        let () = print_endline usage_msg;
          Arg.usage speclist "[OPTION]:" in exit 1
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
		      (* prta [(make_cms (make_cn cn) JProgram.main_signature)] in *)
		      prta [(make_cms (make_cn cn) (make_ms "start" [] None))] in
    (if not (List.is_empty callgraph) then
       let () = JProgram.store_callgraph callgraph "/tmp/Callgraph.txt" in
       raise (Not_supported "Only a single method allowed, please inline manually, see /tmp/Callgraph.txt"));
    let methods_to_explore = [((make_cn cn), (make_ms "start" [] None))]  in
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

    (* (\* XXX:  DEBUG *\) *)
    let () = print_endline "IF AND LOOP FIRST BB CHECKPOINTS" in
    let () =
      List.iter2 (fun a (cn, ms) ->
    	let () = print_endline ((cn_name cn) ^ "." ^ (ms_name ms)) in
    	Array.iter(function
    	| Some x -> x |> string_of_int |> print_endline
    	| None -> ()) a) possible_checkpoints methods_to_explore in

    (* TODO:  Now get the wcet of the various methods *)
    let method_cfgs =
      List.map (fun (x,y) -> CFG.build_method_cfg x y pbir) methods_to_explore in
    (* XXX:  DEBUG *)
    (* let () = List.iter (CFG.print_cfg []) method_cfgs in *)

    (* XXX: "l" is a assoc-list where is the key is the class-name and
       the values are array of tuples of type: (line_num, loop-bound)*)
    let l = LW.parsewca !sourcep in
    (* XXX: We do not provide the loop-bounds to this thing! *)
    let mm = LW.internal_main cp cn (Hashtbl.create 1) true in
    (* TODO: attach the wcet for each BB in method_cfgs *)
    let () = List.iter (method_wcet pbir cp [] mm) method_cfgs in
    (* TODO:  Now compute the wcet with the loop-bounds! *)
    let bound_list = List.map (get_loops cp l) method_cfgs in
    let bound_list =
      List.map (fun l ->
		List.map
		  (function
		    | (Some x, Some y, z) -> (x,y,z)
		    | _ -> raise (Internal "Unitialized loop bounds")) l ) bound_list in
    let bound_list = List.map (fun l -> BatList.unique l) bound_list in
    (* TODO:  Update the wcet values with the loop_bounds *)
    let () = List.iter2 (update_wcet (ref [])) bound_list method_cfgs in
    (* TODO:  Computed the wcrc of the edges, this function is side-effecting *)
    ignore(List.map (cfg_wcrc []) method_cfgs);
    (* Get the final BB *)
    let bb_cmp c1 c2 = Pervasives.compare c1.CFG.lppe c2.CFG.lppe in
    let fbbs = List.map (fun x ->
			 let fbb = ref [] in
			 let () = get_fbb fbb x in
			 List.last (List.fast_sort bb_cmp !fbb)) method_cfgs in
    (* TODO:  Now add the checkpoint to the edges *)
    let () = List.iter2 (add_chkpt (ref [])) possible_checkpoints (List.combine method_cfgs fbbs) in
    (* XXX:  DEBUG*)
    List.iter (CFG.print_cfg []) method_cfgs;
    let wcet =
      List.map (fun cfg ->
		match (List.hd cfg.CFG.o) with
		| CFG.Edge(_,_,Some x,_) -> x
		| _ -> raise (Internal "Cannot get the wcet!")) method_cfgs in
    (* XXX:  DEBUG*)
    print_endline "WCET IS: ";
    List.iter (print_endline >> string_of_int) wcet;
    (* TODO: Now we need to insert Native.wcrc into the method at the
       checkpoint bytecode along with the wcrc value *)
    let rec get_checkpts visited cfg = 
      let is_back_edge d =
	match List.Exceptionless.find ((==) d) visited with
	| Some x -> true
	| None -> false in
      if List.is_empty cfg.CFG.o then []
      else
	(* TODO: Now collect the checkpoints from edges and assoc them *)
	List.map
	  (function
	    | CFG.Edge(_,d,wcrc,chkpt) -> 
	       if not (is_back_edge d) then
		 (match (chkpt,wcrc) with
		  | (Some x, Some y) -> [(x,y)]
		  | _ ->[]) @
		   (get_checkpts (d :: visited) d)
	       else []) cfg.CFG.o |> List.flatten in
    let checkpts_assoc_list = List.map (get_checkpts []) method_cfgs in
    (* FIXME:  Change the method bytecode! *)
    let rec update_branches doit start index code =
      (* let () = (print_endline >> string_of_int) index in *)
      List.mapi
	(fun i code ->
	 match code with
	 | OpIfCmp (xx,target) as s ->
	    if (not doit) && (i+target+start) > index then
	      OpIfCmp (xx, target+5)
	    else if doit && ((target+start+i) < index) then
	      OpIfCmp(xx, target-5)
	    else s
	 | OpIf (xx, target) as s ->
	    if (not doit) && (target+i+start) > index then
	      OpIf (xx, target+5)
	    else if doit && ((target+start+i) < index) then
	      OpIf(xx, target-5)
	    else s
	 | OpGoto target as s ->
	    (* let () = JPrint.jopcode s |> print_endline in *)
	    if (not doit) && (target+i+start) > index then
	      OpGoto (target + 5)
	    else if doit && ((target+start+i) < index) then
	      OpGoto (target - 5)
	    else s
	 | OpTableSwitch _
	 | OpLookupSwitch _ -> raise (Not_supported "Class switch statements not supported")
	 | _ as s -> s)
	code
    in
    let prta =
      List.fold_left2
	(fun p (mcn, mms) achkp ->
	 JProgram.map_program
	   (fun cn ms code ->
	    if (cn_equal mcn cn) && (ms_equal mms ms) then
	      let achkp = BatList.unique_cmp achkp in
	      let achkp = List.fast_sort (fun (i,_) (j,_) -> compare i j) achkp in
	      let (jcode,_) =
		List.fold_left
		  (fun (jcode, count) (i, wcrc) ->
		   (* TODO: Update the array correctly here *)
		   let new_code = [
		       OpConst (`Int (Int32.of_int wcrc)); OpInvalid; (* 2 bytes *)
		       OpInvoke ((`Static (make_cn "com.jopdesign.sys.Native")),
				 (make_ms "wcrc" [(TBasic `Int)] None));
		       OpInvalid; OpInvalid; (* 3 bytes *)
		     ] in
		   let p_code, n_code = List.takedrop (i+count) (Array.to_list jcode) in
		   (Array.of_list ((update_branches false 0 (i+count) p_code) @ new_code @
				     (update_branches true (i+count) (i+count) n_code)),
		    count+5)) (code.c_code, 0) achkp in
	      {code with c_code = jcode}
	    else code) None p) prta methods_to_explore checkpts_assoc_list in
    (* Output *)
    (* JPrint.print_class (JProgram.to_ioc (JProgram.get_node prta (make_cn cn))) JPrint.jcode stdout; *)
    unparse_class (JProgram.to_ioc (JProgram.get_node prta (make_cn cn))) (open_out_bin (cn^".class"));
  with
  | NARGS -> ()
	       

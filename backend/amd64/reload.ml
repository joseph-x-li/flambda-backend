# 2 "backend/amd64/reload.ml"
(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 2000 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)
[@@@ocaml.warning "+4"]

open Cmm
open Reg
open Mach

(* Reloading for the AMD64 *)

(* Summary of instruction set constraints:
   "S" means either stack or register, "R" means register only.
   Operation                    Res     Arg1    Arg2
     Imove                      R       S
                             or S       R
     Iconst_int                 S if 32-bit signed, R otherwise
     Iconst_float               R
     Iconst_symbol (not PIC)    S
     Iconst_symbol (PIC)        R
     Icall_ind                          R
     Itailcall_ind                      R
     Iload                      R       R       R
     Istore                             R       R
     Iintop(Icomp)              R       R       S
                            or  R       S       R
     Iintop(Imul|Idiv|Imod)     R       R       S
     Iintop(Imulh)              R       R       S
     Iintop(shift)              S       S       R
     Iintop(others)             R       R       S
                            or  S       S       R
     Iintop_imm(Iadd, n)/lea    R       R
     Iintop_imm(Icomp _)        R       S
     Iintop_imm(others)         S       S
     Iintop(Ipopcnt|Iclz|Ictz)  R       S
     Inegf...Idivf              R       R       S
     Ifloatofint                R       S
     Iintoffloat                R       S
     Ispecific(Ilea)            R       R       R
     Ispecific(Ifloatarithmem)  R       R       R
     Ispecific(Icrc32q)         R       R       S   (and Res = Arg1)
     Ispecific(Irdtsc)          R
     Ispecific(Irdpmc)          R       R           (Arg1 = rcx)
     Ispecific(Ifloat_iround)   R       S
     Ispecific(Ifloat_round _)  R       S
     Ispecific(Ifloat_min)      R       R       S   (and Res = Arg1)
     Ispecific(Ifloat_max)      R       R       S   (and Res = Arg1)

   Conditional branches:
     Iinttest                           S       R
                                    or  R       S
     Ifloattest                         R       S    (or  S R if swapped test)
     other tests                        S
*)

let stackp r =
  match r.loc with
    Stack _ -> true
  | Reg _ | Unknown -> false

let imm operands ~index =
  if Array.length operands > index then
    match operands.(index) with
    | Iimm n -> Some n
    | Ireg _ | Imem _ -> None
  else
    None

let is_immediate operands ~index =
  if Array.length operands > index then
    match operands.(index) with
    | Iimm _ -> true
    | Ireg _ | Imem _ -> false
  else
    false

let is_stack arg operands ~index =
  if Array.length operands > index then
    match operands.(index) with
    | Iimm _ -> false
    | Ireg j -> stackp arg.(j)
    | Imem _ -> assert false
  else begin
      assert (Array.length arg > index);
      stackp arg.(index)
    end

let same_loc_arg0_res0 arg res operands =
  if Array.length operands > 0 then
    match operands.(0) with
    | Ireg j -> Reg.same_loc arg.(j) res.(0)
    | Iimm _ | Imem _ -> false
  else
    Reg.same_loc arg.(0) res.(0)

class reload = object (self)

inherit Reloadgen.reload_generic as super

method private one_stack arg =
  if stackp arg.(0) && stackp arg.(1)
  then [|arg.(0); self#makereg arg.(1)|]
  else arg

method private one_mem_or_stack arg operands =
  match Array.length operands with
  | 0 ->
    self#one_stack arg
  | n ->
     match operands.(0), operands.(1) with
     | Iimm _, _ | _, Iimm _ -> arg
     | Ireg _, Ireg _ -> self#one_stack arg
     | Imem _, Imem _ -> assert false
     | Imem (_,_,r), Ireg j | Ireg j, Imem (_,_,r) ->
         assert (Array.for_all (fun i -> not (stackp arg.(i))) r);
         if stackp arg.(j) then
           arg.(j) <- self#makereg arg.(j);
         arg
(* First argument (= result) must be in register, second arg
         can reside in the stack or memory or immediate *)
method private same_reg_res0_arg0 arg res operands =
  if is_stack arg operands ~index:0
  then begin
    let r = self#makereg arg.(0) in
    arg.(0) <- r;
    (arg, [|r|])
  end else (arg, res)

method! reload_operation op arg res operands =
  let arg = Array.copy arg in
  (* If operand.(i) is a memory access, force any Reg.t it refers to
     to be in reg, not on the stack. *)
  Array.iter (function
      | Ireg _ | Iimm _ -> ()
      | Imem (_,_, r) ->
          Array.iter (fun j ->
            if stackp arg.(j) then
              arg.(j) <- self#makereg arg.(j))
            r)
    operands;
  match op with
  | Iintop(Iadd) when (not (same_loc_arg0_res0 arg res operands))
                      && is_immediate operands ~index:1 ->
      (* This add will be turned into a lea; args and results must be
         in registers *)
      super#reload_operation op arg res operands
  | Iintop(Iadd|Isub|Iand|Ior|Ixor|Icheckbound) ->
      (* One of the two arguments can reside in the stack or memory, but not both *)
      (self#one_mem_or_stack arg operands, res)
  | Iintop (Icomp _) ->
      (* One of the two arguments can reside in the stack, but not both.
         The result must be in a register. *)
      let res =
        if stackp res.(0) then [| self#makereg res.(0) |] else res
      in
      (self#one_mem_or_stack arg operands, res)
  | Ispecific Ifloat_iround
  | Ispecific (Ifloat_round _) ->
      (* The argument(s) can be either in register or on stack.
         The result must be in a register. *)
      let res =
        if stackp res.(0) then [| self#makereg res.(0) |] else res
      in
      (arg, res)
  | Iintop(Imulh _ | Idiv | Imod | Ilsl | Ilsr | Iasr) ->
      (* The argument(s) and results can be either in register or on stack *)
      (* Note: Imulh, Idiv, Imod: arg(0) and res(0) already forced in regs
               Ilsl, Ilsr, Iasr: arg(1) already forced in regs *)
      (arg, res)
  | Iintop(Imul) | Ifloatop (Iaddf | Isubf | Imulf | Idivf) ->
      (* First argument (= result) must be in register, second arg
         can reside in the stack *)
      self#same_reg_res0_arg0 arg res operands
  | Ispecific (Irdtsc | Irdpmc) ->
      (* Irdtsc: result must be in register.
         Irdpmc: result must be in register, arg.(0) already forced in reg. *)
      if stackp res.(0)
      then (let r = self#makereg res.(0) in (arg, [|r|]))
      else (arg, res)
  | Ispecific(Ifloat_min | Ifloat_max)
  | Ispecific Icrc32q ->
    (* First argument and result must be in the same register.
       Second argument can be either in a register or on stack. *)
      self#same_reg_res0_arg0 arg res operands
  | Ifloatop(Icompf _) ->
    (* First argument is forced to be the same as the second result,
       and it must be in register. *)
      if stackp res.(1)
      then (let r = self#makereg res.(1) in ([|r; arg.(1)|], [|res.(0); r|]))
      else (arg, res)
  | Ifloatofint | Iintoffloat ->
      (* Result must be in register, but argument can be on stack *)
      (arg, (if stackp res.(0) then [| self#makereg res.(0) |] else res))
  | Iconst_int n ->
      if n <= 0x7FFFFFFFn && n >= -0x80000000n
      then (arg, res)
      else super#reload_operation op arg res operands
  | Iconst_symbol _ ->
      if !Clflags.pic_code || !Clflags.dlcode || Arch.win64
      then super#reload_operation op arg res operands
      else (arg, res)
  | Iintop (Ipopcnt | Iclz _| Ictz _) ->
      (* Result must be in register, but argument can be on stack *)
      (arg, (if stackp res.(0) then [| self#makereg res.(0) |] else res))
  | Ispecific  (Isqrtf | Isextend32 | Izextend32 | Ilea _
               | Istore_int (_, _, _)
               | Ioffset_loc (_, _)
               | Iprefetch _
               | Ibswap _)
  | Imove|Ispill|Ireload|Ifloatop(Inegf|Iabsf)
  | Iconst_float _|Icall_ind|Icall_imm _
  | Itailcall_ind|Itailcall_imm _|Iextcall _|Istackoffset _|Iload (_, _)
  | Istore (_, _, _)|Ialloc _|Iname_for_debugger _|Iprobe _|Iprobe_is_enabled _
  | Iopaque
    -> (* Other operations: all args and results in registers *)
      super#reload_operation op arg res operands

method! reload_test tst arg operands =
  match tst with
    Iinttest _ ->
      (* One of the two arguments can reside on stack *)
      self#one_mem_or_stack arg operands
  | Ifloattest (CFlt | CFnlt | CFle | CFnle | CFeq
               | CFneq | CFgt | CFngt | CFge | CFnge) ->
      (* Second argument can be on stack, first must be in register *)
      if is_stack arg operands ~index:0 then arg.(0) <- self#makereg arg.(0);
      arg
  | Itruetest
  | Ifalsetest
  | Ioddtest
  | Ieventest ->
      (* The argument(s) can be either in register or on stack *)
      arg

end

let fundecl f num_stack_slots =
  (new reload)#fundecl f num_stack_slots

(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Insert load/stores for pseudoregs that got assigned to stack locations. *)

open Misc
open Reg
open Mach

let operands rv = Array.map (fun r -> Ireg r) rv

let insert_move src dst next =
  if src.loc = dst.loc
  then next
  else instr_cons (Iop Imove) [|dst|] [|Ireg src|] next

let insert_moves src dst next =
  let rec insmoves i =
    if i >= Array.length src
    then next
    else insert_move src.(i) dst.(i) (insmoves (i+1))
  in insmoves 0

let insert_moves_operands src dst next =
  let rec insmoves i =
    if i >= Array.length src
    then next
    else begin
      (* CR gyorsh: the following assumes that target's reload can only
         change the registers refered to by operands but not the shape
         of operands. Later if we represent load and store using operands,
         we can also generate move between  memory and register here. *)
      match src.(i), dst.(i) with
      | o, o' when Mach.equal_operand o o' -> insmoves (i+1)
      | Ireg r_src, Ireg r_dst -> insert_move r_src r_dst (insmoves (i+1))
      | Imem (c,a,rv), Imem (c',a',rv')
        when Cmm.equal_memory_chunk c c' &&
             Arch.equal_addressing_mode a a' ->
        insert_moves rv rv' (insmoves (i+1))
      (* | (Imem _ | Iimm _ | Iimmf _), Ireg r when not (Reg.is_stack r) ->
       *   insert_move src.(i) r (insmoves (i+1))
       * | Ireg r, Imem _ when not (Reg.is_stack r) ->
       *   insert_move src.(i) dst.(i) (insmoves (i+1)) *)
      | (Ireg _ | Imem _ | Iimm _ | Iimmf _),_  ->
        Misc.fatal_errorf "Reloadgen.insert_moves_operands: mismatch %d" i ()
    end
  in insmoves 0

class reload_generic = object (self)

val mutable redo_regalloc = false

method makereg r =
  match r.loc with
    Unknown -> fatal_error "Reload.makereg"
  | Reg _ -> r
  | Stack _ ->
      redo_regalloc <- true;
      let newr = Reg.clone r in
      (* Strongly discourage spilling this register *)
      newr.spill_cost <- 100000;
      newr

method private makeregs rv =
  Array.init (Array.length rv) (fun i -> self#makereg rv.(i))

method makereg_operand o =
  match o with
  | Iimm _ | Iimmf _ -> o
  | Ireg r -> Ireg (self#makereg r)
  | Imem (c, a, rv) -> Imem (c, a, self#makeregs rv)

method private makeregs_operands ov =
  Array.init (Array.length ov) (fun i -> self#makereg_operand ov.(i))

method private makereg1 ov =
  let newv = Array.copy ov in
  newv.(0) <- self#makereg_operand ov.(0);
  newv

(* If operand.(i) is a memory access, force any Reg.t it refers to
   to be in hardware reg, not on the stack. *)
method makeregs_for_mem_operands operands =
  Array.map (fun operand ->
    match operand with
    | Ireg _ | Iimm _ | Iimmf _ -> operand
    | Imem (c,a,rv) -> Imem (c,a,self#makeregs rv))
    operands;

method reload_operation op res operands =
  let operands = self#makeregs_for_mem_operands operands in
  (* By default, assume that arguments and results must reside
     in hardware registers. For moves, allow one arg or one
     res to be stack-allocated, but do something for
     stack-to-stack moves *)
  match op with
  | Imove | Ireload | Ispill ->
    begin match operands.(0) with
    | Ireg r ->
      begin match r.loc, res.(0).loc with
      |  Stack s1, Stack s2 when s1 <> s2 ->
        ([| Ireg (self#makereg r) |], res)
      | _ ->
        (operands, res)
      end
    | Iimm _ | Iimmf _ -> (operands, res)
    | Imem _ ->
      Misc.fatal_errorf "Reloadgen.reload_operation: \
                         Imove from memory not supported, use Istore."
    end
  | Iprobe _ ->
    (* No constraints on where the arguments reside,
       so that the presence of a probe does not affect
       register allocation of the rest of the code. *)
    (operands, res)
  | Iopaque ->
      (* arg = result, can be on stack or register *)
      assert (Mach.arg_reg operands.(0).stamp = res.(0).stamp);
      (operands, res)
  | _ ->
      (self#makeregs_operands operands, self#makeregs res)

method reload_test _tst operands =
  self#makeregs_operands operands

method private reload i k =
  match i.desc with
    (* For function calls, returns, etc: the arguments and results are
       already at the correct position (e.g. on stack for some arguments).
       However, something needs to be done for the function pointer in
       indirect calls. *)
    Iend | Ireturn _ | Iop(Itailcall_imm _) | Iraise _ -> k i
  | Iop(Itailcall_ind) ->
      let newarg = self#makereg1 i.operands in
      k (insert_moves_operands i.operands newarg
           (Mach.copy i ~operands:newarg))
  | Iop(Icall_imm _ | Iextcall _) ->
      self#reload i.next (fun next -> k (Mach.copy i ~next))
  | Iop(Icall_ind) ->
      let newarg = self#makereg1 i.operands in
      self#reload i.next (fun next ->
        k (insert_moves_operands i.operands newarg
             (Mach.copy i ~operands:newarg ~next)))
  | Iop op ->
      let (newarg, newres) = self#reload_operation op i.res i.operands in
      self#reload i.next (fun next ->
        k (insert_moves_operands i.operands newarg
             (Mach.copy i ~operands:newarg ~res:newres
                     ~next:(insert_moves (operands newres) i.res next))))
  | Iifthenelse(tst, ifso, ifnot) ->
      let newarg = self#reload_test tst i.operands in
      self#reload ifso (fun ifso ->
        self#reload ifnot (fun ifnot ->
          self#reload i.next (fun next ->
            k (insert_moves_operands i.operands newarg
                 (instr_cons (Iifthenelse(tst, ifso, ifnot))
                    newarg [||] i.operands next)))))
  | Iswitch(index, cases) ->
      let newarg = self#makeregs_operands i.operand in
      let cases = Array.map (fun case -> self#reload case Fun.id) cases in
      self#reload i.next (fun next ->
        k (insert_moves_operands i.operands newarg
             (instr_cons (Iswitch(index, cases)) [||] newarg next)))
  | Icatch(rec_flag, ts, handlers, body) ->
      let new_handlers = List.map
          (fun (nfail, ts, handler) -> nfail, ts, self#reload handler Fun.id)
          handlers in
      self#reload body (fun body ->
        self#reload i.next (fun next ->
          k (instr_cons (Icatch(rec_flag, ts, new_handlers, body))
               [||] [||] next)))
  | Iexit (i, traps) ->
      k (instr_cons (Iexit (i, traps)) [||] [||] dummy_instr)
  | Itrywith(body, kind, (ts, handler)) ->
      self#reload body (fun body ->
        self#reload handler (fun handler ->
          self#reload i.next (fun next ->
            k (instr_cons (Itrywith(body, kind, (ts, handler)))
                 [||] [||] next))))

method fundecl f num_stack_slots =
  redo_regalloc <- false;
  let new_body = self#reload f.fun_body Fun.id in
  ({fun_name = f.fun_name; fun_args = f.fun_args;
    fun_body = new_body; fun_codegen_options = f.fun_codegen_options;
    fun_dbg  = f.fun_dbg;
    fun_contains_calls = f.fun_contains_calls;
    fun_num_stack_slots = Array.copy num_stack_slots;
   },
   redo_regalloc)
end

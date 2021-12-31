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

(* Selection of pseudo-instructions, assignment of pseudo-registers,
   sequentialization. *)

type environment

val env_add
   : ?mut:Asttypes.mutable_flag
  -> Backend_var.With_provenance.t
  -> Reg.t array
  -> environment
  -> environment

val env_find : Backend_var.t -> environment -> Reg.t array

val size_expr : environment -> Cmm.expression -> int

(* During selection, the shape of operands is chosen before the arguments
   are converted from Cmm expression to Mach expressions. This module
   specifies how to construct operands and then emit them
   once the registers are determined in which the result of
   argument evaluation is place. *)
module Operands : sig
  type t                  (** a constructor for operand array  *)
  type operand_builder (** a constructor for a single operand  *)

  val mem : Cmm.memory_chunk option -> Arch.addressing_mode ->
    index:int -> len:int -> operand_builder
  val reg : index:int -> operand_builder
  val imm : Targetint.t -> operand_builder
  val immf : int64 -> operand_builder

  val selected : operand_builder array -> t
  val in_registers : unit -> t
  val emit : t -> Reg.t array -> Mach.operand array

  (* val is_immediate : t -> index:int -> bool *)
end

module Effect : sig
  type t =
    | None
    | Raise
    | Arbitrary
end

module Coeffect : sig
  type t =
    | None
    | Read_mutable
    | Arbitrary
end

module Effect_and_coeffect : sig
  type t

  val none : t
  val arbitrary : t

  val effect : t -> Effect.t
  val coeffect : t -> Coeffect.t

  val effect_only : Effect.t -> t
  val coeffect_only : Coeffect.t -> t
  val create : Effect.t -> Coeffect.t -> t

  val join : t -> t -> t
  val join_list_map : 'a list -> ('a -> t) -> t
end

class virtual selector_generic : object
  (* The following methods must or can be overridden by the processor
     description *)
  method is_immediate_int : Mach.operation -> int -> bool
    (* Must be overriden to indicate whether an integer constant
       is a suitable immediate operand to the given arithmetic instruction.
       The default implementation handles shifts by immediate amounts,
       but produces no immediate operations otherwise. *)
  method is_immediate_float : Mach.operation -> float -> bool
    (* Can be overriden to indicate whether a float constant is a suitable
       immediate operand to the given arithmetic instruction. *)
  method virtual is_immediate_test_int : Mach.test -> int -> bool
    (* Must be defined to indicate whether an integer constant is a suitable
       immediate operand to the given test *)
  method is_immediate_test_float : Mach.test -> float -> bool
    (* Can be be defined to indicate whether a float constant is a suitable
       immediate operand to the given test *)
  method virtual select_addressing :
    Cmm.memory_chunk -> Cmm.expression ->
    Arch.addressing_mode * Cmm.expression * int
    (* Must be defined to select addressing modes *)
  method is_simple_expr: Cmm.expression -> bool
  method effects_of : Cmm.expression -> Effect_and_coeffect.t
    (* Can be overridden to reflect special extcalls known to be pure *)
  method select_operation :
    Cmm.operation ->
    Cmm.expression list ->
    Debuginfo.t ->
    Mach.operation * Cmm.expression list * Operands.t
    (* Can be overridden to deal with special arithmetic instructions *)
  method swap_operands : Mach.operation -> Mach.operation option
    (* Can be overridden to deal with special operands whose
       arguments can be swapped.
       Returns [Some new_op] for binary operations whose arguments
       can be swapped and the corresponding operation to use
       for swapped arguments. Otherwise, returns [None],
       in particualr  if the operation is not binary
       or not commutative.*)
  method select_operands :
    Mach.operation ->
    Cmm.expression list ->
    Mach.operation * Cmm.expression list * Operands.t
    (* Can be overridden to deal with special operands *)
  method select_operands_condition :
    Mach.test ->
    Cmm.expression list ->
    Mach.test * Cmm.expression * Operands.t
    (* Can be overridden to deal with special operands *)
  method select_condition :
    Cmm.expression ->
    Mach.test * Cmm.expression * Operands.t
    (* Can be overridden to deal with special test instructions *)
  method select_store :
    bool -> Cmm.memory_chunk option -> Arch.addressing_mode -> int ->
    Cmm.expression -> Mach.operation * Cmm.expression * Operands.t
    (* Can be overridden to deal with special store constant instructions *)
  method memory_operands_supported : Mach.operation -> Cmm.memory_chunk -> bool
    (* Can be overridden to enable memory operands selection *)
  method memory_operands_supported_condition :
    Mach.test -> Cmm.memory_chunk -> bool
    (*  Can be overridden to enable memory operands selection *)
  method regs_for : Cmm.machtype -> Reg.t array
    (* Return an array of fresh registers of the given type.
       Default implementation is like Reg.createv.
       Can be overridden if float values are stored as pairs of
       integer registers. *)
  method insert_op :
    environment -> Mach.operation -> Mach.operand array -> Reg.t array
      -> Reg.t array
    (* Can be overridden to deal with 2-address instructions
       or instructions with hardwired input/output registers *)
  method insert_op_debug :
    environment -> Mach.operation -> Debuginfo.t -> Mach.operand array
      -> Reg.t array -> Reg.t array
    (* Can be overridden to deal with 2-address instructions
       or instructions with hardwired input/output registers *)
  method insert_move_extcall_arg :
    environment -> Cmm.exttype -> Reg.t array -> Reg.t array -> unit
    (* Can be overridden to deal with unusual unboxed calling conventions,
       e.g. on a 64-bit platform, passing unboxed 32-bit arguments
       in 32-bit stack slots. *)
  method emit_extcall_args :
    environment -> Cmm.exttype list -> Cmm.expression list -> Reg.t array * int
    (* Can be overridden to deal with stack-based calling conventions *)
  method emit_stores :
    environment -> Cmm.expression list -> Reg.t array -> unit
    (* Fill a freshly allocated block.  Can be overridden for architectures
       that do not provide Arch.offset_addressing. *)

  method mark_call : unit
  (* informs the code emitter that the current function is non-leaf:
     it may perform a (non-tail) call; by default, sets
     [contains_calls := true] *)

  method mark_tailcall : unit
  (* informs the code emitter that the current function may end with
     a tail-call; by default, does nothing *)

  method mark_c_tailcall : unit
  (* informs the code emitter that the current function may call
     a C function that never returns; by default, does nothing.

     It is unnecessary to save the stack pointer in this situation
     (which is the main purpose of tracking leaf functions) but some
     architectures still need to ensure that the stack is properly
     aligned when the C function is called. This is achieved by
     overloading this method to set [contains_calls := true] *)

  method mark_instr : Mach.instruction_desc -> unit
  (* dispatches on instructions to call one of the marking function
     above; overloading this is useful if Ispecific instructions need
     marking *)

  (* The following method is the entry point and should not be overridden. *)
  method emit_fundecl : Cmm.fundecl -> ppf_dump:Format.formatter -> Mach.fundecl

  (* The following methods should not be overridden.  They cannot be
     declared "private" in the current implementation because they
     are not always applied to "self", but ideally they should be private. *)
  method extract : Mach.instruction
  method insert :
    environment -> Mach.instruction_desc -> Mach.operand array -> Reg.t array
    -> unit
  method insert_debug :
    environment -> Mach.instruction_desc -> Debuginfo.t ->
       Mach.operand array -> Reg.t array -> unit
  method insert_move : environment -> Reg.t -> Reg.t -> unit
  method insert_move_args :
    environment -> Reg.t array -> Reg.t array -> int -> unit
  method insert_move_results :
    environment -> Reg.t array -> Reg.t array -> int -> unit
  method insert_moves : environment -> Reg.t array -> Reg.t array -> unit
  method emit_expr :
    environment -> Cmm.expression -> Reg.t array option
  method emit_tail : environment -> Cmm.expression -> unit

  (* [contains_calls] is declared as a reference instance variable,
     instead of a mutable boolean instance variable,
     because the traversal uses functional object copies. *)
  val contains_calls : bool ref
end

val reset : unit -> unit

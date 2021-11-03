(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1997 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

class reload_generic : object
  method reload_operation :
    Mach.operation -> Reg.t array -> Mach.operand array ->
    Mach.operand array * Reg.t array
  method reload_test : Mach.test -> Mach.operand array ->
    Reg.t array
    (* Can be overridden to reflect instructions that can operate
       directly on stack locations *)
  method makereg : Reg.t -> Reg.t
    (* Can be overridden to avoid creating new registers of some class
       (i.e. if all "registers" of that class are actually on stack) *)
  method fundecl : Mach.fundecl -> int array -> Mach.fundecl * bool
    (* The entry point *)

  (* The following methods should not be overridden.  They are provided
     as utilities to be used in classes that inherit from reloadgen. *)
  method makeregs_for_memory : Mach.operand array -> Mach.operand array
     (*  Force all "registers" used by memory operands to be in hardware
         registers, not on the stack. *)
  method makeregs_operands : Mach.operand array -> Mach.operand array
     (*  Force all "registers" referred to by the operands
         to be in hardware registers, not on the stack. *)
end

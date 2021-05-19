(* CR-soon xclerc for xclerc: use the same warning set as flambda2. *)
[@@@ocaml.warning "+a-40-41-42"]
open! Int_replace_polymorphic_compare[@@ocaml.warning "-66"]

type basic_or_terminator =
  | Basic of Cfg.basic
  | Terminator of Cfg.terminator

let basic_or_terminator_of_operation
  : Mach.operation -> fun_name:string -> basic_or_terminator
  = fun op ~fun_name ->
    match op with
    | Imove ->
      Basic (Op Move)
    | Ispill ->
      Basic (Op Spill)
    | Ireload ->
      Basic (Op Reload)
    | Iconst_int i ->
      Basic (Op (Const_int i))
    | Iconst_float f ->
      Basic (Op (Const_float f))
    | Iconst_symbol s ->
      Basic (Op (Const_symbol s))
    | Icall_ind { label_after; } ->
      Basic (Call (F (Indirect { label_after; })))
    | Icall_imm { func; label_after; } ->
      Basic (Call (F (Direct { func_symbol = func; label_after; })))
    | Itailcall_ind { label_after; } ->
      Terminator (Tailcall (Func (Indirect { label_after; })))
    | Itailcall_imm { func; label_after; } ->
      Terminator
        (Tailcall
           (if String.equal fun_name func then
              Self { label_after; }
            else
              Func (Direct { func_symbol = func; label_after; })))
    | Iextcall { func; alloc; label_after; } ->
      Basic (Call (P (External { func_symbol = func; alloc; label_after; })))
    | Istackoffset ofs ->
      Basic (Op (Stackoffset ofs))
    | Iload (mem, mode) ->
      Basic (Op (Load (mem, mode)))
    | Istore (mem, mode, assignment) ->
      Basic (Op (Store (mem, mode, assignment)))
    | Ialloc { bytes; label_after_call_gc; dbginfo; spacetime_index; } ->
      Basic
        (Call
           (P (Alloc { bytes; label_after_call_gc; dbginfo; spacetime_index; })))
    | Iintop op ->
      Basic (Op (Intop op))
    | Iintop_imm (op, imm) ->
      Basic (Op (Intop_imm (op, imm)))
    | Inegf ->
      Basic (Op Negf)
    | Iabsf ->
      Basic (Op Absf)
    | Iaddf ->
      Basic (Op Addf)
    | Isubf ->
      Basic (Op Subf)
    | Imulf ->
      Basic (Op Mulf)
    | Idivf ->
      Basic (Op Divf)
    | Ifloatofint ->
      Basic (Op Floatofint)
    | Iintoffloat ->
      Basic (Op Intoffloat)
    | Ispecific op ->
      Basic (Op (Specific op))
    | Iname_for_debugger { ident; which_parameter; provenance; is_assignment; } ->
      Basic (Op (Name_for_debugger { ident; which_parameter; provenance; is_assignment; }))
    | Iprobe { name; handler_code_sym; } ->
      Basic (Op (Probe { name; handler_code_sym; }))
    | Iprobe_is_enabled { name; } ->
      Basic (Op (Probe_is_enabled { name; }))

let float_test_of_float_comparison
  : Cmm.float_comparison -> label_false:Label.t -> label_true:Label.t -> Cfg.float_test
  = fun comparison ~label_false ~label_true ->
    let lt, eq, gt, uo =
      match comparison with
      | CFeq  -> label_false, label_true,  label_false, label_false
      | CFneq -> label_true,  label_false, label_true,  label_true
      | CFlt  -> label_true,  label_false, label_false, label_false
      | CFnlt -> label_false, label_true,  label_true,  label_true
      | CFgt  -> label_false, label_false, label_true,  label_false
      | CFngt -> label_true,  label_true,  label_false, label_true
      | CFle  -> label_true,  label_true,  label_false, label_false
      | CFnle -> label_false, label_false, label_true,  label_true
      | CFge  -> label_false, label_true,  label_true,  label_false
      | CFnge -> label_true,  label_false, label_false, label_true in
    { lt; eq; gt; uo; }

let int_test_of_integer_comparison
  : Cmm.integer_comparison
    -> signed:bool
    -> immediate:int option
    -> label_false:Label.t
    -> label_true:Label.t
    -> Cfg.int_test
  = fun comparison ~signed:is_signed ~immediate:imm ~label_false ~label_true ->
    let lt, eq, gt =
      match comparison with
      | Ceq -> label_false, label_true,  label_false
      | Cne -> label_true,  label_false, label_true
      | Clt -> label_true,  label_false, label_false
      | Cgt -> label_false, label_false, label_true
      | Cle -> label_true,  label_true,  label_false
      | Cge -> label_false, label_true,  label_true in
     { lt; eq; gt; is_signed; imm; }

let terminator_of_test
  : Mach.test -> label_false:Label.t -> label_true:Label.t -> Cfg.terminator
  = fun test ~label_false ~label_true ->
    let int_test comparison immediate =
      let signed, comparison =
        match comparison with
        | Mach.Isigned comparison -> true, comparison
        | Mach.Iunsigned comparison -> false, comparison in
      int_test_of_integer_comparison comparison ~signed ~immediate ~label_false ~label_true in
    match test with
    | Itruetest ->
      Truth_test { ifso = label_true; ifnot = label_false; }
    | Ifalsetest ->
      Truth_test { ifso = label_false; ifnot = label_true; }
    | Iinttest comparison ->
      Int_test (int_test comparison None)
    | Iinttest_imm (comparison, value) ->
      Int_test (int_test comparison (Some value))
    | Ifloattest comparison ->
      Float_test (float_test_of_float_comparison comparison ~label_false ~label_true)
    | Ioddtest ->
      Parity_test { ifso = label_false; ifnot = label_true; }
    | Ieventest ->
      Parity_test { ifso = label_true; ifnot = label_false; }

(* CR-soon xclerc for xclerc: double check whether it should be reset for each function. *)
let get_next_instruction_id
  : unit -> int
  =
  let next_instruction_id = ref 0 in
  fun () ->
    let res = !next_instruction_id in
    incr next_instruction_id;
    res

let copy_instruction
  : type a . Mach.instruction -> desc:a -> trap_depth:int -> a Cfg.instruction
  = fun instr ~desc ~trap_depth ->
    let { Mach.
          arg; res; dbg; live;
          desc = _; next = _; available_before = _; available_across = _;
        } = instr in
    let id = get_next_instruction_id () in
    { desc; arg; res; dbg; live; trap_depth; id; }

let can_raise_operation
  : Cfg.operation -> bool
  = fun op ->
    match op with
    | Move -> false
    | Spill -> false
    | Reload -> false
    | Const_int _ -> false
    | Const_float _ -> false
    | Const_symbol _ -> false
    | Stackoffset _ -> false
    | Load _ -> false
    | Store _  -> false
    | Intop _ -> false
    | Intop_imm _ -> false
    | Negf -> false
    | Absf -> false
    | Addf -> false
    | Subf -> false
    | Mulf -> false
    | Divf -> false
    | Floatofint -> false
    | Intoffloat -> false
    | Probe _ -> false (* CR xclerc for xclerc: double check *)
    | Probe_is_enabled _ -> false (* CR xclerc for xclerc: double check *)
    | Specific _ -> false (* CR xclerc for xclerc: double check *)
    | Name_for_debugger _ -> false

let can_raise_instr
  : Cfg.basic Cfg.instruction -> bool
  = fun instr ->
    match instr.desc with
    | Op op -> can_raise_operation op
    | Call _ -> true
    | Reloadretaddr -> false
    | Pushtrap _ -> false
    | Poptrap -> false
    | Prologue -> false

let can_raise_instrs
  : Cfg.basic Cfg.instruction list -> bool
  = fun instrs ->
    List.exists can_raise_instr instrs

let can_raise_terminator
  : Cfg.terminator -> bool
  = fun terminator ->
    match terminator with
    | Never -> false
    | Always _ -> false
    | Parity_test _ -> false
    | Truth_test _ -> false
    | Float_test _ -> false
    | Int_test _ -> false
    | Switch _ -> false
    | Return -> false
    | Raise _ -> true
    | Tailcall _ -> false

type block_info = {
  instrs : Cfg.basic Cfg.instruction list;
  last : Mach.instruction;
  terminator : Cfg.terminator option;
  can_raise : bool;
}

(* [extract_block_info first ~fun_name ~trap_depth] returns a [block_info]
   containing all the instructions starting from [first] until some kind of
   control flow is encountered or the end of the block is reached (i.e. [Iend]).
   If the returned terminator is [None], it is guaranteed that the [last]
   instruction is not an [Iop] (as it would either be part of [instrs] or be
   a terminator). *)
let extract_block_info
  : Mach.instruction -> fun_name:string -> trap_depth:int -> block_info
  = fun first ~fun_name ~trap_depth ->
    let rec loop (instr : Mach.instruction) acc =
      let return terminator can_raise =
        let instrs = List.rev acc in
        let can_raise = can_raise || can_raise_instrs instrs in
        { instrs; last = instr; terminator; can_raise; } in
      match instr.desc with
      | Iop op ->
        begin match basic_or_terminator_of_operation op ~fun_name with
          | Basic desc ->
            loop instr.next (copy_instruction instr ~desc ~trap_depth :: acc)
          | Terminator terminator ->
            return (Some terminator) (can_raise_terminator terminator)
        end
      | Iend | Ireturn | Iifthenelse _ | Iswitch _
      | Icatch _ | Iexit _ | Itrywith _ ->
        return None false
      | Iraise _ ->
        return None true in
    loop first []

(* Represents the control flow exiting the function without encountering a return. *)
let fallthrough_label : Label.t = -1

module State : sig

  type t

  val make : Cfg.basic_block Label.Tbl.t -> t

  val add_block : t -> label:Label.t -> block:Cfg.basic_block -> unit

  val get_layout : t -> Label.t list

  val add_catch_handler : t -> handler_id:int -> label:Label.t -> unit

  val get_handler_label : t -> handler_id:int -> Label.t

end = struct

  type t = {
    blocks : Cfg.basic_block Label.Tbl.t;
    mutable layout : Label.t list;
    catch_handlers : Label.t Numbers.Int.Tbl.t;
  }

  let make blocks =
    let layout = [] in
    let catch_handlers = Numbers.Int.Tbl.create 31 in
    { blocks; layout; catch_handlers; }

  let add_block t ~label ~block =
    if Label.Tbl.mem t.blocks label then
      Misc.fatal_errorf "Cfgize.State.add_block duplicate block for label %d" label
    else begin
      t.layout <- label :: t.layout;
      Label.Tbl.replace t.blocks label block;
    end

  let get_layout t =
    List.rev t.layout

  let add_catch_handler t ~handler_id ~label =
    (* XCR gyorsh: fail if handler_id is already in the table?
       Previous passes are supposed to guarantee that handler ids are unique within
       a function, but it is easy to check and might pay off as we add new
       transformations (and bugs). *)
    if Numbers.Int.Tbl.mem t.catch_handlers handler_id then
      Misc.fatal_errorf "Cfgize.State.add_catch_handler duplicate handler %d" handler_id
    else
      Numbers.Int.Tbl.replace t.catch_handlers handler_id label

  let get_handler_label t ~handler_id =
    match Numbers.Int.Tbl.find_opt t.catch_handlers handler_id with
    | Some res -> res
    | None ->
      Misc.fatal_errorf "Cfgize.State.get_handler_label unknown handler_id %d"
        handler_id

end

(* [add_blocks instr state ~fun_name ~start ~exns ~trap_depth ~next] adds the block
   beginning at [instr] with label [start], and all recursively-reachable blocks to
   [state]; [next] is the label of the block to be executed after the one beginning
   at [instr]. *)
let rec add_blocks
  : Mach.instruction
    -> State.t
    -> fun_name:string
    -> start:Label.t
    -> exns:Label.Set.t
    -> trap_depth:int
    -> next:Label.t
    -> unit
  = fun instr state ~fun_name ~start ~exns ~trap_depth ~next ->
    let { instrs; last; terminator; can_raise; } =
      extract_block_info instr ~fun_name ~trap_depth in
    let terminate_block desc =
      State.add_block state ~label:start ~block:{
        start;
        body = instrs;
        terminator = (copy_instruction last ~desc ~trap_depth);
        predecessors = Label.Set.empty; (* See [update_blocks_with_predecessors] *)
        trap_depth;
        exns;
        (* XCR gyorsh: [can_raise] should be computed in cfgize either as a
           separate pass or add a field of [block_info] to record it.
           If / when we make calls as terminators, we won't need to compute
           it during extract_block_info.
        *)
        can_raise;
        (* XCR gyorsh: I think that [can_raise_interproc] is not used after computation of
           exceptional successors.
           xclerc: sorry I am not sure how to interpret your comment; should it be
           computed here? *)
        can_raise_interproc = false;
        (* CR gyorsh: [is_trap_handler] is needed for cfg_to_linear.
           where does cfgize compute it? *)
        is_trap_handler = false;
        dead = false;
      } in
    let prepare_next_block () =
      match last.next.desc with
      | Iend -> next, (fun () -> ())
      | Iop _ | Ireturn | Iifthenelse _ | Iswitch _
      | Icatch _ | Iexit _ | Itrywith _ | Iraise _ ->
        let start = Cmm.new_label () in
        let add_next_block () =
          add_blocks last.next state ~fun_name ~start ~exns ~trap_depth ~next in
        start, add_next_block in
    (* XCR gyorsh for gyorsh: it should be the same layout as linearize
       xclerc: is it a nice-to-have (e.g. for testing), or a hard requirement? *)
    match terminator with
    | Some terminator ->
      terminate_block terminator
    | None ->
      match last.desc with
      | Iop _ ->
        Misc.fatal_error "Cfgize.extract_block_info returned an Iop with no terminator"
      | Iend ->
        if Label.equal next fallthrough_label then
          Misc.fatal_error "Cfgize.add_blocks reached the end of a function without \
                            encountering a return"
        else
          terminate_block (Cfg.Always next)
      | Ireturn ->
        terminate_block Cfg.Return
      | Iifthenelse (test, ifso, ifnot) ->
        let label_true = Cmm.new_label () in
        let label_false = Cmm.new_label () in
        terminate_block (terminator_of_test test ~label_false ~label_true);
        let next, add_next_block = prepare_next_block () in
        add_blocks ifso state ~fun_name ~start:label_true ~exns ~trap_depth ~next;
        add_blocks ifnot state ~fun_name ~start:label_false ~exns ~trap_depth ~next;
        add_next_block ()
      | Iswitch (indexes, cases) ->
        let case_labels = Array.map (fun _ -> Cmm.new_label ()) cases in
        terminate_block (Cfg.Switch (Array.map (fun idx -> case_labels.(idx)) indexes));
        let next, add_next_block = prepare_next_block () in
        Array.iteri
          (fun idx case ->
             add_blocks case state ~fun_name ~start:case_labels.(idx) ~exns ~trap_depth ~next)
          cases;
        add_next_block ()
      | Icatch (_rec, handlers, body) ->
        let handlers =
          List.map
            (fun (handler_id, handler) ->
               let handler_label = Cmm.new_label () in
               State.add_catch_handler state ~handler_id ~label:handler_label;
               handler_label, handler)
            handlers in
        let body_label = Cmm.new_label () in
        terminate_block (Cfg.Always body_label);
        let next, add_next_block = prepare_next_block () in
        add_blocks body state ~fun_name ~start:body_label ~exns ~trap_depth ~next;
        List.iter
          (fun (handler_label, handler) ->
             add_blocks handler state ~fun_name ~start:handler_label ~exns ~trap_depth ~next)
          handlers;
        add_next_block ()
      | Iexit handler_id ->
        let handler_label = State.get_handler_label state ~handler_id in
        terminate_block (Cfg.Always handler_label)
      | Itrywith (body, handler) ->
        let label_body = Cmm.new_label () in
        let label_handler = Cmm.new_label () in
        terminate_block (Cfg.Always label_body);
        let next, add_next_block = prepare_next_block () in
        add_blocks body state ~fun_name ~start:label_body
          ~exns:(Label.Set.singleton label_handler) ~trap_depth:(succ trap_depth) ~next;
        add_blocks handler state ~fun_name ~start:label_handler ~exns ~trap_depth ~next;
        add_next_block ()
      | Iraise raise_kind ->
        terminate_block (Cfg.Raise raise_kind)

let update_blocks_with_predecessors
  : Cfg.t -> unit
  = fun cfg ->
  Label.Tbl.iter
    (fun block_label block ->
       let successor_labels = Cfg.successor_labels cfg ~normal:true ~exn:true block in
       Label.Set.iter
         (fun successor_label ->
            match Label.Tbl.find_opt cfg.blocks successor_label with
            | None ->
              Misc.fatal_errorf "Cfgize.update_blocks_with_predecessors received an \
                                 inconsistent graph (no block labelled %d)"
                successor_label
            | Some successor_block ->
              successor_block.predecessors <-
                Label.Set.add block_label successor_block.predecessors)
         successor_labels)
    cfg.blocks

let fundecl
  : Mach.fundecl -> preserve_orig_labels:bool -> Cfg_with_layout.t
  = fun fundecl ~preserve_orig_labels ->
    let { Mach.
          fun_name;
          fun_args = _;
          fun_body;
          fun_codegen_options = _;
          fun_dbg = _;
          fun_spacetime_shape = _;
          fun_num_stack_slots = _;
          fun_contains_calls = _; } = fundecl in
    let start_label = Cmm.new_label () in
    let tailrec_label = Cmm.new_label () in
    let cfg = Cfg.create ~fun_name ~fun_tailrec_entry_point_label:tailrec_label in
    let state = State.make cfg.blocks in
    (* XCR gyorsh: is this adding an extra block at the front of the layout? The start
       label of the very first block should be entry_label, tailrec_label comes after it,
       not the other way around.  *)
    State.add_block state ~label:(Cfg.entry_label cfg) ~block:{
      start = (Cfg.entry_label cfg);
      body = [];
      terminator = (copy_instruction fun_body ~desc:(Cfg.Always tailrec_label) ~trap_depth:0);
      predecessors = Label.Set.empty; (* See [update_blocks_with_predecessors] *)
      trap_depth = 0;
      exns = Label.Set.empty;
      (* CR xclerc for xclerc: double check that the following fields are indeed
         expected to be computed later. *)
      can_raise = false;
      can_raise_interproc = false;
      is_trap_handler = false;
      dead = false;
    };
    State.add_block state ~label:tailrec_label ~block:{
      start = tailrec_label;
      body = [];
      terminator = (copy_instruction fun_body ~desc:(Cfg.Always start_label)
                      (* XCR gyorsh: why is trap_depth 0 here?
                         xclerc: sorry, how could this block be under a
                         [try .. with ...] construct? *)
                      ~trap_depth:0);
      predecessors = Label.Set.empty; (* See [update_blocks_with_predecessors] *)
      trap_depth = 0;
      exns = Label.Set.empty;
      (* CR xclerc for xclerc: double check that the following fields are indeed
         expected to be computed later. *)
      can_raise = false;
      can_raise_interproc = false;
      is_trap_handler = false;
      dead = false;
    };
    add_blocks
      fun_body
      state
      ~fun_name
      ~start:start_label
      ~exns:Label.Set.empty
      ~trap_depth:0
      ~next:fallthrough_label;
    update_blocks_with_predecessors cfg;
    Cfg_with_layout.create
      cfg
      ~layout:(State.get_layout state)
      ~preserve_orig_labels
      (* CR xclerc for xclerc: double check that it is fine to return an empty set. *)
      ~new_labels:Label.Set.empty

(**********************************************************************************
 *                             MIT License                                        *
 *                                                                                *
 *                                                                                *
 * Copyright (c) 2021 Jane Street Group LLC                                       *
 *                                                                                *
 * Permission is hereby granted, free of charge, to any person obtaining a copy   *
 * of this software and associated documentation files (the "Software"), to deal  *
 * in the Software without restriction, including without limitation the rights   *
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell      *
 * copies of the Software, and to permit persons to whom the Software is          *
 * furnished to do so, subject to the following conditions:                       *
 *                                                                                *
 * The above copyright notice and this permission notice shall be included in all *
 * copies or substantial portions of the Software.                                *
 *                                                                                *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR     *
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,       *
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE    *
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER         *
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,  *
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE  *
 * SOFTWARE.                                                                      *
 *                                                                                *
 **********************************************************************************)
[@@@ocaml.warning "+a-30-40-41-42"]

(* let string_of_layout layout =
 *   List.map Int.to_string layout
 *   |> String.concat " "
 *
 * let check_layout cfg layout =
 *   (* [layout] is not empty and entry of cfg is the first node in the layout. *)
 *   (match layout with
 *    | [] -> Misc.fatal_errorf "Empty layout for %s" cfg.fun_name ()
 *    | hd::_ ->
 *      if not (Label.equal hd cfg.entry_label) then
 *        Misc.fatal_errorf "Cfg entry node %d is not the first first in the layout %s"
 *          cfg.entry_label cfg.fun_name ());
 *   (* No duplicates in layout *)
 *   let labels = Label.Set.of_list layout in
 *   let num_labels = Label.Set.cardinal layout in
 *   if List.compare_length_with layout num_labels  > 0 then
 *     Misc.fatal_errorf "Layout of %s contains duplicates: %s"
 *       cfg.fun_name (string_of_layout layout) ();
 *   (* The set of nodes in the layout is the same as the set of nodes in the cfg. *)
 *   let num_nodes = Label.Tbl.length cfg.blocks in
 *   if num_nodes > num_labels then
 *     Misc.fatal_error "Not all cfg nodes are in the layout" cfg.fun_name ();
 *   List.iter (fun label ->
 *     match Cfg.get_block cfg label with
 *     | Some _ -> ()
 *     | None -> Misc.fatal_error "Node not found for label %d in %s"
 *                 cfg.fun_name ()
 *   )
 *     layout
 *   let nodes = Label.Set.of_seq in
 *   if not ( Label.Set.equal cur_layout new_layout
 *       && Label.equal (List.hd layout) t.cfg.entry_label )
 *   then
 *     Misc.fatal_error
 *       "Cfg set_layout: new layout is not a permutation of the current \
 *        layout, or first label is not entry";
 *   t.layout <- layout
 *
 *
 * (* successors and predecessors agree *)
 * let check_edges cfg =
 *
 * let run cfg_with_layout =
 *   let cfg = Cfg_with_layout.cfg cfg_with_layout in
 *   let layout  =Cfg_with_layout.layout cfg_with_layout in
 *   (* check all Tailrec Self agree on the successory label *)
 *   check_entry cfg;
 *   check_layout cfg layout;
 *   check_edges cfg;
 *
 *   () *)

let run _ _ = true

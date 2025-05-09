(* Once you are done writing the code, remove this directive,
   whose purpose is to disable several warnings. *)
[@@@warning "-26-27-33"]

(* You should read and understand active_borrows.ml *fully*, before filling the holes
  in this file. The analysis in this file follows the same structure. *)

open Type
open Minimir

type analysis_results = label -> PlaceSet.t

let go prog mir : analysis_results =
  (* The set of all places appearing in the MIR code. We are not interesting in initializedness for places
    which are not member of this set. *)
  let all_places =
    (* The set of local places*)
    let acc =
      Hashtbl.fold
        (fun l _ acc -> PlaceSet.add (PlLocal l) acc)
        mir.mlocals PlaceSet.empty
    in
    (* We add all non local places to it*)
    let a = Array.fold_left
      (fun acc (i, _) ->
        match i with
        | Ideinit _ | Igoto _ | Ireturn -> acc
        | Iif (pl, _, _) -> PlaceSet.add pl acc
        | Icall (_, pls, pl, _) -> PlaceSet.add_seq (Seq.cons pl (List.to_seq pls)) acc
        | Iassign (pl, rv, _) -> (
            let acc = PlaceSet.add pl acc in
            match rv with
            | RVplace pl | RVborrow (_, pl) | RVunop (_, pl) -> PlaceSet.add pl acc
            | RVbinop (_, pl1, pl2) -> PlaceSet.add pl1 (PlaceSet.add pl2 acc)
            | RVmake (_, pls) -> PlaceSet.add_seq (List.to_seq pls) acc
            | RVunit | RVconst _ -> acc))
      acc mir.minstrs
      in 
      a
  in
  
  (* Printf.printf "All places:\n";
  PlaceSet.iter (fun p -> Print_minimir.pp_place ( Format.std_formatter) p ) all_places;
  Printf.printf "\n"; *)

  (* The set of subplaces of a given place. *)
  let subplaces = Hashtbl.create 7 in
  let () =
    PlaceSet.iter
      (fun pl ->
        let pls = PlaceSet.filter (fun pl_sub -> is_subplace pl_sub pl) all_places in
        Hashtbl.add subplaces pl pls)
      all_places
  in

  (* Printf.printf "Subplaces:\n";
  Hashtbl.iter ( fun pl pls -> 
    (Print_minimir.pp_place (Format.std_formatter) pl;
    Printf.printf " -> ";
      PlaceSet.iter (fun p -> Print_minimir.pp_place ( Format.std_formatter) p ) pls;
       Printf.printf "\n");
    )
    subplaces;
  Printf.printf "\n"; *)


  (* Effect of initializing a place [pl] on the abstract state [state]: [pl] and all its subplaces
    become initialized. Hence, given that the state is the set of uninitialized places, we remove
    the subplaces [pl] from the abstract state.

    It is important to understand that places can be nested. In order to make a place uninitialized,
    it is *not* enough to remove it from the state. One should also remove subplaces. *)
  let initialize pl state = PlaceSet.diff state (Hashtbl.find subplaces pl) in

  (* This is the dual: we are consuming or deinitiailizing place [pl], so all its subplaces
    become uninitialized, so they are added to [state]. *)
  let deinitialize pl state = PlaceSet.union state (Hashtbl.find subplaces pl) in

  (* Effect of using (copying or moving) a place [pl] on the abstract state [state]. *)
  let move_or_copy pl state =
    (* If the type of [pl] is Copy, we may move/copy it with nothing that changes*)
    if typ_is_copy prog (typ_of_place prog mir pl) then 
      state
    (* Otherwise, it is considered unitialized afterwards *)
    else
      deinitialize pl state
  in

  (* These modules are parameters of the [Fix.DataFlow.ForIntSegment] functor below. *)
  let module Instrs = struct let n = Array.length mir.minstrs end in

  let module Prop = struct
    type property = PlaceSet.t
    let leq_join p q = if PlaceSet.subset p q then q else PlaceSet.union p q
  end in

  let module Graph = struct
    type variable = int
    type property = PlaceSet.t


    (* Calls the go function for all entry points with corresponding abstract state 
    Only entry point = [mir.mentry];
    with abstract state = [all_places - (mir.locals places and their subplaces)]*)
    let foreach_root go =
      let local_vars = 
        Hashtbl.fold (fun l _ acc -> PlaceSet.add (PlLocal l) acc) mir.mlocals PlaceSet.empty
      in
      (* union of all subplaces of local_vars*)
      let local_vars_and_subplaces = 
        PlaceSet.fold (fun pl acc -> PlaceSet.union acc (Hashtbl.find subplaces pl)) local_vars PlaceSet.empty
      in
      go mir.mentry (PlaceSet.diff all_places local_vars_and_subplaces)



    (* The function [foreach_successor] should call the [go] parameter for each successor
    of [lbl], with the corresponding modified abstract state.

    For a given label, [Fix] will then automatically compute the join of the initial
    abstract state (if it exists) and of the modified states propagated by each of its
    predecessors. *)
    let foreach_successor lbl state go =
      (*removes pl and all its subplaces from state*)
      let assign pl state = 
        let pl_and_subplaces = Hashtbl.find subplaces pl in
        PlaceSet.diff state pl_and_subplaces
      in

      match fst mir.minstrs.(lbl) with
      | Iassign (pl, RVplace pl1, next) ->
        let state = move_or_copy pl1 state in
        go next (assign pl state)
      | Iassign (pl, _, next) -> go next (assign pl state)
      | Ideinit (l, next) -> go next (assign (PlLocal l) state)
      | Igoto next -> go next state
      | Iif (_, next1, next2) ->
          go next1 state;
          go next2 state
      | Ireturn -> ()
      | Icall (_, param, pl, next) -> 
        (* When calling a function, we de-initialise the places of the parameters. *)
        let state = List.fold_left (fun state pls -> deinitialize pls state ) state param in
        go next (assign pl state)

  end in
  let module Fix = Fix.DataFlow.ForIntSegment (Instrs) (Prop) (Graph) in
  
  fun i -> Option.value (Fix.solution i) ~default:PlaceSet.empty 
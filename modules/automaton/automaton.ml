(**
 * Automaton
 *
 * This class represents finite-state automatons.
 *)

(* type run = state list
   type word = letter list *)


let rec list_last = function
  | [] -> raise (Invalid_argument "list_last")
  | [e] -> e
  | t :: q -> list_last q
			
			
module type OrderedType =
  sig
    type t
    val compare : t -> t -> int
  end

module Make (State: OrderedType) (TrueLetter: OrderedType) = struct

  (*
   * The letter that we will use will be the "true letters" plus epsilon.
   * This will be encoded by a `TrueLetter.t option`, `None` representing
   * epsilon and `Some l` representing the true letter `l`.
   *)
  
  module StateSet  = Set.Make (State)

  (* Should not appear in signature *)
  module Letter = struct
    type t = TrueLetter.t option
    let compare l1 l2 =
      match (l1, l2) with
      | None     , None     ->  0
      | None     , _        -> -1
      | _        , None     ->  1
      | Some tl1 , Some tl2 -> TrueLetter.compare tl1 tl2
  end
  (* / Should not appear in signature *)

  module LetterSet = Set.Make (Letter)
  
  type state = StateSet.elt
  (** The type of the automaton states. *)

  type letter = LetterSet.elt
  (** The type of the automaton letters. *)

  (* Should not appear in signature *)
  module Transition = struct
    type t = State.t * Letter.t * State.t
    let compare (s1, l, s2) (s1', l', s2') =
      match State.compare s1 s1' with
      | 0 ->
	 (match State.compare s2 s2' with
	  | 0 ->
	     (Letter.compare l l')
	  | n -> n)
      | n -> n
  end
  (* / Should not appear in signature *)

  module TransitionSet = Set.Make (Transition)

  type t =
      { states        : StateSet.t
      ; start_states  : StateSet.t
      ; accept_states : StateSet.t
      ; transitions   : TransitionSet.t }
  (** The type of the automatons. *)
	
  let empty =
    { states        = StateSet.empty
    ; start_states  = StateSet.empty
    ; accept_states = StateSet.empty
    ; transitions   = TransitionSet.empty }
  (** The empty automaton. *)

  let is_empty a =
    (StateSet.is_empty a.states)
    && (StateSet.is_empty a.start_states)
    && (StateSet.is_empty a.accept_states)
    && (TransitionSet.is_empty a.transitions)
  (** Test whether an automaton is empty or not. *)

  let states a =
    StateSet.fold (fun s l -> s :: l) a.states []

  let add_state a s =
    { a with states = StateSet.add s a.states }
  (** [add_state a s] returns an automaton containing all states of [a], plus
      [s]. If [s] was already in [a], [a] is returned unchanged. *)

  let del_state a s =
    { states        = StateSet.remove s a.states
    ; start_states  = StateSet.remove s a.start_states
    ; accept_states = StateSet.remove s a.accept_states
    ; transitions   = TransitionSet.filter (fun (s1,l,s2) -> s1<>s&&s2<>s) a.transitions }
  (** [del_state a s] returns an automaton containing all states of [a], except
      [s]. If [s] was not in [a], [a] is returned unchanged. *)

  let start_states a =
    StateSet.fold (fun s l -> s :: l) a.start_states []

  let add_start_state a s =
    { states        = StateSet.add s a.states
    ; start_states  = StateSet.add s a.start_states
    ; accept_states = a.accept_states
    ; transitions   = a.transitions }
  (** [add_start_state a s] returns an automaton containing all states of [a],
      plus [s]. [s] is also marked as a start state. If [s] was already in [a],
      [s] is only marked as a start state. If [s] was already a start state in
      [a], [a] is returned unchanged. *)

  let del_start_state a s =
    { a with start_states = StateSet.remove s a.start_states }
  (** [del_start_state a s] returns an automaton containing all states of [a],
      but where [s] is not a start state. If [s] was not a start state in [a],
      [a] is returned unchanged. *)

  let clear_start_states a =
    { a with start_states = StateSet.empty }

  let accept_states a =
    StateSet.fold (fun s l -> s :: l) a.accept_states []

  let add_accept_state a s =
    { states        = StateSet.add s a.states
    ; start_states  = a.start_states
    ; accept_states = StateSet.add s a.accept_states
    ; transitions   = a.transitions }
  (** [add_accept_state a s] returns an automaton containing all states of [a],
      plus [s]. [s] is also marked as an accept state. If [s] was already in
      [a], [s] is only marked as an accept state. If [s] was already an accept
      state in [a], [a] is returned unchanged. *)

  let del_accept_state a s =
    { a with accept_states = StateSet.remove s a.accept_states }
  (** [del_accept_state a s] returns an automaton containing all states of [a],
      but where [s] is not an accept state. If [s] was not an accept state in
      [a], [a] is returned unchanged. *)

  let clear_accept_states a =
    { a with accept_states = StateSet.empty }

  let transitions a =
    TransitionSet.fold (fun tr l -> tr :: l) a.transitions []

  let add_transition a (s1, l, s2) =
    { states        = StateSet.add s1 (StateSet.add s2 a.states)
    ; start_states  = a.start_states
    ; accept_states = a.accept_states
    ; transitions   = TransitionSet.add (s1, l, s2) a.transitions }

  let del_transition a tr =
    { a with transitions = TransitionSet.remove tr a.transitions }

  let clear_transitions a =
    { a with transitions = TransitionSet.empty }

  let of_lists st_l sst_l ast_l tr_l =
    List.fold_left add_transition (List.fold_left add_accept_state (List.fold_left add_start_state (List.fold_left add_state empty st_l) sst_l) ast_l) tr_l

  let union a1 a2 =
    { states        = StateSet.union a1.states a2.states
    ; start_states  = StateSet.union a1.start_states a2.start_states
    ; accept_states = StateSet.union a1.accept_states a2.accept_states
    ; transitions   = TransitionSet.union a1.transitions a2.transitions }
		   
      
  let run a w = (* word = letter list *)
    let step a s l =
      TransitionSet.fold
	(fun (s1, l', s2) st_l -> if s1 = s && l' = l then s2 :: st_l else st_l)
	a.transitions
	[]
    in
    (* be carefull, this function is not doing what is expected. in particular,
       it is not handling the epsilon-transitions ! *)

    let epsilon_closure a sl =
      TransitionSet.fold
	(fun (s1, l, s2) st_l -> if (List.mem s1 sl) && l = None then s2 :: st_l else st_l)
	a.transitions
	sl
    in
    (* this function computes all the states you can reach spontaneously with an
       epsilon transition *)
    
    let rec run_aux s = function
      | [] -> [[s]]
      | l :: w' ->
	 (* all the states we can touch from s with letter l *)
	 let st_l' = step a s l in

	 (* all the runs we can find from these states with the other letters *)
	 let rn_l' = List.flatten (List.map (fun s' -> run_aux s' w') st_l') in

	 (* we add our state before *)
	 List.map (fun st_l -> s :: st_l) rn_l'
    in
    StateSet.fold (fun s rn_l -> (run_aux s w) @ rn_l) a.start_states []

  let accepts a w =
    if w = [] then
      not (StateSet.is_empty (StateSet.inter a.start_states a.accept_states))
    else
      List.exists
	(fun r -> StateSet.mem (list_last r) a.accept_states)
	(run a w)

end


(*-
 * /!\ I should only use sets in this module, for efficiency (way more efficient than lists).
 *
 * TODO list
 *
 * - Add a way to define automatons with a state stream. That would be really
 *   usefull when we don't care about the state definition (the int stream would
 *   be a good example). That could be done in an other file.
 *
 * - Add an other module defining deterministic automatons.
 *
 * - Handle epsilon transition
 *
 * - Add determinization of automatons
 *)

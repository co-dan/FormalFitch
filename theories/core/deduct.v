(* Fitch proofs: (pre)deductions and associated definitions *)
From stdpp Require Export base strings.
From fitch Require Import prelude.

(** * Formulas *)

(** Atomic formulas - for now just abstract variables P, Q, R... *)
Definition atom := string.

#[global] Instance atom_eqdecision : EqDecision atom.
Proof. solve_decision. Qed.

(** Compound formulas, →, ∧ for now *)
Inductive frml :=
| fAtomic : atom -> frml
| fImpl : frml -> frml -> frml
| fConj : frml -> frml -> frml
.

Declare Scope frml_scope.
Delimit Scope frml_scope with F.

Notation "A → B" := (fImpl A B)
  (at level 99, B at level 200, right associativity) : frml_scope.
Notation "A ∧ B" := (fConj A B)
  (at level 80, right associativity) : frml_scope.

#[global] Instance frml_eqdecision : EqDecision frml.
Proof. solve_decision. Qed.

(** Now we set up proofs.
    A Fitch proof is a list of lines, each (main) line indexed by an id
*)
Definition id := nat.


(** * Lines *)
(** There are several kinds of lines: Assumptions/Raises, Scope
control lines and deductions. Deductions are accompanied by
justifications. *)

(* Justifications *)
Inductive just :=
| Repeat (l : id)
| ConjI (l1 l2 : id)
| ConjE (flag : bool) (l : id)
| ImplI (l1 l2 : id)
| ImplE (l1 l2 : id)
.

(** `Assume` introduces a top-level assumption. `Raise` both opens a
   new subproof and introduces its assumption in one go. `ScopeClose
   l1 l2` closes the subproof with lines `l1-l2`, as long as it is the
   most recently open one. *)
Inductive line :=
| Assume (f : frml) (l : id)
| Raise (f : frml) (l : id)
| ScopeClose (l1 l2 : id)
| Deduce (f : frml) (j : just) (l : id)
.

(* Accessors and functions for `line` *)

Definition is_assume (l : line) : Prop :=
  match l with Assume _ _ => True | _ => False end.

Definition id_of_line (S : line) : option id :=
  match S with
  | Assume _ i => Some i
  | Raise _ i => Some i
  | ScopeClose _ _ => None
  | Deduce _ _ i => Some i
  end.

Definition frml_of_line (S : line) : option frml :=
  match S with
  | Assume f _ => Some f
  | Raise f _ => Some f
  | ScopeClose _ _ => None
  | Deduce f _ _ => Some f
  end.

(** Collect all the lines that are references in a given justification, line, or a (pre)deduction *)
Definition references_in_just (j : just) : list id :=
  match j with
  | Repeat l => [l]
  | ConjI l1 l2 => [l1;l2]
  | ConjE _ l => [l]
  | ImplI l1 l2 => [l1;l2]
  | ImplE l1 l2 => [l1;l2]
  end.

Definition references_in_line (s : line) : list id :=
  match s with
  | Deduce _ j _ => references_in_just j
  | ScopeClose l1 l2 => [l1; l2]
  | _ => []
end.


(** * Predeductions *)

(** A pre-deduction is just a list of lines. We later define a
property that demarcates (valid) deductions and pre-deductions *)
Definition prededuct := list line.

(* `line_at Σ i` returns the line with id `i` in `Σ`, or `None` if no
   line with that id exists *)
Fixpoint line_at (Σ : prededuct) (i : id) : option line :=
  match Σ with
  | [] => None
  | s :: Σ' =>
    match id_of_line s with
    | Some j => if decide (i = j)
                then Some s
                else line_at Σ' i
    | None => line_at Σ' i
    end
  end.

Definition frml_at (Σ : prededuct) (i : id) : option frml :=
  x ← line_at Σ i;
  frml_of_line x.


(* The formula of the very last line of Σ, if any: the conclusion of the
   deduction. *)
Definition conclusion_of (Σ : prededuct) : option frml :=
  match last Σ with
  | Some (Deduce f _ _) => Some f
  | _ => None
  end.

(* The formulas of the top-level assumptions of Σ, in the order they were
   assumed. Only meaningful when [is_deduct Σ] holds, since that is what
   guarantees every [Assume] in Σ really is at the top level. *)
Fixpoint assumptions_of (Σ : prededuct) : list frml :=
  match Σ with
  | [] => []
  | Assume f _ :: Σ' => f :: assumptions_of Σ'
  | _ :: Σ' => assumptions_of Σ'
  end.

Fixpoint lines_of_prededuct (Σ : prededuct) : list id :=
  match Σ with
  | [] => []
  | Assume _ l::Σ => l::(lines_of_prededuct Σ)
  | Raise _ l::Σ => l::(lines_of_prededuct Σ)
  | Deduce _ _ l::Σ => l::(lines_of_prededuct Σ)
  | _::Σ => lines_of_prededuct Σ
  end.


Fixpoint referenced_lines (Σ : prededuct) : list id :=
  match Σ with
  | s::Σ => references_in_line s ++ referenced_lines Σ
  | [] => []
  end.

(** `restr Σ i` is the prefix of `Σ` up to and including the first line
   whose id is `i`. If `i` does not appear in `Σ` the whole list
   is returned. *)
Fixpoint restr (Σ : prededuct) (i : id) : prededuct :=
  match Σ with
  | [] => []
  | s :: Σ' =>
    match id_of_line s with
    | Some j => if decide (i = j) then [s] else s :: restr Σ' i
    | None   => s :: restr Σ' i
    end
  end.

(** We have to put this lemma here, since it is useful for defining
functions on prededuction by length-recursion *)
Lemma restr_length Σ l :
  length (restr Σ l) <= length Σ.
Proof.
  induction Σ; simpl; [done |].
  case_match; simpl; try lia.
  case_decide; simpl; lia.
Qed.

Lemma restr_length_unsnoc Σ Σ' l s :
  unsnoc Σ = Some (Σ', s) →
  length (restr Σ' l) < length Σ.
Proof.
  intros. eapply Nat.le_lt_trans; [apply restr_length|].
  eapply unsnoc_length; eauto.
Qed.

(** * Scope and sub-proof scope

    The most important component in defining deductions is notion of scope -- which lines
    are available for a current given line.

The scope behaves similar to variable scope in programming languages.
Everything above, except for the subproofs, can be reference. But if
we are inside a subproof everything above in a given subproof is also
available to us.

We model the scope as a stack of frames: each frame record
the lines available directly within the current (sub)proof.

For example,

```
1 | A    Assume
  |--
2 | | B   Raise
  | |--
3 | | A   R: 1
  | |
4 | | B → A   →I:2-3
```

At line three the current frame contains [A] and [B] on lines 1 and 2.
At line four the current frame contains [A] and [B → A].

The scope is then all the lines avaialble in all the current frames.
The subproof scope is computed similarly.
*)


Record frame := mkFrame {
  frame_lines : list (frml * id);
  frame_subproofs : list ((frml * id) * (frml * id));
}.

(* [frame_step pre stk s] extends the frame stack [stk] with one more
   line [s], given that [pre] are the lines seen so far.  The prefix is
   needed so that [ScopeClose l1 l2] can look up the formulas at lines
   [l1] and [l2] via [frml_at].  If either lookup fails (ill-formed
   input) the stack is returned unchanged; well-formedness is checked
   separately. *)
Definition frame_step (pre : prededuct) (stk : list frame) (s : line) : list frame :=
  match s with
  | Raise A l => mkFrame [(A, l)] [] :: stk
  | Deduce A J l =>
    match stk with
    | fr :: rest => mkFrame (frame_lines fr ++ [(A, l)]) (frame_subproofs fr) :: rest
    | [] => []
    end
  | ScopeClose l1 l2 =>
    match stk with
    | _ :: fr2 :: rest =>
      match frml_at pre l1, frml_at pre l2 with
      | Some f1, Some f2 =>
        mkFrame (frame_lines fr2) (frame_subproofs fr2 ++ [((f1, l1), (f2, l2))]) :: rest
      | _, _ => stk
      end
    | _ => stk
    end
  | Assume f l' =>
    match stk with
    | fr :: rest => mkFrame (frame_lines fr ++ [(f, l')]) (frame_subproofs fr) :: rest
    | [] => []
    end
  end.

Fixpoint frame_stack_go (pre : prededuct) (stk : list frame) (Σ : prededuct)
    : list frame :=
  match Σ with
  | [] => stk
  | s :: Σ' => frame_stack_go (pre ++ [s]) (frame_step pre stk s) Σ'
  end.

Definition frame_stack (Σ : prededuct) : list frame :=
  frame_stack_go [] [mkFrame [] []] Σ.

(* The lines available to justify the line that would come right after Σ:
   those opened in the current subproof and in all of its ancestors,
   oldest first. *)
Definition scope (Σ : prededuct) : list (frml * id) :=
  concat (map frame_lines (frame_stack Σ)).

(* The subproofs available to justify (e.g. via ImplI) the line that would
   come right after Σ: those closed directly in the current subproof or
   one of its ancestors. *)
Definition sp_scope (Σ : prededuct) : list ((frml * id) * (frml * id)) :=
  concat (map frame_subproofs (frame_stack Σ)).


(** * Well-formed deductions *)

(** First, we consider when deductions and other lines are valid in a given proof. *)

(** `just_ok pre f j` holds when `j` correctly justifies deriving `f`, given
   that `pre` are the lines that come before it *)
Definition just_ok (pre : prededuct) (f : frml) (j : just) : Prop :=
  match j with
  | Repeat l0 => (f, l0) ∈ scope pre
  | ConjI l1 l2 =>
    ∃ f1 f2, (f1, l1) ∈ scope pre ∧
             (f2, l2) ∈ scope pre ∧
               f = (f1 ∧ f2)%F
  | ConjE flag l0 =>
    ∃ f1 f2, ((f1 ∧ f2)%F, l0) ∈ scope pre ∧
             f = (if flag then f1 else f2)
  | ImplI l1 l2 =>
    ∃ f1 f2, ((f1, l1), (f2, l2)) ∈ sp_scope pre ∧
               f = (f1 → f2)%F
  | ImplE l1 l2 =>
    ∃ f1 f2, ((f1 → f2)%F, l1) ∈ scope pre ∧
             (f1, l2) ∈ scope pre ∧
             f = f2
  end.



(** `line_ok pre l` holds when it is legal for `l` to come right after
   the prefix `pre` *)
Definition line_ok (pre : prededuct) (l : line) : Prop :=
  match l with
  | Deduce f j _ =>
    (** A single deduction line is correct if the justification is correct *)
    just_ok pre f j
  | Assume _ _ =>
      (** Assumes only come at the beginning: the whole prefix must be assumes *)
      Forall is_assume pre
  | Raise _ _ =>
      (** Raises are always okay *)
      True
  | ScopeClose l1 l2 =>
    (** When we close the sub-proof we want to make sure that it is well-formed;
        1. the closing statement should come directly after the line `l2`
        2. the stack of the prefix should contain the top frame,
           and the top frame should be of the form [(A,l1)...(B,l2)]
    *)
    match last pre with
    |  Some (Deduce _ _ l) => l = l2
    | _ => False end
         /\
    match frame_stack pre with
    | fr :: _ :: _ =>
      option_map snd (head (frame_lines fr)) = Some l1 /\
      option_map snd (last (frame_lines fr)) = Some l2
    | _ => False
    end
  end.

Inductive lines_ok : prededuct -> Prop :=
| lines_ok_nil : lines_ok []
| lines_ok_cons l pre :
  lines_ok pre ->
  line_ok pre l ->
  lines_ok (pre ++ [l])
.

(** A prededuction is a deduction when all of its lines are
    individually okay; it does not end with a subproof still open (the
    frame stack is f size one), its line ids are unique, and it ends
    on an actual conclusion (rather than a dangling `ScopeClose` or
    `Assume`). *)
Definition is_deduct (Σ : prededuct) : Prop :=
  lines_ok Σ /\
  length (frame_stack Σ) = 1 /\
  NoDup (lines_of_prededuct Σ) /\
  is_Some (conclusion_of Σ).

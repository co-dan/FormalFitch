(* Fitch proofs: reductions and equivalences *)
From stdpp Require Export base strings relations.
From fitch Require Import prelude.
From fitch.core Require Import deduct.

(** * Garbage removal reduction *)
Inductive garb_step : prededuct -> prededuct -> Prop :=
| garb_step_deduce Θ1 Θ3 A j l :
  Θ3 ≠ [] ->
  l ∉ referenced_lines Θ3 ->
  garb_step (Θ1 ++ [Deduce A j l] ++ Θ3)
            (Θ1 ++ Θ3)
| garb_step_subproof Θ1 Θ2 Θ3 A l1 l2 :
  Θ3 ≠ [] ->
  l1 ∉ referenced_lines Θ3 ->
  l2 ∉ referenced_lines Θ3 ->
  garb_step (Θ1 ++ [Raise A l1] ++ Θ2 ++ [ScopeClose l1 l2] ++ Θ3)
            (Θ1 ++ Θ3)
.

Definition garb : relation prededuct := rtc garb_step.

(** * "Independent statements swap" equivalence *)
Inductive indep_step : prededuct -> prededuct -> Prop :=
| indep_step_deduce_deduce Θ1 Θ3 A1 A2 j1 j2 l1 l2 :
  Θ3 ≠ [] ->
  l1 ∉ references_in_just j2 ->
  l2 ∉ references_in_just j1 ->
  (forall a b, ScopeClose a b ∈ Θ3 -> a ≠ l1 ∧ a ≠ l2 ∧ b ≠ l1 ∧ b ≠ l2) ->
  indep_step (Θ1 ++ [Deduce A1 j1 l1; Deduce A2 j2 l2] ++ Θ3)
             (Θ1 ++ [Deduce A2 j2 l2; Deduce A1 j1 l1] ++ Θ3)
| indep_step_deduce_subproof Θ1 Θ2 Θ3 A l1 l2 B j' n :
  Θ3 ≠ [] ->
  n ∉ referenced_lines Θ2 ->
  l1 ∉ references_in_just j' ->
  l2 ∉ references_in_just j' ->
  indep_step (Θ1 ++
             [Deduce B j' n; Raise A l1] ++ Θ2 ++ [ScopeClose l1 l2] ++
             Θ3)
             (Θ1 ++
             [Raise A l1] ++ Θ2 ++ [ScopeClose l1 l2; Deduce B j' n] ++
             Θ3)
| indep_step_subproof_deduce Θ1 Θ2 Θ3 A l1 l2 B j' n :
  Θ3 ≠ [] ->
  n ∉ referenced_lines Θ2 ->
  l1 ∉ references_in_just j' ->
  l2 ∉ references_in_just j' ->
  indep_step (Θ1 ++
             [Raise A l1] ++ Θ2 ++ [ScopeClose l1 l2; Deduce B j' n] ++
             Θ3)
             (Θ1 ++
             [Deduce B j' n; Raise A l1] ++ Θ2 ++ [ScopeClose l1 l2] ++
             Θ3)
| indep_step_subproof_subproof Θ1 Θ3 Σ1 Σ2 A1 A2 i1 i2 j1 j2 :
    Θ3 ≠ [] ->
    (forall k,
      k ∈ lines_of_prededuct ([Raise A1 i1] ++ Σ1 ++ [ScopeClose i1 j1]) ->
      k ∉ referenced_lines ([Raise A2 i2] ++ Σ2 ++ [ScopeClose i2 j2])) ->
    (forall k,
      k ∈ lines_of_prededuct ([Raise A2 i2] ++ Σ2 ++ [ScopeClose i2 j2]) ->
      k ∉ referenced_lines ([Raise A1 i1] ++ Σ1 ++ [ScopeClose i1 j1])) ->
    indep_step
      (Θ1 ++
         [Raise A1 i1] ++ Σ1 ++ [ScopeClose i1 j1] ++
         [Raise A2 i2] ++ Σ2 ++ [ScopeClose i2 j2] ++
         Θ3)
      (Θ1 ++
         [Raise A2 i2] ++ Σ2 ++ [ScopeClose i2 j2] ++
         [Raise A1 i1] ++ Σ1 ++ [ScopeClose i1 j1] ++
         Θ3).


Definition indep : relation prededuct := rtc indep_step.

(** Typeclass properties *)

#[global] Instance indep_step_sym : Symmetric indep_step.
Proof.
  intros Σ1 Σ2 H. inversion H; subst.
  - constructor; auto.
    intros a b Hab. destruct (H3 a b Hab) as (?&?&?&?). auto.
  - by constructor.
  - by constructor.
  - by constructor.
Qed.

#[global] Instance indep_sym : Symmetric indep.
Proof. apply _. Qed.


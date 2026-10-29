From stdpp Require Import list.
From fitch Require Import prelude core.

(** * Examples *)

(** Proves typing judgments for concrete programs. Context lookups pick
    the first binding with a matching name, which is the right one under
    [names_unique]. *)
Ltac typecheck :=
  repeat match goal with
  | |- _ ∈ _ :: _ => first [apply list_elem_of_here | apply list_elem_of_further]
  | |- _ => econstructor
  end.

Section examples.
  Let P := fAtomic "P".
  Let Q := fAtomic "Q".

  (** ⊢ P → P, via the subproof [1 | | P Raise; 2 | | P R:1] *)
  Example ex_id :=
    <{ { LET SUB [1, 2] : P → P = SUB (VAR 1) { RETURN : P = CPY(1) } IN
         RETURN : P → P = FUNC([1, 2]) } AS 3 }>.

  Example ex_id_ok : prog_ok ex_id (P → P)%F.
  Proof. split; [compute_done|]. unfold ex_id. by typecheck. Qed.

  (** P, Q ⊢ Q ∧ P *)
  Example ex_swap :=
    <{ VAR 1 : P ;
       VAR 2 : Q ;
       { LET 3 : P ∧ Q = (1, 2) IN
         LET 4 : Q = SND(3) IN
         RETURN : Q ∧ P = (4, 1) } AS 5 }>.

  Example ex_swap_ok : prog_ok ex_swap (Q ∧ P)%F.
  Proof. split; [compute_done|]. unfold ex_swap. by typecheck. Qed.

  (** P ⊢ (P → Q) → Q; the subroutine refers to the outer variable 1 *)
  Example ex_mp :=
    <{ VAR 1 : P ;
       { LET SUB [2, 3] : (P → Q) → Q = SUB (VAR 2) {
           RETURN : Q = APPLY(2, 1)
         } IN
         RETURN : (P → Q) → Q = FUNC([2, 3]) } AS 4 }>.

  Example ex_mp_ok : prog_ok ex_mp ((P → Q) → Q)%F.
  Proof. split; [compute_done|]. unfold ex_mp. by typecheck. Qed.

  (** Variables bound inside a subroutine are not visible after it. Only
      the subroutine itself is, under the name [[1, 2]]. *)
  Example ex_scope_bad :
    ¬ prog_typed []
      <{ { LET SUB [1, 2] : P → P = SUB (VAR 1) { RETURN : P = CPY(1) } IN
           RETURN : P = CPY(1) } AS 3 }> P.
  Proof.
    inversion 1 as [|???? Hb]; subst.
    inversion Hb as [|????????? Hk|]; subst.
    inversion Hk as [| |??? Ho]; subst.
    inversion Ho as [| | | | | ?? Hin]; subst.
    set_solver.
  Qed.
  (** ** Translations *)

  (** [ex_id] corresponds to the deduction

        1 | | P       Raise
        2 | | P       R:1
        3 | P → P     →I:1-2 *)
  Example ex_id_to_pd :
    ⦇ex_id⦈ᶜ = [Raise P 1; Deduce P (Repeat 1) 2; ScopeClose 1 2;
                Deduce (fImpl P P) (ImplI 1 2) 3].
  Proof. done. Qed.

  Example ex_id_roundtrip : ⟦⦇ex_id⦈ᶜ⟧ᶜ = ex_id.
  Proof. done. Qed.

  (** [ex_mp] corresponds to the deduction

        1 | P             Assume
          |----
        2 | | P → Q       Raise
        3 | | Q           →E:2,1
        4 | (P → Q) → Q   →I:2-3 *)
  Example ex_mp_to_pd :
    ⦇ex_mp⦈ᶜ = [Assume P 1; Raise (fImpl P Q) 2; Deduce Q (ImplE 2 1) 3;
                ScopeClose 2 3; Deduce (fImpl (fImpl P Q) Q) (ImplI 2 3) 4].
  Proof. done. Qed.

  Example ex_mp_roundtrip : ⟦⦇ex_mp⦈ᶜ⟧ᶜ = ex_mp.
  Proof. done. Qed.
End examples.

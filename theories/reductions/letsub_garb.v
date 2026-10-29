From stdpp Require Import list.
From fitch Require Import prelude core deduction_lemmas
  translations_lemmas typing_lemmas reduction_lemmas.
From fitch.reductions Require Import validity.
From fitch.reductions Require Export letsub_reductions.

(** * Garbage removal is preserved by the translation *)



(** A binder [l] of the redex that is not used in the continuation [k]
    is not referenced after the redex *)
Lemma redex_not_referenced Γ E b C y Γh v0 T0 k C' l :
  body_typed Γ (fill E b) C ->
  (∀ l, l ∈ ctx_ids Γh -> l ∈ ctx_ids Γ ∨ l ∈ ectx_pre_binders E) ->
  (v0, T0) :: Γh ⊢ k : C' ->
  v0 ∉ body_fv k ->
  l ∈ var_ids v0 ->
  l ∉ ctx_ids Γ -> l ∉ ectx_pre_binders E -> l ∉ ectx_post_binders E ->
  l ∉ body_binders k ->
  l ∉ referenced_lines (⦇k⦈ (ectx_ret y E) ++ ectx_post y E).
Proof.
  intros Hb Hids Hk Hfv Hl ????. rewrite referenced_lines_app elem_of_app.
  intros [Hr|Hr].
  - destruct (deduct_of_body_refs_ctx _ _ _ _ _ Hk Hr)
      as [(v & T & ? & [[= -> ->]|?]%elem_of_cons & ?)|]; [done| |done].
    destruct (Hids l); [|done..]. apply elem_of_ctx_ids. eauto.
  - destruct (ectx_post_refs _ _ _ _ _ _ Hb Hr) as [|[|]]; done.
Qed.


Lemma body_garb_step_to_deduct Γ b b' C y :
  Γ ⊢ b : C ->
  NoDup (ctx_ids Γ ++ body_binders b) ->
  body_garb_step b b' ->
  garb_step (⦇b⦈ y) (⦇b'⦈ y).
Proof.
  intros Hb Hnd Hstep. revert Hb Hnd.
  destruct Hstep as [E r r' Hr]; intros Hb Hnd. rewrite !deduct_of_body_fill.
  destruct (fill_typed _ _ _ _ Hb) as (Γh & C' & Hrt & Hids & _).
  destruct (fill_redex_NoDup _ _ _ _ Hnd Hids) as [Hnd' _].
  (* the binders of the redex occur nowhere else *)
  assert (∀ l, l ∈ body_binders r ->
            l ∉ ctx_ids Γ ∧ l ∉ ectx_pre_binders E ∧ l ∉ ectx_post_binders E)
    as Hout.
  { rewrite body_binders_fill app_assoc in Hnd. intros l Hl.
    destruct (NoDup_mid _ _ _ l Hnd Hl). set_solver. }
  assert (∀ k z, ⦇k⦈ z ++ ectx_post y E ≠ []) as Hne.
  { intros k z [? _]%app_nil. by eapply deduct_of_body_nonempty. }
  destruct Hr as [x A o k Hfv|x y' A B s k Hfv]; simpl in Hnd', Hout.
  - (* LET *)
    apply let_typed_inv in Hrt as [_ Hk].
    destruct (Hout x) as (? & ? & ?); [set_solver|].
    apply (garb_step_deduce (ectx_pre E)); [apply Hne|].
    eapply redex_not_referenced; [done|done|done|done|by left|done|done|done|nodup_tac Hnd'].
  - (* LET SUB *)
    apply letsub_typed_inv in Hrt as (_ & _ & Hk).
    destruct (Hout x) as (? & ? & ?); [set_solver|].
    destruct (Hout y') as (? & ? & ?); [set_solver|].
    rewrite deduct_of_letsub -!app_assoc.
    apply (garb_step_subproof (ectx_pre E)); [apply Hne| |];
      (eapply redex_not_referenced; [done|done|done|done|set_solver|done|done|done|nodup_tac Hnd']).
Qed.

Theorem let_garb_step_deduct p p' C :
  prog_ok p C -> let_garb_step p p' -> garb_step ⦇p⦈ᶜ ⦇p'⦈ᶜ.
Proof. exact (prog_step_to_deduct _ _ garb_step_cons body_garb_step_to_deduct p p' C). Qed.

(** * Subject reduction *)

Lemma garb_redex_wf : redex_wf garb_redex.
Proof. intros r r' []; simpl; naive_solver. Qed.

Theorem let_garb_step_ok p p' C :
  prog_ok p C -> let_garb_step p p' -> prog_ok p' C.
Proof.
  exact (prog_step_ok _ _ garb_redex_wf garb_step_is_deduct garb_step_conclusion
           garb_step_cons body_garb_step_to_deduct p p' C).
Qed.

(** * Multiple steps *)

Theorem let_garb_deduct p p' C :
  prog_ok p C -> let_garb p p' -> garb ⦇p⦈ᶜ ⦇p'⦈ᶜ ∧ prog_ok p' C.
Proof.
  exact (prog_steps_to_deduct _ _ garb_redex_wf garb_step_is_deduct garb_step_conclusion
           garb_step_cons body_garb_step_to_deduct p p' C).
Qed.

(** * Garbage steps of translations come from garbage steps of programs *)

(** Inversion of the two kinds of garbage removal on the translation
    of a body [b0] followed by [post] *)
Lemma garb_redex_inv_deduce Γh b0 C z post Θ3 A j l :
  Γh ⊢ b0 : C -> (post = [] ∨ z ∈ referenced_lines post) ->
  ⦇b0⦈ z ++ post = Deduce A j l :: Θ3 ->
  Θ3 ≠ [] -> l ∉ referenced_lines Θ3 ->
  ∃ b0', garb_redex b0 b0' ∧ ⦇b0'⦈ z ++ post = Θ3.
Proof.
  intros Hb0 Hpost Heq Hne Hnref.
  destruct b0 as [x B o k|x y A' B [x' s] k|B o]; simpl in Heq; [|discriminate|].
  - apply let_typed_inv in Hb0 as [_ Hk].
    injection Heq as <- <- <- <-.
    exists k. split; [constructor|done].
    intros Hv. apply Hnref. rewrite referenced_lines_app elem_of_app. left.
    by apply (body_fv_refs _ _ _ Hk z (LVar x)).
  - injection Heq as <- <- <- ->. by destruct Hpost.
Qed.

Lemma garb_redex_inv_sub Γh b0 C z post Θ2 Θ3 A l1 l2 :
  Γh ⊢ b0 : C -> NoDup (body_binders b0) ->
  (∀ a c, ScopeClose a c ∈ post -> a ∉ body_binders b0) ->
  ⦇b0⦈ z ++ post = Raise A l1 :: Θ2 ++ ScopeClose l1 l2 :: Θ3 ->
  l1 ∉ referenced_lines Θ3 ->
  ∃ b0', garb_redex b0 b0' ∧ ⦇b0'⦈ z ++ post = Θ3.
Proof.
  intros Hb0 Hnd Hsc Heq Hnref.
  destruct b0 as [x B o k|x y A' B [x' s] k|B o]; simpl in Heq;
    [discriminate| |discriminate].
  apply letsub_typed_inv in Hb0 as (-> & Hs & Hk).
  rewrite -!app_assoc /= in Heq. injection Heq as <- <- Heq.
  simpl in Hnd, Hsc.
  destruct (split_scope_close _ _ _ _ _ _ _ _ _ Hs Heq)
    as (-> & -> & ->); [nodup_tac Hnd|apply (deduct_of_body_scs_not _ _ _ _ _ _ Hk); [nodup_tac Hnd|intros a c Ha ->; apply (Hsc _ _ Ha); set_solver]|].
  exists k. split; [constructor|done].
  intros Hv. apply Hnref. rewrite referenced_lines_app elem_of_app. left.
  by apply (body_fv_refs _ _ _ Hk z (SVar x y)).
Qed.

Lemma body_garb_inv Γ b C y Σ' :
  Γ ⊢ b : C -> NoDup (body_binders b) -> garb_step (⦇b⦈ y) Σ' ->
  ∃ b', body_garb_step b b' ∧ ⦇b'⦈ y = Σ'.
Proof.
  intros Hb Hnd Hstep. remember (⦇b⦈ y) as Σ eqn:HΣ.
  destruct Hstep as [Θ1 Θ3 A j l Hne Hnref|Θ1 Θ2 Θ3 A l1 l2 Hne Hnref1 Hnref2].
  - eapply (redex_lift garb_redex _ _ _ y Θ1 (Deduce A j l) Θ3);
      [done|done|by symmetry|by eexists|].
    red; intros. by eapply garb_redex_inv_deduce.
  - eapply (redex_lift garb_redex _ _ _ y Θ1 (Raise A l1)
              (Θ2 ++ ScopeClose l1 l2 :: Θ3));
      [done|done|by symmetry|by eexists|].
    red; intros. by eapply garb_redex_inv_sub.
Qed.


Theorem deduct_garb_step_let Σ Σ' :
  is_deduct Σ -> garb_step Σ Σ' -> let_garb_step ⟦Σ⟧ᶜ ⟦Σ'⟧ᶜ.
Proof.
  exact (deduct_to_prog_step _ _ garb_redex_wf garb_step_is_deduct garb_step_conclusion
           garb_step_cons body_garb_step_to_deduct garb_step_assume_inv body_garb_inv Σ Σ').
Qed.

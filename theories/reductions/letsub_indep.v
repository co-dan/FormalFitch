From stdpp Require Import list.
From fitch Require Import prelude core deduction_lemmas
  translations_lemmas typing_lemmas reduction_lemmas.
From fitch.reductions Require Import validity.
From fitch.reductions Require Export letsub_reductions.

(** * Swaps are preserved by the translation *)




Lemma indep_redex_to_deduct Γh r r' C z :
  Γh ⊢ r : C ->
  NoDup (body_binders r) ->
  (∀ l, l ∈ body_binders r -> l ∉ ctx_ids Γh) ->
  indep_redex r r' ->
  indep_step (⦇r⦈ z) (⦇r'⦈ z).
Proof.
  intros Hr Hnd Hfresh Hstep.
  destruct Hstep as [x1 x2 A1 A2 o1 o2 k Hx1 Hx2|n B o x y A C' s k Hn Hxy
                    |n B o x y A C' s k Hn Hxy
                    |x1 y1 A1 B1 s1 x2 y2 A2 B2 s2 k Hxy1 Hxy2];
    simpl in Hnd, Hfresh; decompose_NoDup;
    rewrite ?deduct_of_let ?deduct_of_letsub ?deduct_of_let.
  - (* LET / LET *)
    apply let_typed_inv in Hr as [Ho1 (Ho2 & Hk)%let_typed_inv].
    apply (indep_step_deduce_deduce [] (⦇k⦈ z));
      [apply not_closing_deduct_of_body|eapply op_refs_not_in; [done|]..].
    + intros v T Hv [[= -> ->]|HvT]%elem_of_cons Hl; [done|].
      apply (Hfresh x1); [set_solver|]. by eapply ctx_ids_elem.
    + intros v T Hv HvT Hl. apply (Hfresh x2); [set_solver|].
      by eapply ctx_ids_elem.
  - (* LET / LET SUB *)
    apply let_typed_inv in Hr as [Ho (_ & Hs & Hk)%letsub_typed_inv].
    apply (indep_step_deduce_subproof [] (⦇s⦈ y) (⦇k⦈ z));
      [apply not_closing_deduct_of_body| |eapply op_refs_not_in; [done|]..].
    + eapply body_refs_not_in; [done| |set_solver].
      intros v T Hv [[= -> ->]|[[= -> ->]|HvT]%elem_of_cons]%elem_of_cons Hl;
        [set_solver|done|].
      apply (Hfresh n); [set_solver|]. by eapply ctx_ids_elem.
    + intros v T Hv HvT Hl. apply (Hfresh x); [set_solver|].
      by eapply ctx_ids_elem.
    + intros v T Hv HvT Hl. apply (Hfresh y); [set_solver|].
      by eapply ctx_ids_elem.
  - (* LET SUB / LET *)
    apply letsub_typed_inv in Hr as (_ & Hs & (Ho & Hk)%let_typed_inv).
    apply (indep_step_subproof_deduce [] (⦇s⦈ y) (⦇k⦈ z));
      [apply not_closing_deduct_of_body| |eapply op_refs_not_in; [done|]..].
    + eapply body_refs_not_in; [done| |set_solver].
      intros v T Hv [[= -> ->]|HvT]%elem_of_cons Hl; [set_solver|].
      apply (Hfresh n); [set_solver|]. by eapply ctx_ids_elem.
    + intros v T Hv [[= -> ->]|HvT]%elem_of_cons Hl; [done|].
      apply (Hfresh x); [set_solver|]. by eapply ctx_ids_elem.
    + intros v T Hv [[= -> ->]|HvT]%elem_of_cons Hl; [done|].
      apply (Hfresh y); [set_solver|]. by eapply ctx_ids_elem.
  - (* LET SUB / LET SUB *)
    apply letsub_typed_inv in Hr as (_ & Hs1 & (_ & Hs2 & Hk)%letsub_typed_inv).
    apply (indep_step_subproof_subproof [] (⦇k⦈ z) (⦇s1⦈ y1) (⦇s2⦈ y2));
      [apply deduct_of_body_nonempty| |];
      intros l; rewrite !lines_of_prededuct_app lines_of_deduct_of_body
        !referenced_lines_app /=; intros Hl.
    + assert (l ∉ referenced_lines (⦇s2⦈ y2)); [|set_solver].
      eapply body_refs_not_in; [done| |set_solver].
      intros v T Hv [[= -> ->]|[[= -> ->]|HvT]%elem_of_cons]%elem_of_cons Hlv;
        [set_solver|done|].
      apply (Hfresh l); [set_solver|]. by eapply ctx_ids_elem.
    + assert (l ∉ referenced_lines (⦇s1⦈ y1)); [|set_solver].
      eapply body_refs_not_in; [done| |set_solver].
      intros v T Hv [[= -> ->]|HvT]%elem_of_cons Hlv; [set_solver|].
      apply (Hfresh l); [set_solver|]. by eapply ctx_ids_elem.
Qed.

Lemma body_indep_step_to_deduct Γ b b' C y :
  Γ ⊢ b : C ->
  NoDup (ctx_ids Γ ++ body_binders b) ->
  body_indep_step b b' ->
  indep_step (⦇b⦈ y) (⦇b'⦈ y).
Proof.
  intros Hb Hnd Hstep. revert Hb Hnd. destruct Hstep as [E r r' Hr]; intros Hb Hnd. rewrite !deduct_of_body_fill.
  destruct (fill_typed _ _ _ _ Hb) as (Γh & C' & Hrt & Hids & _).
  destruct (fill_redex_NoDup _ _ _ _ Hnd Hids) as [Hnd' Hfresh].
  apply indep_step_app_l, indep_step_app_r. by eapply indep_redex_to_deduct.
Qed.

Theorem let_indep_step_deduct p p' C :
  prog_ok p C -> let_indep_step p p' -> indep_step ⦇p⦈ᶜ ⦇p'⦈ᶜ.
Proof. exact (prog_step_to_deduct _ _ indep_step_cons body_indep_step_to_deduct p p' C). Qed.

(** * Subject reduction *)

Lemma indep_redex_wf : redex_wf indep_redex.
Proof. intros r r' []; simpl; naive_solver. Qed.

Theorem let_indep_step_ok p p' C :
  prog_ok p C -> let_indep_step p p' -> prog_ok p' C.
Proof.
  exact (prog_step_ok _ _ indep_redex_wf indep_step_is_deduct indep_step_conclusion
           indep_step_cons body_indep_step_to_deduct p p' C).
Qed.

(** * Multiple steps *)

Theorem let_indep_deduct p p' C :
  prog_ok p C -> let_indep p p' -> indep ⦇p⦈ᶜ ⦇p'⦈ᶜ ∧ prog_ok p' C.
Proof.
  exact (prog_steps_to_deduct _ _ indep_redex_wf indep_step_is_deduct indep_step_conclusion
           indep_step_cons body_indep_step_to_deduct p p' C).
Qed.

(** * Swaps of translations come from swaps of programs *)

(** Inversion of the four kinds of swaps on the translation of a body
    [b0] followed by [post] *)
Lemma indep_redex_inv_dd Γh b0 C z post Θ3 A1 A2 j1 j2 l1 l2 :
  Γh ⊢ b0 : C -> ¬ not_closing post ->
  ⦇b0⦈ z ++ post = [Deduce A1 j1 l1; Deduce A2 j2 l2] ++ Θ3 ->
  not_closing Θ3 ->
  l1 ∉ references_in_just j2 ->
  l2 ∉ references_in_just j1 ->
  ∃ b0', indep_redex b0 b0' ∧
         ⦇b0'⦈ z ++ post = [Deduce A2 j2 l2; Deduce A1 j1 l1] ++ Θ3.
Proof.
  intros Hb0 Hpost Heq Hnc Hl1 Hl2.
  destruct b0 as [x B o k|x y A B [x' s] k|B o]; simpl in Heq; [|discriminate|].
  - destruct k as [x' B' o' k'|x' y A' B' [x'' s] k'|B' o'];
      simpl in Heq; [|discriminate|].
    + injection Heq as <- <- <- <- <- <- <-.
      eexists. split; [constructor|done].
      * by intros Hv%(op_vars_refs_rev _ (LVar x)).
      * by intros Hv%(op_vars_refs_rev _ (LVar x')).
    + injection Heq as <- <- <- <- <- <- <-. done.
  - injection Heq as <- <- <- ->. by destruct Hpost; eexists.
Qed.

Lemma indep_redex_inv_ds Γh b0 C z post Θ2 Θ3 A B j' l1 l2 n :
  Γh ⊢ b0 : C -> NoDup (body_binders b0) -> ¬ not_closing post ->
  (∀ a c, ScopeClose a c ∈ post -> a ∉ body_binders b0) ->
  ⦇b0⦈ z ++ post =
    [Deduce B j' n; Raise A l1] ++ Θ2 ++ [ScopeClose l1 l2] ++ Θ3 ->
  n ∉ referenced_lines Θ2 ->
  l1 ∉ references_in_just j' ->
  l2 ∉ references_in_just j' ->
  ∃ b0', indep_redex b0 b0' ∧
         ⦇b0'⦈ z ++ post =
           [Raise A l1] ++ Θ2 ++ [ScopeClose l1 l2; Deduce B j' n] ++ Θ3.
Proof.
  intros Hb0 Hnd Hpost Hsc Heq Hn Hl1 Hl2.
  destruct b0 as [x B0 o k|x y A0 B0 [x' s] k|B0 o]; simpl in Heq;
    [|discriminate|].
  - apply let_typed_inv in Hb0 as [Ho Hk].
    destruct k as [x1 B1 o1 k1|x1 y1 A1 B1 [x1' s1] k1|B1 o1];
      simpl in Heq; [discriminate| |discriminate].
    apply letsub_typed_inv in Hk as (-> & Hs1 & Hk1).
    rewrite -!app_assoc /= in Heq.
    injection Heq as <- <- <- <- <- Heq.
    simpl in Hnd, Hsc.
    destruct (split_scope_close _ _ _ _ _ _ _ _ _ Hs1 Heq)
      as (-> & -> & ->); [nodup_tac Hnd|apply (deduct_of_body_scs_not _ _ _ _ _ _ Hk1); [nodup_tac Hnd|intros a c Ha ->; apply (Hsc _ _ Ha); set_solver]|].
    eexists. split; [constructor|by rewrite /= -!app_assoc].
    + intros Hv. apply Hn. by apply (body_fv_refs _ _ _ Hs1 y1 (LVar x)).
    + by intros Hv%(op_vars_refs_rev _ (SVar x1 y1)).
  - injection Heq as <- <- <- Heq. destruct Hpost. rewrite Heq. by eexists.
Qed.

Lemma indep_redex_inv_sd Γh b0 C z post Θ2 Θ3 A B j' l1 l2 n :
  Γh ⊢ b0 : C -> NoDup (body_binders b0) -> ¬ not_closing post ->
  (∀ a c, ScopeClose a c ∈ post -> a ∉ body_binders b0) ->
  ⦇b0⦈ z ++ post =
    [Raise A l1] ++ Θ2 ++ [ScopeClose l1 l2; Deduce B j' n] ++ Θ3 ->
  not_closing Θ3 ->
  n ∉ referenced_lines Θ2 ->
  l1 ∉ references_in_just j' ->
  l2 ∉ references_in_just j' ->
  ∃ b0', indep_redex b0 b0' ∧
         ⦇b0'⦈ z ++ post =
           [Deduce B j' n; Raise A l1] ++ Θ2 ++ [ScopeClose l1 l2] ++ Θ3.
Proof.
  intros Hb0 Hnd Hpost Hsc Heq Hnc Hn Hl1 Hl2.
  destruct b0 as [x B0 o k|x y A0 B0 [x' s] k|B0 o]; simpl in Heq;
    [discriminate| |discriminate].
  apply letsub_typed_inv in Hb0 as (-> & Hs & Hk).
  rewrite -!app_assoc /= in Heq.
  injection Heq as <- <- Heq.
  simpl in Hnd, Hsc.
  destruct (split_scope_close _ _ _ _ _ _ _ _ _ Hs Heq)
    as (-> & -> & Heq'); [nodup_tac Hnd|apply (deduct_of_body_scs_not _ _ _ _ _ _ Hk); [nodup_tac Hnd|intros a c Ha ->; apply (Hsc _ _ Ha); set_solver]|].
  destruct k as [x1 B1 o1 k1|x1 y1 A1 B1 [x1' s1] k1|B1 o1];
    simpl in Heq'; [|discriminate|].
  - injection Heq' as -> -> -> ->.
    eexists. split; [constructor|by rewrite /= -!app_assoc].
    + intros Hv. apply Hn. by apply (body_fv_refs _ _ _ Hs y (LVar x1)).
    + by intros Hv%(op_vars_refs_rev _ (SVar x y)).
  - injection Heq' as -> -> -> ->. done.
Qed.

Lemma indep_redex_inv_ss Γh b0 C z post Θ3 Σ1 Σ2 A1 A2 i1 i2 j1 j2 :
  Γh ⊢ b0 : C -> NoDup (body_binders b0) -> ¬ not_closing post ->
  (∀ a c, ScopeClose a c ∈ post -> a ∉ body_binders b0) ->
  ⦇b0⦈ z ++ post =
    [Raise A1 i1] ++ Σ1 ++ [ScopeClose i1 j1] ++
    [Raise A2 i2] ++ Σ2 ++ [ScopeClose i2 j2] ++ Θ3 ->
  (∀ k,
    k ∈ lines_of_prededuct ([Raise A1 i1] ++ Σ1 ++ [ScopeClose i1 j1]) →
    k ∉ referenced_lines ([Raise A2 i2] ++ Σ2 ++ [ScopeClose i2 j2])) →
  (∀ k,
    k ∈ lines_of_prededuct ([Raise A2 i2] ++ Σ2 ++ [ScopeClose i2 j2]) →
    k ∉ referenced_lines ([Raise A1 i1] ++ Σ1 ++ [ScopeClose i1 j1])) →
  ∃ b0', indep_redex b0 b0' ∧
         ⦇b0'⦈ z ++ post =
           [Raise A2 i2] ++ Σ2 ++ [ScopeClose i2 j2] ++
           [Raise A1 i1] ++ Σ1 ++ [ScopeClose i1 j1] ++ Θ3.
Proof.
  intros Hb0 Hnd Hpost Hsc Heq.
  destruct b0 as [x B0 o k|x1 y1 A1' B1 [x1' s1] k|B0 o]; simpl in Heq;
    [discriminate| |discriminate].
  apply letsub_typed_inv in Hb0 as (-> & Hs1 & Hk).
  rewrite -!app_assoc /= in Heq. injection Heq as <- <- Heq.
  simpl in Hnd, Hsc.
  destruct (split_scope_close _ _ _ _ _ _ _ _ _ Hs1 Heq)
    as (-> & -> & Heq'); [nodup_tac Hnd|apply (deduct_of_body_scs_not _ _ _ _ _ _ Hk); [nodup_tac Hnd|intros a c Ha ->; apply (Hsc _ _ Ha); set_solver]|].
  destruct k as [x B0 o k|x2 y2 A2' B2 [x2' s2] k|B0 o];
    simpl in Heq'; [discriminate| |discriminate].
  apply letsub_typed_inv in Hk as (-> & Hs2 & Hk). simpl in Hnd, Hsc.
  rewrite -!app_assoc /= in Heq'. injection Heq' as -> -> Heq'.
  symmetry in Heq'.
  destruct (split_scope_close _ _ _ _ _ _ _ _ _ Hs2 Heq')
    as (-> & -> & ->); [nodup_tac Hnd|apply (deduct_of_body_scs_not _ _ _ _ _ _ Hk); [nodup_tac Hnd|intros a c Ha ->; apply (Hsc _ _ Ha); set_solver]|].
  intros H12 H21. eexists.
  split; [constructor|by rewrite /= -!app_assoc /= -!app_assoc].
  - intros Hv. apply (H12 x1); [simpl; apply elem_of_cons; by left|].
    rewrite /= referenced_lines_app elem_of_app. left.
    by apply (body_fv_refs _ _ _ Hs2 y2 (SVar x1 y1)).
  - intros Hv. apply (H21 x2); [simpl; apply elem_of_cons; by left|].
    rewrite /= referenced_lines_app elem_of_app. left.
    by apply (body_fv_refs _ _ _ Hs1 y1 (SVar x2 y2)).
Qed.

Lemma body_indep_inv Γ b C y Σ' :
  Γ ⊢ b : C -> NoDup (body_binders b) -> indep_step (⦇b⦈ y) Σ' ->
  ∃ b', body_indep_step b b' ∧ ⦇b'⦈ y = Σ'.
Proof.
  intros Hb Hnd Hstep. remember (⦇b⦈ y) as Σ eqn:HΣ.
  destruct Hstep as [Θ1 Θ3 A1 A2 j1 j2 l1 l2 Hnc Hl1 Hl2
                    |Θ1 Θ2 Θ3 A l1 l2 B j' n Hnc Hn Hl1 Hl2
                    |Θ1 Θ2 Θ3 A l1 l2 B j' n Hnc Hn Hl1 Hl2
                    |Θ1 Θ3 Σ1 Σ2 A1 A2 i1 i2 j1 j2 Hne H12 H21].
  - eapply (redex_lift indep_redex _ _ _ y Θ1 (Deduce A1 j1 l1) (Deduce A2 j2 l2 :: Θ3));
      [done|done|by symmetry|by eexists|].
    red; intros. by eapply indep_redex_inv_dd.
  - eapply (redex_lift indep_redex _ _ _ y Θ1 (Deduce B j' n)
              (Raise A l1 :: Θ2 ++ ScopeClose l1 l2 :: Θ3));
      [done|done|by symmetry|by eexists|].
    red; intros. by eapply indep_redex_inv_ds.
  - eapply (redex_lift indep_redex _ _ _ y Θ1 (Raise A l1)
              (Θ2 ++ ScopeClose l1 l2 :: Deduce B j' n :: Θ3));
      [done|done|by symmetry|by eexists|].
    red; intros. by eapply indep_redex_inv_sd.
  - eapply (redex_lift indep_redex _ _ _ y Θ1 (Raise A1 i1)
              (Σ1 ++ ScopeClose i1 j1 :: Raise A2 i2 :: Σ2 ++
                 ScopeClose i2 j2 :: Θ3));
      [done|done|by symmetry|by eexists|].
    red; intros. by eapply indep_redex_inv_ss.
Qed.


Theorem deduct_indep_step_let Σ Σ' :
  is_deduct Σ -> indep_step Σ Σ' -> let_indep_step ⟦Σ⟧ᶜ ⟦Σ'⟧ᶜ.
Proof.
  exact (deduct_to_prog_step _ _ indep_redex_wf indep_step_is_deduct indep_step_conclusion
           indep_step_cons body_indep_step_to_deduct indep_step_assume_inv body_indep_inv Σ Σ').
Qed.

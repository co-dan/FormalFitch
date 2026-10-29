From stdpp Require Import list.
From fitch Require Import prelude core.

(** * Variables and contexts *)

Lemma elem_of_ctx_ids Γ l :
  l ∈ ctx_ids Γ ↔ ∃ v T, (v, T) ∈ Γ ∧ l ∈ var_ids v.
Proof.
  rewrite /ctx_ids list_elem_of_bind. split.
  - intros ([v T] & ? & ?). eauto.
  - intros (v & T & ? & ?). by exists (v, T).
Qed.

Lemma ctx_ids_cons v T Γ : ctx_ids ((v, T) :: Γ) = var_ids v ++ ctx_ids Γ.
Proof. done. Qed.

Lemma ctx_ids_elem Γ v T l : (v, T) ∈ Γ -> l ∈ var_ids v -> l ∈ ctx_ids Γ.
Proof. intros. apply elem_of_ctx_ids. eauto. Qed.

(** * Typing *)

Lemma let_typed_inv Γ x A o k C :
  body_typed Γ (BLet x A o k) C ->
  op_typed Γ o A ∧ body_typed ((LVar x, TFrml A) :: Γ) k C.
Proof. by inversion 1. Qed.

Lemma letsub_typed_inv Γ x y A B x' s k C :
  body_typed Γ (BLetSub x y A B (mkSubr x' s) k) C ->
  x' = x ∧ body_typed ((LVar x, TFrml A) :: Γ) s B ∧
  body_typed ((SVar x y, TSub A B) :: Γ) k C.
Proof. by inversion 1. Qed.

Lemma op_vars_typed Γ o A v :
  Γ ⊢ₒ o : A -> v ∈ op_vars o -> ∃ T, (v, T) ∈ Γ.
Proof. destruct 1; set_solver. Qed.

Lemma op_typed_weaken Γ Γ' o A :
  Γ ⊢ₒ o : A ->
  (∀ v T, v ∈ op_vars o -> (v, T) ∈ Γ -> (v, T) ∈ Γ') ->
  Γ' ⊢ₒ o : A.
Proof. destruct 1; intros HΓ; simpl in HΓ; econstructor; eauto with set_solver. Qed.

Lemma body_typed_weaken Γ Γ' b C :
  Γ ⊢ b : C -> (∀ vT, vT ∈ Γ -> vT ∈ Γ') -> Γ' ⊢ b : C.
Proof.
  intros Hb. revert Γ'.
  induction Hb as [Γ x A o k C Ho _ IH|Γ x y A B b k C _ IHb _ IHk|Γ A o Ho];
    intros Γ' HΓ; constructor; try (eapply op_typed_weaken; [done|]);
    first [by eauto | apply IH | apply IHb | apply IHk]; set_solver.
Qed.

(** Removing an unused variable from the context *)
Lemma body_typed_strengthen Γ1 Γ2 v0 T0 b C :
  Γ1 ++ (v0, T0) :: Γ2 ⊢ b : C ->
  v0 ∉ body_fv b ->
  (∀ l, l ∈ var_ids v0 -> l ∉ body_binders b) ->
  Γ1 ++ Γ2 ⊢ b : C.
Proof.
  remember (Γ1 ++ (v0, T0) :: Γ2) as Γ eqn:HΓ. intros Hb. revert Γ1 HΓ.
  induction Hb as [Γ x A o k C Ho _ IH|Γ x y A B b k C _ IHb _ IHk|Γ A o Ho];
    intros Γ1 -> Hfv Hbind; simpl in *.
  - constructor.
    + eapply op_typed_weaken; [done|]. set_solver.
    + apply (IH ((LVar x, TFrml A) :: Γ1)); [done| |set_solver].
      intros Hv. destruct v0; set_solver.
  - constructor.
    + apply (IHb ((LVar x, TFrml A) :: Γ1)); [done| |set_solver].
      intros Hv. destruct v0; set_solver.
    + apply (IHk ((SVar x y, TSub A B) :: Γ1)); [done| |set_solver].
      intros Hv. destruct v0; set_solver.
  - constructor. eapply op_typed_weaken; [done|]. set_solver.
Qed.

(** The free variables of a well-typed body are in its context *)
Lemma body_fv_typed Γ b C v :
  Γ ⊢ b : C -> v ∈ body_fv b -> ∃ T, (v, T) ∈ Γ.
Proof.
  intros Hb. revert v.
  induction Hb as [Γ x A o k C Ho _ IH|Γ x y A B b k C _ IHb _ IHk|Γ A o Ho];
    intros v; simpl; rewrite ?elem_of_app ?list_elem_of_filter.
  - intros [Hv|[Hv Hfv]]; [by eapply op_vars_typed|].
    destruct (IH _ Hfv) as [T HT]. set_solver.
  - intros [[Hv Hfv]|[Hv Hfv]].
    + destruct (IHb _ Hfv) as [T HT]. set_solver.
    + destruct (IHk _ Hfv) as [T HT]. set_solver.
  - by eapply op_vars_typed.
Qed.

(** Typing of a filled context item *)
Lemma fill_item_typed Γ Ei b C :
  body_typed Γ (fill_item Ei b) C ->
  ∃ Γ' C', (Γ' ⊢ b : C') ∧
    (∀ l, l ∈ ctx_ids Γ' -> l ∈ ctx_ids Γ ∨ l ∈ item_pre_binders Ei) ∧
    (∀ b', Γ' ⊢ b' : C' -> body_typed Γ (fill_item Ei b') C).
Proof.
  destruct Ei; simpl; inversion 1; subst;
    (eexists _, _; split_and!; [done| |by econstructor; eauto]);
    intros l; rewrite ctx_ids_cons /=; set_solver.
Qed.

Lemma fill_typed Γ E b C :
  body_typed Γ (fill E b) C ->
  ∃ Γh C', (Γh ⊢ b : C') ∧
    (∀ l, l ∈ ctx_ids Γh -> l ∈ ctx_ids Γ ∨ l ∈ ectx_pre_binders E) ∧
    (∀ b', Γh ⊢ b' : C' -> body_typed Γ (fill E b') C).
Proof.
  revert Γ C. induction E as [|Ei E IH]; intros Γ C Hb.
  - exists Γ, C. naive_solver.
  - destruct (fill_item_typed _ _ _ _ Hb) as (Γ' & C' & Hb' & Hids' & Hfill').
    destruct (IH _ _ Hb') as (Γh & C'' & ? & Hids & Hfill).
    exists Γh, C''. split_and!; [done| |naive_solver].
    rewrite ectx_pre_binders_cons.
    intros l [|]%Hids; [destruct (Hids' l)|]; set_solver.
Qed.

(** The binders of a redex are fresh for its typing context *)
Lemma fill_redex_NoDup Γ E b Γh :
  NoDup (ctx_ids Γ ++ body_binders (fill E b)) ->
  (∀ l, l ∈ ctx_ids Γh -> l ∈ ctx_ids Γ ∨ l ∈ ectx_pre_binders E) ->
  NoDup (body_binders b) ∧ (∀ l, l ∈ body_binders b -> l ∉ ctx_ids Γh).
Proof.
  rewrite body_binders_fill app_assoc. intros Hnd Hids. split.
  - by apply NoDup_app in Hnd as (_ & _ & (? & _)%NoDup_app).
  - intros l Hl Hl'. destruct (NoDup_mid _ _ _ l Hnd Hl) as [H1 _].
    destruct (Hids l Hl'); set_solver.
Qed.

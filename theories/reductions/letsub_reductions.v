From stdpp Require Import list.
From fitch Require Import prelude core deduction_lemmas
  translations_lemmas typing_lemmas.

(** * Reductions closed under contexts *)

(** A reduction of bodies is given by its redexes [Rr]. It applies
    anywhere in a body ([body_step]), and in the body of a program
    ([prog_step]). *)
Inductive body_step (Rr : body -> body -> Prop) : body -> body -> Prop :=
| body_step_fill E r r' :
  Rr r r' ->
  body_step Rr (fill E r) (fill E r')
.
Arguments body_step_fill {_} _ _ _ _.

Inductive prog_step (Rr : body -> body -> Prop) : prog -> prog -> Prop :=
| prog_step_var x A p p' :
  prog_step Rr p p' ->
  prog_step Rr <{ VAR x : A ; p }> <{ VAR x : A ; p' }>
| prog_step_body y b b' :
  body_step Rr b b' ->
  prog_step Rr <{ { b } AS y }> <{ { b' } AS y }>
.
Arguments prog_step_var {_} _ _ _ _ _.
Arguments prog_step_body {_} _ _ _ _.

#[global] Instance body_step_sym Rr : Symmetric Rr -> Symmetric (body_step Rr).
Proof. intros ? b b' [E r r' H]. constructor. by symmetry. Qed.

#[global] Instance prog_step_sym Rr : Symmetric Rr -> Symmetric (prog_step Rr).
Proof. intros ? p p' H. induction H; constructor; by try symmetry. Qed.

(** * Garbage reduction *)

(** Removing a binding that is not used in its scope *)
Inductive garb_redex : body -> body -> Prop :=
| garb_let x A o k :
  LVar x ∉ body_fv k ->
  garb_redex <{ LET x : A = o IN k }> k
| garb_sub x y A B s k :
  SVar x y ∉ body_fv k ->
  garb_redex <{ LET SUB [x, y] : A → B = SUB (VAR x) { s } IN k }> k
.

Abbreviation body_garb_step := (body_step garb_redex).
Abbreviation let_garb_step := (prog_step garb_redex).

Definition let_garb : relation prog := rtc let_garb_step.

(** * Independent bindings swap *)

(** Swapping two adjacent bindings, when neither uses the other. The
    four cases correspond to the four cases of [indep_step]. The
    binding after the swapped pair is always followed by a body, so
    the [RETURN] of a (sub)routine never moves; this corresponds to
    the [not_closing] side conditions of [indep_step]. *)
Inductive indep_redex : body -> body -> Prop :=
| indep_let_let x1 x2 A1 A2 o1 o2 k :
  LVar x1 ∉ op_vars o2 ->
  LVar x2 ∉ op_vars o1 ->
  indep_redex
    <{ LET x1 : A1 = o1 IN LET x2 : A2 = o2 IN k }>
    <{ LET x2 : A2 = o2 IN LET x1 : A1 = o1 IN k }>
| indep_let_sub n B o x y A C s k :
  LVar n ∉ body_fv s ->
  SVar x y ∉ op_vars o ->
  indep_redex
    <{ LET n : B = o IN LET SUB [x, y] : A → C = SUB (VAR x) { s } IN k }>
    <{ LET SUB [x, y] : A → C = SUB (VAR x) { s } IN LET n : B = o IN k }>
| indep_sub_let n B o x y A C s k :
  LVar n ∉ body_fv s ->
  SVar x y ∉ op_vars o ->
  indep_redex
    <{ LET SUB [x, y] : A → C = SUB (VAR x) { s } IN LET n : B = o IN k }>
    <{ LET n : B = o IN LET SUB [x, y] : A → C = SUB (VAR x) { s } IN k }>
| indep_sub_sub x1 y1 A1 B1 s1 x2 y2 A2 B2 s2 k :
  SVar x1 y1 ∉ body_fv s2 ->
  SVar x2 y2 ∉ body_fv s1 ->
  indep_redex
    <{ LET SUB [x1, y1] : A1 → B1 = SUB (VAR x1) { s1 } IN
       LET SUB [x2, y2] : A2 → B2 = SUB (VAR x2) { s2 } IN k }>
    <{ LET SUB [x2, y2] : A2 → B2 = SUB (VAR x2) { s2 } IN
       LET SUB [x1, y1] : A1 → B1 = SUB (VAR x1) { s1 } IN k }>
.

Abbreviation body_indep_step := (body_step indep_redex).
Abbreviation let_indep_step := (prog_step indep_redex).

Definition let_indep : relation prog := rtc let_indep_step.

(** Typeclass properties *)
#[global] Instance indep_redex_sym : Symmetric indep_redex.
Proof. intros r r' H. inversion H; subst; by constructor. Qed.

#[global] Instance let_indep_sym : Symmetric let_indep.
Proof. apply _. Qed.


(** * Lifting redex inversions *)



(** The inversion of a kind of redex [Rr], for a line [s] followed by
    [Θ'], on the translation of a body [b0] followed by [post] *)
Definition redex_inv (Rr : body -> body -> Prop) (s : line) (Θ' Θ'' : prededuct) :=
  ∀ Γh b0 C z post,
    Γh ⊢ b0 : C -> NoDup (body_binders b0) -> ¬ not_closing post ->
    (post = [] ∨ z ∈ referenced_lines post) ->
    (∀ a c, ScopeClose a c ∈ post -> a ∉ body_binders b0) ->
    ⦇b0⦈ z ++ post = s :: Θ' ->
    ∃ b0', Rr b0 b0' ∧ ⦇b0'⦈ z ++ post = Θ''.

(** Lifting the inversion of a redex to a whole body *)
Lemma redex_lift Rr Γ b C y Θ1 s Θ' Θ'' :
  Γ ⊢ b : C -> NoDup (body_binders b) ->
  ⦇b⦈ y = Θ1 ++ s :: Θ' -> is_Some (id_of_line s) ->
  redex_inv Rr s Θ' Θ'' ->
  ∃ b', body_step Rr b b' ∧ ⦇b'⦈ y = Θ1 ++ Θ''.
Proof.
  intros Hb Hnd Heq Hs Hinv.
  rewrite -(app_nil_r (⦇b⦈ y)) in Heq.
  destruct (deduct_of_body_split _ _ _ Hb _ _ _ _ _ Heq Hs)
    as [(Θ1' & _ & HR)|(E & b0 & -> & -> & HE)]; [by destruct Θ1'|].
  destruct (fill_typed _ _ _ _ Hb) as (Γh & C' & Hb0 & _ & _).
  rewrite body_binders_fill in Hnd.
  destruct (Hinv Γh b0 C' (ectx_ret y E) (ectx_post y E ++ []))
    as (b0' & Hr & HE').
  - done.
  - by apply NoDup_app in Hnd as (_ & _ & (? & _)%NoDup_app).
  - apply ectx_post_not_closing. by intros [? ?].
  - rewrite app_nil_r. destruct (ectx_post_ret y E) as [[-> _]|]; auto.
  - intros a c Hsc Ha. rewrite app_nil_r in Hsc.
    destruct (NoDup_mid _ _ _ a Hnd Ha).
    by destruct (ectx_post_scs _ _ _ _ _ _ _ Hb Hsc).
  - by rewrite HE.
  - exists (fill E b0'). split; [by constructor|].
    by rewrite deduct_of_body_fill -HE' app_nil_r.
Qed.

(** * Well-formedness under contexts *)

Lemma ret_ty_fill E b b' :
  ret_ty b' = ret_ty b -> ret_ty (fill E b') = ret_ty (fill E b).
Proof. intros Hr. induction E as [|[] E IH]; simpl; auto. Qed.

Lemma body_wf_fill_inv E b : body_wf (fill E b) -> body_wf b.
Proof. induction E as [|[x A o|x y A B k|x y A B []] E IH]; simpl; naive_solver. Qed.

Lemma body_wf_fill E b b' :
  body_wf (fill E b) -> body_wf b' -> ret_ty b' = ret_ty b -> body_wf (fill E b').
Proof.
  induction E as [|[x A o|x y A B k|x y A B []] E IH]; simpl;
    intros Hwf Hb' Hr; [done|naive_solver| |naive_solver].
  destruct Hwf as (-> & ? & ?). split_and!; [|by apply IH|done].
  by rewrite (ret_ty_fill _ _ _ Hr).
Qed.

(** * Generic results *)

(** The program-level results hold for any kind of redex [Rr] that
    keeps programs well-formed. They relate the reduction of programs
    to a reduction [Rd] of deductions, given the corresponding results
    for bodies. Subject reduction is not proved for each kind of redex
    separately: it follows from the validity of [Rd] (see
    [reductions/validity.v]), using the fact that the translation of a
    well-typed program is a deduction ([deduct_of_term_ok]). *)

(** Redexes preserve well-formedness and the type of the return *)
Definition redex_wf (Rr : body -> body -> Prop) : Prop :=
  ∀ r r', Rr r r' -> body_wf r -> body_wf r' ∧ ret_ty r' = ret_ty r.

Section generic.
  Context (Rr : body -> body -> Prop) (Rd : relation prededuct).

  Hypothesis Hwf : redex_wf Rr.
  (** Validity of the reduction of deductions *)
  Hypothesis Hvalid : ∀ Σ Σ', Rd Σ Σ' -> is_deduct Σ -> is_deduct Σ'.
  Hypothesis Hconcl : ∀ Σ Σ', Rd Σ Σ' -> conclusion_of Σ' = conclusion_of Σ.
  (** From programs to deductions *)
  Hypothesis Hcons : ∀ s Σ Σ', Rd Σ Σ' -> Rd (s :: Σ) (s :: Σ').
  Hypothesis Hfwd : ∀ Γ b b' C y,
    Γ ⊢ b : C -> NoDup (ctx_ids Γ ++ body_binders b) ->
    body_step Rr b b' -> Rd (⦇b⦈ y) (⦇b'⦈ y).
  (** From deductions to programs *)
  Hypothesis Hassume : ∀ A x Σ Σ',
    Rd (Assume A x :: Σ) Σ' -> ∃ Σ'', Σ' = Assume A x :: Σ'' ∧ Rd Σ Σ''.
  Hypothesis Hinv : ∀ Γ b C y Σ',
    Γ ⊢ b : C -> NoDup (body_binders b) -> Rd (⦇b⦈ y) Σ' ->
    ∃ b', body_step Rr b b' ∧ ⦇b'⦈ y = Σ'.

  (** ** Well-formedness *)

  Lemma body_step_wf b b' : body_wf b -> body_step Rr b b' -> body_wf b'.
  Proof using Hwf.
    intros Hb Hstep. revert Hb. destruct Hstep as [E r r' Hr]; intros Hb.
    destruct (Hwf _ _ Hr) as [? ?]; [by eapply body_wf_fill_inv|].
    by eapply body_wf_fill.
  Qed.

  Lemma prog_step_wf p p' : prog_wf p -> prog_step Rr p p' -> prog_wf p'.
  Proof using Hwf.
    intros Hp Hstep. revert Hp.
    induction Hstep; simpl; eauto using body_step_wf.
  Qed.

  (** ** From programs to deductions *)

  Lemma prog_step_to_deduct_ctx Γ p p' C :
    Γ ⊢ₚ p : C ->
    NoDup (ctx_ids Γ ++ prog_binders p) ->
    prog_step Rr p p' ->
    Rd ⦇p⦈ᶜ ⦇p'⦈ᶜ.
  Proof using Hcons Hfwd.
    intros Hp Hnd Hstep. revert Γ Hp Hnd.
    induction Hstep as [x A p p' _ IH|y b b' Hstep]; intros Γ Hp Hnd;
      inversion Hp; subst; simpl in *.
    - apply Hcons, (IH _ ltac:(eassumption)).
      rewrite /ctx_ids /= -/(ctx_ids _). by rewrite -Permutation_middle in Hnd.
    - eapply Hfwd; [done| |done].
      rewrite app_assoc NoDup_app in Hnd. by destruct Hnd.
  Qed.

  Lemma prog_step_to_deduct p p' C :
    prog_ok p C -> prog_step Rr p p' -> Rd ⦇p⦈ᶜ ⦇p'⦈ᶜ.
  Proof using Hcons Hfwd. intros [Hnd Hp]. by eapply prog_step_to_deduct_ctx. Qed.

  (** ** Subject reduction *)

  (** The translation of the reduct is a deduction by [Hvalid]; hence
      the reduct is well-typed by [prog_typed_of_deduct] *)
  Lemma prog_step_ok p p' C :
    prog_ok p C -> prog_step Rr p p' -> prog_ok p' C.
  Proof using Hwf Hvalid Hconcl Hcons Hfwd.
    clear Hassume Hinv. intros Hok Hstep.
    pose proof (prog_step_to_deduct _ _ _ Hok Hstep) as HRd.
    destruct (Hvalid _ _ HRd (deduct_of_term_ok _ _ Hok)) as (Hok' & _ & Hnd' & _).
    assert (Hty' : prog_typed [] p' (prog_ret_ty p')).
    { apply (prog_typed_of_deduct _ []); [done|done| |split; simpl; set_solver].
      eapply prog_step_wf; [|done]. destruct Hok as [_ Hty]. by eapply prog_typed_wf. }
    pose proof (deduct_of_term_conclusion _ _ _ Hty') as HC'.
    rewrite (Hconcl _ _ HRd) (deduct_of_term_conclusion _ _ _ (proj2 Hok)) in HC'.
    injection HC' as ->. split; [|done].
    by rewrite /names_unique -lines_of_deduct_of_term.
  Qed.

  Lemma prog_steps_to_deduct p p' C :
    prog_ok p C -> rtc (prog_step Rr) p p' -> rtc Rd ⦇p⦈ᶜ ⦇p'⦈ᶜ ∧ prog_ok p' C.
  Proof using Hwf Hvalid Hconcl Hcons Hfwd.
    intros Hok Hsteps. induction Hsteps as [p|p p'' p' Hstep _ IH]; [done|].
    destruct IH as [HRd Hok']; [by eapply prog_step_ok|].
    split; [|done]. eapply rtc_l; [|done]. by eapply prog_step_to_deduct.
  Qed.

  (** ** From deductions to programs *)

  Lemma prog_step_inv Γ p C Σ' :
    Γ ⊢ₚ p : C -> NoDup (prog_binders p) -> Rd ⦇p⦈ᶜ Σ' ->
    ∃ p', prog_step Rr p p' ∧ ⦇p'⦈ᶜ = Σ'.
  Proof using Hassume Hinv.
    intros Hp. revert Σ'.
    induction Hp as [Γ x A p C _ IH|Γ y b C Hb]; intros Σ' Hnd Hstep; simpl in *.
    - destruct (Hassume _ _ _ _ Hstep) as (Σ'' & -> & Hstep').
      apply NoDup_cons in Hnd as [_ Hnd].
      destruct (IH _ Hnd Hstep') as (p' & ? & <-).
      exists <{ VAR x : A ; p' }>. split; [by constructor|done].
    - apply NoDup_app in Hnd as [Hnd _].
      destruct (Hinv _ _ _ _ _ Hb Hnd Hstep) as (b' & ? & <-).
      exists (PBody y b'). split; [by constructor|done].
  Qed.

  Theorem deduct_to_prog_step Σ Σ' :
    is_deduct Σ -> Rd Σ Σ' -> prog_step Rr ⟦Σ⟧ᶜ ⟦Σ'⟧ᶜ.
  Proof using Hwf Hvalid Hconcl Hcons Hfwd Hassume Hinv.
    intros HΣ Hstep. pose proof HΣ as (_ & _ & _ & [C HC]).
    destruct (term_of_deduct_ok Σ C HΣ HC) as [Hnd Hty'].
    rewrite -(deduct_of_term_of_deduct Σ HΣ) in Hstep.
    destruct (prog_step_inv _ _ _ _ Hty' Hnd Hstep) as (p' & Hp' & <-).
    destruct (prog_step_ok _ _ _ (conj Hnd Hty') Hp') as [_ Hty''].
    by rewrite (term_of_deduct_of_term _ _ _ Hty'').
  Qed.
End generic.

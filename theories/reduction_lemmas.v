(** Reduction infrastructure for the proof-to-term-to-proof direction. *)
From stdpp Require Import ssreflect.
From stdpp Require Import base strings relations.
From fitch Require Import prelude core deduction_lemmas.

(** Garbage collection commutes with restriction at every identifier that
    survives the step.  Depending on where the identifier occurs, the
    restricted proofs are either equal or related by the same garbage
    step. *)
Lemma garb_step_restr Σ Σ' :
  is_deduct Σ ->
  garb_step Σ Σ' ->
  forall i,
    i ∈ lines_of_prededuct Σ' ->
    restr Σ i = restr Σ' i \/
    garb_step (restr Σ i) (restr Σ' i).
Proof.
  intros Hdeduct.
  unfold is_deduct in Hdeduct.
  destruct Hdeduct as (_ & _ & Hnodup & _).
  inversion 1; subst.
  - intros i. revert Hnodup.
    rewrite !lines_of_prededuct_app.
    intros Hnodup.
    intros [Hi | Hi]%elem_of_app.
    + left. rewrite !restr_app_l //.
    + right.
      apply NoDup_app in Hnodup as (_ & Hsep1 & Hrest).
      apply NoDup_app in Hrest as (_ & Hsep2 & _).
      assert (i ∉ lines_of_prededuct Θ1).
      { intros Hi1. apply (Hsep1 i Hi1).
        apply elem_of_app. by right. }
      assert (i ∉ lines_of_prededuct [Deduce A j l]).
      { intros Himid. by eapply Hsep2. }
      rewrite !restr_app_r //.
      apply garb_step_deduce.
      * by apply restr_not_nil.
      * intros Hl. apply H1.
        by eapply referenced_lines_restr_subset.
  - intros i. revert Hnodup.
    rewrite !lines_of_prededuct_app.
    intros Hnodup.
    intros [Hi | Hi]%elem_of_app.
    + left. rewrite !restr_app_l //.
    + right.
      apply NoDup_app in Hnodup as (_ & Hsep1 & Hrest).
      apply NoDup_app in Hrest as (_ & Hsepraise & Hrest).
      apply NoDup_app in Hrest as (_ & Hsep2 & Hrest).
      apply NoDup_app in Hrest as (_ & Hsepclose & _).
      assert (i ∉ lines_of_prededuct Θ1).
      { intros Hi1. apply (Hsep1 i Hi1).
        apply elem_of_app. right. apply elem_of_app. right.
        apply elem_of_app. by right. }
      assert (i ∉ lines_of_prededuct Θ2).
      { intros Hi2. apply (Hsep2 i Hi2).
        apply elem_of_app. by right. }
      assert (i ∉ lines_of_prededuct [ScopeClose l1 l2]).
      { intros Hiclose. by eapply Hsepclose. }
      assert (i ∉ lines_of_prededuct [Raise A l1]).
      { intros Hiraise. apply (Hsepraise i Hiraise).
        apply elem_of_app. right. apply elem_of_app. by right. }
      rewrite !restr_app_r //.
      apply garb_step_subproof.
      * by apply restr_not_nil.
      * intros Hl. apply H1.
        by eapply referenced_lines_restr_subset.
      * intros Hl. apply H2.
        by eapply referenced_lines_restr_subset.
Qed.


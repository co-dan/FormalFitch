(* Generic one-frame-edit stack relation. The idea is that it encodes
 the effects of various reductions/transformations on the frame
 stack. *)
From stdpp Require Import base strings relations.
From fitch Require Import core deduction_lemmas.
From fitch Require Import prelude.

(* [stack_edit FE sW sO]: the two frame stacks are identical except that, in
   at most one frame, a local edit [FE] happened.  The concrete instances
   used for the reductions are [frame_edit RL RS] (end of this file), where
   [RL]/[RS] remove, insert or swap entries of [frame_lines]/
   [frame_subproofs].  They share this whole lemma suite: length
   preservation, transfer of the concatenated projections (the
   [scope]/[sp_scope] lemmas), and preservation under
   [frame_step]/[frame_stack_go]. *)
Section stack_edit.
  Context (FE : frame -> frame -> Prop).

  Inductive stack_edit : list frame -> list frame -> Prop :=
  | stack_edit_eq s : stack_edit s s
  | stack_edit_here fW fO rest :
      FE fW fO -> stack_edit (fW :: rest) (fO :: rest)
  | stack_edit_cons f sW sO :
      stack_edit sW sO -> stack_edit (f :: sW) (f :: sO).

  Lemma stack_edit_length sW sO : stack_edit sW sO -> length sW = length sO.
  Proof. induction 1; simpl; auto. Qed.

  (* Any reflexive, [FE]-closed property of frame pairs holds of the top
     frames. *)
  Lemma stack_edit_top (Q : frame -> frame -> Prop) aW aO sW sO :
    (forall f, Q f f) ->
    (forall f f', FE f f' -> Q f f') ->
    stack_edit (aW :: sW) (aO :: sO) -> Q aW aO.
  Proof. intros Hrefl HQ H; inversion H; subst; auto. Qed.

  (* If the edit can only move an element of the projection [g] sideways or
     out (into [P]), so can the whole stack edit. *)
  Lemma stack_edit_concat_elem_of {A} (g : frame -> list A) (P : A -> Prop) sW sO :
    (forall f f' x, FE f f' -> x ∈ g f -> x ∈ g f' ∨ P x) ->
    stack_edit sW sO ->
    forall x, x ∈ concat (map g sW) -> x ∈ concat (map g sO) ∨ P x.
  Proof.
    intros HFE. induction 1 as [s|fW fO rest HFEf|f sW' sO' Hb IH]; intros x Hx.
    - by left.
    - simpl in Hx |- *. apply elem_of_app in Hx as [Hx|Hx].
      + destruct (HFE _ _ _ HFEf Hx) as [Hx'|HP]; [left|by right].
        apply elem_of_app. by left.
      + left. apply elem_of_app. by right.
    - simpl in Hx |- *. apply elem_of_app in Hx as [Hx|Hx].
      + left. apply elem_of_app. by left.
      + destruct (IH x Hx) as [Hx'|HP]; [left|by right].
        apply elem_of_app. by right.
  Qed.

  (* If the edit preserves membership in the projection [g], so does the
     whole stack edit. *)
  (* If the edit preserves membership in the projection [g] of the elements
     satisfying [P], so does the whole stack edit. *)
  Lemma stack_edit_concat_sub_if {A} (g : frame -> list A) (P : A -> Prop) sW sO :
    (forall f f' x, FE f f' -> x ∈ g f -> P x -> x ∈ g f') ->
    stack_edit sW sO ->
    forall x, x ∈ concat (map g sW) -> P x -> x ∈ concat (map g sO).
  Proof.
    intros HFE. induction 1 as [s|fW fO rest HFEf|f sW' sO' Hb IH]; intros x Hx HP;
      simpl in *; [done| |]; rewrite elem_of_app in Hx; apply elem_of_app;
      naive_solver.
  Qed.

  Lemma stack_edit_concat_sub {A} (g : frame -> list A) sW sO :
    (forall f f' x, FE f f' -> x ∈ g f -> x ∈ g f') ->
    stack_edit sW sO ->
    forall x, x ∈ concat (map g sW) -> x ∈ concat (map g sO).
  Proof.
    intros HFE HE x Hx. by apply (stack_edit_concat_sub_if g (λ _, True) sW sO);
      [naive_solver| | |].
  Qed.

  (* The reverse direction: if the edit only adds elements to the projection
     [g], membership transfers from the edited stack back to the original. *)
  Lemma stack_edit_concat_sub_rev {A} (g : frame -> list A) sW sO :
    (forall f f' x, FE f f' -> x ∈ g f' -> x ∈ g f) ->
    stack_edit sW sO ->
    forall x, x ∈ concat (map g sO) -> x ∈ concat (map g sW).
  Proof.
    intros HFE. induction 1 as [s|fW fO rest HFEf|f sW' sO' Hb IH]; intros x Hx.
    - exact Hx.
    - simpl in Hx |- *. apply elem_of_app in Hx as [Hx|Hx]; apply elem_of_app.
      + left. exact (HFE _ _ _ HFEf Hx).
      + by right.
    - simpl in Hx |- *. apply elem_of_app in Hx as [Hx|Hx]; apply elem_of_app.
      + by left.
      + right. exact (IH x Hx).
  Qed.

  (* If the edit preserves the projection [g] exactly, so does the whole
     stack edit. *)
  Lemma stack_edit_concat_eq {A} (g : frame -> list A) sW sO :
    (forall f f', FE f f' -> g f = g f') ->
    stack_edit sW sO ->
    concat (map g sW) = concat (map g sO).
  Proof. intros HFE. induction 1; simpl; f_equal; auto. Qed.

  (* The [ScopeClose] rule transfers along an edit, as long as the edit
     cannot change the head of the closed frame. *)
  Lemma stack_edit_scopeclose_ok preW preO k1 k2 :
    stack_edit (frame_stack preW) (frame_stack preO) ->
    line_ok preW (ScopeClose k1 k2) ->
    last preO = last preW ->
    (forall fW fO s, FE fW fO ->
       frame_stack preW = fW :: s -> frame_stack preO = fO :: s -> s ≠ [] ->
       option_map snd (head (frame_lines fW)) = Some k1 ->
       option_map snd (head (frame_lines fO)) = Some k1) ->
    line_ok preO (ScopeClose k1 k2).
  Proof.
    intros HE Hline Hlast Hhead.
    apply (scopeclose_ok_transfer preW); [done|done|by rewrite (stack_edit_length _ _ HE)|].
    intros fO HfO.
    destruct Hline as [_ Hstk].
    destruct (frame_stack preW) as [|fW [|fW2 sW]] eqn:EW; try done.
    destruct (frame_stack preO) as [|fO' sO] eqn:EO; [done|]. simplify_eq/=.
    destruct Hstk as [Hh _].
    inversion HE; subst; [done| |done].
    by eapply Hhead.
  Qed.

  (* The two closure conditions under which [stack_edit] is preserved by
     [frame_step]: the edit must commute with appending a line to a frame
     (what [Assume]/[Deduce] do to the top frame) and with appending a closed
     subproof to a frame (what [ScopeClose] does to the promoted frame). *)
  Hypothesis FE_snoc_line : forall fW fO x,
    FE fW fO ->
    FE (mkFrame (frame_lines fW ++ [x]) (frame_subproofs fW))
       (mkFrame (frame_lines fO ++ [x]) (frame_subproofs fO)).

  Hypothesis FE_snoc_subproof : forall fW fO x,
    FE fW fO ->
    FE (mkFrame (frame_lines fW) (frame_subproofs fW ++ [x]))
       (mkFrame (frame_lines fO) (frame_subproofs fO ++ [x])).

  (* Promoting (appending one subproof [x] to) the top frames preserves the
     edit — this is what [ScopeClose] does to the frame it promotes. *)
  Lemma stack_edit_promote aW aO x sW sO :
    stack_edit (aW :: sW) (aO :: sO) ->
    stack_edit (mkFrame (frame_lines aW) (frame_subproofs aW ++ [x]) :: sW)
               (mkFrame (frame_lines aO) (frame_subproofs aO ++ [x]) :: sO).
  Proof.
    intros H; inversion H; subst.
    - apply stack_edit_eq.
    - apply stack_edit_here. by apply FE_snoc_subproof.
    - by apply stack_edit_cons.
  Qed.

  (* One step preserves the edit: only a [ScopeClose] consults the prefix,
     so it suffices that the two prefixes agree at the ids it looks up. *)
  Lemma stack_edit_step preW preO stkW stkO s :
    (forall l1 l2, s = ScopeClose l1 l2 ->
       frml_at preW l1 = frml_at preO l1 /\ frml_at preW l2 = frml_at preO l2) ->
    stack_edit stkW stkO ->
    stack_edit (frame_step preW stkW s) (frame_step preO stkO s).
  Proof.
    intros Hsc Hedit.
    destruct s as [f0 m | f0 m | l1 l2 | f0 j0 m].
    - (* Assume: the top frame gains one line. *)
      destruct Hedit as [s0|fW fO rest HFE|f sW sO Hb].
      + apply stack_edit_eq.
      + simpl. apply stack_edit_here. by apply FE_snoc_line.
      + simpl. apply stack_edit_cons. exact Hb.
    - (* Raise: the same fresh frame is pushed on both stacks. *)
      simpl. apply stack_edit_cons. exact Hedit.
    - (* ScopeClose: the top frame is popped, the next one promoted. *)
      destruct (Hsc l1 l2 eq_refl) as [Ha1 Ha2].
      destruct Hedit as [s0|fW fO rest HFE|f sW sO Hb].
      + simpl. destruct s0 as [|a [|b rest]]; try apply stack_edit_eq.
        rewrite Ha1 Ha2.
        destruct (frml_at preO l1), (frml_at preO l2); apply stack_edit_eq.
      + destruct rest as [|fr2 rest'].
        * simpl. by apply stack_edit_here.
        * simpl. rewrite Ha1 Ha2.
          destruct (frml_at preO l1), (frml_at preO l2);
            try (by apply stack_edit_here); apply stack_edit_eq.
      + destruct sW as [|a sW'].
        * inversion Hb; subst. simpl. apply stack_edit_eq.
        * destruct sO as [|b sO']; [inversion Hb|].
          simpl. rewrite Ha1 Ha2.
          destruct (frml_at preO l1), (frml_at preO l2);
            try (apply stack_edit_cons; exact Hb).
          by apply stack_edit_promote.
    - (* Deduce: the top frame gains one line. *)
      destruct Hedit as [s0|fW fO rest HFE|f sW sO Hb].
      + apply stack_edit_eq.
      + simpl. apply stack_edit_here. by apply FE_snoc_line.
      + simpl. apply stack_edit_cons. exact Hb.
  Qed.

  (* Running a whole suffix [Δ] preserves the edit, provided the two
     prefixes agree at every id that a [ScopeClose] in [Δ] looks up.
     (Agreement at a fixed id is stable under extending both prefixes by the
     same lines, so the hypothesis carries through the induction.) *)
  Lemma stack_edit_run preW preO stkW stkO Δ :
    (forall l1 l2, ScopeClose l1 l2 ∈ Δ ->
       line_at preW l1 = line_at preO l1 /\ line_at preW l2 = line_at preO l2) ->
    stack_edit stkW stkO ->
    stack_edit (frame_stack_go preW stkW Δ) (frame_stack_go preO stkO Δ).
  Proof.
    revert preW preO stkW stkO.
    induction Δ as [|s Δ IH]; intros preW preO stkW stkO Hsc Hedit; simpl.
    - exact Hedit.
    - apply IH.
      + intros l1 l2 Hin.
        destruct (Hsc l1 l2) as [Ha1 Ha2]; [apply elem_of_cons; by right|].
        rewrite !line_at_app Ha1 Ha2. split; reflexivity.
      + apply stack_edit_step; [|exact Hedit].
        intros l1 l2 ->.
        destruct (Hsc l1 l2) as [Ha1 Ha2]; [apply elem_of_cons; by left|].
        unfold frml_at. rewrite Ha1 Ha2. split; reflexivity.
  Qed.


  (* If two prefixes have edited stacks, and every [ScopeClose] of the
     common continuation [Θ] looks up the same formulas in both, the stacks
     stay edited along all of [Θ].  Unlike [stack_edit_run], the lookups may
     be justified using the edit for the prefixes so far. *)
  Lemma stack_edit_prefixes ΣW ΣO Θ :
    stack_edit (frame_stack ΣW) (frame_stack ΣO) ->
    (forall Δ k1 k2 rest, Θ = Δ ++ ScopeClose k1 k2 :: rest ->
       stack_edit (frame_stack (ΣW ++ Δ)) (frame_stack (ΣO ++ Δ)) ->
       frml_at (ΣW ++ Δ) k1 = frml_at (ΣO ++ Δ) k1 ∧
       frml_at (ΣW ++ Δ) k2 = frml_at (ΣO ++ Δ) k2) ->
    forall Δ rest, Θ = Δ ++ rest ->
      stack_edit (frame_stack (ΣW ++ Δ)) (frame_stack (ΣO ++ Δ)).
  Proof.
    intros H0 Hagree Δ. induction Δ as [|s Δ IH] using rev_ind; intros rest HΘ.
    - by rewrite !app_nil_r.
    - rewrite !app_assoc !frame_stack_snoc.
      apply stack_edit_step.
      + intros l1 l2 ->. apply (Hagree Δ l1 l2 rest); [by rewrite HΘ -app_assoc|].
        apply (IH (ScopeClose l1 l2 :: rest)). by rewrite HΘ -app_assoc.
      + apply (IH (s :: rest)). by rewrite HΘ -app_assoc.
  Qed.
End stack_edit.

Lemma stack_edit_flip FE sW sO :
  stack_edit FE sW sO -> stack_edit (flip FE) sO sW.
Proof. induction 1; by constructor. Qed.

(** * Frame edits given by list relations *)

(* [frame_edit RL RS fW fO]: the lines of the two frames are related by
   [RL], and their subproofs by [RS]. All the edits made by the reductions
   are of this form. *)
Definition frame_edit (RL : relation (list (frml * id)))
    (RS : relation (list subproof)) (fW fO : frame) : Prop :=
  RL (frame_lines fW) (frame_lines fO) ∧ RS (frame_subproofs fW) (frame_subproofs fO).

Lemma stack_edit_frame_edit_flip RL RS sW sO :
  stack_edit (frame_edit RL RS) sW sO ->
  stack_edit (frame_edit (flip RL) (flip RS)) sO sW.
Proof. apply stack_edit_flip. Qed.

(* When [RL] and [RS] are [list_edit]s keeping the entries whose ids satisfy
   [Keep], the frame edit is preserved by [frame_step], and justifications
   citing only such ids transfer along it. *)
Section frame_edit.
  Context {RL : relation (list (frml * id))} {RS : relation (list subproof)}.
  Context {Keep : id -> Prop}.
  Context (HL : list_edit RL (λ x, Keep x.2)).
  Context (HS : list_edit RS (λ q, Keep (sp_start q))).

  Lemma frame_edit_snoc_line fW fO x :
    frame_edit RL RS fW fO ->
    frame_edit RL RS (mkFrame (frame_lines fW ++ [x]) (frame_subproofs fW))
                     (mkFrame (frame_lines fO ++ [x]) (frame_subproofs fO)).
  Proof. intros [??]. split; [by apply (list_edit_snoc _ _ HL)|done]. Qed.

  Lemma frame_edit_snoc_subproof fW fO x :
    frame_edit RL RS fW fO ->
    frame_edit RL RS (mkFrame (frame_lines fW) (frame_subproofs fW ++ [x]))
                     (mkFrame (frame_lines fO) (frame_subproofs fO ++ [x])).
  Proof. intros [??]. split; [done|by apply (list_edit_snoc _ _ HS)]. Qed.

  Lemma stack_edit_just_ok preW preO f j :
    stack_edit (frame_edit RL RS) (frame_stack preW) (frame_stack preO) ->
    (forall k, k ∈ references_in_just j -> Keep k) ->
    just_ok preW f j -> just_ok preO f j.
  Proof.
    intros HE HK. apply just_ok_transfer.
    - intros g k Hk Hin. apply (stack_edit_concat_sub_if _ frame_lines (λ x, Keep x.2) _ _
        (λ _ _ _ H, list_edit_elem_of _ _ HL _ _ _ (proj1 H)) HE _ Hin). by apply HK.
    - intros q Hk Hin. apply (stack_edit_concat_sub_if _ frame_subproofs (λ q, Keep (sp_start q)) _ _
        (λ _ _ _ H, list_edit_elem_of _ _ HS _ _ _ (proj2 H)) HE _ Hin). by apply HK.
  Qed.
End frame_edit.

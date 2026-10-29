(** Validity of the reductions: garbage removal ([garb]) and swapping
    independent statements ([indep]) map deductions to deductions.

    Proof pattern: a reduction replaces a prefix [ΣW] of the proof by a
    prefix [ΣO], and keeps the continuation [Θ].  The frame stacks of [ΣW]
    and [ΣO] differ by a one-frame edit [frame_edit RL RS] (see
    [stackedit.v]), where [RL] and [RS] remove an entry ([list_del]), insert
    one ([flip list_del]) or swap two adjacent ones ([list_swap]).  The
    generic lemma [edit_lines_ok] carries the edit along [Θ] and re-checks
    every line of [Θ]; each reduction only supplies a few local facts. *)
From stdpp Require Import base strings relations.
From fitch Require Import prelude core deduction_lemmas.
From fitch.reductions Require Import stackedit.

(* A closed subproof, as it appears in the reductions. *)
Abbreviation closed_block A l1 Θ2 l2 := (Raise A l1 :: Θ2 ++ [ScopeClose l1 l2]).

(** * Carrying a frame edit along a continuation *)

Section edit_tail.
  Context {RL : relation (list (frml * id))} {RS : relation (list subproof)}.
  Context {Keep : id -> Prop}.
  Context (HL : list_edit RL (λ x, Keep x.2)).
  Context (HS : list_edit RS (λ q, Keep (sp_start q))).

  (* Let [ΣW ++ Θ] be legal and [ΣO] be legal, with the stacks of [ΣW] and
     [ΣO] related by the edit.  Then [ΣO ++ Θ] is legal (and the edit
     persists), provided:
     - [ΣW] is not only assumptions, so [Θ] has no [Assume];
     - [Θ] only cites ids satisfying [Keep] (the entries the edit keeps);
     - the edit does not change the lines that the closes in [Θ] look up;
     - a close right after the prefix still comes right after its last line;
     - the edit does not change the head of a frame that [Θ] closes. *)
  Lemma edit_lines_ok ΣW ΣO Θ :
    lines_ok (ΣW ++ Θ) -> lines_ok ΣO ->
    stack_edit (frame_edit RL RS) (frame_stack ΣW) (frame_stack ΣO) ->
    (∃ s, s ∈ ΣW ∧ ¬ is_assume s) ->
    (forall k, k ∈ referenced_lines Θ -> Keep k) ->
    (forall Δ rest f k, Θ = Δ ++ rest ->
       stack_edit (frame_edit RL RS) (frame_stack (ΣW ++ Δ)) (frame_stack (ΣO ++ Δ)) ->
       (f, k) ∈ scope (ΣW ++ Δ) -> Keep k ->
       line_at (ΣW ++ Δ) k = line_at (ΣO ++ Δ) k) ->
    (forall k1 k2 rest, Θ = ScopeClose k1 k2 :: rest -> Keep k2 ->
       line_ok ΣW (ScopeClose k1 k2) -> last ΣO = last ΣW) ->
    (forall Δ rest k fW fO s, Θ = Δ ++ rest -> frame_edit RL RS fW fO ->
       frame_stack (ΣW ++ Δ) = fW :: s -> frame_stack (ΣO ++ Δ) = fO :: s ->
       s ≠ [] -> Keep k ->
       option_map snd (head (frame_lines fW)) = Some k ->
       option_map snd (head (frame_lines fO)) = Some k) ->
    lines_ok (ΣO ++ Θ) ∧
    stack_edit (frame_edit RL RS) (frame_stack (ΣW ++ Θ)) (frame_stack (ΣO ++ Θ)).
  Proof.
    intros HokW HokO H0 Hna HK Hagree Hfirst Hhead.
    assert (HKs : forall Δ s rest k,
      Θ = Δ ++ s :: rest -> k ∈ references_in_line s -> Keep k).
    { intros Δ s rest k -> Hk. apply HK, (referenced_lines_elem_of _ s); [set_solver|done]. }
    assert (Hedit : forall Δ rest, Θ = Δ ++ rest ->
      stack_edit (frame_edit RL RS) (frame_stack (ΣW ++ Δ)) (frame_stack (ΣO ++ Δ))).
    { apply stack_edit_prefixes;
        [apply (frame_edit_snoc_line HL)|apply (frame_edit_snoc_subproof HS)|done|].
      intros Δ k1 k2 rest HΘ HE.
      assert (Keep k1 ∧ Keep k2) as [HK1 HK2].
      { split; (eapply HKs; [exact HΘ|set_solver]). }
      destruct (scopeclose_ids_in_scope (ΣW ++ Δ) k1 k2) as [[f1 Hk1] [f2 Hk2]].
      { apply (lines_ok_line_ok _ _ _ rest). by rewrite -HΘ. }
      by rewrite /frml_at (Hagree Δ _ f1 k1 HΘ HE Hk1 HK1) (Hagree Δ _ f2 k2 HΘ HE Hk2 HK2). }
    split; [|by apply (Hedit Θ []); rewrite app_nil_r].
    apply (lines_ok_tail_transfer ΣW ΣO Θ); [done| |done].
    intros Δ s rest HΘ _ _ Hline.
    pose proof (Hedit Δ (s :: rest) HΘ) as HE.
    destruct s as [f k|f k|k1 k2|f j k].
    - (* Assume: impossible after a non-assumption *)
      exfalso. destruct Hna as (s & Hs & Hna). apply Hna.
      eapply Forall_forall; [exact Hline|set_solver].
    - done.
    - (* ScopeClose *)
      eapply (stack_edit_scopeclose_ok _ _ _ _ _ HE Hline).
      + destruct Δ as [|s' Δ']; [|by apply last_app_ne].
        rewrite !app_nil_r in Hline |- *. eapply Hfirst; [exact HΘ| |done].
        eapply HKs; [exact HΘ|set_solver].
      + intros fW fO s' HFE EW EO Hs'. eapply Hhead; [exact HΘ|done..|].
        eapply HKs; [exact HΘ|set_solver].
    - (* Deduce *)
      apply (stack_edit_just_ok HL HS _ _ _ _ HE); [|done].
      intros k' Hk'. by eapply HKs.
  Qed.
End edit_tail.

(* The remaining conditions of [is_deduct] for the result of
   [edit_lines_ok]: the edit keeps the stack height. *)
Lemma edit_is_deduct FE ΣW ΣO Θ :
  lines_ok (ΣO ++ Θ) ∧ stack_edit FE (frame_stack (ΣW ++ Θ)) (frame_stack (ΣO ++ Θ)) ->
  NoDup (lines_of_prededuct (ΣO ++ Θ)) -> Θ ≠ [] ->
  is_deduct (ΣW ++ Θ) -> is_deduct (ΣO ++ Θ).
Proof.
  intros [Hok HE] Hnd HΘ (_ & Hlen & _ & Hconc).
  split_and!; [done|by rewrite -(stack_edit_length _ _ _ HE)|done|].
  by rewrite (conclusion_of_mid ΣO ΣW).
Qed.

(** * Removing and inserting lines and closed subproofs *)

(* Appending a [Deduce] line adds it to the top frame. *)
Lemma deduce_edit Σ A j l :
  stack_edit (frame_edit (list_del (λ x : frml * id, x.2 = l)) (=))
    (frame_stack (Σ ++ [Deduce A j l])) (frame_stack Σ).
Proof.
  destruct (frame_stack_snoc_deduce Σ A j l) as (fr & rest & -> & ->).
  apply stack_edit_here. split; [|done].
  exists (frame_lines fr), (A, l), []. by rewrite app_nil_r.
Qed.

(* Appending a legal closed subproof adds it to the top frame. *)
Lemma closed_block_edit P A l1 Θ2 l2 :
  lines_ok (P ++ closed_block A l1 Θ2 l2) ->
  NoDup (lines_of_prededuct (P ++ closed_block A l1 Θ2 l2)) ->
  stack_edit (frame_edit (=) (list_del (λ q, sp_start q = l1)))
    (frame_stack (P ++ closed_block A l1 Θ2 l2)) (frame_stack P).
Proof.
  intros Hok Hnd.
  destruct (frame_stack_closed_block P A l1 Θ2 l2 Hok Hnd)
    as (fr & rest & f2 & j & -> & _ & ->).
  apply stack_edit_here. split; [done|].
  exists (frame_subproofs fr), (SubProof A l1 f2 l2), []. by rewrite app_nil_r.
Qed.

Lemma closed_block_last P A l1 Θ2 l2 :
  last (P ++ closed_block A l1 Θ2 l2) = Some (ScopeClose l1 l2).
Proof. by rewrite app_comm_cons app_assoc last_snoc. Qed.

(* Removing a [Deduce] line that is not cited later. *)
Lemma garb_line_lines_ok Θ1 A j l Θ :
  lines_ok ((Θ1 ++ [Deduce A j l]) ++ Θ) -> l ∉ referenced_lines Θ ->
  lines_ok (Θ1 ++ Θ) ∧
  stack_edit (frame_edit (list_del (λ x : frml * id, x.2 = l)) (=))
    (frame_stack ((Θ1 ++ [Deduce A j l]) ++ Θ)) (frame_stack (Θ1 ++ Θ)).
Proof.
  intros Hok Hl.
  apply (edit_lines_ok (Keep := λ k, k ≠ l) (list_edit_del _) (list_edit_eq _));
    [done| | | | | | |].
  - exact (prefix_lines_ok _ _ (prefix_lines_ok _ _ Hok)).
  - apply deduce_edit.
  - exists (Deduce A j l). split; [set_solver|by intros []].
  - intros k Hk ->. by apply Hl.
  - intros Δ rest f k _ _ _ Hk. rewrite -app_assoc line_at_app_mid //. set_solver.
  - intros k1 k2 rest _ Hk2 [Hlast _]. rewrite last_snoc /= in Hlast. by subst.
  - intros Δ rest k fW fO s _ [Hdel _] _ _ _ Hk Hh.
    destruct (list_del_head _ _ _ Hdel) as [->|(x & Hx & Hhx)]; [done|].
    rewrite Hhx /= in Hh. by simplify_eq.
Qed.

(* Removing a closed subproof that is not cited later. *)
Lemma garb_subproof_lines_ok Θ1 A l1 Θ2 l2 Θ :
  lines_ok ((Θ1 ++ closed_block A l1 Θ2 l2) ++ Θ) ->
  NoDup (lines_of_prededuct ((Θ1 ++ closed_block A l1 Θ2 l2) ++ Θ)) ->
  l1 ∉ referenced_lines Θ ->
  lines_ok (Θ1 ++ Θ) ∧
  stack_edit (frame_edit (=) (list_del (λ q, sp_start q = l1)))
    (frame_stack ((Θ1 ++ closed_block A l1 Θ2 l2) ++ Θ)) (frame_stack (Θ1 ++ Θ)).
Proof.
  intros Hok Hnd Hl.
  apply (edit_lines_ok (Keep := λ k, k ≠ l1) (list_edit_eq _) (list_edit_del _));
    [done| | | | | | |].
  - exact (prefix_lines_ok _ _ (prefix_lines_ok _ _ Hok)).
  - apply closed_block_edit; [by eapply prefix_lines_ok|by eapply nodup_lines_prefix].
  - exists (Raise A l1). split; [set_solver|by intros []].
  - intros k Hk ->. by apply Hl.
  - (* The ids in scope are not in the removed block. *)
    intros Δ rest f k HΘ HE Hk _.
    rewrite /scope (stack_edit_concat_eq _ frame_lines _ _ (λ _ _ H, proj1 H) HE) in Hk.
    apply scope_id_in_lines in Hk.
    rewrite -app_assoc line_at_app_mid //.
    apply (nodup_lines_mid_disjoint Θ1 _ Δ rest); [|done].
    by rewrite -HΘ app_assoc.
  - intros k1 k2 rest _ _ [Hlast _]. by rewrite closed_block_last in Hlast.
  - intros Δ rest k fW fO s _ [Hlines _] _ _ _ _ Hh. by rewrite -Hlines.
Qed.

(* Inserting a legal [Deduce] line in front of a subproof. *)
Lemma garb_line_lines_ok_rev Θ1 A j l A' l' Θ :
  lines_ok (Θ1 ++ Raise A' l' :: Θ) -> just_ok Θ1 A j ->
  NoDup (lines_of_prededuct (Θ1 ++ Deduce A j l :: Raise A' l' :: Θ)) ->
  lines_ok (Θ1 ++ Deduce A j l :: Raise A' l' :: Θ).
Proof.
  intros Hok Hj Hnd.
  pose proof (mid_proof_line_fresh Θ1 (Deduce A j l) l _ eq_refl Hnd) as Hl.
  replace (Θ1 ++ Deduce A j l :: Raise A' l' :: Θ)
    with (((Θ1 ++ [Deduce A j l]) ++ [Raise A' l']) ++ Θ) in Hnd |- * by list_assoc.
  rewrite (cons_middle _ Θ1 Θ) app_assoc in Hok.
  eapply proj1, (edit_lines_ok (Keep := λ _, True)
    (list_edit_ins (λ x : frml * id, x.2 = l) _) (list_edit_eq_flip _) (Θ1 ++ [Raise A' l']));
    [done| | | | | | |].
  - apply lines_ok_cons; [apply lines_ok_cons|done]; [|done].
    exact (prefix_lines_ok _ _ (prefix_lines_ok _ _ Hok)).
  - rewrite !frame_stack_snoc_raise.
    apply stack_edit_cons, stack_edit_frame_edit_flip, deduce_edit.
  - exists (Raise A' l'). split; [set_solver|by intros []].
  - done.
  - (* The ids in scope are not the inserted one. *)
    intros Δ rest f k HΘ _ Hk _. apply scope_id_in_lines in Hk.
    rewrite -!app_assoc (line_at_app_mid Θ1 [Deduce A j l]) //.
    rewrite HΘ !lines_of_prededuct_app /= !lines_of_prededuct_app in Hl Hk.
    set_solver.
  - intros. by rewrite !last_snoc.
  - (* The inserted line cannot head a frame that is closed later. *)
    intros Δ rest k fW fO [|fr s] HΘ [Hdel _] EW EO Hs _ Hh; [done|].
    destruct (list_del_head _ _ _ Hdel) as [<-|(x & Hx & Hhx)]; [done|].
    exfalso. eapply (frame_stack_top_not_deduce _ _ _ _ A j l); [|exact EO|set_solver|].
    + apply (nodup_lines_prefix _ rest). by rewrite -app_assoc -HΘ.
    + by rewrite Hhx /= Hx.
Qed.

(* Inserting a legal closed subproof in front of a subproof. *)
Lemma garb_subproof_lines_ok_rev Θ1 A l1 Θ2 l2 A' l' Θ :
  lines_ok (Θ1 ++ closed_block A l1 Θ2 l2) -> lines_ok (Θ1 ++ Raise A' l' :: Θ) ->
  NoDup (lines_of_prededuct (Θ1 ++ closed_block A l1 Θ2 l2 ++ Raise A' l' :: Θ)) ->
  lines_ok (Θ1 ++ closed_block A l1 Θ2 l2 ++ Raise A' l' :: Θ).
Proof.
  intros HokB Hok Hnd.
  replace (Θ1 ++ closed_block A l1 Θ2 l2 ++ Raise A' l' :: Θ)
    with (((Θ1 ++ closed_block A l1 Θ2 l2) ++ [Raise A' l']) ++ Θ) by list_assoc.
  rewrite (cons_middle _ Θ1 Θ) app_assoc in Hok.
  eapply proj1, (edit_lines_ok (Keep := λ _, True)
    (list_edit_eq_flip _) (list_edit_ins (λ q, sp_start q = l1) _) (Θ1 ++ [Raise A' l']));
    [done| | | | | | |].
  - by apply lines_ok_cons.
  - rewrite !frame_stack_snoc_raise.
    apply stack_edit_cons, stack_edit_frame_edit_flip, closed_block_edit; [done|].
    exact (nodup_lines_app_prefix _ _ _ Hnd).
  - exists (Raise A' l'). split; [set_solver|by intros []].
  - done.
  - (* The ids in scope are not in the inserted block. *)
    intros Δ rest f k HΘ _ Hk _. apply scope_id_in_lines in Hk.
    rewrite -!app_assoc (line_at_app_mid Θ1 (closed_block A l1 Θ2 l2)) //.
    apply (nodup_lines_mid_disjoint Θ1 _ ([Raise A' l'] ++ Δ) rest);
      [|by rewrite -app_assoc in Hk].
    by rewrite -app_assoc -HΘ.
  - intros. by rewrite !last_snoc.
  - intros Δ rest k fW fO s _ [Hlines _] _ _ _ _ Hh. by rewrite Hlines.
Qed.

(** * Garbage removal preserves deductions *)

Lemma garb_step_is_deduct Σ Σ' :
  garb_step Σ Σ' -> is_deduct Σ -> is_deduct Σ'.
Proof.
  intros Hstep Hded. pose proof Hded as (Hok & _ & Hnd & _).
  destruct Hstep as [Θ1 Θ3 A j l HΘ3 Hl|Θ1 Θ2 Θ3 A l1 l2 HΘ3 Hl1 _]; simpl in *.
  - rewrite (cons_middle _ Θ1 Θ3) app_assoc in Hok Hded.
    apply (edit_is_deduct _ _ _ _ (garb_line_lines_ok _ _ _ _ _ Hok Hl));
      [by eapply nodup_mid_proof_line|done|done].
  - assert (Heq : Θ1 ++ Raise A l1 :: Θ2 ++ ScopeClose l1 l2 :: Θ3 =
                  (Θ1 ++ closed_block A l1 Θ2 l2) ++ Θ3) by list_assoc.
    rewrite Heq in Hok Hnd Hded.
    apply (edit_is_deduct _ _ _ _ (garb_subproof_lines_ok _ _ _ _ _ _ Hok Hnd Hl1));
      [|done|done].
    move: Hnd. rewrite !lines_of_prededuct_app -app_assoc. apply NoDup_app_remove_mid.
Qed.

Lemma garb_is_deduct Σ Σ' :
  garb Σ Σ' -> is_deduct Σ -> is_deduct Σ'.
Proof. induction 1; eauto using garb_step_is_deduct. Qed.

(** * Swaps *)

(* A swap reorders the prefix: the lookups and the ids are unchanged, and
   the swapped lines may be cited later. *)
Lemma swap_is_deduct {RL RS} (HL : list_edit RL (λ _, True))
    (HS : list_edit RS (λ _, True)) ΣW ΣO Θ :
  ΣW ≡ₚ ΣO -> Θ ≠ [] -> lines_ok ΣO ->
  stack_edit (frame_edit RL RS) (frame_stack ΣW) (frame_stack ΣO) ->
  (∃ s, s ∈ ΣW ∧ ¬ is_assume s) ->
  (forall k1 k2 rest, Θ = ScopeClose k1 k2 :: rest ->
     line_ok ΣW (ScopeClose k1 k2) -> last ΣO = last ΣW) ->
  (forall Δ k fW fO s, NoDup (lines_of_prededuct (ΣW ++ Δ)) -> frame_edit RL RS fW fO ->
     frame_stack (ΣW ++ Δ) = fW :: s -> s ≠ [] ->
     option_map snd (head (frame_lines fW)) = Some k ->
     option_map snd (head (frame_lines fO)) = Some k) ->
  is_deduct (ΣW ++ Θ) -> is_deduct (ΣO ++ Θ).
Proof.
  intros Hp HΘ HokO H0 Hna Hfirst Hhead Hded. pose proof Hded as (HokW & _ & Hnd & _).
  assert (HndΔ : forall Δ rest, Θ = Δ ++ rest -> NoDup (lines_of_prededuct (ΣW ++ Δ))).
  { intros Δ rest ->. exact (nodup_lines_app_prefix _ _ _ Hnd). }
  assert (HndO : NoDup (lines_of_prededuct (ΣO ++ Θ))).
  { rewrite -(lines_of_prededuct_perm (ΣW ++ Θ)) //. by apply Permutation_app_tail. }
  apply (edit_is_deduct (frame_edit RL RS) ΣW ΣO Θ); [|done|done|done].
  apply (edit_lines_ok (Keep := λ _, True) HL HS); [done..| | |].
  - intros Δ rest f k HΘ' _ _ _. apply line_at_perm; [by apply Permutation_app_tail|].
    exact (HndΔ Δ rest HΘ').
  - intros k1 k2 rest HΘ' _. exact (Hfirst k1 k2 rest HΘ').
  - intros Δ rest k fW fO s HΘ' HFE EW _ Hs _. eapply Hhead; [exact (HndΔ Δ rest HΘ')|done..].
Qed.

Lemma indep_deduce_deduce_is_deduct Θ1 Θ3 A1 A2 j1 j2 l1 l2 :
  not_closing Θ3 ->
  l1 ∉ references_in_just j2 -> l2 ∉ references_in_just j1 ->
  is_deduct (Θ1 ++ [Deduce A1 j1 l1; Deduce A2 j2 l2] ++ Θ3) ->
  is_deduct (Θ1 ++ [Deduce A2 j2 l2; Deduce A1 j1 l1] ++ Θ3).
Proof.
  intros Hnc Hl1 Hl2 Hded. pose proof Hded as (Hok & _ & _ & _).
  rewrite app_assoc in Hded. rewrite app_assoc.
  apply (swap_is_deduct (list_edit_swap (λ x : frml * id, x.2 = l1) _) (list_edit_eq _)
           (Θ1 ++ [Deduce A1 j1 l1; Deduce A2 j2 l2]));
    [| | | | | | |done].
  - apply Permutation_app_head, perm_swap.
  - intros ->. by destruct Hnc.
  - (* Each swapped line is still legal *)
    change (Θ1 ++ [Deduce A2 j2 l2; Deduce A1 j1 l1])
      with (Θ1 ++ [Deduce A2 j2 l2] ++ [Deduce A1 j1 l1]).
    rewrite app_assoc. apply lines_ok_cons; [apply lines_ok_cons|].
    + exact (prefix_lines_ok _ _ Hok).
    + apply (stack_edit_just_ok (Keep := λ k, k ≠ l1) (list_edit_del _) (list_edit_eq _)
               (Θ1 ++ [Deduce A1 j1 l1])); [apply deduce_edit|by intros ? ? ->|].
      exact (lines_ok_line_ok Θ1 [Deduce A1 j1 l1] _ _ Hok).
    + apply (stack_edit_just_ok (Keep := λ _, True)
               (list_edit_ins (λ x : frml * id, x.2 = l2) _) (list_edit_eq_flip _) Θ1);
        [apply stack_edit_frame_edit_flip, deduce_edit|done|].
      exact (lines_ok_line_ok_here Θ1 _ _ Hok).
  - (* The two lines are recorded in the other order *)
    change (Θ1 ++ [Deduce A1 j1 l1; Deduce A2 j2 l2])
      with (Θ1 ++ [Deduce A1 j1 l1] ++ [Deduce A2 j2 l2]).
    change (Θ1 ++ [Deduce A2 j2 l2; Deduce A1 j1 l1])
      with (Θ1 ++ [Deduce A2 j2 l2] ++ [Deduce A1 j1 l1]).
    rewrite !app_assoc (frame_stack_snoc (_ ++ [Deduce A1 j1 l1]))
      (frame_stack_snoc (_ ++ [Deduce A2 j2 l2])).
    destruct (frame_stack_snoc_deduce Θ1 A1 j1 l1) as (fr & rest & E & ->).
    destruct (frame_stack_snoc_deduce Θ1 A2 j2 l2) as (? & ? & E' & ->).
    rewrite E in E'. injection E' as <- <-.
    apply stack_edit_here. split; [|done].
    exists (frame_lines fr), (A1, l1), (A2, l2), []. by rewrite -!app_assoc.
  - exists (Deduce A1 j1 l1). split; [set_solver|by intros []].
  - intros k1 k2 rest -> _. by destruct Hnc.
  - (* The first swapped line cannot head a frame that is closed later *)
    intros Δ k fW fO [|fr s] Hnd [Hswap _] EW Hs Hh; [done|].
    destruct (list_swap_head _ _ _ Hswap) as [->|(x & Hx & Hhx)]; [done|].
    exfalso. eapply (frame_stack_top_not_deduce _ _ _ _ A1 j1 l1 Hnd EW); [set_solver|].
    by rewrite Hhx /= Hx.
Qed.

(* A [Deduce] line commutes with a closed subproof that neither cites the
   other: both orders are legal, and they have the same frame stack. *)
Lemma deduce_block_comm Θ1 B j n A l1 Θ2 l2 :
  n ∉ referenced_lines Θ2 -> l1 ∉ references_in_just j ->
  NoDup (lines_of_prededuct (Θ1 ++ Deduce B j n :: closed_block A l1 Θ2 l2)) ->
  lines_ok (Θ1 ++ Deduce B j n :: closed_block A l1 Θ2 l2) ∨
  lines_ok (Θ1 ++ closed_block A l1 Θ2 l2 ++ [Deduce B j n]) ->
  lines_ok (Θ1 ++ Deduce B j n :: closed_block A l1 Θ2 l2) ∧
  lines_ok (Θ1 ++ closed_block A l1 Θ2 l2 ++ [Deduce B j n]) ∧
  frame_stack (Θ1 ++ Deduce B j n :: closed_block A l1 Θ2 l2) =
    frame_stack (Θ1 ++ closed_block A l1 Θ2 l2 ++ [Deduce B j n]).
Proof.
  intros Hn Hl1 Hnd Hok.
  pose proof (nodup_mid_proof_line _ _ _ Hnd) as HndB.
  pose proof (mid_proof_line_fresh Θ1 (Deduce B j n) n _ eq_refl Hnd) as Hfresh.
  rewrite (cons_middle _ Θ1) app_assoc in Hnd Hok |- *.
  (* The block alone is legal: [Deduce B j n] is not cited in it. *)
  assert (HokB : lines_ok (Θ1 ++ closed_block A l1 Θ2 l2)).
  { destruct Hok as [Hok|Hok]; [|rewrite app_assoc in Hok; by eapply prefix_lines_ok].
    eapply proj1, garb_line_lines_ok; [done|].
    destruct (closed_block_last_line (Θ1 ++ [Deduce B j n]) A l1 Θ2 l2) as (f & j' & Hl2);
      [done|].
    apply last_Some_elem_of in Hl2.
    rewrite /= referenced_lines_app /= lines_of_prededuct_app /= lines_of_prededuct_app in Hfresh |- *.
    assert (l2 ∈ lines_of_prededuct Θ2) by by eapply id_in_lines_of_prededuct.
    set_solver. }
  destruct (frame_stack_closed_block Θ1 A l1 Θ2 l2 HokB HndB)
    as (fr & rest & f2 & j2 & E0 & HL & E1).
  (* Either order is legal, given the other one. *)
  assert (HokDB : lines_ok ((Θ1 ++ [Deduce B j n]) ++ closed_block A l1 Θ2 l2)).
  { destruct Hok as [Hok|Hok]; [done|].
    rewrite -app_assoc. apply garb_line_lines_ok_rev; [done| |by rewrite -app_assoc in Hnd].
    rewrite app_assoc in Hok. apply lines_ok_snoc_inv in Hok as [_ Hj].
    apply (stack_edit_just_ok (Keep := λ k, k ≠ l1) (list_edit_eq _) (list_edit_del _)
             (Θ1 ++ closed_block A l1 Θ2 l2)); [|by intros ? ? ->|done].
    by apply closed_block_edit. }
  assert (HokBD : lines_ok (Θ1 ++ closed_block A l1 Θ2 l2 ++ [Deduce B j n])).
  { destruct Hok as [Hok|Hok]; [|done].
    rewrite app_assoc. apply lines_ok_cons; [done|].
    apply (stack_edit_just_ok (Keep := λ _, True)
             (list_edit_eq_flip _) (list_edit_ins (λ q, sp_start q = l1) _) Θ1);
      [|done|apply (lines_ok_line_ok_here Θ1 (Deduce B j n) (closed_block A l1 Θ2 l2)); by rewrite -app_assoc in HokDB].
    apply stack_edit_frame_edit_flip, closed_block_edit; [done|].
    exact HndB. }
  split_and!; [done|done|].
  destruct (frame_stack_closed_block (Θ1 ++ [Deduce B j n]) A l1 Θ2 l2)
    as (fr' & rest' & f2' & j2' & E0' & HL' & ->); [done..|].
  rewrite app_assoc frame_stack_snoc E1.
  rewrite frame_stack_snoc E0 in E0'. injection E0' as <- <-.
  rewrite HL in HL'. by simplify_eq.
Qed.

(* A reordering of the prefix that leaves its frame stack unchanged. *)
Lemma same_stack_is_deduct ΣW ΣO Θ :
  ΣW ≡ₚ ΣO -> not_closing Θ -> lines_ok ΣO ->
  frame_stack ΣW = frame_stack ΣO ->
  (∃ s, s ∈ ΣW ∧ ¬ is_assume s) ->
  is_deduct (ΣW ++ Θ) -> is_deduct (ΣO ++ Θ).
Proof.
  intros Hp Hnc HokO Hstk Hna.
  apply (swap_is_deduct (list_edit_eq _) (list_edit_eq _)); try done.
  - intros ->. by destruct Hnc.
  - rewrite Hstk. apply stack_edit_eq.
  - intros k1 k2 rest -> _. by destruct Hnc.
  - by intros Δ k fW fO s _ [-> _].
Qed.

Lemma indep_deduce_subproof_is_deduct Θ1 Θ2 Θ3 A l1 l2 B j' n :
  not_closing Θ3 -> n ∉ referenced_lines Θ2 ->
  l1 ∉ references_in_just j' -> l2 ∉ references_in_just j' ->
  is_deduct (Θ1 ++ [Deduce B j' n; Raise A l1] ++ Θ2 ++ [ScopeClose l1 l2] ++ Θ3) ->
  is_deduct (Θ1 ++ [Raise A l1] ++ Θ2 ++ [ScopeClose l1 l2; Deduce B j' n] ++ Θ3).
Proof.
  intros Hnc Hn Hl1 _ Hded.
  replace (Θ1 ++ [Deduce B j' n; Raise A l1] ++ Θ2 ++ [ScopeClose l1 l2] ++ Θ3)
    with ((Θ1 ++ Deduce B j' n :: closed_block A l1 Θ2 l2) ++ Θ3) in Hded by list_assoc.
  replace (Θ1 ++ [Raise A l1] ++ Θ2 ++ [ScopeClose l1 l2; Deduce B j' n] ++ Θ3)
    with ((Θ1 ++ closed_block A l1 Θ2 l2 ++ [Deduce B j' n]) ++ Θ3) by list_assoc.
  pose proof Hded as (Hok & _ & Hnd & _).
  destruct (deduce_block_comm Θ1 B j' n A l1 Θ2 l2) as (_ & HokO & Hstk);
    [done|done|by eapply nodup_lines_prefix|left; by eapply prefix_lines_ok|].
  apply (same_stack_is_deduct (Θ1 ++ Deduce B j' n :: closed_block A l1 Θ2 l2)); try done.
  - apply Permutation_app_head, Permutation_cons_append.
  - exists (Deduce B j' n). split; [set_solver|by intros []].
Qed.

Lemma indep_subproof_deduce_is_deduct Θ1 Θ2 Θ3 A l1 l2 B j' n :
  not_closing Θ3 -> n ∉ referenced_lines Θ2 ->
  l1 ∉ references_in_just j' -> l2 ∉ references_in_just j' ->
  is_deduct (Θ1 ++ [Raise A l1] ++ Θ2 ++ [ScopeClose l1 l2; Deduce B j' n] ++ Θ3) ->
  is_deduct (Θ1 ++ [Deduce B j' n; Raise A l1] ++ Θ2 ++ [ScopeClose l1 l2] ++ Θ3).
Proof.
  intros Hnc Hn Hl1 _ Hded.
  replace (Θ1 ++ [Raise A l1] ++ Θ2 ++ [ScopeClose l1 l2; Deduce B j' n] ++ Θ3)
    with ((Θ1 ++ closed_block A l1 Θ2 l2 ++ [Deduce B j' n]) ++ Θ3) in Hded by list_assoc.
  replace (Θ1 ++ [Deduce B j' n; Raise A l1] ++ Θ2 ++ [ScopeClose l1 l2] ++ Θ3)
    with ((Θ1 ++ Deduce B j' n :: closed_block A l1 Θ2 l2) ++ Θ3) by list_assoc.
  pose proof Hded as (Hok & _ & Hnd & _).
  assert (Hp : Θ1 ++ closed_block A l1 Θ2 l2 ++ [Deduce B j' n] ≡ₚ
               Θ1 ++ Deduce B j' n :: closed_block A l1 Θ2 l2).
  { symmetry. apply Permutation_app_head, Permutation_cons_append. }
  destruct (deduce_block_comm Θ1 B j' n A l1 Θ2 l2) as (HokO & _ & Hstk);
    [done|done| |right; by eapply prefix_lines_ok|].
  { rewrite -(lines_of_prededuct_perm _ _ Hp). by eapply nodup_lines_prefix. }
  apply (same_stack_is_deduct (Θ1 ++ closed_block A l1 Θ2 l2 ++ [Deduce B j' n])); try done.
  exists (Deduce B j' n). split; [set_solver|by intros []].
Qed.

Lemma indep_subproof_subproof_is_deduct Θ1 Θ3 Σ1 Σ2 A1 A2 i1 i2 j1 j2 :
  Θ3 ≠ [] ->
  (forall k,
    k ∈ lines_of_prededuct ([Raise A1 i1] ++ Σ1 ++ [ScopeClose i1 j1]) ->
    k ∉ referenced_lines ([Raise A2 i2] ++ Σ2 ++ [ScopeClose i2 j2])) ->
  (forall k,
    k ∈ lines_of_prededuct ([Raise A2 i2] ++ Σ2 ++ [ScopeClose i2 j2]) ->
    k ∉ referenced_lines ([Raise A1 i1] ++ Σ1 ++ [ScopeClose i1 j1])) ->
  is_deduct (Θ1 ++ [Raise A1 i1] ++ Σ1 ++ [ScopeClose i1 j1] ++
             [Raise A2 i2] ++ Σ2 ++ [ScopeClose i2 j2] ++ Θ3) ->
  is_deduct (Θ1 ++ [Raise A2 i2] ++ Σ2 ++ [ScopeClose i2 j2] ++
             [Raise A1 i1] ++ Σ1 ++ [ScopeClose i1 j1] ++ Θ3).
Proof.
  intros HΘ3 H12 _ Hded.
  replace (Θ1 ++ [Raise A1 i1] ++ Σ1 ++ [ScopeClose i1 j1] ++
           [Raise A2 i2] ++ Σ2 ++ [ScopeClose i2 j2] ++ Θ3)
    with ((Θ1 ++ closed_block A1 i1 Σ1 j1 ++ closed_block A2 i2 Σ2 j2) ++ Θ3)
    in Hded by list_assoc.
  replace (Θ1 ++ [Raise A2 i2] ++ Σ2 ++ [ScopeClose i2 j2] ++
           [Raise A1 i1] ++ Σ1 ++ [ScopeClose i1 j1] ++ Θ3)
    with ((Θ1 ++ closed_block A2 i2 Σ2 j2 ++ closed_block A1 i1 Σ1 j1) ++ Θ3)
    by list_assoc.
  pose proof Hded as (Hok & _ & Hnd & _).
  assert (Hp : Θ1 ++ closed_block A1 i1 Σ1 j1 ++ closed_block A2 i2 Σ2 j2 ≡ₚ
               Θ1 ++ closed_block A2 i2 Σ2 j2 ++ closed_block A1 i1 Σ1 j1).
  { apply Permutation_app_head, Permutation_app_comm. }
  apply prefix_lines_ok in Hok as Hok12. apply nodup_lines_prefix in Hnd as Hnd12.
  assert (Hnd21 : NoDup (lines_of_prededuct
            (Θ1 ++ closed_block A2 i2 Σ2 j2 ++ closed_block A1 i1 Σ1 j1)))
    by by rewrite -(lines_of_prededuct_perm _ _ Hp).
  pose proof (nodup_lines_app_prefix _ _ _ Hnd12) as Hnd1.
  pose proof (nodup_lines_app_prefix _ _ _ Hnd21) as Hnd2.
  rewrite app_assoc in Hok12, Hnd12.
  pose proof (prefix_lines_ok _ _ Hok12) as Hok1.
  (* First [B2] alone, then [B1] inserted after it. *)
  assert (Hok2 : lines_ok (Θ1 ++ closed_block A2 i2 Σ2 j2)).
  { eapply proj1, garb_subproof_lines_ok; [done|done|]. apply H12. set_solver. }
  assert (Hok21 : lines_ok (Θ1 ++ closed_block A2 i2 Σ2 j2 ++ closed_block A1 i1 Σ1 j1))
    by by apply garb_subproof_lines_ok_rev.
  apply (swap_is_deduct (list_edit_eq _) (list_edit_swap (λ _, True) _)
           (Θ1 ++ closed_block A1 i1 Σ1 j1 ++ closed_block A2 i2 Σ2 j2)); try done.
  - (* The two closed subproofs are recorded in the other order *)
    destruct (frame_stack_closed_block _ _ _ _ _ Hok1 Hnd1)
      as (fr & rest & g1 & ? & E0 & L1 & E1).
    destruct (frame_stack_closed_block _ _ _ _ _ Hok2 Hnd2)
      as (? & ? & g2 & ? & E0' & L2 & E2).
    destruct (frame_stack_closed_block (Θ1 ++ closed_block A1 i1 Σ1 j1) A2 i2 Σ2 j2)
      as (? & ? & g2' & ? & E1' & L2' & E12); [done..|].
    destruct (frame_stack_closed_block (Θ1 ++ closed_block A2 i2 Σ2 j2) A1 i1 Σ1 j1)
      as (? & ? & g1' & ? & E2' & L1' & E21); [by rewrite -app_assoc..|].
    rewrite app_assoc E12 app_assoc E21.
    rewrite E0 in E0'. rewrite E1 in E1'. rewrite E2 in E2'. simplify_eq.
    apply stack_edit_here. split; [done|].
    eexists _, _, _, []. by rewrite /= -!app_assoc.
  - exists (Raise A1 i1). split; [set_solver|by intros []].
  - intros k1 k2 rest -> [Hlast _]. by rewrite app_assoc closed_block_last in Hlast.
  - intros Δ k fW fO s _ [Hlines _] _ _ Hh. by rewrite -Hlines.
Qed.

(** * Swapping independent statements preserves deductions *)

Lemma indep_step_is_deduct Σ Σ' :
  indep_step Σ Σ' -> is_deduct Σ -> is_deduct Σ'.
Proof.
  destruct 1.
  - by apply indep_deduce_deduce_is_deduct.
  - by apply indep_deduce_subproof_is_deduct.
  - by apply indep_subproof_deduce_is_deduct.
  - by apply indep_subproof_subproof_is_deduct.
Qed.

Lemma indep_is_deduct Σ Σ' :
  indep Σ Σ' -> is_deduct Σ -> is_deduct Σ'.
Proof. induction 1; eauto using indep_step_is_deduct. Qed.

(** Lemmas about (pre)deductions and associated operations *)
From fitch Require Import core.
From fitch Require Import prelude.

(** * Auxiliary definitions *)
(* The formulas of all still-open subproofs' assumptions, innermost
   first, except the outermost (base) frame — whose own [Assume] facts
   are already accounted for by the global premises, not by a separately
   tracked local hypothesis. These are exactly the hypotheses that are
   "currently in force" while still inside those subproofs. *)
Fixpoint local_hyps (stk : list frame) : list frml :=
  match stk with
  | [] => []
  | fr :: rest =>
    match head (frame_lines fr) with
    | Some (h, _) => h :: local_hyps rest
    | None => local_hyps rest
    end
  end.

(* Every frame except possibly the outermost (base) one is non-empty: a
   non-base frame was opened by [Raise], which always puts at least the
   assumption itself into it, and frames only ever grow while open. *)
Fixpoint all_inner_nonempty (stk : list frame) : Prop :=
  match stk with
  | [] => True
  | [_] => True
  | fr :: rest => frame_lines fr <> [] /\ all_inner_nonempty rest
  end.

(* [Assume A l] and [Deduce A j l] are handled identically by [frame_step]:
   both append the pair [(A, l)] to the top frame.  [adds_to_frame s (A, l)]
   captures exactly those two constructors, so proofs that case-split on a
   line can treat them in a single branch (see [frame_step_adds]). *)
Inductive adds_to_frame : line -> frml * id -> Prop :=
| Deduce_adds_to_frame A j l :
  adds_to_frame (Deduce A j l) (A, l)
| Assume_adds_to_frame A l :
  adds_to_frame (Assume A l) (A, l)
.

Lemma adds_to_frame_id s A l :
  adds_to_frame s (A, l) ->
  id_of_line s = Some l.
Proof. by inversion 1. Qed.

(* The defining property: a line that [adds_to_frame s (A, l)] extends the top
   frame with [(A, l)] and leaves everything else untouched, regardless of
   whether it is an [Assume] or a [Deduce]. *)
Lemma frame_step_adds pre stk s A l :
  adds_to_frame s (A, l) ->
  frame_step pre stk s =
    match stk with
    | fr :: rest => mkFrame (frame_lines fr ++ [(A, l)]) (frame_subproofs fr) :: rest
    | [] => []
    end.
Proof. by destruct 1. Qed.

(* The line contributed by an [adds_to_frame] line is its own id. *)
Lemma adds_to_frame_in_lines s A l :
  adds_to_frame s (A, l) -> l ∈ lines_of_prededuct [s].
Proof. inversion 1; simpl; apply list_elem_of_here. Qed.

(* Case analysis on a line that treats the two "append to the top frame"
   constructors ([Assume] and [Deduce]) as a single class, exposed through
   [adds_to_frame].  Meant to be used with [destruct]/[induction ... using]:
   it yields three genuine cases — an [adds_to_frame] line, a [Raise], and a
   [ScopeClose] — instead of four constructors two of which must be merged by
   hand.  In the [adds_to_frame] branch the line stays opaque, so [frame_step]
   is reduced through [frame_step_adds] rather than by computation. *)
Lemma line_case_adds (P : line -> Prop) :
  (forall s A l, adds_to_frame s (A, l) -> P s) ->
  (forall A l, P (Raise A l)) ->
  (forall l1 l2, P (ScopeClose l1 l2)) ->
  forall s, P s.
Proof.
  intros Hadd HR HS s.
  destruct s as [A l|A l|l1 l2|A j l].
  - apply (Hadd _ A l). constructor.
  - apply HR.
  - apply HS.
  - apply (Hadd _ A l). constructor.
Qed.


(** * Auxiliary properties*)

(** Useful induction principle for a relation on predeductions *)

Theorem prededuct_app_length_ind Θ1 Θ2 (P : prededuct -> prededuct -> Prop) :
  (forall Θ1 Θ2,
      (forall Θ1' Θ2',
          length (Θ1' ++ Θ2') < length (Θ1 ++ Θ2) ->
          P Θ1' Θ2') ->
      P Θ1 Θ2) ->
  P Θ1 Θ2.
Proof.
  intros Hstep.
  change (P Θ1 Θ2) with ((fun p => P p.1 p.2) (Θ1, Θ2)).
  apply (induction_ltof1 (prededuct * prededuct) (fun p => length (p.1 ++ p.2))).
  intros [Θ1' Θ2'] IH. apply Hstep. intros Θ1'' Θ2'' Hlt.
  exact (IH (Θ1'', Θ2'') Hlt).
Qed.

Theorem prededuct_strong_ind Σ (P : prededuct -> Prop) :
  (forall Σ, (forall Θ, length Θ < length Σ -> P Θ) -> P Σ) ->
  P Σ.
Proof.
  intros Hstep. exact (induction_ltof1 _ length P Hstep Σ).
Qed.





(** Various projection functions *)

Lemma assumptions_of_app Σ1 Σ2 :
  assumptions_of (Σ1 ++ Σ2) = assumptions_of Σ1 ++ assumptions_of Σ2.
Proof.
  induction Σ1 as [|l Σ1 IH]; [done|].
  destruct l; simpl; rewrite ?IH; done.
Qed.

Lemma lines_of_prededuct_app Σ1 Σ2 :
  lines_of_prededuct (Σ1 ++ Σ2) = lines_of_prededuct Σ1 ++ lines_of_prededuct Σ2.
Proof.
  induction Σ1 as [|l Σ1 IH]; [done|].
  destruct l; simpl; rewrite ?IH; done.
Qed.

(* The ids of the top-level assumptions of Σ, cf. [assumptions_of] *)
Fixpoint assumption_ids (Σ : prededuct) : list id :=
  match Σ with
  | [] => []
  | Assume _ x :: Σ' => x :: assumption_ids Σ'
  | _ :: Σ' => assumption_ids Σ'
  end.

(* Σ without its [Assume] lines *)
Fixpoint drop_assumes (Σ : prededuct) : prededuct :=
  match Σ with
  | [] => []
  | Assume _ _ :: Σ' => drop_assumes Σ'
  | l :: Σ' => l :: drop_assumes Σ'
  end.

Lemma assumption_ids_app Σ1 Σ2 :
  assumption_ids (Σ1 ++ Σ2) = assumption_ids Σ1 ++ assumption_ids Σ2.
Proof. induction Σ1 as [|[] ? IH]; simpl; rewrite ?IH //. Qed.

Lemma drop_assumes_app Σ1 Σ2 :
  drop_assumes (Σ1 ++ Σ2) = drop_assumes Σ1 ++ drop_assumes Σ2.
Proof. induction Σ1 as [|[] ? IH]; simpl; rewrite ?IH //. Qed.

Lemma drop_assumes_sublist Σ :
  lines_of_prededuct (drop_assumes Σ) `sublist_of` lines_of_prededuct Σ.
Proof.
  induction Σ as [|[] Σ IH]; simpl;
    auto using sublist_nil_l, sublist_skip, sublist_cons.
Qed.

Lemma referenced_lines_app Θ1 Θ2 :
  referenced_lines (Θ1 ++ Θ2) = referenced_lines Θ1 ++ referenced_lines Θ2.
Proof.
  induction Θ1 as [|l Θ1 IH]; [done|].
  destruct l; simpl; rewrite ?IH; try done.
  rewrite app_assoc. done.
Qed.

Lemma referenced_lines_elem_of Θ s k :
  s ∈ Θ -> k ∈ references_in_line s -> k ∈ referenced_lines Θ.
Proof. induction Θ; set_solver. Qed.

Lemma lines_of_prededuct_sublist Σ1 Σ2 :
  Σ1 `sublist_of` Σ2 ->
  lines_of_prededuct Σ1 `sublist_of` lines_of_prededuct Σ2.
Proof.
  induction 1 as [|s Σ1 Σ2 Hsub IH|s Σ1 Σ2 Hsub IH].
  - apply sublist_nil.
  - destruct s as [A l|A l|l1 l2|A j l]; simpl.
    + apply sublist_skip. exact IH.
    + apply sublist_skip. exact IH.
    + exact IH.
    + apply sublist_skip. exact IH.
  - destruct s as [A l|A l|l1 l2|A j l]; simpl.
    + apply sublist_cons. exact IH.
    + apply sublist_cons. exact IH.
    + exact IH.
    + apply sublist_cons. exact IH.
Qed.

Lemma referenced_lines_sublist Σ1 Σ2 :
  Σ1 `sublist_of` Σ2 ->
  referenced_lines Σ1 `sublist_of` referenced_lines Σ2.
Proof.
  induction 1 as [|s Σ1 Σ2 Hsub IH|s Σ1 Σ2 Hsub IH].
  - apply sublist_nil.
  - destruct s as [A l|A l|l1 l2|A j l]; simpl;
      repeat apply sublist_skip; auto.
    apply sublist_app; auto.
  - destruct s as [A l|A l|l1 l2|A j l]; simpl;
      repeat apply sublist_skip; auto.
    + repeat apply sublist_cons. exact IH.
    + apply sublist_inserts_l; auto.
Qed.

Lemma lines_of_prededuct_cons_id l pre j :
  id_of_line l = Some j ->
  lines_of_prededuct (l :: pre) = j :: lines_of_prededuct pre.
Proof. destruct l; simpl; intros; congruence. Qed.

Lemma lines_of_prededuct_cons_None l pre :
  id_of_line l = None ->
  lines_of_prededuct (l :: pre) = lines_of_prededuct pre.
Proof. destruct l; simpl; intros; congruence. Qed.

Lemma id_in_lines_of_prededuct pre l j :
  l ∈ pre -> id_of_line l = Some j -> j ∈ lines_of_prededuct pre.
Proof.
  induction pre as [|l' pre IH]; intros Hin Hid.
  - apply elem_of_nil in Hin. done.
  - apply elem_of_cons in Hin as [-> | Hin].
    + destruct l'; simpl in Hid; try congruence; injection Hid as ->; apply list_elem_of_here.
    + destruct l'; simpl.
      * apply list_elem_of_further. exact (IH Hin Hid).
      * apply list_elem_of_further. exact (IH Hin Hid).
      * exact (IH Hin Hid).
      * apply list_elem_of_further. exact (IH Hin Hid).
Qed.

Lemma lines_of_prededuct_elem_of L i :
  i ∈ lines_of_prededuct L -> exists s, s ∈ L /\ id_of_line s = Some i.
Proof.
  induction L as [|s L IH]; intros Hin.
  - simpl in Hin. apply elem_of_nil in Hin. done.
  - destruct (id_of_line s) as [j|] eqn:Hid.
    + rewrite (lines_of_prededuct_cons_id s L j Hid) in Hin.
      apply elem_of_cons in Hin as [->|Hin].
      * exists s. split; [apply elem_of_cons; by left|exact Hid].
      * destruct (IH Hin) as (s' & ? & ?).
        exists s'. split; [apply elem_of_cons; by right|done].
    + rewrite (lines_of_prededuct_cons_None s L Hid) in Hin.
      destruct (IH Hin) as (s' & ? & ?).
      exists s'. split; [apply elem_of_cons; by right|done].
Qed.


Lemma line_at_some_id_in_lines pre i l :
  line_at pre i = Some l ->
  i ∈ lines_of_prededuct pre.
Proof.
  induction pre as [|s pre IH]; intros Hline; [done|].
  simpl in Hline.
  destruct (id_of_line s) as [j|] eqn:Hid.
  - destruct (decide (i = j)) as [->|Hne].
    + erewrite lines_of_prededuct_cons_id; [apply list_elem_of_here|exact Hid].
    + erewrite lines_of_prededuct_cons_id; [apply list_elem_of_further; exact (IH Hline)|exact Hid].
  - erewrite lines_of_prededuct_cons_None; [exact (IH Hline)|exact Hid].
Qed.

Lemma frml_at_some_id_in_lines pre i f :
  frml_at pre i = Some f ->
  i ∈ lines_of_prededuct pre.
Proof.
  unfold frml_at.
  destruct (line_at pre i) as [l|] eqn:Hline; [|done].
  intros _. exact (line_at_some_id_in_lines pre i l Hline).
Qed.


Lemma line_at_app Σ1 Σ2 i :
  line_at (Σ1 ++ Σ2) i =
  match line_at Σ1 i with
  | Some f => Some f
  | None => line_at Σ2 i
  end.
Proof.
  revert Σ2.
  induction Σ1 as [|s Σ1 IH]; intros Σ2; [done|].
  rewrite <- app_comm_cons. simpl.
  destruct (id_of_line s) as [k|]; auto.
  case_decide; auto.
Qed.

(* If an id does not occur in [Σ] then looking it up fails. *)
Lemma line_at_not_in Σ i :
  i ∉ lines_of_prededuct Σ -> line_at Σ i = None.
Proof.
  induction Σ as [|s Σ IH]; [done|]; intros Hni.
  destruct s as [f l|f l|l1 l2|f j l]; simpl in *;
    try (case_decide; [set_solver|]); apply IH; set_solver.
Qed.


Lemma frml_at_of_line pre i f :
  (exists l, l ∈ pre /\ id_of_line l = Some i /\ frml_of_line l = Some f) ->
  NoDup (lines_of_prededuct pre) ->
  frml_at pre i = Some f.
Proof.
  induction pre as [|l pre IH]; intros [l0 [Hin [Hid Hfrm]]] Hnodup.
  - apply elem_of_nil in Hin. done.
  - apply elem_of_cons in Hin as [-> | Hin].
    + unfold frml_at. simpl. rewrite Hid. by rewrite decide_True.
    + simpl.
      unfold frml_at; simpl.
      destruct (id_of_line l) as [j|] eqn:Hjl.
      * pose proof (lines_of_prededuct_cons_id l pre j Hjl) as Hcons.
        rewrite Hcons in Hnodup.
        rewrite decide_False.
        ** apply IH; [|by apply NoDup_cons_1_2 in Hnodup].
           exists l0. exact (conj Hin (conj Hid Hfrm)).
        ** intro Heq. subst.
           exact (NoDup_cons_1_1 _ _ Hnodup (id_in_lines_of_prededuct pre l0 j Hin Hid)).
      * apply IH; [|destruct l; simpl in Hjl; try congruence; simpl in Hnodup; exact Hnodup].
        exists l0. exact (conj Hin (conj Hid Hfrm)).
Qed.

(** Monotonicity of [frml_at] under appending lines. *)
Lemma frml_at_app_l Σ1 Σ2 i f :
  frml_at Σ1 i = Some f -> frml_at (Σ1 ++ Σ2) i = Some f.
Proof.
  unfold frml_at. rewrite line_at_app.
  destruct (line_at Σ1 i) as [ln|]; simpl; [done|discriminate].
Qed.


(** Every id occurring in [Σ] is resolved by [line_at]. *)
Lemma line_at_isSome Σ l :
  l ∈ lines_of_prededuct Σ -> is_Some (line_at Σ l).
Proof.
  induction Σ as [|s Σ' IH].
  { intros ?%elem_of_nil; done. }
  intros Hin.
  destruct (id_of_line s) as [j|] eqn:Hid.
  - rewrite (lines_of_prededuct_cons_id s Σ' j Hid) in Hin.
    cbn [line_at]. rewrite Hid.
    case_decide as Hlj; [done|].
    rewrite elem_of_cons in Hin. destruct Hin as [->|Hin]; [done|]. by apply IH.
  - assert (lines_of_prededuct (s :: Σ') = lines_of_prededuct Σ') as Hls
      by (destruct s; simpl in Hid; done).
    rewrite Hls in Hin. cbn [line_at]. rewrite Hid. by apply IH.
Qed.

Lemma frml_at_isSome Σ i :
  i ∈ lines_of_prededuct Σ -> is_Some (frml_at Σ i).
Proof.
  rewrite /frml_at. induction Σ as [|[] Σ IH]; simpl;
    rewrite ?elem_of_cons; intros Hi; [set_solver| | | |];
    try case_decide; naive_solver.
Qed.

Lemma line_at_Some_inv Σ k s :
  line_at Σ k = Some s -> s ∈ Σ ∧ id_of_line s = Some k.
Proof.
  induction Σ as [|s' Σ IH]; simpl; [done|].
  destruct (id_of_line s') eqn:?; [case_decide|]; set_solver.
Qed.

(* With unique ids, [line_at] finds every line by its id. *)
Lemma line_at_NoDup_elem_of Σ k s :
  NoDup (lines_of_prededuct Σ) -> s ∈ Σ -> id_of_line s = Some k ->
  line_at Σ k = Some s.
Proof.
  induction Σ as [|s' Σ IH]; intros Hnd Hs Hid; [set_solver|]. simpl.
  apply elem_of_cons in Hs as [<- | Hs].
  - by rewrite Hid decide_True.
  - destruct (id_of_line s') as [j|] eqn:Hj.
    + rewrite (lines_of_prededuct_cons_id _ _ _ Hj) in Hnd.
      apply NoDup_cons in Hnd as [Hj' Hnd].
      rewrite decide_False; [by apply IH|].
      intros ->. apply Hj'. by eapply id_in_lines_of_prededuct.
    + rewrite (lines_of_prededuct_cons_None _ _ Hj) in Hnd. by apply IH.
Qed.

(* A [Raise] and a [Deduce] cannot share an id. *)
Lemma NoDup_raise_deduce Σ A B j k :
  NoDup (lines_of_prededuct Σ) -> Raise A k ∈ Σ -> Deduce B j k ∈ Σ -> False.
Proof.
  intros Hnd H1 H2.
  pose proof (line_at_NoDup_elem_of _ k _ Hnd H1 eq_refl).
  pose proof (line_at_NoDup_elem_of _ k _ Hnd H2 eq_refl). congruence.
Qed.

Lemma line_at_app_mid X B Y k :
  k ∉ lines_of_prededuct B -> line_at (X ++ B ++ Y) k = line_at (X ++ Y) k.
Proof. intros Hk. by rewrite !line_at_app (line_at_not_in B). Qed.

(** Permuting the lines of a prededuction *)

Lemma lines_of_prededuct_omap Σ : lines_of_prededuct Σ = omap id_of_line Σ.
Proof. induction Σ as [|[] Σ IH]; by f_equal/=. Qed.

Lemma lines_of_prededuct_perm Σ Σ' :
  Σ ≡ₚ Σ' -> lines_of_prededuct Σ ≡ₚ lines_of_prededuct Σ'.
Proof. rewrite !lines_of_prededuct_omap. by intros ->. Qed.

(* With unique ids, [line_at] does not see the order of the lines. *)
Lemma line_at_perm Σ Σ' k :
  Σ ≡ₚ Σ' -> NoDup (lines_of_prededuct Σ) -> line_at Σ k = line_at Σ' k.
Proof.
  intros Hp Hnd.
  assert (Hnd' : NoDup (lines_of_prededuct Σ')) by by rewrite -(lines_of_prededuct_perm _ _ Hp).
  destruct (line_at Σ k) as [s|] eqn:Hs.
  - destruct (line_at_Some_inv _ _ _ Hs) as [Hin Hid].
    symmetry. apply line_at_NoDup_elem_of; [done|by rewrite -Hp|done].
  - destruct (line_at Σ' k) as [s|] eqn:Hs'; [|done].
    destruct (line_at_Some_inv _ _ _ Hs') as [Hin Hid].
    rewrite (line_at_NoDup_elem_of Σ k s) in Hs; [done|done|by rewrite Hp|done].
Qed.

(** Restriction properties *)
Lemma restr_app_r Θ1 Θ2 l:
  l ∉ lines_of_prededuct Θ1 ->
  restr (Θ1 ++ Θ2) l = Θ1 ++ (restr Θ2 l).
Proof.
  induction Θ1 as [|s Θ1 IH].
  { intros _. reflexivity. }
  intros Hl.
  simpl.
  destruct (id_of_line s) as [i | ] eqn:Hids.
  - erewrite lines_of_prededuct_cons_id in Hl; eauto.
    rewrite not_elem_of_cons in Hl. destruct Hl as [Hne Hl].
    rewrite decide_False; [|congruence].
    f_equiv. by apply IH.
  - erewrite lines_of_prededuct_cons_None in Hl; eauto.
    f_equiv. by apply IH.
Qed.

Lemma restr_app_l Θ1 Θ2 l:
  l ∈ lines_of_prededuct Θ1 ->
  restr (Θ1 ++ Θ2) l = restr Θ1 l.
Proof.
  induction Θ1 as [|s Θ1 IH].
  { intros ?. exfalso. simpl in H.
    eapply elem_of_nil; eauto. }
  intros Hl.
  simpl.
  destruct (id_of_line s) as [i | ] eqn:Hids.
  - erewrite lines_of_prededuct_cons_id in Hl ; eauto.
    apply elem_of_cons in Hl.
    destruct Hl as [-> | Hl].
    + rewrite !decide_True//.
    + case_decide; eauto.
      f_equiv. by apply IH.
  - erewrite lines_of_prededuct_cons_None in Hl ; eauto.
    f_equiv. by apply IH.
Qed.


Lemma last_restr Σ l :
  l ∈ lines_of_prededuct Σ -> last (restr Σ l) = line_at Σ l.
Proof.
  induction Σ as [|s Σ' IH].
  { intros ?%elem_of_nil; done. }
  intros Hin.
  destruct (id_of_line s) as [j|] eqn:Hid.
  - rewrite (lines_of_prededuct_cons_id s Σ' j Hid) in Hin.
    cbn [restr line_at]. rewrite Hid.
    case_decide as Hlj.
    + by rewrite last_singleton.
    + rewrite elem_of_cons in Hin. destruct Hin as [->|Hin]; [done|].
      rewrite last_cons (IH Hin).
      destruct (line_at_isSome Σ' l Hin) as [ln ->]. done.
  - assert (lines_of_prededuct (s :: Σ') = lines_of_prededuct Σ') as Hls
      by (destruct s; simpl in Hid; done).
    rewrite Hls in Hin.
    cbn [restr line_at]. rewrite Hid.
    rewrite last_cons (IH Hin).
    destruct (line_at_isSome Σ' l Hin) as [ln ->]. done.
Qed.

Lemma restr_snoc Σ s i :
  NoDup (lines_of_prededuct (Σ ++ [s])) ->
  id_of_line s = Some i ->
  restr (Σ ++ [s]) i = Σ ++ [s].
Proof.
  intros Hnd Hid.
  rewrite restr_app_r.
  - simpl. rewrite Hid. rewrite decide_True; [reflexivity|done].
  - rewrite lines_of_prededuct_app in Hnd.
    apply NoDup_app in Hnd as (_ & Hfresh & _).
    intros Hin.
    apply (Hfresh i Hin).
    destruct s as [A j|A j|j k|A js j]; simpl in Hid; try discriminate;
      injection Hid as ->; apply list_elem_of_here.
Qed.

(** Restricting at a freshly appended identifier retains the entire
    extended prededuction. *)
Lemma restr_snoc_notin Σ s i :
  i ∉ lines_of_prededuct Σ ->
  id_of_line s = Some i ->
  restr (Σ ++ [s]) i = Σ ++ [s].
Proof.
  intros Hnin Hid.
  rewrite restr_app_r; [|assumption].
  simpl. rewrite Hid.
  rewrite decide_True; [reflexivity|done].
Qed.

(** Under unique line identifiers, restricting at the identifier of a line
    ends exactly at that line. *)
Lemma restr_elem_of {Σ s l} :
  NoDup (lines_of_prededuct Σ) ->
  s ∈ Σ ->
  id_of_line s = Some l ->
  ∃ Σ0, restr Σ l = Σ0 ++ [s] /\
          l ∉ lines_of_prededuct Σ0.
Proof.
  intros Hnd Hs Hsid.
  apply list_elem_of_split in Hs as (pre & rest & ->).
  assert (Hfresh : l ∉ lines_of_prededuct pre).
  { rewrite !lines_of_prededuct_app in Hnd. simpl in Hnd.
    apply NoDup_app in Hnd as (_ & Hdisj & _).
    intros Hl. apply (Hdisj l Hl).
    change (l ∈ lines_of_prededuct (s :: rest)).
    eapply id_in_lines_of_prededuct.
    - apply elem_of_cons. by left.
    - apply Hsid. }
  exists pre. split; [|apply Hfresh].
  rewrite restr_app_r; [|apply Hfresh].
  cbn [restr]. rewrite Hsid decide_True //.
Qed.

Lemma restr_not_nil Σ l :
  Σ ≠ [] → restr Σ l ≠ [].
Proof.
  induction Σ; first done; intros _; simpl.
  case_match; try case_decide; eauto.
Qed.

Lemma restr_prefix Σ l : ∃ Σ', Σ = restr Σ l ++ Σ'.
Proof.
  induction Σ as [|s Σ IH]; [by exists []|].
  simpl. destruct (id_of_line s) as [j|].
  - case_decide.
    + by exists Σ.
    + destruct IH as [Σ' HΣ']. exists Σ'. simpl. by rewrite <- HΣ'.
  - destruct IH as [Σ' HΣ']. exists Σ'. simpl. by rewrite <- HΣ'.
Qed.

Lemma restr_sublist Σ l :
  restr Σ l `sublist_of` Σ.
Proof.
  destruct (restr_prefix Σ l) as [Σ' HΣ'].
  assert (Hrefl : forall xs : prededuct, xs `sublist_of` xs).
  { induction xs as [|s xs IH]; [apply sublist_nil|].
    apply sublist_skip. exact IH. }
  assert (Hsub : restr Σ l `sublist_of` restr Σ l ++ Σ').
  { apply sublist_inserts_r. apply Hrefl. }
  rewrite <- HΣ' in Hsub.
  exact Hsub.
Qed.


Lemma referenced_lines_restr_subset Σ l l1 :
  l1 ∈ referenced_lines (restr Σ l) -> l1 ∈ referenced_lines Σ.
Proof.
  intros Hin.
  destruct (restr_prefix Σ l) as [Σ' HΣ'].
  rewrite HΣ' referenced_lines_app. apply elem_of_app. by left.
Qed.



(** Frame and stack lemmas *)

Lemma frame_stack_go_app pre stk Σ1 Σ2 :
  frame_stack_go pre stk (Σ1 ++ Σ2) =
  frame_stack_go (pre ++ Σ1) (frame_stack_go pre stk Σ1) Σ2.
Proof.
  induction Σ1 as [|s Σ1' IH] in pre, stk |-*; simpl.
  - rewrite app_nil_r. reflexivity.
  - rewrite (IH (pre ++ [s]) (frame_step pre stk s)).
    rewrite <- app_assoc. done.
Qed.

(* The frame stack of a concatenation: process [Σ1] from the base, then
   continue with [Σ2] on top of the resulting stack. *)
Lemma frame_stack_app Σ1 Σ2 :
  frame_stack (Σ1 ++ Σ2) = frame_stack_go Σ1 (frame_stack Σ1) Σ2.
Proof.
  unfold frame_stack. rewrite frame_stack_go_app. by rewrite app_nil_l.
Qed.

Lemma frame_stack_snoc pre l :
  frame_stack (pre ++ [l]) = frame_step pre (frame_stack pre) l.
Proof.
  unfold frame_stack. rewrite frame_stack_go_app. rewrite app_nil_l. simpl. reflexivity.
Qed.

(* The frame stack always has at least the base frame on it. *)
Lemma frame_stack_nonempty pre : frame_stack pre <> [].
Proof.
  induction pre as [|l pre IH] using rev_ind; [done|].
  rewrite frame_stack_snoc.
  destruct (frame_stack pre) as [|fr rest] eqn:Hstk; [done|].
  destruct l as [f i|f i|i1 i2|f j i]; simpl; try done.
  destruct rest as [|fr' rest']; simpl; [done|].
  destruct (frml_at pre i1) as [f1|], (frml_at pre i2) as [f2|]; done.
Qed.

Lemma frame_stack_snoc_raise pre A l :
  frame_stack (pre ++ [Raise A l]) = mkFrame [(A, l)] [] :: frame_stack pre.
Proof. by rewrite frame_stack_snoc. Qed.

Lemma frame_stack_snoc_deduce pre A j l :
  ∃ fr rest, frame_stack pre = fr :: rest ∧
    frame_stack (pre ++ [Deduce A j l]) =
      mkFrame (frame_lines fr ++ [(A, l)]) (frame_subproofs fr) :: rest.
Proof.
  rewrite frame_stack_snoc.
  destruct (frame_stack pre) eqn:E; [by destruct (frame_stack_nonempty pre)|]. by eexists _, _.
Qed.


Lemma frame_stack_all_inner_nonempty pre : all_inner_nonempty (frame_stack pre).
Proof.
  induction pre as [|l pre IH] using rev_ind; [done|].
  rewrite frame_stack_snoc.
  pose proof (frame_stack_nonempty pre) as Hne.
  destruct (frame_stack pre) as [|fr rest] eqn:Hstk; [done|]. clear Hne.
  induction l as [s A a Hadds| f l' | i1 i2] using line_case_adds.
  - (* adds-to-frame: append to the top frame *)
    rewrite (frame_step_adds pre (fr :: rest) s A a Hadds).
    destruct rest as [|fr' rest']; [done|].
    destruct IH as [_ IH']. split; [|exact IH']. simpl. by destruct (frame_lines fr).
  - (* Raise *)
    simpl. split; [done|]. destruct rest as [|fr0 rest0]; [done|exact IH].
  - (* ScopeClose i1 i2 *)
    simpl. destruct rest as [|fr' rest']; [done|].
    destruct (frml_at pre i1) as [f1|], (frml_at pre i2) as [f2|]; simpl; try exact IH.
    destruct rest' as [|fr'' rest'']; [done|].
    split; [exact (proj1 (proj2 IH)) | exact (proj2 (proj2 IH))].
Qed.

(* A run of nothing but [Assume]s never opens a subproof: the frame stack
   stays a single (base) frame throughout. *)
Lemma assume_run_stack pre :
  Forall is_assume pre -> ∃ base, frame_stack pre = [base].
Proof.
  induction pre as [|l pre IH] using rev_ind; intros Hpre.
  - exists (mkFrame [] []). done.
  - apply Forall_app in Hpre as [Hpre Hl].
    rewrite Forall_singleton in Hl.
    destruct (IH Hpre) as [base Hbase].
    rewrite frame_stack_snoc Hbase.
    destruct l; simpl in Hl; try done.
    eexists; reflexivity.
Qed.

(* scope *)

Lemma frame_lines_in_pre pre f i :
  (f, i) ∈ scope pre ->
  exists l, l ∈ pre /\ id_of_line l = Some i /\ frml_of_line l = Some f.
Proof.
  induction pre as [|l pre IH] using rev_ind.
  - simpl. intro H. apply elem_of_nil in H. done.
  - unfold scope. rewrite frame_stack_snoc.
    pose proof (frame_stack_nonempty pre) as Hne.
    destruct (frame_stack pre) as [|fr rest] eqn:Hstk; [done|].
    intro Hin.
    assert (lift : forall l0, l0 ∈ pre -> l0 ∈ pre ++ [l]).
    { intros l0 Hl0. apply elem_of_app. left. exact Hl0. }
    assert (use_IH : forall Hc : (f, i) ∈ concat (map frame_lines (fr :: rest)),
      exists l0, l0 ∈ pre ++ [l] /\ id_of_line l0 = Some i /\ frml_of_line l0 = Some f).
    { intros Hc.
      rewrite -Hstk in Hc.
      destruct (IH Hc) as [l0 [Hl0 [Hid0 Hfrm0]]].
      exists l0. exact (conj (lift l0 Hl0) (conj Hid0 Hfrm0)). }
    destruct l as [f0 i0 | f0 i0 | i1 i2 | f0 j0 i0]; simpl in Hin.
    + apply elem_of_app in Hin as [Hin | Hin].
      * apply elem_of_app in Hin as [Hin | Hin].
        ** apply use_IH. simpl. apply elem_of_app. left. exact Hin.
        ** apply list_elem_of_singleton in Hin. injection Hin as -> ->.
           exists (Assume f0 i0). split; [apply elem_of_app; right; apply list_elem_of_here|].
           split; reflexivity.
      * apply use_IH. simpl. apply elem_of_app. right. exact Hin.
    + apply elem_of_cons in Hin as [Hin | Hin].
      * injection Hin as -> ->.
        exists (Raise f0 i0). split; [apply elem_of_app; right; apply list_elem_of_here|].
        split; reflexivity.
      * apply use_IH. simpl. exact Hin.
    + destruct rest as [|fr2 rest2].
      * simpl in Hin. rewrite app_nil_r in Hin.
        apply use_IH. simpl. rewrite app_nil_r. exact Hin.
      * destruct (frml_at pre i1) as [fa|] eqn:Hi1.
        ** destruct (frml_at pre i2) as [fb|] eqn:Hi2.
           *** simpl in Hin.
               apply use_IH. simpl. apply elem_of_app. right. exact Hin.
           *** apply use_IH. exact Hin.
        ** apply use_IH. exact Hin.
    + apply elem_of_app in Hin as [Hin | Hin].
      * apply elem_of_app in Hin as [Hin | Hin].
        ** apply use_IH. simpl. apply elem_of_app. left. exact Hin.
        ** apply list_elem_of_singleton in Hin. injection Hin as -> ->.
           exists (Deduce f0 j0 i0). split; [apply elem_of_app; right; apply list_elem_of_here|].
           split; reflexivity.
      * apply use_IH. simpl. apply elem_of_app. right. exact Hin.
Qed.


Lemma frml_at_frame_lines pre f i :
  (f, i) ∈ scope pre ->
  NoDup (lines_of_prededuct pre) ->
  frml_at pre i = Some f.
Proof.
  intros Hin Hnodup.
  apply frml_at_of_line; [|exact Hnodup].
  exact (frame_lines_in_pre pre f i Hin).
Qed.

(** An [sp_scope] entry records the formulas at the lines it pairs (the
    [frml_at] strengthening of [sp_scope_id_in_lines]). *)
Lemma sp_scope_frml_at pre f1 f2 i j :
  SubProof f1 i f2 j ∈ sp_scope pre ->
  frml_at pre i = Some f1 /\ frml_at pre j = Some f2.
Proof.
  revert f1 f2 i j.
  induction pre as [|l pre IH] using rev_ind; intros f1 f2 i j.
  - unfold sp_scope. simpl. intros Hin. apply elem_of_nil in Hin. done.
  - unfold sp_scope in *. rewrite frame_stack_snoc.
    pose proof (frame_stack_nonempty pre) as Hne.
    destruct (frame_stack pre) as [|fr rest] eqn:Hstk; [done|].
    intros Hin.
    assert (old_ids : forall q,
      q ∈ concat (map frame_subproofs (fr :: rest)) ->
      match q with SubProof g1 i0 g2 j0 =>
        frml_at (pre ++ [l]) i0 = Some g1 /\
        frml_at (pre ++ [l]) j0 = Some g2
      end).
    { intros [g1 i0 g2 j0] Hq.
      destruct (IH g1 g2 i0 j0 Hq) as [Hi Hj].
      split; by apply frml_at_app_l. }
    destruct l as [A k|A k|k1 k2|A js k]; simpl in Hin.
    + exact (old_ids _ Hin).
    + exact (old_ids _ Hin).
    + destruct rest as [|fr2 rest2].
      * exact (old_ids _ Hin).
      * destruct (frml_at pre k1) as [g1|] eqn:Hk1;
        destruct (frml_at pre k2) as [g2|] eqn:Hk2; simpl in Hin;
        try exact (old_ids _ Hin).
        apply elem_of_app in Hin as [Hin|Hin].
        ** apply elem_of_app in Hin as [Hin|Hin].
           *** refine (old_ids (SubProof f1 i f2 j) _).
               simpl. apply elem_of_app. right.
               apply elem_of_app. left. exact Hin.
           *** apply list_elem_of_singleton in Hin. injection Hin as -> -> -> ->.
               split; by apply frml_at_app_l.
        ** refine (old_ids (SubProof f1 i f2 j) _).
           simpl. apply elem_of_app. right.
           apply elem_of_app. right. exact Hin.
    + exact (old_ids _ Hin).
Qed.


(* The conclusion of a deduction is always actually in its final scope —
   connecting [conclusion_of], which only looks at the last line, with
   [scope], which is built up via the frame stack. *)
Lemma conclusion_in_scope Σ f :
  length (frame_stack Σ) = 1 ->
  conclusion_of Σ = Some f ->
  ∃ l, (f, l) ∈ scope Σ.
Proof.
  intros Hlen Hconcl.
  unfold conclusion_of in Hconcl.
  destruct (last Σ) as [ln|] eqn:Hlast; [|done].
  apply last_Some in Hlast as [pre ->].
  rewrite frame_stack_snoc in Hlen.
  unfold scope. rewrite frame_stack_snoc.
  destruct ln as [f0 l0|f0 l0|l1 l2|f0 j0 l0]; simpl in Hconcl; try done.
  injection Hconcl as ->.
  destruct (frame_stack pre) as [|fr rest]; simpl in Hlen; [done|].
  destruct rest; simpl in Hlen; [|done].
  exists l0. simpl. rewrite app_nil_r. apply elem_of_app; right; apply list_elem_of_singleton; done.
Qed.

Lemma restr_frml_at_snoc Σ i A :
  frml_at Σ i = Some A ->
  exists Σ0 s,
    restr Σ i = Σ0 ++ [s] /\
    id_of_line s = Some i /\
    frml_of_line s = Some A.
Proof.
  induction Σ as [|s Σ' IH]; simpl.
  - unfold frml_at. simpl. done.
  - unfold frml_at. simpl.
    destruct (id_of_line s) as [j|] eqn:Hids.
    + case_decide as Hij; simpl.
      * intros Hfrm. subst j. exists [], s. split; [reflexivity|].
        split; [exact Hids|exact Hfrm].
      * intros Hfrm.
        destruct (IH Hfrm) as (Σ0 & s0 & Hrestr & Hid0 & Hfrm0).
        exists (s :: Σ0), s0. split; [by rewrite Hrestr|].
        split; [exact Hid0|exact Hfrm0].
    + intros Hfrm.
      destruct (IH Hfrm) as (Σ0 & s0 & Hrestr & Hid0 & Hfrm0).
      exists (s :: Σ0), s0. split; [by rewrite Hrestr|].
      split; [exact Hid0|exact Hfrm0].
Qed.

Lemma scope_restr_snoc A i Σ :
  NoDup (lines_of_prededuct Σ) ->
  (A, i) ∈ scope Σ ->
  exists Σ0 s, restr Σ i = Σ0 ++ [s] ∧ frml_of_line s = Some A.
Proof.
  intros Hnd Hin.
  pose proof (frml_at_frame_lines Σ A i Hin Hnd) as Hfrml.
  destruct (restr_frml_at_snoc Σ i A Hfrml) as (Σ0 & s & Hrestr & _ & Hfrm).
  exists Σ0, s. split; [exact Hrestr|exact Hfrm].
Qed.


(* ========================================================================= *)
(* "Fresh ids never become frame heads": machinery for the subproof balance
   lemma.  [no_head i stk] means no frame in [stk] has [i] as the id of its
   first line. *)

(* One step preserves [no_head i], provided the line's own id is not [i]. *)
Lemma frame_step_no_head pre stk s i :
  (forall l, id_of_line s = Some l -> l <> i) ->
  Forall (fun fr => option_map snd (head (frame_lines fr)) <> Some i) stk ->
  Forall (fun fr => option_map snd (head (frame_lines fr)) <> Some i) (frame_step pre stk s).
Proof.
  intros Hid Hstk.
  induction s as [s A l Hadds| A l | l1 l2] using line_case_adds.
  - (* adds-to-frame: append to the top frame *)
    rewrite (frame_step_adds pre stk s A l Hadds).
    destruct stk as [|fr rest]; [exact Hstk|].
    apply Forall_cons in Hstk as [Hfr Hrest].
    constructor; [|exact Hrest].
    destruct (frame_lines fr) as [|y ys]; simpl in *.
    + intros [= Heq]. apply (Hid l (adds_to_frame_id _ _ _ Hadds)). exact Heq.
    + exact Hfr.
  - (* Raise: push a fresh frame *)
    simpl. constructor; [|exact Hstk].
    simpl. intros [= Heq]. apply (Hid l eq_refl). exact Heq.
  - (* ScopeClose: pop the top, promote the second *)
    simpl. destruct stk as [|f1 [|f2 rest]]; try exact Hstk.
    apply Forall_cons in Hstk as [Hf1 Hstk2].
    apply Forall_cons in Hstk2 as [Hf2 Hrest].
    destruct (frml_at pre l1) as [g1|], (frml_at pre l2) as [g2|];
      try (constructor; [exact Hf1| constructor; [exact Hf2|exact Hrest]]).
    constructor; [exact Hf2|exact Hrest].
Qed.

(* Running a suffix [Δ] that does not mention [i] preserves [no_head i]. *)
Lemma frame_stack_go_no_head Δ pre stk i :
  i ∉ lines_of_prededuct Δ ->
  Forall (fun fr => option_map snd (head (frame_lines fr)) <> Some i) stk ->
  Forall (fun fr => option_map snd (head (frame_lines fr)) <> Some i) (frame_stack_go pre stk Δ).
Proof.
  revert pre stk. induction Δ as [|s Δ IH]; intros pre stk Hni Hstk; simpl.
  - exact Hstk.
  - apply IH.
    + intro Hc. apply Hni. destruct s; simpl; try (apply elem_of_cons; by right); exact Hc.
    + apply frame_step_no_head; [|exact Hstk].
      intros l Hidl Heq. subst l. apply Hni.
      destruct s; simpl in Hidl; inversion Hidl; subst; simpl; apply elem_of_cons; by left.
Qed.

(* The frame stack of [Θ] has no frame headed by an id not in [Θ]. *)
Lemma frame_stack_no_head Θ i :
  i ∉ lines_of_prededuct Θ ->
  Forall (fun fr => option_map snd (head (frame_lines fr)) <> Some i) (frame_stack Θ).
Proof.
  intros Hni. unfold frame_stack.
  apply frame_stack_go_no_head; [exact Hni|].
  constructor; [|constructor]. simpl. discriminate.
Qed.

(* The disjunctive invariant for a [Raise A l1] followed by [Θ2]: either the
   raised frame survived (and everything below it is exactly [frame_stack Θ1]),
   or it was closed and no frame has head [l1].  The final matching
   [ScopeClose] later rules out the second disjunct. *)
Lemma block_invariant Θ1 A l1 Θ2 :
  l1 ∉ lines_of_prededuct Θ1 ->
  l1 ∉ lines_of_prededuct Θ2 ->
  (exists upper G',
     frame_stack (Θ1 ++ Raise A l1 :: Θ2) = upper ++ G' :: frame_stack Θ1 /\
     Forall (fun fr => option_map snd (head (frame_lines fr)) <> Some l1) upper /\
     option_map snd (head (frame_lines G')) = Some l1)
  \/ Forall (fun fr => option_map snd (head (frame_lines fr)) <> Some l1)
            (frame_stack (Θ1 ++ Raise A l1 :: Θ2)).
Proof.
  intros HΘ1.
  induction Θ2 as [|s Θ2' IH] using rev_ind; intros HΘ2.
  - (* base: just the raised frame on top of [frame_stack Θ1] *)
    left. exists [], (mkFrame [(A, l1)] []).
    rewrite frame_stack_snoc. simpl.
    split; [reflexivity | split; [constructor | reflexivity]].
  - assert (HΘ2' : l1 ∉ lines_of_prededuct Θ2').
    { rewrite lines_of_prededuct_app in HΘ2. set_solver. }
    assert (Hmne : forall m, id_of_line s = Some m -> m <> l1).
    { intros m Hm Heq. subst m. apply HΘ2. rewrite lines_of_prededuct_app.
      apply elem_of_app. right.
      destruct s; simpl in Hm |- *; inversion Hm; subst; apply elem_of_cons; by left. }
    assert (Hre : Θ1 ++ Raise A l1 :: Θ2' ++ [s] = (Θ1 ++ Raise A l1 :: Θ2') ++ [s]).
    { change (Raise A l1 :: Θ2' ++ [s]) with ([Raise A l1] ++ Θ2' ++ [s]).
      change (Raise A l1 :: Θ2') with ([Raise A l1] ++ Θ2'). by rewrite -!app_assoc. }
    rewrite Hre frame_stack_snoc. clear Hre.
    specialize (IH HΘ2').
    pose proof (frame_stack_nonempty (Θ1 ++ Raise A l1 :: Θ2')) as Hne.
    pose proof (frame_stack_no_head Θ1 l1 HΘ1) as Hnh.
    induction s as [s B m Hadds| B m | a b] using line_case_adds.
    { (* adds-to-frame: append [(B, m)] to the top frame *)
      assert (Hm : m <> l1) by (apply (Hmne m); exact (adds_to_frame_id _ _ _ Hadds)).
      rewrite (frame_step_adds _ _ _ B m Hadds).
      destruct IH as [(upper & G' & Heq & Hupper & HG')| Hright].
      - rewrite Heq. destruct upper as [|u upper''].
        + simpl.
          left. exists [], (mkFrame (frame_lines G' ++ [(B, m)]) (frame_subproofs G')).
          split; [reflexivity|]. split; [constructor|].
          simpl. destruct (frame_lines G') as [|y ys]; simpl in HG' |- *;
            [discriminate HG' | exact HG'].
        + simpl.
          left. exists (mkFrame (frame_lines u ++ [(B, m)]) (frame_subproofs u) :: upper''), G'.
          split; [reflexivity|]. split; [|exact HG'].
          apply Forall_cons in Hupper as [Hu Hupper''].
          constructor; [|exact Hupper'']. simpl.
          destruct (frame_lines u) as [|y ys]; simpl in Hu |- *;
            [intros [= H]; exact (Hm H) | exact Hu].
      - destruct (frame_stack (Θ1 ++ Raise A l1 :: Θ2')) as [|fr rest] eqn:HFS; [done|].
        simpl. apply Forall_cons in Hright as [Hfr Hrest].
        right. constructor; [|exact Hrest]. simpl.
        destruct (frame_lines fr) as [|y ys]; simpl in Hfr |- *;
          [intros [= H]; exact (Hm H) | exact Hfr]. }
    { (* Raise: push a fresh frame *)
      assert (Hm : m <> l1) by (apply (Hmne m); reflexivity).
      simpl.
      destruct IH as [(upper & G' & Heq & Hupper & HG')| Hright].
      - left. exists (mkFrame [(B, m)] [] :: upper), G'.
        rewrite Heq. split; [reflexivity|].
        split; [|exact HG']. constructor; [|exact Hupper].
        simpl. intros [= H]. exact (Hm H).
      - right. constructor; [simpl; intros [= H]; exact (Hm H) | exact Hright]. }
    { (* ScopeClose: pop the top, promote the second *)
      destruct (frame_stack (Θ1 ++ Raise A l1 :: Θ2')) as [|f1 [|f2 rest]] eqn:HFS.
      - done.
      - simpl. exact IH.
      - destruct (frml_at (Θ1 ++ Raise A l1 :: Θ2') a) as [g1|] eqn:Ha;
        destruct (frml_at (Θ1 ++ Raise A l1 :: Θ2') b) as [g2|] eqn:Hb; simpl; try exact IH.
        2:{ rewrite Ha Hb. exact IH. }
        2:{ rewrite Ha. exact IH. }
        2:{ rewrite Ha. exact IH. }
        rewrite Ha Hb.
        destruct IH as [(upper & G' & Heq & Hupper & HG')| Hright].
        2:{ apply Forall_cons in Hright as [Hf1 Hrest1].
            apply Forall_cons in Hrest1 as [Hf2 Hrest].
            right. constructor; [exact Hf2 | exact Hrest]. }
        destruct upper as [|u [|u1 upper'']].
        1:{ (* upper empty: the raised frame is popped -> RIGHT disjunct *)
            injection Heq as Hf1 Hfr.
            right. rewrite <- Hfr in Hnh. apply Forall_cons in Hnh as [Hf2 Hrest].
            constructor; [exact Hf2 | exact Hrest]. }
        1:{ (* upper = [u]: the raised frame is promoted, stays head l1 *)
            injection Heq as Hf1 Heq2.
            left. exists [], (mkFrame (frame_lines f2) (frame_subproofs f2 ++ [SubProof g1 a g2 b])).
            subst rest. split; [reflexivity|]. split; [constructor|].
            simpl. rewrite Heq2. exact HG'. }
        injection Heq as Hf1 Hf2 Hrest.
        left. exists (mkFrame (frame_lines f2) (frame_subproofs f2 ++ [SubProof g1 a g2 b]) :: upper''), G'.
        subst rest. split; [reflexivity|]. split; [|exact HG'].
        apply Forall_cons in Hupper as [Hu Hupper2]. apply Forall_cons in Hupper2 as [Hu1 Hupper3].
        constructor; [|exact Hupper3]. simpl. rewrite Hf2. exact Hu1. }
Qed.

(* The id of any line visible in [scope pre] is one of [pre]'s line ids. *)
Lemma scope_id_in_lines pre f i :
  (f, i) ∈ scope pre -> i ∈ lines_of_prededuct pre.
Proof.
  intros Hin. unfold scope in Hin.
  destruct (frame_lines_in_pre pre f i Hin) as [l [Hlin [Hid _]]].
  exact (id_in_lines_of_prededuct pre l i Hlin Hid).
Qed.

Lemma sp_scope_id_in_lines pre f1 f2 i j :
  SubProof f1 i f2 j ∈ sp_scope pre ->
  i ∈ lines_of_prededuct pre ∧ j ∈ lines_of_prededuct pre.
Proof.
  intros Hin.
  destruct (sp_scope_frml_at pre f1 f2 i j Hin) as [Hi Hj].
  split; eauto using frml_at_some_id_in_lines.
Qed.

(** ** lines_ok properties *)

(* Snoc inversion for [lines_ok]: legality of [pre ++ [l]] is exactly
   legality of [pre] together with [l] being legal right after it.  This
   packages the [inversion ... ; app_inj_tail ; subst] ritual that the
   [lines_ok_cons] constructor (keyed on a snoc) otherwise forces at every
   use site. *)
Lemma lines_ok_snoc_inv pre l :
  lines_ok (pre ++ [l]) -> lines_ok pre /\ line_ok pre l.
Proof.
  intros H. inversion H as [Hnil | line pre' Hpre Hline Heq].
  - by destruct pre.
  - apply app_inj_tail in Heq as [-> ->]. split; assumption.
Qed.

(* After the leading assumptions, there are no more assumptions *)
Lemma drop_assumes_after pre s Σ :
  lines_ok (pre ++ s :: Σ) -> ¬ is_assume s -> drop_assumes Σ = Σ.
Proof.
  intros Hok Hs. induction Σ as [|l Σ IH] using rev_ind; [done|].
  rewrite app_comm_cons app_assoc in Hok.
  apply lines_ok_snoc_inv in Hok as [Hok Hl].
  rewrite drop_assumes_app IH //.
  destruct l; simpl in *; try done.
  exfalso. apply Hs. apply Forall_app in Hl as [_ Hl]. by inversion Hl.
Qed.


(* In a legal prededuction every [ScopeClose] refers to genuine line ids:
   [line_ok] forces its two ids to be the first and last line of the
   innermost open frame, which are lines that actually occur. *)
Lemma lines_ok_scopeclose_ids Σ l1 l2 :
  lines_ok Σ ->
  ScopeClose l1 l2 ∈ Σ ->
  l1 ∈ lines_of_prededuct Σ /\ l2 ∈ lines_of_prededuct Σ.
Proof.
  induction 1 as [|l pre Hok IH Hlok].
  - intros H. apply elem_of_nil in H. done.
  - rewrite lines_of_prededuct_app.
    intros [Hin|Hin]%elem_of_app.
    + destruct (IH Hin) as [H1 H2]. split; apply elem_of_app; by left.
    + apply list_elem_of_singleton in Hin. subst l.
      unfold line_ok in Hlok. destruct Hlok as [_ Hlok].
      destruct (frame_stack pre) as [|fr [|fr2 rest]] eqn:Hstk; try done.
      destruct Hlok as [Hh Hlst].
      remember (frame_lines fr) as fl eqn:Hfl.
      destruct fl as [|y ys]; simpl in Hh; [done|].
      injection Hh as Hh.
      destruct (last (y :: ys)) as [z|] eqn:Hlz; simpl in Hlst; [|done].
      injection Hlst as Hlst.
      apply last_Some in Hlz as [zs Hzs].
      assert (Hscope : forall w, w ∈ frame_lines fr -> w ∈ scope pre).
      { intros w Hw. unfold scope. rewrite Hstk. simpl.
        apply elem_of_app. by left. }
      assert (Hy : y ∈ scope pre).
      { apply Hscope. rewrite <- Hfl. apply list_elem_of_here. }
      assert (Hz : z ∈ scope pre).
      { apply Hscope. rewrite <- Hfl, Hzs. apply elem_of_app. right.
        apply list_elem_of_here. }
      destruct y as [yf yi]; simpl in Hh; subst yi.
      destruct z as [zf zi]; simpl in Hlst; subst zi.
      split; apply elem_of_app; left.
      * exact (scope_id_in_lines pre yf l1 Hy).
      * exact (scope_id_in_lines pre zf l2 Hz).
Qed.

Lemma prefix_lines_ok Σ1 Σ2 :
  lines_ok (Σ1 ++ Σ2) ->
  lines_ok Σ1.
Proof.
  revert Σ1. induction Σ2 as [|s Σ2 IH] using rev_ind; intros Σ1 H.
  - by rewrite app_nil_r in H.
  - rewrite app_assoc in H.
    inversion H as [Hnil | line pre Hpre Hline Heq].
    + by destruct (Σ1 ++ Σ2).
    + apply app_inj_tail in Heq as [-> _].
      exact (IH _ Hpre).
Qed.

(* Legality of a single line inside a legal proof, does not depend on
what comes *after* the line *)
Lemma lines_ok_line_ok Σ Δ s rest :
  lines_ok (Σ ++ Δ ++ s :: rest) -> line_ok (Σ ++ Δ) s.
Proof.
  intros H. rewrite app_assoc (cons_middle s) app_assoc in H.
  by apply prefix_lines_ok, lines_ok_snoc_inv in H as [_ ?].
Qed.

Lemma lines_ok_line_ok_here Σ s rest :
  lines_ok (Σ ++ s :: rest) -> line_ok Σ s.
Proof. intros H. by apply (lines_ok_line_ok Σ [] s rest) in H; rewrite app_nil_r in H. Qed.

(* Generic tail transfer for [lines_ok].  Every [*_lines_ok] induction lemma
   (removing a line, removing a subproof, swapping two [Deduce]s, moving a
   [Deduce] past a subproof) shares the same skeleton: a source prefix [Σ]
   and a target prefix [Σ'] over a common tail [Θ], with each tail line's
   legality transferred individually.  This packages the
   [rev_ind]/reassociation/[lines_ok_snoc_inv]/[lines_ok_cons] boilerplate,
   leaving each caller only its genuinely interesting per-line argument.  The
   transfer is handed the decomposition [Θ = Δ ++ s :: rest] (so freshness /
   scope side conditions on the whole tail restrict to the processed prefix
   [Δ]) together with legality of both the source prefix [Σ ++ Δ] and the
   already-transferred target prefix [Σ' ++ Δ]. *)
Lemma lines_ok_tail_transfer Σ Σ' Θ :
  lines_ok Σ' ->
  (forall Δ s rest,
     Θ = Δ ++ s :: rest ->
     lines_ok (Σ ++ Δ) ->
     lines_ok (Σ' ++ Δ) ->
     line_ok (Σ ++ Δ) s ->
     line_ok (Σ' ++ Δ) s) ->
  lines_ok (Σ ++ Θ) ->
  lines_ok (Σ' ++ Θ).
Proof.
  intros HΣ' Htr.
  cut (forall suf pre, Θ = pre ++ suf ->
         lines_ok (Σ' ++ pre) ->
         lines_ok (Σ ++ pre ++ suf) ->
         lines_ok (Σ' ++ pre ++ suf)).
  { intros H Hsrc. pose proof (H Θ [] eq_refl) as H0. simpl in H0.
    rewrite app_nil_r in H0. apply H0; [ exact HΣ' | exact Hsrc ]. }
  induction suf as [|s suf' IH]; intros pre Heq Htgt Hsrc.
  - by rewrite app_nil_r.
  - assert (Hsrc_pre_s : lines_ok ((Σ ++ pre) ++ [s])).
    { rewrite -app_assoc. apply (prefix_lines_ok _ suf'). by rewrite -!app_assoc. }
    apply lines_ok_snoc_inv in Hsrc_pre_s as [Hsrc_pre Hline_src].
    assert (Hline_tgt : line_ok (Σ' ++ pre) s).
    { apply (Htr pre s suf'); [ exact Heq | exact Hsrc_pre | exact Htgt | exact Hline_src ]. }
    assert (Htgt' : lines_ok (Σ' ++ pre ++ [s])).
    { rewrite app_assoc. apply lines_ok_cons; [ exact Htgt | exact Hline_tgt ]. }
    replace (Σ' ++ pre ++ s :: suf') with (Σ' ++ (pre ++ [s]) ++ suf')
      by (by rewrite -!app_assoc).
    apply IH.
    + rewrite Heq. by rewrite -!app_assoc.
    + exact Htgt'.
    + replace ((pre ++ [s]) ++ suf') with (pre ++ s :: suf')
        by (by rewrite -!app_assoc).
      exact Hsrc.
Qed.

(* [NoDup] is inherited by a prefix of the tail: dropping the trailing
   [rest] cannot introduce duplicates.  Used to feed the per-line transfers
   whose side conditions are stated for the shorter prefix. *)
Lemma nodup_lines_app_prefix Σ Δ rest :
  NoDup (lines_of_prededuct (Σ ++ Δ ++ rest)) ->
  NoDup (lines_of_prededuct (Σ ++ Δ)).
Proof.
  rewrite app_assoc lines_of_prededuct_app. apply NoDup_app_remove_r.
Qed.

Lemma nodup_lines_prefix Σ rest :
  NoDup (lines_of_prededuct (Σ ++ rest)) -> NoDup (lines_of_prededuct Σ).
Proof. rewrite lines_of_prededuct_app. apply NoDup_app_remove_r. Qed.

(* Whatever is visible from [X ++ Δ] is not in a block [B] that sits
   between [X] and [Δ]. *)
Lemma nodup_lines_mid_disjoint X B Δ rest k :
  NoDup (lines_of_prededuct (X ++ B ++ Δ ++ rest)) ->
  k ∈ lines_of_prededuct (X ++ Δ) -> k ∉ lines_of_prededuct B.
Proof.
  rewrite !lines_of_prededuct_app. intros Hnd Hk HkB.
  apply NoDup_app in Hnd as (_ & H1 & Hnd). apply NoDup_app in Hnd as (_ & H2 & _).
  apply elem_of_app in Hk as [Hk|Hk]; [apply (H1 k Hk)|apply (H2 k HkB)]; set_solver.
Qed.

Lemma nodup_mid_proof_line Θ1 s Θ3 :
  NoDup (lines_of_prededuct (Θ1 ++ s :: Θ3)) ->
  NoDup (lines_of_prededuct (Θ1 ++ Θ3)).
Proof.
  intros H.
  rewrite lines_of_prededuct_app in H. simpl in H.
  rewrite lines_of_prededuct_app.
  destruct s; first [done | eapply (NoDup_app_remove_mid (lines_of_prededuct Θ1) [l]) ]; eassumption.
Qed.


Lemma mid_proof_line_fresh Θ1 s l Θ3 :
  id_of_line s = Some l ->
  NoDup (lines_of_prededuct (Θ1 ++ s :: Θ3)) ->
  l ∉ lines_of_prededuct (Θ1 ++ Θ3).
Proof.
  intros Hs H.
  rewrite lines_of_prededuct_app in H. simpl in H.
  apply NoDup_app in H as (HnΘ1 & Hsep & Hcons).
  rewrite lines_of_prededuct_app. rewrite elem_of_app.
  destruct s; inversion Hs;
    simplify_eq/=;
    try apply NoDup_cons in Hcons as [HlΘ3 _]; set_solver.
Qed.


Lemma restr_lines_ok Σ l :
  lines_ok Σ ->
  lines_ok (restr Σ l).
Proof.
  intros H.
  destruct (restr_prefix Σ l) as [Σ' HΣ'].
  apply (prefix_lines_ok (restr Σ l) Σ').
  by rewrite <- HΣ'.
Qed.

Lemma just_ok_references_in_lines pre B j :
  just_ok pre B j ->
  forall i, i ∈ references_in_just j -> i ∈ lines_of_prededuct pre.
Proof.
  destruct j as [i|i1 i2|flag i|i1 i2|i1 i2]; simpl.
  - intros Hjust k Hk. apply elem_of_cons in Hk as [->|Hk]; [|apply elem_of_nil in Hk; done].
    exact (scope_id_in_lines _ _ _ Hjust).
  - intros (B1 & B2 & H1 & H2 & ->) k Hk.
    rewrite !elem_of_cons elem_of_nil in Hk.
    destruct Hk as [->|[->|[]]]; eauto using scope_id_in_lines.
  - intros (B1 & B2 & H & ->) k Hk.
    apply elem_of_cons in Hk as [->|Hk]; [|apply elem_of_nil in Hk; done].
    exact (scope_id_in_lines _ _ _ H).
  - intros (B1 & B2 & H & ->) k Hk.
    rewrite !elem_of_cons elem_of_nil in Hk.
    destruct Hk as [->|[->|[]]].
    + exact (proj1 (sp_scope_id_in_lines _ _ _ _ _ H)).
    + exact (proj2 (sp_scope_id_in_lines _ _ _ _ _ H)).
  - intros (B1 & B2 & H1 & H2 & ->) k Hk.
    rewrite !elem_of_cons elem_of_nil in Hk.
    destruct Hk as [->|[->|[]]]; eauto using scope_id_in_lines.
Qed.

(** Every line that an okay line actually references is one of [pre]'s
    line ids. Extends [just_ok_references_in_lines] (the [Deduce] case) to
    the [ScopeClose] references, which [line_ok] pins to the head/last of
    the current top frame. *)
Lemma references_in_line_in_lines pre s i :
  line_ok pre s ->
  i ∈ references_in_line s ->
  i ∈ lines_of_prededuct pre.
Proof.
  destruct s as [A l|A l|l1 l2|A j l]; simpl.
  - intros _ Hi. by apply elem_of_nil in Hi.
  - intros _ Hi. by apply elem_of_nil in Hi.
  - intros [_ Hok]. revert Hok.
    destruct (frame_stack pre) as [|fr [|fr2 rest]] eqn:Hstk;
      [by intros []|by intros []|].
    intros [Hhd Hlst] Hi.
    assert (Hscope : forall f k, (f, k) ∈ frame_lines fr ->
                                 k ∈ lines_of_prededuct pre).
    { intros f k Hk. eapply scope_id_in_lines.
      unfold scope. rewrite Hstk. simpl. apply elem_of_app. left. exact Hk. }
    apply elem_of_cons in Hi as [->|Hi].
    + destruct (head (frame_lines fr)) as [[f0 x0]|] eqn:Hh; simpl in Hhd;
        [|discriminate].
      injection Hhd as Hx0. rewrite <- Hx0.
      exact (Hscope f0 x0 (head_Some_elem_of _ _ Hh)).
    + apply elem_of_cons in Hi as [->|Hi]; [|by apply elem_of_nil in Hi].
      destruct (last (frame_lines fr)) as [[f1 x1]|] eqn:Hl; simpl in Hlst;
        [|discriminate].
      injection Hlst as Hx1. rewrite <- Hx1.
      exact (Hscope f1 x1 (last_Some_elem_of _ _ Hl)).
  - intros Hok Hi. exact (just_ok_references_in_lines pre A j Hok i Hi).
Qed.

(** [just_ok_transfer] is the workhorse monotonicity principle for
    justifications: a justification valid at [pre] is valid at [pre'] as
    long as every line- and subproof-scope entry it actually cites
    (i.e. whose id is in [references_in_just j]) transfers from [pre] to
    [pre'].  The [references_in_just] guard means transfers that only hold
    away from a removed/moved id (as in the subproof reductions) are still
    instances.  It replaces the 5-way [destruct j' … exists f1, f2 …] case
    analysis that otherwise recurs at every scope-manipulation site. *)
Lemma just_ok_transfer pre pre' f j :
  (forall g k, k ∈ references_in_just j -> (g, k) ∈ scope pre -> (g, k) ∈ scope pre') ->
  (forall q, sp_start q ∈ references_in_just j -> q ∈ sp_scope pre -> q ∈ sp_scope pre') ->
  just_ok pre f j -> just_ok pre' f j.
Proof.
  intros Hsc Hsp Hj.
  destruct j as [l0|m1 m2|flag l0|m1 m2|m1 m2]; simpl in Hsc, Hsp, Hj |- *.
  - apply (Hsc f l0); [apply elem_of_cons; by left | exact Hj].
  - destruct Hj as (f1 & f2 & H1 & H2 & ->). exists f1, f2.
    split; [apply (Hsc f1 m1); [apply elem_of_cons; by left | exact H1]|].
    split; [apply (Hsc f2 m2);
              [apply elem_of_cons; right; apply elem_of_cons; by left | exact H2]
           | reflexivity].
  - destruct Hj as (f1 & f2 & H1 & ->). exists f1, f2.
    split; [apply (Hsc (fConj f1 f2) l0); [apply elem_of_cons; by left | exact H1]
           | reflexivity].
  - destruct Hj as (f1 & f2 & H1 & ->). exists f1, f2.
    split; [apply (Hsp (SubProof f1 m1 f2 m2)); [apply elem_of_cons; by left | exact H1]
           | reflexivity].
  - destruct Hj as (f1 & f2 & H1 & H2 & ->). exists f1, f2.
    split; [apply (Hsc (fImpl f1 f2) m1); [apply elem_of_cons; by left | exact H1]|].
    split; [apply (Hsc f1 m2);
              [apply elem_of_cons; right; apply elem_of_cons; by left | exact H2]
           | reflexivity].
Qed.

(** Plain monotonicity: when the whole line- and subproof-scope grow, every
    justification is preserved — the common special case of
    [just_ok_transfer] with the [references_in_just] guard discharged. *)
Lemma just_ok_mono pre pre' f j :
  (forall x, x ∈ scope pre -> x ∈ scope pre') ->
  (forall x, x ∈ sp_scope pre -> x ∈ sp_scope pre') ->
  just_ok pre f j -> just_ok pre' f j.
Proof.
  intros Hsc Hsp. apply just_ok_transfer.
  - intros g k _ H. exact (Hsc (g, k) H).
  - intros q _ H. exact (Hsp q H).
Qed.


(** ** conclusion properties *)

Lemma conclusion_of_app Σ Θ :
  Θ ≠ [] ->
  conclusion_of (Σ ++ Θ) = conclusion_of Θ.
Proof.
  intros (Θ' & s & ->)%not_nil_snoc.
  unfold conclusion_of. by rewrite app_assoc !last_snoc.
Qed.

Lemma conclusion_of_mid X Y Θ :
  Θ ≠ [] -> conclusion_of (X ++ Θ) = conclusion_of (Y ++ Θ).
Proof. intros. by rewrite !conclusion_of_app. Qed.

Lemma conclusion_of_snoc_inv pre s f :
  conclusion_of (pre ++ [s]) = Some f ->
  conclusion_of [s] = Some f.
Proof.
  unfold conclusion_of.
  by rewrite last_app_cons !last_singleton.
Qed.

Lemma conclusion_of_snoc_deduce pre f j i :
  conclusion_of (pre ++ [Deduce f j i]) = Some f.
Proof. by rewrite conclusion_of_app. Qed.



(** ** Closing subproofs *)

(* A [Deduce] line puts its id at the end of the top frame. *)
Lemma frame_stack_last_deduce pre f j k :
  last pre = Some (Deduce f j k) ->
  ∃ fr rest, frame_stack pre = fr :: rest ∧ last (frame_lines fr) = Some (f, k).
Proof.
  intros [pre' ->]%last_Some.
  rewrite frame_stack_snoc /=.
  destruct (frame_stack pre') as [|fr rest] eqn:E; [by destruct (frame_stack_nonempty pre')|].
  eexists _, _. split; [done|]. by rewrite /= last_snoc.
Qed.

(* The lines named by a legal [ScopeClose] are in scope. *)
Lemma scopeclose_ids_in_scope pre k1 k2 :
  line_ok pre (ScopeClose k1 k2) ->
  (∃ f, (f, k1) ∈ scope pre) ∧ (∃ f, (f, k2) ∈ scope pre).
Proof.
  intros [_ Hstk]. rewrite /scope.
  destruct (frame_stack pre) as [|fr [|fr' rest]]; try done.
  destruct Hstk as [Hh Hl].
  destruct (head (frame_lines fr)) as [[f i]|] eqn:Eh; simplify_eq/=.
  destruct (last (frame_lines fr)) as [[g i']|] eqn:El; simplify_eq/=.
  split; [exists f|exists g]; apply elem_of_app; left;
    [by apply head_Some_elem_of|by apply last_Some_elem_of].
Qed.

(* Thanks to the rule "a [ScopeClose] comes right after a [Deduce] of its
   last line", the [last] condition of a close is automatic; only the
   [head] condition needs to be transferred. *)
Lemma scopeclose_ok_transfer preW preO k1 k2 :
  line_ok preW (ScopeClose k1 k2) ->
  last preO = last preW ->
  length (frame_stack preO) = length (frame_stack preW) ->
  (forall fO, head (frame_stack preO) = Some fO ->
     option_map snd (head (frame_lines fO)) = Some k1) ->
  line_ok preO (ScopeClose k1 k2).
Proof.
  rewrite /line_ok. intros [Hlast Hstk] HlastO Hlen Hhead.
  rewrite HlastO. split; [done|].
  destruct (last preW) as [[| | |f j k]|] eqn:EW; try done. subst k.
  destruct (frame_stack_last_deduce preO f j k2) as (fr & rest & Efr & Hl);
    [by rewrite HlastO|].
  rewrite Efr in Hlen Hhead |- *.
  destruct (frame_stack preW) as [|? [|? ?]]; try done.
  destruct rest as [|? ?]; [simpl in Hlen; lia|].
  split; [by apply Hhead|]. by rewrite Hl.
Qed.

(** Every frame of the stack except the bottom one was pushed by a
    [Raise], so its first line is that [Raise]. *)
Fixpoint inner_raised (pre : prededuct) (stk : list frame) : Prop :=
  match stk with
  | [] => True
  | [_] => True
  | fr :: rest =>
    (∃ A i, head (frame_lines fr) = Some (A, i) ∧ Raise A i ∈ pre) ∧
    inner_raised pre rest
  end.

Lemma inner_raised_mono pre pre' stk :
  (forall x, x ∈ pre -> x ∈ pre') -> inner_raised pre stk -> inner_raised pre' stk.
Proof.
  intros Hsub. induction stk as [|fr [|fr' rest] IH]; [done|done|].
  intros [(A & i & Hh & Hin) Hrest]. split; [by eauto|by apply IH].
Qed.

Lemma inner_raised_step pre stk s :
  inner_raised pre stk -> inner_raised (pre ++ [s]) (frame_step pre stk s).
Proof.
  intros H. apply (inner_raised_mono pre (pre ++ [s])) in H; [|set_solver].
  destruct s as [f l|f l|l1 l2|f j l]; simpl.
  - destruct stk as [|fr [|fr' rest]]; [done|done|].
    destruct H as [(A & i & Hh & Hin) Hrest]. split; [|done].
    exists A, i. by rewrite /= head_app Hh.
  - destruct stk as [|fr rest]; [done|].
    split; [|done]. eexists _, _. split; [done|set_solver].
  - destruct stk as [|a [|fr2 rest]]; try done.
    destruct (frml_at pre l1), (frml_at pre l2); try done.
    destruct rest as [|fr3 rest]; [done|].
    by destruct H as [_ [Hfr2 Hrest]].
  - destruct stk as [|fr [|fr' rest]]; [done|done|].
    destruct H as [(A & i & Hh & Hin) Hrest]. split; [|done].
    exists A, i. by rewrite /= head_app Hh.
Qed.

Lemma inner_raised_go pre stk Δ :
  inner_raised pre stk -> inner_raised (pre ++ Δ) (frame_stack_go pre stk Δ).
Proof.
  revert pre stk. induction Δ as [|s Δ IH]; intros pre stk H; simpl.
  - by rewrite app_nil_r.
  - rewrite (cons_middle s pre Δ) app_assoc. apply IH. by apply inner_raised_step.
Qed.

(* The top frame of a stack with an open subproof starts with a [Raise]
   line; with unique ids, it does not start with a [Deduce] line. *)
Lemma frame_stack_top_not_deduce pre fr fr' rest B j k :
  NoDup (lines_of_prededuct pre) ->
  frame_stack pre = fr :: fr' :: rest ->
  Deduce B j k ∈ pre ->
  option_map snd (head (frame_lines fr)) ≠ Some k.
Proof.
  intros Hnd E HD.
  pose proof (inner_raised_go [] [mkFrame [] []] pre I) as H.
  rewrite /frame_stack in E. rewrite E /= in H.
  destruct H as [(A & i & Hh & Hin) _].
  rewrite Hh /=. intros [= ->]. by eapply NoDup_raise_deduce.
Qed.

(* The line before a legal close is the last line of the subproof's body. *)
Lemma closed_block_last_line P A l1 Θ2 l2 :
  lines_ok (P ++ Raise A l1 :: Θ2 ++ [ScopeClose l1 l2]) ->
  ∃ f j, last Θ2 = Some (Deduce f j l2).
Proof.
  rewrite app_comm_cons app_assoc. intros [_ [Hlast _]]%lines_ok_snoc_inv.
  rewrite last_app_cons last_cons in Hlast.
  destruct (last Θ2) as [[| | |f j k]|]; try done. subst. by eexists _, _.
Qed.

(* A legal closed subproof [Raise A l1 … ScopeClose l1 l2] leaves the frame
   stack as it found it, except that the current frame records the
   subproof. *)
Lemma frame_stack_closed_block P A l1 Θ2 l2 :
  lines_ok (P ++ Raise A l1 :: Θ2 ++ [ScopeClose l1 l2]) ->
  NoDup (lines_of_prededuct (P ++ Raise A l1 :: Θ2 ++ [ScopeClose l1 l2])) ->
  ∃ fr rest f2 j,
    frame_stack P = fr :: rest ∧
    last Θ2 = Some (Deduce f2 j l2) ∧
    frame_stack (P ++ Raise A l1 :: Θ2 ++ [ScopeClose l1 l2]) =
      mkFrame (frame_lines fr) (frame_subproofs fr ++ [SubProof A l1 f2 l2]) :: rest.
Proof.
  intros Hok Hnd.
  destruct (closed_block_last_line _ _ _ _ _ Hok) as (f2 & j & EL).
  apply (nodup_lines_app_prefix _ (Raise A l1 :: Θ2)) in Hnd.
  rewrite app_comm_cons app_assoc in Hok |- *.
  apply lines_ok_snoc_inv in Hok as [_ [_ Hstk]].
  pose proof Hnd as Hnd'.
  rewrite lines_of_prededuct_app /= in Hnd'.
  apply NoDup_app in Hnd' as (_ & Hdisj & Hnd2). apply NoDup_cons in Hnd2 as [Hl1Θ2 _].
  assert (Hl1P : l1 ∉ lines_of_prededuct P).
  { intros H. apply (Hdisj l1 H). set_solver. }
  assert (Hf1 : frml_at (P ++ Raise A l1 :: Θ2) l1 = Some A).
  { rewrite /frml_at (line_at_NoDup_elem_of _ l1 (Raise A l1)) //. set_solver. }
  assert (Hf2 : frml_at (P ++ Raise A l1 :: Θ2) l2 = Some f2).
  { rewrite /frml_at (line_at_NoDup_elem_of _ l2 (Deduce f2 j l2)) //.
    apply last_Some_elem_of in EL. set_solver. }
  rewrite frame_stack_snoc.
  destruct (block_invariant P A l1 Θ2 Hl1P Hl1Θ2)
    as [([|u upper] & G' & Estk & Hup & HG)|Hno].
  - rewrite Estk /=.
    destruct (frame_stack P) as [|fr rest] eqn:EP; [by destruct (frame_stack_nonempty P)|].
    exists fr, rest, f2, j. by rewrite /= Hf1 Hf2.
  - rewrite Estk in Hstk. apply Forall_cons in Hup as [Hu _].
    destruct upper; simpl in Hstk; destruct Hstk; contradiction.
  - destruct (frame_stack (P ++ Raise A l1 :: Θ2)) as [|fr [|? ?]]; try done.
    apply Forall_cons in Hno as [Hno _]. by destruct Hstk.
Qed.

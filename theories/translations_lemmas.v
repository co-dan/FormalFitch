(* Translations between Fitch (pre)deductions and LetLang programs *)
From stdpp Require Import list.
From fitch Require Import prelude core
  deduction_lemmas typing_lemmas.

(** * Typing preservation *)

(** The types of the parameters of a program *)
Fixpoint prog_vars (p : prog) : list frml :=
  match p with
  | PVar _ A p' => A :: prog_vars p'
  | PBody _ _ => []
  end.

Lemma assumptions_of_deduct_of_body y b :
  assumptions_of (⦇b⦈ y) = [].
Proof.
  revert y.
  induction b as [x A o k IH|x y' A B s IHs k IHk|A o|x b IH] using body_mut
    with (P0 := λ s, ∀ x y A, assumptions_of (deduct_of_sub x y A s) = []);
    simpl; intros; rewrite ?assumptions_of_app /=.
  - done.
  - by rewrite IHs IHk.
  - done.
  - by rewrite IH.
Qed.

Theorem deduct_of_term_assumptions p : assumptions_of ⦇p⦈ᶜ = prog_vars p.
Proof.
  induction p; simpl; [by f_equal|]. apply assumptions_of_deduct_of_body.
Qed.

Lemma deduct_of_body_conclusion Γ y b C :
  Γ ⊢ b : C -> conclusion_of (⦇b⦈ y) = Some C.
Proof.
  induction 1 as [????? C _ _ IH|????????? _ _ IH|]; simpl.
  - by rewrite conclusion_of_cons IH.
  - rewrite app_comm_cons conclusion_of_app // => Hnil. by rewrite Hnil in IH.
  - done.
Qed.

Theorem deduct_of_term_conclusion Γ p C :
  Γ ⊢ₚ p : C -> conclusion_of ⦇p⦈ᶜ = Some C.
Proof.
  induction 1 as [????? _ IH|???? Hb]; simpl.
  - by rewrite conclusion_of_cons IH.
  - by eapply deduct_of_body_conclusion.
Qed.

(** * Auxiliary functions *)

Fixpoint ret_op (b : body) : op :=
  match b with
  | BLet _ _ _ k | BLetSub _ _ _ _ _ k => ret_op k
  | BRet _ o => o
  end.

Lemma just_of_op_of_just J : just_of_op (op_of_just J) = J.
Proof. by destruct J. Qed.

Lemma op_of_just_of_op Γ o A : Γ ⊢ₒ o : A -> op_of_just (just_of_op o) = o.
Proof. by destruct 1. Qed.

Lemma term_of_deduct_no_assume Σ :
  (∀ A x Σ', Σ ≠ Assume A x :: Σ') -> ⟦Σ⟧ᶜ = PBody (last_line_id Σ) ⟦Σ⟧.
Proof. destruct Σ as [|[] ?]; naive_solver. Qed.

Lemma deduct_of_body_not_assume y b A x Σ' :
  ⦇b⦈ y ≠ Assume A x :: Σ'.
Proof. by destruct b as [|???? [] ?|]. Qed.

(** The return of a body is its last line *)
Lemma last_deduct_of_body y b :
  last (⦇b⦈ y) = Some (Deduce (ret_ty b) (just_of_op (ret_op b)) y).
Proof.
  induction b as [x A o k IH|x y' A B s k IH|A o]; simpl; [| |done].
  - rewrite last_cons IH. done.
  - rewrite last_app IH. done.
Qed.

(** * Programs → deductions → programs

Relatively simple induction on the structure of the program. *)

Lemma body_typed_ret_ty Γ b C : Γ ⊢ b : C -> ret_ty b = C.
Proof. induction 1; done. Qed.

(** If we start with a well-typed program, then converting it
to a proof and back gives the same result and does not modify the stack. *)
Lemma term_of_deduct'_of_body Γ b C y stk :
  Γ ⊢ b : C ->
  term_of_deduct' (⦇b⦈ y) stk = {| trstate_cur := Some b; trstate_stk := stk |}.
Proof.
  intros Hty.
  revert y stk.
  induction Hty as [Γ x A o k C Ho _ IH|Γ x y' A B b k C Hb IHb _ IHk|Γ A o Ho]
    => y stk.
  - simpl.
    rewrite IH /=. do 2 f_equiv.
    rewrite (op_of_just_of_op Γ o A)//.
  - unfold term_of_deduct' in *.
    rewrite foldr_app.
    rewrite IHk /= foldr_app /= IHb /=.
    by rewrite (body_typed_ret_ty _ _ _ Hb).
  - simpl. do 2 f_equiv.
    rewrite (op_of_just_of_op Γ o A)//.
Qed.

Theorem body_of_deduct_of_body Γ y b C :
  Γ ⊢ b : C -> ⟦⦇b⦈ y⟧ = b.
Proof.
  intros Hb.
  unfold body_of_deduct.
  rewrite (term_of_deduct'_of_body Γ b C)//.
Qed.

Theorem term_of_deduct_of_term Γ p C :
  Γ ⊢ₚ p : C -> ⟦⦇p⦈ᶜ⟧ᶜ = p.
Proof.
  induction 1 as [Γ x A p C _ IH|Γ y b C Hb]; simpl.
  - by rewrite IH.
  - rewrite term_of_deduct_no_assume
      ?(body_of_deduct_of_body _ _ _ _ Hb).
    + by rewrite /last_line_id last_deduct_of_body.
    + intros. apply deduct_of_body_not_assume.
Qed.

(** * Deductions → programs → deductions *)

(** We show that translating a deduction is undone by [⦇ .. ⦈ᶜ]. Since
    the translation goes from right to left, we consider the suffixes
    of a valid deduction, and show that the translation state after a
    suffix stands for exactly the lines of the suffix
    ([trstate_lines]). The stack of the state has one entry for every
    subproof that is open before the suffix. *)

(** ** Auxiliary facts about valid deductions *)

(** Pre-deduction Σ starts with a Deduce or a Subproof *)
Definition opens_body (Σ : prededuct) : Prop :=
  match Σ with Deduce _ _ _ :: _ | Raise _ _ :: _ => True | _ => False end.

(** After a [Raise] or a [ScopeClose], a valid deduction continues
    with a deduction or a subproof *)
Lemma lines_ok_opens_body P s S y A J :
  lines_ok (P ++ s :: S) ->
  last (P ++ s :: S) = Some (Deduce A J y) ->
  match s with
    | Raise _ _ | ScopeClose _ _ => True
    | _ => False end ->
  opens_body S.
Proof.
  intros Hok Hlast Hs.
  destruct S as [|s' S].
  { destruct s as [B l|B l|l1 l2|B J' l]; try done.
    + rewrite last_snoc in Hlast.
      inversion Hlast.
    + rewrite last_snoc in Hlast.
      inversion Hlast. }
  rewrite cons_middle app_assoc in Hok.
  apply lines_ok_line_ok_here in Hok.
  destruct s' as [B l|B l|l1 l2|B J' l]; try done;
    simpl in Hok.
  - exfalso.
    apply Forall_app in Hok as [_ [? _]%Forall_cons].
    by destruct s.
  - destruct Hok as [Hok _]. rewrite last_snoc in Hok.
    by destruct s.
Qed.

(** The depth of the frame stack *)
Lemma length_frame_stack_snoc pre s :
  lines_ok (pre ++ [s]) ->
  length (frame_stack (pre ++ [s])) =
  match s with
  | Raise _ _ => S (length (frame_stack pre))
  | ScopeClose _ _ => pred (length (frame_stack pre))
  | _ => length (frame_stack pre)
  end.
Proof.
  intros Hok. rewrite frame_stack_snoc.
  pose proof (lines_ok_line_ok_here _ _ _ Hok) as Hl.
  destruct (frame_stack pre) as [|fr rest] eqn:Hfs;
    [by destruct (frame_stack_nonempty pre)|].
  destruct s as [A x|A x|l1 l2|A J l]; simpl; [done|done| |done].
  (* [ScopeClose]: the lookups of [l1] and [l2] succeed *)
  assert (l1 ∈ lines_of_prededuct pre ∧ l2 ∈ lines_of_prededuct pre) as [Hi1 Hi2]
    by (pose proof (lines_ok_scopeclose_ids _ l1 l2 Hok) as Hids;
        rewrite lines_of_prededuct_app /= app_nil_r in Hids; apply Hids; set_solver).
  destruct (frml_at_isSome _ _ Hi1) as [f1 ->], (frml_at_isSome _ _ Hi2) as [f2 ->].
  destruct Hl as [_ Hl]. rewrite Hfs in Hl. by destruct rest.
Qed.

(** ** The lines of a translation state *)

Definition opt_lines (y : id) (ob : option body) : prededuct :=
  from_option (deduct_of_body y) [] ob.

(** The lines that the translation state [(cur, stk)] stands for, where
    [y] is the id of the last line of the deduction *)
Fixpoint trstate_lines (y : id) (cur : option body)
    (stk : list (id * id * option body)) : prededuct :=
  match stk with
  | [] => opt_lines y cur
  | (l1, l2, k) :: stk' =>
    opt_lines l2 cur ++ ScopeClose l1 l2 :: trstate_lines y k stk'
  end.

Lemma trstate_lines_opens_body y cur stk :
  opens_body (trstate_lines y cur stk) -> is_Some cur.
Proof. destruct cur as [b|], stk as [|[[??]?]?]; naive_solver. Qed.

(** ** The invariant *)

Lemma term_of_deduct_step_assume A x st :
  term_of_deduct_step (Assume A x) st = st.
Proof. by destruct st. Qed.

Lemma foldr_term_of_deduct_step Σ : ∀ P y A J,
  lines_ok (P ++ Σ) ->
  last (P ++ Σ) = Some (Deduce A J y) ->
  length (frame_stack (P ++ Σ)) = 1 ->
  ∃ cur stk,
    foldr term_of_deduct_step {| trstate_cur := None; trstate_stk := [] |}
      Σ = {| trstate_cur := cur; trstate_stk := stk |} ∧
    trstate_lines y cur stk = drop_assumes Σ ∧
    S (length stk) = length (frame_stack P) ∧
    Forall (λ e, is_Some e.2) stk.
Proof.
  induction Σ as [|s Σ IH]; intros P y A' J' Hok Hlast Hlen.
  { rewrite app_nil_r in Hlen. by eexists None, []. }
  pose proof (lines_ok_line_ok_here _ _ _ Hok) as Hl.
  pose proof (lines_ok_opens_body _ _ _ _ _ _ Hok Hlast) as Hop.
  pose proof Hok as Hok'. rewrite cons_middle app_assoc in Hok Hlast Hlen.
  destruct (IH _ _ _ _ Hok Hlast Hlen) as (cur & stk & Hst & Hlines & Hlen' & Hsome).
  rewrite length_frame_stack_snoc in Hlen'; [|by eapply prefix_lines_ok].
  pose proof (frame_stack_nonempty P) as Hne.
  destruct s as [A x|A x|l1 l2|A J l];
    [exists cur, stk; rewrite foldr_cons Hst term_of_deduct_step_assume;
     by simpl in *|..];
    rewrite /= (drop_assumes_after P _ Σ Hok' (λ H, H)) in Hlines Hop |- *;
    rewrite /= Hst; simpl in Hlen'.
  - (* Raise *)
    destruct stk as [|[[l1 l2] ok] stk]; [by destruct (frame_stack P)|].
    apply Forall_cons in Hsome as [[k Hk] Hsome]. simpl in Hk; subst ok.
    rewrite -Hlines in Hop. destruct (trstate_lines_opens_body _ _ _ (Hop I)) as [b ->].
    eexists _, _. split_and!; [done| |by simplify_eq/=|done].
    rewrite -Hlines. destruct stk as [|[[??]?]?]; simpl; by rewrite -!app_assoc.
  - (* ScopeClose *)
    rewrite -Hlines in Hop. pose proof (trstate_lines_opens_body _ _ _ (Hop I)).
    eexists _, _. split_and!; [done|by rewrite -Hlines| |by constructor].
    destruct (frame_stack P); simpl in *; [done|lia].
  - (* Deduce: the next line closes the subproof that ends with it *)
    assert (match Σ with
            | [] => l = y
            | ScopeClose _ l2 :: _ => l = l2
            | _ => True
            end) as Hl'.
    { destruct Σ as [|[] Σ]; try done.
      - by rewrite app_nil_r last_snoc in Hlast; simplify_eq.
      - apply lines_ok_line_ok_here in Hok as [Hok _].
        by rewrite last_snoc in Hok. }
    destruct cur; eexists _, _; (split_and!; [done| |done|done]);
      rewrite -Hlines in Hl' |- *;
      destruct stk as [|[[??]?]?]; simplify_eq/=; by rewrite just_of_op_of_just.
Qed.

Lemma body_of_deduct_assume A x Σ : ⟦Assume A x :: Σ⟧ = ⟦Σ⟧.
Proof.
  unfold body_of_deduct, term_of_deduct'.
  by rewrite foldr_cons term_of_deduct_step_assume.
Qed.

Lemma last_line_id_assume A x Σ :
  last_line_id (Assume A x :: Σ) = last_line_id Σ.
Proof.
  rewrite /last_line_id last_cons. by destruct (last Σ).
 Qed.

(** ** The round trip *)

Theorem deduct_of_body_of_deduct Σ :
  is_deduct Σ -> ⦇⟦Σ⟧⦈ (last_line_id Σ) = drop_assumes Σ.
Proof.
  intros (Hok & Hlen & _ & [f Hc]). rewrite /conclusion_of in Hc.
  rewrite /last_line_id.
  destruct (last Σ) as [[| | |A J y]|] eqn:Hl; try done.
  destruct (foldr_term_of_deduct_step Σ [] y A J)
    as (cur & stk & Hst & Hlines & Hstk & _); [eauto..|].
  rewrite /body_of_deduct /term_of_deduct' Hst.
  destruct stk; [|done]. destruct cur as [b|].
  - by rewrite -Hlines.
  - apply last_Some in Hl as [Σ0 ->].
    by rewrite drop_assumes_app /= in Hlines; destruct (drop_assumes Σ0).
Qed.

Lemma deduct_of_term_of_deduct_aux as_ Σ :
  lines_ok (as_ ++ Σ) ->
  ⦇⟦Σ⟧⦈ (last_line_id Σ) = drop_assumes Σ -> ⦇⟦Σ⟧ᶜ⦈ᶜ = Σ.
Proof.
  revert as_. induction Σ as [|l Σ IH]; intros as_ Hok HΣ; [done|].
  destruct l as [A x|A x|l1 l2|A J n];
    [|rewrite term_of_deduct_no_assume // /= HΣ /=; f_equal;
      by eapply drop_assumes_after; [exact Hok|intros []]..].
  (* Assume *)
  rewrite /=. f_equal. apply (IH (as_ ++ [Assume A x])); [by rewrite -app_assoc|].
  by rewrite body_of_deduct_assume last_line_id_assume in HΣ.
Qed.

Theorem deduct_of_term_of_deduct Σ : is_deduct Σ -> ⦇⟦Σ⟧ᶜ⦈ᶜ = Σ.
Proof.
  intros HΣ. apply (deduct_of_term_of_deduct_aux []); [apply HΣ|].
  by apply deduct_of_body_of_deduct.
Qed.

(** * Translations of valid deductions are valid programs *)

(** ** Syntactic well-formedness *)

(** Operations use variables of the right kind, and the type of a
    subroutine agrees with its return. Translations of deductions are
    always well-formed. *)
Definition op_wf (o : op) : Prop := op_of_just (just_of_op o) = o.

Fixpoint body_wf (b : body) : Prop :=
  match b with
  | BLet _ _ o k => op_wf o ∧ body_wf k
  | BLetSub _ _ _ B (mkSubr _ b') k => B = ret_ty b' ∧ body_wf b' ∧ body_wf k
  | BRet _ o => op_wf o
  end.

Fixpoint prog_wf (p : prog) : Prop :=
  match p with
  | PVar _ _ p' => prog_wf p'
  | PBody _ b => body_wf b
  end.

Definition trstate_wf (st : TrState) : Prop :=
  from_option body_wf True (trstate_cur st) ∧
  Forall (λ e, from_option body_wf True e.2) (trstate_stk st).

Lemma term_of_deduct_step_wf s st :
  trstate_wf st -> trstate_wf (term_of_deduct_step s st).
Proof.
  destruct st as [cur stk], s as [A x|A x|l1 l2|A J l];
    rewrite /trstate_wf /=; intros [Hcur Hstk]; [done| | |].
  - destruct cur as [b|], stk as [|[[l1 l2] [k|]] stk]; try done.
    apply Forall_cons in Hstk as [Hk Hstk]. done.
  - split; [done|]. by constructor.
  - destruct cur; (split; [|done]); simpl in *;
      rewrite /op_wf just_of_op_of_just; done.
Qed.

Lemma body_of_deduct_wf Σ : body_wf ⟦Σ⟧.
Proof.
  rewrite /body_of_deduct.
  assert (trstate_wf (foldr term_of_deduct_step
            {| trstate_cur := None; trstate_stk := [] |} Σ)) as [Hcur _].
  { induction Σ as [|s Σ IH]; [done|]. by apply term_of_deduct_step_wf. }
  unfold term_of_deduct'.
  destruct (foldr _ _ _) as [[b|] [|]]; done.
Qed.

Lemma term_of_deduct_wf Σ : prog_wf ⟦Σ⟧ᶜ.
Proof.
  induction Σ as [|[A x| | |] Σ IH]; simpl; try done; apply body_of_deduct_wf.
Qed.

(** Well-typed programs are well-formed *)
Lemma body_typed_wf Γ b C : Γ ⊢ b : C -> body_wf b.
Proof.
  induction 1 as [Γ x A o k C Ho _ IH|Γ x y A B b k C Hb IHb _ IHk|Γ A o Ho];
    simpl; rewrite /op_wf.
  - split; [|done]. by eapply op_of_just_of_op.
  - split_and!; [|done|done]. symmetry. by eapply body_typed_ret_ty.
  - by eapply op_of_just_of_op.
Qed.

Lemma prog_typed_wf Γ p C : Γ ⊢ₚ p : C -> prog_wf p.
Proof. induction 1; simpl; [done|]. by eapply body_typed_wf. Qed.

(** ** Typing *)

Lemma deduct_of_body_nonempty y b : ⦇b⦈ y ≠ [].
Proof. by destruct b as [|???? [] ?|]. Qed.

(** The ids of the lines of a translation are the binders *)
Lemma lines_of_deduct_of_body y b :
  lines_of_prededuct (⦇b⦈ y) = body_binders b ++ [y].
Proof.
  revert y.
  induction b as [x A o k IH|x y' A B s IHs k IHk|A o|x b IH] using body_mut
    with (P0 := λ s, ∀ x y A,
       lines_of_prededuct (deduct_of_sub x y A s) = subr_binders s ++ [y]);
    simpl; intros.
  - by rewrite IH.
  - by rewrite lines_of_prededuct_app IHs IHk -!app_assoc.
  - done.
  - by rewrite lines_of_prededuct_app IH /= app_nil_r.
Qed.

Lemma lines_of_deduct_of_term p : lines_of_prededuct ⦇p⦈ᶜ = prog_binders p.
Proof.
  induction p; simpl; [by f_equal|]. apply lines_of_deduct_of_body.
Qed.

(** The typing context [Γ] contains the lines and subproofs in the
    scope of the frame stack [fs] *)
Definition ctx_ok (fs : list frame) (Γ : ctx) : Prop :=
  (∀ f i, (f, i) ∈ concat (frame_lines <$> fs) -> (LVar i, TFrml f) ∈ Γ) ∧
  (∀ f1 i f2 j, SubProof f1 i f2 j ∈ concat (frame_subproofs <$> fs) ->
     (SVar i j, TSub f1 f2) ∈ Γ).

Lemma ctx_ok_add fr rest Γ A x :
  ctx_ok (fr :: rest) Γ ->
  ctx_ok (mkFrame (frame_lines fr ++ [(A, x)]) (frame_subproofs fr) :: rest)
    ((LVar x, TFrml A) :: Γ).
Proof.
  intros [Hl Hs]. split; simpl.
  - intros f i. rewrite -app_assoc !elem_of_app list_elem_of_singleton.
    intros [?|[[= -> ->]|?]]; [| |]; [|by left|]; right; apply Hl; set_solver.
  - intros f1 i f2 j Hi. right. by apply Hs.
Qed.

Lemma ctx_ok_push fs Γ A x :
  ctx_ok fs Γ -> ctx_ok (mkFrame [(A, x)] [] :: fs) ((LVar x, TFrml A) :: Γ).
Proof.
  intros [Hl Hs]. split; simpl.
  - intros f i [[= -> ->]|?]%elem_of_cons; [by left|]. right. by apply Hl.
  - intros f1 i f2 j Hi. right. by apply Hs.
Qed.

Lemma ctx_ok_close fr rest Γ A x B y :
  ctx_ok (fr :: rest) Γ ->
  ctx_ok (mkFrame (frame_lines fr) (frame_subproofs fr ++ [SubProof A x B y]) :: rest)
    ((SVar x y, TSub A B) :: Γ).
Proof.
  intros [Hl Hs]. split; simpl.
  - intros f i Hi. right. by apply Hl.
  - intros f1 i f2 j. rewrite -app_assoc !elem_of_app list_elem_of_singleton.
    intros [?|[[= -> -> -> ->]|?]]; [| |]; [|by left|]; right; apply Hs; set_solver.
Qed.

Lemma just_ok_typed pre Γ f J :
  ctx_ok (frame_stack pre) Γ -> just_ok pre f J -> op_typed Γ (op_of_just J) f.
Proof.
  intros [Hl Hs]. rewrite /scope /sp_scope in Hl Hs.
  destruct J as [l|l1 l2|[] l|l1 l2|l1 l2]; simpl.
  - intros Hf. constructor. by apply Hl.
  - intros (f1 & f2 & ? & ? & ->). constructor; by apply Hl.
  - intros (f1 & f2 & ? & ->). eapply op_typed_fst. by apply Hl.
  - intros (f1 & f2 & ? & ->). eapply op_typed_snd. by apply Hl.
  - intros (f1 & f2 & ? & ->). constructor. by apply Hs.
  - intros (f1 & f2 & ? & ? & ->). econstructor; by apply Hl.
Qed.

(** If the translation of a well-formed body is valid, then the body
    is well-typed. Moreover, the body extends the top frame. *)
Lemma body_typed_of_deduct b : ∀ P y R Γ fr rest,
  lines_ok (P ++ ⦇b⦈ y ++ R) ->
  NoDup (lines_of_prededuct (P ++ ⦇b⦈ y ++ R)) ->
  body_wf b ->
  frame_stack P = fr :: rest ->
  ctx_ok (fr :: rest) Γ ->
  body_typed Γ b (ret_ty b) ∧
  ∃ L S, frame_stack (P ++ ⦇b⦈ y) =
         mkFrame (frame_lines fr ++ L) S :: rest.
Proof.
  revert b. fix IH 1.
  intros b P y R Γ fr rest Hok Hnd Hwf Hfs Hctx.
  destruct b as [x A o k|x y' A B [x' b0] k|A o]; simpl in *.
  - (* LET *)
    destruct Hwf as [Ho Hk].
    pose proof (lines_ok_line_ok P [] _ _ Hok) as Hline.
    rewrite app_nil_r /= in Hline.
    destruct (frame_stack_snoc_deduce P A (just_of_op o) x)
      as (fr0 & rest0 & Hfs0 & Hfs1).
    rewrite Hfs in Hfs0. injection Hfs0 as <- <-.
    rewrite cons_middle app_assoc in Hok Hnd.
    destruct (IH k _ y R ((LVar x, TFrml A) :: Γ) _ rest Hok Hnd Hk Hfs1)
      as [Hk' (L & S & HL)]; [by apply ctx_ok_add|].
    split.
    + constructor; [|done]. rewrite -Ho. apply (just_ok_typed P); [|done].
      by rewrite Hfs.
    + exists ((A, x) :: L), S. by rewrite cons_middle app_assoc HL -app_assoc.
  - (* LET SUB *)
    destruct Hwf as (HB & Hb0 & Hk).
    assert (∀ X, P ++ ((Raise A x' :: ⦇b0⦈ y' ++ [ScopeClose x y'])
                       ++ ⦇k⦈ y) ++ X =
                 (P ++ [Raise A x']) ++ ⦇b0⦈ y' ++
                 ScopeClose x y' :: ⦇k⦈ y ++ X) as Heq1.
    { intros X. by rewrite -!app_assoc /= -!app_assoc. }
    destruct (IH b0 (P ++ [Raise A x']) y' (ScopeClose x y' :: ⦇k⦈ y ++ R)
                ((LVar x', TFrml A) :: Γ) (mkFrame [(A, x')] []) (fr :: rest))
      as [Hb0' (L0 & S0 & HL0)].
    { by rewrite -Heq1. }
    { by rewrite -Heq1. }
    { done. }
    { by rewrite frame_stack_snoc_raise Hfs. }
    { by apply ctx_ok_push. }
    (* the parameter is the name of the subroutine *)
    pose proof (lines_ok_line_ok _ _ _ _ (eq_rect _ lines_ok Hok _ (Heq1 R)))
      as [_ Hline].
    rewrite HL0 /= in Hline. destruct Hline as [[= <-] _].
    (* the frame stack after the subroutine *)
    assert (∀ X, P ++ ((Raise A x' :: ⦇b0⦈ y' ++ [ScopeClose x' y'])
                       ++ ⦇k⦈ y) ++ X =
                 (P ++ Raise A x' :: ⦇b0⦈ y' ++ [ScopeClose x' y'])
                 ++ ⦇k⦈ y ++ X) as Heq2.
    { intros X. by rewrite -!app_assoc. }
    rewrite Heq2 in Hok Hnd.
    destruct (frame_stack_closed_block P A x' (⦇b0⦈ y') y')
      as (fr2 & rest2 & f2 & j & Hfs2 & Hlast & Hfs3).
    { by eapply prefix_lines_ok. }
    { rewrite lines_of_prededuct_app in Hnd. by apply NoDup_app in Hnd as [? _]. }
    rewrite Hfs in Hfs2. injection Hfs2 as <- <-.
    rewrite last_deduct_of_body in Hlast. injection Hlast as <- _ .
    destruct (IH k _ y R ((SVar x' y', TSub A B) :: Γ) _ rest Hok Hnd Hk Hfs3)
      as [Hk' (L & S & HL)]; [rewrite HB; by apply ctx_ok_close|].
    split.
    + constructor; [|done]. by rewrite HB.
    + exists L, S. rewrite -HL. f_equal. by rewrite -!app_assoc /= -!app_assoc.
  - (* RETURN *)
    pose proof (lines_ok_line_ok P [] _ _ Hok) as Hline.
    rewrite app_nil_r /= in Hline.
    split.
    + constructor. rewrite -Hwf. apply (just_ok_typed P); [|done].
      by rewrite Hfs.
    + destruct (frame_stack_snoc_deduce P A (just_of_op o) y)
        as (fr0 & rest0 & Hfs0 & Hfs1).
      rewrite Hfs in Hfs0. injection Hfs0 as <- <-. eauto.
Qed.

Fixpoint prog_ret_ty (p : prog) : frml :=
  match p with
  | PVar _ _ p' => prog_ret_ty p'
  | PBody _ b => ret_ty b
  end.

Lemma prog_typed_of_deduct p : ∀ P Γ,
  lines_ok (P ++ ⦇p⦈ᶜ) ->
  NoDup (lines_of_prededuct (P ++ ⦇p⦈ᶜ)) ->
  prog_wf p ->
  ctx_ok (frame_stack P) Γ ->
  prog_typed Γ p (prog_ret_ty p).
Proof.
  induction p as [x A p IH|y b]; intros P Γ Hok Hnd Hwf Hctx; simpl in *.
  - constructor. rewrite cons_middle app_assoc in Hok Hnd.
    apply (IH (P ++ [Assume A x])); [done..|].
    rewrite frame_stack_snoc (frame_step_adds _ _ _ A x); [|constructor].
    destruct (frame_stack P) as [|fr rest] eqn:Hfs;
      [by destruct (frame_stack_nonempty P)|].
    by apply ctx_ok_add.
  - constructor.
    destruct (frame_stack P) as [|fr rest] eqn:Hfs;
      [by destruct (frame_stack_nonempty P)|].
    rewrite -(app_nil_r (⦇b⦈ y)) in Hok Hnd.
    by eapply body_typed_of_deduct.
Qed.

(** ** Validity *)

Theorem term_of_deduct_ok Σ C :
  is_deduct Σ -> conclusion_of Σ = Some C -> prog_ok ⟦Σ⟧ᶜ C.
Proof.
  intros HΣ HC. pose proof (deduct_of_term_of_deduct Σ HΣ) as Hrt.
  destruct HΣ as (Hok & _ & Hnd & _).
  assert (prog_typed [] ⟦Σ⟧ᶜ (prog_ret_ty ⟦Σ⟧ᶜ)) as Hty.
  { apply (prog_typed_of_deduct _ []); rewrite /= ?Hrt //.
    - apply term_of_deduct_wf.
    - split; simpl; set_solver. }
  pose proof (deduct_of_term_conclusion _ _ _ Hty) as HC'.
  rewrite Hrt HC in HC'. injection HC' as ->.
  split; [|done]. rewrite /names_unique -lines_of_deduct_of_term. by rewrite Hrt.
Qed.

(** * Translations on the level of contexts *)

(** The translation of a context: the lines before and after the hole,
    and the id of the return of the (sub)proof that contains the hole *)
Definition item_ret (y : id) (Ei : ectx_item) : id :=
  match Ei with
  | CSubBody _ y' _ _ _ => y'
  | _ => y
  end.

Definition item_pre (Ei : ectx_item) : prededuct :=
  match Ei with
  | CLet x A o => [Deduce A (just_of_op o) x]
  | CSubBody x _ A _ _ => [Raise A x]
  | CSubCont x y A _ s => deduct_of_sub x y A s
  end.

Definition item_post (y : id) (Ei : ectx_item) : prededuct :=
  match Ei with
  | CSubBody x y' _ _ k => ScopeClose x y' :: ⦇k⦈ y
  | _ => []
  end.

Definition ectx_ret (y : id) (E : ectx) : id := foldl item_ret y E.

Definition ectx_pre (E : ectx) : prededuct := E ≫= item_pre.

Fixpoint ectx_post (y : id) (E : ectx) : prededuct :=
  match E with
  | [] => []
  | Ei :: E => ectx_post (item_ret y Ei) E ++ item_post y Ei
  end.

Lemma deduct_of_body_fill_item y Ei b :
  ⦇fill_item Ei b⦈ y =
  item_pre Ei ++ ⦇b⦈ (item_ret y Ei) ++ item_post y Ei.
Proof. destruct Ei; simpl; by rewrite ?app_nil_r -?app_assoc. Qed.

Lemma deduct_of_body_fill y E b :
  ⦇fill E b⦈ y =
  ectx_pre E ++ ⦇b⦈ (ectx_ret y E) ++ ectx_post y E.
Proof.
  revert y. induction E as [|Ei E IH]; intros y; [by rewrite /= app_nil_r|].
  rewrite fill_cons deduct_of_body_fill_item IH /ectx_pre bind_cons /=.
  by rewrite -!app_assoc.
Qed.

Lemma deduct_of_let z x A o k :
  ⦇BLet x A o k⦈ z = Deduce A (just_of_op o) x :: ⦇k⦈ z.
Proof. done. Qed.

Lemma deduct_of_letsub z x y A B s k :
  ⦇BLetSub x y A B (mkSubr x s) k⦈ z =
  [Raise A x] ++ ⦇s⦈ y ++ [ScopeClose x y] ++ ⦇k⦈ z.
Proof. simpl. by rewrite -app_assoc. Qed.

Lemma not_closing_deduct_of_body y b : not_closing (⦇b⦈ y).
Proof. destruct b as [|???? [] ?|]; by eexists. Qed.

(** * Translation and references *)

Lemma op_vars_refs o l :
  l ∈ references_in_just (just_of_op o) -> ∃ v, v ∈ op_vars o ∧ l ∈ var_ids v.
Proof.
  intros Hl. cut (l ∈ op_vars o ≫= var_ids).
  { rewrite list_elem_of_bind. naive_solver. }
  revert Hl.
  destruct o; repeat match goal with v : var |- _ => destruct v end;
    simpl; set_solver.
Qed.

Lemma op_vars_refs_rev o v :
  v ∈ op_vars o -> var_id v ∈ references_in_just (just_of_op o).
Proof.
  destruct o; repeat match goal with w : var |- _ => destruct w end;
    simpl; set_solver.
Qed.

Lemma op_refs_not_in Γ o A l :
  Γ ⊢ₒ o : A ->
  (∀ v T, v ∈ op_vars o -> (v, T) ∈ Γ -> l ∈ var_ids v -> False) ->
  l ∉ references_in_just (just_of_op o).
Proof.
  intros Ho Hl (v & Hv & Hlv)%op_vars_refs.
  destruct (op_vars_typed _ _ _ _ Ho Hv) as [T HT]. eauto.
Qed.

(** The lines referenced by the translation of a well-typed body are
    those of its free variables, or its own binders *)
Lemma deduct_of_body_refs Γ b C :
  Γ ⊢ b : C -> ∀ y l, l ∈ referenced_lines (⦇b⦈ y) ->
  (∃ v, v ∈ body_fv b ∧ l ∈ var_ids v) ∨ l ∈ body_binders b.
Proof.
  induction 1 as [Γ x A o k C _ _ IH|Γ x y' A B b k C _ IHb _ IHk|Γ A o _];
    intros y l; simpl; rewrite ?referenced_lines_app /= ?elem_of_app.
  - intros [(v & ? & ?)%op_vars_refs|Hl]; [left; set_solver|].
    destruct (IH _ _ Hl) as [(v & ? & ?)|?]; [|set_solver].
    destruct (decide (v = LVar x)) as [->|]; [set_solver|].
    left. exists v. rewrite elem_of_app list_elem_of_filter. naive_solver.
  - intros [[Hl|Hl]|Hl].
    + destruct (IHb _ _ Hl) as [(v & ? & ?)|?]; [|set_solver].
      destruct (decide (v = LVar x)) as [->|]; [set_solver|].
      left. exists v. rewrite elem_of_app !list_elem_of_filter. naive_solver.
    + set_solver.
    + destruct (IHk _ _ Hl) as [(v & ? & ?)|?]; [|set_solver].
      destruct (decide (v = SVar x y')) as [->|]; [set_solver|].
      left. exists v. rewrite elem_of_app !list_elem_of_filter. naive_solver.
  - intros [(v & ? & ?)%op_vars_refs|?]; [left; eauto|set_solver].
Qed.

Lemma deduct_of_body_refs_ctx Γ b C y l :
  Γ ⊢ b : C -> l ∈ referenced_lines (⦇b⦈ y) ->
  (∃ v T, v ∈ body_fv b ∧ (v, T) ∈ Γ ∧ l ∈ var_ids v) ∨
  l ∈ body_binders b.
Proof.
  intros Hb Hl. destruct (deduct_of_body_refs _ _ _ Hb _ _ Hl) as [(v & ? & ?)|?];
    [left|by right].
  destruct (body_fv_typed _ _ _ _ Hb ltac:(done)) as [T ?]. eauto.
Qed.

(** The lines referenced after the hole *)
Lemma item_post_refs Γ Ei b C y l :
  body_typed Γ (fill_item Ei b) C -> l ∈ referenced_lines (item_post y Ei) ->
  l ∈ ctx_ids Γ ∨ l ∈ item_pre_binders Ei ∨ l ∈ item_post_binders Ei.
Proof.
  destruct Ei as [|x y' A B k|]; simpl; [set_solver| |set_solver].
  inversion 1; subst. rewrite !elem_of_cons. intros [->|[->|Hl]]; [set_solver..|].
  destruct (deduct_of_body_refs_ctx _ _ _ _ _ ltac:(eassumption) Hl)
    as [(v & T & _ & HvT & Hlv)|]; [|set_solver].
  apply elem_of_cons in HvT as [[= -> ->]|HvT]; [set_solver|].
  left. apply elem_of_ctx_ids. eauto.
Qed.

Lemma ectx_post_refs Γ E b C y l :
  body_typed Γ (fill E b) C -> l ∈ referenced_lines (ectx_post y E) ->
  l ∈ ctx_ids Γ ∨ l ∈ ectx_pre_binders E ∨ l ∈ ectx_post_binders E.
Proof.
  revert Γ C y. induction E as [|Ei E IH]; intros Γ C y Hb; [set_solver|].
  destruct (fill_item_typed _ _ _ _ Hb) as (Γ' & C' & Hb' & Hids' & _).
  cbn [ectx_post]. rewrite referenced_lines_app elem_of_app.
  rewrite ectx_pre_binders_cons ectx_post_binders_cons !elem_of_app.
  intros [Hl|Hl].
  - destruct (IH _ _ _ Hb' Hl) as [[|]%Hids'|]; set_solver.
  - destruct (item_post_refs _ _ _ _ _ _ Hb Hl); set_solver.
Qed.

Lemma body_refs_not_in Γ b C y l :
  Γ ⊢ b : C ->
  (∀ v T, v ∈ body_fv b -> (v, T) ∈ Γ -> l ∈ var_ids v -> False) ->
  l ∉ body_binders b ->
  l ∉ referenced_lines (⦇b⦈ y).
Proof.
  intros Hb Hl Hbind Hr.
  by destruct (deduct_of_body_refs_ctx _ _ _ _ _ Hb Hr)
    as [(v & T & ? & ? & ?)|]; eauto.
Qed.

(** Free variables are referenced in the translation *)
Lemma body_fv_refs Γ b C :
  Γ ⊢ b : C -> ∀ y v, v ∈ body_fv b ->
  var_id v ∈ referenced_lines (⦇b⦈ y).
Proof.
  induction 1 as [Γ x A o k C _ _ IH|Γ x y' A B b k C _ IHb _ IHk|Γ A o _];
    intros y v; simpl; rewrite ?elem_of_app ?list_elem_of_filter.
  - intros [Hv|[_ Hv]]; [left; by apply op_vars_refs_rev|right; by apply IH].
  - rewrite !referenced_lines_app /=.
    intros [[_ Hv]|[_ Hv]]; [apply (IHb y') in Hv|apply (IHk y) in Hv]; set_solver.
  - intros Hv%op_vars_refs_rev. set_solver.
Qed.

(** The subproofs closed in a translation are named by binders *)
Lemma body_scs_binders Γ b C :
  Γ ⊢ b : C -> ∀ y a c,
  ScopeClose a c ∈ ⦇b⦈ y -> a ∈ body_binders b.
Proof.
  induction 1 as [Γ x A o k C _ _ IH|Γ x y' A B b k C _ IHb _ IHk|Γ A o _];
    intros y a c; simpl.
  - intros [[=]|Hin]%elem_of_cons. right. by eapply IH.
  - intros [[=]|Hin]%elem_of_cons. rewrite !elem_of_app in Hin.
    destruct Hin as [[Hin|[[= -> _]|[]%not_elem_of_nil]%elem_of_cons]|Hin].
    + apply IHb in Hin. set_solver.
    + set_solver.
    + apply IHk in Hin. set_solver.
  - by intros [[=]|[]%not_elem_of_nil]%elem_of_cons.
Qed.

(** * Splitting translations *)

(** A split of a translation before a line with an id is either after
    the translation, or at the start of a sub-body *)
Lemma deduct_of_body_split Γ b C :
  Γ ⊢ b : C -> ∀ y R Θ1 s Θ',
  ⦇b⦈ y ++ R = Θ1 ++ s :: Θ' -> is_Some (id_of_line s) ->
  (∃ Θ1', Θ1 = ⦇b⦈ y ++ Θ1' ∧ R = Θ1' ++ s :: Θ') ∨
  (∃ E b0, b = fill E b0 ∧ Θ1 = ectx_pre E ∧
           s :: Θ' = ⦇b0⦈ (ectx_ret y E) ++ ectx_post y E ++ R).
Proof.
  induction 1 as [Γ x B o k C Ho Hk IH|Γ x y' B C' b0 k C Hb0 IHb Hk IHk|Γ B o Ho];
    intros y R Θ1 s Θ' Heq Hs; simpl in Heq.
  - (* LET *)
    destruct Θ1 as [|s' Θ1]; simpl in Heq.
    + right. exists [], <{ LET x : B = o IN k }>. split_and!; [done|done|].
      simpl. congruence.
    + injection Heq as <- Heq.
      destruct (IH y R Θ1 s Θ' Heq Hs)
        as [(Θ1' & -> & ->)|(E & b0 & -> & -> & HE)].
      * left. by exists Θ1'.
      * right. exists (CLet x B o :: E), b0. split_and!; [done|done|].
        rewrite HE. cbn [ectx_post item_post item_ret]. by rewrite app_nil_r.
  - (* LET SUB *)
    rewrite -!app_assoc /= in Heq.
    destruct Θ1 as [|s' Θ1]; simpl in Heq.
    + right. exists [], (BLetSub x y' B C' (mkSubr x b0) k).
      split_and!; [done|done|]. rewrite /= -!app_assoc /=. congruence.
    + injection Heq as <- Heq.
      destruct (IHb y' (ScopeClose x y' :: ⦇k⦈ y ++ R) Θ1 s Θ' Heq Hs)
        as [(Θ1' & -> & HR)|(E & b1 & -> & -> & HE)].
      * destruct Θ1' as [|s'' Θ1']; simpl in HR.
        { injection HR as <- _. by destruct Hs. }
        injection HR as <- HR.
        destruct (IHk y R Θ1' s Θ' HR Hs)
          as [(Θ1'' & -> & ->)|(E & b1 & -> & -> & HE)].
        -- left. exists Θ1''. by rewrite /= -!app_assoc.
        -- right. exists (CSubCont x y' B C' (mkSubr x b0) :: E), b1.
           split_and!; [done|by rewrite /ectx_pre bind_cons /= -!app_assoc|].
           rewrite HE. cbn [ectx_post item_post item_ret]. by rewrite app_nil_r.
      * right. exists (CSubBody x y' B C' k :: E), b1.
        split_and!; [done|by rewrite /ectx_pre bind_cons|].
        rewrite HE. cbn [ectx_post item_post item_ret]. by rewrite -!app_assoc.
  - (* RETURN *)
    destruct Θ1 as [|s' Θ1]; simpl in Heq.
    + right. exists [], (BRet B o). split_and!; [done|done|].
      simpl. congruence.
    + injection Heq as <- Heq. left. by exists Θ1.
Qed.

(** What follows a hole is empty or starts by closing a subproof *)
Lemma ectx_post_not_closing y E R :
  ¬ not_closing R -> ¬ not_closing (ectx_post y E ++ R).
Proof.
  revert y R. induction E as [|Ei E IH]; intros y R HR; [done|].
  cbn [ectx_post]. rewrite -app_assoc. apply IH.
  destruct Ei; [exact HR| |exact HR].
  intros [? Hc]. by simpl in Hc.
Qed.

(** What follows a hole is empty, or closes the subproof whose last
    line is the return of the hole *)
Lemma ectx_post_ret y E :
  (ectx_post y E = [] ∧ ectx_ret y E = y) ∨
  ectx_ret y E ∈ referenced_lines (ectx_post y E).
Proof.
  revert y. induction E as [|Ei E IH]; intros y; [by left|].
  change (ectx_ret y (Ei :: E)) with (ectx_ret (item_ret y Ei) E).
  cbn [ectx_post]. rewrite referenced_lines_app elem_of_app.
  destruct (IH (item_ret y Ei)) as [[-> ->]|?]; [|by right; left].
  destruct Ei as [|x y' A B k|]; simpl; [by left|right; right; set_solver|by left].
Qed.

Lemma ectx_post_scs Γ E b C y a c :
  body_typed Γ (fill E b) C -> ScopeClose a c ∈ ectx_post y E ->
  a ∈ ectx_pre_binders E ∨ a ∈ ectx_post_binders E.
Proof.
  revert Γ C y. induction E as [|Ei E IH]; intros Γ C y Hb;
    [by intros []%not_elem_of_nil|].
  destruct (fill_item_typed _ _ _ _ Hb) as (Γ' & C' & Hb' & _ & _).
  cbn [ectx_post]. rewrite ectx_pre_binders_cons ectx_post_binders_cons !elem_of_app.
  intros [Hin|Hin]; [destruct (IH _ _ _ Hb' Hin); auto|].
  destruct Ei as [|x y' A B k|]; simpl in Hin; [set_solver| |set_solver].
  rewrite fill_cons /= in Hb. apply letsub_typed_inv in Hb as (_ & _ & Hk).
  apply elem_of_cons in Hin as [[= -> _]|Hin]; [set_solver|].
  right. right. simpl. right. by eapply body_scs_binders.
Qed.

(** Splitting at the closing line of the subproof [x] *)
Lemma split_scope_close Γ s C x y y0 R Θ2 Θ3 :
  Γ ⊢ s : C ->
  ⦇s⦈ y ++ ScopeClose x y :: R = Θ2 ++ ScopeClose x y0 :: Θ3 ->
  x ∉ body_binders s ->
  (∀ a c, ScopeClose a c ∈ R -> a ≠ x) ->
  Θ2 = ⦇s⦈ y ∧ y0 = y ∧ Θ3 = R.
Proof.
  intros Hs Heq Hx HR.
  destruct (app_cons_unique (λ w, ∃ c, w = ScopeClose x c) _ _ _ _ _ _ Heq)
    as (<- & [= <-] & <-); [eauto|eauto| | |done].
  - intros w Hw (c & ->). by apply Hx, (body_scs_binders _ _ _ Hs y _ c).
  - intros w Hw (c & ->). by apply (HR x c).
Qed.

(** The side condition of [split_scope_close] for a continuation [k]
    followed by [post] *)
Lemma deduct_of_body_scs_not Γ k C z post x :
  Γ ⊢ k : C -> x ∉ body_binders k ->
  (∀ a c, ScopeClose a c ∈ post -> a ≠ x) ->
  ∀ a c, ScopeClose a c ∈ ⦇k⦈ z ++ post -> a ≠ x.
Proof.
  intros Hk Hx Hpost a c [Ha|Ha]%elem_of_app ->.
  - by apply Hx, (body_scs_binders _ _ _ Hk z _ c).
  - by apply (Hpost x c).
Qed.

(** * Translations of well-typed programs are valid deductions *)

(** The converse of [ctx_ok]: the lines and subproofs in the typing
    context [Γ] are in the scope of the frame stack [fs] *)
Definition ctx_in_scope (fs : list frame) (Γ : ctx) : Prop :=
  (∀ f i, (LVar i, TFrml f) ∈ Γ -> (f, i) ∈ concat (frame_lines <$> fs)) ∧
  (∀ f1 i f2 j, (SVar i j, TSub f1 f2) ∈ Γ ->
     SubProof f1 i f2 j ∈ concat (frame_subproofs <$> fs)).

Lemma ctx_in_scope_add fr rest Γ A x :
  ctx_in_scope (fr :: rest) Γ ->
  ctx_in_scope (mkFrame (frame_lines fr ++ [(A, x)]) (frame_subproofs fr) :: rest)
    ((LVar x, TFrml A) :: Γ).
Proof.
  intros [Hl Hs]. split; simpl.
  - intros f i [[= -> ->]|Hi%Hl]%elem_of_cons; set_solver.
  - intros f1 i f2 j [[=]|Hi%Hs]%elem_of_cons. done.
Qed.

Lemma ctx_in_scope_push fs Γ A x :
  ctx_in_scope fs Γ ->
  ctx_in_scope (mkFrame [(A, x)] [] :: fs) ((LVar x, TFrml A) :: Γ).
Proof.
  intros [Hl Hs]. split; simpl.
  - intros f i [[= -> ->]|Hi%Hl]%elem_of_cons; set_solver.
  - intros f1 i f2 j [[=]|Hi%Hs]%elem_of_cons. done.
Qed.

Lemma ctx_in_scope_close fr rest Γ A x B y :
  ctx_in_scope (fr :: rest) Γ ->
  ctx_in_scope (mkFrame (frame_lines fr) (frame_subproofs fr ++ [SubProof A x B y]) :: rest)
    ((SVar x y, TSub A B) :: Γ).
Proof.
  intros [Hl Hs]. split; simpl.
  - intros f i [[=]|Hi%Hl]%elem_of_cons. done.
  - intros f1 i f2 j [[= -> -> -> ->]|Hi%Hs]%elem_of_cons; set_solver.
Qed.

Lemma ctx_in_scope_extend fr rest Γ L S :
  ctx_in_scope (fr :: rest) Γ ->
  ctx_in_scope (mkFrame (frame_lines fr ++ L) (frame_subproofs fr ++ S) :: rest) Γ.
Proof.
  intros [Hl Hs]. split; simpl.
  - intros f i Hi%Hl. set_solver.
  - intros f1 i f2 j Hi%Hs. set_solver.
Qed.

(** The converse of [just_ok_typed] *)
Lemma just_ok_of_typed pre Γ o f :
  ctx_in_scope (frame_stack pre) Γ -> Γ ⊢ₒ o : f -> just_ok pre f (just_of_op o).
Proof.
  intros [Hl Hs]. rewrite /just_ok /scope /sp_scope.
  destruct 1; simpl; eauto 10.
Qed.

(** The translation of a well-typed body is valid after any valid
    prefix [P] whose scope contains the context. Moreover, the body
    extends the top frame. *)
Lemma deduct_of_body_lines_ok Γ b C :
  Γ ⊢ b : C -> ∀ P y fr rest,
  lines_ok P ->
  NoDup (lines_of_prededuct (P ++ ⦇b⦈ y)) ->
  frame_stack P = fr :: rest ->
  ctx_in_scope (fr :: rest) Γ ->
  lines_ok (P ++ ⦇b⦈ y) ∧
  ∃ L S, frame_stack (P ++ ⦇b⦈ y) =
         mkFrame (frame_lines fr ++ L) (frame_subproofs fr ++ S) :: rest.
Proof.
  induction 1 as [Γ x A o k C Ho Hk IH|Γ x y' A B b k C Hb IHb Hk IHk|Γ A o Ho];
    intros P y fr rest Hok Hnd Hfs Hctx.
  - (* LET *)
    rewrite deduct_of_let cons_middle app_assoc in Hnd |- *.
    destruct (frame_stack_snoc_deduce P A (just_of_op o) x) as (? & ? & Hfs' & Hfs1).
    rewrite Hfs in Hfs'. injection Hfs' as <- <-.
    destruct (IH (P ++ [Deduce A (just_of_op o) x]) y
                (mkFrame (frame_lines fr ++ [(A, x)]) (frame_subproofs fr)) rest)
      as [Hok' (L & S & HL)];
      [|done|done|by apply ctx_in_scope_add|].
    { apply lines_ok_cons; [done|]. apply (just_ok_of_typed _ Γ); [by rewrite Hfs|done]. }
    split; [done|]. exists ((A, x) :: L), S. by rewrite HL /= -app_assoc.
  - (* LET SUB *)
    rewrite deduct_of_letsub in Hnd |- *.
    assert (P ++ [Raise A x] ++ ⦇b⦈ y' ++ [ScopeClose x y'] ++ ⦇k⦈ y =
            (((P ++ [Raise A x]) ++ ⦇b⦈ y') ++ [ScopeClose x y']) ++ ⦇k⦈ y) as Heq
      by (by rewrite -!app_assoc).
    rewrite Heq in Hnd |- *.
    (* the body of the subproof, in a new frame *)
    destruct (IHb (P ++ [Raise A x]) y' (mkFrame [(A, x)] []) (fr :: rest))
      as [Hok1 (L & S & HL)].
    { by apply lines_ok_cons. }
    { by do 2 eapply nodup_lines_prefix. }
    { by rewrite frame_stack_snoc_raise Hfs. }
    { by apply ctx_in_scope_push. }
    (* closing the subproof *)
    assert (Hlast : last ((P ++ [Raise A x]) ++ ⦇b⦈ y') =
                    Some (Deduce B (just_of_op (ret_op b)) y')).
    { by rewrite last_app last_deduct_of_body (body_typed_ret_ty _ _ _ Hb). }
    assert (Hok2 : lines_ok (((P ++ [Raise A x]) ++ ⦇b⦈ y') ++ [ScopeClose x y'])).
    { apply lines_ok_cons; [done|].
      destruct (frame_stack_last_deduce _ _ _ _ Hlast) as (? & ? & Hfs0 & Hl0).
      rewrite HL in Hfs0. injection Hfs0 as <- <-.
      rewrite /line_ok Hlast HL /=. simpl in Hl0. by rewrite Hl0. }
    assert (((P ++ [Raise A x]) ++ ⦇b⦈ y') ++ [ScopeClose x y'] =
            P ++ Raise A x :: ⦇b⦈ y' ++ [ScopeClose x y']) as Heq'
      by (by rewrite -!app_assoc).
    rewrite Heq' in Hnd Hok2 |- *.
    destruct (frame_stack_closed_block P A x (⦇b⦈ y') y')
      as (? & ? & f2 & j & Hfs' & Hlast' & Hfs2); [done|by eapply nodup_lines_prefix|].
    rewrite Hfs in Hfs'. injection Hfs' as <- <-.
    rewrite last_deduct_of_body (body_typed_ret_ty _ _ _ Hb) in Hlast'.
    injection Hlast' as <- _.
    (* the continuation, which can use the subproof *)
    destruct (IHk (P ++ Raise A x :: ⦇b⦈ y' ++ [ScopeClose x y']) y
                (mkFrame (frame_lines fr) (frame_subproofs fr ++ [SubProof A x B y'])) rest)
      as [Hok3 (L' & S' & HL')]; [done|done|done|by apply ctx_in_scope_close|].
    split; [done|]. exists L', (SubProof A x B y' :: S'). by rewrite HL' /= -app_assoc.
  - (* RETURN *)
    destruct (frame_stack_snoc_deduce P A (just_of_op o) y) as (? & ? & Hfs' & Hfs1).
    rewrite Hfs in Hfs'. injection Hfs' as <- <-. simpl.
    split.
    + apply lines_ok_cons; [done|]. apply (just_ok_of_typed _ Γ); [by rewrite Hfs|done].
    + exists [(A, y)], []. by rewrite Hfs1 app_nil_r.
Qed.

(** The translation of a well-typed program is valid after any prefix
    of assumptions whose scope contains the context *)
Lemma deduct_of_term_lines_ok Γ p C :
  Γ ⊢ₚ p : C -> ∀ P,
  lines_ok P -> Forall is_assume P ->
  NoDup (lines_of_prededuct (P ++ ⦇p⦈ᶜ)) ->
  ctx_in_scope (frame_stack P) Γ ->
  lines_ok (P ++ ⦇p⦈ᶜ) ∧ length (frame_stack (P ++ ⦇p⦈ᶜ)) = 1.
Proof.
  induction 1 as [Γ x A p C _ IH|Γ y b C Hb]; intros P Hok Has Hnd Hctx;
    destruct (assume_run_stack P Has) as [base Hfs]; simpl in Hnd |- *.
  - rewrite cons_middle app_assoc in Hnd |- *. apply IH; [| |done|].
    + by apply lines_ok_cons.
    + apply Forall_app. by split; [|apply Forall_singleton].
    + rewrite frame_stack_snoc (frame_step_adds _ _ _ A x); [|constructor].
      rewrite Hfs. apply ctx_in_scope_add. by rewrite -Hfs.
  - destruct (deduct_of_body_lines_ok _ _ _ Hb P y base [])
      as [? (L & S & ->)]; [done|done|done|by rewrite -Hfs|]. done.
Qed.

Theorem deduct_of_term_ok p C : prog_ok p C -> is_deduct ⦇p⦈ᶜ.
Proof.
  intros [Hnd Hty].
  destruct (deduct_of_term_lines_ok _ _ _ Hty []) as [Hok Hlen].
  - constructor.
  - constructor.
  - by rewrite /= lines_of_deduct_of_term.
  - split; intros *; set_solver.
  - split_and!; [done|done|by rewrite lines_of_deduct_of_term|].
    by erewrite deduct_of_term_conclusion.
Qed.

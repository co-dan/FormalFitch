(* Translations between Fitch (pre)deductions and LetLang programs *)
From stdpp Require Import list.
From fitch Require Import prelude core deduction_lemmas.

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

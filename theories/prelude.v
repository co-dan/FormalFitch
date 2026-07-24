From stdpp Require Export ssreflect.

(** nodup *)

Lemma NoDup_app_remove_mid {A} (l1 l2 l3 : list A) : NoDup (l1 ++ l2 ++ l3) -> NoDup (l1 ++ l3).
Proof.
  rewrite !NoDup_app. intros (Hnd1 & Hno & _ & _ & Hnd3).
  split; [done|]. split; [|done].
  intros x Hx1 Hx3. eapply Hno; [done|]. apply elem_of_app. by right.
Qed.

Lemma NoDup_app_remove_l {A} (l1 l2 : list A) : NoDup (l1 ++ l2) -> NoDup l2.
Proof. rewrite NoDup_app. tauto. Qed.

Lemma NoDup_app_remove_r {A} (l1 l2 : list A) : NoDup (l1 ++ l2) -> NoDup l1.
Proof. rewrite NoDup_app. tauto. Qed.

Lemma NoDup_app_elem_of {A} (l k : list A) : NoDup (l ++ k) → (∀ x, x ∈ l → x ∉ k).
Proof. rewrite NoDup_app. tauto. Qed.

Lemma NoDup_app_elem_of_2 {A} (l k : list A) : NoDup (l ++ k) → (∀ x, x ∈ k → x ∉ l).
Proof.
  rewrite NoDup_app. intros (_ & H & _) x Hx Hl. by eapply H.
Qed.

Lemma NoDup_app_two_prefix {A : Type} (xs ys : list A) (a b : A) :
  NoDup (xs ++ [a; b] ++ ys) ->
  NoDup (xs ++ [a]).
Proof.
  intros H.
  apply (NoDup_app_remove_r (xs ++ [a]) (b :: ys)).
  replace ((xs ++ [a]) ++ b :: ys) with (xs ++ [a; b] ++ ys)
    by (rewrite -app_assoc; reflexivity).
  exact H.
Qed.

Lemma NoDup_app_two_second_fresh {A : Type} (xs ys : list A) (a b : A) :
  NoDup (xs ++ [a; b] ++ ys) ->
  b ∉ xs ++ [a].
Proof.
  intros H Hin.
  assert (H' : NoDup ((xs ++ [a]) ++ b :: ys)).
  { replace ((xs ++ [a]) ++ b :: ys) with (xs ++ [a; b] ++ ys)
      by (rewrite -app_assoc; reflexivity).
    exact H. }
  rewrite NoDup_app in H'. destruct H' as (_ & Hsep & _).
  eapply Hsep; [exact Hin|].
  apply elem_of_cons. by left.
Qed.

Lemma NoDup_app_two_swap_prefix {A : Type} (xs ys : list A) (a b : A) :
  NoDup (xs ++ [a; b] ++ ys) ->
  a <> b ->
  NoDup (xs ++ [b; a]).
Proof.
  intros H Hab.
  rewrite NoDup_app.
  assert (H' : NoDup (xs ++ [a; b] ++ ys)) by exact H.
  rewrite NoDup_app in H'. destruct H' as (Hxs & Hsep & _).
  split; [exact Hxs|]. split.
  - intros x Hx Hin.
    apply (Hsep x Hx). simpl in Hin |- *.
    rewrite !elem_of_cons !elem_of_nil in Hin |- *.
    naive_solver.
  - repeat constructor.
    + intros Hin. apply list_elem_of_singleton in Hin. congruence.
    + apply not_elem_of_nil.
Qed.

(* When [f] is injective on the elements of [l] (witnessed by [f <$> l]
   having no duplicates), equal images come from equal elements. *)
Lemma NoDup_fmap_elem_inj {A B} (f : A -> B) (l : list A) x y :
  NoDup (f <$> l) -> x ∈ l -> y ∈ l -> f x = f y -> x = y.
Proof.
  intros Hnd Hx Hy Hfxy.
  apply list_elem_of_lookup_1 in Hx as [i Hi].
  apply list_elem_of_lookup_1 in Hy as [j Hj].
  assert (Hfi : (f <$> l) !! i = Some (f x)) by (rewrite list_lookup_fmap Hi //).
  assert (Hfj : (f <$> l) !! j = Some (f y)) by (rewrite list_lookup_fmap Hj //).
  rewrite Hfxy in Hfi.
  assert (i = j) as -> by (eapply NoDup_lookup; eauto).
  rewrite Hi in Hj. by simplify_eq.
Qed.

Lemma submseteq_NoDup {A} (l k : list A) :
  l ⊆+ k -> NoDup k -> NoDup l.
Proof.
  intros [l2 [Hsub Hperm]]%submseteq_sublist_l Hk.
  eapply sublist_NoDup; [|exact Hsub]. by rewrite Hperm.
Qed.




(** snoc etc *)

Definition but_last {A} (l : list A) : list A :=
  reverse (tail (reverse l)).

Definition unsnoc {A} (l : list A) : option (list A * A) :=
  match (last l) with
  | Some s => Some (but_last l, s)
  | None => None
  end.

Lemma but_last_snoc {A} (xs : list A) x :
  but_last (xs ++ [x]) = xs.
Proof.
  unfold but_last.
  rewrite reverse_snoc. simpl.
  apply reverse_involutive.
Qed.

Lemma unsnoc_Some {A} (x : A) xs xs' :
  unsnoc xs = Some (xs', x)  -> xs = xs' ++ [x].
Proof.
  unfold unsnoc.
  destruct (last xs) as [y|] eqn:Hlast; [|done].
  intros Hsome. injection Hsome as <- <-.
  apply last_Some in Hlast as [ys ->].
  by rewrite but_last_snoc.
Qed.

Lemma unsnoc_None {A} (xs : list A) :
  unsnoc xs = None -> xs = [].
Proof.
  destruct xs as [|x xs]; [done|].
  unfold unsnoc. destruct (last (x :: xs)) eqn:Hlast; [done|].
  exfalso.
  destruct xs as [|y xs] using rev_ind.
  - done.
  - rewrite app_comm_cons in Hlast.
    rewrite last_snoc in Hlast. done.
Qed.

Lemma unsnoc_length {A} x (xs xs' : list A) :
  unsnoc xs = Some (xs', x)  -> length xs' < length xs.
Proof.
  intros ->%unsnoc_Some.
  rewrite length_app. simpl. lia.
Qed.

Lemma unsnoc_snoc {A} (xs : list A) x :
  unsnoc (xs ++ [x]) = Some (xs, x).
Proof.
  unfold unsnoc.
  rewrite last_snoc.
  by rewrite but_last_snoc.
Qed.


Lemma not_nil_snoc {A} (xs : list A) :
  xs ≠ [] -> ∃ xs' x, xs = xs' ++ [x].
Proof.
  intros Hne.
  destruct (unsnoc xs) as [[xs' x]|] eqn:Hsplit.
  - exists xs', x. by apply unsnoc_Some.
  - apply unsnoc_None in Hsplit. done.
Qed.


(** misc *)
Lemma not_elem_of_sublist {A : Type} (l1 l2 : list A) (x : A) :
  x ∉ l2 → l1 `sublist_of` l2 → x ∉ l1.
Proof.
  intros H2 Hs H1.
  eapply elem_of_sublist in H1; eauto.
Qed.



Lemma perm_app_interleave {A} (a b c d e : list A) :
  (a ++ b) ++ (c ++ d) ++ e ≡ₚ (a ++ c) ++ b ++ d ++ e.
Proof.
  rewrite <- !app_assoc.
  apply Permutation_app; [done|].
  rewrite !app_assoc.
  rewrite (Permutation_app_comm b c).
  done.
Qed.


(** ** Lifting step-level facts along [rtc] *)

(** A version of [rtc_congruence] with an additional invariant [Q] *)
Lemma rtc_congruence' {A B} (f : A -> B) (R : relation A) (R' : relation B) (Q : A -> Prop)  :
  (forall x y, Q x -> R x y -> Q y) ->
  (forall x y, Q x -> R x y -> R' (f x) (f y)) ->
  forall x y, rtc R x y -> Q x -> rtc R' (f x) (f y).
Proof.
  intros HQ HR x y Hrtc. induction Hrtc as [|x y z Hxy Hyz IH]; [done|].
  intros Hx. econstructor; eauto.
Qed.

Lemma rtc_once_inv {A} (R : relation A) `{!Reflexive R, !Transitive R} :
  forall x y, rtc R x y -> R x y.
Proof.
  intros x y. induction 1; eauto.
Qed.

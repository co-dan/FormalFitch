From stdpp Require Export ssreflect.

(** nodup *)

Lemma NoDup_app_remove_mid {A} (l1 l2 l3 : list A) : NoDup (l1 ++ l2 ++ l3) -> NoDup (l1 ++ l3).
Proof. rewrite !NoDup_app. set_solver. Qed.

Lemma NoDup_app_remove_r {A} (l1 l2 : list A) : NoDup (l1 ++ l2) -> NoDup l1.
Proof. rewrite NoDup_app. tauto. Qed.

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
Proof. rewrite /unsnoc -last_None. by destruct (last xs). Qed.

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
Proof. intros [x [xs' ->]%last_Some]%last_is_Some. eauto. Qed.

(** misc *)

Lemma last_app_ne {A} (X Y Δ : list A) :
  Δ ≠ [] → last (X ++ Δ) = last (Y ++ Δ).
Proof. rewrite !last_app -last_is_Some. by intros [? ->]. Qed.

(** ** Local edits of lists *)

(* [list_del P L L']: [L'] is [L] with one element satisfying [P] removed. *)
Definition list_del {A} (P : A → Prop) (L L' : list A) : Prop :=
  ∃ L1 x L2, P x ∧ L = L1 ++ x :: L2 ∧ L' = L1 ++ L2.

(* [list_swap P L L']: [L'] is [L] with two adjacent elements transposed,
   the first of which satisfies [P]. *)
Definition list_swap {A} (P : A → Prop) (L L' : list A) : Prop :=
  ∃ L1 x y L2, P x ∧ L = L1 ++ x :: y :: L2 ∧ L' = L1 ++ y :: x :: L2.

(* Both edits can only change the head if the edited element was the head. *)
Lemma list_del_head {A} (P : A → Prop) L L' :
  list_del P L L' → head L' = head L ∨ ∃ x, P x ∧ head L = Some x.
Proof. intros (L1 & x & L2 & Hx & -> & ->). destruct L1; naive_solver. Qed.

Lemma list_swap_head {A} (P : A → Prop) L L' :
  list_swap P L L' → head L' = head L ∨ ∃ x, P x ∧ head L = Some x.
Proof. intros (L1 & x & y & L2 & Hx & -> & ->). destruct L1; naive_solver. Qed.

(* [list_edit R Keep]: the relation [R] is stable under appending the same
   element on both sides, and it keeps every element satisfying [Keep]. *)
Record list_edit {A} (R : relation (list A)) (Keep : A → Prop) : Prop := {
  list_edit_snoc L L' x : R L L' → R (L ++ [x]) (L' ++ [x]);
  list_edit_elem_of L L' x : R L L' → x ∈ L → Keep x → x ∈ L';
}.

Lemma list_edit_eq {A} (Keep : A → Prop) : list_edit (=) Keep.
Proof. split; naive_solver. Qed.

Lemma list_edit_eq_flip {A} (Keep : A → Prop) : list_edit (flip (=)) Keep.
Proof. split; rewrite /flip; naive_solver. Qed.

Lemma list_edit_del {A} (P : A → Prop) : list_edit (list_del P) (λ x, ¬ P x).
Proof.
  split.
  - intros L L' z (L1 & x & L2 & Hx & -> & ->).
    exists L1, x, (L2 ++ [z]). by rewrite -!app_assoc.
  - intros L L' z (L1 & x & L2 & Hx & -> & ->). set_solver.
Qed.

Lemma list_edit_ins {A} (P Keep : A → Prop) : list_edit (flip (list_del P)) Keep.
Proof.
  split; rewrite /flip.
  - intros L L' z ?. by apply (list_edit_snoc _ _ (list_edit_del P)).
  - intros L L' z (L1 & x & L2 & Hx & -> & ->). set_solver.
Qed.

Lemma list_edit_swap {A} (P Keep : A → Prop) : list_edit (list_swap P) Keep.
Proof.
  split.
  - intros L L' z (L1 & x & y & L2 & Hx & -> & ->).
    exists L1, x, y, (L2 ++ [z]). by rewrite -!app_assoc.
  - intros L L' z (L1 & x & y & L2 & Hx & -> & ->). set_solver.
Qed.

Lemma NoDup_mid {A} (I M Q : list A) l :
  NoDup (I ++ M ++ Q) -> l ∈ M -> l ∉ I ∧ l ∉ Q.
Proof. rewrite !NoDup_app. set_solver. Qed.

(** Splitting a list at the unique element with property [P] *)
Lemma app_cons_unique {A} (P : A -> Prop) (l1 l2 r1 r2 : list A) a b :
  l1 ++ a :: r1 = l2 ++ b :: r2 -> P a -> P b ->
  (∀ z, z ∈ l1 -> ¬ P z) -> (∀ z, z ∈ r1 -> ¬ P z) ->
  l1 = l2 ∧ a = b ∧ r1 = r2.
Proof.
  intros [(k & -> & Hk)|(k & -> & Hk)]%app_eq_inv Ha Hb Hl1 Hr1;
    (destruct k as [|c k]; simplify_list_eq; [done|set_solver]).
Qed.

(** Tactics for [NoDup] hypotheses *)
Ltac decompose_NoDup :=
  repeat match goal with
  | H : NoDup (_ :: _) |- _ => apply NoDup_cons in H as [? ?]
  | H : NoDup (_ ++ _) |- _ => apply NoDup_app in H as (? & ? & ?)
  end.

Ltac nodup_tac Hnd := clear - Hnd; decompose_NoDup; set_solver.

(* Reassociate list equations to the right. *)
Ltac list_assoc := simpl; repeat progress (rewrite -?app_assoc /=); try done.

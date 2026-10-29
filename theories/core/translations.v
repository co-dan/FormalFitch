(* Translations between Fitch (pre)deductions and LetLang programs *)
From stdpp Require Import list.
From fitch.core Require Import deduct letsub.
(** In this file we develop two translations:

    - ⟦ . ⟧ᶜ : Deduct → LetSub
    - ⦇ . ⦈ᶜ : LetSub → Deduct

We show that the two translations are inverses of each other, and
that the translation of a well-typed program is a deduction with
the same assumptions and conclusion.

The translation identifies Fitch line ids with LetLang variables:

The first translation ⟦ . ⟧ᶜ works as follows. Consider a generic Fitch proof:

```
     1 | P_1
     2 | P_2
     ....
     n | P_n
       |-------
    n+1| S_1   J_1
    n+2| S_2   J_2
    ....
    n+m| S_m   J_m
```

(where P's and S's are formulas, and J's are justifications)
It is translated into the following program (maybe modulo variable names):

```
    VAR y_1 : P_1;
    VAR y_2 : P_2;
    ...
    VAR y_n : P_n;
    {
      LET x_{n+1} : S_1 = ⟦J_1⟧ in
      LET x_{n_2} : S_2 = ⟦J_2⟧ in
    ...
      RETURN : S_m = ⟦J_m⟧
    } AS x_{n+m}
```

where `⟦J⟧` is the translation of the justification `J`, which is
defined as follows:

Conjunction introduction

```
    l | A ∧ B   ∧Intro:i,j
```

is translated as

```
    let x_l : A ∧ B = (x_i, x_j) ..
```

Conjunction elimination

```
    i | A ∧ B   ...
    ...
    l | A       ∧Elim:i
    ...
```

is translated as

```
    let x_l = fst(x_i) in ..
```

Implication introduction

```
    i | | A
      | |--
      | | ..
    j | | B     J_j
      ...
    k | A → B   →Intro:i-j
      ...
```

is translated as

```
    let SUB s_[i, j] : A → B = sub (var x_i) {
       ...
       RETURN : B = ⟦J_j⟧
    } in
    ...
    let x_k : A → B = func(s_[i, j])
```

Implication elimination

```
    i | A → B     J_i
    ...
    j | A         J_j
    ...
    k | B         →Elim:i,j
``

is translated as

```
    let x_k : B = apply(x_i,x_j) in ...
```

Finally, Repeat

```
    j | A     Repeat:i
```

is translated as

```
   let x_j : A = cpy(x_i)
```

The translation back works in a similar way, but
its easier to define becaues it is purely recursive.

 *)


(** * Notation *)

(** [⟦ Σ ⟧ᶜ] translates a deduction to a program, [⦇ p ⦈ᶜ] translates
    a program to a deduction, and [⦇ b ⦈ k] translates a body whose
    [RETURN] becomes the line [k]. *)
Reserved Notation "⟦ Σ ⟧ᶜ" (format "⟦ Σ ⟧ᶜ").
Reserved Notation "⦇ p ⦈ᶜ" (format "⦇ p ⦈ᶜ").
#[warnings="-level-0-notation-not-closed"]
Reserved Notation "⦇ b ⦈ k" (at level 0, k at level 0, format "⦇ b ⦈  k").

(** * From deductions to programs: ⟦ .. ⟧ᶜ *)

Definition op_of_just (J : just) : op :=
  match J with
  | Repeat l => OCpy (LVar l)
  | ConjI l1 l2 => OPair (LVar l1) (LVar l2)
  | ConjE flag l => OProj flag (LVar l)
  | ImplI l1 l2 => OFunc (SVar l1 l2)
  | ImplE l1 l2 => OApply (LVar l1) (LVar l2)
  end.

(** The type of the return of a body, useful for figuring out the
types of (sub)routines. *)
Fixpoint ret_ty (b : body) : frml :=
  match b with
  | BLet _ _ _ k | BLetSub _ _ _ _ _ k => ret_ty k
  | BRet A _ => A
  end.

(** A default body for ill-formed deductions *)
Definition junk_body : body := BRet (fAtomic "") (OCpy (LVar 0)).

(** The translation goes from the end of the proof to the beginning,
implemented using foldr. This means that the continuations in the
let-clauses are already translated when it comes to translating the
clause.

The translation keep track of the state (cur, stk) where

    - `cur` is the body translated so far, in a given (sub)proof; if
      nothig has been translated so far, that means that we are
      looking at the last line of the subproof, which should be
      translated as a return

    - `stk` keeps track of tuples `(l1, l2, k)` when we enter a
      subproof at lines `l1-l2`. I.e. suppose our state is `(cur,
      stk)` and we are looking at the closing line in the proof:

           i | | A
             | |--
          .. | | ..
           j | | B    J_j
             | ScopeClose i-j

      then we need to stop translating what we have been translating
      so far (by pushing `(i, j, cur)` onto the stack), and recursively
      translate the subproof `i-j` as a `LET SUB = { .. } in cur`
*)
Record TrState := {
    trstate_cur : option body;
    trstate_stk : list (id * id * option body);
}.

Definition term_of_deduct_step (s : line) (st : TrState) : TrState :=
  match s, trstate_cur st, trstate_stk st with
  | Deduce A J _, None, stk =>
    (* the current term is empty, so we translate
       the line as a return *)
    {| trstate_cur := Some (BRet A (op_of_just J));
       trstate_stk := stk |}
  | Deduce A J l, Some k, stk =>
    (* A single line deduction is tranlated as a let *)
    {| trstate_cur := Some (BLet l A (op_of_just J) k);
       trstate_stk := stk |}
  | ScopeClose l1 l2, cur, stk =>
    (* Entering a new subproof *)
    {| trstate_cur := None;
       trstate_stk := (l1, l2, cur) :: stk |}
  | Raise A x, Some b, (l1, l2, Some k) :: stk' =>
    (* Exiting a subproof *)
    {| trstate_cur :=
        Some (BLetSub l1 l2 A (ret_ty b) (mkSubr x b) k);
       trstate_stk := stk' |}
  | _, _, _ =>
    (* this should not happen! *)
      st
  end.

Definition term_of_deduct' Σ stk :=
  foldr term_of_deduct_step
        {| trstate_cur := None;
          trstate_stk := stk |}
        Σ.

(** The body of a deduction, ignoring its assumptions. Its return
    variable is the id of the last line. Junk for ill-formed
    deductions. *)
Definition body_of_deduct (Σ : prededuct) : body :=
  match term_of_deduct' Σ [] with
  | {| trstate_cur := Some cur; trstate_stk := [] |} =>
      cur
  | _ => (* should not happen on well-formed proofs *) junk_body
  end.

Notation "⟦ Σ ⟧" := (body_of_deduct Σ) (format "⟦ Σ ⟧").


Definition last_line_id (Σ : prededuct) : id :=
  match last Σ with
  | Some (Deduce _ _ k) => k
  | _ => 0
  end.


Fixpoint term_of_deduct (Σ : prededuct) : prog :=
  match Σ with
  | Assume A x :: Σ' => PVar x A ⟦ Σ' ⟧ᶜ
  | _ => PBody (last_line_id Σ) ⟦ Σ ⟧
  end
where "⟦ Σ ⟧ᶜ" := (term_of_deduct Σ).

(** * From programs to deductions: ⦇ .. ⦈ᶜ *)

Definition var_id (x : var) : id :=
  match x with LVar x | SVar x _ => x end.

(** Variables of the wrong kind are only possible in ill-typed
    programs; we translate them to junk *)
Definition just_of_op (o : op) : just :=
  match o with
  | OPair x y => ConjI (var_id x) (var_id y)
  | OProj flag x => ConjE flag (var_id x)
  | OFunc (SVar x y) => ImplI x y
  | OFunc (LVar x) => ImplI x x
  | OApply x y => ImplE (var_id x) (var_id y)
  | OCpy x => Repeat (var_id x)
  end.

(** [deduct_of_body k b] translates the body [b], whose [RETURN]
    becomes the line [k]. [deduct_of_sub x k A s] translates the
    subroutine [s] named [[x, y]] with parameter type [A]. *)
Fixpoint deduct_of_body (k : id) (b : body) : prededuct :=
  match b with
  | BLet x A o b =>
      Deduce A (just_of_op o) x ::
      ⦇ b ⦈ k
  | BLetSub x y A B s b =>
       deduct_of_sub x y A s ++
       ⦇ b ⦈ k
  | BRet A o => [Deduce A (just_of_op o) k]
  end
where "⦇ b ⦈ k" := (deduct_of_body k b)
with deduct_of_sub (x y : id) (A : frml) (s : subr) : prededuct :=
  match s with
  | mkSubr x' b =>
      Raise A x' ::
      ⦇ b ⦈ y ++
      [ScopeClose x y]
  end.

Fixpoint deduct_of_term (p : prog) : prededuct :=
  match p with
  | PVar x A p' => Assume A x :: ⦇ p' ⦈ᶜ
  | PBody y b => ⦇ b ⦈ y
  end
where "⦇ p ⦈ᶜ" := (deduct_of_term p).

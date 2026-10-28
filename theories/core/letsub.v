(** LetLang (λ_letsub): the computational counterpart of Fitch deductions *)
From stdpp Require Import list.
From fitch Require Import prelude deduct.

(** LetLang is based on λ-calculus with let in A-normal form. That is,
the programs of LetLang are of the form

```
    VAR y1 : A1 ;
    VAR y2 : A2 ;
    {
      LET x3 : B3 = op3(..) IN
      LET SUB [x4, x7] : A → B = SUB (VAR x4) {
         LET x5 : B5 = op5(..) IN
         ...
         RETURN : B = op7(..)
      } IN
      ...
      RETURN : C = opn(..)
    } AS xn
```

where each operation [op] is one of [(x, y)], [FST(x)], [SND(x)],
[FUNC([x, y])], [APPLY(f, x)] or [CPY(x)] applied to variables. *)



(** * Syntax *)

(** There are two kinds of variables, mirroring what a Fitch proof can
refer to. A line variable [LVar x] is a natural number/id, like a line
of a Fitch proof. A subroutine variable [SVar x y] names a subroutine
by its parameter [x] and its return variable [y], like a subproof is
referred to by the range of its lines. *)
Inductive var :=
| LVar (x : nat)
| SVar (x y : nat)
.

#[global] Instance var_eqdecision : EqDecision var.
Proof. solve_decision. Qed.

(** The are two kinds of types: formulas of intuitionistic logic, and
a primitive type of subroutines [Sub(A;B)] *)
Inductive ty :=
| TFrml : frml -> ty
| TSub : frml -> frml -> ty
.

#[global] Instance ty_eqdecision : EqDecision ty.
Proof. solve_decision. Qed.

Inductive op :=
| OPair (x y : var)   (* pairs *)
| OProj (flag : bool) (x : var) (* projections *)
| OFunc (x : var)  (* turn a subroutine into a function *)
| OApply (x y : var) (* apply a function *)
| OCpy (x : var)  (* repeat a variable *)
.

#[global] Instance op_eqdecision : EqDecision op.
Proof. solve_decision. Qed.

(** The main part of the program is the body, which is a sequence of
let-bindings in an ANF:

    - [BLet x A o k] is [LET x : A = o IN k]
    - [BLetSub x y A B s k] is [LET SUB [x, y] : A → B = s IN k]
    - [BRet A op] is [RETURN : A = op]

    A subroutine [mkSubr x b] is [SUB (VAR x) { b }]. The name [[x, y]]
    of a subroutine consists of its parameter [x] and its return
    variable [y]. The return variable is bound by the name only, the
    parameter is bound in both places; the typing judgment checks that
    they agree. *)
Inductive body :=
| BLet (x : nat) (A : frml) (o : op) (k : body)
| BLetSub (x y : nat) (A B : frml) (s : subr) (k : body)
| BRet (A : frml) (o : op)
with subr :=
| mkSubr (x : nat) (b : body)
.

Scheme body_mut := Induction for body Sort Prop
with subr_mut := Induction for subr Sort Prop.
Combined Scheme body_subr_mut from body_mut, subr_mut.

(** Programs: a sequence of parameters (translations of the top-level
    assumptions) followed by a body [PBody y b], written [{ b } AS y],
    where [y] is the return variable of the body. *)
Inductive prog :=
| PVar (x : nat) (A : frml) (p : prog)
| PBody (y : nat) (b : body)
.

(** * Notations *)

(** Programs are written between [<{ }>]. Keywords are in all caps to
    avoid clashing with Rocq's own [let], [fst], etc. Variables are
    numerals (or Rocq identifiers).

    Types are written with the formula notations above. They are parsed
    in the custom entry [letsub_frml], which duplicates [→] and [∧]: a
    [constr] at level 99 would also parse the [=] in [LET x : A = o] as
    an equality, and below level 70 it cannot contain [→] or [∧]. Any
    other term, e.g. an identifier or a parenthesized term, is parsed as
    a Rocq term with [frml_scope] open.

    <{ VAR 1 : A ;
       { LET SUB [x, y] : A → B = SUB (VAR x) { ... RETURN : B = o } IN
         LET 3 : A ∧ B = (1, 2) IN
         RETURN : A = FST(3) } AS 4 }>
*)
Declare Custom Entry letsub_frml.

Notation "A → B" := (fImpl A B)
  (in custom letsub_frml at level 99, B at level 200, right associativity).
Notation "A ∧ B" := (fConj A B)
  (in custom letsub_frml at level 80, right associativity).
Notation "A" := (A%F) (in custom letsub_frml at level 0, A constr at level 0).
Notation "( A )" := A
  (in custom letsub_frml at level 0, A custom letsub_frml at level 200, only printing).

Declare Custom Entry letsub.
Declare Custom Entry letsub_op.
Declare Custom Entry letsub_var.

Notation "<{ p }>" := p (p custom letsub at level 200, format "<{  p  }>").
Notation "x" := x (in custom letsub at level 0, x ident).
Notation "x" := x (in custom letsub_op at level 0, x ident).

(** Line variables are written as numerals, subroutine variables as
    [[x, y]] *)
Notation "x" := (LVar x) (in custom letsub_var at level 0, x constr at level 0).
Notation "[ x , y ]" := (SVar x y)
  (in custom letsub_var at level 0, x constr at level 0, y constr at level 0).

Notation "( x , y )" := (OPair x y)
  (in custom letsub_op at level 0, x custom letsub_var, y custom letsub_var).
Notation "'FST' ( x )" := (OProj true x)
  (in custom letsub_op at level 0, x custom letsub_var).
Notation "'SND' ( x )" := (OProj false x)
  (in custom letsub_op at level 0, x custom letsub_var).
Notation "'FUNC' ( f )" := (OFunc f)
  (in custom letsub_op at level 0, f custom letsub_var).
Notation "'APPLY' ( x , y )" := (OApply x y)
  (in custom letsub_op at level 0, x custom letsub_var, y custom letsub_var).
Notation "'CPY' ( x )" := (OCpy x)
  (in custom letsub_op at level 0, x custom letsub_var).

Notation "'RETURN' : A = o" := (BRet A o)
  (in custom letsub at level 10, A custom letsub_frml,
   o custom letsub_op, format "'RETURN'  :  A  =  o").
Notation "'LET' x : A = o 'IN' k" := (BLet x A o k)
  (in custom letsub at level 200, x constr at level 0, A custom letsub_frml,
   o custom letsub_op, k custom letsub at level 200,
   format "'[v' 'LET'  x  :  A  =  o  'IN' '/' k ']'").
Notation "'LET' 'SUB' [ x , y ] : A → B = 'SUB' ( 'VAR' x' ) { b } 'IN' k" :=
  (BLetSub x y A B (mkSubr x' b) k)
  (in custom letsub at level 200,
   x constr at level 0, y constr at level 0,
   A custom letsub_frml at level 98, B custom letsub_frml at level 200,
   x' constr at level 0,
   b custom letsub at level 200, k custom letsub at level 200,
   format "'[v' '[v  ' 'LET'  'SUB'  [ x ,  y ]  :  A  →  B  =  'SUB'  ( 'VAR'  x' )  { '/' b ']' '/' }  'IN' '/' k ']'").
Notation "{ b } 'AS' y" := (PBody y b)
  (in custom letsub at level 200, b custom letsub at level 200,
   y constr at level 0,
   format "'[v' '[v  ' { '/' b ']' '/' }  'AS'  y ']'").
Notation "'VAR' x : A ; p" := (PVar x A p)
  (in custom letsub at level 200, x constr at level 0, A custom letsub_frml,
   p custom letsub at level 200,
   format "'[v' 'VAR'  x  :  A  ; '/' p ']'").

(** * Unique names *)

(** We assume that all bound line variables of a program are
    syntactically different. This is not part of the typing judgment,
    but is checked separately by [names_unique]. The binders are
    listed in the order of the lines of the Fitch proof: the return
    variable [y] of [LET SUB [x, y]] comes after the binders of the
    subroutine. *)
Fixpoint body_binders (b : body) : list nat :=
  match b with
  | BLet x _ _ k => x :: body_binders k
  | BLetSub _ y _ _ s k => subr_binders s ++ y :: body_binders k
  | BRet _ _ => []
  end
with subr_binders (s : subr) : list nat :=
  match s with
  | mkSubr x b => x :: body_binders b
  end.

Fixpoint prog_binders (p : prog) : list nat :=
  match p with
  | PVar x _ p' => x :: prog_binders p'
  | PBody y b => body_binders b ++ [y]
  end.

Definition names_unique (p : prog) : Prop := NoDup (prog_binders p).

#[global] Instance names_unique_dec p : Decision (names_unique p).
Proof. unfold names_unique. apply _. Defined.

(** * Typing *)

(** Typing contexts, most recent binding first. Like [scope] for Fitch
    proofs, variables are looked up by membership; this is unambiguous
    under [names_unique]. *)
Definition ctx := list (var * ty).

(** The typing judgments for operations, bodies and programs *)
Reserved Notation "Γ ⊢ₒ o : A"
  (at level 70, o custom letsub_op, A custom letsub_frml).
Reserved Notation "Γ ⊢ b : A"
  (at level 70, b custom letsub, A custom letsub_frml).
Reserved Notation "Γ ⊢ₚ p : A"
  (at level 70, p custom letsub, A custom letsub_frml).

Inductive op_typed (Γ : ctx) : op -> frml -> Prop :=
| op_typed_pair x y A B :
  (LVar x, TFrml A) ∈ Γ ->
  (LVar y, TFrml B) ∈ Γ ->
  Γ ⊢ₒ (x, y) : A ∧ B
| op_typed_fst x A B :
  (LVar x, TFrml (A ∧ B)%F) ∈ Γ ->
  Γ ⊢ₒ FST(x) : A
| op_typed_snd x A B :
  (LVar x, TFrml (A ∧ B)%F) ∈ Γ ->
  Γ ⊢ₒ SND(x) : B
| op_typed_func x y A B :
  (SVar x y, TSub A B) ∈ Γ ->
  Γ ⊢ₒ FUNC([x, y]) : A → B
| op_typed_apply x y A B :
  (LVar x, TFrml (A → B)%F) ∈ Γ ->
  (LVar y, TFrml A) ∈ Γ ->
  Γ ⊢ₒ APPLY(x, y) : B
| op_typed_cpy x A :
  (LVar x, TFrml A) ∈ Γ ->
  Γ ⊢ₒ CPY(x) : A
where "Γ ⊢ₒ o : A" := (op_typed Γ o A).

(** [Γ ⊢ b : C]: the body [b] returns a value of type [C]. The
    variables bound inside a subroutine are not visible after it, but
    the subroutine can refer to the variables of the enclosing scopes.
    The parameter of a subroutine must agree with its name. The return
    variable [y] is not part of the typing: it only names the last
    line of the subroutine, and is never in scope on its own. Type
    annotations are checked, not inferred. *)
Inductive body_typed : ctx -> body -> frml -> Prop :=
| body_typed_let Γ x A o k C :
  Γ ⊢ₒ o : A ->
  (LVar x, TFrml A) :: Γ ⊢ k : C ->
  Γ ⊢ LET x : A = o IN k : C
| body_typed_letsub Γ x y A B b k C :
  (LVar x, TFrml A) :: Γ ⊢ b : B ->
  (SVar x y, TSub A B) :: Γ ⊢ k : C ->
  Γ ⊢ LET SUB [x, y] : A → B = SUB (VAR x) { b } IN k : C
| body_typed_ret Γ A o :
  Γ ⊢ₒ o : A ->
  Γ ⊢ RETURN : A = o : A
where "Γ ⊢ b : A" := (body_typed Γ b A).

Inductive prog_typed : ctx -> prog -> frml -> Prop :=
| prog_typed_var Γ x A p C :
  (LVar x, TFrml A) :: Γ ⊢ₚ p : C ->
  Γ ⊢ₚ VAR x : A ; p : C
| prog_typed_body Γ y b C :
  Γ ⊢ b : C ->
  Γ ⊢ₚ { b } AS y : C
where "Γ ⊢ₚ p : A" := (prog_typed Γ p A).

(** A closed, well-typed program with conclusion [C] *)
Definition prog_ok (p : prog) (C : frml) : Prop :=
  names_unique p /\ [] ⊢ₚ p : C.

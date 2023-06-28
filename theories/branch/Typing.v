From UntitledLang Require Import Map.
From UntitledLang.branch Require Import Ast Evaluation.

#[local] Hint Resolve update_eq : core.

Inductive type : Type :=
  | T_Bool
  | T_Nat.

Notation "'Bool'" := T_Bool (in custom mylang_branch at level 0): mylang_branch_scope.
Notation "'Nat'" := T_Nat (in custom mylang_branch at level 0): mylang_branch_scope.

Inductive value_has_type : value -> type -> Prop :=
  | Ty_VBool : forall (b : bool), value_has_type b T_Bool
  | Ty_VNat : forall (n : nat), value_has_type n T_Nat.

Definition context := map type.

Declare Scope type_scope.
Reserved Notation "Gamma |- e : T" (at level 101, e custom mylang_branch, T custom mylang_branch).

Inductive expr_has_type : context -> expr -> type -> Prop :=
  | Ty_Var : forall Gamma (x : ident) T,
      Gamma x = Some T ->
      Gamma |- x : T
  | Ty_ConstBool : forall Gamma (b : bool),
      Gamma |- b : Bool
  | Ty_And : forall Gamma e1 e2,
      Gamma |- e1 : Bool ->
      Gamma |- e2 : Bool ->
      Gamma |- e1 && e2 : Bool
  | Ty_Or : forall Gamma e1 e2,
      Gamma |- e1 : Bool ->
      Gamma |- e2 : Bool ->
      Gamma |- e1 || e2 : Bool
  | Ty_Not : forall Gamma e,
      Gamma |- e : Bool ->
      Gamma |- ~e : Bool
  | Ty_EqBool : forall Gamma e1 e2,
      Gamma |- e1 : Bool ->
      Gamma |- e2 : Bool ->
      Gamma |- e1 = e2 : Bool
  | Ty_ConstNat : forall Gamma (n : nat),
      Gamma |- n : Nat
  | Ty_Plus : forall Gamma e1 e2,
      Gamma |- e1 : Nat ->
      Gamma |- e2 : Nat ->
      Gamma |- e1 + e2 : Nat
  | Ty_Mult : forall Gamma e1 e2,
      Gamma |- e1 : Nat ->
      Gamma |- e2 : Nat ->
      Gamma |- e1 * e2 : Nat
  | Ty_EqNat : forall Gamma e1 e2,
      Gamma |- e1 : Nat ->
      Gamma |- e2 : Nat ->
      Gamma |- e1 = e2 : Bool
  | Ty_Le : forall Gamma e1 e2,
      Gamma |- e1 : Nat ->
      Gamma |- e2 : Nat ->
      Gamma |- e1 <= e2 : Bool
  | Ty_Guess : forall Gamma,
      Gamma |- guess : Bool

where "Gamma |- e : T" := (expr_has_type Gamma e T): mylang_branch_scope.

Inductive well_typed_stmt : context -> stmt -> Prop :=
  | Ty_Skip : forall Gamma,
      well_typed_stmt Gamma <{ skip }>
  | Ty_Assign : forall Gamma (x : ident) e T,
      Gamma |- x : T ->
      Gamma |- e : T ->
      well_typed_stmt Gamma <{ x := e }>
  | Ty_Seq : forall Gamma s1 s2,
      well_typed_stmt Gamma s1 ->
      well_typed_stmt Gamma s2 ->
      well_typed_stmt Gamma <{ s1; s2 }>
  | Ty_If : forall Gamma cond s1 s2,
      Gamma |- cond : Bool ->
      well_typed_stmt Gamma s1 ->
      well_typed_stmt Gamma s2 ->
      well_typed_stmt Gamma <{ if cond then s1 else s2 end }>
  | Ty_While : forall Gamma cond s,
      Gamma |- cond : Bool ->
      well_typed_stmt Gamma s ->
      well_typed_stmt Gamma <{ while cond do s done }>.

Definition well_typed_state (Gamma : context) (st : state) : Prop :=
  forall x T, Gamma x = Some T -> exists v, (st x = Some v /\ value_has_type v T).

#[export] Hint Constructors type value_has_type expr_has_type well_typed_stmt : core.

Theorem expr_evalR_soundness: forall Gamma st e T v,
  well_typed_state Gamma st ->
  Gamma |- e : T ->
  e / st ==> v ->
  value_has_type v T.
Proof.
  intros Gamma st e T v Hst. generalize dependent v. generalize dependent T.
  induction e; intros T v He Heval; inversion Heval; inversion He; subst; auto.
  - (* E_Var *)
    destruct (Hst x T H5) as [v' [Hv' Htyv]].
    rewrite H1 in Hv'. injection Hv' as Hv'; subst.
    apply Htyv.
Qed.

Theorem expr_evalR_completeness: forall Gamma st e T,
  well_typed_state Gamma st ->
  Gamma |- e : T ->
  exists v, e / st ==> v /\ value_has_type v T.
Proof with eauto.
  intros Gamma st e T Hst. generalize dependent T.
  induction e; intros T He; inversion He; subst...
  - destruct (Hst x T H1) as [v [Hv Htyv]]. exists v. split...
  - destruct (IHe1 <{ Bool }> H2) as [v1 [Hv1 Tv1]].
    destruct (IHe2 <{ Bool }> H4) as [v2 [Hv2 Tv2]].
    inversion Tv1; inversion Tv2; subst...
  - destruct (IHe1 <{ Bool }> H2) as [v1 [Hv1 Tv1]].
    destruct (IHe2 <{ Bool }> H4) as [v2 [Hv2 Tv2]].
    inversion Tv1; inversion Tv2; subst...
  - destruct (IHe <{ Bool }> H1) as [v [Hv Tv]].
    inversion Tv; subst...
  - destruct (IHe1 <{ Nat }> H2) as [v1 [Hv1 Tv1]].
    destruct (IHe2 <{ Nat }> H4) as [v2 [Hv2 Tv2]].
    inversion Tv1; inversion Tv2; subst...
  - destruct (IHe1 <{ Nat }> H2) as [v1 [Hv1 Tv1]].
    destruct (IHe2 <{ Nat }> H4) as [v2 [Hv2 Tv2]].
    inversion Tv1; inversion Tv2; subst...
  - destruct (IHe1 <{ Bool }> H2) as [v1 [Hv1 Tv1]].
    destruct (IHe2 <{ Bool }> H4) as [v2 [Hv2 Tv2]].
    inversion Tv1; inversion Tv2; subst...
  - destruct (IHe1 <{ Nat }> H2) as [v1 [Hv1 Tv1]].
    destruct (IHe2 <{ Nat }> H4) as [v2 [Hv2 Tv2]].
    inversion Tv1; inversion Tv2; subst...
  - destruct (IHe1 <{ Nat }> H2) as [v1 [Hv1 Tv1]].
    destruct (IHe2 <{ Nat }> H4) as [v2 [Hv2 Tv2]].
    inversion Tv1; inversion Tv2; subst...
  Unshelve. apply true.
Qed.

Theorem stmt_evalR_preservation: forall Gamma s st st',
  well_typed_state Gamma st ->
  well_typed_stmt Gamma s ->
  st =[ s ]=> st' ->
  well_typed_state Gamma st'.
Proof.
  intros Gamma s st st' Hty_st Hty_s Heval.
  induction Heval; inversion Hty_s; subst; auto.
  - (* x := e *)
    intros y Ty Hty. destruct (String.eqb_spec x y).
    + (* x = y *)
      subst y. exists v. rewrite update_eq. split; trivial.
      inversion H3; subst. rewrite H2 in Hty; subst. injection Hty as Hty; subst Ty.
      apply expr_evalR_soundness with (Gamma := Gamma) (T := T) in H; trivial.
    + (* x <> y *)
      rewrite update_neq; auto.
Qed.

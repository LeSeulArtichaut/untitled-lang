From UntitledLang Require Import Ast Evaluation Map.

#[local] Hint Resolve update_eq : core.

Inductive type : Type :=
  | T_Bool
  | T_Nat.

Notation "'Bool'" := T_Bool (in custom mylang at level 0): mylang_scope.
Notation "'Nat'" := T_Nat (in custom mylang at level 0): mylang_scope.

Inductive value_has_type : value -> type -> Prop :=
  | Ty_VBool : forall (b : bool), value_has_type b T_Bool
  | Ty_VNat : forall (n : nat), value_has_type n T_Nat.

Definition context := map type.

Declare Scope type_scope.
Reserved Notation "Gamma |- e : T" (at level 101, e custom mylang, T custom mylang).

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

where "Gamma |- e : T" := (expr_has_type Gamma e T): mylang_scope.

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

(* (* Helper macro for the next theorem *)
Ltac invert_soundness_IH st e IHe Hv v T :=
  destruct (expr_eval st e) as [v|]; [| discriminate];
  assert (Hv: value_has_type v T) by (apply IHe; trivial);
  inversion Hv; subst.

Theorem expr_eval_soundness: forall Gamma st e T v,
  well_typed_state Gamma st ->
  Gamma |- e : T ->
  expr_eval st e = Some v ->
  value_has_type v T.
Proof.
  intros Gamma st e T v Hst. generalize dependent v. generalize dependent T.
  induction e; intros T v He Heval; inversion He; subst; simpl in *.
  - destruct (Hst x T H1) as [v' [Hv' Htyv]].
    rewrite Hv' in Heval. injection Heval as Evv'; subst v'. apply Htyv.
  - injection Heval as E; subst v. apply Ty_VBool.
  - invert_soundness_IH st e1 IHe1 Hv1 v1 <{ Bool }>.
    invert_soundness_IH st e2 IHe2 Hv2 v2 <{ Bool }>.
    injection Heval as Hv; subst v.
    apply Ty_VBool.
  - invert_soundness_IH st e1 IHe1 Hv1 v1 <{ Bool }>.
    invert_soundness_IH st e2 IHe2 Hv2 v2 <{ Bool }>.
    injection Heval as Hv; subst v.
    apply Ty_VBool.
  - invert_soundness_IH st e IHe Hv' v' <{ Bool }>.
    injection Heval as Hv; subst v.
    apply Ty_VBool.
  - injection Heval as E; subst v. apply Ty_VNat.
  - invert_soundness_IH st e1 IHe1 Hv1 v1 <{ Nat }>.
    invert_soundness_IH st e2 IHe2 Hv2 v2 <{ Nat }>.
    injection Heval as Hv; subst v.
    apply Ty_VNat.
  - invert_soundness_IH st e1 IHe1 Hv1 v1 <{ Nat }>.
    invert_soundness_IH st e2 IHe2 Hv2 v2 <{ Nat }>.
    injection Heval as Hv; subst v.
    apply Ty_VNat.
  - invert_soundness_IH st e1 IHe1 Hv1 v1 <{ Bool }>.
    invert_soundness_IH st e2 IHe2 Hv2 v2 <{ Bool }>.
    injection Heval as Hv; subst v.
    apply Ty_VBool.
  - invert_soundness_IH st e1 IHe1 Hv1 v1 <{ Nat }>.
    invert_soundness_IH st e2 IHe2 Hv2 v2 <{ Nat }>.
    injection Heval as Hv; subst v.
    apply Ty_VBool.
  - invert_soundness_IH st e1 IHe1 Hv1 v1 <{ Nat }>.
    invert_soundness_IH st e2 IHe2 Hv2 v2 <{ Nat }>.
    injection Heval as Hv; subst v.
    apply Ty_VBool.
Qed. *)

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

Corollary expr_eval_soundness : forall Gamma st e T v,
  well_typed_state Gamma st ->
  Gamma |- e : T ->
  expr_eval st e = Some v ->
  value_has_type v T.
Proof.
  intros. rewrite <- expr_eval_evalR_equiv in *. eapply expr_evalR_soundness; eauto.
Qed.

Theorem expr_eval_completeness: forall Gamma st e T,
  well_typed_state Gamma st ->
  Gamma |- e : T ->
  exists v, expr_eval st e = Some v /\ value_has_type v T.
Proof with eauto.
  intros Gamma st e T Hst. generalize dependent T.
  induction e; intros T He; inversion He; subst; simpl.
  - destruct (Hst x T H1) as [v Hv]...
  - exists b...
  - destruct (IHe1 <{ Bool }> H2) as [v1 [Hv1 Tv1]]; rewrite Hv1.
    destruct (IHe2 <{ Bool }> H4) as [v2 [Hv2 Tv2]]; rewrite Hv2.
    inversion Tv1; inversion Tv2; subst...
  - destruct (IHe1 <{ Bool }> H2) as [v1 [Hv1 Tv1]]; rewrite Hv1.
    destruct (IHe2 <{ Bool }> H4) as [v2 [Hv2 Tv2]]; rewrite Hv2.
    inversion Tv1; inversion Tv2; subst...
  - destruct (IHe <{ Bool }> H1) as [v [Hv Tv]]; rewrite Hv.
    inversion Tv; subst...
  - exists n...
  - destruct (IHe1 <{ Nat }> H2) as [v1 [Hv1 Tv1]]; rewrite Hv1.
    destruct (IHe2 <{ Nat }> H4) as [v2 [Hv2 Tv2]]; rewrite Hv2.
    inversion Tv1; inversion Tv2; subst...
  - destruct (IHe1 <{ Nat }> H2) as [v1 [Hv1 Tv1]]; rewrite Hv1.
    destruct (IHe2 <{ Nat }> H4) as [v2 [Hv2 Tv2]]; rewrite Hv2.
    inversion Tv1; inversion Tv2; subst...
  - destruct (IHe1 <{ Bool }> H2) as [v1 [Hv1 Tv1]]; rewrite Hv1.
    destruct (IHe2 <{ Bool }> H4) as [v2 [Hv2 Tv2]]; rewrite Hv2.
    inversion Tv1; inversion Tv2; subst...
  - destruct (IHe1 <{ Nat }> H2) as [v1 [Hv1 Tv1]]; rewrite Hv1.
    destruct (IHe2 <{ Nat }> H4) as [v2 [Hv2 Tv2]]; rewrite Hv2.
    inversion Tv1; inversion Tv2; subst...
  - destruct (IHe1 <{ Nat }> H2) as [v1 [Hv1 Tv1]]; rewrite Hv1.
    destruct (IHe2 <{ Nat }> H4) as [v2 [Hv2 Tv2]]; rewrite Hv2.
    inversion Tv1; inversion Tv2; subst...
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

(* Theorem stmt_evalR_progress: forall Gamma st s,
  well_typed_state Gamma st ->
  well_typed_stmt Gamma s ->
  exists st', st =[ s ]=> st'.
Proof.
  intros Gamma st s. generalize dependent st.
  induction s; intros st Hst Hs; inversion Hs; subst.
  - eauto.
  - destruct (expr_evalR_completeness) with Gamma st e T
      as [v [Heval Hty]]; auto.
    exists (x |-> v; st). auto.
  - destruct (IHs1 st Hst H2) as [st' Eeval_st].
    specialize
      (stmt_evalR_preservation Gamma s1 st st' Hst H2 Eeval_st) as Hst'.
    destruct (IHs2 st' Hst' H3) as [st'' Eeval_st'].
    exists st''. eauto.
  - destruct (expr_evalR_completeness Gamma st cond <{ Bool }>) as [v [Hv Tv]]; trivial.
    inversion Tv; subst.
    destruct b.
    + destruct (IHs1 st) as [st' Hst']; trivial. exists st'.
      apply Eval_IfTrue; auto.
    + destruct (IHs2 st) as [st' Hst']; trivial. exists st'.
      apply Eval_IfFalse; auto.
Qed. *)

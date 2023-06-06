Require Import Nat Arith.PeanoNat String Lia.
From UntitledLang Require Import Map.
From UntitledLang.branch Require Import Ast.

Open Scope mylang_branch_scope.
Open Scope bool_scope.
Open Scope string_scope.
Open Scope nat_scope.

Definition x : ident := "x".
Definition y : ident := "y".
Definition z : ident := "z".

Reserved Notation "e '/' st '==>' v " (at level 40, st at level 39, v at level 39).
Reserved Notation "st '=[' s ']=>' st'"
  (at level 40, s custom mylang_branch at level 99,
   st constr, st' constr at next level).

Inductive value :=
  | V_Bool (b : bool)
  | V_Nat (n : nat).

Coercion V_Bool : bool >-> value.
Coercion V_Nat : nat >-> value.

Definition state := map value.

Inductive expr_evalR : state -> expr -> value -> Prop :=
  | Eval_Var : forall st (x : ident) v,
      st x = Some v ->
      x / st ==> v
  | Eval_ConstBool : forall st (b : bool), b / st ==> b
  | Eval_And : forall st e1 e2 (b1 b2 : bool),
      e1 / st ==> b1 ->
      e2 / st ==> b2 ->
      <{ e1 && e2 }> / st ==> (b1 && b2)
  | Eval_Or : forall st e1 e2 (b1 b2 : bool),
      e1 / st ==> b1 ->
      e2 / st ==> b2 ->
      <{ e1 || e2 }> / st ==> (b1 || b2)
  | Eval_Not : forall st e (b : bool),
      e / st ==> b ->
      <{ ~e }> / st ==> (negb b)
  | Eval_ConstNat : forall st (n : nat), n / st ==> n
  | Eval_Plus : forall st e1 e2 (n1 n2 : nat),
      e1 / st ==> n1 ->
      e2 / st ==> n2 ->
      <{ e1 + e2 }> / st ==> (n1 + n2)
  | Eval_Mult : forall st e1 e2 (n1 n2 : nat),
      e1 / st ==> n1 ->
      e2 / st ==> n2 ->
      <{ e1 * e2 }> / st ==> (n1 * n2)
  | Eval_EqBool : forall st e1 e2 (b1 b2 : bool),
      e1 / st ==> b1 ->
      e2 / st ==> b2 ->
      <{ e1 = e2 }> / st ==> (Bool.eqb b1 b2)
  | Eval_EqNat : forall st e1 e2 (n1 n2 : nat),
      e1 / st ==> n1 ->
      e2 / st ==> n2 ->
      <{ e1 = e2 }> / st ==> (n1 =? n2)
  | Eval_Le : forall st e1 e2 (n1 n2 : nat),
      e1 / st ==> n1 ->
      e2 / st ==> n2 ->
      <{ e1 <= e2 }> / st ==> (n1 <=? n2)
  | Eval_Guess : forall st (b : bool),
      <{ guess }> / st ==> b

where "e '/' st '==>' v " := (expr_evalR st e v).

Inductive stmt_evalR : state -> stmt -> state -> Prop :=
  | Eval_Skip : forall st, st =[ skip ]=> st
  | Eval_Assign : forall st x e v,
      e / st ==> v ->
      st =[ x := e ]=> (x |-> v; st)
  | Eval_Seq : forall st st' st'' s1 s2,
      st =[ s1 ]=> st' ->
      st' =[ s2 ]=> st'' ->
      st =[ s1; s2 ]=> st''
  | Eval_IfTrue : forall st st' cond s1 s2,
      cond / st ==> true ->
      st =[ s1 ]=> st' ->
      st =[ if cond then s1 else s2 end ]=> st'
  | Eval_IfFalse : forall st st' cond s1 s2,
      cond / st ==> false ->
      st =[ s2 ]=> st' ->
      st =[ if cond then s1 else s2 end ]=> st'
  | Eval_WhileTrue : forall st st' st'' cond s,
      cond / st ==> true ->
      st =[ s ]=> st' ->
      st' =[ while cond do s done ]=> st'' ->
      st =[ while cond do s done ]=> st''
  | Eval_WhileFalse : forall st cond s,
      cond / st ==> false ->
      st =[ while cond do s done ]=> st

where "st '=[' s ']=>' st'" := (stmt_evalR st s st') : mylang_branch_scope.

Definition expr_equivalence (e1 e2 : expr) : Prop :=
  forall st v, e1 / st ==> v <-> e2 / st ==> v.

Definition stmt_equivalence (s1 s2 : stmt) : Prop :=
  forall st st', st =[ s1 ]=> st' <-> st' =[ s2 ]=> st'.

#[export] Hint Constructors expr_evalR stmt_evalR : core.

Definition stmt_ex := <{ while guess do x := x + 1 done }>.

Example stmt_ex_true : forall n,
  (x |-> V_Nat 0) =[ stmt_ex ]=> (x |-> V_Nat n).
Proof.
  intros n. replace n with (0 + n) by lia. generalize 0; intros m.
  generalize dependent m; induction n; intros m.
  - replace (m + 0) with m by lia. apply Eval_WhileFalse. auto.
  - replace (m + S n) with (m + 1 + n) by lia.
    apply Eval_WhileTrue with (x |-> V_Nat (m + 1)); auto.
    + replace (x |-> V_Nat (m + 1))
        with (x |-> V_Nat (m + 1); x|-> V_Nat m)
        by apply update_shadow.
      auto.
Qed.

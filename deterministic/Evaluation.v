Require Import Nat Arith.PeanoNat String Relations.Relation_Operators.
From UntitledLang Require Import Map OptMonadNotation.
From UntitledLang.deterministic Require Import Ast.

Open Scope mylang_scope.
Open Scope opt_monad_scope.
Open Scope bool_scope.
Open Scope string_scope.
Open Scope nat_scope.

Definition x : ident := "x".
Definition y : ident := "y".
Definition z : ident := "z".

Reserved Notation "e '/' st '==>' v " (at level 40, st at level 39, v at level 39).
Reserved Notation "st '=[' s ']=>' st'"
  (at level 40, s custom mylang at level 99,
   st constr, st' constr at next level).
Reserved Notation "s '/' st '-->e' s'" (at level 40, st at level 39, s' at level 39).
Reserved Notation "s '/' st '-->' s' '/' st'" (at level 40, st at level 39, s' at level 39).

Inductive value :=
  | V_Bool (b : bool)
  | V_Nat (n : nat).

Coercion V_Bool : bool >-> value.
Coercion V_Nat : nat >-> value.

Definition state := map value.

Fixpoint expr_eval (st : state) (e : expr) : option value :=
  match e with
  | E_Var x => st x
  | E_ConstBool b => Some (V_Bool b)
  | <{ e1 && e2 }> =>
    match expr_eval st e1, expr_eval st e2 with
    | Some (V_Bool b1), Some (V_Bool b2) => Some (V_Bool (b1 && b2))
    | _, _ => None
    end
  | <{ e1 || e2 }> =>
    match expr_eval st e1, expr_eval st e2 with
    | Some (V_Bool b1), Some (V_Bool b2) => Some (V_Bool (b1 || b2))
    | _, _ => None
    end
  | <{ ~e1 }> =>
    match expr_eval st e1 with
    | Some (V_Bool b1) => Some (V_Bool (negb b1))
    | _ => None
    end
  | E_ConstNat n => Some (V_Nat n)
  | <{ e1 + e2 }> =>
    match expr_eval st e1, expr_eval st e2 with
    | Some (V_Nat n1), Some (V_Nat n2) => Some (V_Nat (n1 + n2))
    | _, _ => None
    end
  | <{ e1 * e2 }> =>
    match expr_eval st e1, expr_eval st e2 with
    | Some (V_Nat n1), Some (V_Nat n2) => Some (V_Nat (n1 * n2))
    | _, _ => None
    end
  | <{ e1 = e2 }> =>
    match expr_eval st e1, expr_eval st e2 with
    | Some (V_Nat n1), Some (V_Nat n2) => Some (V_Bool (n1 =? n2))
    | Some (V_Bool b1), Some (V_Bool b2) => Some (V_Bool (Bool.eqb b1 b2))
    | _, _ => None
    end
  | <{ e1 <= e2 }> =>
    match expr_eval st e1, expr_eval st e2 with
    | Some (V_Nat n1), Some (V_Nat n2) => Some (V_Bool (n1 <=? n2))
    | _, _ => None
    end
  end.

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

where "st '=[' s ']=>' st'" := (stmt_evalR st s st') : mylang_scope.

Fixpoint stmt_eval (fuel : nat) (st : state) (s : stmt) : option state :=
  match fuel with
  | O => None
  | S fuel' =>
    match s with
    | <{ skip }> => Some st
    | <{ x := e }> =>
      v <- expr_eval st e; Some (x |-> v; st)
    | <{ s1; s2 }> =>
      st' <- stmt_eval fuel' st s1;
      stmt_eval fuel' st' s2
    | <{ if cond then s1 else s2 end }> =>
      match expr_eval st cond with
      | Some true => stmt_eval fuel' st s1
      | Some false => stmt_eval fuel' st s2
      | _ => None
      end
    | <{ while cond do s1 done }> =>
      match expr_eval st cond with
      | Some true =>
        st' <- stmt_eval fuel' st s1;
        stmt_eval fuel' st' s
      | Some false => Some st
      | _ => None
      end
    end
  end.

Inductive expr_value : expr -> Prop :=
  | Value_Bool : forall (b : bool), expr_value b
  | Value_Nat : forall (n : nat), expr_value n.
  
Inductive expr_stepR : state -> expr -> expr -> Prop :=
  | Step_VarBool : forall st x b,
      st x = Some (V_Bool b) ->
      x / st -->e b
  | Step_VarNat : forall st x n,
      st x = Some (V_Nat n) ->
      x / st -->e n
  | Step_AndStepL : forall st e1 e1' e2,
      e1 / st -->e e1' ->
      <{ e1 && e2 }> / st -->e <{ e1' && e2 }>
  | Step_AndStepR : forall st (b1 : bool) e2 e2',
      e2 / st -->e e2' ->
      <{ b1 && e2 }> / st -->e <{ b1 && e2' }>
  | Step_And : forall st (b1 b2 : bool),
      <{ b1 && b2 }> / st -->e (b1 && b2)
  | Step_OrStepL : forall st e1 e1' e2,
      e1 / st -->e e1' ->
      <{ e1 || e2 }> / st -->e <{ e1' || e2 }>
  | Step_OrStepR : forall st (b1 : bool) e2 e2',
      e2 / st -->e e2' ->
      <{ b1 || e2 }> / st -->e <{ b1 || e2' }>
  | Step_Or : forall st (b1 b2 : bool),
      <{ b1 || b2 }> / st -->e (b1 || b2)
  | Step_NotStep : forall st e e',
      e / st -->e e' ->
      <{ ~e }> / st -->e <{ ~e' }>
  | Step_Not : forall st (b : bool),
      <{ ~b }> / st -->e b
  | Step_PlusStepL : forall st e1 e1' e2,
      e1 / st -->e e1' ->
      <{ e1 + e2 }> / st -->e <{ e1' + e2 }>
  | Step_PlusStepR : forall st (n1 : nat) e2 e2',
      e2 / st -->e e2' ->
      <{ n1 + e2 }> / st -->e <{ n1 + e2' }>
  | Step_Plus : forall st (n1 n2 : nat),
      <{ n1 + n2 }> / st -->e (n1 + n2)
  | Step_MultStepL : forall st e1 e1' e2,
      e1 / st -->e e1' ->
      <{ e1 * e2 }> / st -->e <{ e1' * e2 }>
  | Step_MultStepR : forall st (n1 : nat) e2 e2',
      e2 / st -->e e2' ->
      <{ n1 * e2 }> / st -->e <{ n1 * e2' }>
  | Step_Mult : forall st (n1 n2 : nat),
      <{ n1 * n2 }> / st -->e (n1 * n2)
  | Step_EqStepL : forall st e1 e1' e2,
      e1 / st -->e e1' ->
      <{ e1 = e2 }> / st -->e <{ e1' = e2 }>
  | Step_EqBoolStepR : forall st (b1 : bool) e2 e2',
      e2 / st -->e e2' ->
      <{ b1 = e2 }> / st -->e <{ b1 = e2' }>
  | Step_EqNatStepR : forall st (n1 : nat) e2 e2',
      e2 / st -->e e2' ->
      <{ n1 = e2 }> / st -->e <{ n1 = e2' }>
  | Step_EqBool : forall st (b1 b2 : bool),
      <{ b1 = b2 }> / st -->e (Bool.eqb b1 b2)
  | Step_EqNat : forall st (n1 n2 : nat),
      <{ n1 = n2 }> / st -->e (Nat.eqb n1 n2)
  | Step_LeStepL : forall st e1 e1' e2,
      e1 / st -->e e1' ->
      <{ e1 <= e2 }> / st -->e <{ e1' <= e2 }>
  | Step_LeStepR : forall st (n1 : nat) e2 e2',
      e2 / st -->e e2' ->
      <{ n1 <= e2 }> / st -->e <{ n1 <= e2' }>
  | Step_Le : forall st (n1 n2 : nat),
      <{ n1 <= n2 }> / st -->e (n1 <=? n2)

where "s '/' st '-->e' s'" := (expr_stepR st s s'): mylang_scope.

Definition expr_reduceR st := clos_refl_trans expr (expr_stepR st).

Notation "s '/' st '-->e*' s'" := (expr_reduceR st s s')
  (at level 40, st at level 39, s' at level 39): mylang_scope.

Inductive stmt_stepR : state * stmt -> state * stmt -> Prop :=
  | Step_AssignStep : forall st x e e',
      e / st -->e e' ->
      <{ x := e }> / st --> <{ x := e' }> / st
  | Step_AssignBool : forall st x (b : bool),
      <{ x := b }> / st --> <{ skip }> / (x |-> b; st)
  | Step_AssignNat : forall st x (n : nat),
      <{ x := n }> / st --> <{ skip }> / (x |-> n; st)
  | Step_SeqStep : forall st st' s1 s1' s2,
      s1 / st --> s1' / st' ->
      <{ s1; s2 }> / st --> <{ s1'; s2 }> / st'
  | Step_Seq : forall st s2,
      <{ skip; s2 }> / st --> s2 / st
  | Step_IfStep : forall st cond cond' s1 s2,
      cond / st -->e cond' ->
      <{ if cond then s1 else s2 end }> / st --> <{ if cond' then s1 else s2 end }> / st
  | Step_IfTrue : forall st s1 s2,
      <{ if true then s1 else s2 end }> / st --> s1 / st
  | Step_IfFalse : forall st s1 s2,
      <{ if false then s1 else s2 end }> / st --> s2 / st
  | Step_While : forall st cond s,
      <{ while cond do s done }> / st -->
        <{ if cond then while cond do s done else skip end }> / st

where "s '/' st '-->' s' '/' st'" := (stmt_stepR (st, s) (st', s')).

Definition stmt_reduceR := clos_refl_trans (state * stmt) stmt_stepR.

Notation "s '/' st '-->*' s' '/' st'" := (stmt_reduceR (st, s) (st', s'))
  (at level 40, st at level 39, s' at level 39): mylang_scope.

#[export] Hint Constructors expr_evalR stmt_evalR expr_value expr_stepR stmt_stepR : core.
#[local] Hint Constructors clos_refl_trans : core.

Example ex_stmt_reduce_to_skip :
  <{ x := 1; y := 2 }> / empty
    -->* <{ skip }> / (y |-> V_Nat 2; x |-> V_Nat 1).
Proof.
  apply rt_trans with (x |-> V_Nat 1, <{ skip; y := 2 }>); eauto.
Qed.

Theorem expr_eval_evalR_equiv: forall st e v,
  e / st ==> v <-> expr_eval st e = Some v.
Proof with auto.
  intros st e. split.
  - (* evalR -> eval *)
    generalize dependent v. induction e;
    intros v H; simpl; inversion H; subst...
    + rewrite (IHe1 b1)... rewrite (IHe2 b2)...
    + rewrite (IHe1 b1)... rewrite (IHe2 b2)...
    + rewrite (IHe b)...
    + rewrite (IHe1 n1)... rewrite (IHe2 n2)...
    + rewrite (IHe1 n1)... rewrite (IHe2 n2)...
    + rewrite (IHe1 b1)... rewrite (IHe2 b2)...
    + rewrite (IHe1 n1)... rewrite (IHe2 n2)...
    + rewrite (IHe1 n1)... rewrite (IHe2 n2)...
  - (* eval -> evalR *)
    generalize dependent v. induction e;
    intros v H; simpl in H; try (injection H as H; subst)...
    + destruct (expr_eval st e1) as [v1|]; try destruct v1; try discriminate.
      destruct (expr_eval st e2) as [v2|]; try destruct v2; try discriminate.
      injection H as H; subst...
    + destruct (expr_eval st e1) as [v1|]; try destruct v1; try discriminate.
      destruct (expr_eval st e2) as [v2|]; try destruct v2; try discriminate.
      injection H as H; subst...
    + destruct (expr_eval st e) as [v1|]; try destruct v1; try discriminate.
      injection H as H; subst...
    + destruct (expr_eval st e1) as [v1|]; try destruct v1; try discriminate.
      destruct (expr_eval st e2) as [v2|]; try destruct v2; try discriminate.
      injection H as H; subst...
    + destruct (expr_eval st e1) as [v1|]; try destruct v1; try discriminate.
      destruct (expr_eval st e2) as [v2|]; try destruct v2; try discriminate.
      injection H as H; subst...
    + destruct (expr_eval st e1) as [v1|]; [| discriminate]; destruct v1;
      destruct (expr_eval st e2) as [v2|]; try destruct v2; try discriminate;
      injection H as H; subst...
    + destruct (expr_eval st e1) as [v1|]; try destruct v1; try discriminate.
      destruct (expr_eval st e2) as [v2|]; try destruct v2; try discriminate.
      injection H as H; subst...
Qed.

Corollary expr_evalR_deterministic : forall st e v v',
  e / st ==> v -> e / st ==> v' -> v = v'.
Proof.
  intros st e v v' Hv Hv'.
  rewrite expr_eval_evalR_equiv in *.
  rewrite Hv in Hv'. injection Hv'. trivial.
Qed.

Lemma stmt_eval_more_fuel : forall fuel1 fuel2 s st st',
  fuel1 <= fuel2 ->
  stmt_eval fuel1 st s = Some st' ->
  stmt_eval fuel2 st s = Some st'.
Proof.
  induction fuel1; intros fuel2 s st st' Hle Heval.
  - simpl in Heval. discriminate Heval.
  - destruct fuel2. inversion Hle. apply le_S_n in Hle.
    destruct s; simpl in *.
    + inversion Heval; subst. reflexivity.
    + apply Heval.
    + destruct (stmt_eval fuel1 st s1) as [st0|] eqn:Hs1; [| discriminate].
      rewrite (IHfuel1 fuel2 s1 st st0 Hle Hs1).
      destruct (stmt_eval fuel1 st0 s2) as [st1|] eqn:Hs2; [| discriminate].
      injection Heval as Heval; subst.
      rewrite (IHfuel1 fuel2 s2 st0 st' Hle Hs2).
      reflexivity.
    + destruct (expr_eval st cond) as [v|] eqn:Hcond; [| discriminate].
      rewrite <- expr_eval_evalR_equiv in Hcond.
      destruct v; [| discriminate].
      destruct b; auto.
    + destruct (expr_eval st cond) as [v|] eqn:Hcond; [| discriminate].
      rewrite <- expr_eval_evalR_equiv in Hcond.
      destruct v; [| discriminate].
      destruct b; auto.
      destruct (stmt_eval fuel1 st s) eqn:Hs1; [| discriminate].
      apply (IHfuel1 fuel2 s) in Hs1; trivial. rewrite Hs1.
      destruct (stmt_eval fuel1 s0 <{ while cond do s done }>)
        eqn:Hwhile; [| discriminate].
      apply (IHfuel1 fuel2 <{ while cond do s done }>) in Hwhile; trivial.
      rewrite Hwhile. apply Heval.
Qed.

Theorem stmt_eval_evalR_equiv: forall s st st',
  st =[ s ]=> st' <-> exists fuel, stmt_eval fuel st s = Some st'.
Proof.
  split; generalize dependent st'; generalize dependent st.
  - intros st st' H. induction H.
    + exists 1. reflexivity.
    + exists 1. simpl.
      rewrite (expr_eval_evalR_equiv st e v) in H.
      rewrite H. reflexivity.
    + destruct (IHstmt_evalR1) as [fuel1 Hfuel1].
      destruct (IHstmt_evalR2) as [fuel2 Hfuel2].
      exists (S (max fuel1 fuel2)). simpl.
      apply stmt_eval_more_fuel with (fuel2 := max fuel1 fuel2) in Hfuel1;
        [| apply Nat.le_max_l].
      apply stmt_eval_more_fuel with (fuel2 := max fuel1 fuel2) in Hfuel2;
        [| apply Nat.le_max_r].
      rewrite Hfuel1. rewrite Hfuel2. reflexivity.
    + destruct IHstmt_evalR as [fuel1 Hfuel1].
      exists (S fuel1). simpl.
      rewrite expr_eval_evalR_equiv in H. rewrite H.
      apply Hfuel1.
    + destruct IHstmt_evalR as [fuel2 Hfuel2].
      exists (S fuel2). simpl.
      rewrite expr_eval_evalR_equiv in H. rewrite H.
      apply Hfuel2.
    + destruct (IHstmt_evalR1) as [fuel1 Hfuel1].
      destruct (IHstmt_evalR2) as [fuel2 Hfuel2].
      exists (S (max fuel1 fuel2)). simpl.
      rewrite expr_eval_evalR_equiv in H. rewrite H.
      apply stmt_eval_more_fuel with (fuel2 := max fuel1 fuel2) in Hfuel1;
        [| apply Nat.le_max_l].
      apply stmt_eval_more_fuel with (fuel2 := max fuel1 fuel2) in Hfuel2;
        [| apply Nat.le_max_r].
      rewrite Hfuel1. rewrite Hfuel2. reflexivity.
    + exists 1. simpl.
      rewrite expr_eval_evalR_equiv in H. rewrite H. reflexivity.
  - intros st st' [fuel Hfuel].
    generalize dependent st'. generalize dependent st. generalize dependent s.
    induction fuel; intros s st st' H; [discriminate|].
    destruct s; simpl in H.
    + injection H as H; subst; auto.
    + destruct (expr_eval st e) as [v|] eqn:He; [| discriminate].
      rewrite <- expr_eval_evalR_equiv in He.
      injection H as H; subst; auto.
    + destruct (stmt_eval fuel st s1) as [st0|] eqn:Hs1; [| discriminate].
      eauto.
    + destruct (expr_eval st cond) as [v|] eqn:Hcond; [| discriminate].
      rewrite <- expr_eval_evalR_equiv in Hcond.
      destruct v; [| discriminate].
      destruct b; auto.
    + destruct (expr_eval st cond) as [v|] eqn:Hcond; [| discriminate].
      rewrite <- expr_eval_evalR_equiv in Hcond.
      destruct v; [| discriminate].
      destruct b.
      * destruct (stmt_eval fuel st s) as [st0|] eqn:Hs; [| discriminate].
        eauto.
      * injection H as H; subst; auto.
Qed.

Theorem stmt_evalR_deterministic: forall s st st1 st2,
  st =[ s ]=> st1 ->
  st =[ s ]=> st2 ->
  st1 = st2.
Proof.
  intros s st st1 st2 Hst1. generalize dependent st2.
  induction Hst1; intros st2 Hst2; inversion Hst2; subst; auto.
  - rewrite (expr_evalR_deterministic st e v v0); trivial.
  - apply IHHst1_1 in H2; subst; auto.
  - specialize (expr_evalR_deterministic st cond true false H H5). discriminate.
  - specialize (expr_evalR_deterministic st cond false true H H5). discriminate.
  - apply IHHst1_1 in H4; subst; auto.
  - specialize (expr_evalR_deterministic st2 cond true false H H4). discriminate.
  - specialize (expr_evalR_deterministic st cond false true H H2). discriminate.
Qed.

Theorem expr_stepR_deterministic : forall st e e' e'',
  e / st -->e e' ->
  e / st -->e e'' ->
  e' = e''.
Admitted.

Theorem stmt_stepR_deterministic : forall st st' st'' s s' s'',
  s / st --> s' / st' ->
  s / st --> s'' / st'' ->
  s' = s'' /\ st' = st''.
Admitted.

Theorem expr_evalR_stepR_equiv: forall st e (b : bool),
  e / st ==> b <-> e / st -->e* b.
Admitted.

Theorem stmt_evalR_stepR_equiv: forall st st' s,
  st =[ s ]=> st' <-> s / st -->* <{ skip }> / st'.
Admitted.

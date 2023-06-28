From Coq Require Import List String.
Import ListNotations. Open Scope string_scope.

From UntitledLang Require Import Map.

Inductive expr : Type :=
  (* variables *)
  | E_Var (x : ident)
  (* booleans *)
  | E_ConstBool (b : bool)
  | E_And (e1 e2 : expr)
  | E_Or (e1 e2 : expr)
  | E_Not (e : expr)
  (* Numbers *)
  | E_ConstNat (n : nat)
  | E_Plus (e1 e2 : expr)
  | E_Mult (e1 e2 : expr)
  | E_Eq (e1 e2 : expr)
  | E_Le (e1 e2 : expr).

Coercion E_Var : ident >-> expr.
Coercion E_ConstBool : bool >-> expr.
Coercion E_ConstNat : nat >-> expr.

Inductive stmt : Type :=
  | S_Skip
  | S_Assign (x : ident) (e : expr)
  | S_Seq (s1 s2 : stmt)
  | S_If (cond : expr) (s1 s2 : stmt)
  | S_While (cond : expr) (s : stmt).

Declare Custom Entry mylang.
Declare Scope mylang_scope.

Notation "<{ e }>" := e (at level 0, e custom mylang at level 99).
Notation "x" := x (in custom mylang at level 0, x constr at level 0) : mylang_scope.
Notation "( e )" := e (in custom mylang, e at level 99) : mylang_scope.

Notation "x && y" := (E_And x y) (in custom mylang at level 80, left associativity) : mylang_scope.
Notation "x || y" := (E_Or x y) (in custom mylang at level 85, left associativity) : mylang_scope.
Notation "'~' x" := (E_Not x) (in custom mylang at level 75, right associativity) : mylang_scope.
Notation "x + y" := (E_Plus x y) (in custom mylang at level 50, left associativity) : mylang_scope.
Notation "x * y" := (E_Mult x y) (in custom mylang at level 40, left associativity) : mylang_scope.
Notation "x = y" := (E_Eq x y) (in custom mylang at level 70, no associativity) : mylang_scope.
Notation "x <= y" := (E_Le x y) (in custom mylang at level 70, no associativity) : mylang_scope.

Notation "'skip'" := S_Skip (in custom mylang at level 0) : mylang_scope.
Notation "x := e" := (S_Assign x e) (in custom mylang at level 0, x constr at level 0, e at level 90, no associativity) : mylang_scope.
Notation "s1 ; s2" := (S_Seq s1 s2) (in custom mylang at level 95, right associativity) : mylang_scope.
Notation "'if' cond 'then' s1 'else' s2 'end'" := (S_If cond s1 s2) (in custom mylang at level 94, cond at level 99, s1 at level 99, s2 at level 99): mylang_scope.
Notation "'while' cond 'do' s 'done'" := (S_While cond s) (in custom mylang at level 94, cond at level 99, s at level 99): mylang_scope.

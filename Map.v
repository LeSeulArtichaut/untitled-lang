From Coq Require Import String FunctionalExtensionality.

Definition ident := String.string.
Definition map (V : Type) := ident -> option V.

Definition empty {V : Type} : map V := (fun _ => None).
Definition update {V : Type} (m : map V) (x : ident) (v : V) :=
  (fun y => if String.eqb x y then Some v else m y).

Notation "x |-> v ';' m" := (update m x v) (at level 100, v at next level, right associativity).
Notation "x |-> v" := (update empty x v) (at level 100, v at next level, right associativity).

Theorem apply_empty : forall V x, @empty V x = None.
Proof. reflexivity. Qed.

Theorem update_eq : forall V (m : map V) x v,
  (x |-> v; m) x = Some v.
Proof. intros. unfold update. rewrite String.eqb_refl. reflexivity. Qed.

Theorem update_neq: forall V (m : map V) x y v,
  x <> y -> (x |-> v; m) y = m y.
Proof.
  intros. unfold update.
  rewrite <- String.eqb_neq in H. rewrite H.
  reflexivity.
Qed.

Theorem update_shadow: forall V (m : map V) x v1 v2,
  (x |-> v1; x |-> v2; m) x = Some v1.
Proof. intros. unfold update. rewrite String.eqb_refl. reflexivity. Qed.

Theorem update_same: forall V (m : map V) x v,
  m x = Some v -> (x |-> v; m) = m.
Proof.
  intros. apply functional_extensionality. intros y.
  destruct (String.eqb_spec x y).
  - subst y. rewrite H. apply update_eq.
  - apply update_neq. assumption.
Qed.

Theorem update_permute: forall V (m : map V) x1 x2 v1 v2,
  x1 <> x2 -> (x1 |-> v1; x2 |-> v2; m) = (x2 |-> v2; x1 |-> v1; m).
Proof.
  intros. apply functional_extensionality. intros y.
  destruct (String.eqb_spec x1 y).
  - (* y = x1 *)
    subst y. rewrite update_eq.
    rewrite update_neq by auto. rewrite update_eq.
    reflexivity.
  - rewrite update_neq by assumption.
    destruct (String.eqb_spec x2 y).
    + (* y = x2 *)
      subst y. repeat rewrite update_eq. reflexivity.
    + (* y <> x1, y <> x2 *)
      repeat rewrite update_neq by assumption. reflexivity.
Qed.

Definition included_in {V : Type} (m1 m2 : map V) :=
  forall x v, m1 x = Some v -> m2 x = Some v.

Theorem included_in_update: forall V (m1 m2 : map V) x v,
 included_in m1 m2 -> included_in (x |-> v; m1) (x |-> v; m2).
Proof.
  intros. unfold included_in. intros y vy Hy.
  unfold update. destruct (String.eqb_spec x y).
  - subst y. rewrite <- Hy. symmetry. apply update_eq.
  - rewrite update_neq in Hy by assumption.
    unfold included_in in H. apply H. apply Hy.
Qed.

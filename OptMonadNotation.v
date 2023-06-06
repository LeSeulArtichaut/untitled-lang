Declare Scope opt_monad_scope.

Notation "x <- e1 ; e2" := (
  match e1 with
  | None => None
  | Some x => e2
  end
) (right associativity, at level 60) : opt_monad_scope.

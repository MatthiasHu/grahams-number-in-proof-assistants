
(* Definition of Graham's number *)

Definition mult (a : nat) (b : nat) : nat
  := a * b.

Fixpoint iterate (f : nat -> nat -> nat) (a : nat) (b : nat) : nat :=
  match b with
    | 0 => 1
    | (S b') => f a (iterate f a b')
  end.

Fixpoint arrows (n : nat) (a : nat) (b : nat) : nat :=
  match n with
    | 0 => a * b
    | (S n') => iterate (arrows n') a b
  end.

Fixpoint g (n : nat) : nat :=
  match n with
    | 0 => 4
    | (S n') => arrows (g n') 3 3
  end.

Definition G : nat := g 64.

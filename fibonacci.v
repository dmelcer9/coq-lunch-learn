Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Inductive Fibonacci : nat -> nat -> Prop :=
  | Fib1 : Fibonacci 1 1
  | Fib2 : Fibonacci 1 2
  | FibPlus : forall val_1 val_2 seq, Fibonacci val_1 seq -> Fibonacci val_2 (seq + 1) -> Fibonacci (val_1 + val_2) (seq + 2).
Hint Constructors Fibonacci.

Definition f3 : Fibonacci 2 3 := FibPlus Fib1 Fib2.

Definition f4 : Fibonacci 3 4.
  exact (FibPlus Fib2 f3).
Qed.

Print f4.

Definition f6 : Fibonacci 8 6.
  cut (Fibonacci 5 5).
  move=> f5.
  exact (FibPlus f4 f5).
  exact (FibPlus f3 f4).
Qed.

Print f6.

Require Import Coq.Arith.Even.

Print even.

Definition even0: even 0 := even_O.
Definition odd1 : odd 1 := odd_S 0 even0.
Definition odd3: odd 3 := odd_S 2 (even_S 1 odd1).
(* https://coq.inria.fr/library/Coq.Arith.Even.html *)

Lemma even_repeat_3 :
  forall n0 n1 seq,
    Fibonacci n0 seq ->
    Fibonacci n1 (seq + 1) ->
    even n0 ->
    odd n1 ->
    (exists n3,
     Fibonacci n3 (seq + 3) /\ even n3).
  move=> n0 n1 seq fib0 fib1 even0 odd1.
  have fib2: Fibonacci (n0 + n1) (seq + 2).
  (exact (FibPlus fib0 fib1)).
  have plus1 : 2 = (1 + 1). eauto.
  rewrite plus1 in fib2.
  rewrite addnA in fib2.
  exists (n1 + (n0 + n1)).
  split.
  - have->: (3) = (1 + 2). eauto.
    rewrite [(seq + (1 + 2))] addnA.
    exact: (FibPlus fib1 fib2).
  - have odd2: odd (n0 + n1). by apply odd_plus_r.
    by apply odd_even_plus.
Qed.

Print even_repeat_3.

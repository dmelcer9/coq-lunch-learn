Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

(* A basic "language" that consists only of adding and constants *)
Inductive term : Set :=
| N : nat -> term
| Plus : term -> term -> term.
Hint Constructors term.

(* (1 + 0) + 5 *)
Definition randomTerm : term := (Plus (Plus (N 1) (N 0)) (N 5)).

(* An evaluator for our language *)
Fixpoint teval (t : term) :=
  match t with
    | (N x) => x
    | (Plus t1 t2) => (teval t1) + (teval t2)
  end.

(* Prints out 6 *)
Eval compute in (teval randomTerm).


(* Get rid of some +0s *)
Fixpoint compile (t : term) :=
  match t with
  | (N x) => (N x)
  | (Plus (N 0) t2) => compile t2
  | (Plus t1 (N 0)) => compile t1
  | (Plus t1 t2) => (Plus (compile t1) (compile t2))
  end.

Definition compiledRandomTerm : term := (compile randomTerm).

(* Print it out *)
(* Plus (N 1) (N 5) *)
Eval compute in compiledRandomTerm.

(* Also 6 *)
Eval compute in (teval randomTerm).


(* Ignore what this really bad proof is actually doing, this is a whole bunch of code generation steps *)
Lemma compile_correct : forall t,
    (eq (teval t) (teval (compile t))).
  elim.
  - eauto.
  - move=> l IH_l r IH_r.
    simpl.
    case: l IH_l.
    + case.
      * rewrite IH_r.
        reflexivity.
      * move=> n _.
        case: r IH_r.
        -- case.
           ++ simpl.
                rewrite addn0.
                reflexivity.
           ++ by simpl.
        -- move=> t t0 te.
           rewrite te.
           reflexivity.
    + elim: r IH_r.
      * case.
        -- simpl (teval (N 0)).
           intros.
           rewrite addn0.
           assumption.
        -- intros.
           rewrite IH_l.
           constructor.
      * intros.
        rewrite IH_r IH_l.
        constructor.
Qed.

Print compile_correct.


(* Formally define what it means for a step to occur *)
Inductive step : term -> term -> Prop :=
| SPlus1 : forall e1 e1' e2, step e1 e1' -> step (Plus e1 e2) (Plus e1' e2)
| SPlus2 : forall n e2 e2', step e2 e2' -> step (Plus (N n) e2) (Plus (N n) e2')
| SPlus : forall n1 n2, step (Plus (N n1) (N n2)) (N (n1 + n2)).
Hint Constructors step.

(* You can step from (1 + 0) to 1 *)
Definition step_n01 : step (Plus (N 1) (N 0)) (N 1) := SPlus 1 0.

(* You can step from ((1 + 0) + 5) to (1 + 5) *)
(* We could omit the first two arguments to SPlus1 because they can be deduced from its last argument *)
Definition step_randomTerm : step randomTerm (Plus (N 1) (N 5)) := SPlus1 (N 5) step_n01.

(* Less tedious way to do this *)
Lemma step_randomTerm_codegen : step randomTerm (Plus (N 1) (N 5)).
  unfold randomTerm.
  apply: SPlus1.
  apply: SPlus.
Qed.

(* It generates the same code as what we just put in step_randomTerm *)
Print step_randomTerm_codegen.

(* Relation between source and compiled code *)
Inductive sim : term -> term -> Prop :=
| sim_comp t : sim t (compile t).

(* Example of the sim relation *)
Definition example_sim : sim randomTerm compiledRandomTerm := sim_comp randomTerm.

(* Doing something 0 or more times *)
Inductive Rstar {T : Type} (P : T -> T -> Prop) : T -> T -> Prop :=
| RRefl : forall a, Rstar P a a
| RStep : forall a b c, P a b -> Rstar P b c -> Rstar P a c.
Hint Constructors Rstar.

Definition rstar_example : Rstar step randomTerm (N 6).
  apply: RStep.
  exact step_randomTerm.
  apply: RStep.
  exact (SPlus 1 5).
  apply: RRefl.
Qed.

(* Prints out RStep step_randomTerm (RStep (SPlus 1 5) (RRefl step (N (1 + 5)))), we could have manually typed this. *)
Print rstar_example.

(* This proof would be finished if I remembered more from that class *)
Lemma sim_step : forall t1 t1',
   step t1 t1' ->
   forall t2,
   sim t1 t2 ->
   exists t2', Rstar step t2 t2' /\ sim t1' t2'.
 Admitted.

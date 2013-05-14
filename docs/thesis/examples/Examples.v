Extraction Language Haskell.

Module Examples.

Require Import List.
Open Scope list_scope.

Set Contextual Implicit.

Fixpoint append { a : Set } (x0 : list a) (x1 : list a) : list a :=
           match x0, x1 with
             | nil, ys => ys
             | cons x xs, ys => cons x (append xs ys)
           end.

Fixpoint gt (x0 : nat) (x1 : nat) : bool :=
           match x0, x1 with
             | O, O => false
             | O, S n => false
             | S n, O => true
             | S n, S m => gt n m
           end.

Definition le (x0 : nat) (x1 : nat) : bool :=
             match x0, x1 with
               | a, b => negb (gt a b)
             end.

Set Implicit Arguments.

Inductive quicksort_acc : list nat -> Set :=
          | quicksort_acc_0 : quicksort_acc nil
          | quicksort_acc_1 : forall (x : nat) (xs : list nat) , quicksort_acc (filter (gt x) xs) -> quicksort_acc (filter (le x) xs) -> quicksort_acc (cons x xs).

Theorem quicksort_acc_inv_1_0 : forall (x0 : list nat) (x : nat) (xs : list nat) , quicksort_acc x0 -> (x0 = cons x xs) -> quicksort_acc (filter (gt x) xs) .
intros x0 x xs H; case H; try (intros; discriminate). intros x' xs' Hcall0 Hcall1 . intros Heq0; injection Heq0. intros Heq0_ctx_0 Heq0_ctx_1. try (rewrite <- Heq0_ctx_0).  try (rewrite <- Heq0_ctx_1). assumption.
Defined.

Theorem quicksort_acc_inv_1_1 : forall (x0 : list nat) (x : nat) (xs : list nat) , quicksort_acc x0 -> (x0 = cons x xs) -> quicksort_acc (filter (le x) xs) .
intros x0 x xs H; case H; try (intros; discriminate). intros x' xs' Hcall0 Hcall1 . intros Heq0; injection Heq0. intros Heq0_ctx_0 Heq0_ctx_1. try (rewrite <- Heq0_ctx_0).  try (rewrite <- Heq0_ctx_1). assumption.
Defined.

Unset Implicit Arguments.

Fixpoint quicksort (x0 : list nat) (x1 : quicksort_acc x0) : list nat :=
           match x0 as _y0 return (x0 = _y0) -> list nat with
             | nil => fun _h0 => nil
             | cons x xs => fun _h0 => append (quicksort (filter (gt x) xs) (quicksort_acc_inv_1_0 x1 _h0)) (quicksort (filter (le x) xs) (quicksort_acc_inv_1_1 x1 _h0))
           end (refl_equal x0).

End Examples.

Extraction Examples.
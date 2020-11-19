Require Import Ensembles.
Section ltl.

  Context {AP : Set}.

  Inductive Formula :=
  | f_atomic (a : AP)
  | f_neg (f : Formula)
  | f_and (f1 f2 : Formula)
  | f_next (f : Formula)
  | f_until (f1 f2 : Formula)
  .

  Definition Model : Type := nat -> Ensemble AP.

  Fixpoint satisfies (m: Model) (i : nat) (f : Formula) : Prop :=
    match f with
    | f_atomic a => m i a
    | f_neg f' => ~ satisfies m i f'
    | f_and f1 f2 => satisfies m i f1 /\ satisfies m i f2
    | f_next f' => satisfies m (i+1) f'
    | f_until f1 f2 => exists (d: nat), satisfies m (i+d) f2 /\ forall (c:nat), c < d -> satisfies m (i+c) f1
    end.
 

End ltl.

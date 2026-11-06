From ITree Require Import ITree.
From FpyCert Require Import Denote Syntax State.


Variant EvalOut : Type :=
    | Done (v : Value)
    | Panic {X : Type} (e : PanicE X)
    | OutOfFuel.

Fixpoint eval_itree (fuel : nat) (t : FinalTree) : EvalOut :=
    match fuel with
    | O => OutOfFuel
    | S n =>
        match observe t with
        | RetF (_, v) => Done v
        | TauF t' => eval_itree n t'
        | VisF e _ => Panic e
        end
    end.


Definition eval_term (fuel : nat) (t : Term) (env : tlm_env) : EvalOut :=
    eval_itree fuel (handle_base_events (denote_term t) env).
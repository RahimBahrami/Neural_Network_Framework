Require Export Omega.
Require Export List.
Require Export Setoid.
Require Export SetoidPermutation.
Require Export Relation_Definitions.
Require Import Arith.
Require Import ZArith.
Require Export BinNums.
Require Import BinPos BinNat.
Require Import Logic.
Require Import QArith QArith_base Qabs Qpower Qreduction Qring Qfield.
Import ListNotations.

Section NeuralNetwork.

Record Neuron := MakeNeuron {
  Output: list nat;
  Weights: list Q;
  Leak_Factor: Q;
  Tau: Q;
  Current: Q;
}.

Fixpoint nth {T:Type} (l: list T) (ind: nat) : option T :=
  match ind%nat with
  | O => match l with
         | nil => None
         | h::t => (Some h)
        end
  | S n' => match l with
            | nil => None
            | h::t => nth t (ind - 1)
            end
end.

Fixpoint potential (Weights: list Q) (Inputs: list nat): Q :=
  match Weights, Inputs with
  | nil, nil => 0
  | nil, _ => 0
  | _, nil => 0
  | h1::t1, h2::t2 => if (beq_nat h2 0%nat)
                        then (potential t1 t2)
                        else (potential t1 t2) + h1
end.

Definition Qlt_bool (a b: Q): bool :=
  andb (Qle_bool a b) (negb (Qeq_bool b a)).

(* coercion of binary nats to binary Q *)
Definition binQ (n:nat) : option Q :=
match n with
| 0%nat => (Some 0)
| 1%nat => (Some 1)
| _ => None
end.

(* Input = [0;1;1;...] with indexing starting at 1
   n mod 3 = 1 -> nth element of Input is 0
   n mod 3 = 2 -> nth element of Input is 1
   n mod 3 = 0 -> nth element of Input is 1 *)
Inductive series2values : nat -> Neuron -> Neuron -> list Q -> list Q -> Prop :=
| (* This case is before any input is processed *)
  s2v_start : forall (N1 N2: Neuron) (P1 P2: list Q),
    nth (Output N1) 0%nat = (Some 0%nat) ->
    nth (Output N2) 0%nat = (Some 0%nat) ->
    series2values 0 N1 N2 [0] [0]
| (* This case processes the next input *)
  s2v_next : forall (t:nat) (N1 N2: Neuron) (P1 P2: list Q) 
                    (N1o N2o N1o' N2o':nat) (Input:Q) (N1w0 N1w1 N2w qN1o qN2o p1' p2':Q),    
    (((S t) mod 3 = 1%nat /\ Input = 0) \/
     ((S t) mod 3 = 2%nat /\ Input = 1) \/
     ((S t) mod 3 = 0%nat /\ Input = 1)) ->
    (* The following are "known" from the "recursive call" *)
    series2values t N1 N2 P1 P2 ->
    nth (Weights N1) 0%nat = (Some N1w0) -> 
    nth (Weights N1) 1%nat = (Some N1w1) ->
    nth (Weights N2) 0%nat = (Some N2w) ->
    nth (Output N1) t = (Some N1o%nat) ->
    nth (Output N2) t = (Some N2o%nat) ->
    binQ N1o = (Some qN1o) ->
    binQ N2o = (Some qN2o) ->
    (* The following are calculated from the known information *)
    p1' = (qN2o*N1w1)+(Input*N1w0) ->
    p2' = qN1o*N2w ->
    N1o' = (if (Qlt_bool p1' (Tau N1)) then 0%nat else 1%nat) ->
    N2o' = (if (Qlt_bool p2' (Tau N2)) then 0%nat else 1%nat) ->
    nth (Output N1) (S t) = (Some N1o'%nat) ->
    nth (Output N2) (S t) = (Some N2o'%nat) ->
    series2values (S t) N1 N2 (P1 ++ [p1']) (P2 ++ [p2']).


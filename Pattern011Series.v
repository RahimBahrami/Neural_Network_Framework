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


Inductive series2values : nat -> Neuron -> Neuron -> list Q -> list Q -> Prop :=
| s2v_0 : forall (N1 N2: Neuron) (P1 P2: list Q),
    nth (Output N1) 0%nat = (Some 0%nat) ->
    nth (Output N2) 0%nat = (Some 0%nat) ->
    series2values 0 N1 N2 [0] [0].

(* unfinished part
| s2v_1 : forall (N1 N2: Neuron) (P1 P2: list Q) (O1 O2 O1' O2':nat) (w1:Q) (t:nat),
    t = 1 \/ t = 2 ->
    series2values t N1 N2 P1 P2 ->
    nth (Output N1) 0%nat = (Some o1%nat) ->
    nth (Output N2) 0%nat = (Some o2%nat) ->
    nth (Output N1) 1%nat = (Some o1'%nat) ->
    nth (Output N2) 1%nat = (Some o2'%nat) ->
    nth (Weights N1) 0%nat = (Some w1) -> 
    series2values 1 N1 N2 ((o2%Q*w1)::P1) (..::P2).
xxx    
    nth (P1 
    Output1 = (Qlt_bool 
    series2values 1 N1 N2 
    nth (Output N1) 0%nat = (Some 0%nat) ->
    nth (Output N2) 0%nat = (Some 0%nat) ->
    series2values 0 N1 N2 [0] [0]
| sv2_mod1 : forall (N1 N2: Neuron) (P1 P2: list Q) (t:nat),
    t mod 3 = 1%nat \/ ->
    series2values 0 N1 N2 [0] [0].

               t mod 3 = 1 \/ t mod 3 = 2 *)


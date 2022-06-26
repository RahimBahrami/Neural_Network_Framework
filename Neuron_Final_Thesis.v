Require Export Omega.
Require Export List.
Require Export Setoid.
Require Export SetoidPermutation.
Require Export Relation_Definitions.
Require Import Arith.
Require Import ZArith.
Require Export BinNums.
Require Import BinPos BinNat Nat.
Require Import Logic.
Require Import QArith QArith_base Qabs Qpower Qreduction Qring Qfield.
Import ListNotations.
Require Export Lists.List.

Section NeuralNetwork.

Fixpoint Bin_List (In: list nat): Prop :=
  match In with
  | nil => True
  | h::t => (orb (beq_nat h 0%nat) (beq_nat h 1%nat)) = true /\ (Bin_List t)
end.

Definition Qlt_bool (a b: Q): bool :=
  andb (Qle_bool a b) (negb (Qeq_bool b a)).

Fixpoint WeightInRange (Weights: list Q): bool :=
  match Weights with
  | nil => true
  | h::t => andb (Qle_bool h 1) (Qle_bool (-(1)) h)
end.

(*We need to connect Current and Output list in the object*)

Record Neuron := MakeNeuron {
  Output: list nat;
  Weights: list Q;
  Leak_Factor: Q;
  Tau: Q;
  Current: Q;
  Output_Bin: Bin_List Output;
  LeakRange: Qle_bool 0 Leak_Factor = true /\ Qle_bool Leak_Factor 1 = true;
  PosTau: Qlt_bool 0 Tau = true;
  WRange: WeightInRange Weights = true
}.

(*(beq_nat (length (Weights N1)) 2) = true ->
  (beq_nat (length (Weights N2)) 1%nat) = true ->
  (w1 == (hd 0 (Weights N1))) ->
  (w2 == (hd 0 (tl (Weights N1)))) ->
  (w3 == (hd 0 (Weights N2))) ->
  (Qle_bool (Tau N1) (Qabs(w2) - w1)) = true ->
  (Qle_bool (Tau N1) w1) = true ->
  (Qle_bool (Tau N2) w3)  = true ->
  All1 Inputs ->
  Eq_Neuron2 M1 (AfterNArch2N1 (ResetNeuron N1) (ResetNeuron N2) Inputs) ->
   ->
  (lt 1%nat t) -> Index (rev (Output M1)) t 1%nat = 1%nat.*)

Fixpoint potential (Weights: list Q) (Inputs: list nat): Q :=
  match Weights, Inputs with
  | nil, nil => 0
  | nil, _ => 0
  | _, nil => 0
  | h1::t1, h2::t2 => if (beq_nat h2 0%nat)
                        then (potential t1 t2)
                        else (potential t1 t2) + h1
end.

Fixpoint Eq_List (In: list nat) (Out: list nat): bool :=
  match In, Out with
  | nil, nil => true
  | nil, _ => false
  | _, nil => false
  | h::t, h':: t' => (andb (beq_nat h h') (Eq_List t t'))
end.

Fixpoint Eq_ListQ (In: list Q) (Out: list Q): bool :=
  match In, Out with
  | nil, nil => true
  | nil, _ => false
  | _, nil => false
  | h::t, h':: t' => (andb (Qeq_bool h h') (Eq_ListQ t t'))
end.

Fixpoint OneAfterSecond (In: list nat): Prop :=
  match In with
  | nil => False
  | h1::t1 => match t1 with
              | nil => (beq_nat h1 0%nat) = true
              | h2::t2 => match t2 with
                          | nil => (beq_nat h1 0%nat) = true /\ (beq_nat h2 0%nat) = true
                          | h3::t3 => (beq_nat h1 1%nat) = true /\ OneAfterSecond t1
                          end
              end
end.

Fixpoint Index {T:Type} (l: list T) (ind: nat) (def: T): T :=
  match ind with
  | O => match l with
         | nil => def
         | h::t => h
        end
  | S n' => match l with
            | nil => def
            | h::t => Index t n' def
            end
end.

(*Fixpoint RevIndex {T:Type} (l: list T) (ind: nat) (def: T): T :=
  match ind with
  | O => match l with
         | nil => def
         | h::t => RevIndex t O def
         end
  | S ind' => if (beq_nat ind (length l)) then h else (RevIndex T ind')
end.*)

Fixpoint Index1 {T:Type} (l: list T) (ind: nat) (def: T): T :=
  match ind with
  | O => def
  | S O => match l with
            | nil => def
            | h::t => h
            end
  | S n' => match l with
            | nil => def
            | h::t => (Index1 t (ind - 1) (def))
            end
end.


Fixpoint nth {T:Type} (l: list T) (ind: nat) : option T :=
  match ind with
  | O => match l with
         | nil => None
         | h::t => (Some h)
        end
  | S ind' => match l with
            | nil => None
            | h::t => nth t ind'
            end
end.

Fixpoint PatternAcc {T: Type} (P: list T) (l: list T) (ind: nat): Prop :=
  match P with
  | nil => True
  | h::t => if (beq_nat ind ((length l) - 1)) then
               (nth l ind) = Some h /\ PatternAcc t l 0%nat
            else
               (nth l ind) = Some h /\ PatternAcc t l (ind + 1)
end.

Fixpoint Pattern {T: Type} (P: list T) (l: list T) (ind: nat): Prop :=
  match ind with
  | O => PatternAcc P l 0%nat
  | S ind' => Pattern (tl P) l ind'
end. 

Compute (Index [2;5;6;7;9;10] 3 100).
Compute (Index1 [2;5;6;7;9;10] 3 100).

Check Qle_bool.

Definition NextPotential (N: Neuron) (Inputs: list nat): Q :=
  if (Qle_bool (Tau N) (Current N))
      then  (potential (Weights N) Inputs)
      else  (potential (Weights N) Inputs) + (Leak_Factor N) * (Current N).

Definition NextOutput (N: Neuron) (Inputs: list nat) : nat :=
  if (Qle_bool (Tau N) (NextPotential N Inputs))
      then 1%nat
      else 0%nat.

Lemma NextOutput_Bin_List: forall (N: Neuron) (Inputs: list nat),
    Bin_List (Output N) -> Bin_List (NextOutput N Inputs::Output N).
Proof.
  intros. simpl. split.
  - unfold NextOutput. destruct (Qle_bool (Tau N) (NextPotential N Inputs)).
    + simpl. reflexivity.
    + simpl. reflexivity.
  - apply H.
Qed.

Definition NextNeuron (N: Neuron) (Inputs: list nat): Neuron := MakeNeuron
  ((NextOutput N Inputs)::(Output N))
  (Weights N)
  (Leak_Factor N)
  (Tau N)
  (NextPotential N Inputs)
  (NextOutput_Bin_List N Inputs (Output_Bin N))
  (LeakRange N)
  (PosTau N)
  (WRange N).

(*Compute NextOutput (MakeNeuron ([0%nat]) ([Qmake 5 10]) (Qmake 1 10) (Qmake 3 10) (0)) [1%nat].
Compute NextNeuron (MakeNeuron ([0%nat]) ([Qmake 5 10]) (Qmake 1 10) (Qmake 3 10) (Qmake 5 10)) [1%nat].*)

Definition binQ (n:nat) : option Q :=
match n with
| 0%nat => (Some 0)
| 1%nat => (Some 1)
| _ => None
end.

Fixpoint Delayer_Effect (In: list nat) (Out: list nat): Prop :=
  match In with
  | nil => match Out with
           | nil => False
           | h2::t2 => (beq_nat h2 0%nat) = true /\ t2 = nil
           end
  | h1::t1 => match Out with
              | nil => False
              | h2::t2 => (beq_nat h1 h2) = true /\ (Delayer_Effect t1 t2)
              end
end.

Fixpoint NZeros (n: nat): list nat :=
  match n with
  | O => nil
  | S n' => 0%nat::NZeros n'
end.

Fixpoint RestAfterN (l: list nat) (n: nat): (list nat) :=
  match l with
  | nil => nil
  | h::t => if (beq_nat n 0%nat) then l else (RestAfterN t (n - 1))
end.
     
Fixpoint NDelayer_Effect (In: list nat) (Out: list nat) (n: nat): Prop :=
  match In with
  | nil => Out = NZeros n
  | h1::t1 => match Out with
              | nil => False
              | h2::t2 => (beq_nat h1 h2) = true /\ NDelayer_Effect t1 t2 n
              end
end.

Definition Start_with (l: list nat) (x: nat): bool :=
  match l with
  | nil => false
  | h::t => beq_nat h x
end.

Fixpoint Consecutive (l: list nat) (x: nat): bool :=
  match l with
  | nil => true
  | h::t => if (beq_nat h x)
               then (andb (negb (Start_with t x)) (Consecutive t x))
               else Consecutive t x
end.

Fixpoint Filter_Effect (Out: list nat): Prop :=
  match Out with
  | nil => False
  | h1::t1 => match t1 with
            | nil => False
            | h2::t2 => match t2 with
                        | nil => (beq_nat h1 0%nat) = true /\ (beq_nat h2 0%nat) = true
                        | h3::t3 => if (beq_nat h1 0%nat)
                                    then Filter_Effect t1
                                    else ((beq_nat h2 0%nat) = true) /\ Filter_Effect t1
                        end
              end
end.

Fixpoint Pattern011 (In: list nat): Prop :=
  match In with
  | nil => True
  | h1::t1 => match t1 with
            | nil => (beq_nat h1 0%nat) = true
            | h2::t2 => match t2 with
                        | nil => (beq_nat h1 0%nat) = true /\ (beq_nat h2 1%nat) = true
                        | h3::t3 => (beq_nat h1 0%nat) = true /\ (beq_nat h2 1%nat) = true /\ (beq_nat h3 1%nat) = true /\ (Pattern011 t3)
                        end
              end
end.

Fixpoint All1(Input: list nat): Prop :=
  match Input with
  | nil => True
  | h::t => (beq_nat h 1%nat) = true /\ (All1 t)
end.

Fixpoint All0(Input: list nat): Prop :=
  match Input with
  | nil => True
  | h::t => (beq_nat h 0%nat) = true /\ (All0 t)
end.


Print Visibility.

Lemma Reset_Output: Bin_List [0%nat].
Proof.
  simpl. split. reflexivity. apply I.
Qed.

Definition ResetNeuron (N: Neuron): Neuron := MakeNeuron
  ([0%nat])  
  (Weights N)
  (Leak_Factor N)
  (Tau N)
  (0)
  (Reset_Output)
  (LeakRange N)
  (PosTau N)
  (WRange N).

Print QArith_base.
(*Compute MakeNeuron (nil) ([Qmake 5 10]) (Qmake 1 10) (Qmake 3 10) (0).
Compute Output (NextNeuron (MakeNeuron (nil) ([Qmake 5 10]) (Qmake 1 10) (Qmake 3 10) (0)) [1%nat]).*) 

(*Hypothesis Output_Bin: forall N: Neuron, Bin_List (Output N).
Hypothesis LeakRange: forall N: Neuron, Qle_bool 0 (Leak_Factor N) = true /\ Qle_bool (Leak_Factor N) 1 = true .
Hypothesis PosTau: forall N: Neuron, Qlt_bool 0 (Tau N) = true.
Hypothesis WRange: forall N: Neuron, (WeightInRange (Weights N)) = true.*)

(*Lemma PosTau_bool: forall N: Neuron,*)

(*Fixpoint ProduceNoutputs (N: Neuron) (In: list nat): list nat :=
  match In with
  | nil => [0%nat]
  | h::t => ProduceNoutputs
              (MakeNeuron
              ((Output N) ++ [NextOutput N t])
              (Weights N)
              (Leak_Factor N)
              (Tau N)
              (NextPotential N [h])) t
end.*)

Fixpoint AfterNsteps (N: Neuron) (In: list nat): Neuron :=
  match In with
  | nil => N
  | h::t => NextNeuron (AfterNsteps N t) [h]
end.

Fixpoint AfterNstepsM (N: Neuron) (In: list (list nat)): Neuron :=
  match In with
  | nil => N
  | h::t => NextNeuron (AfterNstepsM N t) h
end.

Fixpoint SeriesNetworkOutput (Input: list nat) (NeuronList: list Neuron): (list nat) :=
  match NeuronList with
  | nil => Input
  | h::t => (Output (AfterNsteps (ResetNeuron h) (SeriesNetworkOutput Input t)))
end.

Fixpoint AllDelayers (NeuronList: list Neuron): Prop :=
  match NeuronList with
  | nil => True
  | h::t => (beq_nat (length (Weights h)) 1%nat) = true /\ 
             Qle_bool (Tau h) (hd 0 (Weights h)) = true /\
             AllDelayers t
end.

Fixpoint AllPositive (l: list Q): Prop :=
  match l with
  | nil => True
  | h::t => 0 < h /\ AllPositive t
end.

Fixpoint AllNegative (l: list Q): Prop :=
  match l with
  | nil => True
  | h::t =>  h <= 0 /\ AllNegative t
end.

Fixpoint AllBinary (input: list (list nat)): Prop :=
  match input with
  | nil => True
  | h::t =>  Bin_List h /\ AllBinary t
end.

Fixpoint AllLengthN (input: list (list nat)) (n: nat): Prop :=
  match input with
  | nil => True
  | h::t =>  (beq_nat n (length h)) = true /\ AllLengthN t n
end.

(*Compute (AfterNsteps (MakeNeuron ([0%nat]) ([Qmake 5 10]) (Qmake 1 10) (Qmake 3 10) (0)) [1%nat; 1%nat]).
Example Test_After:
  Output (AfterNsteps (MakeNeuron ([0%nat]) ([Qmake 5 10]) (Qmake 1 10) (Qmake 3 10) (0)) [1%nat]) = [1%nat;0%nat].
Proof.
  simpl. 
  unfold NextOutput. simpl. reflexivity.
Qed.*)

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
    (((S t) mod 3 = 1%nat /\ Input == 0) \/
     ((S t) mod 3 = 2%nat /\ Input == 1) \/
     ((S t) mod 3 = 0%nat /\ Input == 1)) ->
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
    p1' == (qN2o*N1w1)+(Input*N1w0) ->
    p2' == qN1o*N2w ->
    N1o' = (if (Qlt_bool p1' (Tau N1)) then 0%nat else 1%nat) ->
    N2o' = (if (Qlt_bool p2' (Tau N2)) then 0%nat else 1%nat) ->
    nth (Output N1) (S t) = (Some N1o'%nat) ->
    nth (Output N2) (S t) = (Some N2o'%nat) ->
    series2values (S t) N1 N2 (P1 ++ [p1']) (P2 ++ [p2']).

Inductive series2neurons : nat -> Neuron -> Neuron -> Prop :=
| (* This case is before any input is processed *)
  s2v_base : forall (N1 N2: Neuron),
    (length (Output N1) = 1%nat) ->
    (length (Output N2) = 1%nat) ->
    (hd 1%nat (Output N1)) = 0%nat ->
    (hd 1%nat (Output N2)) = 0%nat ->
    series2neurons 0 N1 N2
| (* This case processes the next input *)
  s2v_ind : forall (t:nat) (N1 N2: Neuron) (Input:nat),    
    (((S t) mod 3 = 1%nat /\ Input = 0%nat) \/
     ((S t) mod 3 = 2%nat /\ Input = 1%nat) \/
     ((S t) mod 3 = 0%nat /\ Input = 1%nat)) ->
    (* The following are "known" from the "recursive call" *)
    series2neurons t N1 N2 ->
    (length (Output N1) = (S t)) ->
    (length (Output N2) = (S t)) ->
    series2neurons (S t) (NextNeuron N1 [Input;(hd 0%nat (Output N2))]) (NextNeuron N2 [(hd 0%nat (Output N1))]).

Fixpoint even n :=
match n with
| O => true
| S n' => odd n'
end
with odd n :=
match n with
| O => false
| S n' => even n'
end.

Fixpoint AfterNTwoLoopN1 (N1 N2: Neuron) (Inputs: list nat): Neuron :=
  match Inputs with
  | nil => N1
  | h::t => NextNeuron (AfterNTwoLoopN1 N1 N2 t) [h; (hd 0%nat (Output (AfterNTwoLoopN2 N1 N2 t)))]
  end
with AfterNTwoLoopN2 N1 N2 Inputs :=
  match Inputs with
  | nil => N2
  | h::t => NextNeuron (AfterNTwoLoopN2 N1 N2 t) [(hd 0%nat (Output (AfterNTwoLoopN1 N1 N2 t)))] 
end.

(*Fixpoint AfterNNegLoopN1 (N1 N2: Neuron) (Inputs: list nat): Neuron :=
  match Inputs with
  | nil => N1
  | h::t => AfterNArch2N1 (NextNeuron N1 [h;(hd 2%nat (Output N2))]) (NextNeuron N2 [(hd 2%nat (Output N1))]) t
end.

Fixpoint AfterNArch2N2 (N1 N2: Neuron) (Inputs: list nat): Neuron :=
  match Inputs with
  | nil => N2
  | h::t => AfterNArch2N2 (NextNeuron N1 [h;(hd 2%nat (Output N2))]) (NextNeuron N2 [(hd 0%nat (Output N1))]) t
end.*)

Fixpoint AfterNCIN1 (N1 N2: Neuron) (Inp1 Inp2: list nat): Neuron :=
  match Inp1 with
  | nil => N1
  | h::t => AfterNCIN1 (NextNeuron N1 [h;(hd (2%nat) (Output N2))]) (NextNeuron N2 [(hd (0%nat) Inp2);(hd (2%nat) (Output N1))]) t (tl Inp2)
end.

Fixpoint AfterNCIN2 (N1 N2: Neuron) (Inp1 Inp2: list nat): Neuron :=
  match Inp2 with
  | nil => N2
  | h::t => AfterNCIN2 (NextNeuron N1 [(hd (0%nat) Inp1);(hd (2%nat) (Output N2))]) (NextNeuron N2 [h;(hd (2%nat) (Output N1))]) (tl Inp1) t
end.

Definition Eq_Neuron (N: Neuron) (M: Neuron): bool :=
  (andb
  (andb
  (andb (Eq_List (Output N) (Output M)) (Eq_ListQ (Weights N) (Weights M)))
  (andb (Qeq_bool (Leak_Factor N) (Leak_Factor M)) (Qeq_bool (Tau N) (Tau M))))
  (Qeq_bool (Current N) (Current M))).

Definition Eq_Neuron2 (N: Neuron) (M: Neuron): Prop :=
  (Output N) = (Output M) /\ (Weights N) = (Weights M) /\
  (Leak_Factor N) == (Leak_Factor M) /\ (Tau N) == (Tau M) /\
  (Current N) == (Current M).

Lemma Neuron_Equality: forall (N: Neuron) (M: Neuron),
  Eq_Neuron N M = true -> Eq_List    (Output N) (Output M) = true /\
                          Eq_ListQ   (Weights N) (Weights M) = true /\
                          Qeq_bool (Leak_Factor N) (Leak_Factor M) = true /\
                          Qeq_bool (Tau N) (Tau M) = true  /\
                          Qeq_bool (Current N) (Current M) = true.
Proof. 
   intros. unfold Eq_Neuron in H. unfold andb in H.
   destruct (Eq_List (Output N) (Output M)).
   {  destruct (Eq_ListQ (Weights N) (Weights M)).
      {  destruct (Qeq_bool (Leak_Factor N) (Leak_Factor M)).
         {  destruct (Qeq_bool (Tau N) (Tau M)).
            { destruct (Qeq_bool (Current N) (Current M)).
              { split; auto. }
              { split; auto. } }
            { destruct (Qeq_bool (Current N) (Current M)).
              { split; auto. }
              { split; auto. } } }
         {  destruct (Qeq_bool (Tau N) (Tau M)).
            { destruct (Qeq_bool (Current N) (Current M)).
              { split; auto. }
              { split; auto. } }
            { destruct (Qeq_bool (Current N) (Current M)).
              { split; auto. }
              { split; auto. } } } }
      {  destruct (Qeq_bool (Leak_Factor N) (Leak_Factor M)).
         {  destruct (Qeq_bool (Tau N) (Tau M)).
            { destruct (Qeq_bool (Current N) (Current M)).
              { split; auto. }
              { split; auto. } }
            { destruct (Qeq_bool (Current N) (Current M)).
              { split; auto. }
              { split; auto. } } }
         {  destruct (Qeq_bool (Tau N) (Tau M)).
            { destruct (Qeq_bool (Current N) (Current M)).
              { split; auto. }
              { split; auto. } }
            { destruct (Qeq_bool (Current N) (Current M)).
              { split; auto. }
              { split; auto. } } } } }
  {  destruct (Eq_ListQ (Weights N) (Weights M)).
      {  destruct (Qeq_bool (Leak_Factor N) (Leak_Factor M)).
         {  destruct (Qeq_bool (Tau N) (Tau M)).
            { destruct (Qeq_bool (Current N) (Current M)).
              { split; auto. }
              { split; auto. } }
            { destruct (Qeq_bool (Current N) (Current M)).
              { split; auto. }
              { split; auto. } } }
         {  destruct (Qeq_bool (Tau N) (Tau M)).
            { destruct (Qeq_bool (Current N) (Current M)).
              { split; auto. }
              { split; auto. } }
            { destruct (Qeq_bool (Current N) (Current M)).
              { split; auto. }
              { split; auto. } } } }
      {  destruct (Qeq_bool (Leak_Factor N) (Leak_Factor M)).
         {  destruct (Qeq_bool (Tau N) (Tau M)).
            { destruct (Qeq_bool (Current N) (Current M)).
              { split; auto. }
              { split; auto. } }
            { destruct (Qeq_bool (Current N) (Current M)).
              { split; auto. }
              { split; auto. } } }
         {  destruct (Qeq_bool (Tau N) (Tau M)).
            { destruct (Qeq_bool (Current N) (Current M)).
              { split; auto. }
              { split; auto. } }
            { destruct (Qeq_bool (Current N) (Current M)).
              { split; auto. }
              { split; auto. } } } } }
Qed.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P [] H.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. inversion H'.
Qed.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  destruct contra.
Qed.

Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P [] H.
  - split.
    + reflexivity.
    + intros H1. inversion H. apply H0.
  - split.
    + intros H1. inversion H. unfold not in H0. apply ex_falso_quodlibet. inversion H. 
      apply H0 in H1. apply H1.
    + intros H1. inversion H1.
Qed.
       
Lemma beq_natP : forall n m, reflect (n = m) (beq_nat n m).
Proof.
  intros n m.
  apply iff_reflect. rewrite beq_nat_true_iff. reflexivity.
Qed.

Lemma Delayer_lists: forall (In Out: list nat),
  Delayer_Effect In Out -> Out = In ++ [0%nat].
Proof.
  induction In as [|h1 t1].
  - intros. simpl. destruct Out as [|h2 t2] eqn: HO.
    + simpl in H. inversion H.
    + simpl in H. inversion H as [H1 H2]. rewrite H2. generalize (beq_natP h2 0);intro HB.
      apply reflect_iff in HB. inversion HB as [HB1 HB2]. apply HB2 in H1. rewrite H1. auto.
  - intros. simpl. destruct Out as [|h2 t2] eqn: HO.
    + simpl in H. inversion H.
    + simpl in H. generalize (IHt1 t2); intro HT. inversion H as [H1 H2].
      apply HT in H2. rewrite H2. generalize (beq_natP h1 h2);intro HB.
      apply reflect_iff in HB. inversion HB as [HB1 HB2]. apply HB2 in H1.
      rewrite H1. reflexivity.
Qed.

Lemma Not_nil_Output: forall (In: list nat) (N: Neuron),
  Output (AfterNsteps (ResetNeuron N) In) <> nil.
Proof.
  destruct In as [|h l ].
  - intros N H. simpl in H. inversion H.
  - intros N H. simpl in H. unfold NextOutput in H.
    destruct (Qle_bool (Tau (AfterNsteps (ResetNeuron N) l))
        (NextPotential (AfterNsteps (ResetNeuron N) l) [h])).
    + inversion H.
    + inversion H.
Qed.

Lemma Not_nil_Tail: forall (N: Neuron) (In: list nat),
  In <> nil -> tl (Output (AfterNsteps (ResetNeuron N) In)) <> nil.
Proof.
  intros. destruct In as [|h l].
  - unfold not in H. simpl. unfold not. apply H.
  - simpl. unfold not. intros H1. generalize (Not_nil_Output l N); intro HNN.
    unfold not in HNN. apply HNN in H1. apply H1.
Qed. 

Lemma ZeroOne: forall (l: list nat),
  Bin_List l -> (beq_nat (hd 0%nat l) 0%nat) = true \/ (beq_nat (hd 0%nat l) 1%nat) = true.
Proof.
  destruct l as [|h t].
  - simpl. left. reflexivity.
  - intros H. simpl in H. inversion H as [H1 H2]. unfold orb in H1.
    simpl. destruct (beq_nat h 0).
           + left. reflexivity.
           + right. apply H1.
Qed.

Lemma HeadZeroFilter: forall (l: list nat),
  (beq_nat (hd 1%nat l) 0%nat) = true /\ Filter_Effect (tl l) -> Filter_Effect l.
Proof.
  intros. inversion H as [H1 H2].
  destruct l as [|h t].
  - simpl in H2. inversion H2.
  - simpl in H2. 
    destruct t as [|h' t'].
    + simpl in H2. inversion H2.
    + destruct t' as [|h1 t1].
      * simpl in H2. inversion H2.
      * simpl in H1. generalize (beq_natP h 0);intro HB.
        apply reflect_iff in HB. inversion HB as [HB1 HB2]. apply HB2 in H1.
        rewrite H1. assert (H': Filter_Effect (0%nat::h'::h1::t1) = Filter_Effect (h'::h1::t1)).
        { reflexivity. } auto.
Qed.

Lemma LengthZero: forall {T: Type} (l: list T),
  (beq_nat (length l) 0%nat) = true -> l = nil.
Proof.
  intros. destruct l as [|h t].
  - reflexivity.
  - inversion H.
Qed.

Lemma PosMult: forall (x y: Q),
  Qle_bool 0 x = true /\ Qle_bool 0 y = true -> Qle_bool 0 (x * y) = true.
Proof.
  intros. inversion H as [H1 H2].
  apply Qle_bool_iff. apply Qle_bool_iff in H1. apply Qle_bool_iff in H2.
  apply Qmult_le_0_compat. apply H1. apply H2.
Qed.

Lemma TailStartZeroFilter: forall (l: list nat),
  (beq_nat (hd 1%nat (tl l)) 0%nat) = true /\ Filter_Effect (tl l) -> Filter_Effect l.
Proof.
  intros. inversion H as [H1 H2]. destruct l as [|h t].
  - simpl in H2. inversion H2.
  - simpl in H2. destruct t as [|h' t'].
    + simpl in H2. inversion H2.
    + destruct t' as [|h1 t1].
      * simpl in H2. inversion H2.
      * simpl in H1. generalize (beq_natP h' 0);intro HB.
        apply reflect_iff in HB. inversion HB as [HB1 HB2]. apply HB2 in H1.
        rewrite H1. rewrite H1 in H2. destruct (beq_nat h 0) eqn: H3.
        { generalize (beq_natP h 0);intro HB'.
          apply reflect_iff in HB'. inversion HB' as [HB3 HB4]. apply HB4 in H3.
          rewrite H3.
          assert (H': Filter_Effect (0%nat::0%nat::h1::t1) = Filter_Effect (0%nat::h1::t1)).
          { reflexivity. } auto. }
        { simpl. rewrite H3. split. 
          { reflexivity. }
          { simpl in H2. apply H2. } }
Qed.

Lemma Unchanged: forall (N: Neuron) (Inputs: list nat),
  (Leak_Factor N) == Leak_Factor (AfterNsteps N Inputs) /\ 
  (Tau N) == (Tau (AfterNsteps N Inputs)) /\
  (Weights N) = (Weights (AfterNsteps N Inputs)).
Proof.
  intros.  induction Inputs as [|h t].
  - simpl. split. reflexivity. split. reflexivity. reflexivity.
  - inversion IHt as [H1 [H2 H3]]. simpl. split.
    + apply H1.
    + split.
      * apply H2.
      * apply H3.
Qed.

Lemma UnchangedM: forall (N: Neuron) (Inputs: list (list nat)),
  (Leak_Factor N) == Leak_Factor (AfterNstepsM N Inputs) /\ 
  (Tau N) == (Tau (AfterNstepsM N Inputs)) /\
  (Weights N) = (Weights (AfterNstepsM N Inputs)).
Proof.
  intros.  induction Inputs as [|h t].
  - simpl. split. reflexivity. split. reflexivity. reflexivity.
  - inversion IHt as [H1 [H2 H3]]. simpl. split.
    + apply H1.
    + split.
      * apply H2.
      * apply H3.
Qed.

Lemma ListForm: forall {T: Type} (l: list T),
  (beq_nat (length l) 1%nat) = true -> exists hq:T, l = hq::nil.
Proof.
  intros. destruct l as [|h t].
  - simpl in H. inversion H.
  - simpl in H. apply LengthZero in H. rewrite H. exists h. reflexivity.
Qed.

Lemma ListForm2: forall {T: Type} (l:list T),
  (beq_nat (length l) 2%nat) = true -> exists hq1 hq2:T, l = hq1::hq2::nil.
Proof.
  intros. destruct l as [|h t].
  - simpl in H. inversion H.
  - destruct t as [|h' t'].
    + simpl in H. inversion H.
    + simpl in H. apply LengthZero in H. rewrite H.
      exists h. exists h'. reflexivity.
Qed.

Lemma ResetUnchanged: forall (N: Neuron),
  (Leak_Factor N) == Leak_Factor (ResetNeuron N) /\ 
  (Tau N) == (Tau (ResetNeuron N)) /\
  (Weights N) = (Weights (ResetNeuron N)).
Proof.
  intros. simpl. split.
  - reflexivity.
  - split.
    + reflexivity.
    + reflexivity.
Qed.

Lemma ReflexivityNeuron: forall (N: Neuron),
  Eq_Neuron2 N N.
Proof.
  intros. unfold Eq_Neuron2.
  split. reflexivity. split. reflexivity. split. reflexivity.
  split; reflexivity.
Qed.
 
Lemma NextNeuronUnchanged: forall (N: Neuron) (Inputs: list nat),
  (Leak_Factor N) == Leak_Factor (NextNeuron N Inputs) /\ 
  (Tau N) == (Tau (NextNeuron N Inputs)) /\
  (Weights N) = (Weights (NextNeuron N Inputs)).
Proof.
  intros. simpl. split.
  - reflexivity.
  - split.
    + reflexivity.
    + reflexivity.
Qed.

Lemma Qlt_bool_iff: forall (x y : Q),
   Qlt_bool x y = true <-> x < y.
Proof.
   intros. split.
   - intros H. unfold Qlt_bool in H. unfold andb in H.
     destruct (Qle_bool x y) eqn: H0.
     + unfold negb in H.
       destruct (Qeq_bool y x) eqn: H1.
       * inversion H.
       * apply Qle_bool_iff in H0. apply Qeq_bool_neq in H1.
         apply Qle_lteq in H0. inversion H0.
         { apply H2. }
         { rewrite <- H2 in H1. unfold not in H1. generalize (Qeq_refl x); intro HQR.
           apply H1 in HQR. inversion HQR. }
    + inversion H.
  - intros H. unfold Qlt_bool. unfold andb.
    destruct (Qle_bool x y) eqn: H0.
    + unfold negb. destruct (Qeq_bool y x) eqn: H1.
      * apply Qeq_bool_iff in H1. apply Qlt_not_eq in H. unfold not in H.
        rewrite H1 in H. generalize (Qeq_refl x); intro HQR. apply H in HQR. inversion HQR.
      * reflexivity.
    + apply Qlt_le_weak in H. apply Qle_bool_iff in H. rewrite H in H0. inversion H0.
Qed.

Instance Qltb_comp : Proper (Qeq==>Qeq==>eq) Qlt_bool.
Proof.
 intros p q H r s H'; apply eq_true_iff_eq.
 rewrite 2 Qlt_bool_iff, H, H'; split; auto with qarith.
Qed.

Lemma Qlt_bool_not_iff: forall (x y: Q),
  Qlt_bool x y = false <-> ~ x < y.
Proof.
  intros. split.
  - intros H. unfold Qlt_bool in H. unfold andb in H.
    destruct (Qle_bool x y) eqn: H1.
    + destruct (Qeq_bool y x) eqn: H2.
      * apply Qeq_bool_iff in H2. unfold not. intro H3.
        apply Qlt_not_eq in H3. unfold not in H3. apply Qeq_sym in H2.
        apply H3 in H2. auto.
      * simpl in H. inversion H.
    + unfold not. intro H2. apply Qlt_le_weak in H2.
      apply Qle_bool_iff in H2. rewrite H2 in H1. inversion H1.
  - intros H. unfold not in H. unfold Qlt_bool. unfold andb.
    destruct (Qle_bool x y) eqn: H1.
    + apply Qle_bool_iff in H1. apply Qle_lteq in H1.
      inversion H1 as [H2 | H3].
      * apply H in H2. inversion H2.
      * apply Qeq_sym in H3. apply Qeq_bool_iff in H3. rewrite H3.
        reflexivity.
    + reflexivity.
Qed.

Lemma Qle_bool_not_iff: forall (x y: Q),
  Qle_bool x y = false <-> ~ x <= y.
Proof.
  intros. split.
  - intros H. unfold not. intros H1. apply Qle_bool_iff in H1.
    rewrite H1 in H. inversion H.
  - intros H. unfold not in H. destruct (Qle_bool x y) eqn: H'.
    + apply Qle_bool_iff in H'. apply H in H'. inversion H'.
    + reflexivity.
Qed.

Lemma LessThanOneFactor: forall (x y z: Q),
  Qlt_bool 0 z = true /\ Qlt_bool x z = true /\ 
  Qle_bool 0 y = true /\ Qle_bool y 1 = true -> Qlt_bool (y * x) z = true.
Proof.
  intros. inversion H as [H1 [H2 [H3 H4]]].
  apply Qlt_bool_iff in H1.
  apply Qlt_bool_iff in H2.
  apply Qle_bool_iff in H3.
  apply Qle_bool_iff in H4.
  apply Qlt_bool_iff.
  rewrite Qmult_comm.
  apply Qle_lteq in H3.
  apply Qle_lteq in H4.
  inversion H3 as [H5 | H6].
  - inversion H4 as [H7 | H8].
    + generalize (Qmult_lt_r x z y); intro HQL.
      generalize (Qmult_lt_r y 1 z); intro HQ1.
      apply HQL in H5. apply HQ1 in H1.
          apply H5 in H2. apply H1 in H7. rewrite Qmult_comm in H7.
          rewrite Qmult_1_l in H7.
          generalize (Qlt_trans (x * y) (z * y) z); intro HQT.
          apply HQT in H2. auto. auto.
    + rewrite H8. rewrite Qmult_1_r. auto. 
  - rewrite <- H6. rewrite Qmult_0_r. auto. 
Qed. 

Lemma LastOutputZero: forall (l: list nat) (N M: Neuron),
  Eq_Neuron2 M (AfterNsteps (ResetNeuron N) l) /\ 
  (beq_nat (length (Weights N)) 1%nat) = true /\  
  Qlt_bool (Current M) (Tau M) = true -> 
  beq_nat (hd 1%nat (Output M)) 0%nat = true.
Proof.
  destruct l as [|h t].
  - intros. unfold Eq_Neuron2 in H. simpl in H.
    inversion H as [H1 H2]. inversion H1 as [H3 [H4 [H5 H6]]].
    rewrite H3. simpl. reflexivity.
  - intros. generalize (Unchanged (ResetNeuron N) (h::t)); intro HU.
    unfold Eq_Neuron2 in H. inversion H as [H1 [H2 H3]].
    inversion H1 as [H4 [H5 [H6 [H7 H8]]]]. 
    inversion HU as [HU1 [HU2 HU3]]. 
    generalize (ResetUnchanged N); intro HR. 
    inversion HR as [HR1 [HR2 HR3]]. rewrite <- HR3 in HU3.
    rewrite <- HU3 in H5. rewrite <- H5 in H2.
    apply ListForm in H2. destruct H2 as [hq H2].
    destruct (Output M) as [|h' t'].
    + inversion H4.
    + inversion H4. simpl.
      remember (AfterNsteps (ResetNeuron N) t)as T.
      unfold NextOutput.
      unfold NextPotential.
      destruct (Qle_bool (Tau T) (Current T)) eqn: H'.
      * rewrite HU3 in H5. simpl in H5. rewrite <- HeqT in H5.
        rewrite H5 in H2. rewrite H2. unfold potential.
        destruct (beq_nat h 0%nat) eqn:HBN.
        { generalize (PosTau T); intro HPT.
          destruct (Qle_bool (Tau T) 0) eqn: HQ.
          { apply Qlt_bool_iff in HPT. apply Qlt_not_le in HPT.
            unfold not in HPT. apply Qle_bool_iff in HQ.
            apply HPT in HQ. inversion HQ. }
          { reflexivity. } }
        { simpl. simpl in H8. rewrite <- HeqT in H8.
          unfold NextPotential in H8. rewrite H' in H8.
          rewrite H2 in H8. unfold potential in H8.
          rewrite HBN in H8. rewrite <- H8. simpl in H7.
          rewrite <- HeqT in H7. rewrite <- H7.
          apply Qlt_bool_iff in H3. apply Qlt_not_le in H3.
          unfold not in H3.
          destruct (Qle_bool (Tau M) (Current M)) eqn: HTC.
          { apply Qle_bool_iff in HTC. apply H3 in HTC.
            inversion HTC. } { reflexivity. } }
      * simpl in HU3. rewrite <- HeqT in HU3. 
        rewrite HU3 in H5. rewrite H5 in H2. rewrite H2. 
        unfold potential. destruct (beq_nat h 0%nat) eqn:HBN.
        { rewrite Qplus_0_l. apply Qle_bool_not_iff in H'.
          apply Qnot_le_lt in H'.
          generalize (LeakRange T); intro HLT.
          generalize (LessThanOneFactor (Current T) (Leak_Factor T) (Tau T)); intro HLOF.
          generalize (PosTau T); intro HP.
          apply Qlt_bool_iff in H'.
          assert (HL: Qlt_bool 0 (Tau T) = true /\
                      Qlt_bool (Current T) (Tau T) = true /\
                      Qle_bool 0 (Leak_Factor T) = true /\ Qle_bool (Leak_Factor T) 1 = true).
          { split; auto. }
          apply HLOF in HL. apply Qlt_bool_iff in HL.
          apply Qlt_not_le in HL. apply Qle_bool_not_iff in HL.
          rewrite HL. reflexivity. }
        { rewrite Qplus_0_l. simpl in H8. rewrite <- HeqT in H8.
          unfold NextPotential in H8. rewrite H' in H8.
          rewrite H2 in H8. unfold potential in H8. rewrite HBN in H8.
          rewrite Qplus_0_l in H8. rewrite <- H8. simpl in H7.
          rewrite <- HeqT in H7. rewrite <- H7.
          apply Qlt_bool_iff in H3. apply Qlt_not_le in H3.
          apply Qle_bool_not_iff in H3. rewrite H3. reflexivity. }
Qed.

Lemma AddPos: forall (x y z: Q),
  Qle_bool x y = true /\ Qle_bool 0 z = true -> Qle_bool x (y + z) = true.
Proof.
  intros. inversion H as [H1 H2]. 
  apply Qle_bool_iff in H1.
  apply Qle_bool_iff in H2.
  apply Qle_bool_iff.
  generalize (Qplus_le_compat x y 0 z); intro HQLC.
  apply HQLC in H1. rewrite Qplus_0_r in H1. auto. auto.
Qed.

Lemma Eq_reverse: forall (m n: Q),
  Qlt_bool m n = true <-> Qle_bool n m = false.
Proof.
  intros. split.
  - intros H. destruct (Qle_bool n m) eqn: H0.
    + apply Qlt_bool_iff in H. apply Qle_bool_iff in H0. apply Qle_not_lt in H0.
      unfold not in H0. apply H0 in H. inversion H.
    + reflexivity. 
  - intros H. destruct (Qlt_bool m n) eqn: H0.
    + reflexivity.
    + unfold Qlt_bool in H0. unfold andb in H0. destruct (Qle_bool n m) eqn: H1.
      * inversion H.
      * destruct (Qle_bool m n) eqn: H2.
        { destruct (Qeq_bool n m) eqn: H'.
          { apply Qeq_bool_iff in H'. 
            assert (H3: forall x y: Q, x == y -> x <= y).
            { intros. apply Qle_lteq. auto. }
            apply H3 in H'. apply Qle_bool_iff in H'. rewrite H' in H1.
            inversion H1. }
          { simpl in H0. inversion H0. } }
        { apply Qle_bool_not_iff in H2. apply Qle_bool_not_iff in H1.
          apply Qnot_le_lt in H2. apply Qlt_le_weak in H2.
          unfold not in H1. apply H1 in H2. inversion H2. }
Qed.

Lemma LessEqTransivity: forall (n m p: Q),
  Qlt_bool n m = true /\ Qle_bool m p = true -> Qlt_bool n p = true.
Proof.
  intros. inversion H as [H1 H2]. apply Qlt_bool_iff in H1. apply Qle_bool_iff in H2.
  apply Qlt_bool_iff. generalize (Qlt_le_trans n m p); intro HQLT. auto.
Qed.

Lemma AlwaysPos: forall (l: list nat) (N: Neuron),
  beq_nat (length (Weights N)) 1%nat = true /\
  Qle_bool 0 (hd 0 (Weights N)) = true
  -> Qle_bool 0 (Current (AfterNsteps (ResetNeuron N) l)) = true.
Proof.
  induction l as [|h t].
  - intros. simpl. reflexivity.
  - intros. inversion H as [H1 H2]. 
    apply ListForm in H1. destruct H1 as [hq H1].
    rewrite H1 in H2. simpl in H2. simpl. 
    remember (AfterNsteps (ResetNeuron N) t) as T.
    generalize (ResetUnchanged N); intro HRU.
    inversion HRU as [HRU1 [HRU2 HRU3]].
    generalize (Unchanged (ResetNeuron N) t); intro HU.
    inversion HU as [HU1 [HU2 HU3]]. rewrite <- HeqT in HU3.
    rewrite HU3 in HRU3. rewrite HRU3 in H1.
    unfold NextPotential. 
    destruct (Qle_bool (Tau T) (Current T)) eqn: H'.
    + rewrite H1. unfold potential. 
      destruct (beq_nat h 0%nat) eqn: HBN.
      * reflexivity.
      * rewrite Qplus_0_l. apply H2.
    + rewrite H1. unfold potential.
      destruct (beq_nat h 0%nat) eqn: HBN.
      * rewrite Qplus_0_l. generalize (IHt N); intro IH.
        apply IH in H. rewrite <- HeqT in H.
        generalize (LeakRange T); intro HLR.
        inversion HLR as [HLR1 HLR2].
        apply Qle_bool_iff in H. apply Qle_bool_iff in HLR1.
        generalize (Qmult_le_0_compat (Leak_Factor T) (Current T)); intro HQ.
        apply Qle_bool_iff. apply HQ in HLR1. auto. auto.
      * rewrite Qplus_0_l. generalize (IHt N); intro IH.
        apply IH in H. rewrite <- HeqT in H.
        generalize (LeakRange T); intro HLR.
        inversion HLR as [HLR1 HLR2].
        apply Qle_bool_iff in H. apply Qle_bool_iff in HLR1.
        generalize (Qmult_le_0_compat (Leak_Factor T) (Current T)); intro HQ.
        apply Qle_bool_iff in H2.
        generalize (Qplus_le_compat 0 hq 0 (Leak_Factor T * Current T)); intro HC.
        apply HC in H2. rewrite Qplus_0_l in H2. apply Qle_bool_iff. auto.
        apply HQ in HLR1. auto. auto.
Qed.
               
Lemma LessThanEq: forall (x y: Q),
  Qlt_bool x y = true -> Qle_bool x y = true.
Proof.
  intros. unfold Qlt_bool in H. unfold andb in H.
  destruct (Qeq_bool x y) eqn: H1.
  - destruct (Qle_bool x y).
    + reflexivity.
    + inversion H.
  - destruct (Qle_bool x y).
    + reflexivity.
    + inversion H.
Qed.

Lemma BinOutputGeneral: forall (l: list nat),
  (Bin_List l) <-> (forall (ind: nat), nth l ind = Some 0%nat \/ nth l ind = Some 1%nat \/ nth l ind = None).
Proof.
split.
  - induction l as [ | h t IH].
    + destruct ind as [ | n]; simpl; right; right; reflexivity.
    + destruct ind as [ | n]. 
      * simpl in H. inversion H as [H1 H2]. simpl. apply orb_prop in H1. inversion H1 as [H3 | H4].
        { apply beq_nat_true in H3. left. simpl. rewrite H3. reflexivity. }
        { apply beq_nat_true in H4. right. left. simpl. rewrite H4. reflexivity. }
      * simpl in H. inversion H as [H1 H2]. simpl. (*rewrite Nat.sub_0_r.*) 
        generalize (IH H2 n); intro HK. auto.
  - induction l as [ | h t IH]. 
    + intros. simpl. auto.
    + intros. simpl. split.
      * generalize (H 0%nat); intro H1. simpl in H1. inversion H1 as [H2 | [H3 | H4]].
        { inversion H2. auto. }
        { inversion H3. auto. }
        { inversion H4. }
      * assert (Ht: forall ind : nat,
              nth t ind = Some 0%nat \/ nth t ind = Some 1%nat \/ nth t ind = None).
        { intros. generalize (H (S ind)); intro HA. simpl in HA. (*rewrite Nat.sub_0_r in HA.*) auto. }
        apply IH in Ht. auto.
Qed.

Lemma IsBinList: forall (l: list nat),
    (forall (ind: nat), nth l ind = Some 0%nat \/ nth l ind = Some 1%nat \/ nth l ind = None) -> Bin_List l.
Proof.
  induction l as [ | h t IH]. 
  - intros. simpl. auto.
  - intros. simpl. split.
    + generalize (H 0%nat); intro H1. simpl in H1. inversion H1 as [H2 | [H3 | H4]].
      * inversion H2. auto.
      * inversion H3. auto.
      * inversion H4.
    + assert (Ht: forall ind : nat,
              nth t ind = Some 0%nat \/ nth t ind = Some 1%nat \/ nth t ind = None).
      { intros. generalize (H (S ind)); intro HA. simpl in HA. (*rewrite Nat.sub_0_r in HA.*) auto. }
      apply IH in Ht. auto.
Qed.

Lemma OutofRange:
  forall {T: Type} (l: list T) (ind: nat),
  (length l) <=? ind = true <-> nth l ind = None.
Proof.
  induction l as[ | h t IH].
  - split; intros; destruct ind as [ | n]; simpl; reflexivity.
  - intros. destruct ind as [ | n]. 
    + split.
      * intros. inversion H.
      * intros. simpl in H. inversion H. 
    + split. 
      * intros. simpl. (*rewrite Nat.sub_0_r.*) generalize (IH n); intro NIH. 
        apply NIH in H. auto. 
      * intros. simpl in H. (*rewrite Nat.sub_0_r in H.*) simpl. 
        generalize (IH n); intro NIH. apply NIH in H. auto. 
Qed.
   
Lemma LengthCover: forall {T: Type} (l: list T) (ind: nat),
  (exists k: T, (nth l ind) = Some k) <-> (lt ind (length l)).
Proof.
  induction l as [ | h t IH].
  - split.
    + intros. destruct H as [k H1]. destruct ind as [ | n]; simpl in H1; inversion H1.
    + intros. inversion H. 
  - split.
    + intros. simpl. destruct ind as [ | n].
      * apply Nat.lt_0_succ.
      * destruct H as [k H1]. simpl in H1. (*rewrite Nat.sub_0_r in H1.*)
        apply lt_n_S. generalize (IH n); intro HK. inversion HK as [H2 H3].
        assert (H: exists k : T, nth t n = Some k).
        { exists k. auto. } apply H2 in H. auto.
   + intros. destruct ind as [ | n].
     * simpl. exists h. reflexivity.
     * simpl in H. apply lt_S_n in H. generalize (IH n); intro HK.
       apply HK in H. simpl. (*rewrite Nat.sub_0_r.*) auto.
Qed.

Lemma BinOutput: forall (l: list nat) (ind: nat),
  (Bin_List l) -> (lt ind (length l)) -> (nth l ind = Some 0%nat) \/ (nth l ind = Some 1%nat).
Proof.
  intros l ind H1 H2.
  generalize (BinOutputGeneral l); intro HBOG. inversion HBOG as [HA HB].
  generalize (HA H1 ind); intro HK. inversion HK as [H3 | [H4 | H5]].
  - left. auto.
  - right. auto.
  - generalize (OutofRange l ind); intro HOR. apply HOR in H5.
    apply lt_not_le in H2. apply Nat.leb_nle in H2. rewrite H2 in H5. 
    inversion H5.
Qed.

Lemma ZeroEqual: forall (z: positive),
  0 == 0 # z.
Proof.
  intros. unfold Qeq. simpl. reflexivity.
Qed.

Lemma FirstElement: forall (l: list Q),
  (1%nat <=? (length l)) = true -> (nth l 0) = Some (hd 0 l).
Proof.
  intros. destruct l as [| h t].
  - simpl in H. inversion H. 
  - simpl. reflexivity.
Qed.

Lemma SecondElement: forall (l: list Q),
  (2%nat <=? (length l)) = true -> (nth l 1) = Some (hd 0 (tl l)).
Proof.
  intros. destruct l as [|h t].
  - simpl in H. inversion H.
  - destruct t as [|h' t'].
    + simpl in H. inversion H.
    + simpl. reflexivity.
Qed.

Lemma PlusSides: forall (a b c d: Q),
  a == b -> c == d -> a + c == b + d.
Proof.
  intros. rewrite H. rewrite H0. reflexivity.
Qed.

Lemma AppendZero: forall (n: nat),
  (NZeros n) ++ [0%nat] = 0%nat::(NZeros n).
Proof.
  intros. induction n as [| n'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Lemma AppendBins: forall (l1 l2: list nat),
  Bin_List l1 -> Bin_List l2 -> Bin_List (l1 ++ l2).
Proof.
  intros l1 l2 H1 H2.
  induction l1 as [| h1 t1].
  - simpl. apply H2.
  - simpl. simpl in H1. inversion H1 as [H3 H4]. split. 
    + auto. 
    + apply IHt1 in H4.  auto.
Qed.

Lemma StillBin: forall (blist: list nat) (num: nat),
  Bin_List blist -> Bin_List (blist ++ (NZeros num)).
Proof.
 intros.
 induction num as [| num'].
 - simpl. rewrite app_nil_r. auto. 
 - simpl. rewrite <- AppendZero. rewrite app_assoc.
   assert (Htemp: Bin_List [0%nat]).
   { simpl. split; auto. }
   apply AppendBins; auto.
Qed.

Lemma Delayer_Property: forall (Inputs: list nat) (N M: Neuron),
  beq_nat (length (Weights N)) 1%nat = true /\
  Eq_Neuron2 M (AfterNsteps (ResetNeuron N) Inputs) /\
  Bin_List Inputs /\ 
  Qle_bool (Tau N) (hd 0 (Weights N)) = true -> (Delayer_Effect Inputs (Output M)).
Proof.
  induction Inputs as [|h1 l1].
  - intros N M [H1 [H2 [H3 H4]]]. simpl in H2. unfold Eq_Neuron2 in H2. simpl in H2. inversion H2 as [ H1' [H2' [H3' [H4' H5']]]].
    rewrite H1'. simpl. auto.
  - intros N M [H1 [H2 [H3 H4]]]. 
      destruct (Output M) as [|h2 l2] eqn: H0.
    + unfold Eq_Neuron2 in H2. inversion H2 as [ H1' [H2' [H3' [H4' H5']]]].
      rewrite -> H0 in H1'. symmetry in H1'. apply Not_nil_Output in H1'. inversion H1'.
    + simpl in H2. unfold NextNeuron in H2. unfold Eq_Neuron2 in H2. simpl in H2.
      inversion H2 as [ H1' [H2' [H3' [H4' H5']]]].
      remember (AfterNsteps (ResetNeuron N) l1) as T.
      assert (H': (beq_nat (length (Weights N)) 1%nat) = true /\ 
                  Eq_Neuron2 T (AfterNsteps (ResetNeuron N) l1) /\
                  Bin_List l1 /\ Qle_bool (Tau N) (hd 0 (Weights N)) = true).
      { split.
        { apply H1. }
        { split.
          { rewrite <- HeqT. unfold Eq_Neuron2. split; auto. split; auto. split; unfold Qeq; auto. }
          { split. 
            { simpl in H3. inversion H3 as [H6' H7']. apply H7'. } 
            { apply H4. } } } }
      apply IHl1 in H'. 
      generalize (ResetUnchanged N); intro HRU.
      generalize (Unchanged (ResetNeuron N) l1); intro HU.
      inversion HRU as [HRU3 [HRU2 HRU1]]. inversion HU as [HU3 [HU2 HU1]].
      clear HRU3. clear HU3. clear HRU. clear HU.
      rewrite <- HeqT in HU1. rewrite HU1 in HRU1.
      rewrite <- HeqT in HU2. rewrite HU2 in HRU2.
      rewrite H0 in H1'. unfold NextOutput in H1'.
      (assert (exists hq: Q, Weights T = hq::nil)).
      { rewrite HRU1 in H1. apply ListForm in H1. apply H1. }
      destruct H as [hw H]. rewrite HRU1 in H4. rewrite H in H4. simpl in H4. rewrite HRU2 in H4.
      simpl. split.
      { destruct (Qle_bool (Tau T) (Current T)) eqn: HTC.
            { destruct (beq_nat h1 0%nat) eqn: HBN.
              { unfold NextPotential in H1'. rewrite HTC in H1'.
                rewrite H in H1'. unfold potential in H1'. rewrite HBN in H1'. 
                generalize (PosTau T); intro HPT. apply Eq_reverse in HPT. rewrite HPT in H1'.
                inversion H1'. apply HBN. }
              { unfold NextPotential in H1'. rewrite HTC in H1'. rewrite H in H1'.
                unfold potential in H1'. rewrite HBN in H1'. rewrite Qplus_0_l in H1'.
                rewrite H4 in H1'. inversion H1'. simpl in H3.
                inversion H3 as [H8 H9]. unfold orb in H8. rewrite HBN in H8. apply H8. } }    
           { destruct (beq_nat h1 0%nat) eqn: HBN.
              { unfold NextPotential in H1'. rewrite HTC in H1'. rewrite H in H1'.
                unfold potential in H1'. rewrite HBN in H1'. rewrite Qplus_0_l in H1'.
                generalize (LeakRange T); intro HLR. apply Eq_reverse in HTC.
                generalize (PosTau T); intro HPT.
                assert (HRel: Qlt_bool 0 (Tau T) = true /\
                              Qlt_bool (Current T) (Tau T) = true /\ 
                              Qle_bool 0 (Leak_Factor T) = true /\ 
                              Qle_bool (Leak_Factor T) 1 = true). { split; auto. }
                apply LessThanOneFactor in HRel. apply Eq_reverse in HRel.
                rewrite HRel in H1'. inversion H1'. apply HBN. }
              { unfold NextPotential in H1'. rewrite HTC in H1'. rewrite H in H1'.
                unfold potential in H1'.  rewrite HBN in H1'. rewrite Qplus_0_l in H1'.
                generalize (PosTau T); intro HPT.
                assert (H7: Qlt_bool 0 (Tau T) = true /\ Qle_bool (Tau T) hw = true). { auto. }
                apply LessEqTransivity in H7. apply LessThanEq in H7.
                assert (H8: beq_nat (length (Weights N)) 1%nat = true /\ Qle_bool 0 (hd 0 (Weights N)) = true).
                {  split. { apply H1. } 
                          { rewrite HRU1. rewrite H. simpl. apply H7. }  } 
                generalize (AlwaysPos l1 N); intro HAT. apply HAT in H8. rewrite <- HeqT in H8.
                generalize (LeakRange T); intro HLR. inversion HLR as [HLR1 HLR2].
                assert (H9: Qle_bool 0 (Leak_Factor T) = true /\ Qle_bool 0 (Current T) = true). { auto. }
                apply PosMult in H9.
                assert (H10: Qle_bool (Tau T) hw = true /\ Qle_bool 0 (Leak_Factor T * Current T) = true). { auto. }
                apply AddPos in H10. rewrite H10 in H1'. inversion H1'. simpl in H3.
                inversion H3 as [H12 H13]. unfold orb in H12. rewrite HBN in H12. apply H12. } }  }
                { inversion H1'. apply H'. }
Qed.

Lemma Filter_Property: forall (Inputs: list nat) (N M: Neuron),
  (beq_nat (length (Weights N)) 1%nat) = true /\
  Eq_Neuron2 M (AfterNsteps (ResetNeuron N) Inputs) /\
  Bin_List Inputs /\ 
  Qle_bool (Tau N) (hd 0 (Weights N)) = false /\ 
  Inputs <> nil -> Filter_Effect (Output M).
Proof.
  induction Inputs as [|h1 l1].
  - intros N M [H1 [H2 [H3 [H4 H5]]]]. unfold not in H5. remember ([]) as Empty. assert (H6: Empty = Empty). { auto. }
    apply H5 in H6. inversion H6.
  - intros N M [H1 [H2 [H3 [H4 H5]]]]. 
    destruct (Output M) as [|h2 l2] eqn: H0.
    + unfold Eq_Neuron2 in H2. inversion H2 as [ H1' [H2' [H3' [H4' H5']]]].
      rewrite -> H0 in H1'. symmetry in H1'. apply Not_nil_Output in H1'. inversion H1'.
    + generalize (PosTau N); intro HPT. simpl in H2. unfold NextNeuron in H2. unfold Eq_Neuron2 in H2.
      simpl in H2. inversion H2 as [ H1' [H2' [H3' [H4' H5']]]].
      remember (AfterNsteps (ResetNeuron N) l1) as T.
      destruct l1 as [|hl1 ll1] eqn: Head.
      * simpl in HeqT. unfold ResetNeuron in HeqT. rewrite HeqT in H1'. simpl in H1'.
        rewrite H0 in H1'. inversion H1'.
        destruct (beq_nat h1 0 % nat) eqn: HBN.
        { unfold NextOutput. simpl. unfold NextPotential. simpl. 
          apply Eq_reverse in HPT. rewrite HPT. simpl.
          apply ListForm in H1. destruct H1 as [hn H1]. rewrite H1. unfold potential.
          rewrite HBN. simpl. rewrite Qplus_0_l. rewrite Qmult_0_r. rewrite HPT. simpl. auto. }
        { unfold NextOutput. simpl. unfold NextPotential. simpl.
          apply Eq_reverse in HPT. rewrite HPT.
          apply ListForm in H1. destruct H1 as [hn H1]. rewrite H1. unfold potential. 
          rewrite HBN. rewrite Qmult_0_r. rewrite Qplus_0_l. rewrite Qplus_comm. rewrite Qplus_0_l.
          assert (H8: (Weights T) = Weights N). { rewrite HeqT. simpl. reflexivity. }
          assert (H9: (Tau T) == (Tau N)). { rewrite HeqT. simpl. reflexivity. }
          rewrite <- H2' in H8. rewrite <- H4' in H9. (*rewrite H8 in H4. rewrite H9 in H4.*)
          rewrite H1 in H4. simpl in H4. rewrite H4. auto. }
      * generalize (ResetUnchanged N); intro HRU.
        generalize (Unchanged (ResetNeuron N) l1); intro HU.
        inversion HRU as [HRU3 [HRU1 HRU2]]. inversion HU as [HU3 [HU1 HU2]].
        clear HRU3. clear HU3. rewrite <- Head in HeqT.
        rewrite <- HeqT in HU1. rewrite <- HeqT in HU2. rewrite HU1 in HRU1. rewrite HU2 in HRU2.
        assert (H': (beq_nat (length (Weights N)) 1%nat) = true /\ 
                  Eq_Neuron2 T (AfterNsteps (ResetNeuron N) l1) /\
                  Bin_List l1 /\ Qle_bool (Tau T) (hd 0 (Weights T)) = false /\
                  l1 <> nil).
        { split.
          { apply H1. }
          { split.
            { rewrite <- HeqT. unfold Eq_Neuron2.
              split; auto. split; auto. split; auto. split; auto. split; auto. split; auto. split; auto. }
              split.
              { rewrite <- Head in H3. simpl in H3. inversion H3 as [H6 H7]. apply H7. }
                split.
                { rewrite <- H2'. rewrite <- H4'. rewrite <- HRU1 in H4'.
                  rewrite <- HRU2 in H2'. rewrite <- H2' in H4. rewrite <- H4' in H4. apply H4. }
                { unfold not. intro H6. rewrite Head in H6. inversion H6. } } }
        rewrite Head in H'. rewrite <- HRU1 in H'. rewrite <- HRU2 in H'. 
        apply IHl1 in H'. rewrite H0 in H1'.
        unfold NextOutput in H1'. unfold NextPotential in H1'.
        apply ListForm in H1. destruct H1 as [hn Hnew].
        rewrite Hnew in HRU2. apply Eq_reverse in HPT. rewrite HRU1 in HPT.
        destruct (Qle_bool (Tau T) (Current T)) eqn: HTC.
        { destruct (beq_nat h1 0%nat) eqn: HBN. 
          { rewrite <- HRU2 in H1'. unfold potential in H1'. rewrite HBN in H1'.
            rewrite HPT in H1'. inversion H1'.
            generalize (HeadZeroFilter (Output M)); intro HZF.
            assert (H7: beq_nat (hd 1%nat (Output M)) 0%nat = true /\ Filter_Effect (tl (Output M))).
            { split. 
              { rewrite H0. simpl. rewrite H1. simpl. reflexivity. }
              { rewrite H0. simpl. rewrite <- H6 in H'. apply H'. }  }
            apply HZF in H7. rewrite <- H1. rewrite <- H6. rewrite <- H0. apply H7.  }
          { rewrite <- HRU2 in H1'. unfold potential in H1'. rewrite HBN in H1'.
            rewrite Qplus_0_l in H1'. rewrite <- HRU2 in H2'. rewrite Hnew in H4.
            simpl in H4. rewrite HRU1 in H4. rewrite H4 in H1'. inversion H1'.
            generalize (HeadZeroFilter (Output M)); intro HZF.
            assert (H7: beq_nat (hd 1%nat (Output M)) 0%nat = true /\ Filter_Effect (tl (Output M))).
            { split. 
              { rewrite H0. simpl. rewrite H1. simpl. reflexivity. }
              { rewrite H0. simpl. rewrite <- H6 in H'. apply H'. }  }
            apply HZF in H7. rewrite <- H1. rewrite <- H6. rewrite <- H0. apply H7.  }  }
        { generalize (LastOutputZero l1 N T); intro HLO. generalize (TailStartZeroFilter (Output M)); intro HTZ.
          rewrite <- Eq_reverse in HTC. 
          assert (H6: Eq_Neuron2 T (AfterNsteps (ResetNeuron N) l1) /\
                      (length (Weights N) =? 1) = true /\
                       Qlt_bool (Current T) (Tau T) = true).
          { split. 
            { rewrite <- HeqT. unfold Eq_Neuron2. 
              split. reflexivity. split. reflexivity. split. reflexivity. split; reflexivity. }
            { split. rewrite Hnew. reflexivity. auto. } }
          apply HLO in H6.
          assert (H7: beq_nat (hd 1%nat (tl (Output M))) 0%nat = true /\ Filter_Effect (tl (Output M))).
          { split.
            { rewrite H0. simpl. inversion H1'. apply H6. }
            { rewrite H0. simpl. inversion H1'. apply H'. } }
          apply HTZ in H7. rewrite <- H0. apply H7. }
Qed.

Theorem DelayerOrFilterEffect: forall (Inputs: list nat) (N: Neuron) (M: Neuron),
  (beq_nat (length (Weights N)) 1%nat) = true /\
  Eq_Neuron2 M (AfterNsteps (ResetNeuron N) Inputs) /\
  Bin_List Inputs                        -> (Delayer_Effect Inputs (Output M)) \/ (Filter_Effect (Output M)).
Proof.
  intros. inversion H as [H1 [H2 H3]].
  destruct (Qle_bool (Tau N) (hd 0 (Weights N))) eqn: H'.
  - assert (H4: (beq_nat (length (Weights N)) 1%nat) = true /\
                Eq_Neuron2 M (AfterNsteps (ResetNeuron N) Inputs) /\
                Bin_List Inputs /\ 
                Qle_bool (Tau N) (hd 0 (Weights N)) = true). { split; auto. }
    apply Delayer_Property in H4. left. apply H4.
  - destruct Inputs as [|h1 l1] eqn: HI.
    + left. simpl in H2. unfold Eq_Neuron2 in H2. inversion H2 as [H1' [H2' [H3' [H4' H5']]]].
      unfold ResetNeuron in H1'. simpl in H1'. rewrite H1'. simpl. auto.
    + assert (H4: (beq_nat (length (Weights N)) 1%nat) = true /\
                  Eq_Neuron2 M (AfterNsteps (ResetNeuron N) Inputs) /\
                  Bin_List Inputs /\ 
                  Qle_bool (Tau N) (hd 0 (Weights N)) = false /\ 
                  Inputs <> nil).
      { split. (*repeat split; auto.*)
        { apply H1. }
        { split.
          { rewrite HI. apply H2. }
          { split.
            { rewrite HI. apply H3. }
            { split.
              { apply H'. }
              { unfold not. intro Hcon. rewrite HI in Hcon. inversion Hcon. } } } } }
     apply Filter_Property in H4. right. apply H4.
Qed.

Theorem Series2: forall (Inputs: list nat) (N1 N2 N3 N4: Neuron),
  (beq_nat (length (Weights N1)) 1%nat) = true /\
  Eq_Neuron2 N2 (AfterNsteps (ResetNeuron N1) Inputs) /\
  (beq_nat (length (Weights N3)) 1%nat) = true /\
  Eq_Neuron2 N4 (AfterNsteps (ResetNeuron N3) (Output N2)) /\
  Bin_List Inputs /\ 
  Qle_bool (Tau N1) (hd 0 (Weights N1)) = true /\
  Qle_bool (Tau N3) (hd 0 (Weights N3)) = true
    -> Output N4 = Inputs ++ [0%nat; 0%nat].
Proof.
  intros. inversion H as [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]].
  generalize (Delayer_Property Inputs N1 N2); intro HDI.
  assert (H1': (length (Weights N1) =? 1) = true /\
              Eq_Neuron2 N2 (AfterNsteps (ResetNeuron N1) Inputs) /\
              Bin_List Inputs /\ 
              Qle_bool (Tau N1) (hd 0 (Weights N1)) = true).
  { split; auto. } apply HDI in H1'.
  generalize (Output_Bin N2); intro HB.
  generalize (Delayer_Property (Output N2) N3 N4); intro HDO.
  assert (H2': (length (Weights N3) =? 1) = true /\
                Eq_Neuron2 N4 (AfterNsteps (ResetNeuron N3) (Output N2)) /\
                Bin_List (Output N2) /\ Qle_bool (Tau N3) (hd 0 (Weights N3)) = true).
  { split; auto. } apply HDO in H2'.
  apply Delayer_lists in H1'. apply Delayer_lists in H2'. rewrite H1' in H2'.
  generalize (app_assoc Inputs [0%nat] [0%nat]); intro HPA.
  rewrite <- HPA in H2'. simpl in H2'. apply H2'.
Qed.

(*Theorem NegativeWeight: forall (Inputs: list nat) (M N: Neuron),
  beq_nat (length (Weights N)) 1%nat = true /\
  Qlt_bool (hd 0 (Weights N)) 0  = true /\
  Eq_Neuron2 M (AfterNsteps (ResetNeuron N) Inputs) /\
  Bin_List Inputs -> ~(In 1%nat (Output M)).
Proof.
  induction Inputs as [|h t].
  (*Have variable M as the first variable and do intro M and induction on Output M*)
  - intros. intros H'. inversion H as [H1 [H2 [H3 H4]]].
    simpl in H3. unfold Eq_Neuron2 in H3. inversion H3 as [ H1' [H2' [H3' [H4' H5']]]].
    simpl in H1'. rewrite H1' in H'. unfold In in H'. inversion H' as [HX | HY]. inversion HX. auto.
  - intros M N H. unfold not. intros H'. inversion H as [H1 [H2 [H3 H4]]].
    simpl in H3. simpl in H4. inversion H4 as [H5 H6].
    apply ListForm in H1. destruct H1 as [hq HL].
    destruct (h =? 0) eqn: HEXT.
    + rewrite beq_nat_true_iff in HEXT. rewrite HEXT in H3. unfold Eq_Neuron2 in H3.
    inversion H3 as [ H1' [H2' [H3' [H4' H5']]]]. simpl in H2'.
    remember (AfterNsteps (ResetNeuron N) t) as P. simpl in H1'.    
    assert (HInd: (length (Weights N) =? 1) = true /\
                  Qlt_bool (hd 0 (Weights N)) 0 = true /\
                  Eq_Neuron2 P (AfterNsteps (ResetNeuron N) t) /\ Bin_List t). 
    { split. auto. split. auto. rewrite <- HeqP. unfold Eq_Neuron2. split. auto.
      split. auto. split. auto. split. auto. split. auto. split. reflexivity. reflexivity. auto. }
    generalize (IHt P N); intro IH. apply IH in HInd. unfold NextOutput in H1'.
    unfold NextPotential in H1'. apply ListForm in H1. destruct H1 as [hq HL].
    
    destruct Inputs as [|h' t'].
    + simpl in H1'. rewrite H1' in H'. simpl in H'. inversion H'. 
      * inversion H0. 
      * apply H0.
    + simpl in H1'. unfold NextOutput in H1'. unfold NextPotential in H1'.
      remember (AfterNsteps (ResetNeuron N) t') as T.
      generalize (IHt t' T N); intro HT.
      assert (IH: (length (Weights N) =? 1) = true /\
              Qlt_bool (hd 0 (Weights N)) 0 = true /\
              Eq_Neuron2 T (AfterNsteps (ResetNeuron N) t') /\ t = Output T).
      { split. auto. split. auto. split. rewrite <- HeqT. simpl. unfold Eq_Neuron2.
        split. auto. split. auto. split. reflexivity. split; reflexivity.
        rewrite <- H4 in H1'. inversion H1'. reflexivity. }
      apply HT in IH. unfold not in IH.
      generalize (ResetUnchanged N); intro HRU. inversion HRU as [HRU1 [HRU2 HRU3]].
      generalize (Unchanged (ResetNeuron N) t'); intro HU. inversion HU as [HU1 [HU2 HU3]].
      rewrite <- HeqT in HU3. rewrite HU3 in HRU3. apply ListForm in H1.
      destruct H1 as [hq H1]. rewrite <- HRU3 in H1'. rewrite H1 in H1'.
      unfold potential in H1'. 
      destruct (Qle_bool (Tau T) (Current T)) eqn: HTC.
      * destruct (beq_nat h' 0%nat).
        { generalize (PosTau T); intro HPT. apply Qlt_bool_iff in HPT.
          apply Qlt_not_le in HPT. apply Qle_bool_not_iff in HPT.
          rewrite HPT in H1'. rewrite <- H4 in H1'. rewrite <- H4 in H'.
          simpl in H'. inversion H'.
          { inversion H1'. rewrite H6 in H0. inversion H0. }
          { inversion H1'. rewrite H7 in H0. apply IH in H0. apply H0. } }
        { rewrite Qplus_0_l in H1'. rewrite H1 in H2. simpl in H2.
          generalize (PosTau T); intro HPT. apply Qlt_bool_iff in HPT.
          apply Qlt_bool_iff in H2. generalize (Qlt_trans hq 0 (Tau T)); intro HQT.
          apply HQT in H2. apply Qlt_not_le in H2. apply Qle_bool_not_iff in H2.
          rewrite H2 in H1'. rewrite <- H4 in H1'. rewrite <- H4 in H'.
          simpl in H'. inversion H'.
          { inversion H1'. rewrite H6 in H0. inversion H0. }
          { inversion H1'. rewrite H7 in H0. apply IH in H0. apply H0. } auto. }
      * destruct (beq_nat h' 0%nat).
        { rewrite Qplus_0_l in H1'.
          generalize (LessThanOneFactor (Current T) (Leak_Factor T) (Tau T)); intro HLT.
          generalize (LeakRange T); intro HLR. generalize (PosTau T); intro HPT.
          assert (HL: Qlt_bool 0 (Tau T) = true /\
                      Qlt_bool (Current T) (Tau T) = true /\
                      Qle_bool 0 (Leak_Factor T) = true /\
                      Qle_bool (Leak_Factor T) 1 = true).
          { split. auto. split. apply Qle_bool_not_iff in HTC.
            apply Qnot_le_lt in HTC. apply Qlt_bool_iff in HTC. auto. auto. }
          apply HLT in HL. apply Qlt_bool_iff in HL. apply Qlt_not_le in HL.
          apply Qle_bool_not_iff in HL. rewrite HL in H1'. rewrite <- H4 in H1'.
          rewrite <- H4 in H'. simpl in H'. inversion H'.
          { inversion H1'. rewrite H6 in H0. inversion H0. }
          { inversion H1'. rewrite H7 in H0. apply IH in H0. apply H0. } }
        { rewrite Qplus_0_l in H1'.
          generalize (LessThanOneFactor (Current T) (Leak_Factor T) (Tau T)); intro HLT.
          generalize (LeakRange T); intro HLR. generalize (PosTau T); intro HPT.
          assert (HL: Qlt_bool 0 (Tau T) = true /\
                      Qlt_bool (Current T) (Tau T) = true /\
                      Qle_bool 0 (Leak_Factor T) = true /\
                      Qle_bool (Leak_Factor T) 1 = true).
          { split. auto. split. apply Qle_bool_not_iff in HTC.
            apply Qnot_le_lt in HTC. apply Qlt_bool_iff in HTC. auto. auto. }
            apply HLT in HL. apply Qlt_bool_iff in HL. apply Qlt_not_le in HL.
            apply Qle_bool_not_iff in HL. rewrite H1 in H2. simpl in H2.
            apply Qlt_bool_iff in H2. apply Qle_bool_not_iff in HL. apply Qnot_le_lt in HL.
            apply Qlt_le_weak in H2. 
            generalize (Qplus_lt_le_compat (Leak_Factor T * Current T) (Tau T) hq 0); intro HQL.
            apply HQL in HL. rewrite Qplus_0_r in HL. rewrite Qplus_comm in HL.
            apply Qlt_not_le in HL. apply Qle_bool_not_iff in HL.
            rewrite HL in H1'. rewrite <- H4 in H1'. rewrite <- H4 in H'. simpl in H'. inversion H'.
            { inversion H1'. rewrite H6 in H0. inversion H0. }
            { inversion H1'. rewrite H7 in H0. apply IH in H0. apply H0. } auto. }
Qed.*)

Theorem NegativeWeight: forall (Out Inputs: list nat) (M N: Neuron),
  beq_nat (length (Weights N)) 1%nat = true /\
  Qlt_bool (hd 0 (Weights N)) 0  = true /\
  Eq_Neuron2 M (AfterNsteps (ResetNeuron N) Inputs) /\ 
  Out = Output M -> ~(In 1%nat (Output M)).
Proof.
  induction Out as [| h t].
  (*Have variable M as the first variable and do intro M and induction on Output M*)
  - intros. intros H'. inversion H as [H1 [H2 [H3 H4]]].
    rewrite <- H4 in H'. unfold In in H'. apply H'.
  - intros Inputs M N H. unfold not. intros H'. inversion H as [H1 [H2 [H3 H4]]].
    unfold Eq_Neuron2 in H3.
    inversion H3 as [ H1' [H2' [H3' [H4' H5']]]].
    destruct Inputs as [|h' t'].
    + simpl in H1'. rewrite H1' in H'. simpl in H'. inversion H'. 
      * inversion H0. 
      * apply H0.
    + simpl in H1'. unfold NextOutput in H1'. unfold NextPotential in H1'.
      remember (AfterNsteps (ResetNeuron N) t') as T.
      generalize (IHt t' T N); intro HT.
      assert (IH: (length (Weights N) =? 1) = true /\
              Qlt_bool (hd 0 (Weights N)) 0 = true /\
              Eq_Neuron2 T (AfterNsteps (ResetNeuron N) t') /\ t = Output T).
      { split. auto. split. auto. split. rewrite <- HeqT. simpl. unfold Eq_Neuron2.
        split. auto. split. auto. split. reflexivity. split; reflexivity.
        rewrite <- H4 in H1'. inversion H1'. reflexivity. }
      apply HT in IH. unfold not in IH.
      generalize (ResetUnchanged N); intro HRU. inversion HRU as [HRU1 [HRU2 HRU3]].
      generalize (Unchanged (ResetNeuron N) t'); intro HU. inversion HU as [HU1 [HU2 HU3]].
      rewrite <- HeqT in HU3. rewrite HU3 in HRU3. apply ListForm in H1.
      destruct H1 as [hq H1]. rewrite <- HRU3 in H1'. rewrite H1 in H1'.
      unfold potential in H1'. 
      destruct (Qle_bool (Tau T) (Current T)) eqn: HTC.
      * destruct (beq_nat h' 0%nat).
        { generalize (PosTau T); intro HPT. apply Qlt_bool_iff in HPT.
          apply Qlt_not_le in HPT. apply Qle_bool_not_iff in HPT.
          rewrite HPT in H1'. rewrite <- H4 in H1'. rewrite <- H4 in H'.
          simpl in H'. inversion H'.
          { inversion H1'. rewrite H6 in H0. inversion H0. }
          { inversion H1'. rewrite H7 in H0. apply IH in H0. apply H0. } }
        { rewrite Qplus_0_l in H1'. rewrite H1 in H2. simpl in H2.
          generalize (PosTau T); intro HPT. apply Qlt_bool_iff in HPT.
          apply Qlt_bool_iff in H2. generalize (Qlt_trans hq 0 (Tau T)); intro HQT.
          apply HQT in H2. apply Qlt_not_le in H2. apply Qle_bool_not_iff in H2.
          rewrite H2 in H1'. rewrite <- H4 in H1'. rewrite <- H4 in H'.
          simpl in H'. inversion H'.
          { inversion H1'. rewrite H6 in H0. inversion H0. }
          { inversion H1'. rewrite H7 in H0. apply IH in H0. apply H0. } auto. }
      * destruct (beq_nat h' 0%nat).
        { rewrite Qplus_0_l in H1'.
          generalize (LessThanOneFactor (Current T) (Leak_Factor T) (Tau T)); intro HLT.
          generalize (LeakRange T); intro HLR. generalize (PosTau T); intro HPT.
          assert (HL: Qlt_bool 0 (Tau T) = true /\
                      Qlt_bool (Current T) (Tau T) = true /\
                      Qle_bool 0 (Leak_Factor T) = true /\
                      Qle_bool (Leak_Factor T) 1 = true).
          { split. auto. split. apply Qle_bool_not_iff in HTC.
            apply Qnot_le_lt in HTC. apply Qlt_bool_iff in HTC. auto. auto. }
          apply HLT in HL. apply Qlt_bool_iff in HL. apply Qlt_not_le in HL.
          apply Qle_bool_not_iff in HL. rewrite HL in H1'. rewrite <- H4 in H1'.
          rewrite <- H4 in H'. simpl in H'. inversion H'.
          { inversion H1'. rewrite H6 in H0. inversion H0. }
          { inversion H1'. rewrite H7 in H0. apply IH in H0. apply H0. } }
        { rewrite Qplus_0_l in H1'.
          generalize (LessThanOneFactor (Current T) (Leak_Factor T) (Tau T)); intro HLT.
          generalize (LeakRange T); intro HLR. generalize (PosTau T); intro HPT.
          assert (HL: Qlt_bool 0 (Tau T) = true /\
                      Qlt_bool (Current T) (Tau T) = true /\
                      Qle_bool 0 (Leak_Factor T) = true /\
                      Qle_bool (Leak_Factor T) 1 = true).
          { split. auto. split. apply Qle_bool_not_iff in HTC.
            apply Qnot_le_lt in HTC. apply Qlt_bool_iff in HTC. auto. auto. }
            apply HLT in HL. apply Qlt_bool_iff in HL. apply Qlt_not_le in HL.
            apply Qle_bool_not_iff in HL. rewrite H1 in H2. simpl in H2.
            apply Qlt_bool_iff in H2. apply Qle_bool_not_iff in HL. apply Qnot_le_lt in HL.
            apply Qlt_le_weak in H2. 
            generalize (Qplus_lt_le_compat (Leak_Factor T * Current T) (Tau T) hq 0); intro HQL.
            apply HQL in HL. rewrite Qplus_0_r in HL. rewrite Qplus_comm in HL.
            apply Qlt_not_le in HL. apply Qle_bool_not_iff in HL.
            rewrite HL in H1'. rewrite <- H4 in H1'. rewrite <- H4 in H'. simpl in H'. inversion H'.
            { inversion H1'. rewrite H6 in H0. inversion H0. }
            { inversion H1'. rewrite H7 in H0. apply IH in H0. apply H0. } auto. }
Qed.

(*Theorem MultipleNegativeWeight: forall (Inputs: list (list nat)) (n: nat) (M N: Neuron),
  (beq_nat (length (Weights N)) n) = true /\
  AllLengthN Inputs n /\
  AllBinary Inputs /\
  AllNegative (Weights N) /\
  Eq_Neuron2 M (AfterNstepsM (ResetNeuron N) Inputs) ->
  ~(In 1%nat (Output M)).
Proof.
  Admitted.*)
    
  
Record NeuronSeries {Input: list nat} := MakeNeuronSeries 
{
  NeuronList: list Neuron;
  NSOutput: list nat;
  AllSingle: forall (N:Neuron), In N NeuronList -> (beq_nat (length (Weights N)) 1%nat) = true;
  SeriesOutput: NSOutput = (SeriesNetworkOutput Input NeuronList);
}.

Compute (MakeNeuronSeries [1%nat;0%nat] ([]) ([1%nat;0%nat]) ). 

Lemma AllSingleInput: forall (NL: list Neuron),
  AllDelayers NL -> forall (N: Neuron), In N NL -> (beq_nat (length (Weights N)) 1%nat) = true /\ Qle_bool (Tau N) (hd 0 (Weights N)) = true.
Proof.
  intros.
  induction NL as [| h t].
  - simpl in H0. inversion H0.
  - simpl in H. inversion H as [H1 [H2 H3]]. simpl in H0.
    destruct H0 as [H4 | H5].
    + rewrite H4 in H1. rewrite H4 in H2. split; auto.
    + apply IHt in H3. auto. auto.
Qed.

Theorem SeriesN: forall (*(SeriesList: list Neuron)*) (Input: list nat) (NSeries: @NeuronSeries Input),
    (*SeriesList = (NeuronList NSeries) ->*) 
    AllDelayers (NeuronList NSeries) ->
    Bin_List Input ->
    (NSOutput NSeries) = Input ++ (NZeros (length (NeuronList NSeries))).
Proof.
  intros Input NSeries.
  destruct NSeries.
  simpl. generalize dependent NSOutput0.
  induction NeuronList0 as [| h t].
  - simpl. rewrite app_nil_r. auto.
  - simpl; intros. inversion H as [H1 [H2 H3]]. clear H.
    assert (H: SeriesNetworkOutput Input t = SeriesNetworkOutput Input t).
    { auto. } 
    assert (HAS: forall N: Neuron, In N t -> (beq_nat (length (Weights N)) 1%nat) = true).
    { generalize (AllSingleInput t H3); intro HAN. apply HAN. }
    generalize (IHt HAS (SeriesNetworkOutput Input t) H H3 H0).
    (*generalize (IHt (SeriesNetworkOutput Input t) H H3 H0).*)
    intro H4. clear H.
    rewrite SeriesOutput0. clear SeriesOutput0 NSOutput0.
    rewrite -> H4. clear H4.
    generalize (StillBin Input (length t)); intro HSB.
    apply HSB in H0.
    remember (AfterNsteps (ResetNeuron h) (Input ++ NZeros (length t))) as M.
    generalize (Delayer_Property (Input ++ NZeros (length t)) h M); intro HDP.
    assert (Htemp: (length (Weights h) =? 1) = true /\
                   Eq_Neuron2 M (AfterNsteps (ResetNeuron h) (Input ++ NZeros (length t))) /\
                   Bin_List (Input ++ NZeros (length t)) /\
                   Qle_bool (Tau h) (hd 0 (Weights h)) = true).
    { split; auto. split; auto. rewrite HeqM. unfold Eq_Neuron2.
      split; auto. split; auto. split; auto. reflexivity.
      split; auto. reflexivity. split; auto. }
    apply HDP in Htemp. apply Delayer_lists in Htemp. rewrite Htemp.
    rewrite <- app_assoc. rewrite AppendZero. reflexivity.
Qed.
  
Theorem SeriesN': forall (NList: list Neuron) (Input: list nat),
  AllDelayers NList -> Bin_List Input ->
   (SeriesNetworkOutput Input NList) = Input ++ (NZeros (length NList)).
Proof.
  intros.
  induction NList as [| h t].
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl in H. inversion H as [H1 [H2 H3]]. apply IHt in H3.
    simpl. rewrite H3. generalize (StillBin Input (length t)); intro HSB.
    apply HSB in H0.
    remember (AfterNsteps (ResetNeuron h) (Input ++ NZeros (length t))) as M.
    generalize (Delayer_Property (Input ++ NZeros (length t)) h M); intro HDP.
    assert (Htemp: (length (Weights h) =? 1) = true /\
                   Eq_Neuron2 M (AfterNsteps (ResetNeuron h) (Input ++ NZeros (length t))) /\
                   Bin_List (Input ++ NZeros (length t)) /\
                   Qle_bool (Tau h) (hd 0 (Weights h)) = true).
   { split; auto. split; auto. rewrite HeqM. unfold Eq_Neuron2.
     split; auto. split; auto. split; auto. reflexivity.
     split; auto. reflexivity. split; auto. }
    apply HDP in Htemp. apply Delayer_lists in Htemp. rewrite Htemp.
    rewrite <- app_assoc. rewrite AppendZero. reflexivity.
Qed.

Check count_occ.

Fixpoint count (l : list nat) (x : nat) : nat :=
match l with
  | [] => 0
  | h :: t => if beq_nat h x then
                 1 + count t x
              else count t x 
end.

Theorem NextOutput01: forall (N: Neuron) (Inputs: list nat),
    (beq_nat (NextOutput N Inputs) 0%nat) = true \/ (beq_nat (NextOutput N Inputs) 1%nat) = true.
Proof.
  intros. unfold NextOutput.
  destruct (Qle_bool (Tau N) (NextPotential N Inputs)).
  - right. simpl. reflexivity.
  - left. simpl. reflexivity.
Qed.

Lemma LessThanSucc: forall (n: nat),
  n <? (S n) = true.
Proof.
  intros. induction n as [ | n'].
  - simpl. reflexivity.
  - simpl. auto.
Qed.


Lemma LeqSucc: forall (n: nat),
  n <=? (S n) = true.
Proof.
  intros. induction n as [ | n'].
  - simpl. reflexivity.
  - simpl. auto.
Qed.

Lemma LeqAssociativity: forall (a b c: nat),
  a <=? b = true -> b <=? c = true -> a <=? c = true.
Proof.
  induction a as [ | a'].  
  - intros. simpl. reflexivity.
  - intros. destruct b as [ | b'].
    + simpl in H. inversion H.
    + destruct c as [ | c'].
      * simpl in H0. inversion H0.
      * generalize (IHa' b' c'); intro HISS. simpl in H. simpl in H0. 
        apply HISS in H. simpl. auto. auto.
Qed.

Lemma ZeroInputZeroOutput: forall (N: Neuron) (Inputs: list nat),
  beq_nat (length (Weights N)) 1%nat = true -> 
  beq_nat (length Inputs) 1%nat = true -> 
  beq_nat (hd 0%nat Inputs) 0%nat = true ->        beq_nat (NextOutput N Inputs) 0%nat = true.
Proof.
  intros. apply ListForm in H0. destruct H0. destruct Inputs as [ | h t] eqn: HIN. 
  - simpl. inversion H0.
  - inversion H0. simpl in H1. rewrite beq_nat_true_iff in H1. rewrite H1 in H3.
    rewrite <- H3. apply ListForm in H. destruct H. unfold NextOutput.
    unfold NextPotential. rewrite H. simpl.
    destruct (Qle_bool (Tau N) (Current N)) eqn: HQTC.
    + generalize (PosTau N); intro HPN. apply Qlt_bool_iff in HPN.
      apply Qlt_not_le in HPN. apply Qle_bool_not_iff in HPN. rewrite HPN.
      simpl. reflexivity.
    + rewrite Qplus_0_l. apply Eq_reverse in HQTC. generalize (PosTau N); intro HPN.
      generalize (LeakRange N); intro HLN. 
      generalize (LessThanOneFactor (Current N) (Leak_Factor N) (Tau N)); intro HLCLT.
      assert (Htemp: 
        Qlt_bool 0 (Tau N) = true /\
        Qlt_bool (Current N) (Tau N) = true /\
        Qle_bool 0 (Leak_Factor N) = true /\ Qle_bool (Leak_Factor N) 1 = true).
        { split. apply HPN. split. apply HQTC. apply HLN. }
     apply HLCLT in Htemp. apply Qlt_bool_iff in Htemp. apply Qlt_not_le in Htemp.
     apply Qle_bool_not_iff in Htemp. rewrite Htemp. simpl. reflexivity.
Qed.

Theorem SpikeDecreasing: forall (Inputs: list nat) (N: Neuron) (M: Neuron),
  beq_nat (length (Weights N)) 1%nat = true /\
  Eq_Neuron2 M (AfterNsteps (ResetNeuron N) Inputs) /\
  Bin_List Inputs                        -> (count (Output M) 1%nat) <=? (count Inputs 1%nat) = true.
Proof.
  induction Inputs as [| h l].
  - intros. inversion H as [H1 [H2 H3]]. simpl in H2. unfold Eq_Neuron2 in H2. 
    inversion H2 as [H4 [H5 [H6 [H7 H8]]]]. simpl in H4. rewrite H4. simpl. reflexivity.
  - intros. inversion H as [H1 [H2 H3]]. simpl in H3.
    inversion H3 as [H4 H5]. unfold Eq_Neuron2 in H2. inversion H2 as [H6 [H7 [H8 [H9 H10]]]].
      simpl in H7. simpl in H8. simpl in H9. simpl in H10.
      simpl in H6. remember (AfterNsteps (ResetNeuron N) l) as M2.
      assert (Htemp: (length (Weights N) =? 1) = true /\
                        Eq_Neuron2 M2 (AfterNsteps (ResetNeuron N) l) /\ Bin_List l).
        { split. apply H. split. rewrite <- HeqM2. unfold Eq_Neuron2. simpl.
          split. reflexivity. split. reflexivity. split. reflexivity.
          split; reflexivity. apply H5. }
      generalize (IHl N M2); intro Hl. apply Hl in Htemp.
      destruct (h =? 0) eqn: HBN.
    + rewrite beq_nat_true_iff in HBN. rewrite HBN. simpl.
      assert (HLen: (length (Weights M2) =? 1) = true).
      { generalize (Unchanged (ResetNeuron N) l); intro HRM.
        inversion HRM as [HRM1 [HRM2 HRM3]]. generalize (ResetUnchanged N); intro HR.
        inversion HR as [HR1 [HR2 HR3]]. rewrite <- HR3 in HRM3. rewrite <- HeqM2 in HRM3.
        rewrite HRM3 in H1. auto. }
        generalize (ZeroInputZeroOutput M2 [0%nat]); intro HZM.
        apply HZM in HLen. rewrite HBN in H6. rewrite beq_nat_true_iff in HLen.
        rewrite HLen in H6. rewrite H6. simpl. auto. auto. auto.
    + simpl in H4. rewrite beq_nat_true_iff in H4. rewrite H4.
      generalize (NextOutput01 M2 [h]); intro HNAR. inversion HNAR as [HN1 | HN2].
      * rewrite beq_nat_true_iff in HN1. rewrite HN1 in H6. rewrite H6. simpl. 
        rewrite <- HN1 in H6. generalize (LeqSucc (count l 1)); intro HLC.
        generalize (LeqAssociativity (count (Output M2) 1) (count l 1) (S (count l 1))); intro HLA.
        apply HLA in Htemp. auto. auto.
      * rewrite beq_nat_true_iff in HN2. rewrite HN2 in H6. rewrite H6. simpl. auto.
Qed.
   
Record PositiveLoop {Inputs: list nat} := MakePositiveLoop {
  PL_N1: Neuron;
  PL_N2: Neuron;
  PL_NinputN1: (beq_nat (length (Weights PL_N1)) 2%nat) = true;
  PL_NinputN2: (beq_nat (length (Weights PL_N2)) 1%nat) = true;
  PL_PW1: 0 < (hd 0 (Weights PL_N1));
  PL_PW2: 0 < (hd 0 (tl (Weights PL_N1)));
  PL_PW3: 0 < (hd 0 (Weights PL_N2));
  PL_Connection1: Eq_Neuron2 PL_N1 (AfterNTwoLoopN1 (ResetNeuron PL_N1) (ResetNeuron PL_N2) Inputs);
  PL_Connection2: Eq_Neuron2 PL_N2 (AfterNTwoLoopN2 (ResetNeuron PL_N1) (ResetNeuron PL_N2) Inputs)
}.

Compute 6 mod 4.
Search le true.
Search rev_ind.
Search rev app.

Lemma InOutLengthHelper:
  forall (Inputs: list nat) (N M P Q: Neuron),
  Eq_Neuron2 N (AfterNTwoLoopN1 (ResetNeuron P) (ResetNeuron Q) Inputs) ->
  Eq_Neuron2 M (AfterNTwoLoopN2 (ResetNeuron P) (ResetNeuron Q) Inputs) ->
  beq_nat (length Inputs + 1%nat) (length (Output N)) = true /\ 
  beq_nat (length Inputs + 1%nat) (length (Output M)) = true.
Proof.
  induction Inputs as [ | h t IH].
  - intros N M P Q H1 H2. simpl in H1. simpl in H2. inversion H1 as [H3 H4].
    inversion H2 as [H5 H6]. simpl in H5. simpl in H3. rewrite H3. rewrite H5.
    simpl. auto.
  - intros N M P Q H1 H2. simpl in H1. simpl in H2.
    remember (AfterNTwoLoopN1 (ResetNeuron P) (ResetNeuron Q) t) as X.
    remember (AfterNTwoLoopN2 (ResetNeuron P) (ResetNeuron Q) t) as Y.
    generalize (IH X Y P Q); intro IHnew. rewrite <- HeqX in IHnew.
    rewrite <- HeqY in IHnew. generalize (ReflexivityNeuron X); intro HRNX.
    apply IHnew in HRNX. unfold Eq_Neuron2 in H1. inversion H1 as [H3 H4].
    unfold Eq_Neuron2 in H2. inversion H2 as [H5 H6]. simpl in H3. simpl in H5.
    rewrite H3. rewrite H5. simpl. auto.
    generalize (ReflexivityNeuron Y); intro HRNY. auto.
Qed. 

Lemma InOutLength:
  forall (Inputs: list nat) (PLP: @PositiveLoop Inputs),
  beq_nat (length Inputs + 1%nat) (length (Output (PL_N1 PLP))) = true /\ 
  beq_nat (length Inputs + 1%nat) (length (Output (PL_N2 PLP))) = true.
Proof.
  destruct PLP. simpl.
  generalize (InOutLengthHelper Inputs PL_N3 PL_N4 (ResetNeuron PL_N3) (ResetNeuron PL_N4)); intro HIOL.
  apply HIOL in PL_Connection3. auto. auto.
Qed.

Lemma PositivePotential:
  forall (l: list nat) (w: list Q),
  AllPositive w -> 0 <= potential w l.
Proof.
  induction l as [ | h t IH]. 
  - intros. destruct w as [ | hw ht].
    + simpl. apply Qle_lteq. right. reflexivity.
    + simpl. apply Qle_lteq. right. reflexivity.
  - destruct w as [ | hw ht].
    + intros. simpl. apply Qle_lteq. right. reflexivity.
    + intros. generalize (IH ht); intro IHC. simpl.
      simpl in H. inversion H as [H1 H2]. apply IHC in H2.
      destruct (beq_nat h 0%nat). 
      * auto.
      * apply Qlt_le_weak in H1.
        generalize (Qplus_le_compat 0 (potential ht t) 0 hw); intro HQLC. 
        apply HQLC in H1. auto. auto.
Qed.

Lemma NegativePotential:
  forall (l: list nat) (w: list Q),
  AllNegative w -> potential w l <= 0.
Proof.
  induction l as [ | h t IH]. 
  - intros. destruct w as [ | hw ht].
    + simpl. apply Qle_lteq. right. reflexivity.
    + simpl. apply Qle_lteq. right. reflexivity.
  - destruct w as [ | hw ht].
    + intros. simpl. apply Qle_lteq. right. reflexivity.
    + intros. generalize (IH ht); intro IHC. simpl.
      simpl in H. inversion H as [H1 H2]. apply IHC in H2.
      destruct (beq_nat h 0%nat). 
      * auto.
      * (*apply Qlt_le_weak in H1.*)
        generalize (Qplus_le_compat (potential ht t) 0 hw 0); intro HQLC. 
        generalize (HQLC H2 H1); intro HF. auto.
Qed.


Lemma PositiveCurrent1:
  forall (Inputs: list nat) (N M P: Neuron),
  AllPositive (Weights N) ->
  N = AfterNTwoLoopN1 (ResetNeuron M) (ResetNeuron P) Inputs -> 0 <= (Current N).
Proof.
  induction Inputs as [ | h t IH].
  - intros N M P H1 H2. simpl in H2. unfold ResetNeuron in H2. rewrite H2. simpl.
    apply Qle_lteq. right. reflexivity.
  - intros N M P H1 H2. simpl in H2.
    remember (AfterNTwoLoopN1 (ResetNeuron M) (ResetNeuron P) t) as X.
    remember (AfterNTwoLoopN2 (ResetNeuron M) (ResetNeuron P) t) as Y.
    generalize (NextNeuronUnchanged X [h; hd 0%nat (Output Y)]); intro HNNX.
    inversion HNNX as [H3 [H4 H5]]. generalize (IH X M P); intro HIH.
    unfold NextNeuron in H2. rewrite H2 in H1. simpl in H1.  
    assert (H1Copy: AllPositive (Weights X)). { auto. } apply HIH in H1.
    + rewrite H2. simpl. unfold NextPotential.
      generalize (PositivePotential [h; hd 0%nat (Output Y)] (Weights X)); intro HPP.
      destruct (Qle_bool (Tau X) (Current X)) eqn: HQTC.
      * auto.
      * apply HPP in H1Copy. (generalize (LeakRange X)); intro HLRX.
        inversion HLRX as [H6 H7]. apply Qle_bool_iff in H6.
        generalize (Qmult_le_0_compat (Leak_Factor X) (Current X)); intro HQM.
        apply HQM in H6.
        generalize (Qplus_le_compat 0 (potential (Weights X) [h; hd 0%nat (Output Y)]) 0 (Leak_Factor X * Current X)); intro HQP.
        apply HQP in H1Copy. auto. auto. auto.
   + auto.
Qed.

Lemma PositiveCurrent2:
  forall (Inputs: list nat) (N M P: Neuron),
  AllPositive (Weights N) ->
  N = AfterNTwoLoopN2 (ResetNeuron M) (ResetNeuron P) Inputs -> 0 <= (Current N).
Proof.
  induction Inputs as [ | h t IH].
  - intros N M P H1 H2. simpl in H2. unfold ResetNeuron in H2. rewrite H2. simpl.
    apply Qle_lteq. right. reflexivity.
  - intros N M P H1 H2. simpl in H2.
    remember (AfterNTwoLoopN1 (ResetNeuron M) (ResetNeuron P) t) as X.
    remember (AfterNTwoLoopN2 (ResetNeuron M) (ResetNeuron P) t) as Y.
    generalize (NextNeuronUnchanged Y [hd 0%nat (Output X)]); intro HNNX.
    inversion HNNX as [H3 [H4 H5]]. generalize (IH Y M P); intro HIH.
    unfold NextNeuron in H2. rewrite H2 in H1. simpl in H1.  
    assert (H1Copy: AllPositive (Weights Y)). { auto. } apply HIH in H1.
    + rewrite H2. simpl. unfold NextPotential.
      generalize (PositivePotential [hd 0%nat (Output X)] (Weights Y)); intro HPP.
      destruct (Qle_bool (Tau Y) (Current Y)) eqn: HQTC.
      * auto.
      * apply HPP in H1Copy. (generalize (LeakRange Y)); intro HLRY.
        inversion HLRY as [H6 H7]. apply Qle_bool_iff in H6.
        generalize (Qmult_le_0_compat (Leak_Factor Y) (Current Y)); intro HQM.
        apply HQM in H6.
        generalize (Qplus_le_compat 0 (potential (Weights Y) [hd 0%nat (Output X)]) 0 (Leak_Factor Y * Current Y)); intro HQP.
        apply HQP in H1Copy. auto. auto. auto.
   + auto.
Qed.

Lemma AfterN1Unchanged:
  forall (Inputs: list nat) (N P Q: Neuron),
  Eq_Neuron2 N (AfterNTwoLoopN1 (ResetNeuron P) (ResetNeuron Q) Inputs) ->
  (Leak_Factor P == Leak_Factor N) /\ (Tau P == Tau N) /\ (Weights P = Weights N).
Proof.
  induction Inputs as [ | h t IH].
  - intros N P Q H. simpl in H. generalize (ResetUnchanged P); intro HRU.
    unfold Eq_Neuron2 in H. inversion H as [H1 [H2 [H3 [H4 H5]]]].
    rewrite <- H2 in HRU. rewrite <- H3 in HRU. rewrite <- H4 in HRU. auto.
  - intros N P Q H. simpl in H.
    remember (AfterNTwoLoopN1 (ResetNeuron P) (ResetNeuron Q) t) as M.
    assert (Htemp: Eq_Neuron2 M (AfterNTwoLoopN1 (ResetNeuron P) (ResetNeuron Q) t)).
    { rewrite <- HeqM. unfold Eq_Neuron2. split. auto. split. auto. split. reflexivity.
      split; reflexivity. } generalize (IH M P Q); intro IHnew.
    generalize (NextNeuronUnchanged M [h; hd 0%nat (Output (AfterNTwoLoopN2 (ResetNeuron P) (ResetNeuron Q) t))]); intro HSR.
    apply IHnew in Htemp. unfold Eq_Neuron2 in H. inversion H as [H1 [H2 [H3 [H4 H5]]]].
    inversion HSR as [H6 [H7 H8]]. rewrite <- H2 in H8. rewrite <- H3 in H6.
    rewrite <- H4 in H7. rewrite H6 in Htemp. rewrite H7 in Htemp.
    rewrite H8 in Htemp. auto.
Qed.
    
Lemma AfterN2Unchanged:
  forall (Inputs: list nat) (N P Q: Neuron),
  Eq_Neuron2 N (AfterNTwoLoopN2 (ResetNeuron P) (ResetNeuron Q) Inputs) ->
  (Leak_Factor Q == Leak_Factor N) /\ (Tau Q == Tau N) /\ (Weights Q = Weights N).
Proof.
  induction Inputs as [ | h t IH].
  - intros N P Q H. simpl in H. generalize (ResetUnchanged Q); intro HRU.
    unfold Eq_Neuron2 in H. inversion H as [H1 [H2 [H3 [H4 H5]]]].
    rewrite <- H2 in HRU. rewrite <- H3 in HRU. rewrite <- H4 in HRU. auto.
  - intros N P Q H. simpl in H.
    remember (AfterNTwoLoopN2 (ResetNeuron P) (ResetNeuron Q) t) as M.
    assert (Htemp: Eq_Neuron2 M (AfterNTwoLoopN2 (ResetNeuron P) (ResetNeuron Q) t)).
    { rewrite <- HeqM. unfold Eq_Neuron2. split. auto. split. auto. split. reflexivity.
      split; reflexivity. } generalize (IH M P Q); intro IHnew.
    generalize (NextNeuronUnchanged M [hd 0%nat (Output (AfterNTwoLoopN1 (ResetNeuron P) (ResetNeuron Q) t))]); intro HSR.
    apply IHnew in Htemp. unfold Eq_Neuron2 in H. inversion H as [H1 [H2 [H3 [H4 H5]]]].
    inversion HSR as [H6 [H7 H8]]. rewrite <- H2 in H8. rewrite <- H3 in H6.
    rewrite <- H4 in H7. rewrite H6 in Htemp. rewrite H7 in Htemp.
    rewrite H8 in Htemp. auto.
Qed.

Lemma NextOutputN1_TPL_Helper:
  forall (Inputs: list nat) (P Q N M: Neuron),
  Qle_bool (Tau N) (hd 0 (Weights N)) = true ->
  Qle_bool (Tau N) (hd 0 (tl (Weights N)))  = true ->
  Qle_bool (Tau M) (hd 0 (Weights M))  = true ->
  (beq_nat (length (Weights N)) 2%nat) = true ->
  (beq_nat (length (Weights M)) 1%nat) = true ->
  0 < (hd 0 (Weights N)) ->
  0 < (hd 0 (tl (Weights N))) ->
  0 < (hd 0 (Weights M)) ->
  (hd 0%nat Inputs) = 1%nat \/ (hd 0%nat (tl (Output Q)) = 1%nat) ->
  Eq_Neuron2 P (AfterNTwoLoopN1 (ResetNeuron N) (ResetNeuron M) Inputs) ->
  Eq_Neuron2 Q (AfterNTwoLoopN2 (ResetNeuron N) (ResetNeuron M) Inputs) ->
    hd 0%nat (Output P) = 1%nat.
Proof.
  intros Inputs P Q N M H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
  remember (hd 0 (Weights N)) as w11.
  remember (hd 0 (Weights M)) as w21.
  remember (hd 0 (tl (Weights N))) as w12.
  assert (HWS: (Weights N) = [w11;w12]).
    { destruct (Weights N) as [ | h t].
      - simpl in H4. inversion H4. 
      - destruct t as [ | h' t']. 
        + simpl in H4. inversion H4. 
        + destruct t' as [ | h'' t'']. 
          * simpl in Heqw11. simpl in Heqw12. rewrite Heqw11. rewrite Heqw12. reflexivity.
          * simpl in H4. inversion H4. }
  assert (CopyH10: Eq_Neuron2 P (AfterNTwoLoopN1 (ResetNeuron N) (ResetNeuron M) Inputs)).
  { auto. }
  generalize (AfterN1Unchanged Inputs P N M); intro HAN1. apply HAN1 in CopyH10.
  inversion CopyH10 as [HA1 [HA2 HA3]]. clear HAN1.
  inversion H9 as [H12 | H13].
  - destruct Inputs as [ | h t].
    + inversion H12.
    + simpl in H10. unfold Eq_Neuron2 in H10.
      inversion H10 as [H14 [H15 H16]]. simpl in H12. rewrite H12 in H14.
      unfold NextNeuron in H14. simpl in H14. unfold NextOutput in H14. 
      unfold NextPotential in H14.
      remember (AfterNTwoLoopN1 (ResetNeuron N) (ResetNeuron M) t) as X.
      remember (AfterNTwoLoopN2 (ResetNeuron N) (ResetNeuron M) t) as Y.
      generalize (NextNeuronUnchanged X [h; hd 0%nat (Output Y)]); intro HNNU.
      inversion HNNU as [H17 [H18 H19]]. rewrite <- H19 in H15. rewrite <- HA3 in H15.
      rewrite HWS in H15. rewrite <- H15 in H14.
      destruct (Qle_bool (Tau X) (Current X)) eqn: HQTC.
      * unfold potential in H14. simpl in H14. generalize (Output_Bin Y); intro HOBY.
        generalize (ZeroOne (Output Y)); intro HZOY. apply HZOY in HOBY.
        inversion H16 as [H20 [H21 H22]]. rewrite <- H21 in H18. rewrite H18 in H14.
        inversion HOBY as [H23 | H24].
        { rewrite H23 in H14. rewrite Qplus_0_l in H14. rewrite HA2 in H1.
          rewrite H1 in H14. rewrite H14. auto. } 
        { rewrite beq_nat_true_iff in H24. rewrite H24 in H14. simpl in H14. 
          rewrite Qplus_0_l in H14. rewrite Qplus_comm in H14. apply Qle_bool_iff in H2. 
          generalize (Qplus_lt_le_compat 0 w11 (Tau N) w12); intro HQPLL.
          apply HQPLL in H6. rewrite Qplus_0_l in H6. apply Qlt_le_weak in H6.
          apply Qle_bool_iff in H6. rewrite HA2 in H6. rewrite H6 in H14. rewrite H14.
          auto. auto. }
      * assert (PositiveWeightsN: AllPositive (Weights X)). 
        { rewrite <- H15. simpl. auto. }
        assert (HighPotential: (Tau X) <= (potential [w11; w12] [1%nat; hd 0%nat (Output Y)])).
        { inversion H16 as [H20 [H21 H22]]. rewrite <- H18 in H21. rewrite <- H21.
          generalize (Output_Bin Y); intro HOB. generalize (ZeroOne (Output Y)); intro HZO.
          apply HZO in HOB. inversion HOB as [H23 | H24].
          { apply beq_nat_true_iff in H23. rewrite H23. simpl. rewrite Qplus_0_l.
            rewrite HA2 in H1. apply Qle_bool_iff in H1. auto. }
          { apply beq_nat_true_iff in H24. rewrite H24. simpl. rewrite Qplus_0_l.
            apply Qlt_le_weak in H7. apply Qle_bool_iff in H1.
            generalize (Qplus_le_compat 0 w12 (Tau N) w11); intro HQC.
            apply HQC in H7. rewrite Qplus_0_l in H7. rewrite <- HA2. auto. auto. } }
        generalize (PositiveCurrent1 t X N M); intro HPC. apply HPC in PositiveWeightsN.
        generalize (LeakRange X); intro HLN. inversion HLN as [H20 H21]. 
        apply Qle_bool_iff in H20. 
        generalize (Qmult_le_0_compat (Leak_Factor X) (Current X)); intro HQP.
        apply HQP in H20. 
        generalize (Qplus_le_compat (Tau X) (potential [w11; w12] [1%nat; hd 0%nat (Output Y)]) 0 (Leak_Factor X * Current X)); intro HQFinal.
        apply HQFinal in HighPotential. rewrite Qplus_0_r in HighPotential.
        apply Qle_bool_iff in HighPotential. rewrite HighPotential in H14.
        rewrite H14. simpl. reflexivity. auto. auto. auto.
  - unfold Eq_Neuron2 in H10.
    inversion H10 as [H14 [H15 [H16 [H17 H18]]]].
    destruct Inputs as [ | h t].
    + unfold Eq_Neuron2 in H11. inversion H11 as [H19 H20].
      simpl in H19. rewrite H19 in H13. simpl in H13. inversion H13.
    + simpl in H11. unfold Eq_Neuron2 in H11. inversion H11 as [H19 H20].
      unfold NextNeuron in H19. simpl in H19. simpl in H14. rewrite H19 in H13. simpl in H13.
      rewrite H13 in H14. 
      remember (AfterNTwoLoopN1 (ResetNeuron N) (ResetNeuron M) t) as X.
      remember (AfterNTwoLoopN2 (ResetNeuron N) (ResetNeuron M) t) as Y.
      unfold NextOutput in H14. unfold NextPotential in H14.
      generalize (NextNeuronUnchanged X [h; hd 0%nat (Output Y)]); intro HNNU.
      inversion HNNU as [H21 [H22 H23]]. simpl in H15. rewrite <- HeqX in H15.
      rewrite <- HA3 in H15. rewrite HWS in H15. rewrite <- H15 in H14. simpl in H17.
      rewrite <- HeqX in H17. destruct (Qle_bool (Tau X) (Current X)) eqn: HQTC.
      * destruct (beq_nat h 0%nat) eqn: HBN.
        { rewrite beq_nat_true_iff in HBN. rewrite HBN in H14.
          simpl in H14. rewrite Qplus_0_l in H14. rewrite <- HA2 in H17. rewrite H17 in H2.
          rewrite H2 in H14. rewrite H14. simpl. reflexivity. }
        { simpl in H14. rewrite HBN in H14. rewrite Qplus_0_l in H14.
          generalize (Qplus_le_compat 0 w12 (Tau X) w11); intro HQC.
          apply Qle_bool_iff in H1. rewrite <- HA2 in H17. rewrite H17 in H1.
          apply Qlt_le_weak in H7. apply HQC in H7. rewrite Qplus_0_l in H7.
          apply Qle_bool_iff in H7. rewrite H7 in H14. rewrite H14. simpl. reflexivity. auto. }
      * assert (PositiveWeightsX: AllPositive (Weights X)). 
        { rewrite <- H15. simpl. auto. }
        generalize (PositiveCurrent1 t X N M); intro HPC. apply HPC in PositiveWeightsX.
        generalize (LeakRange X); intro HLX. inversion HLX as [H24 H25].
        apply Qle_bool_iff in H24. generalize (Qmult_le_0_compat (Leak_Factor X) (Current X)); intro HQP.
        apply HQP in H24. destruct (beq_nat h 0%nat) eqn: HBN.
        { simpl in H14. rewrite HBN in H14. rewrite Qplus_0_l in H14.
          generalize (Qplus_le_compat (Tau X) w12 0 (Leak_Factor X * Current X)); intro HQC.
          rewrite <- HA2 in H17. rewrite H17 in H2. apply Qle_bool_iff in H2. apply HQC in H2.
          rewrite Qplus_0_r in H2. apply Qle_bool_iff in H2. rewrite H2 in H14.
          rewrite H14. simpl. reflexivity. auto. } 
        { simpl in H14. rewrite HBN in H14. rewrite Qplus_0_l in H14.
          generalize (Qplus_le_compat 0 w12 (Tau X) w11); intro HQC.
          apply Qlt_le_weak in H7. apply HQC in H7. rewrite Qplus_0_l in H7.
          generalize (Qplus_le_compat (Tau X) (w12 + w11) 0 (Leak_Factor X * Current X)); intro HQLC.
          apply HQLC in H7. rewrite Qplus_0_r in H7. apply Qle_bool_iff in H7.
          rewrite H7 in H14. rewrite H14. simpl. reflexivity. auto.
          rewrite <- HA2 in H17. rewrite H17 in H1. apply Qle_bool_iff in H1. auto. }
        auto. auto.
Qed.

Lemma NextOutputN1_TPL:
  forall (Inputs: list nat) (PLP: @PositiveLoop Inputs),
  Qle_bool (Tau (PL_N1 PLP)) (hd 0 (Weights (PL_N1 PLP)))  = true ->
  (Qle_bool (Tau (PL_N1 PLP)) (hd 0 (tl (Weights (PL_N1 PLP)))))  = true ->
  (Qle_bool (Tau (PL_N2 PLP)) (hd 0 (Weights (PL_N2 PLP))))  = true ->
  (hd 0%nat (Inputs)) = 1%nat \/ (hd 0%nat (tl (Output (PL_N2 PLP))) = 1%nat) -> 
    hd 0%nat (Output (PL_N1 PLP)) = 1%nat.
Proof.
  destruct PLP. simpl.
  intros H1 H2 H3 H4.
  generalize (NextOutputN1_TPL_Helper Inputs PL_N3 PL_N4 PL_N3 PL_N4); intro HNONTPLH.
  apply HNONTPLH in H1; auto.
Qed.

Lemma NextOutputN2_TPL_Helper:
  forall (Inputs: list nat) (P Q N M: Neuron),
  Qle_bool (Tau N) (hd 0 (Weights N)) = true ->
  Qle_bool (Tau N) (hd 0 (tl (Weights N)))  = true ->
  Qle_bool (Tau M) (hd 0 (Weights M))  = true ->
  (beq_nat (length (Weights N)) 2%nat) = true ->
  (beq_nat (length (Weights M)) 1%nat) = true ->
  0 < (hd 0 (Weights N)) ->
  0 < (hd 0 (tl (Weights N))) ->
  0 < (hd 0 (Weights M)) ->
  (hd 0%nat (tl (Output P)) = 1%nat) ->
  Eq_Neuron2 P (AfterNTwoLoopN1 (ResetNeuron N) (ResetNeuron M) Inputs) ->
  Eq_Neuron2 Q (AfterNTwoLoopN2 (ResetNeuron N) (ResetNeuron M) Inputs) ->
    hd 0%nat (Output Q) = 1%nat.
Proof.
  intros Inputs P Q N M H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
  remember (hd 0 (Weights M)) as w21.
  assert (HWS: (Weights M) = [w21]).
    { destruct (Weights M) as [ | h t]. 
      - simpl in H5. inversion H5. 
      - destruct t as [ | h' t']. 
        + simpl in Heqw21. rewrite Heqw21. reflexivity.
        + simpl in H5. inversion H5. }
  assert (CopyH11: Eq_Neuron2 Q (AfterNTwoLoopN2 (ResetNeuron N) (ResetNeuron M) Inputs)).
  { auto. }
  generalize (AfterN2Unchanged Inputs Q N M); intro HAN2.
  apply HAN2 in CopyH11. inversion CopyH11 as [HN1 [HN2 HN3]]. clear HAN2.
  unfold Eq_Neuron2 in H11.
  inversion H11 as [H12 [H13 [H14 [H15 H16]]]].
    destruct Inputs as [ | h t].
    - unfold Eq_Neuron2 in H10. inversion H10 as [H17 H18].
      simpl in H17. rewrite H17 in H9. simpl in H9. inversion H9.
    - simpl in H10. unfold Eq_Neuron2 in H10. inversion H10 as [H17 H18].
      unfold NextNeuron in H17. simpl in H17. simpl in H12. rewrite H17 in H9. simpl in H9.
      rewrite H9 in H12.
      remember (AfterNTwoLoopN1 (ResetNeuron N) (ResetNeuron M) t) as X.
      remember (AfterNTwoLoopN2 (ResetNeuron N) (ResetNeuron M) t) as Y.
      unfold NextOutput in H12. unfold NextPotential in H12.
      simpl in H13. rewrite <- HeqY in H13. rewrite <- HN3 in H13. rewrite H13 in HWS.
      rewrite HWS in H12. simpl in H15. rewrite <- HeqY in H15. rewrite <- HN2 in H15.
      rewrite H15 in H3. destruct (Qle_bool (Tau Y) (Current Y)) eqn: HQTC.
      + simpl in H12. rewrite Qplus_0_l in H12. rewrite H3 in H12. rewrite H12.
        simpl. reflexivity.
      + simpl in H12. rewrite Qplus_0_l in H12.
        assert (PositiveWeightsY: AllPositive (Weights Y)). 
        { rewrite HWS. simpl. auto. }
        generalize (PositiveCurrent2 t Y N M); intro HPC. apply HPC in PositiveWeightsY.
        generalize (LeakRange Y); intro HLY. inversion HLY as [H19 H20]. apply Qle_bool_iff in H19.
        generalize (Qmult_le_0_compat (Leak_Factor Y) (Current Y)); intro HQP. apply HQP in H19.
        generalize (Qplus_le_compat (Tau Y) w21 0 (Leak_Factor Y * Current Y)); intro HQC.
        apply Qle_bool_iff in H3. apply HQC in H3. rewrite Qplus_0_r in H3. apply Qle_bool_iff in H3.
        rewrite H3 in H12. rewrite H12. simpl. reflexivity. auto. auto. auto.
Qed.

Lemma NextOutputN2_TPL:
  forall (Inputs: list nat) (PLP: @PositiveLoop Inputs),
  Qle_bool (Tau (PL_N1 PLP)) (hd 0 (Weights (PL_N1 PLP)))  = true ->
  (Qle_bool (Tau (PL_N1 PLP)) (hd 0 (tl (Weights (PL_N1 PLP)))))  = true ->
  (Qle_bool (Tau (PL_N2 PLP)) (hd 0 (Weights (PL_N2 PLP))))  = true ->
  (hd 0%nat (tl (Output (PL_N1 PLP))) = 1%nat) -> hd 0%nat (Output (PL_N2 PLP)) = 1%nat.
Proof.
  destruct PLP. simpl.
  intros H1 H2 H3 H4.
  generalize (NextOutputN2_TPL_Helper Inputs PL_N3 PL_N4 PL_N3 PL_N4); intro HNONTPLH.
  apply HNONTPLH in H1; auto.
Qed.

Search modulo plus.
Search S plus.
Lemma Module3: forall (n: nat),
  (n mod 3) = 0%nat \/ (n mod 3) = 1%nat \/ (n mod 3) = 2%nat.
Proof.
 intros. induction n as [ | n'].
  - left. simpl. reflexivity.
  - inversion IHn' as [H1 | [H2 | H3]].
    + right. left. rewrite <- Nat.add_1_r. rewrite Nat.add_mod. rewrite H1.
      simpl. reflexivity. auto.
    + right. right. rewrite <- Nat.add_1_r. rewrite Nat.add_mod. rewrite H2.
      simpl. reflexivity. auto.
    + left. rewrite <- Nat.add_1_r. rewrite Nat.add_mod. rewrite H3.
      simpl. reflexivity. auto.
Qed.

(*Lemma  ReDefined:*)
 
Search List.nth rev. 

Search List.nth hd.

Search skipn.
Lemma FeedNInputs1:
  forall (n: nat) (Inputs rh: list nat) (N1 N2: Neuron),
  rh = skipn n Inputs ->
  n <=? (length Inputs) = true ->  
  Output (AfterNTwoLoopN1 (ResetNeuron N1) (ResetNeuron N2) rh) =
  skipn n (Output (AfterNTwoLoopN1 (ResetNeuron N1) (ResetNeuron N2) Inputs)).
Proof.
  induction n as [ | n' IH].
  - intros. simpl. simpl in H. rewrite H. reflexivity.
  - intros Inputs rh N1 N2 H1 H2. destruct Inputs as [ | h t].
    + simpl in H2. inversion H2. 
    + simpl in H1. simpl in H2. generalize (IH t rh N1 N2); intro IHnew.
      apply IHnew in H1. simpl. auto. auto.
Qed.

Lemma FeedNInputs2:
  forall (n: nat) (Inputs rh: list nat) (N1 N2: Neuron),
  rh = skipn n Inputs ->
  n <=? (length Inputs) = true ->  
  Output (AfterNTwoLoopN2 (ResetNeuron N1) (ResetNeuron N2) rh) =
  skipn n (Output (AfterNTwoLoopN2 (ResetNeuron N1) (ResetNeuron N2) Inputs)).
Proof.
  induction n as [ | n' IH].
  - intros. simpl. simpl in H. rewrite H. reflexivity.
  - intros Inputs rh N1 N2 H1 H2. destruct Inputs as [ | h t].
    + simpl in H2. inversion H2. 
    + simpl in H1. simpl in H2. generalize (IH t rh N1 N2); intro IHnew.
      apply IHnew in H1. simpl. auto. auto.
Qed.

Lemma HeadAfterSkip:
  forall (n d: nat) (l: list nat),
  List.nth n l d = hd d (skipn n l).
Proof.
  induction n as [ | n' IH].
  - intros d l. destruct l as [ | h t]. 
    + simpl. reflexivity.
    + simpl. reflexivity.
  - intros d l. destruct l as [ | h t].
    + simpl. reflexivity.
    + simpl. generalize (IH d t); intro IHnew. auto.
Qed.

(*Lemma SkipRev:
  forall (n m: nat) (l: list nat),
  m = length l -> skipn n (rev l) = rev (skipn (m - n) l).

skipn 2 (rev [1; 2; 4; 5; 6; 7]) = [5; 4; 2; 1]
rev (skipn (
*)
 
Lemma TailSkip:
  forall (x: nat) (l: list nat),
  skipn (S x) l = skipn x (tl l).
Proof. 
  intros.
  destruct x as [ | x'].
  - destruct l as [ | h t].
    + simpl. reflexivity.
    + simpl. reflexivity.
  - destruct l as [ | h t].
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.

Lemma TailOneMoreSkip:
  forall (l2 l1: list nat) (n: nat),
  l1 = skipn n l2 -> (tl l1) = skipn (S n) l2.
Proof.
  induction l2 as [ | h2 t2 IH].
  - destruct l1 as [ | h1 t1].
    + intros. simpl. reflexivity.
    + intros. destruct n as [ | n']. 
      * simpl in H. inversion H.
      * simpl in H. inversion H.
  - intros. destruct l1 as [ | h1 t1].
    + destruct n as [ | n'] eqn: HN.
      * simpl in H. inversion H.
      * simpl in H. destruct t2 as [ | h t].
        { simpl. reflexivity. }
        { simpl. generalize (IH [] n'); intro IHnew. apply IHnew in H.
          simpl in H. auto. }
    + destruct n as [ | n'] eqn: HN.
      * simpl in H. simpl. inversion H. auto.
      * simpl in H. destruct t2 as [ | h t].
        { simpl. generalize (IH (h1::t1) n'); intro IHnew. apply IHnew in H.
          simpl in H. auto. }
        { simpl. generalize (IH (h1::t1) n'); intro IHnew. apply IHnew in H.
          simpl in H. auto. }
Qed. 

Definition NewPosLoop (Inputs: list nat) (N M: Neuron)
           (NinputN1: (beq_nat (length (Weights N)) 2%nat) = true)
           (NinputN2: (beq_nat (length (Weights M)) 1%nat) = true)
           (PW1: 0 < (hd 0 (Weights N)))
           (PW2: 0 < (hd 0 (tl (Weights N))))
           (PW3: 0 < (hd 0 (Weights M)))
           (PL_Conn1: Eq_Neuron2 N
                                 (AfterNTwoLoopN1 (ResetNeuron N)
                                                  (ResetNeuron M) Inputs))
           (PL_Conn2: Eq_Neuron2 M
                                 (AfterNTwoLoopN2 (ResetNeuron N)
                                                  (ResetNeuron M) Inputs))
  : (@PositiveLoop Inputs) :=
  MakePositiveLoop
    (Inputs)
    (N)
    (M)
    (NinputN1)
    (NinputN2)
    (PW1)
    (PW2)
    (PW3)
    (PL_Conn1)
    (PL_Conn2).

Lemma NextTimeN1TPL_Helper:
  forall (Inputs: list nat) (time: nat) (P Q N M: Neuron),
  Qle_bool (Tau N) (hd 0 (Weights N)) = true ->
  Qle_bool (Tau N) (hd 0 (tl (Weights N)))  = true ->
  Qle_bool (Tau M) (hd 0 (Weights M))  = true ->
  (beq_nat (length (Weights N)) 2%nat) = true ->
  (beq_nat (length (Weights M)) 1%nat) = true ->
  0 < (hd 0 (Weights N)) ->
  0 < (hd 0 (tl (Weights N))) ->
  0 < (hd 0 (Weights M)) ->
  Eq_Neuron2 P (AfterNTwoLoopN1 (ResetNeuron N) (ResetNeuron M) Inputs) ->
  Eq_Neuron2 Q (AfterNTwoLoopN2 (ResetNeuron N) (ResetNeuron M) Inputs) ->
  List.nth time (rev (Inputs)) 0%nat = 1%nat \/
  List.nth time (rev (Output Q)) 0%nat = 1%nat ->
  (time + 1) <? length (Output P) = true ->
  List.nth (time + 1) (rev (Output P)) 0%nat = 1%nat.
Proof.
  intros Inputs time P Q N M H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 HEXT.
  inversion H11 as [H12 | H13].
  - generalize (@rev_nth nat Inputs 0%nat time); intro HRNI.
    destruct (time <? (length Inputs)) eqn: Htl.
    + assert (CopyHtl: (time <? length Inputs) = true). { auto. }
      apply Nat.ltb_lt in Htl. apply HRNI in Htl. rewrite Htl in H12.
      generalize (HeadAfterSkip (length Inputs - S time) 0%nat Inputs); intro HHAS. 
      rewrite HHAS in H12. remember (skipn (length Inputs - S time) Inputs) as rh. 
      remember (AfterNTwoLoopN1 (ResetNeuron N) (ResetNeuron M) rh) as X.
      remember (AfterNTwoLoopN2 (ResetNeuron N) (ResetNeuron M) rh) as Y.
      assert (CopyX: X = AfterNTwoLoopN1 (ResetNeuron N) (ResetNeuron M) rh). { auto. }
      generalize (NextOutputN1_TPL_Helper rh X Y N M); intro HNON.  
      generalize (AfterN1Unchanged rh X N M); intro HAN1. 
      assert (HtempX: Eq_Neuron2 X (AfterNTwoLoopN1 (ResetNeuron N) (ResetNeuron M) rh)). 
      { unfold Eq_Neuron2. rewrite <- HeqX. split. auto. split. auto. split. reflexivity. split; reflexivity. }
      assert (CopyHtX: Eq_Neuron2 X (AfterNTwoLoopN1 (ResetNeuron N) (ResetNeuron M) rh)). { auto. }
      assert (HtempY: Eq_Neuron2 Y (AfterNTwoLoopN2 (ResetNeuron N) (ResetNeuron M) rh)). 
      { unfold Eq_Neuron2. rewrite <- HeqY. split. auto. split. auto. split. reflexivity. split; reflexivity. }
      assert (CopyHtY: Eq_Neuron2 Y (AfterNTwoLoopN2 (ResetNeuron N) (ResetNeuron M) rh)). { auto. }
      apply HAN1 in HtempX. inversion HtempX as [H13 [H14 H15]]. (*rewrite H14 in HNON. rewrite H15 in HNON.*)
      apply HNON in H1. generalize (FeedNInputs1 (length Inputs - S time) Inputs rh N M); intro HFNI.
      apply HFNI in Heqrh. rewrite <- CopyX in Heqrh. rewrite Heqrh in H1. 
      generalize (HeadAfterSkip (length Inputs - S time) 0%nat (Output (AfterNTwoLoopN1 (ResetNeuron N) (ResetNeuron M) Inputs))); intro HAS.
      rewrite <- HAS in H1. unfold Eq_Neuron2 in H9. inversion H9 as [H16 H17].
      rewrite <- H16 in H1. generalize (rev_nth (Output P) 0%nat); intro HRN. 
      (* Tell Amy About this *)       
      generalize (InOutLengthHelper Inputs P Q N M); intro HIOL.
      unfold Eq_Neuron2 in HIOL. apply HIOL in H9. inversion H9 as [H18 H19].
      apply beq_nat_true_iff in H18. generalize (HRN (S time)); intro HR. apply Nat.ltb_lt in CopyHtl.
      apply lt_n_S in CopyHtl. rewrite Nat.add_1_r in H18. rewrite H18 in CopyHtl. apply HR in CopyHtl.
      generalize (Nat.sub_succ (length Inputs) (S time)); intro HSS. rewrite H18 in HSS. rewrite <- HSS in H1.
      rewrite H1 in CopyHtl. rewrite Nat.add_1_r. auto.
      unfold Eq_Neuron2 in H10. auto.
      generalize (Nat.le_sub_l (length Inputs) (S time)); intro HNLL. apply Nat.leb_le in HNLL. auto.
      auto. generalize (AfterN2Unchanged rh Y N M); intro HAN2. apply HAN2 in HtempY.
      inversion HtempY as [H16 [H17 H18]]. auto. auto. auto. auto. auto. auto. left. auto. auto. auto.
    + apply Nat.ltb_ge in Htl. generalize (@nth_overflow nat (rev Inputs) time 0%nat); intro HN.
      generalize (rev_length Inputs); intro HRL. rewrite HRL in HN. apply HN in Htl.
      rewrite Htl in H12. inversion H12.
  - generalize (@rev_nth nat (Output Q) 0%nat time); intro HRNI.  
    destruct (time <? (length Inputs)) eqn: Htl.
    + generalize (InOutLengthHelper Inputs P Q N M); intro HIOL. generalize (HIOL H9 H10); intro HA.
      inversion HA as [H12 H14]. apply Nat.ltb_lt in Htl.
      generalize (Nat.lt_lt_succ_r time (length Inputs)); intro HLLS.
      generalize (HLLS Htl); intro HB. generalize (Nat.add_1_r (length Inputs)); intro HAL. rewrite HAL in H14.
      apply beq_nat_true_iff in H14. rewrite H14 in HB. generalize (HRNI HB); intro HC. rewrite HC in H13.
      (*generalize (TailSkip (length Inputs - S time) (Output Q)); intro HTLS. 
      generalize (lt_le_S time (length Inputs)); intro HD. generalize (HD Htl); intro HE. 
      generalize (minus_Sn_m (length Inputs) (S time)); intro HF. generalize (HF HE); intro HG.
      rewrite HG in HTLS. rewrite H14 in HTLS.*)
      remember (skipn (length Inputs - S time) Inputs) as rh.
      remember (AfterNTwoLoopN1 (ResetNeuron N) (ResetNeuron M) rh) as X.
      remember (AfterNTwoLoopN2 (ResetNeuron N) (ResetNeuron M) rh) as Y.
      generalize (FeedNInputs2 (length Inputs - S time) Inputs rh N M); intro HFNI.
      generalize (Nat.le_sub_l (length Inputs) (S time)); intro HNL.  
      apply Nat.leb_le in HNL. generalize (HFNI Heqrh HNL); intro HE.
      rewrite <- HeqY in HE. unfold Eq_Neuron2 in H10. inversion H10 as [H15 H16].
      rewrite <- H15 in HE. generalize (TailOneMoreSkip (Output Q) (Output Y) (length Inputs - S time)); intro HTOM.
      generalize (HTOM HE); intro HF. generalize (lt_le_S time (length Inputs)); intro HG.
      generalize (HG Htl); intro HH. generalize (minus_Sn_m (length Inputs) (S time)); intro HI.
      generalize (HI HH); intro HJ. rewrite HJ in HF. rewrite H14 in HF.
      generalize (HeadAfterSkip (length (Output Q) - S time) 0%nat (Output Q)); intro HSK.
      rewrite <- HF in HSK. rewrite H13 in HSK. generalize (NextOutputN1_TPL_Helper rh X Y N M); intro HNON.
      assert (HtempX: Eq_Neuron2 X (AfterNTwoLoopN1 (ResetNeuron N) (ResetNeuron M) rh)). 
      { unfold Eq_Neuron2. rewrite <- HeqX. split. auto. split. auto. split. reflexivity. split; reflexivity. }
      assert (HtempY: Eq_Neuron2 Y (AfterNTwoLoopN2 (ResetNeuron N) (ResetNeuron M) rh)). 
      { unfold Eq_Neuron2. rewrite <- HeqY. split. auto. split. auto. split. reflexivity. split; reflexivity. }
      assert (HOY: hd 0%nat rh = 1%nat \/ hd 0%nat (tl (Output Y)) = 1%nat). { right. auto. }
      generalize (HNON H1 H2 H3 H4 H5 H6 H7 H8 HOY HtempX HtempY); intro HKEY.
      generalize (FeedNInputs1 (length Inputs - S time) Inputs rh N M); intro HFN.
      generalize (HFN Heqrh HNL); intro HK. unfold Eq_Neuron2 in H9. inversion H9 as [H17 H18].
      rewrite <- H17 in HK. rewrite <- HeqX in HK.
      generalize (HeadAfterSkip (length Inputs - S time) 0%nat (Output P)); intro HAS.
      rewrite <- HK in HAS. rewrite HKEY in HAS. rewrite HAL in H12.
      generalize (@rev_nth nat (Output P) 0%nat (S time)); intro HRNP.
      apply beq_nat_true_iff in H12. assert (HSP: S time <? length (Output P) = true).
      { rewrite <- H12. apply Nat.ltb_lt. apply lt_n_S. auto. }
      apply Nat.ltb_lt in HSP. generalize (HRNP HSP); intro HL. rewrite <- H12 in HL.
      generalize (Nat.sub_succ (length Inputs) (S time)); intro HM. rewrite HM in HL.
      rewrite HAS in HL. generalize (Nat.add_1_r time); intro HNT. rewrite <- HNT in HL. auto.
    + apply Nat.ltb_ge in Htl. generalize (le_n_S (length Inputs) time); intro HLLN.
      generalize (HLLN Htl); intro HA. generalize (InOutLengthHelper Inputs P Q N M); intro HIOL.
      generalize (HIOL H9 H10); intro HB. inversion HB as [H12 H14].
      generalize (Nat.add_1_r (length Inputs)); intro HAL. rewrite HAL in H12.
      apply beq_nat_true_iff in H12. rewrite H12 in HA. generalize (Nat.add_1_r time); intro HC.
      rewrite HC in HEXT. generalize (Nat.ltb_antisym (length (Output P)) (S time)); intro HN.
      apply Nat.leb_le in HA. rewrite HEXT in HN. rewrite HA in HN. simpl in HN. inversion HN.
Qed.

Lemma NextTimeN1TPL:
  forall (Inputs: list nat) (time: nat) (PLP: @PositiveLoop Inputs),
  Qle_bool (Tau (PL_N1 PLP)) (hd 0 (Weights (PL_N1 PLP)))  = true ->
  (Qle_bool (Tau (PL_N1 PLP)) (hd 0 (tl (Weights (PL_N1 PLP)))))  = true ->
  (Qle_bool (Tau (PL_N2 PLP)) (hd 0 (Weights (PL_N2 PLP))))  = true ->
  List.nth time (rev (Inputs)) 0%nat = 1%nat \/
  List.nth time (rev (Output (PL_N2 PLP))) 0%nat = 1%nat ->
  (time + 1) <? length (Output (PL_N1 PLP)) = true ->
  List.nth (time + 1) (rev (Output (PL_N1 PLP))) 0%nat = 1%nat.
Proof.
  destruct PLP. simpl.
  intros H1 H2 H3 H4 H5. 
  generalize (NextTimeN1TPL_Helper Inputs time PL_N3 PL_N4 PL_N3 PL_N4); intro HNTNTPL.
  apply HNTNTPL in H1; auto.
Qed.

Lemma NextTimeN2TPL_Helper:
  forall (Inputs: list nat) (time: nat) (P Q N M: Neuron),
  Qle_bool (Tau N) (hd 0 (Weights N)) = true ->
  Qle_bool (Tau N) (hd 0 (tl (Weights N)))  = true ->
  Qle_bool (Tau M) (hd 0 (Weights M))  = true ->
  (beq_nat (length (Weights N)) 2%nat) = true ->
  (beq_nat (length (Weights M)) 1%nat) = true ->
  0 < (hd 0 (Weights N)) ->
  0 < (hd 0 (tl (Weights N))) ->
  0 < (hd 0 (Weights M)) ->
  Eq_Neuron2 P (AfterNTwoLoopN1 (ResetNeuron N) (ResetNeuron M) Inputs) ->
  Eq_Neuron2 Q (AfterNTwoLoopN2 (ResetNeuron N) (ResetNeuron M) Inputs) ->
  List.nth time (rev (Output P)) 0%nat = 1%nat ->
  (time + 1) <? length (Output Q) = true ->
  List.nth (time + 1) (rev (Output Q)) 0%nat = 1%nat.
Proof.
  intros Inputs time P Q N M H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 HEXT.
  generalize (@rev_nth nat (Output P) 0%nat time); intro HRNI.  
  destruct (time <? (length Inputs)) eqn: Htl.
  + generalize (InOutLengthHelper Inputs P Q N M); intro HIOL. generalize (HIOL H9 H10); intro HA.
    inversion HA as [H12 H13]. apply Nat.ltb_lt in Htl.
    generalize (Nat.lt_lt_succ_r time (length Inputs)); intro HLLS.
    generalize (HLLS Htl); intro HB. generalize (Nat.add_1_r (length Inputs)); intro HAL. rewrite HAL in H12.
    apply beq_nat_true_iff in H12. rewrite H12 in HB. generalize (HRNI HB); intro HC. rewrite HC in H11.
    (*generalize (TailSkip (length Inputs - S time) (Output Q)); intro HTLS. 
    generalize (lt_le_S time (length Inputs)); intro HD. generalize (HD Htl); intro HE. 
    generalize (minus_Sn_m (length Inputs) (S time)); intro HF. generalize (HF HE); intro HG.
    rewrite HG in HTLS. rewrite H14 in HTLS.*)
    remember (skipn (length Inputs - S time) Inputs) as rh.
    remember (AfterNTwoLoopN1 (ResetNeuron N) (ResetNeuron M) rh) as X.
    remember (AfterNTwoLoopN2 (ResetNeuron N) (ResetNeuron M) rh) as Y.
    generalize (FeedNInputs1 (length Inputs - S time) Inputs rh N M); intro HFNI.
    generalize (Nat.le_sub_l (length Inputs) (S time)); intro HNL.  
    apply Nat.leb_le in HNL. generalize (HFNI Heqrh HNL); intro HE.
    rewrite <- HeqX in HE. unfold Eq_Neuron2 in H9. inversion H9 as [H14 H15].
    rewrite <- H14 in HE. generalize (TailOneMoreSkip (Output P) (Output X) (length Inputs - S time)); intro HTOM.
    generalize (HTOM HE); intro HF. generalize (lt_le_S time (length Inputs)); intro HG.
    generalize (HG Htl); intro HH. generalize (minus_Sn_m (length Inputs) (S time)); intro HI.
    generalize (HI HH); intro HJ. rewrite HJ in HF. rewrite H12 in HF.
    generalize (HeadAfterSkip (length (Output P) - S time) 0%nat (Output P)); intro HSK.
    rewrite <- HF in HSK. rewrite H11 in HSK. generalize (NextOutputN2_TPL_Helper rh X Y N M); intro HNON.
    assert (HtempX: Eq_Neuron2 X (AfterNTwoLoopN1 (ResetNeuron N) (ResetNeuron M) rh)). 
    { unfold Eq_Neuron2. rewrite <- HeqX. split. auto. split. auto. split. reflexivity. split; reflexivity. }
    assert (HtempY: Eq_Neuron2 Y (AfterNTwoLoopN2 (ResetNeuron N) (ResetNeuron M) rh)). 
    { unfold Eq_Neuron2. rewrite <- HeqY. split. auto. split. auto. split. reflexivity. split; reflexivity. }
    symmetry in HSK.     
    (*assert (HOX: hd 0%nat rh = 1%nat \/ hd 0%nat (tl (Output X)) = 1%nat). { right. auto. }*)
    generalize (HNON H1 H2 H3 H4 H5 H6 H7 H8 HSK HtempX HtempY); intro HKEY.
    generalize (FeedNInputs2 (length Inputs - S time) Inputs rh N M); intro HFN.
    generalize (HFN Heqrh HNL); intro HK. unfold Eq_Neuron2 in H10. inversion H10 as [H16 H17].
    rewrite <- H16 in HK. rewrite <- HeqY in HK.
    generalize (HeadAfterSkip (length Inputs - S time) 0%nat (Output Q)); intro HAS.
    rewrite <- HK in HAS. rewrite HKEY in HAS. rewrite HAL in H13.
    generalize (@rev_nth nat (Output Q) 0%nat (S time)); intro HRNP.
    apply beq_nat_true_iff in H13. assert (HSP: S time <? length (Output Q) = true).
    { rewrite <- H13. apply Nat.ltb_lt. apply lt_n_S. auto. }
    apply Nat.ltb_lt in HSP. generalize (HRNP HSP); intro HL. rewrite <- H13 in HL.
    generalize (Nat.sub_succ (length Inputs) (S time)); intro HM. rewrite HM in HL.
    rewrite HAS in HL. generalize (Nat.add_1_r time); intro HNT. rewrite <- HNT in HL. auto.
    + apply Nat.ltb_ge in Htl. generalize (le_n_S (length Inputs) time); intro HLLN.
      generalize (HLLN Htl); intro HA. generalize (InOutLengthHelper Inputs P Q N M); intro HIOL.
      generalize (HIOL H9 H10); intro HB. inversion HB as [H12 H13].
      generalize (Nat.add_1_r (length Inputs)); intro HAL. rewrite HAL in H13.
      apply beq_nat_true_iff in H13. rewrite H13 in HA. generalize (Nat.add_1_r time); intro HC.
      rewrite HC in HEXT. generalize (Nat.ltb_antisym (length (Output Q)) (S time)); intro HN.
      apply Nat.leb_le in HA. rewrite HEXT in HN. rewrite HA in HN. simpl in HN. inversion HN.
Qed.

Lemma NextTimeN2TPL:
  forall (Inputs: list nat) (time: nat) (PLP: @PositiveLoop Inputs),
  Qle_bool (Tau (PL_N1 PLP)) (hd 0 (Weights (PL_N1 PLP)))  = true ->
  (Qle_bool (Tau (PL_N1 PLP)) (hd 0 (tl (Weights (PL_N1 PLP)))))  = true ->
  (Qle_bool (Tau (PL_N2 PLP)) (hd 0 (Weights (PL_N2 PLP))))  = true ->
  List.nth time (rev (Output (PL_N1 PLP))) 0%nat = 1%nat ->
  (time + 1) <? length (Output (PL_N2 PLP)) = true ->
  List.nth (time + 1) (rev (Output (PL_N2 PLP))) 0%nat = 1%nat.
Proof.
  destruct PLP. simpl.
  intros H1 H2 H3 H4 H5.
  generalize (NextTimeN2TPL_Helper Inputs time PL_N3 PL_N4 PL_N3 PL_N4); intro HNTNTPL.
  apply HNTNTPL in H1; auto.
Qed.

Search div modulo.
Search mult.

Lemma Division3:
  forall (n: nat) (k: nat),
  k = (n / 3)%nat -> n = (3 * k)%nat \/ n = ((3 * k)%nat + 1%nat)%nat \/ n = ((3 * k)%nat + 2%nat)%nat.
Proof.
  intros n k H. generalize (Module3 n); intro HMK.
  generalize (Nat.div_mod n 3); intro HME. assert (Ht: 3%nat <> 0%nat). { auto. }
  generalize (HME Ht); intro HM.
  inversion HMK as [HM1 | [HM2 | HM3]].
  - left. rewrite HM1 in HM. rewrite <- plus_n_O in HM. rewrite <- H in HM. auto.
  - right. left. rewrite HM2 in HM. rewrite <- H in HM. auto.
  - right. right. rewrite HM3 in HM. rewrite <- H in HM. auto.
Qed.

Lemma Length_Succ:
  forall (t: list nat) (h: nat),
  length (h::t) = S (length t).
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma NextInPatternMod0:
  forall (n: nat) (Inputs: list nat),
  Pattern Inputs [0%nat;1%nat;1%nat] 0%nat ->
  n <? length Inputs = true ->
  n mod 3 = 0%nat -> List.nth n Inputs 0%nat = 0%nat.
Proof.
  intro n. 
  generalize
    (lt_wf_ind n
      (fun n:nat =>
         forall (Inputs: list nat),
           Pattern Inputs [0%nat;1%nat;1%nat] 0%nat ->
           n <? length Inputs = true ->
           n mod 3 = 0%nat -> List.nth n Inputs 0%nat = 0%nat)).
  intro h'.
  apply h'; clear h'; auto.
  clear n.
  intros.
  destruct n as [ | n1].
  - destruct Inputs as [ | h t].
    + inversion H1.
    + simpl in H0. inversion H0 as [H3 H4]. inversion H3. simpl. auto.
  - destruct Inputs as [ | h1 t1].
    + simpl in H1. inversion H1.
    + destruct n1 as [ | n2].
      * inversion H2. 
      * destruct n2 as [ | n3].
        { inversion H2. }
        { destruct t1 as [ | h2 t2]. 
          { inversion H1. }
          { destruct t2 as [ | h3 t3].
            { inversion H1. }
            { simpl. generalize (Nat.add_1_l n3); intro HX. generalize (Nat.add_1_l (1 + n3)%nat); intro HY.
              generalize (Nat.add_1_l (1 + (1 + n3)%nat)%nat); intro HZ. rewrite <- HX in H2. rewrite <- HY in H2.
              rewrite <- HZ in H2. rewrite Nat.add_assoc in H2. rewrite Nat.add_assoc in H2. 
              assert (Htemp: ((1%nat + 1%nat)%nat + 1%nat)%nat = 3%nat). { auto. }
              rewrite Htemp in H2. rewrite Nat.add_mod in H2. assert (Ht: 3 mod 3 = 0%nat). { auto. }
              rewrite Ht in H2. assert (Hs: n3 mod 3 = 0%nat).
              { generalize (Module3 n3); intro HMD. inversion HMD as [HMD1 | [HMD2 | HMD3]].
                { auto. } { rewrite HMD2 in H2. simpl in H2. inversion H2. } 
                { rewrite HMD3 in H2. simpl in H2. inversion H2. } } 
              assert (Hm: (n3 < S (S (S n3)))%nat).
              { generalize (Nat.lt_succ_diag_r n3); intro HA. generalize (Nat.lt_succ_diag_r (S n3)); intro HB.
                generalize (Nat.lt_succ_diag_r (S (S n3))); intro HC.
                generalize (Nat.lt_trans n3 (S n3) (S (S n3))); intro HD. generalize (HD HA HB); intro HE. 
                generalize (Nat.lt_trans n3 (S (S n3)) (S (S (S n3)))); intro HF. 
                generalize (HF HE HC); intro HH. auto. }
              assert (Hn: (n3 <? length t3) = true).
              { rewrite Length_Succ in H1. rewrite Length_Succ in H1. rewrite Length_Succ in H1. 
                apply Nat.ltb_lt in H1. apply lt_S_n in H1. apply lt_S_n in H1. apply lt_S_n in H1. 
                apply Nat.ltb_lt. auto. } 
              simpl in H0. inversion H0 as [H3 [H4 [H5 H6]]].
              assert (Hr: Pattern t3 [0%nat; 1%nat; 1%nat] 0%nat).
              { simpl. auto. } generalize (H n3 Hm t3 Hr Hn Hs); intro HKEY. auto. auto. } } }
Qed. 

Lemma NextInPatternMod1:
  forall (n: nat) (Inputs: list nat),
  Pattern Inputs [0%nat;1%nat;1%nat] 0%nat ->
  n <? length Inputs = true ->
  n mod 3 = 1%nat -> List.nth n Inputs 0%nat = 1%nat. 
Proof.
  intro n. 
  generalize
    (lt_wf_ind n
      (fun n:nat =>
         forall (Inputs: list nat),
           Pattern Inputs [0%nat;1%nat;1%nat] 0%nat ->
           n <? length Inputs = true ->
           n mod 3 = 1%nat -> List.nth n Inputs 0%nat = 1%nat)).
  intro h'.
  apply h'; clear h'; auto.
  clear n.
  intros.
  destruct n as [ | n1].
  - inversion H2. 
  - destruct Inputs as [ | h1 t1].
    + inversion H1.
    + destruct n1 as [ | n2]. 
      * simpl. destruct t1 as [ | h2 t2]. 
        { inversion H1. } 
        { simpl. simpl in H0. inversion H0 as [H3 [H4 H5]]. inversion H4. auto. }
      * destruct n2 as [ | n3].
        { inversion H2. }
        { destruct t1 as [ | h2 t2].
          { inversion H1. }
          { destruct t2 as [ | h3 t3].
            { inversion H1. }
            { simpl. generalize (Nat.add_1_l n3); intro HX. generalize (Nat.add_1_l (1 + n3)%nat); intro HY.
              generalize (Nat.add_1_l (1 + (1 + n3)%nat)%nat); intro HZ. rewrite <- HX in H2. rewrite <- HY in H2.
              rewrite <- HZ in H2. rewrite Nat.add_assoc in H2. rewrite Nat.add_assoc in H2. 
              assert (Htemp: ((1%nat + 1%nat)%nat + 1%nat)%nat = 3%nat). { auto. }
              rewrite Htemp in H2. rewrite Nat.add_mod in H2. assert (Ht: 3 mod 3 = 0%nat). { auto. }
              rewrite Ht in H2. assert (Hs: n3 mod 3 = 1%nat).
              { generalize (Module3 n3); intro HMD. inversion HMD as [HMD1 | [HMD2 | HMD3]].
                { rewrite HMD1 in H2. simpl in H2. inversion H2. } { auto. }
                { rewrite HMD3 in H2. simpl in H2. inversion H2. } } 
              assert (Hm: (n3 < S (S (S n3)))%nat).
              { generalize (Nat.lt_succ_diag_r n3); intro HA. generalize (Nat.lt_succ_diag_r (S n3)); intro HB.
                generalize (Nat.lt_succ_diag_r (S (S n3))); intro HC.
                generalize (Nat.lt_trans n3 (S n3) (S (S n3))); intro HD. generalize (HD HA HB); intro HE. 
                generalize (Nat.lt_trans n3 (S (S n3)) (S (S (S n3)))); intro HF. 
                generalize (HF HE HC); intro HH. auto. }
              assert (Hn: (n3 <? length t3) = true).
              { rewrite Length_Succ in H1. rewrite Length_Succ in H1. rewrite Length_Succ in H1. 
                apply Nat.ltb_lt in H1. apply lt_S_n in H1. apply lt_S_n in H1. apply lt_S_n in H1. 
                apply Nat.ltb_lt. auto. } 
              simpl in H0. inversion H0 as [H3 [H4 [H5 H6]]].
              assert (Hr: Pattern t3 [0%nat; 1%nat; 1%nat] 0%nat).
              { simpl. auto. } generalize (H n3 Hm t3 Hr Hn Hs); intro HKEY. auto. auto. } } }
Qed.

Lemma NextInPatternMod2:
  forall (n: nat) (Inputs: list nat),
  Pattern Inputs [0%nat;1%nat;1%nat] 0%nat ->
  n <? length Inputs = true ->
  n mod 3 = 2%nat -> List.nth n Inputs 0%nat = 1%nat. 
Proof.
  intro n.
  generalize
    (lt_wf_ind n
      (fun n:nat =>
         forall (Inputs: list nat),
           Pattern Inputs [0%nat;1%nat;1%nat] 0%nat ->
           n <? length Inputs = true ->
           n mod 3 = 2%nat -> List.nth n Inputs 0%nat = 1%nat)).
  intro h'.
  apply h'; clear h'; auto.
  clear n.
  intros.
  destruct n as [ | n1].
  - inversion H2. 
  - destruct Inputs as [ | h1 t1].
    + inversion H1.
    + destruct n1 as [ | n2]. 
      * inversion H2. 
      * destruct t1 as [ | h2 t2]. 
        { inversion H1. } 
        { destruct t2 as [ | h3 t3].
          { inversion H1. }
          { destruct n2 as [ | n3].
            { simpl in H0. inversion H0 as [H3 [H4 [H5 H6]]]. simpl. inversion H5. auto. }
            { simpl. generalize (Nat.add_1_l n3); intro HX. generalize (Nat.add_1_l (1 + n3)%nat); intro HY.
              generalize (Nat.add_1_l (1 + (1 + n3)%nat)%nat); intro HZ. rewrite <- HX in H2. rewrite <- HY in H2.
              rewrite <- HZ in H2. rewrite Nat.add_assoc in H2. rewrite Nat.add_assoc in H2. 
              assert (Htemp: ((1%nat + 1%nat)%nat + 1%nat)%nat = 3%nat). { auto. }
              rewrite Htemp in H2. rewrite Nat.add_mod in H2. assert (Ht: 3 mod 3 = 0%nat). { auto. }
              rewrite Ht in H2. assert (Hs: n3 mod 3 = 2%nat).
              { generalize (Module3 n3); intro HMD. inversion HMD as [HMD1 | [HMD2 | HMD3]].
                { rewrite HMD1 in H2. simpl in H2. inversion H2. } 
                { rewrite HMD2 in H2. simpl in H2. inversion H2. } { auto. } } 
              assert (Hm: (n3 < S (S (S n3)))%nat).
              { generalize (Nat.lt_succ_diag_r n3); intro HA. generalize (Nat.lt_succ_diag_r (S n3)); intro HB.
                generalize (Nat.lt_succ_diag_r (S (S n3))); intro HC.
                generalize (Nat.lt_trans n3 (S n3) (S (S n3))); intro HD. generalize (HD HA HB); intro HE. 
                generalize (Nat.lt_trans n3 (S (S n3)) (S (S (S n3)))); intro HF. 
                generalize (HF HE HC); intro HH. auto. }
              assert (Hn: (n3 <? length t3) = true).
              { rewrite Length_Succ in H1. rewrite Length_Succ in H1. rewrite Length_Succ in H1. 
                apply Nat.ltb_lt in H1. apply lt_S_n in H1. apply lt_S_n in H1. apply lt_S_n in H1. 
                apply Nat.ltb_lt. auto. } 
              simpl in H0. inversion H0 as [H3 [H4 [H5 H6]]].
              assert (Hr: Pattern t3 [0%nat; 1%nat; 1%nat] 0%nat).
              { simpl. auto. } generalize (H n3 Hm t3 Hr Hn Hs); intro HKEY. auto. auto. } } }
Qed.

Lemma nthRelation: forall {T: Type} (l: list T) (ind: nat) (k: T) (d: T),
  ind <? length l = true -> (nth l ind = Some k <-> List.nth ind l d = k).
Proof.
  induction l as [ | h t IH].
  - split; inversion H.
  - split.
    + intros H1. destruct ind as [ | n]. 
      * simpl in H1. simpl. inversion H1. auto.
      * simpl in H1. (*rewrite Nat.sub_0_r in H1.*) simpl. generalize (IH n k d); intro HK.
        simpl in H. apply Nat.ltb_lt in H. apply lt_S_n in H. apply Nat.ltb_lt in H.
        apply HK in H. apply H in H1. auto.
    + intros H1. destruct ind as [ | n].
      * simpl in H1. simpl. rewrite H1. reflexivity.
      * simpl in H1. simpl. (*rewrite Nat.sub_0_r.*) generalize (IH n k d); intro HK.
        simpl in H. apply Nat.ltb_lt in H. apply lt_S_n in H. apply Nat.ltb_lt in H.
        apply HK in H. apply H in H1. auto.
Qed. 
    
Lemma Pattern011IsBin: forall (l: list nat),
  Pattern l [0%nat;1%nat;1%nat] 0%nat -> (forall (ind: nat), nth l ind = Some 0%nat \/ nth l ind = Some 1%nat \/ nth l ind = None).
Proof.
  intros. generalize (Module3 ind); intro HM.
  inversion HM as [HM1 | [HM2 | HM3]].
  - destruct (ind <? length l) eqn: H1. 
    + left. generalize (NextInPatternMod0 ind l); intro HNIP.
      generalize (HNIP H H1 HM1); intro HK. generalize (nthRelation l ind 0%nat 0%nat); intro HF.
      apply HF in H1. rewrite H1. auto.
    + right. right. generalize (OutofRange l ind); intro HOR. apply Nat.ltb_nlt in H1.
      apply Nat.nlt_ge in H1. apply Nat.leb_le in H1. apply HOR in H1. auto.
  - destruct (ind <? length l) eqn: H1. 
    + right. left. generalize (NextInPatternMod1 ind l); intro HNIP.
      generalize (HNIP H H1 HM2); intro HK. generalize (nthRelation l ind 1%nat 0%nat); intro HF.
      apply HF in H1. rewrite H1. auto.
    + right. right. generalize (OutofRange l ind); intro HOR. apply Nat.ltb_nlt in H1.
      apply Nat.nlt_ge in H1. apply Nat.leb_le in H1. apply HOR in H1. auto.
  - destruct (ind <? length l) eqn: H1. 
    + right. left. generalize (NextInPatternMod2 ind l); intro HNIP.
      generalize (HNIP H H1 HM3); intro HK. generalize (nthRelation l ind 1%nat 0%nat); intro HF.
      apply HF in H1. rewrite H1. auto.
    + right. right. generalize (OutofRange l ind); intro HOR. apply Nat.ltb_nlt in H1.
      apply Nat.nlt_ge in H1. apply Nat.leb_le in H1. apply HOR in H1. auto.
Qed.

Lemma ModSucc:
  forall (n: nat),
  (n mod 3%nat = 0%nat -> (S n) mod 3%nat = 1%nat) /\
  (n mod 3%nat = 1%nat -> (S n) mod 3%nat = 2%nat) /\
  (n mod 3%nat = 2%nat -> (S n) mod 3%nat = 0%nat).
Proof.
  intros. split.
  - intros H. rewrite <- Nat.add_1_r. rewrite Nat.add_mod. rewrite H. simpl. reflexivity. auto.
  - split. 
    + intros H. rewrite <- Nat.add_1_r. rewrite Nat.add_mod. rewrite H. simpl. reflexivity. auto.
    + intros H. rewrite <- Nat.add_1_r. rewrite Nat.add_mod. rewrite H. simpl. reflexivity. auto. 
Qed. 

Theorem TwoPositiveLoopAmplifier1:
  forall (Inputs: list nat) (PLP: @PositiveLoop Inputs) (time: nat),
  Qle_bool (Tau (PL_N1 PLP)) (hd 0 (Weights (PL_N1 PLP)))  = true ->
  (Qle_bool (Tau (PL_N1 PLP)) (hd 0 (tl (Weights (PL_N1 PLP)))))  = true ->
  (Qle_bool (Tau (PL_N2 PLP)) (hd 0 (Weights (PL_N2 PLP))))  = true ->
  Pattern (rev Inputs) [0%nat;1%nat;1%nat] 0%nat ->
  (lt 1%nat time) ->
  (lt time (length (Output (PL_N1 PLP)))) ->
  List.nth time (rev (Output (PL_N1 PLP))) 0%nat = 1%nat. (*/\ 
                               List.nth time (rev (Output (PL_N2 PLP))) 0%nat = 1%nat.*)
Proof.
  intros Inputs PLP tp H1 H2 H3 H4 H5 H6.
  destruct tp as [ | tp1].
  - inversion H5.
  - destruct tp1 as [ | tp2].
    + inversion H5. inversion H0.
    + generalize (NextTimeN1TPL Inputs (S tp2) PLP); intro HNTN1.
      generalize (NextTimeN2TPL Inputs tp2 PLP); intro HNTN2.
      generalize (HNTN1 H1 H2 H3); intro HN1. clear HNTN1.
      generalize (HNTN2 H1 H2 H3); intro HN2. clear HNTN2. rewrite Nat.add_1_r in HN2.
      generalize (InOutLength Inputs PLP); intro HIOL. rewrite Nat.add_1_r in HIOL.
      inversion HIOL as [H7 H8]. 
      generalize (ModSucc tp2); intro HA. inversion HA as [HA1 [HA2 HA3]].
      (*generalize (ModSucc (S tp2)); intro HB. inversion HB as [HB1 [HB2 HB3]].*)
      generalize (Module3 tp2); intro HMD.
      destruct ((S tp2) <? length (rev Inputs)) eqn: HK.
      * inversion HMD as [HMD1 | [HMD2 | HMD3]]. 
        { generalize (NextInPatternMod1 (S tp2) (rev Inputs)); intro HE.
          generalize (HA1 HMD1); intro HC. (*generalize (HB2 HC); intro HD.*)
          generalize (HE H4 HK HC); intro HKEY. rewrite Nat.add_1_r in HN1.
          assert (Htemp: List.nth (S tp2) (rev Inputs) 0%nat = 1%nat \/ List.nth (S tp2) (rev (Output (PL_N2 PLP))) 0%nat = 1%nat). { left. auto. }
          apply Nat.ltb_lt in H6. generalize (HN1 Htemp H6); intro HFIN. auto. }
        { generalize (NextInPatternMod2 (S tp2) (rev Inputs)); intro HE.
          generalize (HA2 HMD2); intro HC. (*generalize (HB2 HC); intro HD.*)
          generalize (HE H4 HK HC); intro HKEY. rewrite Nat.add_1_r in HN1.
          assert (Htemp: List.nth (S tp2) (rev Inputs) 0%nat = 1%nat \/ List.nth (S tp2) (rev (Output (PL_N2 PLP))) 0%nat = 1%nat). { left. auto. }
          apply Nat.ltb_lt in H6. generalize (HN1 Htemp H6); intro HFIN. auto. }
        { destruct tp2 as [ | tp3].
          { simpl in HMD3. inversion HMD3. }
          { generalize (NextTimeN1TPL Inputs tp3 PLP); intro HNTN1.
            generalize (HNTN1 H1 H2 H3); intro HN11. clear HNTN1. rewrite Nat.add_1_r in HN11.
            generalize (NextInPatternMod1 tp3 (rev Inputs)); intro HE.
            assert (HT1: (tp3 <? length (rev Inputs)) = true).
            { generalize (Nat.lt_succ_diag_r tp3); intro HX.
              generalize (Nat.lt_succ_diag_r (S tp3)); intro HY.
              generalize (Nat.lt_trans tp3 (S tp3) (S (S tp3))); intro HZ.
              generalize (Nat.lt_trans tp3 (S (S tp3)) (length (rev Inputs))); intro HF.
              generalize (HZ HX HY); intro HXX. apply Nat.ltb_lt in HK.
              generalize (HF HXX HK); intro HS. apply Nat.ltb_lt. auto. }
            assert (HT2 : tp3 mod 3%nat = 1%nat).
            { generalize (Module3 tp3); intro HM. inversion HM as [HM1 | [HM2 | HM3]].
              { rewrite <- Nat.add_1_r in HMD3. rewrite Nat.add_mod in HMD3. rewrite HM1 in HMD3.
                simpl in HMD3. inversion HMD3. auto. }
              { auto. }
              { rewrite <- Nat.add_1_r in HMD3. rewrite Nat.add_mod in HMD3. rewrite HM3 in HMD3.
                simpl in HMD3. inversion HMD3. auto. } }
            generalize (HE H4 HT1 HT2); intro HKEY.
            assert (Htemp: List.nth tp3 (rev Inputs) 0%nat = 1%nat \/ List.nth tp3 (rev (Output (PL_N2 PLP))) 0%nat = 1%nat). { auto. }
            assert (Htx: (S tp3 <? length (Output (PL_N1 PLP))) = true).
            { generalize (Nat.lt_succ_diag_r (S tp3)); intro HX.
              generalize (Nat.lt_succ_diag_r (S (S tp3))); intro HY.
              generalize (Nat.lt_trans (S tp3) (S (S tp3)) (S (S (S tp3)))); intro HZ.
              generalize (Nat.lt_trans (S tp3) (S (S (S tp3))) (length (Output (PL_N1 PLP)))); intro HF.
              generalize (HZ HX HY); intro HXX. generalize (HF HXX H6); intro HS. 
              apply Nat.ltb_lt. auto. }
            generalize (HN11 Htemp Htx); intro HKE.
            assert (Ht: (S (S tp3) <? length (Output (PL_N2 PLP))) = true).
            { generalize (Nat.lt_succ_diag_r (length (rev Inputs))); intro HX.
              generalize (Nat.lt_trans (S (S tp3)) (length (rev Inputs)) (S (length (rev Inputs)))); intro HY.
              apply Nat.ltb_lt in HK. generalize (HY HK HX); intro HZ. apply Nat.ltb_lt.
              apply beq_nat_true_iff in H8. generalize (rev_length (Inputs)); intro HRL.
              rewrite HRL in HZ. rewrite H8 in HZ. auto. }
            generalize (HN2 HKE Ht); intro HAF. rewrite Nat.add_1_r in HN1.
            assert (Hty: List.nth (S (S tp3)) (rev Inputs) 0%nat = 1%nat \/ List.nth (S (S tp3)) (rev (Output (PL_N2 PLP))) 0%nat = 1%nat). { right. auto. }
            apply Nat.ltb_lt in H6. generalize (HN1 Hty H6); intro HFIN. auto. } }
      * apply beq_nat_true_iff in H7. rewrite <- H7 in H6. generalize (rev_length Inputs); intro HRL.
        rewrite <- HRL in H6. apply lt_S_n in H6. apply Nat.ltb_lt in H6. rewrite H6 in HK. inversion HK.
Qed.

Theorem TwoPositiveLoopAmplifier2:
  forall (Inputs: list nat) (PLP: @PositiveLoop Inputs) (time: nat),
  Qle_bool (Tau (PL_N1 PLP)) (hd 0 (Weights (PL_N1 PLP)))  = true ->
  (Qle_bool (Tau (PL_N1 PLP)) (hd 0 (tl (Weights (PL_N1 PLP)))))  = true ->
  (Qle_bool (Tau (PL_N2 PLP)) (hd 0 (Weights (PL_N2 PLP))))  = true ->
  Pattern (rev Inputs) [0%nat;1%nat;1%nat] 0%nat ->
  (lt 2%nat time) ->
  (lt time (length (Output (PL_N2 PLP)))) ->
  List.nth time (rev (Output (PL_N2 PLP))) 0%nat = 1%nat.
Proof.
  intros Inputs PLP tp H1 H2 H3 H4 H5 H6.
  - destruct tp as [ | tp1].
    + inversion H5.
    + destruct tp1 as [ | tp2].
      * inversion H5. inversion H0.
      * destruct tp2 as [ | tp3].
        { inversion H5. inversion H0. inversion H8. }
        { generalize (TwoPositiveLoopAmplifier1 Inputs PLP (S (S tp3))); intro HTPL1.
          generalize (NextTimeN2TPL Inputs (S (S tp3)) PLP); intro HNTN2.
          generalize (InOutLength Inputs PLP); intro HIOL. rewrite Nat.add_1_r in HIOL.
          inversion HIOL as [H7 H8]. apply beq_nat_true_iff in H7.
          apply beq_nat_true_iff in H8. rewrite H7 in H8.
          assert (Hx: (1%nat < S (S tp3))%nat). 
          { apply lt_S_n in H5. auto. }
          assert (Htemp: (S (S tp3) < length (Output (PL_N1 PLP)))%nat).
          { generalize (Nat.lt_succ_diag_r (S (S tp3))); intro HX.
            generalize (Nat.lt_trans (S (S tp3)) (S (S (S tp3))) (length (Output (PL_N2 PLP)))); intro HNLL.
            generalize (HNLL HX H6); intro HY. rewrite <- H8 in HY. auto. }
          generalize (HTPL1 H1 H2 H3 H4 Hx Htemp); intro HKEY. apply Nat.ltb_lt in H6.
          rewrite Nat.add_1_r in HNTN2. generalize (HNTN2 H1 H2 H3 HKEY H6); intro HFIN. auto. }
Qed.

Lemma PlusLessThan:
  forall (n m: nat),
  (lt n m) -> exists p: nat, m = (n + p)%nat.
Proof.
  intros.
  induction m as [ | m'].
  - inversion H.
  - destruct (n <? m') eqn: Ht.
    + apply Nat.ltb_lt in Ht. apply IHm' in Ht.
      destruct Ht as [p H1]. apply eq_S in H1. rewrite <- Nat.add_succ_r in H1.
      exists (S p). auto.
    + apply Nat.ltb_ge in Ht. destruct (beq_nat n m') eqn: Hb.
      * exists 1%nat. apply beq_nat_true_iff in Hb. rewrite Hb. 
        rewrite Nat.add_1_r. reflexivity. 
      * apply lt_n_Sm_le in H. generalize (Nat.le_antisymm n m'); intro HNLAS.
        generalize (HNLAS H Ht); intro HC. apply beq_nat_true_iff in HC.
        rewrite HC in Hb. inversion Hb.
Qed.

Lemma RevBinList: forall (l: list nat),
  Bin_List l -> Bin_List (rev l).
Proof.
  intros. induction l as [ | h t IH].
  - simpl. auto.
  - simpl. generalize (AppendBins (rev t) [h]); intro HAB.
    simpl in H. inversion H as [H1 H2]. apply IH in H2. 
    assert (Ht: Bin_List [h]). { simpl. auto. }
    generalize (HAB H2 Ht); intro HK. auto.
Qed.

Lemma nthAfterSkip: forall (l1 l l2: list nat) (m ind d: nat),
  l = l1 ++ l2 -> ind = (length l1 + m)%nat -> (ind < length l)%nat -> 
  List.nth ind l d = List.nth m l2 d.
Proof.
  induction l1 as [ | h t IH].
  - intros l l2 m ind d H1 H2 H3. simpl in H1. rewrite H1. simpl in H2. rewrite H2. reflexivity.
  - intros l l2 m ind d H1 H2 H3. destruct l as [ | h' t']. 
    + inversion H3.
    + simpl in H1. inversion H1. simpl in H2. destruct ind as [ | n]. 
      * inversion H2. 
      * simpl. simpl in H3. apply lt_S_n in H3. inversion H2.
        generalize (IH t' l2 m n d); intro IHnew. generalize (IHnew H4 H5 H3); intro HK.
        rewrite <- H4. rewrite <- H5. auto.
Qed.

Lemma LengthNZeros: forall (n: nat),
  length (NZeros n) = n.
Proof.
  induction n as [ | n'].
  - simpl. reflexivity.
  - simpl. apply eq_S. auto.
Qed.

Lemma Module3OutputSeries0: 
    forall (Inputs: list nat) (Series: @NeuronSeries Inputs) (time: nat) (m: nat),
    AllDelayers (NeuronList Series) ->
    Pattern (rev Inputs) [0%nat;1%nat;1%nat] 0%nat ->
    time = ((length (NeuronList Series)) + m)%nat ->
    m mod 3%nat = 0%nat ->
    lt time (length (NSOutput Series)) ->
    List.nth time (rev (NSOutput Series)) 0%nat = 0%nat.
Proof.
  intros Inputs Series time m H1 H2 H3 H4 H5.
  generalize (SeriesN Inputs Series); intro HSIS.
  generalize (Pattern011IsBin (rev Inputs)); intro HP011B.
  generalize (HP011B H2); intro HA. generalize (BinOutputGeneral (rev Inputs)); intro HBO.
  apply HBO in HA. generalize (RevBinList (rev Inputs)); intro HRBL. apply HRBL in HA.
  rewrite rev_involutive in HA. generalize (HSIS H1 HA); intro HK.
  remember (NZeros (length (NeuronList Series))) as X.
  generalize (rev_app_distr Inputs X); intro HRAD. rewrite <- HK in HRAD.
  generalize (LengthNZeros (length (NeuronList Series))); intro HLNZ. rewrite <- HeqX in HLNZ.
  generalize (rev_length X); intro HRL. rewrite <- HRL in HLNZ. 
  assert (Ht: time = (length (rev X) + m)%nat).
  { rewrite <- HLNZ in H3. auto. }
  generalize (nthAfterSkip (rev X) (rev (NSOutput Series)) (rev Inputs) m time 0%nat); intro HKEY.
  rewrite <- rev_length in H5. generalize (HKEY HRAD Ht H5); intro HF.
  assert (Htemp: (m < length (rev Inputs))%nat).
  { rewrite H3 in H5. generalize (app_length (rev X) (rev Inputs)); intro HX.
    rewrite <- HRAD in HX. rewrite HX in H5. rewrite <- HLNZ in H5.
    Search lt plus. generalize (plus_lt_reg_l m (length (rev Inputs)) (length (rev X))); intro HPLR.
   apply HPLR in H5. auto. } apply Nat.ltb_lt in Htemp.
  generalize (NextInPatternMod0 m (rev Inputs)); intro HMIP. 
  generalize (HMIP H2 Htemp H4); intro HFIN. rewrite HFIN in HF. auto.
Qed.

Lemma Module3OutputSeries1: 
    forall (Inputs: list nat) (Series: @NeuronSeries Inputs) (time: nat) (m: nat),
    AllDelayers (NeuronList Series) ->
    Pattern (rev Inputs) [0%nat;1%nat;1%nat] 0%nat ->
    time = ((length (NeuronList Series)) + m)%nat ->
    m mod 3%nat = 1%nat ->
    lt time (length (NSOutput Series)) ->
    List.nth time (rev (NSOutput Series)) 0%nat = 1%nat.
Proof.
  intros Inputs Series time m H1 H2 H3 H4 H5.
  generalize (SeriesN Inputs Series); intro HSIS.
  generalize (Pattern011IsBin (rev Inputs)); intro HP011B.
  generalize (HP011B H2); intro HA. generalize (BinOutputGeneral (rev Inputs)); intro HBO.
  apply HBO in HA. generalize (RevBinList (rev Inputs)); intro HRBL. apply HRBL in HA.
  rewrite rev_involutive in HA. generalize (HSIS H1 HA); intro HK.
  remember (NZeros (length (NeuronList Series))) as X.
  generalize (rev_app_distr Inputs X); intro HRAD. rewrite <- HK in HRAD.
  generalize (LengthNZeros (length (NeuronList Series))); intro HLNZ. rewrite <- HeqX in HLNZ.
  generalize (rev_length X); intro HRL. rewrite <- HRL in HLNZ. 
  assert (Ht: time = (length (rev X) + m)%nat).
  { rewrite <- HLNZ in H3. auto. }
  generalize (nthAfterSkip (rev X) (rev (NSOutput Series)) (rev Inputs) m time 0%nat); intro HKEY.
  rewrite <- rev_length in H5. generalize (HKEY HRAD Ht H5); intro HF.
  assert (Htemp: (m < length (rev Inputs))%nat).
  { rewrite H3 in H5. generalize (app_length (rev X) (rev Inputs)); intro HX.
    rewrite <- HRAD in HX. rewrite HX in H5. rewrite <- HLNZ in H5.
    generalize (plus_lt_reg_l m (length (rev Inputs)) (length (rev X))); intro HPLR.
    apply HPLR in H5. auto. } apply Nat.ltb_lt in Htemp.
  generalize (NextInPatternMod1 m (rev Inputs)); intro HMIP. 
  generalize (HMIP H2 Htemp H4); intro HFIN. rewrite HFIN in HF. auto.
Qed.

Lemma Module3OutputSeries2:
    forall (Inputs: list nat) (Series: @NeuronSeries Inputs) (time: nat) (m: nat),
    AllDelayers (NeuronList Series) ->
    Pattern (rev Inputs) [0%nat;1%nat;1%nat] 0%nat ->
    time = ((length (NeuronList Series)) + m)%nat ->
    m mod 3%nat = 2%nat ->
    lt time (length (NSOutput Series)) ->
    List.nth time (rev (NSOutput Series)) 0%nat = 1%nat.
Proof.
  intros Inputs Series time m H1 H2 H3 H4 H5.
  generalize (SeriesN Inputs Series); intro HSIS.
  generalize (Pattern011IsBin (rev Inputs)); intro HP011B.
  generalize (HP011B H2); intro HA. generalize (BinOutputGeneral (rev Inputs)); intro HBO.
  apply HBO in HA. generalize (RevBinList (rev Inputs)); intro HRBL. apply HRBL in HA.
  rewrite rev_involutive in HA. generalize (HSIS H1 HA); intro HK.
  remember (NZeros (length (NeuronList Series))) as X.
  generalize (rev_app_distr Inputs X); intro HRAD. rewrite <- HK in HRAD.
  generalize (LengthNZeros (length (NeuronList Series))); intro HLNZ. rewrite <- HeqX in HLNZ.
  generalize (rev_length X); intro HRL. rewrite <- HRL in HLNZ. 
  assert (Ht: time = (length (rev X) + m)%nat).
  { rewrite <- HLNZ in H3. auto. }
  generalize (nthAfterSkip (rev X) (rev (NSOutput Series)) (rev Inputs) m time 0%nat); intro HKEY.
  rewrite <- rev_length in H5. generalize (HKEY HRAD Ht H5); intro HF.
  assert (Htemp: (m < length (rev Inputs))%nat).
  { rewrite H3 in H5. generalize (app_length (rev X) (rev Inputs)); intro HX.
    rewrite <- HRAD in HX. rewrite HX in H5. rewrite <- HLNZ in H5.
    generalize (plus_lt_reg_l m (length (rev Inputs)) (length (rev X))); intro HPLR.
   apply HPLR in H5. auto. } apply Nat.ltb_lt in Htemp.
  generalize (NextInPatternMod2 m (rev Inputs)); intro HMIP. 
  generalize (HMIP H2 Htemp H4); intro HFIN. rewrite HFIN in HF. auto.
Qed.

Theorem SeriesN_PositiveLoop_Composition1:
   forall (Inputs: list nat) (Series: @NeuronSeries Inputs) (PLP: @PositiveLoop (NSOutput Series)) (time: nat),
   AllDelayers (NeuronList Series) ->
   Pattern (rev Inputs) [0%nat;1%nat;1%nat] 0%nat ->
   Qle_bool (Tau (PL_N1 PLP)) (hd 0 (Weights (PL_N1 PLP)))  = true ->
   Qle_bool (Tau (PL_N1 PLP)) (hd 0 (tl (Weights (PL_N1 PLP))))  = true ->
   Qle_bool (Tau (PL_N2 PLP)) (hd 0 (Weights (PL_N2 PLP)))  = true ->
   (lt ((length (NeuronList Series)) + 1%nat)%nat time) ->
   (lt time (length (Output (PL_N1 PLP)))) ->
   List.nth time (rev (Output (PL_N1 PLP))) 0%nat = 1%nat.
Proof.
  intros Inputs Series PLP tp H1 H2 H3 H4 H5 H6 H7.
  generalize (PlusLessThan (length (NeuronList Series)) tp); intro HPLT. rewrite Nat.add_1_r in H6.
  assert (Ht: (length (NeuronList Series) < tp)%nat).
  { generalize (Nat.lt_succ_diag_r (length (NeuronList Series))); intro HA.
    generalize (Nat.lt_trans (length (NeuronList Series)) (S (length (NeuronList Series))) tp); intro HB.
    generalize (HB HA H6); intro HC. auto. }
  generalize (HPLT Ht); intro HA. destruct HA as [m H8].
  destruct m as [ | n1] eqn: HM.
  - rewrite Nat.add_0_r in H8. rewrite <- H8 in Ht. generalize (Nat.lt_irrefl tp); intro H9.
    unfold not in H9. apply H9 in Ht. inversion Ht.
  - destruct n1 as [ | n2].
    + rewrite H8 in H6. rewrite Nat.add_1_r in H6.
      generalize (Nat.lt_irrefl (S (length (NeuronList Series)))); intro H9.
      unfold not in H9. apply H9 in H6. inversion H6.
    + generalize (Module3 m); intro HMX. inversion HMX as [HM1 | [HM2 | HM3]].
      * rewrite Nat.add_succ_r in H8. remember (length (NeuronList Series) + S n2)%nat as prtp.
        generalize (NextTimeN1TPL (NSOutput Series) prtp PLP); intro HNSSP.
        rewrite Nat.add_1_r in HNSSP. generalize (InOutLength (NSOutput Series) PLP); intro HIOL.
        inversion HIOL as [HI1 HI2]. rewrite Nat.add_succ_r in HI1.
        rewrite Nat.add_0_r in HI1. apply beq_nat_true_iff in HI1. rewrite <- HI1 in H7.
        rewrite H8 in H7. apply lt_S_n in H7.
        assert (Hrm: (S n2) mod 3%nat = 2%nat).
        { generalize (Module3 n2); intro HNA. inversion HNA as [HNA1 | [HNA2 | HNA3]].
          { apply ModSucc in HNA1. apply ModSucc in HNA1. rewrite <- HM in HNA1.
            rewrite HM1 in HNA1. inversion HNA1. }
          { apply ModSucc in HNA2. auto. }
          { apply ModSucc in HNA3. apply ModSucc in HNA3. rewrite <- HM in HNA3.
            rewrite HM1 in HNA3. inversion HNA3. } }
        generalize (Module3OutputSeries2 Inputs Series prtp (S n2)); intro HMOS.
        generalize (HMOS H1 H2 Heqprtp Hrm H7); intro HK.
        assert (Htemp: List.nth prtp (rev (NSOutput Series)) 0%nat = 1%nat \/
                       List.nth prtp (rev (Output (PL_N2 PLP))) 0%nat = 1%nat).
        { left. auto. }
        apply lt_n_S in H7. rewrite HI1 in H7. apply Nat.ltb_lt in H7.
        generalize (HNSSP H3 H4 H5 Htemp H7); intro HKEY. rewrite <- H8 in HKEY. auto.
     * destruct n2 as [ | n3].
      { rewrite HM in HM2. simpl in HM2. inversion HM2. }
      { assert (Hrm: n3 mod 3%nat = 1%nat).
        { generalize (Module3 n3); intro HNA. inversion HNA as [HNA1 | [HNA2 | HNA3]].
          { apply ModSucc in HNA1. apply ModSucc in HNA1. apply ModSucc in HNA1. 
            rewrite <- HM in HNA1. rewrite HM2 in HNA1. inversion HNA1. }
          { auto. }       
          { apply ModSucc in HNA3. apply ModSucc in HNA3. apply ModSucc in HNA3.
            rewrite <- HM in HNA3. rewrite HM2 in HNA3. inversion HNA3. } }
        rewrite Nat.add_succ_r in H8. remember (length (NeuronList Series) + S (S n3))%nat as prtp.
        rewrite Nat.add_succ_r in Heqprtp. remember (length (NeuronList Series) + S n3)%nat as pr2tp.
        rewrite Nat.add_succ_r in Heqpr2tp. remember (length (NeuronList Series) + n3)%nat as pr3tp.
        generalize (NextTimeN1TPL (NSOutput Series) pr3tp PLP); intro HNS1.
        generalize (NextTimeN2TPL (NSOutput Series) pr2tp PLP); intro HNS2.
        rewrite Nat.add_1_r in HNS1. rewrite Nat.add_1_r in HNS2.
        generalize (InOutLength (NSOutput Series) PLP); intro HIOL.
        inversion HIOL as [HI1 HI2]. rewrite H8 in H7. rewrite Heqprtp in H7. rewrite Heqpr2tp in H7.
        rewrite Nat.add_1_r in HI1. rewrite Nat.add_1_r in HI2. apply beq_nat_true_iff in HI1.
        apply beq_nat_true_iff in HI2.
        generalize (Nat.lt_succ_diag_r pr3tp); intro HX1.
        generalize (Nat.lt_succ_diag_r (S pr3tp)); intro HX2.
        generalize (Nat.lt_trans pr3tp (S pr3tp) (S (S pr3tp))); intro HX3.
        generalize (HX3 HX1 HX2); intro HX4. 
        generalize (Nat.lt_succ_diag_r (S (S pr3tp))); intro HX5.
        generalize (Nat.lt_trans pr3tp (S (S pr3tp)) (S (S (S pr3tp)))); intro HX6.
        generalize (HX6 HX4 HX5); intro HX7.
        generalize (Nat.lt_trans pr3tp (S (S (S pr3tp))) (length (Output (PL_N1 PLP)))); intro HX8.
        generalize (HX8 HX7 H7); intro HX9. apply Nat.ltb_lt in HX9.
        generalize (Module3OutputSeries1 Inputs Series pr3tp n3); intro HMOS.
        generalize (Nat.lt_trans (S pr3tp) (S (S pr3tp)) (S (S (S pr3tp)))); intro HX10.
        generalize (HX10 HX2 HX5); intro HX11.
        generalize (Nat.lt_trans (S pr3tp) (S (S (S pr3tp))) (length (Output (PL_N1 PLP)))); intro HX12.
        generalize (HX12 HX11 H7); intro HX13. apply Nat.ltb_lt in HX13.
        rewrite <- HI1 in H7. apply lt_S_n in H7.
        generalize (Nat.lt_trans pr3tp (S (S pr3tp)) (length (NSOutput Series))); intro HX14.
        generalize (HX14 HX4 H7); intro HX15.
        generalize (HMOS H1 H2 Heqpr3tp Hrm HX15); intro HK1.
        assert (HK2: List.nth pr3tp (rev (NSOutput Series)) 0%nat = 1%nat \/
                     List.nth pr3tp (rev (Output (PL_N2 PLP))) 0%nat = 1%nat).
        { left. auto. }
        generalize (HNS1 H3 H4 H5 HK2 HX13); intro HK3. rewrite <- Heqpr2tp in HK3.
        apply lt_n_S in H7. rewrite HI2 in H7. rewrite <- Heqpr2tp in H7. 
        generalize (Nat.lt_succ_diag_r (S pr2tp)); intro HY1.
        generalize (Nat.lt_trans (S pr2tp) (S (S pr2tp)) (length (Output (PL_N2 PLP)))); intro HY2.
        generalize (HY2 HY1 H7); intro HY3. apply Nat.ltb_lt in HY3.
        generalize (HNS2 H3 H4 H5 HK3 HY3); intro HK4. rewrite <- Heqprtp in HK4.
        generalize (NextTimeN1TPL (NSOutput Series) prtp PLP); intro HNSSP.
        rewrite <- HI2 in H7. rewrite HI1 in H7. rewrite <- Heqprtp in H7.
        apply Nat.ltb_lt in H7. rewrite Nat.add_1_r in HNSSP.
        assert (HK5: List.nth prtp (rev (NSOutput Series)) 0%nat = 1%nat \/
                     List.nth prtp (rev (Output (PL_N2 PLP))) 0%nat = 1%nat).
        { right. auto. }
        generalize (HNSSP H3 H4 H5 HK5 H7); intro HKEY. rewrite <- H8 in HKEY. auto. }
    * rewrite Nat.add_succ_r in H8. remember (length (NeuronList Series) + S n2)%nat as prtp.
      generalize (NextTimeN1TPL (NSOutput Series) prtp PLP); intro HNSSP.
      rewrite Nat.add_1_r in HNSSP. generalize (InOutLength (NSOutput Series) PLP); intro HIOL.
      inversion HIOL as [HI1 HI2]. rewrite Nat.add_succ_r in HI1.
      rewrite Nat.add_0_r in HI1. apply beq_nat_true_iff in HI1. rewrite <- HI1 in H7.
      rewrite H8 in H7. apply lt_S_n in H7.
      assert (Hrm: (S n2) mod 3%nat = 1%nat).
      { generalize (Module3 n2); intro HNA. inversion HNA as [HNA1 | [HNA2 | HNA3]].
        { apply ModSucc in HNA1. auto. }        
        { apply ModSucc in HNA2. apply ModSucc in HNA2. rewrite <- HM in HNA2.
          rewrite HM3 in HNA2. inversion HNA2. }
        { apply ModSucc in HNA3. apply ModSucc in HNA3. rewrite <- HM in HNA3.
          rewrite HM3 in HNA3. inversion HNA3. } }
        generalize (Module3OutputSeries1 Inputs Series prtp (S n2)); intro HMOS.
        generalize (HMOS H1 H2 Heqprtp Hrm H7); intro HK.
        assert (Htemp: List.nth prtp (rev (NSOutput Series)) 0%nat = 1%nat \/
                       List.nth prtp (rev (Output (PL_N2 PLP))) 0%nat = 1%nat).
        { left. auto. }
        apply lt_n_S in H7. rewrite HI1 in H7. apply Nat.ltb_lt in H7.
        generalize (HNSSP H3 H4 H5 Htemp H7); intro HKEY. rewrite <- H8 in HKEY. auto.
Qed.
        
Theorem SeriesN_PositiveLoop_Composition2:
   forall (Inputs: list nat) (Series: @NeuronSeries Inputs) (PLP: @PositiveLoop (NSOutput Series)) (time: nat),
   AllDelayers (NeuronList Series) ->
   Pattern (rev Inputs) [0%nat;1%nat;1%nat] 0%nat ->
   Qle_bool (Tau (PL_N1 PLP)) (hd 0 (Weights (PL_N1 PLP)))  = true ->
   Qle_bool (Tau (PL_N1 PLP)) (hd 0 (tl (Weights (PL_N1 PLP))))  = true ->
   Qle_bool (Tau (PL_N2 PLP)) (hd 0 (Weights (PL_N2 PLP)))  = true ->
   (lt ((length (NeuronList Series)) + 2%nat)%nat time) ->
   (lt time (length (Output (PL_N2 PLP)))) ->
   List.nth time (rev (Output (PL_N2 PLP))) 0%nat = 1%nat.
Proof.
  intros Inputs Series PLP tp H1 H2 H3 H4 H5 H6 H7.
  destruct tp as [ | tp1].
  - inversion H6.
  - destruct tp1 as [ | tp2].
    + omega.
    + destruct tp2 as [ | tp3].
      * omega.
      * generalize (SeriesN_PositiveLoop_Composition1 Inputs Series PLP (S (S tp3))); intro HSNPLC.
        rewrite Nat.add_succ_r in H6. apply lt_S_n in H6.
        generalize (Nat.lt_succ_diag_r (S (S tp3))); intro HX1.
        generalize (InOutLength (NSOutput Series) PLP); intro HIOL. rewrite Nat.add_1_r in HIOL.
        inversion HIOL as [HI1 HI2]. apply beq_nat_true_iff in HI1. apply beq_nat_true_iff in HI2.
        rewrite HI1 in HI2. rewrite <- HI2 in H7.
        generalize (Nat.lt_trans (S (S tp3)) (S (S (S tp3))) (length (Output (PL_N1 PLP)))); intro HX2.
        generalize (HX2 HX1 H7); intro HK1.
        generalize (HSNPLC H1 H2 H3 H4 H5 H6 HK1); intro HK2.
        generalize (NextTimeN2TPL (NSOutput Series) (S (S tp3)) PLP); intro HNS.
        rewrite Nat.add_1_r in HNS. rewrite HI2 in H7. apply Nat.ltb_lt in H7.
        generalize (HNS H3 H4 H5 HK2 H7); intro HKEY. auto.
Qed.

Lemma NegativeCurrent:
  forall (Inputs: list (list nat)) (N M: Neuron),
  AllNegative (Weights N) ->
  M = AfterNstepsM (ResetNeuron N) Inputs -> (Current M) <= 0.
Proof.
  induction Inputs as [ | h t IH].
  - intros N M H1 H2. simpl in H2. unfold ResetNeuron in H2. rewrite H2. simpl.
    apply Qle_lteq. right. reflexivity.
  - intros N M H1 H2. simpl in H2.
    remember (AfterNstepsM (ResetNeuron N) t) as X.
    (*remember (AfterNTwoLoopN2 (ResetNeuron M) (ResetNeuron P) t) as Y.*)
    generalize (NextNeuronUnchanged X h); intro HNNX. 
    inversion HNNX as [H3 [H4 H5]]. generalize (IH N X); intro HIH.
    generalize (HIH H1 HeqX); intro Hmain. 
    rewrite H2. simpl. unfold NextPotential.
    assert (HQB: Qle_bool (Tau X) (Current X) = false). 
    { generalize (PosTau X); intro HPTX. rewrite Qlt_bool_iff in HPTX.
      generalize (Qle_lt_trans (Current X) 0 (Tau X)); intro H6.
      generalize (H6 Hmain HPTX); intro Hkey. apply Qlt_not_le in Hkey.
      rewrite <- Qle_bool_not_iff in Hkey. auto. }
      rewrite HQB. generalize (NegativePotential h (Weights X)); intro HNP.
      generalize (UnchangedM (ResetNeuron N) t); intro HUM. rewrite <- HeqX in HUM.
      inversion HUM as [HUM1 [HUM2 HUM3]]. generalize (ResetUnchanged N); intro HRU.
      inversion HRU as [HRU1 [HRU2 HRU3]]. rewrite <- HRU3 in HUM3.
      rewrite HUM3 in H1. apply HNP in H1. generalize (LeakRange X); intro HLR.
      inversion HLR as [HLR1 HLR2]. rewrite Qle_bool_iff in HLR1.
      generalize (Qmult_le_compat_r (Current X) 0 (Leak_Factor X)); intro HQLC.
      generalize (HQLC Hmain HLR1); intro HK1. rewrite Qmult_0_l in HK1.
      rewrite Qmult_comm in HK1.
      generalize (Qplus_le_compat (potential (Weights X) h) 0 (Leak_Factor X * Current X) 0); intro HK2.
      generalize (HK2 H1 HK1); intro HF. rewrite Qplus_0_l in HF. auto.
Qed.

Theorem NegativeWeights: forall (Inputs: list (list nat)) (n: nat) (M N: Neuron),
  (beq_nat (length (Weights N)) n) = true /\
  AllLengthN Inputs n /\
  AllNegative (Weights N) /\
  Eq_Neuron2 M (AfterNstepsM (ResetNeuron N) Inputs) 
  -> ~(In 1%nat (Output M)).
Proof.
  induction Inputs as [ | h t].
  - intros. simpl in H. inversion H as [H1 [H2 [H3 H4]]]. unfold Eq_Neuron2 in H4.
    inversion H4 as [H5 H6]. simpl in H5. rewrite H5. simpl. unfold not.
    intro HX. inversion HX as [HX1 | HX2].
    + inversion HX1.
    + assumption.
  - intros. inversion H as [H1 [H2 [H3 H4]]]. simpl in H4.
    remember (AfterNstepsM (ResetNeuron N) t) as NX.
    (*remember H4 as CopyH4.*)
    simpl in H2. unfold Eq_Neuron2 in H4. inversion H4 as [H5 [H6 [H7 [H8 H9]]]].
    simpl in H5. simpl in H6. unfold not. intros HO. rewrite H5 in HO.
    simpl in HO. generalize (IHt n NX N); intro IH. inversion H2 as [HL1 HL2].
    assert (Hmain: (length (Weights N) =? n) = true /\
                    AllLengthN t n /\
                    AllNegative (Weights N) /\ Eq_Neuron2 NX (AfterNstepsM (ResetNeuron N) t)).
    { split. auto. split. auto. split. auto. rewrite <- HeqNX. unfold Eq_Neuron2.
      split. reflexivity. split. reflexivity. split. reflexivity. split. reflexivity.
      reflexivity. } 
    apply IH in Hmain. inversion HO as [HO1 | HO2].
    + unfold NextOutput in HO1. unfold NextPotential in HO1.
      generalize (NegativeCurrent t N NX); intro HNC.
      generalize (HNC H3 HeqNX); intro HF1.
      assert (Htemp: Qle_bool (Tau NX) (Current NX) = false).
      { generalize (PosTau NX); intro HPT. apply Qlt_bool_iff in HPT.
        generalize (Qle_lt_trans (Current NX) 0 (Tau NX)); intro HQ.
        generalize (HQ HF1 HPT); intro HF2. apply Qlt_not_le in HF2.
        rewrite <- Qle_bool_not_iff in HF2. auto. } rewrite Htemp in HO1.
      generalize (UnchangedM (ResetNeuron N) t); intro Hkey. inversion Hkey as [HK1 [HK2 HK3]].
      generalize (ResetUnchanged N); intro HRU. inversion HRU as [HRU1 [HRU2 HRU3]].
      rewrite <- HeqNX in HK3. rewrite HK3 in HRU3. rewrite HRU3 in H3.
      generalize (NegativePotential h (Weights NX)); intro HNP.
      generalize (HNP H3); intro HF2. generalize (LeakRange NX); intro HLR.
      inversion HLR as [HLR1 HLR2]. apply Qle_bool_iff in HLR1.
      generalize (Qmult_le_compat_r (Current NX) 0 (Leak_Factor NX)); intro HQLC.
      generalize (HQLC HF1 HLR1); intro HF3. rewrite Qmult_0_l in HF3.
      generalize (Qplus_le_compat (potential (Weights NX) h) 0 (Current NX * Leak_Factor NX) 0); intro HQLEC.
      generalize (HQLEC HF2 HF3); intro HF4. rewrite Qplus_0_l in HF4.
      generalize (PosTau NX); intro HPT. apply Qlt_bool_iff in HPT.
      generalize (Qle_lt_trans (potential (Weights NX) h + Current NX * Leak_Factor NX) 0 (Tau NX)); intro HQT.
      generalize (HQT HF4 HPT); intro HF5. apply Qlt_not_le in HF5. 
      apply Qle_bool_not_iff in HF5. rewrite Qmult_comm in HF5. rewrite HF5 in HO1.
      inversion HO1.
    + unfold not in Hmain. apply Hmain in HO2. auto. 
Qed. 
    

Lemma PatternKept: forall (l x p: list nat),
  Pattern (l ++ x) p 0%nat -> Pattern l p 0%nat.
Proof. 
  induction x as [ | h t IH].
  - intros. simpl. simpl in H. rewrite app_nil_r in H. auto.
  - intros. simpl. Admitted.
        
Lemma All1Eq: forall (l1 l2: list nat),
  All1 l1 -> All1 l2 -> (length l1) = (length l2) -> l1 = l2.
Proof.
  induction l1 as [ | h1 t1 IHt1].
  - intros l2 H1 H2 H3. simpl in H3. symmetry in H3. apply length_zero_iff_nil in H3. auto.
  - induction l2 as [ | h2 t2 IHt2].
    + intros H1 H2 H3. inversion H3.
    + Admitted.

Record NegativeLoop {Inputs: list nat} := MakeNegativeLoop {
  NL_N1: Neuron;
  NL_N2: Neuron;
  NinputN1: (beq_nat (length (Weights NL_N1)) 2%nat) = true;
  NinputN2: (beq_nat (length (Weights NL_N2)) 1%nat) = true;
  NL_PW1: 0 < (hd 0 (Weights NL_N1));
  NL_NW2: (hd 0 (tl (Weights NL_N1))) < 0;
  NL_PW3: 0 < (hd 0 (Weights NL_N2));
  NL_Connection1: Eq_Neuron2 NL_N1 (AfterNTwoLoopN1 (ResetNeuron NL_N1) (ResetNeuron NL_N2) Inputs);
  NL_Connection2: Eq_Neuron2 NL_N2 (AfterNTwoLoopN2 (ResetNeuron NL_N1) (ResetNeuron NL_N2) Inputs)
}.

Lemma NegativeLoop00Next10:
  forall (Inputs: list nat) (NLP: @NegativeLoop Inputs) (w1 w2 w3: Q) (time: nat),
  (w1 == (hd 0 (Weights (NL_N1 NLP)))) ->
  (w2 == (hd 0 (tl (Weights (NL_N1 NLP))))) ->
  (w3 == (hd 0 (Weights (NL_N2 NLP)))) ->
  (Qle_bool w1 (Qabs w2)) = true ->
  (Qle_bool (Tau (NL_N1 NLP)) w1) = true ->
  (Qle_bool (Tau (NL_N2 NLP)) w3)  = true ->
  All1 Inputs ->
  List.nth time (rev (Output (NL_N1 NLP))) 1%nat = 0%nat ->
  List.nth time (rev (Output (NL_N2 NLP))) 1%nat = 0%nat ->
  (time + 1) <? length (Output (NL_N1 NLP)) = true ->
  List.nth (time + 1) (rev (Output (NL_N1 NLP))) 0%nat = 1%nat /\
  List.nth (time + 1) (rev (Output (NL_N2 NLP))) 1%nat = 0%nat.
Proof.
  intros Inputs NLP w1 w2 w3 time H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
  split.
  - destruct NLP. simpl in H1. simpl in H2. simpl in H3. simpl in H5.
    simpl in H6. simpl in H8. simpl in H9. simpl in H10. simpl.
    destruct Inputs as [ | h Inp].
    + simpl in NL_Connection3. unfold Eq_Neuron2 in NL_Connection3.
      inversion NL_Connection3 as [H11 H12]. simpl in H11.
      destruct time as [ | t].
      * simpl in H10. rewrite H11 in H10. simpl in H10. inversion H10.
      * simpl in H10. rewrite H11 in H10. simpl in H10. inversion H10.
    + simpl in NL_Connection3. simpl in H7. inversion H7 as [H11 H12].
      apply beq_nat_true_iff in H11. rewrite H11 in NL_Connection3.
      unfold Eq_Neuron2 in NL_Connection3.
      unfold Eq_Neuron2 in NL_Connection4.
      inversion NL_Connection3 as [H13 [H14 [H15 [H16 H17]]]].
      inversion NL_Connection4 as [H18 [H19 [H20 [H21 H22]]]].
      remember (AfterNTwoLoopN1 (ResetNeuron NL_N3) (ResetNeuron NL_N4) Inp) as X.
      remember (AfterNTwoLoopN2 (ResetNeuron NL_N3) (ResetNeuron NL_N4) Inp) as Y.
      (*exists X as (AfterNTwoLoopN1 (ResetNeuron NL_N3) (ResetNeuron NL_N4) Inp))

Lemma NegativeLoop01Next00:
  forall (Inputs: list nat) (NLP: @NegativeLoop Inputs) (w1 w2 w3: Q),
  (w1 == (hd 0 (Weights (NL_N1 NLP)))) ->
  (w2 == (hd 0 (tl (Weights (NL_N1 NLP))))) ->
  (w3 == (hd 0 (Weights (NL_N2 NLP)))) ->
  (Qle_bool w1 (Qabs w2)) = true ->
  (Qle_bool (Tau (NL_N1 NLP)) w1) = true ->
  (Qle_bool (Tau (NL_N2 NLP)) w3)  = true ->
  All1 Inputs -> Pattern (rev (Output (NL_N1 NLP))) [1%nat;1%nat;0%nat;0%nat] 1%nat.
Proof.

Lemma NegativeLoop10Next11:
  forall (Inputs: list nat) (NLP: @NegativeLoop Inputs) (w1 w2 w3: Q),
  (w1 == (hd 0 (Weights (NL_N1 NLP)))) ->
  (w2 == (hd 0 (tl (Weights (NL_N1 NLP))))) ->
  (w3 == (hd 0 (Weights (NL_N2 NLP)))) ->
  (Qle_bool w1 (Qabs w2)) = true ->
  (Qle_bool (Tau (NL_N1 NLP)) w1) = true ->
  (Qle_bool (Tau (NL_N2 NLP)) w3)  = true ->
  All1 Inputs -> Pattern (rev (Output (NL_N1 NLP))) [1%nat;1%nat;0%nat;0%nat] 1%nat.
Proof.

Lemma NegativeLoop11Next10:
  forall (Inputs: list nat) (NLP: @NegativeLoop Inputs) (w1 w2 w3: Q),
  (w1 == (hd 0 (Weights (NL_N1 NLP)))) ->
  (w2 == (hd 0 (tl (Weights (NL_N1 NLP))))) ->
  (w3 == (hd 0 (Weights (NL_N2 NLP)))) ->
  (Qle_bool w1 (Qabs w2)) = true ->
  (Qle_bool (Tau (NL_N1 NLP)) w1) = true ->
  (Qle_bool (Tau (NL_N2 NLP)) w3)  = true ->
  All1 Inputs -> Pattern (rev (Output (NL_N1 NLP))) [1%nat;1%nat;0%nat;0%nat] 1%nat.
Proof.

Theorem NegativeLoopN1OutputPattern1100:
  forall (Inputs: list nat) (NLP: @NegativeLoop Inputs) (w1 w2 w3: Q),
  (w1 == (hd 0 (Weights (NL_N1 NLP)))) ->
  (w2 == (hd 0 (tl (Weights (NL_N1 NLP))))) ->
  (w3 == (hd 0 (Weights (NL_N2 NLP)))) ->
  (Qle_bool w1 (Qabs w2)) = true ->
  (Qle_bool (Tau (NL_N1 NLP)) w1) = true ->
  (Qle_bool (Tau (NL_N2 NLP)) w3)  = true ->
  All1 Inputs -> Pattern (rev (Output (NL_N1 NLP))) [1%nat;1%nat;0%nat;0%nat] 1%nat.
Proof.
  intros Inputs NLP w1 w2 w3.
  destruct NLP. simpl.
  intros H1 H2 H3 H4 H5 H6 H7.
  (*generalize dependent NL_N4.
  generalize dependent NL_N3.
  generalize dependent Inputs.*)
  induction Inputs as [ | h t IHt].
  - intros. simpl in NL_Connection3.
    unfold Eq_Neuron2 in NL_Connection3. inversion NL_Connection3 as [H8 [H9 [H10 [H11 H12]]]].
    simpl in H8. rewrite H8. auto.
  - intros. simpl in NL_Connection3. simpl in H7. inversion H7 as [H8 H9].
    (*simpl in Connection4.*) 
    generalize (beq_natP h 1); intro HBP. apply reflect_iff in HBP. apply HBP in H8.
    rewrite H8 in NL_Connection3. 
    remember (AfterNTwoLoopN1 (ResetNeuron NL_N3) (ResetNeuron NL_N4) t) as NL_N5.
    remember (AfterNTwoLoopN2 (ResetNeuron NL_N3) (ResetNeuron NL_N4) t) as NL_N6.
    apply IHt with (NL_N3 := NL_N5) (NL_N4 := NL_N6) in H9. 
    unfold Eq_Neuron2 in NL_Connection3. inversion NL_Connection3 as [H10 [H11 [H12 [H13 H14]]]].
    unfold NextNeuron in H10. unfold NextOutput in H10. simpl in H10.
    unfold NextPotential in H10.
  intros. Admitted. (*induction Inputs as [ | h t IHt].
  - simpl. generalize (Connection1 NLP); intro HCN1.
    simpl in HCN1. unfold Eq_Neuron2 in HCN1. inversion HCN1 as [H6 [H7 [H8 [H9 H10]]]].
    simpl in H6. rewrite H6. simpl. auto.
  - simpl in H5. generalize (IHt (@NegativeLoop t)); intro HIN.*)

Theorem NegativeLoopN2OutputPattern1100:
  forall (Inputs: list nat) (NLP: @NegativeLoop Inputs) (w1 w2 w3: Q),
  (w1 == (hd 0 (Weights (NL_N1 NLP)))) ->
  (w2 == (hd 0 (tl (Weights (NL_N1 NLP))))) ->
  (w3 == (hd 0 (Weights (NL_N2 NLP)))) ->
  (Qle_bool w1 (Qabs w2)) = true ->
  (Qle_bool (Tau (NL_N1 NLP)) w1) = true ->
  (Qle_bool (Tau (NL_N2 NLP)) w3)  = true ->
  All1 Inputs -> Pattern (rev (Output (NL_N2 NLP))) [1%nat;1%nat;0%nat;0%nat] 2%nat.
Proof.
  Admitted.


Record ContralateralInhibition {Input1 Input2: list nat} := MakeContralaterlInhibition {
  CI_N1: Neuron;
  CI_N2: Neuron;
  CI_NinputN1: (beq_nat (length (Weights CI_N1)) 2%nat) = true;
  CI_NinputN2: (beq_nat (length (Weights CI_N2)) 2%nat) = true;
  InputLengthEq: (length Input1) = (length Input2);
  CI_PW1: 0 < (hd 0 (Weights CI_N1));
  CI_PW2: (hd 0 (tl (Weights CI_N1))) < 0;
  CI_PW3: 0 < (hd 0 (Weights CI_N2));
  CI_PW4: (hd 0 (tl (Weights CI_N2))) < 0;
  CI_Connection1: Eq_Neuron2 CI_N1 (AfterNCIN1 (ResetNeuron CI_N1) (ResetNeuron CI_N2) Input1 Input2);
  CI_Connection2: Eq_Neuron2 CI_N2 (AfterNCIN2 (ResetNeuron CI_N1) (ResetNeuron CI_N2) Input1 Input2)
}.

Theorem CLIN1All0: forall (Input1 Input2: list nat) (CLI: @ContralateralInhibition Input1 Input2) (w1 w2 w3 w4: Q),
   w1 == (hd 0 (Weights (CI_N1 CLI))) ->
   w2 == (hd 0 (tl (Weights (CI_N1 CLI)))) ->
   w3 == (hd 0 (Weights (CI_N2 CLI))) ->
   w4 == (hd 0 (tl (Weights (CI_N2 CLI)))) ->
  (Qle_bool (Tau (CI_N1 CLI)) w1) = true ->  
  (Qle_bool w1 (Qabs w2)) = true ->
  (Qle_bool (Tau (CI_N2 CLI)) w3) = true ->
  (Qle_bool (Qabs w4) w3) = true ->
   All1 Input1 ->
   All1 Input2 -> (All0 (tl (tl (rev (Output (CI_N1 CLI)))))).
Proof.
  Admitted.

Theorem CLIN2All1: forall (Input1 Input2: list nat) (CLI: @ContralateralInhibition Input1 Input2) (w1 w2 w3 w4: Q),
   w1 == (hd 0 (Weights (CI_N1 CLI))) ->
   w2 == (hd 0 (tl (Weights (CI_N1 CLI)))) ->
   w3 == (hd 0 (Weights (CI_N2 CLI))) ->
   w4 == (hd 0 (tl (Weights (CI_N2 CLI)))) ->
  (Qle_bool (Tau (CI_N1 CLI)) w1) = true ->  
  (Qle_bool w1 (Qabs w2)) = true ->
  (Qle_bool (Tau (CI_N2 CLI)) w3) = true ->
  (Qle_bool (Qabs w4) w3) = true ->
   All1 Input1 ->
   All1 Input2 -> (All1 (tl (rev (Output (CI_N2 CLI))))).
Proof.
  induction Input1 as [ | h t IHt]. Admitted.


(*Theorem ContralateralInhibition: forall (N1 N2 M1 M2: Neuron) (Inp1 Inp2: list nat) (w1 w2 w3 w4: Q),
  (beq_nat (length (Weights N1)) 2%nat) = true ->
  (beq_nat (length (Weights N2)) 2%nat) = true ->
   w1 == (hd 0 (Weights N1)) ->
   w2 == (hd 0 (tl (Weights N1))) ->
   w3 == (hd 0 (Weights N2)) ->
   w4 == (hd 0 (tl (Weights N2))) ->
  (Qlt_bool w2 0) = true ->
  (Qlt_bool w4 0) = true ->
  (Qle_bool (Tau N1) (Qabs(w2) - w1)) = true ->
  (Qle_bool (Tau N2) (w3 - Qabs(w4))) = true ->
  (All1 Inp1) ->
  (All1 Inp2) ->
  Eq_Neuron2 M1 (AfterNCIN1 (ResetNeuron N1) (ResetNeuron N2) Inp1 Inp2) ->
  Eq_Neuron2 M2 (AfterNCIN2 (ResetNeuron N1) (ResetNeuron N2) Inp1 Inp2) -> (All1 (tl (Output M2))).*)

(*Theorem Steady_Output: forall (P1 P2: list Q) (N1 N2 M1 M2: Neuron) (Inputs: list nat),
  (beq_nat (length (Weights N1)) 2%nat) = true /\
  (beq_nat (length (Weights N2)) 1%nat) = true /\
  (Qlt_bool 0 (hd 0 (Weights N1)))  = true /\
  (Qlt_bool 0 (hd 0 (tl (Weights N1))))  = true /\
  (Qlt_bool 0 (hd 0 (Weights N2)))  = true /\
  (*AfterNsteps and potential function*)
  (forall (t: nat), (series2values t N1 N2 P1 P2)) ->
  (forall (t: nat), t > 2 -> nth (Output N2) t = 1%nat.*)



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

Fixpoint Bin_List (In: list nat): bool :=
  match In with
  | nil => true
  | h::t => andb (orb (beq_nat h 0%nat) (beq_nat h 1%nat)) (Bin_List t)
end.

Check Qle_bool.

Definition NextPotential (N: Neuron) (Inputs: list nat): Q :=
  if (Qle_bool (Tau N) (Current N))
      then  (potential (Weights N) Inputs)
      else  (potential (Weights N) Inputs) + (Leak_Factor N) * (Current N).

Definition NextOutput (N: Neuron) (Inputs: list nat): nat :=
  if (Qle_bool (Current N) 1)
      then 1%nat
      else 0%nat.

Definition NextNeuron (N: Neuron) (Inputs: list nat): Neuron := MakeNeuron
  (if (Qle_bool (Tau N) (Current N))
      then  [1%nat] ++ (Output N)
      else  [0%nat] ++ (Output N))
  (Weights N)
  (Leak_Factor N)
  (Tau N)
  (if (Qle_bool (Tau N) (Current N))
      then  (potential (Weights N) Inputs)
      else  (potential (Weights N) Inputs) + (Leak_Factor N) * (Current N)).

Definition Delayer_Effect (In: list nat) (Out: list nat): bool :=
  match Out with
  | nil => false
  | h::t => andb (beq_nat h 0%nat) (Eq_List In t)
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

Definition Filter_Effect (Out: list nat): bool :=
  match Out with
  | nil => false
  | h::nil => false
  | h1::h2::t => (andb (andb (beq_nat h1 0%nat) (beq_nat h2 0%nat)) (Consecutive Out 1%nat))
end.

Print Visibility.

Fixpoint WeightInRange (Weights: list Q): bool :=
  match Weights with
  | nil => true
  | h::t => andb (Qle_bool h 1) (Qle_bool (-(1)) h)
end.

Definition ResetNeuron (N: Neuron): Neuron := MakeNeuron
  (nil)  
  (Weights N)
  (Leak_Factor N)
  (Tau N)
  (0).

Hypothesis Output_Bin: forall N: Neuron, (Bin_List (Output N) = true).
Hypothesis LeakRange: forall N: Neuron, (andb (Qle_bool (Leak_Factor N) 1) (Qle_bool 0 (Leak_Factor N)) = true).
Hypothesis PosTau: forall N: Neuron, (Qle_bool 0 (Tau N) = true).
Hypothesis WRange: forall N: Neuron, (WeightInRange (Weights N)) = true.


Fixpoint ProduceNoutputs (N: Neuron) (In: list nat): list nat :=
  match In with
  | nil => [0%nat]
  | h::t => ProduceNoutputs
              (MakeNeuron
              ((Output N) ++ [NextOutput N [h]])
              (Weights N)
              (Leak_Factor N)
              (Tau N)
              (NextPotential N [h])) t
end.

Fixpoint AfterNsteps (N: Neuron) (In: list nat): Neuron :=
  match In with
  | nil => MakeNeuron
           ([0%nat])
           (Weights N)
           (Leak_Factor N)
           (Tau N)
           (0)
  | h::t => AfterNsteps
              (MakeNeuron
              ((Output N) ++ [NextOutput N [h]])
              (Weights N)
              (Leak_Factor N)
              (Tau N)
              (NextPotential N [h])) t 
end.

Print QArith.
SearchAbout eqb.

Check eqb.
(*Lemma Part_Equal: forall x y: Q, x == y -> (Qnum x) =? (Qnum y) /\ (Qden x) =? (Qden y).
Lemma Eq_helper1: forall x y: Q, Qeq_bool x y = true <-> x == y.
Proof.
  intros. split.
  - unfold Qeq_bool. unfold Zeq_bool.
    destruct (Qnum x).
    + destruct (Qnum y).
      * simpl. intros H.
Check list_eq_dec.*)
(*(list_eq_dec Q Qeq_dec (Weights N) (Weights M))*)
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
       
(** [] *)

(** The advantage of [reflect] over the normal "if and only if"
    connective is that, by destructing a hypothesis or lemma of the
    form [reflect P b], we can perform case analysis on [b] while at
    the same time generating appropriate hypothesis in the two
    branches ([P] in the first subgoal and [~ P] in the second).

    To use [reflect] to produce a better proof of
    [filter_not_empty_In], we begin by recasting the
    [beq_nat_iff_true] lemma into a more convenient form in terms of
    [reflect]: *)

Lemma beq_natP : forall n m, reflect (n = m) (beq_nat n m).
Proof.
  intros n m.
  apply iff_reflect. rewrite beq_nat_true_iff. reflexivity.
Qed.

(*Lemma Equality_list: forall (l1:list nat) (l2: list nat),
  (Eq_List l1 l2) = true -> l1 = l2.
Proof.
  intros l1 l2 H.
  induction l1 as [|h l].
  - destruct l2 as [|h' l'].
    + auto.
    + simpl in H. inversion H.
  - destruct l2 as [|h' l'].
    + simpl in H. inversion H.
    + unfold Eq_List in H.
      destruct (beq_nat h h') eqn: H1.
      * apply beq_nat_true_iff in H1. rewrite H1. simpl in H.*)   
  

(*Theorem Property1: forall (N: Neuron) (M: Neuron) (Inputs: list nat),
  (beq_nat (length (Weights N)) 1%nat) = true /\
  (beq_nat (length (Weights M)) 1%nat) = true /\
  (Eq_Neuron M (AfterNsteps (ResetNeuron N) Inputs) = true) /\
  (Bin_List Inputs = true)                        -> (Delayer_Effect Inputs (Output M)) = true \/
                                                 (Filter_Effect (Output M)) = true.
Proof.
  intros N M Inputs [H1 [H2 [H3 H4]]].
  assert (exists l: list nat, l = (Output M)).
  { exists (Output M). auto. }
  destruct H as [l h].
  destruct Inputs as [|h1 l1] eqn: H5.
  - simpl in H3. unfold Eq_Neuron in H3. simpl in H3. 
    rewrite H1'. left. simpl. reflexivity.
  - induction (Output M) as [|h2 l2].
    + simpl in H3. unfold Eq_Neuron2 in H3. unfold ResetNeuron in H3. unfold NextOutput in H3.
      unfold AfterNsteps in H3. simpl in H3.
      simpl in H3. 
      unfold Eq_List in H3. inversion H3.
    + destruct l2 as [|h' l'].
      * left. rewrite <- h. simpl. simpl in H3.
        apply Neuron_Equality in H3. simpl in H3. inversion H3 as [ H1' [H2' [H3' [H4' H5']]]].
        
        unfold Eq_Neuron in H3. simpl in H3. rewrite <- h in H3. 
        unfold Eq_List in H3. 
        simpl in H3.*)

Lemma Not_nill_Output: forall (N: Neuron) (In: list nat),
  Output (AfterNsteps N In) <> nil.
Proof.
  intros.
  induction In as [|h l].
  - simpl. intros H. inversion H.
  - unfold AfterNsteps.
    unfold NextOutput. 
    simpl. Admitted.

Lemma Unchanged: forall (N: Neuron) (Inputs: list nat),
  (Leak_Factor N) == Leak_Factor (AfterNsteps N Inputs) /\ 
  (Tau N) == (Tau (AfterNsteps N Inputs)) /\
  (Weights N) = (Weights (AfterNsteps N Inputs)).
  Admitted.

Lemma OutputChange: forall (N: Neuron) (Inputs: list nat),
  Output (AfterNsteps N Inputs) = ProduceNoutputs N Inputs.
Proof.
  intros. 
  induction Inputs as [|h l].
  - simpl. reflexivity.
  - simpl. Admitted.

Theorem Property1: forall (N: Neuron) (M: Neuron) (Inputs: list nat),
  (beq_nat (length (Weights N)) 1%nat) = true /\
  (beq_nat (length (Weights M)) 1%nat) = true /\
  Eq_Neuron2 M (AfterNsteps (ResetNeuron N) Inputs) /\
  (Bin_List Inputs = true)                        -> (Delayer_Effect Inputs (Output M)) = true \/
                                                 (Filter_Effect (Output M)) = true.
Proof.
  intros N M Inputs [H1 [H2 [H3 H4]]].
  (*assert (exists l: list nat, l = (Output M)).
  { exists (Output M). auto. }
  destruct H as [l h].*)
  destruct Inputs as [|h1 l1] eqn: H5.
  (*Focus 2.*)
  - simpl in H3. unfold Eq_Neuron2 in H3. simpl in H3. inversion H3 as [ H1' [H2' [H3' [H4' H5']]]].
    rewrite H1'. left. simpl. reflexivity.
  - (*assert (exists l:list nat, l = (Output M)).
      { generalize dependent M. exists (Output M). auto. }
      elim H.*)
      
      induction (Output M) as [|h2 l2] eqn: H0.
    + simpl in H3. unfold Eq_Neuron2 in H3. inversion H3 as [ H1' [H2' [H3' [H4' H5']]]]. 
      rewrite -> H0 in H1'. symmetry in H1'. apply Not_nill_Output in H1'. inversion H1'.
    + simpl in H3. unfold Eq_Neuron2 in H3. inversion H3 as [ H1' [H2' [H3' [H4' H5']]]].
      rewrite -> OutputChange in H1'. unfold ProduceNoutputs in H1'. 
      unfold AfterNsteps in H3. simpl in H3.
      simpl in H3. 
      unfold Eq_List in H3. inversion H3.
    + destruct l2 as [|h' l'].
      * left. rewrite <- h. simpl. simpl in H3.
        apply Neuron_Equality in H3. simpl in H3. inversion H3 as [ H1' [H2' [H3' [H4' H5']]]].
        
        unfold Eq_Neuron in H3. simpl in H3. rewrite <- h in H3. 
        unfold Eq_List in H3. 
        simpl in H3.


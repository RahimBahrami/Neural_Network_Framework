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

Fixpoint Bin_List (In: list nat): Prop :=
  match In with
  | nil => True
  | h::t => (orb (beq_nat h 0%nat) (beq_nat h 1%nat)) = true /\ (Bin_List t)
end.

Check Qle_bool.

Definition NextPotential (N: Neuron) (Inputs: list nat): Q :=
  if (Qle_bool (Tau N) (Current N))
      then  (potential (Weights N) Inputs)
      else  (potential (Weights N) Inputs) + (Leak_Factor N) * (Current N).

Definition NextOutput (N: Neuron) (Inputs: list nat) : nat :=
  if (Qle_bool (Tau N) (NextPotential N Inputs))
      then 1%nat
      else 0%nat.

Definition NextNeuron (N: Neuron) (Inputs: list nat): Neuron := MakeNeuron
  ((NextOutput N Inputs)::(Output N))
  (Weights N)
  (Leak_Factor N)
  (Tau N)
  (NextPotential N Inputs).

Compute NextOutput (MakeNeuron ([0%nat]) ([Qmake 5 10]) (Qmake 1 10) (Qmake 3 10) (0)) [1%nat].
Compute NextNeuron (MakeNeuron ([0%nat]) ([Qmake 5 10]) (Qmake 1 10) (Qmake 3 10) (Qmake 5 10)) [1%nat].

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

Print Visibility.

Fixpoint WeightInRange (Weights: list Q): bool :=
  match Weights with
  | nil => true
  | h::t => andb (Qle_bool h 1) (Qle_bool (-(1)) h)
end.

Definition ResetNeuron (N: Neuron): Neuron := MakeNeuron
  ([0%nat])  
  (Weights N)
  (Leak_Factor N)
  (Tau N)
  (0).


Definition Qlt_bool (a b: Q): bool :=
  andb (Qle_bool a b) (negb (Qeq_bool b a)).

Print QArith_base.
Compute MakeNeuron (nil) ([Qmake 5 10]) (Qmake 1 10) (Qmake 3 10) (0).
Compute Output (NextNeuron (MakeNeuron (nil) ([Qmake 5 10]) (Qmake 1 10) (Qmake 3 10) (0)) [1%nat]). 

Hypothesis Output_Bin: forall N: Neuron, Bin_List (Output N).
Hypothesis LeakRange: forall N: Neuron, Qle_bool 0 (Leak_Factor N) = true /\ Qle_bool (Leak_Factor N) 1 = true .
Hypothesis PosTau: forall N: Neuron, Qlt_bool 0 (Tau N) = true.
Hypothesis WRange: forall N: Neuron, (WeightInRange (Weights N)) = true.

(*Lemma PosTau_bool: forall N: Neuron,*)

Fixpoint ProduceNoutputs (N: Neuron) (In: list nat): list nat :=
  match In with
  | nil => [0%nat]
  | h::t => ProduceNoutputs
              (MakeNeuron
              ((Output N) ++ [NextOutput N t])
              (Weights N)
              (Leak_Factor N)
              (Tau N)
              (NextPotential N [h])) t
end.

Fixpoint AfterNsteps (N: Neuron) (In: list nat): Neuron :=
  match In with
  | nil => N
  | h::t => NextNeuron (AfterNsteps N t) [h]
end.

Compute (AfterNsteps (MakeNeuron ([0%nat]) ([Qmake 5 10]) (Qmake 1 10) (Qmake 3 10) (0)) [1%nat; 1%nat]).
Example Test_After:
  Output (AfterNsteps (MakeNeuron ([0%nat]) ([Qmake 5 10]) (Qmake 1 10) (Qmake 3 10) (0)) [1%nat]) = [1%nat;0%nat].
Proof.
  simpl. 
  unfold NextOutput. simpl. reflexivity.
Qed.

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

Lemma LengthZero: forall (l: list Q),
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

Lemma ListForm: forall (l: list Q),
  (beq_nat (length l) 1%nat) = true -> exists hq:Q, l = hq::nil.
Proof.
  intros. destruct l as [|h t].
  - simpl in H. inversion H.
  - simpl in H. apply LengthZero in H. rewrite H. exists h. reflexivity.
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

Lemma Delayer_Property: forall (Inputs: list nat) (N M: Neuron),
  (beq_nat (length (Weights N)) 1%nat) = true /\
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
  Inputs <> nil -> (Filter_Effect (Output M)).
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

Theorem Property1: forall (Inputs: list nat) (N: Neuron) (M: Neuron),
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

Theorem Series2: forall (Inputs: list nat) (N1 N2 N3: Neuron),
  (beq_nat (length (Weights N1)) 1%nat) = true /\
  Eq_Neuron2 N2 (AfterNsteps (ResetNeuron N1) Inputs) /\
  Eq_Neuron2 N3 (AfterNsteps N2 (Output N2)) /\
  Bin_List Inputs /\ 
  Qle_bool (Tau N1) (hd 0 (Weights N1)) = true /\
  Qle_bool (Tau N2) (hd 0 (Weights N2)) = true
    -> Output N3 = Inputs ++ [0%nat; 0%nat].
Proof.
  intros. inversion H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
  generalize (Delayer_Property Inputs N1 N2); intro HDI.
  assert (H': (length (Weights N1) =? 1) = true /\
              Eq_Neuron2 N2 (AfterNsteps (ResetNeuron N1) Inputs) /\
              Bin_List Inputs /\ 
              Qle_bool (Tau N1) (hd 0 (Weights N1)) = true).
  { split; auto. } apply HDI in H'. clear H'.
  generalize (Delayer_Property (Output N2) N2 N3); intro HDO.
  assert (H': (length (Weights N2) =? 1) = true /\
              Eq_Neuron2 N3 (AfterNsteps (ResetNeuron N2) (Output N2)) /\
              Bin_List Inputs /\ Qle_bool (Tau N3) (hd 0 (Weights N3)) = true).
  { split; try tauto. Admitted. (*} apply HDO in H'.
  rewrite H5 in H6. Admitted.

Theorem DecreaseNones: forall (N1 N2 N3: Neuron) (Inputs: list nat),
  (beq_nat (length (Weights N)) 1%nat) = true /\
  Eq_Neuron2 N3 (AfterNsteps (ResetNeuron N2) Inputs) /\
  Bin_List Inputs /\ 
   ->*) 
Theorem NegativeWeight: forall (M N: Neuron) (Inputs: list nat),
  (beq_nat (length (Weights N)) 1%nat) = true /\
  Qlt_bool (hd 0 (Weights N)) 0  = true /\
  Eq_Neuron2 M (AfterNsteps (ResetNeuron N) Inputs) (*/\ 
  Out = Output M*) -> ~(In 1%nat (Output M)).
Proof.
  intro M. induction (Output M) as [|h t].
  (*Have variable M as the first variable and do intro M and induction on Output M*)
  - intros. intros H'. unfold In in H'. apply H'.
  - intros N Inputs H. unfold not. inversion H as [H1 [H2 H3]]. unfold Eq_Neuron2 in H3.
    inversion H3 as [ H1' [H2' [H3' [H4' H5']]]]. simpl in H'. 

Theorem SeriesN: forall (Inputs: list nat) (NeuronList: list Neuron),
  forall 

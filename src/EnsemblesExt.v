Require Import
  Coq.Classes.Morphisms
  Coq.Program.Program
  Coq.Unicode.Utf8
  Coq.Sets.Finite_sets
  Coq.Sets.Ensembles.

Require Coq.Sets.Finite_sets_facts.
Require Coq.Sets.Powerset_facts.
Require Coq.Logic.Classical_Prop.

Generalizable All Variables.

Definition first {A B C} (f : A -> C) (p : A * B) : C * B :=
  (f (fst p), snd p).

Definition second {A B C} (f : B -> C) (p : A * B) : A * C :=
  (fst p, f (snd p)).

Ltac inv H := inversion H; subst; clear H.

Tactic Notation "by" tactic(H) :=
  H; first [ tauto
           | discriminate
           | auto
           | congruence
           | eauto
           | intuition
           | firstorder ].

Notation "'IF' c1 'then' c2 'else' c3" := (c1 /\ c2 \/ ~ c1 /\ c3)
  (at level 200, right associativity).

Ltac breakdown :=
  match goal with
  | [ H : IF _ then _ else _ |- _ ] => destruct H
  | [ H : _ /\ _             |- _ ] => destruct H
  | [ H : _ \/ _             |- _ ] => destruct H
  | [ H : _ * _              |- _ ] => destruct H
  | [ H : exists _, _        |- _ ] => destruct H
  | [ H : @sig _ _           |- _ ] => destruct H
  | [ H : @sig2 _ _ _        |- _ ] => destruct H
  | [ H : @sigT _ _          |- _ ] => destruct H
  | [ H : @sigT2 _ _ _       |- _ ] => destruct H
  | [ H : bool               |- _ ] => destruct H
  | [ H : option _           |- _ ] => destruct H
  | [ H : sum _ _            |- _ ] => destruct H
  | [ H : sumor _ _          |- _ ] => destruct H
  | [ H : sumbool _ _        |- _ ] => destruct H

  | [ H : forall x, Some ?X = Some x -> _  |- _ ] => specialize (H X eq_refl)
  | [ H : forall x y, Some (?X, ?Y) = Some (x, y) -> _  |- _ ] =>
    specialize (H X Y eq_refl)

  | [ H1 : ?X = true, H2 : ?X = false |- _ ] => rewrite H1 in H2; discriminate
  end.

Infix    "∪"     := (Union _)        (at level 85, right associativity).
Notation "∅"     := (Empty_set _)    (at level 0, no associativity).
Notation "p ∈ q" := (In _ q p)       (at level 88, no associativity).
Notation "p ⊆ q" := (Included _ p q) (at level 89, no associativity).
Infix    "∩"     := (Intersection _) (at level 80, right associativity).

Program Instance Same_set_Equivalence {A} : Equivalence (@Same_set A).
Next Obligation.
  intro x.
  constructor; intros y H; exact H.
Qed.
Obligation 2.
  intros x y H.
  destruct H.
  split; trivial.
Qed.
Obligation 3.
  intros x y z H1 H2.
  destruct H1, H2.
  split; trivial.
    intros w H3.
    apply H1.
    apply H.
    exact H3.
  intros w H3.
  apply H0.
  apply H2.
  exact H3.
Qed.

Add Parametric Relation {A : Type} : (Ensemble A) (Same_set A)
  reflexivity  proved by (@Equivalence_Reflexive  _ _ Same_set_Equivalence)
  symmetry     proved by (@Equivalence_Symmetric  _ _ Same_set_Equivalence)
  transitivity proved by (@Equivalence_Transitive _ _ Same_set_Equivalence)
  as Same_set_relation.

Program Instance Same_set_equiv A :
  Proper (Same_set A ==> Same_set A ==> Basics.impl) (Same_set A).
Next Obligation.
  repeat intro.
  destruct H, H0, H1.
  split; intros z H5.
    apply H0, H1, H2, H5.
  apply H, H4, H3, H5.
Qed.

Program Instance Same_set_equiv' A :
  Proper (Same_set A ==> Same_set A ==> Basics.flip Basics.impl) (Same_set A).
Next Obligation.
  repeat intro.
  destruct H, H0, H1.
  split; intros z H5.
    apply H3, H1, H, H5.
  apply H2, H4, H0, H5.
Qed.

Program Instance Singleton_Same_set A :
  Proper (eq ==> Same_set A) (Singleton A).
Next Obligation. intros; reflexivity. Qed.

Program Instance In_Same_set A :
  Proper (Same_set A ==> Same_set A) (In A).
Next Obligation.
  repeat intro.
  exact H.
Qed.

Program Instance In_Same_set_eq A :
  Proper (Same_set A ==> eq ==> Basics.impl) (In A).
Next Obligation.
  repeat intro; subst.
  destruct H.
  now apply H.
Qed.

Program Instance In_Same_set_eq' A :
  Proper (Same_set A ==> eq ==> Basics.flip Basics.impl) (In A).
Next Obligation.
  repeat intro; subst.
  destruct H.
  now apply H0.
Qed.

Program Instance In_Same_set_eq'' A :
  Proper (Same_set A --> eq ==> Basics.impl) (In A).
Next Obligation.
  repeat intro; subst.
  destruct H.
  now apply H0.
Qed.

Program Instance In_Same_set_eq''' A :
  Proper (Same_set A --> eq ==> Basics.flip Basics.impl) (In A).
Next Obligation.
  repeat intro; subst.
  destruct H.
  now apply H.
Qed.

Program Instance Union_Same_set A :
  Proper (Same_set A ==> Same_set A ==> Same_set A) (Union A).
Next Obligation.
  repeat intro.
  destruct H, H0.
  split; intros z H3;
  inversion H3; subst; clear H3.
  - apply Union_introl.
    apply H, H4.
  - apply Union_intror.
    apply H0, H4.
  - apply Union_introl.
    apply H1, H4.
  - apply Union_intror.
    apply H2, H4.
Qed.

Program Instance Add_Same_set A :
  Proper (Same_set A ==> eq ==> Same_set A) (Add A).
Next Obligation.
  unfold Add; repeat intro.
  subst.
  rewrite H.
  reflexivity.
Qed.

Program Instance Setminus_Same_set A :
  Proper (Same_set A ==> Same_set A ==> Same_set A) (Setminus A).
Next Obligation.
  repeat intro.
  destruct H, H0.
  split; intros z H3;
  inversion H3; subst; clear H3.
    split.
      apply H, H4.
    unfold not; intros.
    contradiction H5.
    apply H2, H3.
  split.
    apply H1, H4.
  unfold not; intros.
  contradiction H5.
  apply H0, H3.
Qed.

Program Instance Subtract_Same_set A :
  Proper (Same_set A ==> eq ==> Same_set A) (Subtract A).
Next Obligation.
  unfold Subtract; repeat intro.
  subst.
  rewrite H.
  reflexivity.
Qed.

Program Instance Included_Same_set A :
  Proper (Same_set A ==> Same_set A ==> Basics.impl) (Included A).
Next Obligation.
  unfold Included; repeat intro.
  rewrite <- H0.
  rewrite <- H in H2.
  exact (H1 _ H2).
Qed.

Program Instance Included_Same_set_subrelation A :
  subrelation (@Same_set A) (@Included A).
Next Obligation. repeat intro; now apply H. Qed.

Program Instance Finite_Proper A :
  Proper (Same_set A ==> impl) (Finite A).
Next Obligation.
  intros ????.
  eapply Finite_sets_facts.Finite_downward_closed; eauto with sets.
  intros ? H1.
  rewrite <- H in H1.
  assumption.
Qed.

Program Instance Finite_Proper_flip A :
  Proper (Same_set A --> flip impl) (Finite A).
Next Obligation.
  intros ????.
  eapply Finite_sets_facts.Finite_downward_closed; eauto with sets.
  intros ? H1.
  rewrite H in H1.
  assumption.
Qed.

Definition Map_set {A B} (f : A -> B) (r : Ensemble A) : Ensemble B :=
  fun b => exists a : A, In _ r a /\ b = f a.

Lemma Map_set_left_identity {A} (r : Ensemble A) : Same_set A r (Map_set id r).
Proof.
  unfold Map_set; split; intros.
    eexists; intuition.
    assumption.
  intros ??.
  do 2 destruct H.
  unfold id in H0.
  congruence.
Qed.

Lemma Map_set_right_identity {A} (r : Ensemble A) : Same_set A (Map_set id r) r.
Proof.
  unfold Map_set; split; intros.
    intros ??.
    do 2 destruct H.
    unfold id in H0.
    congruence.
  eexists; intuition.
  assumption.
Qed.

Lemma Map_set_composition {A B C} (r : Ensemble A) :
  forall (f : B -> C) (g : A -> B),
   Same_set C (Map_set (fun x => f (g x)) r) (Map_set f (Map_set g r)).
Proof.
  unfold Map_set; split; intros; intros ??.
    do 2 destruct H; subst.
    exists (g x0); simpl in *.
    split; trivial.
    exists x0; simpl.
    intuition.
  do 2 destruct H; subst.
  do 2 destruct H; simpl in *; subst.
  exists x; simpl in *.
  intuition.
Qed.

Definition Product {T U} (X : Ensemble T) (Y : Ensemble U) : Ensemble (T * U) :=
  fun p => In T X (fst p) /\ In U Y (snd p).

Lemma Product_Add_left : forall T U (X : Ensemble T) (Y : Ensemble U) x,
  Same_set _ (Product (Add T X x) Y)
             (Union _ (Product (Singleton _ x) Y) (Product X Y)).
Proof.
  unfold Product; split; intros;
  intros ??; unfold Ensembles.In in *;
  destruct H;
  destruct x0; simpl in *;
  destruct H.
  - right; constructor; simpl; auto.
  - left; constructor; simpl; auto.
  - simpl in *; intuition; right; intuition.
  - simpl in *; intuition; left; intuition.
Qed.

Lemma Product_Add_right : forall T (X : Ensemble T) U (Y : Ensemble U) y,
  Same_set _ (Product X (Add U Y y))
             (Union _ (Product X Y) (Product X (Singleton _ y))).
Proof.
  unfold Product; split; intros;
  intros ??; unfold Ensembles.In in *;
  destruct H;
  destruct x; simpl in *.
  - destruct H0.
    + left; constructor; simpl; auto.
    + right; constructor; simpl; auto.
  - destruct H. intuition; left; intuition.
  - destruct H. intuition; right; intuition.
Qed.

Lemma Product_Empty_set_left : forall T U (X : Ensemble U),
  Same_set _ (Product (Empty_set T) X) (Empty_set (T * U)).
Proof.
  unfold Product; split; intros;
  intros ??; unfold Ensembles.In in *.
  destruct H;
  destruct x; simpl in *;
  destruct H.
  destruct H.
Qed.

Lemma Product_Empty_set_right : forall T (X : Ensemble T) U,
  Same_set _ (Product X (Empty_set U)) (Empty_set (T * U)).
Proof.
  unfold Product; split; intros;
  intros ??; unfold Ensembles.In in *.
  destruct H;
  destruct x; simpl in *.
  destruct H0.
  destruct H.
Qed.

Lemma Product_Singleton_Singleton : forall T U x y,
  Same_set _ (Product (Singleton T x) (Singleton U y))
             (Singleton (T * U) (x, y)).
Proof.
  unfold Product; split; intros;
  intros ??; unfold Ensembles.In in *;
  destruct H.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    rewrite <- surjective_pairing.
    constructor.
  simpl.
  intuition.
Qed.

Section TupleEnsemble.

Variables A B : Type.

Definition EMap := Ensemble (A * B).

Definition Empty : EMap := Empty_set _.

Definition Single (a : A) (b : B) : EMap := Singleton _ (a, b).

Definition Lookup (a : A) (b : B) (r : EMap) := In _ r (a, b).

Definition Functional (r : EMap) :=
  forall addr blk1, Lookup addr blk1 r ->
  forall blk2, Lookup addr blk2 r -> blk1 = blk2.

Definition Same (x y : EMap) : Prop :=
  forall a b, Lookup a b x <-> Lookup a b y.

Global Program Instance Same_Equivalence : Equivalence Same.
Next Obligation.
  constructor; auto.
Qed.
Obligation 2.
  constructor; apply H; auto.
Qed.
Obligation 3.
  constructor; intros.
    apply H0, H; auto.
  apply H, H0; auto.
Qed.

Lemma Same_Same_set : forall x y, Same x y <-> Same_set _ x y.
Proof.
  unfold Same, Lookup.
  split; intros.
    split; intros;
    intros ? H0;
    destruct x0;
    apply H; assumption.
  split; intros;
  apply H; assumption.
Qed.

Global Program Instance Lookup_Proper :
  Proper (eq ==> eq ==> Same ==> Basics.impl) Lookup.
Next Obligation. repeat intro; subst; now apply H1. Qed.

Global Program Instance Lookup_Proper_flip :
  Proper (eq ==> eq ==> Same --> Basics.impl) Lookup.
Next Obligation. repeat intro; subst; now apply H1. Qed.

Definition Member (a : A) (r : EMap) := exists b, Lookup a b r.

Definition Member_dec (a : A) (r : EMap) : Member a r \/ ~ Member a r.
Proof.
  unfold Member.
  elim (Classical_Prop.classic (exists b, Lookup a b r));
  intuition.
Qed.

Definition Insert (a : A) (b : B) (r : EMap)
           (H : forall b' : B, ~ Lookup a b' r) : EMap :=
  Add _ r (a, b).

Definition Remove (a : A) (r : EMap) : EMap :=
  Setminus _ r (fun p => fst p = a).

Program Definition Update (a : A) (b : B) (r : EMap) :
  EMap := Insert a b (Remove a r) _.
Next Obligation. firstorder. Qed.

Definition Map {C} (f : A -> B -> C) (r : EMap) : Ensemble (A * C) :=
  fun p => exists b : B, Lookup (fst p) b r /\ snd p = f (fst p) b.

Definition Relate {C D} (f : A -> B -> C -> D -> Prop) (r : EMap) :
  Ensemble (C * D) :=
  fun p => exists k' e', Lookup k' e' r /\ f k' e' (fst p) (snd p).

Lemma Map_left_identity : forall r, Same r (Map (fun _ x => x) r).
Proof.
  unfold Map; split; intros.
    eexists b.
    intuition.
  do 2 destruct H.
  simpl in *.
  rewrite H0.
  assumption.
Qed.

Lemma Map_right_identity : forall r, Same (Map (fun _ x => x) r) r.
Proof.
  unfold Map; split; intros.
    do 2 destruct H.
    simpl in *.
    rewrite H0.
    assumption.
  eexists b.
  intuition.
Qed.

Lemma Map_composition : forall f g r,
  Same (Map (fun k e => f k (g k e)) r) (Map f (Map g r)).
Proof.
  unfold Map; split; intros.
    destruct H.
    destruct H; simpl in *.
    subst.
    exists (g a x); simpl in *.
    split; trivial.
    exists x; simpl.
    intuition.
  destruct H.
  destruct H; simpl in *.
  subst.
  destruct H; simpl in *.
  exists x0; simpl in *.
  destruct H.
  intuition.
  rewrite <- H0.
  reflexivity.
Qed.

Definition Move (a a' : A) (r : EMap) : EMap :=
  Relate (fun k e k' e' =>
            e = e' /\ ((k' = a' /\ k = a) \/ (k' <> a /\ k = k'))) r.

Definition Filter (P : A -> B -> Prop) (r : EMap) :
  EMap :=
  fun p => Lookup (fst p) (snd p) r /\ P (fst p) (snd p).

Definition Define (P : A -> Prop) (b : B) (r : EMap) :
  EMap :=
  Ensembles.Union
    _ (fun p => P (fst p) /\ In _ (Singleton _ b) (snd p))
      (Filter (fun k _ => ~ P k) r).

Definition Modify (a : A) (f : B -> B) (r : EMap) :
  EMap :=
  Relate (fun k e k' e' => k = k' /\ IF k' = a then e' = f e else e' = e) r.

Definition All (P : A -> B -> Prop) (r : EMap) : Prop :=
  forall a b, Lookup a b r -> P a b.

Definition Any (P : A -> B -> Prop) (r : EMap) : Prop :=
  exists a b, Lookup a b r /\ P a b.

Lemma Lookup_Empty : forall a b, ~ Lookup a b Empty.
Proof. firstorder. Qed.

Lemma Lookup_Single : forall a a' b b',
  a = a' -> b = b' -> Lookup a b (Single a' b').
Proof. intros; rewrite H, H0; firstorder. Qed.

Lemma Lookup_Single_inv : forall a b c d,
  Lookup a b (Single c d) -> a = c /\ b = d.
Proof. split; inversion H; reflexivity. Qed.

Lemma Lookup_Insert : forall a b c d r H,
  (a = c /\ b = d) \/ (a <> c /\ Lookup a b r)
    -> Lookup a b (Insert c d r H).
Proof.
  intros.
  intuition.
    rewrite H0, H2.
    right; constructor.
  left.
  exact H2.
Qed.

Lemma Lookup_Insert_inv : forall a b c d r H,
  Lookup a b (Insert c d r H)
    -> (a = c /\ b = d) \/ (a <> c /\ Lookup a b r).
Proof.
  intros.
  inversion H0; clear H0.
    subst.
    right.
    firstorder.
    unfold not; intros; subst.
    contradiction (H b).
  inversion H1; clear H1.
  firstorder.
Qed.

Lemma Lookup_Remove : forall a b a' r,
  Lookup a b r -> a <> a' -> Lookup a b (Remove a' r).
Proof. firstorder. Qed.

Lemma Lookup_Remove_ex_r : forall a b r,
  Lookup a b r -> exists a', a <> a' -> Lookup a' b (Remove a r).
Proof. firstorder. Qed.

Lemma Lookup_Remove_inv : forall a b a' r,
  Lookup a b (Remove a' r) -> a <> a' /\ Lookup a b r.
Proof. firstorder. Qed.

Lemma Lookup_Update : forall a b a' b' r,
  (a = a' /\ b = b') \/ (a <> a' /\ Lookup a b r)
    -> Lookup a b (Update a' b' r).
Proof.
  intros.
  intuition.
    rewrite H, H1.
    right; constructor.
  left; constructor.
    exact H1.
  exact H.
Qed.

Lemma Lookup_Update_eq : forall a b b' r,
  b = b' -> Lookup a b (Update a b' r).
Proof.
  intros; subst.
  apply Lookup_Update.
  left; intuition.
Qed.

Lemma Lookup_Update_neq : forall a a' b b' r,
  a <> a' -> Lookup a b r -> Lookup a b (Update a' b' r).
Proof.
  intros; subst.
  apply Lookup_Update.
  right; intuition.
Qed.

Lemma Lookup_Update_inv : forall a b a' b' r,
  Lookup a b (Update a' b' r)
    -> (a = a' /\ b = b') \/ (a <> a' /\ Lookup a b r).
Proof.
  intros.
  inversion H; clear H.
    firstorder.
  inversion H0; clear H0.
  firstorder.
Qed.

Lemma Lookup_Update_idem : forall a b r,
  Functional r ->
  (forall a a' : A, a = a' \/ a <> a') ->
    Lookup a b r -> Same r (Update a b r).
Proof.
  split; intros.
    apply Lookup_Update.
    destruct (H0 a0 a).
      left; intuition; subst.
      eapply H; eauto.
    right; intuition.
  apply Lookup_Update_inv in H2.
  firstorder; subst; assumption.
Qed.

Lemma Lookup_Relate : forall a b c d (f : A -> B -> A -> B -> Prop) r,
  Lookup a b r -> f a b c d -> Lookup c d (Relate f r).
Proof. firstorder. Qed.

Lemma Lookup_Relate_inv : forall a b (f : A -> B -> A -> B -> Prop) r,
  Lookup a b (Relate f r) -> exists a' b', f a' b' a b /\ Lookup a' b' r.
Proof.
  intros.
  inversion H; clear H.
  firstorder.
Qed.

Lemma Lookup_Move : forall k e a a' r,
  (IF k = a'
   then Lookup a e r
   else k <> a /\ Lookup k e r)
    -> Lookup k e (Move a a' r).
Proof. firstorder. Qed.

Lemma Lookup_Move_inv : forall k e a a' r,
  Lookup k e (Move a a' r)
    -> (k = a' /\ Lookup a e r) \/ (k <> a /\ Lookup k e r).
Proof.
  firstorder;
  simpl in *; subst;
  firstorder.
Qed.

Lemma Lookup_Map : forall a b f r,
  (exists b', f a b' = b /\ Lookup a b' r) -> Lookup a b (Map f r).
Proof. firstorder. Qed.

Lemma Lookup_Map_inv : forall a b f r,
  Lookup a b (Map f r) -> exists b', f a b' = b /\ Lookup a b' r.
Proof.
  intros.
  inversion H; clear H.
  firstorder.
Qed.

Lemma Lookup_Map_set : forall a b f r,
  (exists p', f p' = (a, b) /\ Lookup (fst p') (snd p') r)
    -> Lookup a b (Map_set f r).
Proof.
  unfold Map_set, Lookup, Ensembles.In; simpl.
  intuition.
  destruct H.
  rewrite <- surjective_pairing in H.
  exists x; simpl.
  intuition.
Qed.

Lemma Lookup_Map_set_inv : forall a b f r,
  Lookup a b (Map_set f r)
    -> exists p', f p' = (a, b) /\ Lookup (fst p') (snd p') r.
Proof.
  intros.
  inversion H; clear H.
  exists x.
  unfold Lookup.
  rewrite <- surjective_pairing.
  firstorder.
Qed.

Lemma Lookup_Filter : forall a b P r,
  Lookup a b r /\ P a b -> Lookup a b (Filter P r).
Proof. firstorder. Qed.

Lemma Lookup_Filter_inv : forall a b P r,
  Lookup a b (Filter P r) -> P a b /\ Lookup a b r.
Proof. firstorder. Qed.

Lemma Lookup_Union : forall a b r r',
  Lookup a b r \/ Lookup a b r'
    -> Lookup a b (Union (A * B) r r').
Proof.
  firstorder.
    left; exact H.
  right; exact H.
Qed.

Lemma Lookup_Union_inv : forall a b r r',
  Lookup a b (Union (A * B) r r')
    -> Lookup a b r \/ Lookup a b r'.
Proof.
  firstorder.
  unfold Lookup, Ensembles.In in *.
  apply Constructive_sets.Union_inv in H.
  intuition.
Qed.

Lemma Lookup_Define : forall a b c P r,
  (IF P a then In _ (Singleton _ c) b else Lookup a b r)
    -> Lookup a b (Define P c r).
Proof.
  unfold Define; intros.
  apply Lookup_Union.
  do 2 destruct H.
    left.
    unfold Lookup, Ensembles.In; simpl.
    intuition.
  right.
  apply Lookup_Filter.
  intuition.
Qed.

Lemma Lookup_Define_inv : forall a b c P r,
  Lookup a b (Define P c r)
    -> IF P a
       then In _ (Singleton _ c) b
       else Lookup a b r.
Proof.
  unfold Define; intros.
  apply Lookup_Union_inv in H.
  destruct H.
    firstorder.
  apply Lookup_Filter_inv in H.
  firstorder.
Qed.

Lemma Lookup_Modify : forall a b a' f r,
  (a = a' /\ exists b', f b' = b /\ Lookup a b' r)
    \/ (a <> a' /\ Lookup a b r)
    -> Lookup a b (Modify a' f r).
Proof.
  firstorder;
  simpl in *; subst;
  firstorder.
Qed.

Lemma Lookup_Modify_inv : forall a b a' f r,
  Lookup a b (Modify a' f r)
    -> (a = a' /\ exists b', f b' = b /\ Lookup a b' r)
         \/ (a <> a' /\ Lookup a b r).
Proof.
  firstorder;
  simpl in *; subst;
  firstorder.
Qed.

Lemma Lookup_Member : forall a b r,
  Lookup a b r -> Member a r.
Proof. firstorder. Qed.

Lemma Member_Lookup_not : forall a r,
  ~ Member a r -> forall b, ~ Lookup a b r.
Proof. firstorder. Qed.

Lemma All_Remove : forall a P r,
  All P r -> All P (Remove a r).
Proof. firstorder. Qed.

Lemma All_Remove_inv : forall a P r,
  All P (Remove a r) -> ~ Member a r -> All P r.
Proof.
  intros.
  intros ???.
  apply H.
  apply Lookup_Remove.
    assumption.
  unfold not; intros.
  subst.
  unfold Member in H0.
  Require Import Classical_Pred_Type.
  apply not_ex_all_not with (n:=b) in H0.
  contradiction.
Qed.

Lemma All_Remove_Lookup_inv : forall a P r,
  All P (Remove a r) -> forall a' b', a' <> a -> Lookup a' b' r -> P a' b'.
Proof. intros; apply H, Lookup_Remove; trivial. Qed.

Lemma All_Update_inv : forall k e P r,
  All P (Update k e r) -> P k e /\ All P (Remove k r).
Proof.
  intros.
  split.
    apply H, Lookup_Update.
    left; auto.
  intros ???.
  apply Lookup_Remove_inv in H0.
  destruct H0.
  apply H, Lookup_Update.
  right; intuition.
Qed.

Definition Unique P a r := All (fun a b => P a b = false) (Remove a r).

End TupleEnsemble.

Arguments Functional : default implicits.
Arguments Empty {_ _} _.
Arguments Single : default implicits.
Arguments Insert : default implicits.
Arguments Remove : default implicits.
Arguments Update : default implicits.
Arguments Modify : default implicits.
Arguments Move : default implicits.
Arguments Filter : default implicits.
Arguments Map : default implicits.
Arguments Relate : default implicits.
Arguments All : default implicits.
Arguments Any : default implicits.
Arguments Define : default implicits.
Arguments Lookup : default implicits.
Arguments Same : default implicits.
Arguments Member : default implicits.

Arguments Lookup_Empty : default implicits.

Ltac t H :=
  unfold Relate;
  split; intros;
  repeat destruct H;
  simpl in *; subst;
  firstorder;
  simpl in *; subst;
  firstorder.

Lemma Relate_left_identity : forall A B (r : EMap A B),
  Same r (Relate (fun k x k' x' => k = k' /\ x = x') r).
Proof. t H. Qed.

Lemma Relate_right_identity : forall A B (r : EMap A B),
  Same (Relate (fun k x k' x' => k = k' /\ x = x') r) r.
Proof. t H. Qed.

Lemma Relate_composition :
  forall A B C D E F
         (f : C -> D -> E -> F -> Prop) (g : A -> B -> C -> D -> Prop) r,
    Same (Relate (fun k e k' e' =>
                  exists k'' e'', g k e k'' e'' /\ f k'' e'' k' e') r)
         (Relate f (Relate g r)).
Proof. t H; exists x1; exists x2; t H. Qed.

Ltac teardown :=
  match goal with
  | [ H : Lookup _ _ Empty            |- _ ] => contradiction (Lookup_Empty H)
  | [ H : Lookup _ _ (Single _ _)     |- _ ] => apply Lookup_Single_inv in H
  | [ H : Lookup _ _ (Insert _ _ _ _) |- _ ] => apply Lookup_Insert_inv in H
  | [ H : Lookup _ _ (Remove _ _)     |- _ ] => apply Lookup_Remove_inv in H
  | [ H : Lookup _ _ (Update _ _ _)   |- _ ] => apply Lookup_Update_inv in H
  | [ H : Lookup _ _ (Move _ _ _)     |- _ ] => apply Lookup_Move_inv in H
  | [ H : Lookup _ _ (Map _ _)        |- _ ] => apply Lookup_Map_inv in H
  | [ H : Lookup _ _ (Map_set _ _)    |- _ ] => apply Lookup_Map_set_inv in H
  | [ H : Lookup _ _ (Relate _ _)     |- _ ] => apply Lookup_Relate_inv in H
  | [ H : Lookup _ _ (Filter _ _)     |- _ ] => apply Lookup_Filter_inv in H
  | [ H : Lookup _ _ (Define _ _ _)   |- _ ] => apply Lookup_Define_inv in H
  | [ H : Lookup _ _ (Modify _ _ _)   |- _ ] => apply Lookup_Modify_inv in H
  | [ H : Lookup _ _ (Union _ _ _)    |- _ ] => apply Lookup_Union_inv in H

  | [ H : Member _ Empty            |- _ ] => unfold Member in H
  | [ H : Member _ (Single _ _)     |- _ ] => unfold Member in H
  | [ H : Member _ (Insert _ _ _ _) |- _ ] => unfold Member in H
  | [ H : Member _ (Remove _ _)     |- _ ] => unfold Member in H
  | [ H : Member _ (Update _ _ _)   |- _ ] => unfold Member in H
  | [ H : Member _ (Move _ _ _)     |- _ ] => unfold Member in H
  | [ H : Member _ (Map _ _)        |- _ ] => unfold Member in H
  | [ H : Member _ (Map_set _ _)    |- _ ] => unfold Member in H
  | [ H : Member _ (Relate _ _)     |- _ ] => unfold Member in H
  | [ H : Member _ (Filter _ _)     |- _ ] => unfold Member in H
  | [ H : Member _ (Define _ _ _)   |- _ ] => unfold Member in H
  | [ H : Member _ (Modify _ _ _)   |- _ ] => unfold Member in H
  | [ H : Member _ (Union _ _ _)    |- _ ] => unfold Member in H

  | [ |- Lookup _ _ Empty            ] => apply Lookup_Empty
  | [ |- Lookup _ _ (Single _ _)     ] => apply Lookup_Single
  | [ |- Lookup _ _ (Insert _ _ _ _) ] => apply Lookup_Insert
  | [ |- Lookup _ _ (Remove _ _)     ] => apply Lookup_Remove
  | [ |- Lookup ?A _ (Update ?A _ _) ] => apply Lookup_Update_eq
  | [ H : ?A = ?B  |- Lookup ?A _ (Update ?B _ _) ] => apply Lookup_Update_eq
  | [ H : ?A <> ?B |- Lookup ?A _ (Update ?B _ _) ] => apply Lookup_Update_neq
  | [ |- Lookup _ _ (Update _ _ _)   ] => apply Lookup_Update_eq ||
                                          apply Lookup_Update
  | [ |- Lookup _ _ (Move _ _ _)     ] => apply Lookup_Move
  | [ |- Lookup _ _ (Map _ _)        ] => apply Lookup_Map
  | [ |- Lookup _ _ (Map_set _ _)    ] => apply Lookup_Map_set
  | [ |- Lookup _ _ (Relate _ _)     ] => apply Lookup_Relate
  | [ |- Lookup _ _ (Filter _ _)     ] => apply Lookup_Filter
  | [ |- Lookup _ _ (Define _ _ _)   ] => apply Lookup_Define
  | [ |- Lookup _ _ (Modify _ _ _)   ] => apply Lookup_Modify
  | [ |- Lookup _ _ (Union _ _ _)    ] => apply Lookup_Union

  | [ H : Lookup ?X ?Y ?R |- Member ?X ?R ] => exists Y; exact H

  (* | [ H1 : All _ (Remove _ _)   |- _ ] => apply All_Remove_inv in H1 *)
  (* | [ H1 : All _ (Update _ _ _) |- _ ] => apply All_Update_inv in H1 *)

  | [ |- All _ (Remove _ _) ] => apply All_Remove

  | [ H1 : All ?P ?R, H2 : Lookup ?X ?Y ?R |- _ ] =>
    specialize (H1 _ _ H2); simpl in H1

  | [ H : IF _ then _ else _ |- _ ] => destruct H
  | [ H : _ /\ _             |- _ ] => destruct H
  | [ H : _ \/ _             |- _ ] => destruct H
  | [ H : _ * _              |- _ ] => destruct H
  | [ H : exists _, _        |- _ ] => destruct H
  | [ H : @sig _ _           |- _ ] => destruct H
  | [ H : @sig2 _ _ _        |- _ ] => destruct H
  | [ H : @sigT _ _          |- _ ] => destruct H
  | [ H : @sigT2 _ _ _       |- _ ] => destruct H
  | [ H : bool               |- _ ] => destruct H
  | [ H : option _           |- _ ] => destruct H
  | [ H : sum _ _            |- _ ] => destruct H
  | [ H : sumor _ _          |- _ ] => destruct H
  | [ H : sumbool _ _        |- _ ] => destruct H

  | [ H : forall x, Some ?X = Some x -> _  |- _ ] => specialize (H X eq_refl)
  | [ H : forall x y, Some (?X, ?Y) = Some (x, y) -> _  |- _ ] =>
    specialize (H X Y eq_refl)

  | [ H1 : ?X = true, H2 : ?X = false |- _ ] => rewrite H1 in H2; discriminate

  end; simpl in *; try tauto.

Lemma Update_Update : forall A (addr : A) B (blk1 blk2 : B) r,
  Same (Update addr blk1 (Update addr blk2 r)) (Update addr blk1 r).
Proof.
  split; intros; repeat teardown.
  right; intuition.
  teardown.
Qed.

Global Program Instance Remove_Proper A B :
  Proper (eq ==> @Same _ _ ==> @Same _ _) (@Remove A B).
Next Obligation.
  split; repeat intro; subst; repeat teardown.
    rewrite <- H0; assumption.
  rewrite H0; assumption.
Qed.

Global Program Instance Map_Proper A B :
  Proper (pointwise_relation _ (pointwise_relation _ eq)
            ==> @Same _ _ ==> @Same _ _) (@Map A B B).
Next Obligation.
  unfold pointwise_relation.
  split; repeat intro; subst; repeat teardown;
  exists x1;
  split.
  - now rewrite <- H.
  - rewrite <- H0; assumption.
  - now rewrite H.
  - rewrite H0; assumption.
Qed.

Lemma Unique_Map_Update : forall A B (P : A -> B -> bool) a b r f,
  (forall x y : A, {x = y} + {x <> y}) ->
  Functional r ->
  Lookup a b r ->
  P a b = true ->
  Unique _ _ P a r ->
  Same (Map (fun k e => if P k e then f k e else e) r) (Update a (f a b) r).
Proof.
  intros.
  split; intros; repeat teardown; subst.
  - destruct (X a0 a) eqn:Heqe.
      subst; left.
      specialize (H _ _ H0 _ H4); subst.
      rewrite H1.
      intuition.
    right.
    eapply All_Remove_Lookup_inv in H2; eauto.
    rewrite H2.
    intuition.
  - exists b.
    rewrite H1.
    intuition.
  - exists b0.
    eapply All_Remove_Lookup_inv in H2; eauto.
    rewrite H2.
    intuition.
Qed.

Global Program Instance Finite_Proper_Same {A B} :
  Proper (Same (B:=B) ==> Basics.impl) (Finite (A * B)).
Next Obligation.
  repeat intro.
  apply Same_Same_set in H.
  now rewrite <- H.
Qed.

Global Program Instance Finite_Proper_Same_flip_1 {A B} :
  Proper (Same (B:=B) ==> Basics.flip Basics.impl) (Finite (A * B)).
Next Obligation.
  repeat intro.
  apply Same_Same_set in H.
  now rewrite H.
Qed.

Global Program Instance Finite_Proper_Same_flip_2 {A B} :
  Proper (Same (B:=B) --> Basics.flip Basics.impl) (Finite (A * B)).
Next Obligation.
  repeat intro.
  apply Same_Same_set in H.
  now rewrite <- H.
Qed.

Section TupleEnsembleFinite.

Variable A : Type.
Variable B : Type.

Lemma Empty_preserves_Finite : Finite _ (@Empty A B).
Proof. constructor. Qed.

Lemma Single_is_Finite : forall a b, Finite _ (@Single A B a b).
Proof. intros; apply Finite_sets_facts.Singleton_is_finite. Qed.

Lemma Insert_preserves_Finite : forall a b `(_ : Finite _ r) H,
  Finite _ (@Insert A B a b r H).
Proof. intros; apply Finite_sets_facts.Add_preserves_Finite; assumption. Qed.

Lemma Setminus_preserves_finite {U} :
  forall A:Ensemble U,
    Finite U A -> forall X:Ensemble U, Finite U (Setminus U A X).
Proof.
  intros A' ? ?; apply Finite_sets_facts.Finite_downward_closed with A'; auto with sets.
  intros ? H0; inversion H0; assumption.
Qed.

Lemma Remove_preserves_Finite : forall a `(_ : Finite _ r),
  Finite _ (@Remove A B a r).
Proof. intros; apply Setminus_preserves_finite; assumption. Qed.

Lemma Update_preserves_Finite : forall a b `(_ : Finite _ r),
  Finite _ (@Update A B a b r).
Proof.
  intros; apply Finite_sets_facts.Add_preserves_Finite, Setminus_preserves_finite; assumption.
Qed.

Lemma Filter_preserves_Finite : forall P `(_ : Finite _ r),
  Finite _ (@Filter A B P r).
Proof.
  unfold Filter; intros.
  eapply Finite_sets_facts.Finite_downward_closed; eauto with sets.
  intros ? H0; inversion H0; clear H0.
  unfold Lookup in H.
  rewrite <- surjective_pairing in H.
  assumption.
Qed.

Lemma Finite_Add_Subtract : forall T (Y : Ensemble T) x,
  Finite _ (Add T (Subtract T Y x) x) -> Finite _ Y.
Proof.
  intros.
  eapply Finite_sets_facts.Finite_downward_closed; eauto with sets; intros ??.
  (* Jason Gross: To avoid the axiom of choice, you'd need a stronger version
     of [Finite], something like having a list of elements together with a
     mapping of elements of the type to indices of the list such that if an
     element of the type is in the subset, then it is equal to the element of
     the list at the corresponding index. In this case, everything is
     constructive, and you shouldn't need either Extensionality_Ensembles nor
     decidable equality. *)
  elim (Classical_Prop.classic (x = x0)); intros.
    subst; right; constructor.
  left; constructor; auto.
  unfold not; intros.
  contradiction H1.
  inversion H2.
  reflexivity.
Qed.

Definition Surjective {A B} (X : Ensemble A) (Y : Ensemble B) f :=
  forall y : B, In _ Y y -> exists x : A, In _ X x /\ y = f x.

Lemma Surjective_Add_Subtract : forall T T' X Y f x,
  Surjective (Add T X x) Y f -> Surjective X (Subtract T' Y (f x)) f.
Proof.
  unfold Surjective; intros.
  inversion H0; clear H0.
  destruct (H _ H1) as [? [? ?]]; subst; clear H H1.
  inversion H0; subst; clear H0.
    exists x0; intuition.
  inversion H; subst; clear H.
  contradiction H2.
  constructor.
Qed.

Lemma Surjection_preserves_Finite : forall T T' X Y f,
  Surjective X Y f -> Finite T X -> Finite T' Y.
Proof.
  intros.
  generalize dependent Y.
  induction H0; intros.
    eapply Finite_sets_facts.Finite_downward_closed; eauto with sets; intros ??.
    firstorder.
  apply Surjective_Add_Subtract in H1; auto.
  specialize (IHFinite _ H1).
  eapply Finite_Add_Subtract.
  constructor.
  exact IHFinite.
  unfold not; intros.
  inversion H2.
  contradiction H4.
  constructor.
Qed.

Lemma Map_preserves_Finite {C} : forall f `(_ : Finite _ r),
  Finite _ (@Map A B C f r).
Proof.
  unfold Map; intros.
  apply Surjection_preserves_Finite
   with (X:=r) (f:=fun p => (fst p, f (fst p) (snd p))); trivial.
  intros ??.
  unfold Ensembles.In in H.
  do 2 destruct H.
  destruct y; simpl in *; subst.
  exists (a, x); simpl.
  intuition.
Qed.

Lemma Map_set_preserves_Finite {T T'} : forall f `(_ : Finite _ r),
  Finite _ (@Map_set T T' f r).
Proof.
  unfold Map_set; intros.
  apply Surjection_preserves_Finite with (X:=r) (f:=f); trivial.
  intros ??.
  unfold Ensembles.In in H.
  do 2 destruct H; subst.
  exists x; simpl.
  intuition.
Qed.

Lemma Relate_preserves_Finite :
  forall A B C D (f : A -> B -> C -> D -> Prop) `(_ : Finite _ r)
         (is_functional : forall k e k' e' k'' e'',
            f k e k' e' -> f k e k'' e'' -> k' = k'' /\ e' = e'')
         (is_total : forall (k : A) (e : B),
            { p : C * D | f k e (fst p) (snd p) }),
    Finite _ (Relate f r).
Proof.
  unfold Relate; intros ????? r ? g k.
  eapply Surjection_preserves_Finite
    with (X:=r) (f:=fun p => proj1_sig (k (fst p) (snd p))); trivial.
  intros ??.
  unfold Ensembles.In in H.
  do 2 destruct H.
  destruct y; simpl in *; subst.
  exists (x, x0); simpl.
  destruct (k x x0), x1.
  simpl in *; intuition.
  destruct (g _ _ _ _ _ _ f0 H1); subst.
  reflexivity.
Qed.

Lemma Relate_Add_preserves_Finite :
  forall A B C D (f : A -> B -> C -> D -> Prop) `(_ : Finite _ r) x
         (is_functional : forall k e k' e' k'' e'',
            f k e k' e' -> f k e k'' e'' -> k' = k'' /\ e' = e'')
         (is_total : forall (k : A) (e : B),
            { p : C * D | f k e (fst p) (snd p) }),
    ~ In (A * B) r x
      -> Finite _ (Relate f r)
      -> Finite _ (Relate f (Add (A * B) r x)).
Proof.
  intros.
  apply Relate_preserves_Finite; auto.
  constructor; auto.
Qed.

Lemma Move_preserves_Finite : forall a a' `(_ : Finite _ r),
  (forall x y : A, {x = y} + {x <> y})
    -> Finite _ (@Move A B a a' r).
Proof.
  intros.
  apply Relate_preserves_Finite; trivial; intros.
    intuition; subst; congruence.
  destruct (X k a); subst.
    exists (a', e); simpl; intuition.
  exists (k, e); simpl; intuition.
Qed.

Lemma Modify_preserves_Finite : forall a f `(_ : Finite _ r),
  (forall x y : A, {x = y} + {x <> y})
    -> Finite _ (@Modify A B a f r).
Proof.
  intros.
  apply Relate_preserves_Finite; trivial; intros.
  - intuition; subst; tauto.
  - destruct (X k a); subst.
    + exists (a, f e); simpl; intuition.
    + exists (k, e); simpl; intuition.
Qed.

Lemma Conjunction_preserves_finite_right {U} :
  forall A:Ensemble U,
    Finite U A -> forall X:Ensemble U,
      Finite U (fun x : U => In U X x /\ In U A x).
Proof.
  intros A' H' X.
  apply Finite_sets_facts.Finite_downward_closed with A'; auto with sets.
  intros ? H0; inversion H0; assumption.
Qed.

Lemma Conjunction_preserves_finite_left {U} :
  forall X:Ensemble U,
    Finite U X -> forall A:Ensemble U,
      Finite U (fun x : U => In U X x /\ In U A x).
Proof.
  intros X H' A'.
  apply Finite_sets_facts.Finite_downward_closed with X; auto with sets.
  intros ? H0; inversion H0; assumption.
Qed.

Lemma Product_preserves_Finite {T U X Y} :
  Finite T X -> Finite U Y -> Finite (T * U) (Product X Y).
Proof.
  intros.
  generalize dependent Y.
  induction H; intros.
    eapply Finite_sets_facts.Finite_downward_closed; eauto with sets.
    intros ? H1; inversion H1; inversion H.
  rewrite Product_Add_left.
  apply Finite_sets_facts.Union_preserves_Finite; auto.
  clear IHFinite H0 H A0.
  induction H1.
    eapply Finite_sets_facts.Finite_downward_closed; eauto with sets.
    intros ? H1; inversion H1; inversion H0.
  rewrite Product_Add_right.
  apply Finite_sets_facts.Union_preserves_Finite; auto.
  rewrite Product_Singleton_Singleton.
  rewrite <- Powerset_facts.Empty_set_zero'.
  constructor.
    constructor.
  unfold not; intros.
  inversion H0.
Qed.

Lemma Define_preserves_Finite : forall P b `(_ : Finite _ r),
  (forall x : A, {P x} + {~ P x})
    -> Finite _ P -> Finite _ (@Define A B P b r).
Proof.
  unfold Define; intros.
  apply Finite_sets_facts.Union_preserves_Finite.
    apply Product_preserves_Finite; auto.
    apply Finite_sets_facts.Singleton_is_finite.
  apply Filter_preserves_Finite; auto.
Qed.

End TupleEnsembleFinite.

Hint Resolve Conjunction_preserves_finite_left : sets.
Hint Resolve Conjunction_preserves_finite_right : sets.
Hint Resolve Define_preserves_Finite : sets.
Hint Resolve Empty_preserves_Finite : sets.
Hint Resolve Filter_preserves_Finite : sets.
Hint Resolve Finite_Add_Subtract : sets.
Hint Resolve Insert_preserves_Finite : sets.
Hint Resolve Map_preserves_Finite : sets.
Hint Resolve Modify_preserves_Finite : sets.
Hint Resolve Move_preserves_Finite : sets.
Hint Resolve Product_Add_left : sets.
Hint Resolve Product_Add_right : sets.
Hint Resolve Product_Empty_set_left : sets.
Hint Resolve Product_Empty_set_right : sets.
Hint Resolve Product_Singleton_Singleton : sets.
Hint Resolve Product_preserves_Finite : sets.
Hint Resolve Relate_Add_preserves_Finite : sets.
Hint Resolve Relate_preserves_Finite : sets.
Hint Resolve Remove_preserves_Finite : sets.
Hint Resolve Setminus_preserves_finite : sets.
Hint Resolve Single_is_Finite : sets.
Hint Resolve Surjection_preserves_Finite : sets.
Hint Resolve Surjective_Add_Subtract : sets.
Hint Resolve Update_preserves_Finite : sets.

Ltac finite_preservation :=
  repeat (
  match goal with
  | [ |- Finite _ Empty            ] => apply Empty_preserves_Finite
  | [ |- Finite _ (Single _ _)     ] => apply Single_is_Finite
  | [ |- Finite _ (Insert _ _ _ _) ] => apply Insert_preserves_Finite
  | [ |- Finite _ (Remove _ _)     ] => apply Remove_preserves_Finite
  | [ |- Finite _ (Update _ _ _)   ] => apply Update_preserves_Finite
  | [ |- Finite _ (Move _ _ _)     ] => apply Move_preserves_Finite
  | [ |- Finite _ (Map _ _)        ] => apply Map_preserves_Finite
  | [ |- Finite _ (Map_set _ _)    ] => apply Map_set_preserves_Finite
  | [ |- Finite _ (Relate _ _)     ] => apply Relate_preserves_Finite
  | [ |- Finite _ (Filter _ _)     ] => apply Filter_preserves_Finite
  | [ |- Finite _ (Define _ _ _)   ] => apply Define_preserves_Finite
  | [ |- Finite _ (Modify _ _ _)   ] => apply Modify_preserves_Finite
  | [ |- Finite _ (Union _ _ _)    ] => apply Finite_sets_facts.Union_preserves_Finite
  | [ |- Finite _ (Add _ _ _)      ] => apply Finite_sets_facts.Add_preserves_Finite
  end; auto).
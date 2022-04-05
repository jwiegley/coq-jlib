Require Import
  Coq.Classes.CMorphisms
  Coq.Classes.SetoidClass
  Coq.Program.Program
  Coq.micromega.Lia
  Coq.Unicode.Utf8
  Coq.Vectors.Fin
  Coq.FSets.FMapInterface
  Coq.Structures.Equalities
  Coq.Structures.DecidableType
  Coq.FSets.FMapAVL
  Coq.FSets.FMapFacts
  Coq.Sets.Finite_sets
  Coq.Logic.Classical
  Coq.Logic.ClassicalFacts
  Coq.Sets.Ensembles.

Generalizable All Variables.

(************************************************************************
 ** Decidable equality
 ************************************************************************)

Class EqDec (a : Type) := {
  eq : a → a → Prop;
  eq_dec : ∀ x y : a, {eq x y} + {~ eq x y};
  eq_Equivalence :> Equivalence eq
}.

(************************************************************************
 ** Types with finite inhabitants.
 ************************************************************************)

Definition Iso (a b : Type) : Type :=
  { h : iffT a b | fst h ∘ snd h = id ∧ snd h ∘ fst h = id }.

(* [a] is a finite type (and thus, enumerable) if there is a bijection from
   that type to the finite naturals for some value of [n]. *)
Class Finite (a : Type) : Type := {
    cardinality : nat;
    (* jww (2022-03-25): There is a drawback to this definition, which is that
       it decides a single ordering, when in fact there are combinatorially
       many witness to this proof. What we should really have here is the
       space of all such isomorphisms. *)
    cardinality_witness : Iso a (Fin.t cardinality)
}.

(* We can enumerate all inhabitants of a finite type by induction on the
   cardinality and asking for the witness. *)
(* jww (2022-03-25): Change the return type to be a vector of Fin.t cardinality length. *)
Definition enumerate `{F : Finite k} : list k.
Proof.
  destruct F as [n [[_ h] [_ _]]]; simpl in *.
  induction n.
  - exact nil.
  - pose proof (@of_nat_lt 0 (S n) ltac:(lia)) as H.
    apply cons.
    + apply h.
      exact H.
    + apply IHn.
      intros.
      apply h.
      apply FS.
      exact H0.
Defined.

(************************************************************************
 ** Helper tactics used below.
 ************************************************************************)

Ltac breakdown :=
  repeat lazymatch goal with
         | [ H : context[eq_dec ?X ?Y] |- _ ] =>
             destruct (eq_dec X Y); subst; firstorder eauto
         | [ |- context[eq_dec ?X ?Y] ] =>
             destruct (eq_dec X Y); subst; firstorder eauto
         end.

(************************************************************************
 ** Map interface
 ************************************************************************)

Record Domain := {
  Result  : Type → Type; (* Type of results *)
  Partial : Type → Type; (* Type of partial results *)
  Bag     : Type → Type; (* Type of unordered, unique collections *)
  Truth   : Type;        (* Type that represents truth *)
  Relation ty := ty → ty → Truth; (* The type of relations or mappings *)
}.

Definition Relations : Domain := {|
  Result  := Ensemble;
  Partial := Ensemble;
  Bag     := Ensemble;
  Truth   := Prop;
|}.

Definition Functions : Domain := {|
  Result  := id;
  Partial := option;
  Bag     := list;
  Truth   := bool;
|}.

(*
obj: Pred v
mor: ∀ x y : Pred v, x → y → Set

Product:   ∪
Coproduct: ∩
Initial:   ∅
Terminal:  ⊤
*)

Class Map (D : Domain) (k : Type) (t : Type → Type) := {
  add      {v}    : k → v → t v → t v;
  remove   {v}    : k → t v → t v;
  find     {v}    : k → t v → Partial D v;
  mem      {v}    : k → t v → Truth D;
  keys     {v}    : t v → Bag D k;
  elements {v}    : t v → Bag D (k * v);
  map      {v v'} : (v → v') → t v → t v';
  mapi     {v v'} : (k → v → v') → t v → t v';
  equal    {v}    : Relation D (t v);
  equal_f  {v}    : Relation D v → Relation D (t v);
  cardinal {v}    : t v → Result D nat;
}.

(*
∀ x y : R, lookup x = y ─HOMO→ Map (denote x) (denote y)
*)

(* STEPS

   - Choose model
   - Algebraic simplification
     Choosing a math standard API that yields the
     smallest "algebraic surface".
   - Homomorphisms
   - Non-computational -> Computational
   - Relations -> Functions (John: same as previous?)

 *)

(*
Class MapHomomorphisms (D E : Domain) (R S : Type → Type) := {
  ⟦_⟧ : R → S;
  ⦃_⦄ ∷ bool → Set

  memₕ : ∀ k m, memₛ k ⟦m⟧ ≈ ⦃ memᵣ k m ⦄
}.
*)

(*
⟦_⟧ ∷ ∀ {k v}, list (k * v) → Ensemble (k * v)
⦃_⦄ ∷ bool → Set
*)

(*
Instance Map_Representation {k v : Type} : Map Relations k (λ v, list (k * v)) := {|
Instance Map_Implementation {k v : Type} : Map Functions k (λ v, list (k * v)) := {|
*)

Definition all_keys {k v} (m : Ensemble (k * v)) : Ensemble k :=
  λ i, ∃ x, In _ m (i, x).

#[global]
Instance Map_Model {k v : Type} : Map Relations k (λ v, Ensemble (k * v)) := {|
  add      v i x m  := Add _ m (i, x);
  remove   v i m    := Setminus _ m (λ '(j, _), i = j);
  find     v i m    := (λ x, In _ m (i, x)) : Partial Relations v;
  mem      v i m    := ∃ x, In _ m (i, x);
  keys     v m      := all_keys m;
  elements v m      := m;
  map      v v' f m := λ '(i, x), ∃ y, In _ m (i, y) ∧ f y = x;
  mapi     v v' f m := λ '(i, x), ∃ y, In _ m (i, y) ∧ f i y = x;
  equal    v        := Same_set _;
  equal_f  v f      := λ m1 m2, ∀ i x y, In _ m1 (i, x) → In _ m2 (i, y) → f x y;
  cardinal v m      := Coq.Sets.Finite_sets.cardinal k (all_keys m);
|}.

(************************************************************************
 ** Semantic model for partial maps.
 ************************************************************************)

(*
Module MapModel.

Section Map.

Variable key : Type.

Section SameValue.

Variable elt : Type.

Definition t := key → elt → Prop.

Context `{EqDec key}.

#[global] Declare Instance t_respects (m : t) :
  Proper (eq ==> Logic.eq ==> iff) m.

Definition equiv : relation t := λ m1 m2, ∀ k v, m1 k v ↔ m2 k v.

#[global] Program Instance equiv_Equivalence : Equivalence equiv.
Next Obligation. now idtac. Qed.
Next Obligation. now idtac. Qed.
Next Obligation.
  unfold equiv.
  split; repeat intro.
  - now apply H1, H0.
  - now apply H0, H1.
Qed.

Definition emptyₘ : t := λ _ _, False.

Definition is_emptyₘ : Ensemble t := λ m, ∀ i v, ~ m i v.

(* jww (2022-03-25): How could this be written so that it supports the meaning
   of total maps, partial maps and multi-maps? *)
Definition addₘ (i : key) (x : elt) (m : t) : t :=
  λ j v, if eq_dec i j then x = v else m j v.

(* Definition addₘ (i : key) (x : elt) (m : t) : t := *)
(*   λ j v, if eq_dec i j then x = v else m j v. *)

#[global] Program Instance addₘ_respects :
  Proper (eq ==> Logic.eq ==> equiv ==> equiv) addₘ.
Next Obligation.
  unfold equiv, addₘ.
  split; repeat intro; subst.
  all: breakdown.
  all: try (rewrite H0 in e; contradiction).
  all: try (rewrite <- H0 in e; contradiction).
Qed.

(* Define a version of add that requires the absence of the key. This permits
   us to more directly express the meaning in terms of sets. *)
(* Definition addxₘ (i : key) (x : elt) (m : t) (H : ~ m i x) : t := *)
(*   λ j v, { x } ∪ m j v. *)

Definition findₘ (i : key) (m : t) : Ensemble elt := m i.

Definition removeₘ `{EqDec key} (i : key) (m : t) : t :=
  λ j v, if eq_dec i j then False else m j v.

(* jww (2022-03-25): Define a version of remove that depends on the presence
   of the key. *)
(* Definition removexₘ `{EqDec key} (i : key) (m : t) *)
(*            (H : ∃ v, m i v) : t := *)
(*   λ j v, `1 H \ m j v. *)

Definition memₘ (i : key) (m : t) : Prop := ∃ v, m i v.

End SameValue.

Variable elt elt' elt'' : Type.

Definition mapₘ (f : elt → elt') (m : t elt) : t elt' :=
  λ i v, ∃ x, m i x ∧ f x = v.

Definition keysₘ (m : t elt) : Ensemble key := λ i, ∃ v, m i v.

Definition mapiₘ (f : key → elt → elt') (m : t elt) : t elt' :=
  λ i v, ∃ x, m i x ∧ f i x = v.

Definition map2ₘ (f : option elt -> option elt' -> option elt'')
           (m1 : t elt) (m2 : t elt') : t elt'' :=
  λ i v,
    (∃ x, m1 i x ∧
     (  (∃ y,   m2 i y ∧ f (Some x) (Some y) = Some v)
      ∨ (∀ y, ~ m2 i y ∧ f (Some x) None = Some v)))
    ∨
    (∀ y, ~ m1 i y ∧
     ∃ y, m2 i y ∧ f None (Some y) = Some v).

Definition elementsₘ (m : t elt) : Ensemble (key * elt) :=
  λ '(i, x), m i x.

(* jww (2022-03-25): Could there be a version of Ensemble only for sets that
   are either singleton or empty? Then I could define partial functions as
   [a → option b], where option is relational rather than computational. *)
Definition cardinalₘ (m : t elt) (n : nat) : Prop :=
  cardinal key (keysₘ m) n.

Definition equalₘ (f : relation elt) : relation (t elt) :=
  λ m1 m2, ∀ k x y, m1 k x → m2 k y → f x y.

Fixpoint fold_right_rel {A B : Type} (f : B → A → A → Prop)
         (z : A) (l : list B) : A → Prop :=
  λ r, match l with
       | nil => z = r
       | b :: t => ∃ r', fold_right_rel f z t r' ∧ f b r' r
       end.

Lemma fold_right_rel_correct
      {A B : Type} (p : B → A → A → Prop) (f : B → A → A)
      (z : A) (l : list B) :
  (∀ x z z', p x z z' → f x z = z') →
  ∀ r', fold_right_rel p z l r' → fold_right f z l = r'.
Proof.
  intros.
  generalize dependent r'.
  induction l; simpl; intros; auto.
  destruct H0, H0; subst.
  now erewrite IHl; eauto.
Qed.

(* jww (2022-03-25): Work out the category of partial functions. *)
(* jww (2022-03-25): Having fold in this interface is a bug. *)

Context `{F : Finite key}.

Definition foldₘ `(f : key → elt → A → A → Prop) (m : t elt) (z : A) : A → Prop :=
  fold_right_rel (λ i rest r, ∃ x, m i x ∧ f i x rest r) z enumerate.

End Map.

Arguments equiv {_ _} _ _.
Arguments addₘ {_ _ _} _ _ _.
Arguments removeₘ {_ _ _} _ _.

Infix "≡" := equiv (at level 100).

(* Notation "k ↦ v" := (t k v) (at level 40, left associativity) : type_scope. *)

Notation "k ↦ v ∈ m" := (m k v)
  (at level 90, m at level 30, only parsing) : core_scope.

Notation "k ↦ '_' ∉ m" := (∀ v, ~ m k v)
  (at level 90, m at level 30, only parsing) : core_scope.

End MapModel.

(************************************************************************
 ** Theorems that hold for all partial maps.
 ************************************************************************)

Module MapFacts.

Module Import M := MapModel.

Section Facts.

Variable k : Type.
Variable v : Type.

Context `{EqDec k}.

Hypothesis unique_keys : ∀ i x y (m : t k v), m i x → m i y → x = y.

Ltac smash :=
  intros;
  repeat (
    breakdown;
    try lazymatch goal with
    | [ |- ?X ≡ ?Y ] =>
        split; intros
    end;
    breakdown
  ).

Theorem add_idem i x (m : t k v) :
  addₘ i x (addₘ i x m) ≡ addₘ i x m.
Proof. unfold addₘ; smash. Qed.

Theorem add_sym i j x y (m : t k v) :
  ~ eq i j → addₘ i x (addₘ j y m) ≡ addₘ j y (addₘ i x m).
Proof.
  unfold addₘ; smash.
  all: rewrite e, e0 in H0; elimtype False; now apply H0.
Qed.

Theorem remove_idem i (m : t k v) :
  removeₘ i (removeₘ i m) ≡ removeₘ i m.
Proof. unfold removeₘ; smash. Qed.

Theorem remove_add i x (m : t k v) :
  i ↦ _ ∉ m → removeₘ i (addₘ i x m) ≡ m.
Proof.
  unfold removeₘ, addₘ; smash.
  rewrite <- e in H1; firstorder eauto.
Qed.

Theorem remove_add_present i x (m : t k v) :
  i ↦ x ∈ m → removeₘ i (addₘ i x m) ≡ removeₘ i m.
Proof. unfold removeₘ, addₘ; smash. Qed.

Theorem add_remove i x (m : t k v) :
  i ↦ x ∈ m → addₘ i x (removeₘ i m) ≡ m.
Proof.
  unfold removeₘ, addₘ; smash.
  - now rewrite <- e.
  - rewrite <- e in H1; firstorder eauto.
Qed.

Theorem add_remove_absent i x (m : t k v) :
  i ↦ _ ∉ m → addₘ i x (removeₘ i m) ≡ addₘ i x m.
Proof. unfold removeₘ, addₘ; smash. Qed.

End Facts.

End MapFacts.

(************************************************************************
 ** Type class that links a map representation with the semantic model.
 ************************************************************************)

Module MapSound.

Module Import M := MapModel.
Module Import F := MapFacts.

Reserved Notation "⟦ m ⟧" (at level 4).

(** Something is a map if it denotes into the semantic model of partial maps,
    and if that denotation is homomorphic over all map operations. *)
Class IsMap {key : Type} {repr : Type → Type} (M : Map key repr) := {
  map_setoid {elt} :> Setoid (repr elt);

  denote {elt} : repr elt → M.t key elt where "⟦ m ⟧" := (denote m);

  (* Two map representations are equivalent if they denote the same model.

     This can be used to transport theorem statements based on equivalence of
     representations to a statement on models, which we can rewrite using the
     theorems of [IsMap]. *)
  equivalence_holds {elt} (m1 m2 : repr elt) :
    (denote m1 ≡ denote m2) ↔ (m1 == m2);

  key_decidable :> EqDec key;

  addₕ (i : key) `(x : elt) (m : repr elt) :
    ⟦ add i x m ⟧ ≡ addₘ i x ⟦ m ⟧
}.

Notation "⟦ m ⟧" := (denote m) (at level 4).

Arguments denote {_ _ _ _} _.

End MapSound.

(************************************************************************
 ** Prove that Coq's FMapAVL library correctly implements a map.
 ************************************************************************)

(* WSfun provides an algebra for partial maps, but without any semantics,
   rather just a set of theorems upon an axiomatic basis. The role of
   PartialMap is to present a semantic model for partial maps, and map which
   denotes into this model should be able to transport its proof terms. I.e.,
   proofs should be done in the domain of partial maps as functions, and not
   in the domain of an efficient representation for partial maps. *)
Module FMapAVL_Map (E : OrderedType) (B : HasEqDec E).

Module Import W := FMapAVL.Make E.

Program Instance E_is_EqDec : EqDec W.E.t := {|
  eq := W.E.eq;
  eq_dec := W.E.eq_dec;
|}.

Program Instance FMapAVL_Map : Map W.E.t W.t := {|
  PartialMap.add := λ _ i, add i
|}.

Module F := WFacts_fun E W.

Program Instance FMapAVL_IsMap : MapSound.IsMap FMapAVL_Map := {|
  MapSound.map_setoid := λ _, {| SetoidClass.equiv := Equal |};
  MapSound.denote := λ _ m i v, MapsTo i v m;
|}.
Next Obligation.
  unfold MapSound.M.equiv.
  split; intro;
  now apply F.Equal_mapsto_iff.
Qed.
Next Obligation.
  unfold MapModel.addₘ.
  split; intros.
  - apply F.add_mapsto_iff in H.
    destruct H.
    + destruct H; subst.
      destruct (eq_dec i k); auto.
      contradiction.
    + destruct H.
      destruct (eq_dec i k); auto.
      contradiction.
  - destruct (eq_dec i k); subst; auto.
    + apply F.add_mapsto_iff.
      constructor; auto.
    + apply F.add_mapsto_iff.
      right; split; auto.
Qed.

End FMapAVL_Map.

(************************************************************************
 ** Simple example of a Finite inductive type.
 ************************************************************************)

Inductive Traffic := Red | Yellow | Green.

Definition Traffic_Finite : Finite Traffic.
Proof.
  exists 3.
  unshelve esplit.
  - constructor.
    + intros.
      destruct H.
      * exact F1.
      * exact (FS F1).
      * exact (FS (FS F1)).
    + intros.
      dependent destruction H; [exact Red|].
      dependent destruction H; [exact Yellow|].
      dependent destruction H; [exact Green|].
      inversion H.
  - unfold compose; simpl.
    split; extensionality x;
    repeat (dependent destruction x; simpl; auto).
Defined.

Compute enumerate (F:=Traffic_Finite).
*)

(************************************************************************
 ** END OF FILE
 ************************************************************************)

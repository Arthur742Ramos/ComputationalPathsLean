/-
# Topos-like Structures via Computational Paths

This module formalizes topos-like constructions using computational paths:
subobject classifiers as path predicates, power objects, internal logic via paths,
characteristic maps, truth values as path properties, exponentials in path categories.

## References

* Mac Lane–Moerdijk, *Sheaves in Geometry and Logic* (1992)
* Johnstone, *Sketches of an Elephant* (2002)
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Category
namespace ToposPaths

open ComputationalPaths.Path

universe u

-- ============================================================
-- §1  Truth Values as Path Properties
-- ============================================================

/-- A truth value in the path-topos: a Bool with its reflexive path witness. -/
structure PathTruth where
  val : Bool

/-- The "true" truth value. -/
def trueTV : PathTruth := ⟨true⟩

/-- The "false" truth value. -/
def falseTV : PathTruth := ⟨false⟩

/-- Every truth value has a reflexive path witness. -/
def truth_witness (tv : PathTruth) : Path tv.val tv.val := Path.refl tv.val

-- ============================================================
-- §2  Subobject Classifier via Paths
-- ============================================================

/-- A subobject classifier Ω in the path setting:
    classifying predicates on a type A via Bool-valued functions. -/
structure SubobjClassifier (A : Type u) where
  classify : A → Bool

/-- Build a subobject classifier from any predicate. -/
def classifierOfPred (p : A → Bool) : SubobjClassifier A where
  classify := p

/-- Characteristic map: reflexive path on the classification. -/
def charMap (sc : SubobjClassifier A) (a : A) : Path (sc.classify a) (sc.classify a) :=
  Path.refl (sc.classify a)

/-- Two classifiers with the same predicate yield path-connected classifications. -/
def classifier_path_of_eq {A : Type u} (sc1 sc2 : SubobjClassifier A)
    (h : ∀ a, sc1.classify a = sc2.classify a) (a : A) :
    Path (sc1.classify a) (sc2.classify a) :=
  Path.ofEq (h a)

/-- Classifier paths compose via trans. -/
theorem classifier_path_trans {A : Type u}
    (sc1 sc2 sc3 : SubobjClassifier A)
    (h12 : ∀ a, sc1.classify a = sc2.classify a)
    (h23 : ∀ a, sc2.classify a = sc3.classify a) (a : A) :
    (Path.trans (classifier_path_of_eq sc1 sc2 h12 a)
                (classifier_path_of_eq sc2 sc3 h23 a)).proof =
    (classifier_path_of_eq sc1 sc3 (fun x => (h12 x).trans (h23 x)) a).proof := by
  simp

-- ============================================================
-- §3  Power Objects via Path Predicates
-- ============================================================

/-- A power object: the type of all subobject classifiers on A. -/
def PowerObj (A : Type u) := SubobjClassifier A

/-- Membership predicate via the classifier. -/
def pathMember (pw : PowerObj A) (a : A) : Bool :=
  pw.classify a

/-- Membership is stable under path identity via congrArg. -/
def member_stable {A : Type u} (pw : PowerObj A) (a b : A)
    (p : Path a b) : Path (pathMember pw a) (pathMember pw b) :=
  Path.congrArg (pathMember pw) p

/-- Singleton embedding into the power object. -/
def singletonEmbed [DecidableEq A] (a : A) : PowerObj A where
  classify := fun x => decide (x = a)

/-- The singleton classifier classifies the element itself as true. -/
theorem singleton_self [DecidableEq A] (a : A) :
    (singletonEmbed a).classify a = true := by
  simp [singletonEmbed]

/-- Singleton membership is transported along paths. -/
def singleton_transport [DecidableEq A] {a b : A}
    (p : Path a b) : Path ((singletonEmbed a).classify a)
                          ((singletonEmbed a).classify b) :=
  Path.congrArg (singletonEmbed a).classify p

-- ============================================================
-- §4  Internal Logic via Paths
-- ============================================================

/-- Internal conjunction of path truth values. -/
def pathAnd (a b : PathTruth) : PathTruth where
  val := a.val && b.val

/-- Internal disjunction of path truth values. -/
def pathOr (a b : PathTruth) : PathTruth where
  val := a.val || b.val

/-- Internal negation of path truth values. -/
def pathNot (a : PathTruth) : PathTruth where
  val := !a.val

/-- Internal implication of path truth values. -/
def pathImpl (a b : PathTruth) : PathTruth where
  val := !a.val || b.val

/-- Conjunction is commutative via paths. -/
def pathAnd_comm (a b : PathTruth) :
    Path (pathAnd a b).val (pathAnd b a).val :=
  Path.ofEq (Bool.and_comm a.val b.val)

/-- Disjunction is commutative via paths. -/
def pathOr_comm (a b : PathTruth) :
    Path (pathOr a b).val (pathOr b a).val :=
  Path.ofEq (Bool.or_comm a.val b.val)

/-- Double negation elimination as a path. -/
def pathNot_not (a : PathTruth) :
    Path (pathNot (pathNot a)).val a.val :=
  Path.ofEq (Bool.not_not a.val)

/-- And with true is identity. -/
def pathAnd_true (a : PathTruth) :
    Path (pathAnd a trueTV).val a.val :=
  Path.ofEq (Bool.and_true a.val)

/-- Or with false is identity. -/
def pathOr_false (a : PathTruth) :
    Path (pathOr a falseTV).val a.val :=
  Path.ofEq (Bool.or_false a.val)

/-- And is associative. -/
def pathAnd_assoc (a b c : PathTruth) :
    Path (pathAnd (pathAnd a b) c).val (pathAnd a (pathAnd b c)).val :=
  Path.ofEq (Bool.and_assoc a.val b.val c.val)

/-- Or is associative. -/
def pathOr_assoc (a b c : PathTruth) :
    Path (pathOr (pathOr a b) c).val (pathOr a (pathOr b c)).val :=
  Path.ofEq (Bool.or_assoc a.val b.val c.val)

/-- Distributivity: a ∧ (b ∨ c) = (a ∧ b) ∨ (a ∧ c). -/
theorem pathAnd_or_distrib (a b c : PathTruth) :
    (pathAnd a (pathOr b c)).val = (pathOr (pathAnd a b) (pathAnd a c)).val := by
  simp [pathAnd, pathOr, Bool.and_or_distrib_left]

-- ============================================================
-- §5  Exponentials in Path Categories
-- ============================================================

/-- An exponential object in the path category: functions with
    path-coherent behavior. -/
structure PathExponential (A B : Type u) where
  apply : A → B
  coherent : ∀ (a₁ a₂ : A), Path a₁ a₂ → Path (apply a₁) (apply a₂)

/-- Evaluation morphism for exponentials. -/
def evalMorphism (e : PathExponential A B) (a : A) : B :=
  e.apply a

/-- The evaluation is coherent with paths. -/
def eval_coherent (e : PathExponential A B) (a₁ a₂ : A)
    (p : Path a₁ a₂) : Path (evalMorphism e a₁) (evalMorphism e a₂) :=
  e.coherent a₁ a₂ p

/-- Identity exponential: the identity function. -/
def idExponential (A : Type u) : PathExponential A A where
  apply := id
  coherent := fun _ _ p => p

/-- Composition of exponentials. -/
def compExponential (e₁ : PathExponential A B) (e₂ : PathExponential B C) :
    PathExponential A C where
  apply := fun a => e₂.apply (e₁.apply a)
  coherent := fun a₁ a₂ p => e₂.coherent _ _ (e₁.coherent a₁ a₂ p)

/-- Identity exponential evaluates to the identity. -/
theorem idExponential_eval (a : A) :
    evalMorphism (idExponential A) a = a := rfl

/-- Composition exponential evaluates correctly. -/
theorem compExponential_eval (e₁ : PathExponential A B) (e₂ : PathExponential B C)
    (a : A) : evalMorphism (compExponential e₁ e₂) a = e₂.apply (e₁.apply a) := rfl

/-- Exponential coherence on refl yields refl-like path. -/
theorem idExponential_coherent_refl (a : A) :
    (idExponential A).coherent a a (Path.refl a) = Path.refl a := rfl

-- ============================================================
-- §6  Characteristic Maps and Pullbacks
-- ============================================================

/-- A pullback square in path terms: given f : A → C, g : B → C,
    the pullback consists of pairs (a, b) with f a = g b. -/
structure PathPullback (A B C : Type u) (f : A → C) (g : B → C) where
  fst : A
  snd : B
  comm : Path (f fst) (g snd)

/-- Projection from pullback to A, lifted through congrArg. -/
def pullback_fst_path {A B C : Type u} {f : A → C} {g : B → C}
    (pb₁ pb₂ : PathPullback A B C f g)
    (ha : Path pb₁.fst pb₂.fst) : Path (f pb₁.fst) (f pb₂.fst) :=
  Path.congrArg f ha

/-- Projection from pullback to B, lifted through congrArg. -/
def pullback_snd_path {A B C : Type u} {f : A → C} {g : B → C}
    (pb₁ pb₂ : PathPullback A B C f g)
    (hb : Path pb₁.snd pb₂.snd) : Path (g pb₁.snd) (g pb₂.snd) :=
  Path.congrArg g hb

/-- The pullback of the identity: fst = snd. -/
def pullbackDiag_path (A : Type u) (pb : PathPullback A A A id id) :
    Path pb.fst pb.snd := pb.comm

/-- Pullback commutativity: the square commutes via symm+trans. -/
theorem pullback_square_commutes {A B C : Type u} {f : A → C} {g : B → C}
    (pb : PathPullback A B C f g) :
    (Path.trans pb.comm (Path.symm pb.comm)).proof = rfl := by
  simp

-- ============================================================
-- §7  Subobject Lattice
-- ============================================================

/-- Meet of two subobject classifiers (intersection). -/
def subObjMeet (sc1 sc2 : SubobjClassifier A) : SubobjClassifier A where
  classify := fun a => sc1.classify a && sc2.classify a

/-- Join of two subobject classifiers (union). -/
def subObjJoin (sc1 sc2 : SubobjClassifier A) : SubobjClassifier A where
  classify := fun a => sc1.classify a || sc2.classify a

/-- Complement of a subobject classifier. -/
def subObjComplement (sc : SubobjClassifier A) : SubobjClassifier A where
  classify := fun a => !sc.classify a

/-- Meet is commutative. -/
def subObjMeet_comm (sc1 sc2 : SubobjClassifier A) (a : A) :
    Path ((subObjMeet sc1 sc2).classify a) ((subObjMeet sc2 sc1).classify a) :=
  Path.ofEq (Bool.and_comm (sc1.classify a) (sc2.classify a))

/-- Join is commutative. -/
def subObjJoin_comm (sc1 sc2 : SubobjClassifier A) (a : A) :
    Path ((subObjJoin sc1 sc2).classify a) ((subObjJoin sc2 sc1).classify a) :=
  Path.ofEq (Bool.or_comm (sc1.classify a) (sc2.classify a))

/-- Double complement returns the original classifier. -/
def subObjComplement_invol (sc : SubobjClassifier A) (a : A) :
    Path ((subObjComplement (subObjComplement sc)).classify a) (sc.classify a) :=
  Path.ofEq (Bool.not_not (sc.classify a))

/-- Total subobject: everything is classified as true. -/
def totalSubObj (A : Type u) : SubobjClassifier A where
  classify := fun _ => true

/-- Empty subobject: nothing is classified as true. -/
def emptySubObj (A : Type u) : SubobjClassifier A where
  classify := fun _ => false

/-- Meet with total is identity. -/
def subObjMeet_total (sc : SubobjClassifier A) (a : A) :
    Path ((subObjMeet sc (totalSubObj A)).classify a) (sc.classify a) :=
  Path.ofEq (Bool.and_true (sc.classify a))

/-- Meet with empty is empty. -/
def subObjMeet_empty (sc : SubobjClassifier A) (a : A) :
    Path ((subObjMeet sc (emptySubObj A)).classify a) false :=
  Path.ofEq (Bool.and_false (sc.classify a))

/-- Join with total is total. -/
def subObjJoin_total (sc : SubobjClassifier A) (a : A) :
    Path ((subObjJoin sc (totalSubObj A)).classify a) true :=
  Path.ofEq (Bool.or_true (sc.classify a))

/-- Join with empty is identity. -/
def subObjJoin_empty (sc : SubobjClassifier A) (a : A) :
    Path ((subObjJoin sc (emptySubObj A)).classify a) (sc.classify a) :=
  Path.ofEq (Bool.or_false (sc.classify a))

-- ============================================================
-- §8  Classifier Functoriality
-- ============================================================

/-- Classifier paths via congrArg. -/
def classifier_congrArg {A : Type u} (sc : SubobjClassifier A)
    {a b : A} (p : Path a b) :
    Path (sc.classify a) (sc.classify b) :=
  Path.congrArg sc.classify p

/-- Classifier congrArg respects trans. -/
theorem classifier_congrArg_trans {A : Type u} (sc : SubobjClassifier A)
    {a b c : A} (p : Path a b) (q : Path b c) :
    Path.congrArg sc.classify (Path.trans p q) =
    Path.trans (Path.congrArg sc.classify p) (Path.congrArg sc.classify q) := by
  cases p with
  | mk sp hp =>
    cases q with
    | mk sq hq =>
      cases hp; cases hq; simp [Path.congrArg, Path.trans, List.map_append]

/-- Classifier congrArg respects refl. -/
theorem classifier_congrArg_refl {A : Type u} (sc : SubobjClassifier A) (a : A) :
    Path.congrArg sc.classify (Path.refl a) = Path.refl (sc.classify a) := by
  simp [Path.congrArg]

/-- Classifier congrArg respects symm. -/
theorem classifier_congrArg_symm {A : Type u} (sc : SubobjClassifier A)
    {a b : A} (p : Path a b) :
    Path.congrArg sc.classify (Path.symm p) =
    Path.symm (Path.congrArg sc.classify p) := by
  cases p with
  | mk sp hp =>
    cases hp; simp [Path.congrArg, Path.symm]

-- ============================================================
-- §9  Internal Heyting Algebra
-- ============================================================

/-- Heyting implication for subobject classifiers. -/
def heytingImpl (sc1 sc2 : SubobjClassifier A) : SubobjClassifier A where
  classify := fun a => !sc1.classify a || sc2.classify a

/-- Modus ponens: if a ∈ sc1 and sc1 → sc2, then a ∈ sc2. -/
theorem heyting_modus_ponens (sc1 sc2 : SubobjClassifier A) (a : A)
    (h1 : sc1.classify a = true) (h2 : (heytingImpl sc1 sc2).classify a = true) :
    sc2.classify a = true := by
  simp [heytingImpl] at h2
  cases h2 with
  | inl h => rw [h1] at h; simp at h
  | inr h => exact h

/-- Implication to total is total. -/
theorem heytingImpl_total (sc : SubobjClassifier A) (a : A) :
    (heytingImpl sc (totalSubObj A)).classify a = true := by
  simp [heytingImpl, totalSubObj]

/-- Implication from empty is total. -/
theorem heytingImpl_from_empty (sc : SubobjClassifier A) (a : A) :
    (heytingImpl (emptySubObj A) sc).classify a = true := by
  simp [heytingImpl, emptySubObj]

-- ============================================================
-- §10  Path Topos Category
-- ============================================================

/-- A path topos: a category with the structure needed for topos constructions. -/
structure PathTopos where
  Obj : Type u
  Hom : Obj → Obj → Type u
  id : (a : Obj) → Hom a a
  comp : {a b c : Obj} → Hom a b → Hom b c → Hom a c
  assoc : ∀ {a b c d : Obj} (f : Hom a b) (g : Hom b c) (h : Hom c d),
    comp (comp f g) h = comp f (comp g h)
  id_comp : ∀ {a b : Obj} (f : Hom a b), comp (id a) f = f
  comp_id : ∀ {a b : Obj} (f : Hom a b), comp f (id b) = f

/-- The path topos of a type A: objects are elements, morphisms are paths. -/
def pathToposOf (A : Type u) : PathTopos where
  Obj := A
  Hom := fun a b => Path a b
  id := fun a => Path.refl a
  comp := fun f g => Path.trans f g
  assoc := fun f g h => by simp
  id_comp := fun f => by simp
  comp_id := fun f => by simp

/-- Symmetry in a path topos gives inverses at the proof level. -/
theorem pathTopos_symm_trans_proof (A : Type u) (a b : A) (p : Path a b) :
    ((pathToposOf A).comp p (Path.symm p)).proof = ((pathToposOf A).id a).proof := by
  simp

/-- Identity composed with itself is identity. -/
theorem pathTopos_id_self (A : Type u) (a : A) :
    (pathToposOf A).comp ((pathToposOf A).id a) ((pathToposOf A).id a) =
    (pathToposOf A).id a := by
  simp [pathToposOf]

/-- Symm then trans recovers identity at the proof level. -/
theorem pathTopos_trans_symm_proof (A : Type u) (a b : A) (p : Path a b) :
    ((pathToposOf A).comp (Path.symm p) p).proof = ((pathToposOf A).id b).proof := by
  simp

-- ============================================================
-- §11  Transport in Topos Structures
-- ============================================================

/-- Transport a truth value along a Bool path. -/
def transportTruth (_p : Path true true) : PathTruth := trueTV

/-- Transport preserves truth value on refl. -/
theorem transportTruth_refl :
    transportTruth (Path.refl true) = trueTV := rfl

/-- Subobject meet is idempotent. -/
def subObjMeet_idem (sc : SubobjClassifier A) (a : A) :
    Path ((subObjMeet sc sc).classify a) (sc.classify a) :=
  Path.ofEq (Bool.and_self (sc.classify a))

/-- Subobject join is idempotent. -/
def subObjJoin_idem (sc : SubobjClassifier A) (a : A) :
    Path ((subObjJoin sc sc).classify a) (sc.classify a) :=
  Path.ofEq (Bool.or_self (sc.classify a))

/-- Complement of total is empty. -/
def subObjComplement_total (A : Type u) (a : A) :
    Path ((subObjComplement (totalSubObj A)).classify a) false :=
  Path.ofEq rfl

/-- Complement of empty is total. -/
def subObjComplement_empty (A : Type u) (a : A) :
    Path ((subObjComplement (emptySubObj A)).classify a) true :=
  Path.ofEq rfl

end ToposPaths
end Category
end Path
end ComputationalPaths

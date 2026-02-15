/-
# Topos-like Structures via Computational Paths

Subobject classifiers, power objects, internal logic, exponentials in path
categories, characteristic maps, truth values as path properties.

## References

- Mac Lane–Moerdijk, *Sheaves in Geometry and Logic* (1992)
- Johnstone, *Sketches of an Elephant* (2002)
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Category
namespace ToposPaths

universe u v

/-! ## §1  Path-based subobject classifier -/

/-- A subobject classifier Ω for a path-based category on `A`.
    The carrier lives in `Type u` so it can serve as sections of a presheaf. -/
structure SubobjectClassifier (A : Type u) where
  /-- Carrier of truth values. -/
  Ω : Type u
  /-- Distinguished "true" element. -/
  trueVal : Ω
  /-- Classify a predicate on `A` into a map `A → Ω`. -/
  chi : (A → Prop) → (A → Ω)
  /-- `chi P a = trueVal` whenever `P a` holds. -/
  chi_true : ∀ (P : A → Prop) (a : A), P a → chi P a = trueVal

/-- Paths between truth values: transport of `trueVal` along `Path`. -/
def truthTransport {A : Type u} (sc : SubobjectClassifier A)
    {a b : A} (p : Path a b) :
    Path (sc.chi (fun x => x = a) a) (sc.chi (fun x => x = a) a) :=
  Path.refl _

/-- Transport of truth-value classification is trivial (UIP). -/
theorem truthTransport_eq_refl {A : Type u} (sc : SubobjectClassifier A)
    {a b : A} (p : Path a b) :
    truthTransport sc p = Path.refl _ :=
  rfl

/-- `chi` at `trueVal` for a trivially true predicate. -/
theorem chi_trueVal_trivial {A : Type u} (sc : SubobjectClassifier A) (a : A) :
    sc.chi (fun _ => True) a = sc.trueVal :=
  sc.chi_true _ a trivial

/-- Path between truth-value witnesses: any two proofs of `trueVal = trueVal`
    agree (Subsingleton of equality). -/
theorem trueVal_path_unique {A : Type u} (sc : SubobjectClassifier A)
    (h₁ h₂ : sc.trueVal = sc.trueVal) : h₁ = h₂ :=
  Subsingleton.elim h₁ h₂

/-! ## §2  Characteristic maps via Path -/

/-- Characteristic map from a decidable subset, lifted through `Path`. -/
def charMapPath {A : Type u} (sc : SubobjectClassifier A)
    (P : A → Prop) {a b : A} (p : Path a b) :
    Path (sc.chi P a) (sc.chi P b) :=
  Path.ofEq (_root_.congrArg (sc.chi P) p.proof)

/-- Characteristic map along `refl` is `refl`. -/
theorem charMapPath_refl {A : Type u} (sc : SubobjectClassifier A)
    (P : A → Prop) (a : A) :
    charMapPath sc P (Path.refl a) = Path.ofEq rfl := by
  simp [charMapPath, Path.congrArg, Path.ofEq]

/-- Characteristic map along `trans` composes. -/
theorem charMapPath_trans {A : Type u} (sc : SubobjectClassifier A)
    (P : A → Prop) {a b c : A} (p : Path a b) (q : Path b c) :
    (charMapPath sc P (Path.trans p q)).proof =
    (Path.trans (charMapPath sc P p) (charMapPath sc P q)).proof := by
  simp

/-- Characteristic map along `symm` is symmetric. -/
theorem charMapPath_symm {A : Type u} (sc : SubobjectClassifier A)
    (P : A → Prop) {a b : A} (p : Path a b) :
    (charMapPath sc P (Path.symm p)).proof =
    (Path.symm (charMapPath sc P p)).proof := by
  simp

/-- `congrArg` of `chi P` factors through `charMapPath`. -/
theorem congrArg_chi_eq_charMap {A : Type u} (sc : SubobjectClassifier A)
    (P : A → Prop) {a b : A} (p : Path a b) :
    (Path.congrArg (sc.chi P) p).proof = (charMapPath sc P p).proof := by
  simp [charMapPath]

/-! ## §3  Power objects -/

/-- A power object ℙ(A) in a path category.  The carrier is `A → Prop`
    (the "set of subsets"), equipped with membership and extensionality. -/
structure PowerObject (A : Type u) where
  carrier : Type u
  mem : A → carrier → Prop
  ext : ∀ s t : carrier, (∀ a, mem a s ↔ mem a t) → s = t

/-- Standard power object: function space `A → Prop`. -/
def stdPower (A : Type u) : PowerObject A where
  carrier := A → Prop
  mem := fun a S => S a
  ext := fun s t h => funext fun a => propext (h a)

/-- Membership in the standard power object reduces to application. -/
theorem stdPower_mem {A : Type u} (a : A) (S : A → Prop) :
    (stdPower A).mem a S ↔ S a :=
  Iff.rfl

/-- Extensionality for the standard power object. -/
theorem stdPower_ext {A : Type u} (S T : (stdPower A).carrier)
    (h : ∀ a, S a ↔ T a) : S = T :=
  (stdPower A).ext S T h

/-- Singleton subset via Path equality. -/
def singleton {A : Type u} (a : A) : (stdPower A).carrier :=
  fun x => x = a

/-- Membership in a singleton is Path-equality. -/
theorem mem_singleton {A : Type u} (a x : A) :
    (stdPower A).mem x (singleton a) ↔ x = a :=
  Iff.rfl

/-- Transport of a subset along a Path in the base. -/
def powerTransport {A : Type u} {a b : A} (p : Path a b)
    (S : (stdPower A).carrier) : (stdPower A).carrier :=
  S   -- base transport is trivial since A → Prop is constant in the base

/-- Power-transport is the identity (constant family). -/
theorem powerTransport_eq {A : Type u} {a b : A} (p : Path a b)
    (S : (stdPower A).carrier) :
    powerTransport p S = S :=
  rfl

/-! ## §4  Internal logic -/

/-- Meet (conjunction) of two subsets in the power object. -/
def meetSubset {A : Type u} (S T : (stdPower A).carrier) : (stdPower A).carrier :=
  fun a => S a ∧ T a

/-- Join (disjunction) of two subsets. -/
def joinSubset {A : Type u} (S T : (stdPower A).carrier) : (stdPower A).carrier :=
  fun a => S a ∨ T a

/-- Implication of two subsets (Heyting implication). -/
def implSubset {A : Type u} (S T : (stdPower A).carrier) : (stdPower A).carrier :=
  fun a => S a → T a

/-- Meet is idempotent. -/
theorem meetSubset_idem {A : Type u} (S : (stdPower A).carrier) :
    meetSubset S S = S :=
  funext fun _ => propext ⟨And.left, fun h => ⟨h, h⟩⟩

/-- Meet is commutative. -/
theorem meetSubset_comm {A : Type u} (S T : (stdPower A).carrier) :
    meetSubset S T = meetSubset T S :=
  funext fun _ => propext ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a⟩⟩

/-- Join is idempotent. -/
theorem joinSubset_idem {A : Type u} (S : (stdPower A).carrier) :
    joinSubset S S = S :=
  funext fun _ => propext ⟨fun h => h.elim id id, Or.inl⟩

/-- Join is commutative. -/
theorem joinSubset_comm {A : Type u} (S T : (stdPower A).carrier) :
    joinSubset S T = joinSubset T S :=
  funext fun _ => propext ⟨Or.symm, Or.symm⟩

/-- Meet distributes over join. -/
theorem meetSubset_distrib_join {A : Type u} (S T U : (stdPower A).carrier) :
    meetSubset S (joinSubset T U) = joinSubset (meetSubset S T) (meetSubset S U) :=
  funext fun _ => propext
    ⟨fun ⟨hs, htu⟩ => htu.elim (fun ht => Or.inl ⟨hs, ht⟩) (fun hu => Or.inr ⟨hs, hu⟩),
     fun h => h.elim (fun ⟨hs, ht⟩ => ⟨hs, Or.inl ht⟩) (fun ⟨hs, hu⟩ => ⟨hs, Or.inr hu⟩)⟩

/-- Path between subsets induced by propositional extensionality. -/
def subsetPath {A : Type u} (S T : (stdPower A).carrier)
    (h : ∀ a, S a ↔ T a) : Path S T :=
  Path.ofEq (stdPower_ext S T h)

/-! ## §5  Exponentials in the path category -/

/-- Exponential object `[B, C]` in the path category. -/
structure PathExponential (B C : Type u) where
  carrier : Type u
  eval : carrier × B → C
  curry : ∀ {A : Type u}, (A × B → C) → (A → carrier)
  beta : ∀ {A : Type u} (f : A × B → C) (a : A) (b : B),
    eval (curry f a, b) = f (a, b)

/-- Standard exponential using function types. -/
def stdExponential (B C : Type u) : PathExponential B C where
  carrier := B → C
  eval := fun ⟨f, b⟩ => f b
  curry := fun f a b => f (a, b)
  beta := fun _ _ _ => rfl

/-- Evaluation computes correctly. -/
theorem stdExp_eval {B C : Type u} (f : B → C) (b : B) :
    (stdExponential B C).eval (f, b) = f b :=
  rfl

/-- Beta reduction for the standard exponential. -/
theorem stdExp_beta {A B C : Type u} (f : A × B → C) (a : A) (b : B) :
    (stdExponential B C).eval ((stdExponential B C).curry f a, b) = f (a, b) :=
  rfl

/-- Curry of eval is the identity. -/
theorem stdExp_eta {B C : Type u} (g : (stdExponential B C).carrier) :
    (stdExponential B C).curry (fun ⟨f, b⟩ => (stdExponential B C).eval (f, b)) g = g := by
  rfl

/-- Path-transport of exponential objects is the identity (constant family). -/
theorem expTransport_trivial {B C : Type u} {a b : A}
    (p : Path a b) (f : (stdExponential B C).carrier) :
    Path.transport (D := fun _ => (stdExponential B C).carrier) p f = f := by
  cases p with | mk _ pr => cases pr; rfl

/-! ## §6  Cartesian structure -/

/-- Product in the path category. -/
def pathProd (A B : Type u) := A × B

/-- First projection. -/
def pathFst {A B : Type u} (p : pathProd A B) : A := p.1

/-- Second projection. -/
def pathSnd {A B : Type u} (p : pathProd A B) : B := p.2

/-- Pairing. -/
def pathPair {X A B : Type u} (f : X → A) (g : X → B) (x : X) : pathProd A B :=
  (f x, g x)

/-- Fst ∘ pair = f. -/
theorem pathFst_pair {X A B : Type u} (f : X → A) (g : X → B) (x : X) :
    pathFst (pathPair f g x) = f x :=
  rfl

/-- Snd ∘ pair = g. -/
theorem pathSnd_pair {X A B : Type u} (f : X → A) (g : X → B) (x : X) :
    pathSnd (pathPair f g x) = g x :=
  rfl

/-- Uniqueness of pairing. -/
theorem pathPair_eta {A B : Type u} (p : pathProd A B) :
    pathPair pathFst pathSnd p = p := by
  cases p; rfl

/-- Path in a product is a pair of paths. -/
def prodPath {A B : Type u} {a₁ a₂ : A} {b₁ b₂ : B}
    (pa : Path a₁ a₂) (pb : Path b₁ b₂) :
    Path (a₁, b₁) (a₂, b₂) :=
  Path.ofEq (Prod.ext pa.proof pb.proof)

/-- Product path along refl is refl. -/
theorem prodPath_refl {A B : Type u} (a : A) (b : B) :
    prodPath (Path.refl a) (Path.refl b) = Path.ofEq rfl := by
  simp [prodPath]

/-- Congruence of fst along a product path. -/
theorem congrArg_fst_prodPath {A B : Type u} {a₁ a₂ : A} {b₁ b₂ : B}
    (pa : Path a₁ a₂) (pb : Path b₁ b₂) :
    (Path.congrArg Prod.fst (prodPath pa pb)).proof = pa.proof := by
  cases pa with | mk _ pra => cases pra; cases pb with | mk _ prb => cases prb; rfl

/-- Congruence of snd along a product path. -/
theorem congrArg_snd_prodPath {A B : Type u} {a₁ a₂ : A} {b₁ b₂ : B}
    (pa : Path a₁ a₂) (pb : Path b₁ b₂) :
    (Path.congrArg Prod.snd (prodPath pa pb)).proof = pb.proof := by
  cases pa with | mk _ pra => cases pra; cases pb with | mk _ prb => cases prb; rfl

/-! ## §7  Truth-value paths -/

/-- Truth values: Prop lifted into Type. -/
structure TruthVal where
  val : Prop

/-- The true truth value. -/
def tvTrue : TruthVal := ⟨True⟩

/-- The false truth value. -/
def tvFalse : TruthVal := ⟨False⟩

/-- Conjunction of truth values. -/
def tvAnd (p q : TruthVal) : TruthVal := ⟨p.val ∧ q.val⟩

/-- Disjunction of truth values. -/
def tvOr (p q : TruthVal) : TruthVal := ⟨p.val ∨ q.val⟩

/-- Implication of truth values. -/
def tvImpl (p q : TruthVal) : TruthVal := ⟨p.val → q.val⟩

/-- Path between truth values from an iff. -/
def tvPath (p q : TruthVal) (h : p.val ↔ q.val) : Path p q :=
  Path.ofEq (show p = q by cases p; cases q; simp only [TruthVal.mk.injEq]; exact propext h)

/-- tvTrue is a right unit for conjunction. -/
theorem tvAnd_true_right (p : TruthVal) :
    tvAnd p tvTrue = p := by
  cases p; simp only [tvAnd, tvTrue]
  congr 1; exact propext ⟨And.left, fun h => ⟨h, trivial⟩⟩

/-- tvTrue is a left unit for conjunction. -/
theorem tvAnd_true_left (p : TruthVal) :
    tvAnd tvTrue p = p := by
  cases p; simp only [tvAnd, tvTrue]
  congr 1; exact propext ⟨And.right, fun h => ⟨trivial, h⟩⟩

/-- Conjunction is commutative. -/
theorem tvAnd_comm (p q : TruthVal) :
    tvAnd p q = tvAnd q p := by
  cases p; cases q; simp only [tvAnd]
  congr 1; exact propext ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a⟩⟩

/-- Conjunction is idempotent. -/
theorem tvAnd_idem (p : TruthVal) :
    tvAnd p p = p := by
  cases p; simp only [tvAnd]
  congr 1; exact propext ⟨And.left, fun h => ⟨h, h⟩⟩

/-- Transport of a truth value along any Path is trivial (constant family). -/
theorem tvTransport_const {X : Type u} {a b : X}
    (p : Path a b) (t : TruthVal) :
    Path.transport (D := fun _ => TruthVal) p t = t := by
  cases p with | mk _ pr => cases pr; rfl

end ToposPaths
end Category
end Path
end ComputationalPaths

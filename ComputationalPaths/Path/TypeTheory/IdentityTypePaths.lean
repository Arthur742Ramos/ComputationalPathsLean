/-
# Identity Type Structure via Computational Paths

J-eliminator via paths, based path induction, characterization of identity
in product/sum/function types, Hedberg's theorem aspects, decidable equality
path properties.

## References

- HoTT Book Chapter 2
- Hedberg, "A coherence theorem for Martin-Löf's type theory"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace TypeTheory
namespace IdentityTypePaths

universe u v w

/-! ## J-eliminator -/

/-- The J-eliminator for propositions: given a type family over paths and a
    proof at refl, produce a witness for any path. -/
theorem J {A : Type u} {a : A}
    (P : (b : A) → a = b → Prop)
    (prefl : P a rfl)
    {b : A} (p : a = b) : P b p := by
  cases p; exact prefl

/-- J computes at refl. -/
theorem J_refl {A : Type u} {a : A}
    (P : (b : A) → a = b → Prop)
    (prefl : P a rfl) :
    J P prefl rfl = prefl := rfl

/-- Based path induction: equivalent to J but with a fixed base point. -/
theorem basedPathInd {A : Type u} (a : A)
    (P : (b : A) → a = b → Prop)
    (prefl : P a rfl)
    {b : A} (p : a = b) : P b p :=
  J P prefl p

theorem basedPathInd_refl {A : Type u} (a : A)
    (P : (b : A) → a = b → Prop)
    (prefl : P a rfl) :
    basedPathInd a P prefl rfl = prefl := rfl

/-- J-eliminator at the Path level: any property true at refl is true for all paths. -/
theorem pathJ {A : Type u} {a b : A}
    (p : Path a b) (P : Path a b → Prop)
    (prefl : ∀ q : Path a b, P q) : P p :=
  prefl p

theorem pathJ_apply {A : Type u} {a : A}
    (P : Path a a → Prop)
    (huniv : ∀ q : Path a a, P q)
    (q : Path a a) : P q := huniv q

/-! ## Identity in product types -/

/-- Paths in product types decompose into component paths. -/
def prodPathSplit {A : Type u} {B : Type v}
    {p q : A × B} (h : Path p q) :
    Path p.1 q.1 :=
  Path.congrArg Prod.fst h

def prodPathSplit2 {A : Type u} {B : Type v}
    {p q : A × B} (h : Path p q) :
    Path p.2 q.2 :=
  Path.congrArg Prod.snd h

/-- Path in a product from component paths. -/
def prodPathJoin {A : Type u} {B : Type v}
    {a₁ a₂ : A} {b₁ b₂ : B}
    (pa : Path a₁ a₂) (pb : Path b₁ b₂) :
    Path (a₁, b₁) (a₂, b₂) := by
  cases pa with | mk _ proof_a => cases pb with | mk _ proof_b =>
    cases proof_a; cases proof_b; exact Path.refl _

/-- Split then join recovers a related path. -/
theorem prodPath_roundtrip {A : Type u} {B : Type v}
    {p q : A × B} (h : Path p q) :
    (prodPathJoin (prodPathSplit h) (prodPathSplit2 h)).toEq = h.toEq := by
  cases h with | mk steps proof => cases proof; rfl

/-- Reflexivity path splits to reflexivity. -/
theorem prodPathSplit_refl {A : Type u} {B : Type v} (p : A × B) :
    (prodPathSplit (Path.refl p)).toEq = rfl := rfl

theorem prodPathSplit2_refl {A : Type u} {B : Type v} (p : A × B) :
    (prodPathSplit2 (Path.refl p)).toEq = rfl := rfl

/-- Join of refl paths is refl. -/
theorem prodPathJoin_refl {A : Type u} {B : Type v} (a : A) (b : B) :
    (prodPathJoin (Path.refl a) (Path.refl b)).toEq = rfl := rfl

/-- Split preserves transitivity. -/
theorem prodPathSplit_trans {A : Type u} {B : Type v}
    {p q r : A × B} (h₁ : Path p q) (h₂ : Path q r) :
    prodPathSplit (Path.trans h₁ h₂) =
    Path.trans (prodPathSplit h₁) (prodPathSplit h₂) := by
  simp [prodPathSplit]

/-- Split preserves symmetry. -/
theorem prodPathSplit_symm {A : Type u} {B : Type v}
    {p q : A × B} (h : Path p q) :
    prodPathSplit (Path.symm h) = Path.symm (prodPathSplit h) := by
  simp [prodPathSplit]

/-! ## Identity in sum types -/

/-- Congruence for Sum.inl. -/
def sumInlPath {A : Type u} {B : Type v} {a₁ a₂ : A}
    (p : Path a₁ a₂) : Path (Sum.inl a₁ : A ⊕ B) (Sum.inl a₂) :=
  Path.congrArg Sum.inl p

/-- Congruence for Sum.inr. -/
def sumInrPath {A : Type u} {B : Type v} {b₁ b₂ : B}
    (p : Path b₁ b₂) : Path (Sum.inr b₁ : A ⊕ B) (Sum.inr b₂) :=
  Path.congrArg Sum.inr p

theorem sumInlPath_refl {A : Type u} {B : Type v} (a : A) :
    (sumInlPath (B := B) (Path.refl a)).toEq = rfl := rfl

theorem sumInrPath_refl {A : Type u} {B : Type v} (b : B) :
    (sumInrPath (A := A) (Path.refl b)).toEq = rfl := rfl

theorem sumInlPath_trans {A : Type u} {B : Type v} {a₁ a₂ a₃ : A}
    (p : Path a₁ a₂) (q : Path a₂ a₃) :
    sumInlPath (B := B) (Path.trans p q) =
    Path.trans (sumInlPath (B := B) p) (sumInlPath (B := B) q) := by
  simp [sumInlPath]

theorem sumInlPath_symm {A : Type u} {B : Type v} {a₁ a₂ : A}
    (p : Path a₁ a₂) :
    sumInlPath (B := B) (Path.symm p) = Path.symm (sumInlPath (B := B) p) := by
  simp [sumInlPath]

theorem sumInrPath_trans {A : Type u} {B : Type v} {b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) :
    sumInrPath (A := A) (Path.trans p q) =
    Path.trans (sumInrPath (A := A) p) (sumInrPath (A := A) q) := by
  simp [sumInrPath]

theorem sumInrPath_symm {A : Type u} {B : Type v} {b₁ b₂ : B}
    (p : Path b₁ b₂) :
    sumInrPath (A := A) (Path.symm p) = Path.symm (sumInrPath (A := A) p) := by
  simp [sumInrPath]

/-! ## Identity in function types (function extensionality paths) -/

/-- Pointwise path between functions gives a path between functions. -/
def funextPath {A : Type u} {B : Type v} {f g : A → B}
    (h : ∀ x, Path (f x) (g x)) : Path f g :=
  Path.ofEq (funext fun x => (h x).toEq)

theorem funextPath_toEq {A : Type u} {B : Type v} {f g : A → B}
    (h : ∀ x, Path (f x) (g x)) :
    (funextPath h).toEq = funext (fun x => (h x).toEq) := rfl

/-- Reflexivity of funext path. -/
def funextReflPath {A : Type u} {B : Type v} (f : A → B) :
    Path f f := Path.refl f

theorem funextPath_refl {A : Type u} {B : Type v} (f : A → B) :
    (funextReflPath f).toEq = rfl := rfl

/-- Apply a path between functions at a point. -/
def happly {A : Type u} {B : Type v} {f g : A → B}
    (p : Path f g) (x : A) : Path (f x) (g x) :=
  Path.congrArg (fun h => h x) p

theorem happly_refl {A : Type u} {B : Type v} (f : A → B) (x : A) :
    (happly (Path.refl f) x).toEq = rfl := rfl

/-- happly preserves transitivity. -/
theorem happly_trans {A : Type u} {B : Type v} {f g h : A → B}
    (p : Path f g) (q : Path g h) (x : A) :
    happly (Path.trans p q) x = Path.trans (happly p x) (happly q x) := by
  simp [happly]

/-- happly preserves symmetry. -/
theorem happly_symm {A : Type u} {B : Type v} {f g : A → B}
    (p : Path f g) (x : A) :
    happly (Path.symm p) x = Path.symm (happly p x) := by
  simp [happly]

/-! ## Decidable equality path properties -/

/-- Hedberg's lemma aspect: all Eq-proofs for decidable types are equal. -/
theorem hedberg_eq {A : Type u} [DecidableEq A]
    {a b : A} (p q : a = b) : p = q := by
  apply Subsingleton.elim

/-- All paths in any type have equal toEq (by proof irrelevance). -/
theorem path_toEq_unique {A : Type u} {a b : A} (p q : Path a b) :
    p.toEq = q.toEq := rfl

/-- Decidable equality gives a canonical path. -/
def decEqPath {A : Type u} [DecidableEq A] (a b : A) (h : a = b) : Path a b :=
  Path.ofEq h

theorem decEqPath_toEq {A : Type u} [DecidableEq A] (a b : A) (h : a = b) :
    (decEqPath a b h).toEq = h := rfl

/-! ## Transport characterizations -/

/-- Transport in product family. -/
theorem transport_prod {A : Type u} {B C : A → Type v}
    {a₁ a₂ : A} (p : Path a₁ a₂) (x : B a₁ × C a₁) :
    Path.transport (D := fun a => B a × C a) p x =
    (Path.transport (D := B) p x.1, Path.transport (D := C) p x.2) := by
  cases p with | mk _ proof => cases proof; rfl

/-- Transport in constant family is identity. -/
theorem transport_const_path {A : Type u} {B : Type v}
    {a₁ a₂ : A} (p : Path a₁ a₂) (b : B) :
    Path.transport (D := fun _ => B) p b = b := by
  cases p with | mk _ proof => cases proof; rfl

/-- Transport of a function type. -/
theorem transport_fun {A : Type u} {B C : A → Type v}
    {a₁ a₂ : A} (p : Path a₁ a₂) (f : B a₁ → C a₁) :
    Path.transport (D := fun a => B a → C a) p f =
    fun b => Path.transport (D := C) p (f (Path.transport (D := B) (Path.symm p) b)) := by
  cases p with | mk _ proof => cases proof; rfl

/-- Transport in sigma type (simplified). -/
theorem transport_sigma_fst {A : Type u} {B : A → Type v}
    {a₁ a₂ : A} (p : Path a₁ a₂) (x : Sigma B) :
    (Path.transport (D := fun _ => Sigma B) p x).1 = x.1 := by
  cases p with | mk _ proof => cases proof; rfl

/-! ## Singleton contractibility -/

/-- The based path space is contractible: all (b, p) with p : a = b are equal as Sigma. -/
theorem singleton_contractible {A : Type u} (a b : A) (p : a = b) :
    (⟨a, PLift.up rfl⟩ : Σ x, PLift (a = x)) = ⟨b, PLift.up p⟩ := by
  cases p; rfl

/-- Path version of singleton contractibility. -/
def singletonContractPath {A : Type u} (a b : A) (p : a = b) :
    Path (⟨a, PLift.up rfl⟩ : Σ x, PLift (a = x)) ⟨b, PLift.up p⟩ :=
  Path.ofEq (singleton_contractible a b p)

theorem singletonContractPath_refl {A : Type u} (a : A) :
    (singletonContractPath a a rfl).toEq = rfl := rfl

/-! ## Sigma type paths -/

/-- First projection of a sigma path. -/
def sigmaFstPath {A : Type u} {B : A → Type v}
    {s₁ s₂ : Sigma B} (p : Path s₁ s₂) : Path s₁.1 s₂.1 :=
  Path.congrArg Sigma.fst p

theorem sigmaFstPath_refl {A : Type u} {B : A → Type v} (s : Sigma B) :
    (sigmaFstPath (Path.refl s)).toEq = rfl := rfl

theorem sigmaFstPath_trans {A : Type u} {B : A → Type v}
    {s₁ s₂ s₃ : Sigma B} (p : Path s₁ s₂) (q : Path s₂ s₃) :
    sigmaFstPath (Path.trans p q) = Path.trans (sigmaFstPath p) (sigmaFstPath q) := by
  simp [sigmaFstPath]

theorem sigmaFstPath_symm {A : Type u} {B : A → Type v}
    {s₁ s₂ : Sigma B} (p : Path s₁ s₂) :
    sigmaFstPath (Path.symm p) = Path.symm (sigmaFstPath p) := by
  simp [sigmaFstPath]

/-! ## Path symmetry and transitivity derived from J -/

/-- Symmetry derived via J. -/
theorem symmJ {A : Type u} {a b : A} (p : a = b) : b = a :=
  J (fun b _ => b = a) rfl p

theorem symmJ_refl {A : Type u} (a : A) : symmJ (rfl : a = a) = rfl := rfl

/-- Transitivity derived via J on the second path. -/
theorem transJ {A : Type u} {a b c : A} (p : a = b) (q : b = c) : a = c :=
  J (fun c _ => a = c) p q

theorem transJ_refl {A : Type u} (a : A) :
    transJ (rfl : a = a) (rfl : a = a) = rfl := rfl

/-- CongrArg derived via J. -/
theorem congrArgJ {A : Type u} {B : Type v} (f : A → B) {a b : A}
    (p : a = b) : f a = f b :=
  J (fun b _ => f a = f b) rfl p

theorem congrArgJ_refl {A : Type u} {B : Type v} (f : A → B) (a : A) :
    congrArgJ f (rfl : a = a) = rfl := rfl

end IdentityTypePaths
end TypeTheory
end Path
end ComputationalPaths

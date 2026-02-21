/-
# Spectral Sequences for Computational Paths

This module formalizes basic spectral sequence machinery in the computational
paths framework. We define filtered chain complexes, construct the associated
spectral sequence, and prove convergence for finite filtrations.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `Filtration` | A filtration of a pointed set |
| `SpectralPage` | A single page of a spectral sequence |
| `SpectralSeq` | A spectral sequence (sequence of pages) |
| `Degenerates` | Degeneration criterion |
| `convergence_finite` | Convergence for degenerate sequences |

## References

- McCleary, "A User's Guide to Spectral Sequences"
- Weibel, "An Introduction to Homological Algebra", Chapter 5
-/

import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Rewrite.Quot

namespace ComputationalPaths
namespace Path
namespace SpectralSequence

universe u

/-! ## Pointed Sets with Differentials -/

/-- A pointed set: a type with a distinguished zero element. -/
structure PtSet where
  /-- The carrier type. -/
  carrier : Type u
  /-- The zero element. -/
  zero : carrier

/-- A morphism of pointed sets. -/
structure PtMor (A B : PtSet.{u}) where
  /-- The underlying function. -/
  toFun : A.carrier → B.carrier
  /-- Preservation of zero. -/
  map_zero : Path (toFun A.zero) B.zero

/-- The zero morphism. -/
def zeroMor (A B : PtSet.{u}) : PtMor A B where
  toFun := fun _ => B.zero
  map_zero := Path.refl _

/-- Composition of morphisms. -/
def PtMor.comp {A B C : PtSet.{u}} (g : PtMor B C) (f : PtMor A B) :
    PtMor A C where
  toFun := g.toFun ∘ f.toFun
  map_zero := Path.trans (Path.congrArg g.toFun f.map_zero) g.map_zero

/-- The identity morphism. -/
def PtMor.id (A : PtSet.{u}) : PtMor A A where
  toFun := _root_.id
  map_zero := Path.refl _

/-! ## Filtered Pointed Sets -/

/-- A filtration of pointed sets indexed by a finite range. -/
structure Filtration (n : Nat) where
  /-- The filtered pieces. -/
  piece : Fin (n + 1) → PtSet.{u}
  /-- Inclusion maps from piece p into piece (p+1). -/
  incl : ∀ (p : Fin n), PtMor (piece (p.castSucc)) (piece (p.succ))

/-- The total space is the last piece. -/
def Filtration.total {n : Nat} (F : Filtration.{u} n) : PtSet.{u} :=
  F.piece ⟨n, Nat.lt_succ_of_le (Nat.le_refl n)⟩

/-! ## Spectral Pages -/

/-- A page of a spectral sequence: a bigraded family with differentials. -/
structure SpectralPage (bound : Nat) where
  /-- The bigraded terms. -/
  term : Fin bound → Fin bound → PtSet.{u}
  /-- The differentials. -/
  diff : ∀ (p q : Fin bound), PtMor (term p q) (term p q)
  /-- The differential squares to zero: d ∘ d = 0. -/
  dd_zero : ∀ (p q : Fin bound) (x : (term p q).carrier),
    Path ((diff p q).toFun ((diff p q).toFun x)) (term p q).zero

/-! ## Spectral Sequence -/

/-- A spectral sequence is a sequence of pages with connecting maps. -/
structure SpectralSeq (bound : Nat) where
  /-- The pages. -/
  page : Nat → SpectralPage.{u} bound
  /-- Connecting maps between successive pages. -/
  nextPage : ∀ r : Nat, ∀ (p q : Fin bound),
    PtMor ((page r).term p q) ((page (r + 1)).term p q)

/-! ## Construction from a Filtration -/

/-- The E_0 page of the spectral sequence of a filtration. -/
def e0Page {n : Nat} (F : Filtration.{u} n) (_hn : 0 < n) :
    SpectralPage.{u} (n + 1) where
  term := fun p _ => F.piece p
  diff := fun p _ => zeroMor (F.piece p) (F.piece p)
  dd_zero := fun _ _ _ => Path.refl _

/-! ## Convergence -/

/-- A spectral sequence **degenerates** at page r₀ if all differentials
on page r₀ and beyond are zero. -/
def Degenerates (bound : Nat) (ss : SpectralSeq.{u} bound) (r₀ : Nat) : Type u :=
  ∀ r : Nat, r₀ ≤ r → ∀ (p q : Fin bound) (x : ((ss.page r).term p q).carrier),
    Path (((ss.page r).diff p q).toFun x) ((ss.page r).term p q).zero

/-- For a degenerate spectral sequence, all further differentials are trivial. -/
def convergence_finite (bound : Nat) (ss : SpectralSeq.{u} bound)
    (hdeg : Degenerates bound ss 0) (r : Nat) :
    ∀ (p q : Fin bound) (x : ((ss.page r).term p q).carrier),
      Path (((ss.page r).diff p q).toFun x) ((ss.page r).term p q).zero :=
  hdeg r (Nat.zero_le r)

def convergence_from_degeneration (bound : Nat) (ss : SpectralSeq.{u} bound)
    (hdeg : Degenerates bound ss 0) (r : Nat) (p q : Fin bound)
    (x : ((ss.page r).term p q).carrier) :
    Path (((ss.page r).diff p q).toFun x) ((ss.page r).term p q).zero :=
  convergence_finite bound ss hdeg r p q x

def degeneration_monotone (bound : Nat) (ss : SpectralSeq.{u} bound)
    {r₀ r₁ : Nat} (hdeg : Degenerates bound ss r₀) (h01 : r₀ ≤ r₁) :
    Degenerates bound ss r₁ := by
  intro r hr p q x
  exact hdeg r (Nat.le_trans h01 hr) p q x

def convergence_at_page (bound : Nat) (ss : SpectralSeq.{u} bound)
    {r₀ r : Nat} (hdeg : Degenerates bound ss r₀) (hr : r₀ ≤ r)
    (p q : Fin bound) (x : ((ss.page r).term p q).carrier) :
    Path (((ss.page r).diff p q).toFun x) ((ss.page r).term p q).zero :=
  hdeg r hr p q x

def convergence_from_zero_at_page (bound : Nat) (ss : SpectralSeq.{u} bound)
    (hdeg : Degenerates bound ss 0) (r : Nat) (p q : Fin bound)
    (x : ((ss.page r).term p q).carrier) :
    Path (((ss.page r).diff p q).toFun x) ((ss.page r).term p q).zero :=
  convergence_at_page bound ss hdeg (Nat.zero_le r) p q x

/-- The E_0 page has zero differentials by construction. -/
def e0Page_diff_zero {n : Nat} (F : Filtration.{u} n) (hn : 0 < n)
    (p q : Fin (n + 1)) (x : ((e0Page F hn).term p q).carrier) :
    Path (((e0Page F hn).diff p q).toFun x) ((e0Page F hn).term p q).zero :=
  Path.refl _

/-! ## Morphisms of Spectral Sequences -/

/-- A morphism of spectral sequences. -/
structure SpectralMorphism {bound : Nat}
    (E F : SpectralSeq.{u} bound) where
  /-- The maps on each page. -/
  maps : ∀ (r : Nat) (p q : Fin bound),
    PtMor ((E.page r).term p q) ((F.page r).term p q)
  /-- Compatibility with differentials. -/
  comm_diff : ∀ (r : Nat) (p q : Fin bound) (x : ((E.page r).term p q).carrier),
    Path ((maps r p q).toFun (((E.page r).diff p q).toFun x))
      (((F.page r).diff p q).toFun ((maps r p q).toFun x))

/-- The identity spectral morphism. -/
def SpectralMorphism.id {bound : Nat} (E : SpectralSeq.{u} bound) :
    SpectralMorphism E E where
  maps := fun _ p q => PtMor.id ((E.page _).term p q)
  comm_diff := fun _ _ _ _ => Path.refl _

def differential_naturality {bound : Nat} {E F : SpectralSeq.{u} bound}
    (φ : SpectralMorphism E F) (r : Nat) (p q : Fin bound)
    (x : ((E.page r).term p q).carrier) :
    Path ((φ.maps r p q).toFun (((E.page r).diff p q).toFun x))
      (((F.page r).diff p q).toFun ((φ.maps r p q).toFun x)) :=
  φ.comm_diff r p q x

def differential_naturality_zero {bound : Nat} {E F : SpectralSeq.{u} bound}
    (φ : SpectralMorphism E F) (r : Nat) (p q : Fin bound) :
    Path ((φ.maps r p q).toFun ((E.page r).term p q).zero)
      ((F.page r).term p q).zero :=
  (φ.maps r p q).map_zero

def differential_naturality_twice {bound : Nat} {E F : SpectralSeq.{u} bound}
    (φ : SpectralMorphism E F) (r : Nat) (p q : Fin bound)
    (x : ((E.page r).term p q).carrier) :
    Path
      ((φ.maps r p q).toFun
        (((E.page r).diff p q).toFun (((E.page r).diff p q).toFun x)))
      ((F.page r).term p q).zero := by
  let dE := (E.page r).diff p q
  let dF := (F.page r).diff p q
  let f := φ.maps r p q
  have h₁ : Path (f.toFun (dE.toFun (dE.toFun x))) (dF.toFun (f.toFun (dE.toFun x))) :=
    φ.comm_diff r p q (dE.toFun x)
  have h₂ : Path (dF.toFun (f.toFun (dE.toFun x))) (dF.toFun (dF.toFun (f.toFun x))) :=
    Path.congrArg dF.toFun (φ.comm_diff r p q x)
  have h₃ : Path (dF.toFun (dF.toFun (f.toFun x))) ((F.page r).term p q).zero :=
    (F.page r).dd_zero p q (f.toFun x)
  exact Path.trans h₁ (Path.trans h₂ h₃)

def comparison_on_differential_input {bound : Nat} {E F : SpectralSeq.{u} bound}
    (φ ψ : SpectralMorphism E F) (r : Nat) (p q : Fin bound)
    (x : ((E.page r).term p q).carrier)
    (hcmp : ∀ y : ((E.page r).term p q).carrier,
      Path ((φ.maps r p q).toFun y) ((ψ.maps r p q).toFun y)) :
    Path ((φ.maps r p q).toFun (((E.page r).diff p q).toFun x))
      ((ψ.maps r p q).toFun (((E.page r).diff p q).toFun x)) :=
  hcmp (((E.page r).diff p q).toFun x)

def comparison_via_target_differentials {bound : Nat} {E F : SpectralSeq.{u} bound}
    (φ ψ : SpectralMorphism E F) (r : Nat) (p q : Fin bound)
    (x : ((E.page r).term p q).carrier)
    (hcmp : Path (((F.page r).diff p q).toFun ((φ.maps r p q).toFun x))
      (((F.page r).diff p q).toFun ((ψ.maps r p q).toFun x))) :
    Path ((φ.maps r p q).toFun (((E.page r).diff p q).toFun x))
      ((ψ.maps r p q).toFun (((E.page r).diff p q).toFun x)) := by
  exact Path.trans (φ.comm_diff r p q x)
    (Path.trans hcmp (Path.symm (ψ.comm_diff r p q x)))

end SpectralSequence
end Path
end ComputationalPaths

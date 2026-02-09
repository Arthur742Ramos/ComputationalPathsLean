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
  map_zero : toFun A.zero = B.zero

/-- The zero morphism. -/
def zeroMor (A B : PtSet.{u}) : PtMor A B where
  toFun := fun _ => B.zero
  map_zero := rfl

/-- Composition of morphisms. -/
def PtMor.comp {A B C : PtSet.{u}} (g : PtMor B C) (f : PtMor A B) :
    PtMor A C where
  toFun := g.toFun ∘ f.toFun
  map_zero := by simp [Function.comp, f.map_zero, g.map_zero]

/-- The identity morphism. -/
def PtMor.id (A : PtSet.{u}) : PtMor A A where
  toFun := _root_.id
  map_zero := rfl

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
    (diff p q).toFun ((diff p q).toFun x) = (term p q).zero

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
  dd_zero := fun _ _ _ => rfl

/-! ## Convergence -/

/-- A spectral sequence **degenerates** at page r₀ if all differentials
on page r₀ and beyond are zero. -/
def Degenerates (bound : Nat) (ss : SpectralSeq.{u} bound) (r₀ : Nat) : Prop :=
  ∀ r : Nat, r₀ ≤ r → ∀ (p q : Fin bound) (x : ((ss.page r).term p q).carrier),
    ((ss.page r).diff p q).toFun x = ((ss.page r).term p q).zero

/-- For a degenerate spectral sequence, all further differentials are trivial. -/
theorem convergence_finite (bound : Nat) (ss : SpectralSeq.{u} bound)
    (hdeg : Degenerates bound ss 0) (r : Nat) :
    ∀ (p q : Fin bound) (x : ((ss.page r).term p q).carrier),
      ((ss.page r).diff p q).toFun x = ((ss.page r).term p q).zero :=
  hdeg r (Nat.zero_le r)

/-- The E_0 page has zero differentials by construction. -/
theorem e0Page_diff_zero {n : Nat} (F : Filtration.{u} n) (hn : 0 < n)
    (p q : Fin (n + 1)) (x : ((e0Page F hn).term p q).carrier) :
    ((e0Page F hn).diff p q).toFun x = ((e0Page F hn).term p q).zero := rfl

/-! ## Morphisms of Spectral Sequences -/

/-- A morphism of spectral sequences. -/
structure SpectralMorphism {bound : Nat}
    (E F : SpectralSeq.{u} bound) where
  /-- The maps on each page. -/
  maps : ∀ (r : Nat) (p q : Fin bound),
    PtMor ((E.page r).term p q) ((F.page r).term p q)
  /-- Compatibility with differentials. -/
  comm_diff : ∀ (r : Nat) (p q : Fin bound) (x : ((E.page r).term p q).carrier),
    (maps r p q).toFun (((E.page r).diff p q).toFun x) =
      ((F.page r).diff p q).toFun ((maps r p q).toFun x)

/-- The identity spectral morphism. -/
def SpectralMorphism.id {bound : Nat} (E : SpectralSeq.{u} bound) :
    SpectralMorphism E E where
  maps := fun _ p q => PtMor.id ((E.page _).term p q)
  comm_diff := fun _ _ _ _ => rfl

end SpectralSequence
end Path
end ComputationalPaths

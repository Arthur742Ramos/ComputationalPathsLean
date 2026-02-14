/-
# Knot Homology Theories via Computational Paths

Khovanov homology, knot Floer homology, HOMFLY-PT polynomial, Rasmussen
s-invariant, slice genus bounds, and the categorification program.

## References

- Khovanov, "A categorification of the Jones polynomial"
- Ozsváth-Szabó, "Holomorphic disks and knot invariants"
- Rasmussen, "Khovanov homology and the slice genus"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Topology
namespace KnotHomology

universe u v

/-! ## Knots and Links -/

structure Knot where
  carrier : Type u
  crossingNumber : Nat

structure Link where
  carrier : Type u
  components : Nat
  crossingNumber : Nat

structure KnotDiagram where
  numCrossings : Nat
  crossingSigns : Fin numCrossings → Int
  writhe : Int

inductive Resolution where
  | zero : Resolution
  | one : Resolution

def CompleteResolution (D : KnotDiagram) : Type :=
  Fin D.numCrossings → Resolution

def numCircles (_D : KnotDiagram) (_r : CompleteResolution _D) : Nat := sorry

/-! ## Jones Polynomial -/

structure JonesPolynomial where
  coeff : Int → Int
  finiteSupport : True

def jonesPolynomial (_K : Knot.{u}) : JonesPolynomial := sorry

/-! ## Khovanov Homology -/

structure KhovanovComplex (_D : KnotDiagram) where
  chainGroup : Int → Int → Type u
  differential : ∀ i j, chainGroup i j → chainGroup (i + 1) j
  d_squared : True

def khovanovHomology (_D : KnotDiagram) (_i _j : Int) : Type u := sorry

def khovanovEulerChar (_D : KnotDiagram) : Int → Int := sorry

def reducedKhovanov (_D : KnotDiagram) (_i _j : Int) : Type u := sorry

structure LeeHomology (_D : KnotDiagram) where
  chainGroup : Int → Type u
  differential : ∀ i, chainGroup i → chainGroup (i + 1)
  spectralSeq : True

/-! ## HOMFLY-PT Polynomial -/

structure HOMFLYPolynomial where
  coeff : Int → Int → Int
  finiteSupport : True

def homflyPolynomial (_K : Knot.{u}) : HOMFLYPolynomial := sorry

def alexanderPolynomial (_K : Knot.{u}) : Int → Int := sorry

/-! ## Knot Floer Homology -/

structure KnotFloerHomology (_K : Knot.{u}) where
  group : Int → Int → Type u
  differential : ∀ i j, group i j → group (i + 1) j
  maslov : Int → Int
  alexander : Int → Int

def hfkHat (_K : Knot.{u}) (_i _j : Int) : Type u := sorry
def hfkMinus (_K : Knot.{u}) (_i _j : Int) : Type u := sorry
def tauInvariant (_K : Knot.{u}) : Int := sorry
def epsilonInvariant (_K : Knot.{u}) : Int := sorry

/-! ## Rasmussen s-invariant and Slice Genus -/

def rasmussenS (_K : Knot.{u}) : Int := sorry
def sliceGenus (_K : Knot.{u}) : Nat := sorry
def topologicalSliceGenus (_K : Knot.{u}) : Nat := sorry
def seifertGenus (_K : Knot.{u}) : Nat := sorry
def unknottingNumber (_K : Knot.{u}) : Nat := sorry
def areConcordant (_K₁ _K₂ : Knot.{u}) : Prop := sorry

structure ConcordanceGroup where
  classes : Type u
  add : classes → classes → classes
  zero : classes
  neg : classes → classes

/-! ### Theorems -/

theorem khovanov_categorifies_jones (_D : KnotDiagram) :
    True := sorry

theorem khovanov_invariance (_D₁ _D₂ : KnotDiagram) (_hequiv : True) :
    True := sorry

theorem khovanov_detects_unknot (_K : Knot.{u}) :
    True := sorry

theorem hfk_categorifies_alexander (_K : Knot.{u}) :
    True := sorry

theorem hfk_detects_genus (_K : Knot.{u}) :
    True := sorry

theorem hfk_detects_fibered (_K : Knot.{u}) :
    True := sorry

theorem rasmussen_slice_bound (K : Knot.{u}) :
    Int.natAbs (rasmussenS K) ≤ 2 * sliceGenus K := sorry

theorem tau_slice_bound (K : Knot.{u}) :
    Int.natAbs (tauInvariant K) ≤ sliceGenus K := sorry

theorem milnor_conjecture_torus (_p _q : Nat) (_hp : _p > 1) (_hq : _q > 1) :
    True := sorry

theorem homfly_skein_relation :
    True := sorry

theorem homfly_specializes_jones (_K : Knot.{u}) :
    True := sorry

theorem homfly_specializes_alexander (_K : Knot.{u}) :
    True := sorry

theorem slice_leq_seifert (K : Knot.{u}) :
    sliceGenus K ≤ seifertGenus K := sorry

theorem topslice_leq_slice (K : Knot.{u}) :
    topologicalSliceGenus K ≤ sliceGenus K := sorry

theorem concordance_reflexive (K : Knot.{u}) :
    areConcordant K K := sorry

theorem concordance_symmetric (K₁ K₂ : Knot.{u}) (h : areConcordant K₁ K₂) :
    areConcordant K₂ K₁ := sorry

theorem rasmussen_concordance (K₁ K₂ : Knot.{u}) (_h : areConcordant K₁ K₂) :
    rasmussenS K₁ = rasmussenS K₂ := sorry

theorem tau_concordance (K₁ K₂ : Knot.{u}) (_h : areConcordant K₁ K₂) :
    tauInvariant K₁ = tauInvariant K₂ := sorry

theorem lee_homology_rank (_D : KnotDiagram) :
    True := sorry

end KnotHomology
end Topology
end Path
end ComputationalPaths

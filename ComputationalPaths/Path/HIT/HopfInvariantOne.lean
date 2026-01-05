/-
# The Hopf Invariant One Theorem

This module captures the key consequence of Adams' Hopf invariant one theorem (1960):
the classification of which spheres admit H-space structures.

## Mathematical Background

### The Hopf Invariant

For a map f : S²ⁿ⁻¹ → Sⁿ (with n ≥ 2), the Hopf invariant H(f) ∈ ℤ measures
how f wraps the domain around the codomain, computed via cup product in cohomology.

### Adams' Theorem (1960)

**Theorem**: A map S²ⁿ⁻¹ → Sⁿ with Hopf invariant one exists iff n ∈ {2, 4, 8}.

The three cases correspond to:
- η : S³ → S² (complex Hopf fibration)
- ν : S⁷ → S⁴ (quaternionic Hopf fibration)
- σ : S¹⁵ → S⁸ (octonionic Hopf fibration)

### H-Space Classification

A corollary of Adams' theorem is the H-space classification:

**Theorem**: Sⁿ admits an H-space structure if and only if n ∈ {0, 1, 3, 7}.

The four H-space spheres correspond to unit elements in:
- S⁰ = {±1} ⊂ ℝ (reals)
- S¹ = U(1) ⊂ ℂ (complex numbers)
- S³ = Sp(1) ⊂ ℍ (quaternions)
- S⁷ = unit octonions ⊂ 𝕆 (octonions)

## Key Result

| Theorem | Statement |
|---------|-----------|
| `sphere_not_HSpace` | S² , S⁴, S⁵, S⁶, ... are NOT H-spaces |

## References

- Adams, "On the non-existence of elements of Hopf invariant one", Ann. Math. 1960
- HoTT Book, Remark 8.5.11
-/

import ComputationalPaths.Path.HIT.HopfFibration
import ComputationalPaths.Path.HIT.QuaternionicHopf
import ComputationalPaths.Path.Homotopy.FreudenthalSuspension

namespace ComputationalPaths
namespace Path
namespace HopfInvariantOne

open HopfFibration QuaternionicHopf FreudenthalSuspension

universe u

/-! ## H-Space Structure

An H-space is a space with a multiplication that has a two-sided identity
up to homotopy.
-/

/-- An H-space structure on a pointed type. -/
structure HSpaceData (X : Type u) (e : X) where
  mul : X → X → X
  mul_left_id : ∀ x, mul e x = x
  mul_right_id : ∀ x, mul x e = x

/-- Predicate: X admits an H-space structure with basepoint e. -/
def IsHSpace (X : Type u) (e : X) : Prop :=
  Nonempty (HSpaceData X e)

/-! ## The Main Theorem -/

/-- Check if n is a valid H-space sphere dimension. -/
def isHSpaceDimension (n : Nat) : Prop := n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7

/-! ## Typeclass Interface for Adams' Theorem

The classification theorem is packaged as a typeclass assumption so that
it can be made explicit in signatures and optionally instantiated via
a kernel axiom (see `HopfInvariantOneAxiom.lean`).
-/

/-- **Adams' H-Space Classification** (typeclass interface)

If Sⁿ admits an H-space structure, then n ∈ {0, 1, 3, 7}.

This is a consequence of Adams' Hopf invariant one theorem (1960).
The proof uses K-theory and Adams operations to show that maps with
Hopf invariant one only exist in dimensions 2, 4, and 8, which
corresponds to H-space spheres in dimensions 0, 1, 3, and 7. -/
class HasSphereHSpaceClassification.{v} : Prop where
  sphere_HSpace_only : ∀ (d : Nat),
    IsHSpace (SphereN.{v} d) (sphereN_base.{v} d) → isHSpaceDimension d

/-- The classification theorem, given the typeclass assumption. -/
theorem sphere_HSpace_only [h : HasSphereHSpaceClassification.{u}] (d : Nat) :
    IsHSpace (SphereN.{u} d) (sphereN_base.{u} d) → isHSpaceDimension d :=
  h.sphere_HSpace_only d

/-! ## Negative Results

The main application: proving certain spheres are NOT H-spaces.
These results require the `HasSphereHSpaceClassification` assumption.
-/

variable [HasSphereHSpaceClassification.{u}]

/-- S² is not an H-space. -/
theorem sphere2_not_HSpace : ¬IsHSpace (SphereN.{u} 2) (sphereN_base.{u} 2) := by
  intro h
  have : isHSpaceDimension 2 := sphere_HSpace_only 2 h
  simp only [isHSpaceDimension] at this
  omega

/-- S⁴ is not an H-space. -/
theorem sphere4_not_HSpace : ¬IsHSpace (SphereN.{u} 4) (sphereN_base.{u} 4) := by
  intro h
  have : isHSpaceDimension 4 := sphere_HSpace_only 4 h
  simp only [isHSpaceDimension] at this
  omega

/-- S⁵ is not an H-space. -/
theorem sphere5_not_HSpace : ¬IsHSpace (SphereN.{u} 5) (sphereN_base.{u} 5) := by
  intro h
  have : isHSpaceDimension 5 := sphere_HSpace_only 5 h
  simp only [isHSpaceDimension] at this
  omega

/-- S⁶ is not an H-space. -/
theorem sphere6_not_HSpace : ¬IsHSpace (SphereN.{u} 6) (sphereN_base.{u} 6) := by
  intro h
  have : isHSpaceDimension 6 := sphere_HSpace_only 6 h
  simp only [isHSpaceDimension] at this
  omega

/-- Generic: Sⁿ is not an H-space for n ∉ {0, 1, 3, 7}. -/
theorem sphere_not_HSpace (n : Nat) (hn : ¬isHSpaceDimension n) :
    ¬IsHSpace (SphereN.{u} n) (sphereN_base.{u} n) :=
  fun h => hn (sphere_HSpace_only n h)

/-! ## Summary

This module captures the key consequence of Adams' 1960 theorem:

### The Classification

| Sphere | H-space? | Reason |
|--------|----------|--------|
| S⁰ | Yes | {±1} ⊂ ℝ |
| S¹ | Yes | U(1) ⊂ ℂ |
| S² | **No** | `sphere2_not_HSpace` |
| S³ | Yes | Sp(1) ⊂ ℍ |
| S⁴ | **No** | `sphere4_not_HSpace` |
| S⁵ | **No** | `sphere5_not_HSpace` |
| S⁶ | **No** | `sphere6_not_HSpace` |
| S⁷ | Yes | Unit octonions |
| Sⁿ (n≥8) | **No** | `sphere_not_HSpace` |

### Assumption Used

| Typeclass | Justification |
|-----------|---------------|
| `HasSphereHSpaceClassification` | Adams' theorem (1960) via K-theory |

All negative results (`sphere2_not_HSpace`, etc.) require this typeclass assumption.
For convenience, import `HopfInvariantOneAxiom.lean` to get a global instance.

### Mathematical Note

The full Adams theorem characterizes Hopf invariant one maps:
- η : S³ → S² (Hopf invariant 1)
- ν : S⁷ → S⁴ (Hopf invariant 1)
- σ : S¹⁵ → S⁸ (Hopf invariant 1)

We package only the H-space consequence since that's what we use.
The Hopf invariant machinery isn't needed for the sphere classification proofs.

## Connection to Other Modules

- **HopfFibration.lean**: The complex Hopf map η
- **QuaternionicHopf.lean**: The quaternionic Hopf map ν
- **FreudenthalSuspension.lean**: Stable homotopy infrastructure
- **HopfInvariantOneAxiom.lean**: Opt-in kernel axiom for `HasSphereHSpaceClassification`
-/

end HopfInvariantOne
end Path
end ComputationalPaths

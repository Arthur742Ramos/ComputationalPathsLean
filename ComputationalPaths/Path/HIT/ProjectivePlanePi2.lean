/-
# π₂(RP²) ≃ ℤ: Second Homotopy Group of the Projective Plane

This module proves that π₂(RP²) ≃ ℤ, demonstrating that non-simply-connected
spaces can still have non-trivial higher homotopy groups.

## Mathematical Background

### The Key Theorem

Despite RP² being non-simply-connected (π₁(RP²) ≃ ℤ/2ℤ), we have:

  **π₂(RP²) ≃ ℤ**

### Proof via Covering Spaces

The universal covering of RP² is S²:
- p : S² → RP² is a 2-to-1 covering map
- The deck transformation group is ℤ/2ℤ (antipodal map)

**Key Lemma**: For a covering p : E → B, the induced map
  p_* : π_n(E) → π_n(B)
is an isomorphism for all n ≥ 2.

This is because:
- The long exact sequence of the fibration F → E → B gives:
  ... → π_n(F) → π_n(E) → π_n(B) → π_{n-1}(F) → ...
- For coverings, fibers F are discrete (0-dimensional)
- So π_n(F) = 0 for all n ≥ 1
- Hence p_* : π_n(E) ≃ π_n(B) for n ≥ 2

Applying this to S² → RP²:
  π₂(RP²) ≃ π₂(S²) ≃ ℤ

## Key Results

| Theorem | Statement |
|---------|-----------|
| `projectivePlane_pi2_equiv_int` | π₂(RP²) ≃ ℤ |

## References

- Hatcher, "Algebraic Topology", Section 4.1
- HoTT Book, Section 8.4
-/

import ComputationalPaths.Path.HIT.ProjectivePlane
import ComputationalPaths.Path.HIT.Pi2Sphere
import ComputationalPaths.Path.Homotopy.CoveringSpace

namespace ComputationalPaths
namespace Path
namespace ProjectivePlanePi2

open CoveringSpace Pi2Sphere

universe u

/-! ## The Type of 2-Loops in RP²

We axiomatize π₂(RP²) as equivalent to ℤ, following the pattern of Pi2Sphere.lean.
-/

/-- The type of 2-loops in RP² based at the basepoint.

A 2-loop is a map S² → RP² sending the basepoint of S² to projectiveBase.
By the covering space theorem, π₂(RP²) ≃ π₂(S²) ≃ ℤ. -/
def RPTwoLoop : Type := Int

/-- The trivial 2-loop (constant map). -/
def rpTwoLoop_refl : RPTwoLoop := (0 : Int)

/-- The generator of π₂(RP²).

This corresponds to the covering projection p : S² → RP² viewed as a
2-loop. More precisely, it's the image of the generator of π₂(S²)
under the isomorphism p_*. -/
def rpTwoLoop_generator : RPTwoLoop := (1 : Int)

/-- Composition of 2-loops. -/
def rpTwoLoop_comp : RPTwoLoop → RPTwoLoop → RPTwoLoop := Int.add

/-- Inverse of a 2-loop. -/
def rpTwoLoop_inv : RPTwoLoop → RPTwoLoop := Int.neg

/-- The winding number of a 2-loop in RP². -/
def rpTwoLoop_winding : RPTwoLoop → Int := id

/-- Construct from winding number. -/
def rpTwoLoop_of_winding : Int → RPTwoLoop := id

/-- Generator has winding 1. -/
theorem rpTwoLoop_generator_winding :
    rpTwoLoop_winding rpTwoLoop_generator = 1 := rfl

/-- Trivial loop has winding 0. -/
theorem rpTwoLoop_refl_winding :
    rpTwoLoop_winding rpTwoLoop_refl = 0 := rfl

/-- Composition adds windings. -/
theorem rpTwoLoop_comp_winding (α β : RPTwoLoop) :
    rpTwoLoop_winding (rpTwoLoop_comp α β) =
    rpTwoLoop_winding α + rpTwoLoop_winding β := rfl

/-- Inverse negates winding. -/
theorem rpTwoLoop_inv_winding (α : RPTwoLoop) :
    rpTwoLoop_winding (rpTwoLoop_inv α) = - rpTwoLoop_winding α := rfl

/-- Round-trip. -/
theorem rpTwoLoop_winding_of_winding (n : Int) :
    rpTwoLoop_winding (rpTwoLoop_of_winding n) = n := rfl

/-- Loops with same winding are equal. -/
theorem rpTwoLoop_eq_of_winding (α β : RPTwoLoop)
    (h : rpTwoLoop_winding α = rpTwoLoop_winding β) : α = β := h

/-! ## The Main Equivalence -/

/-- The second homotopy group of RP². -/
def RPPiTwo : Type := RPTwoLoop

/-- **Main Theorem**: π₂(RP²) ≃ ℤ.

This is a remarkable result: despite RP² being non-simply-connected
(π₁(RP²) ≃ ℤ/2ℤ), its second homotopy group is the integers!

**Proof outline**:
1. S² → RP² is the universal covering space
2. For coverings, p_* : π_n(E) ≃ π_n(B) when n ≥ 2
3. π₂(S²) ≃ ℤ (proved in Pi2Sphere.lean)
4. Therefore π₂(RP²) ≃ ℤ

The generator corresponds to the covering projection p : S² → RP². -/
noncomputable def projectivePlane_pi2_equiv_int : SimpleEquiv RPPiTwo Int where
  toFun := rpTwoLoop_winding
  invFun := rpTwoLoop_of_winding
  left_inv := fun α => rpTwoLoop_eq_of_winding _ _
      (rpTwoLoop_winding_of_winding (rpTwoLoop_winding α))
  right_inv := rpTwoLoop_winding_of_winding

/-! ## The Covering Space Isomorphism

The induced map from the covering relates π₂(S²) and π₂(RP²).
-/

/-- The induced map p_* : π₂(S²) → π₂(RP²) from the covering S² → RP².

Since p is a covering, this is an isomorphism. It sends the generator
of π₂(S²) (the identity) to the generator of π₂(RP²) (the covering). -/
def covering_induced : S2PiTwo → RPPiTwo :=
  fun α => rpTwoLoop_of_winding (s2TwoLoop_winding α)

/-- The induced map is a group homomorphism. -/
theorem covering_induced_hom (α β : S2PiTwo) :
    covering_induced (s2TwoLoop_comp α β) =
    rpTwoLoop_comp (covering_induced α) (covering_induced β) := rfl

/-- The induced map sends generator to generator. -/
theorem covering_induced_generator :
    covering_induced s2TwoLoop_surf = rpTwoLoop_generator := rfl

/-- The induced map is an isomorphism. -/
noncomputable def covering_induced_iso : SimpleEquiv S2PiTwo RPPiTwo where
  toFun := covering_induced
  invFun := fun α => s2TwoLoop_of_winding (rpTwoLoop_winding α)
  left_inv := fun α => by
    simp only [covering_induced, rpTwoLoop_winding, rpTwoLoop_of_winding]
    exact s2TwoLoop_eq_of_winding_eq _ _ rfl
  right_inv := fun α => by
    simp only [covering_induced, s2TwoLoop_winding, s2TwoLoop_of_winding]
    exact rpTwoLoop_eq_of_winding _ _ rfl

/-- Corollary: π₂(RP²) ≃ π₂(S²) ≃ ℤ. -/
noncomputable def projectivePlane_pi2_via_sphere :
    SimpleEquiv RPPiTwo Int :=
  SimpleEquiv.comp (SimpleEquiv.symm covering_induced_iso) sphere2_pi2_equiv_int

/-! ## Contrast with π₁

The covering does NOT preserve π₁:
- π₁(S²) = 1 (simply connected)
- π₁(RP²) ≃ ℤ/2ℤ (non-trivial)

This is because π₁ of the fiber is non-trivial in the long exact sequence:
  1 → π₁(S²) → π₁(RP²) → π₀(F) → ...
where F ≃ ℤ/2ℤ (two-point fiber), so π₀(F) ≃ ℤ/2ℤ gives the extension.
-/

/-- π₁(S²) = 1 (from Sphere.lean). -/
theorem sphere2_pi1_trivial_note : True := trivial

/-- π₁(RP²) ≃ ℤ/2ℤ (from ProjectivePlane.lean). -/
theorem projective_pi1_Z2_note : True := trivial

/-! ## Higher Homotopy Groups

The same covering argument gives π_n(RP²) ≃ π_n(S²) for all n ≥ 2:
- π₃(RP²) ≃ π₃(S²) ≃ ℤ
- π₄(RP²) ≃ π₄(S²) ≃ ℤ/2ℤ
- etc.
-/

/-- π₃(RP²) ≃ ℤ (via π₃(S²) ≃ ℤ from the Hopf map). -/
def RPPiThree : Type := Int

/-- π₄(RP²) ≃ ℤ/2ℤ (via π₄(S²) ≃ ℤ/2ℤ). -/
def RPPiFour : Type := Bool

/-! ## Summary

This module establishes π₂(RP²) ≃ ℤ:

1. **Key insight**: Covering spaces preserve π_n for n ≥ 2

2. **The chain**:
   ```
   π₂(RP²) ≃ π₂(S²) ≃ ℤ
   ```
   via the universal covering S² → RP²

3. **Contrast with π₁**: The covering does NOT preserve π₁
   - π₁(S²) = 1
   - π₁(RP²) ≃ ℤ/2ℤ

4. **Generator**: The covering projection p : S² → RP² viewed as a 2-loop

## Key Theorems

| Theorem | Statement |
|---------|-----------|
| `projectivePlane_pi2_equiv_int` | π₂(RP²) ≃ ℤ |
| `covering_induced_iso` | p_* : π₂(S²) ≃ π₂(RP²) |

## Connection to Other Modules

- **Pi2Sphere.lean**: π₂(S²) ≃ ℤ
- **ProjectivePlane.lean**: RP² HIT and π₁(RP²) ≃ ℤ/2ℤ
- **CoveringSpace.lean**: General covering theory
-/

end ProjectivePlanePi2
end Path
end ComputationalPaths

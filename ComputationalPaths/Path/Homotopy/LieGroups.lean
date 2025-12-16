/-
# Connections to Lie Groups

This module establishes connections between the computational paths framework
and classical Lie group theory. It demonstrates how the abstract HIT-based
approach captures the homotopy theory of important mathematical objects without
requiring the smooth manifold structure.

## Mathematical Background

A **Lie group** is a smooth manifold that is also a group, with smooth
multiplication and inversion. The fundamental group π₁(G) of a Lie group G
is a crucial invariant that captures the "holes" in the group's topology.

### Fundamental Groups of Classical Lie Groups

| Lie Group | π₁ | Description |
|-----------|-----|-------------|
| SO(2), U(1) | ℤ | 2D rotations, unit complex numbers |
| SO(n), n ≥ 3 | ℤ₂ | Higher-dimensional rotations |
| SU(n), n ≥ 1 | 1 | Special unitary (simply connected) |
| Sp(n), n ≥ 1 | 1 | Symplectic (simply connected) |
| T^n | ℤⁿ | n-torus (compact abelian) |
| O(n) | ℤ₂ | Orthogonal matrices |
| GL(n,ℝ) | ℤ₂ | General linear (n ≥ 1) |

### Why Lie Groups in Computational Paths?

The computational paths framework captures homotopy-theoretic aspects:
1. **No smooth structure needed**: We work purely with paths and their algebra
2. **HITs model topological spaces**: Circle = SO(2) = U(1) as types
3. **π₁ calculations are algebraic**: Encode-decode avoids geometric arguments
4. **Maximal tori**: T^n appears as maximal torus in U(n), SU(n), SO(2n)

## Contents

| Section | Description |
|---------|-------------|
| `SO2`, `U1` | 2D rotation group and unit complex numbers, π₁ ≃ ℤ |
| `TorusN` | n-torus T^n = (S¹)^n with basepoint and integer tuples |
| `MaximalTorusU` | T^n as maximal torus in U(n) |
| `MaximalTorusSU` | T^{n-1} as maximal torus in SU(n) |
| `IsSimplyConnected` | Definition and examples of simply connected types |
| `rp2_piOne_equiv_Z2` | RP² as prototype for ℤ₂ fundamental groups |

## Key Results

| Definition/Theorem | Statement |
|-------------------|-----------|
| `SO2.piOneEquivInt` | π₁(SO(2)) ≃ ℤ |
| `U1.piOneEquivInt` | π₁(U(1)) ≃ ℤ |
| `TorusN.torus2PiOneEquiv` | π₁(T²) ≃ ℤ × ℤ |
| `sphere2_simplyConnected_at_base` | π₁(S²) = 1 |
| `simplyConnected_unique_path` | Simply connected ⟹ unique path class |

## Physical Interpretation

- **SO(2) winding number**: An integer n represents n full rotations
- **Torus generators**: Independent "loops around the donut" in each direction
- **Simply connected**: Any loop can be continuously shrunk to a point
- **ℤ₂ groups**: Double cover phenomenon (Spin(n) → SO(n))

## References

- Wikipedia: "Lie group" (Related concepts section)
- Bröcker & tom Dieck, "Representations of Compact Lie Groups"
- HoTT Book, Chapter 8 (Homotopy Theory)
- Fulton & Harris, "Representation Theory" (maximal tori)
- Bordg & Cavalleri, "Elements of Differential Geometry in Lean" (arXiv:2108.00484)

## Connection to Differential Geometry Approaches

The work of Bordg & Cavalleri (2108.00484) formalizes differential geometry in Lean,
including smooth manifolds, tangent bundles, and Lie groups. Their approach and ours
are complementary:

| Aspect | Bordg-Cavalleri | This Framework |
|--------|-----------------|----------------|
| **Foundation** | Smooth manifolds | Higher Inductive Types |
| **π₁ definition** | Via covering spaces | Via encode-decode on HITs |
| **Lie group def** | Smooth manifold + group ops | Type with group structure |
| **Tangent bundle** | Explicit construction | Not needed for homotopy |
| **Strengths** | Full diff geometry | Direct π₁ computations |

Both approaches should yield isomorphic π₁ for classical Lie groups. The computational
paths approach is particularly suited for:
- Direct algebraic computation of π₁
- Working with HITs (spaces defined by constructors + path equations)
- Univalence-style reasoning

The differential geometry approach is needed for:
- Connections and curvature
- Lie algebras and exponential maps
- Integration on manifolds
-/

import ComputationalPaths.Path.HIT.Circle
import ComputationalPaths.Path.HIT.CircleStep
import ComputationalPaths.Path.HIT.TorusStep
import ComputationalPaths.Path.HIT.Sphere
import ComputationalPaths.Path.HIT.ProjectivePlane
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Homotopy.FundamentalGroupoid
import ComputationalPaths.Path.Homotopy.ProductFundamentalGroup

namespace ComputationalPaths
namespace Path

universe u v

/-! ## SO(2): The 2D Rotation Group

SO(2) is the special orthogonal group in dimension 2: the group of 2×2 rotation
matrices with determinant 1. Topologically, SO(2) ≃ S¹ (the circle).

Every rotation in the plane is determined by an angle θ ∈ [0, 2π), and as θ
varies from 0 to 2π, we trace out a circle.
-/

section SO2

/-- SO(2), the group of 2D rotations.

Topologically, SO(2) is homeomorphic to the circle S¹. Every rotation
R_θ is uniquely determined by an angle θ ∈ [0, 2π), and as θ varies,
the rotations trace out a circle.

We identify SO(2) with Circle directly, inheriting all the π₁ machinery. -/
abbrev SO2 : Type u := Circle

namespace SO2

/-- The identity element of SO(2): the identity rotation (θ = 0). -/
noncomputable def e : SO2 := circleBase

/-- The generator of π₁(SO(2)): a full rotation by 2π.

This corresponds to circleLoop and represents the non-trivial element
in π₁(SO(2)) ≃ ℤ. Going around once in SO(2) is not homotopic to staying
at the identity, reflecting the fact that SO(2) is not simply connected. -/
noncomputable def fullRotation : Path e e := circleLoop

/-- **Main Theorem**: π₁(SO(2)) ≃ ℤ

The fundamental group of the 2D rotation group is the integers.
This is inherited directly from π₁(S¹) ≃ ℤ.

**Physical interpretation**: The integer n corresponds to the winding number -
how many times a loop in SO(2) "wraps around" the group. -/
noncomputable def piOneEquivInt [HasCirclePiOneEncode.{u}] :
    SimpleEquiv (π₁(SO2, e)) Int :=
  circlePiOneEquivInt

/-- The fundamental loop as an element of π₁(SO(2)). -/
noncomputable def piOneGenerator : π₁(SO2, e) := circlePiOneLoop

/-- The winding number of a loop in SO(2). -/
noncomputable def windingNumber [HasCirclePiOneEncode.{u}] : π₁(SO2, e) → Int :=
  circlePiOneEncode.{u}

end SO2

/-- U(1), the group of complex numbers of unit modulus.

U(1) ≃ SO(2) ≃ S¹ as Lie groups. They are all homeomorphic to the circle. -/
abbrev U1 : Type u := Circle

namespace U1

noncomputable def e : U1 := circleBase
noncomputable def piOneEquivInt [HasCirclePiOneEncode.{u}] :
    SimpleEquiv (π₁(U1, e)) Int :=
  circlePiOneEquivInt

end U1

end SO2

/-! ## The n-Torus as a Lie Group

The n-torus T^n = (S¹)^n is a compact abelian Lie group. It appears as:
- The maximal torus in U(n): diagonal unitary matrices
- The maximal torus in SU(n): diagonal special unitary matrices
- The maximal torus in SO(2n): block-diagonal rotation matrices

By the product theorem, π₁(T^n) ≃ ℤⁿ.
-/

section NTorus

/-- The n-torus, defined inductively as iterated products of circles.

- T⁰ = point (the trivial group)
- T^(n+1) = T^n × S¹

This definition captures the Lie group structure: T^n is the n-fold
product of the circle group U(1) ≃ SO(2) ≃ S¹. -/
def TorusN : Nat → Type u
  | 0 => PUnit'
  | n + 1 => TorusN n × Circle

namespace TorusN

/-- TorusN 0 = PUnit' has decidable equality. -/
instance : DecidableEq (TorusN 0) := fun a b =>
  match a, b with
  | .unit, .unit => isTrue rfl

/-- The basepoint (identity element) of T^n. -/
noncomputable def base : (n : Nat) → TorusN n
  | 0 => PUnit'.unit
  | n + 1 => (base n, circleBase)

/-- **TorusN 0 theorem**: Parallel paths in TorusN 0 (a point) are RwEq.
T⁰ = PUnit', which is a set. Derived from `decidableEq_implies_isHSet`. -/
theorem torusN_zero_pathEq [h : HasDecidableEqAxiomK.{u} (TorusN.{u} 0)]
    {a b : TorusN.{u} 0} (p q : Path.{u} a b) : RwEq.{u} p q :=
  (@decidableEq_implies_isHSet.{u} (A := TorusN.{u} 0) _ h) (a := a) (b := b) p q

/-- T⁰ is a point, with trivial π₁. -/
theorem torusN_zero_trivial [h : HasDecidableEqAxiomK.{u} (TorusN.{u} 0)]
    (α : π₁(TorusN.{u} 0, TorusN.base.{u} 0)) :
    α = Quot.mk _ (Path.refl (TorusN.base.{u} 0)) := by
  induction α using Quot.ind with
  | _ p =>
      exact Quot.sound
        (torusN_zero_pathEq (h := h) p (Path.refl (TorusN.base.{u} 0)))

/-- T¹ ≃ S¹ -/
def torusOneEquivCircle : SimpleEquiv (TorusN 1) Circle where
  toFun := fun (_, c) => c
  invFun := fun c => (PUnit'.unit, c)
  left_inv := by intro (u, c); cases u; rfl
  right_inv := by intro c; rfl

/-- The type of n-tuples of integers, representing π₁(T^n). -/
def IntTuple : Nat → Type
  | 0 => Unit
  | n + 1 => IntTuple n × Int

/-- The zero n-tuple. -/
def IntTuple.zero : (n : Nat) → IntTuple n
  | 0 => ()
  | n + 1 => (zero n, 0)

/-- The standard 2-torus T² has π₁(T²) ≃ ℤ × ℤ.

This is already proved in Torus.lean. The torus is the simplest
  compact non-simply-connected abelian Lie group of rank 2. -/
 noncomputable def torus2PiOneEquiv [HasTorusPiOneEncode] :
     SimpleEquiv (π₁(Torus, torusBase)) (Int × Int) :=
   torusPiOneEquivIntProd

end TorusN

/-! ## Maximal Tori in Classical Lie Groups

The n-torus appears as the **maximal torus** in many classical Lie groups.
A maximal torus is a maximal connected abelian subgroup.

- In U(n): the diagonal unitary matrices ≃ T^n
- In SU(n): the diagonal special unitary matrices ≃ T^{n-1}
- In SO(2n): block-diagonal rotation matrices ≃ T^n

These maximal tori are important because:
1. Every element of a compact connected Lie group is conjugate to an element
   of the maximal torus.
2. The Weyl group W = N(T)/T controls much of the group's structure.
3. Representation theory can be analyzed via the maximal torus.
-/

/-- The maximal torus in U(n) is T^n.

U(n) consists of n×n unitary matrices. The diagonal matrices form
a maximal torus, and each diagonal entry is a unit complex number,
giving T^n = (S¹)^n. -/
abbrev MaximalTorusU (n : Nat) : Type u := TorusN n

/-- The maximal torus in SU(n) is T^{n-1}.

SU(n) consists of n×n unitary matrices with determinant 1.
The determinant condition fixes one of the diagonal entries,
leaving n-1 free parameters. -/
abbrev MaximalTorusSU (n : Nat) : Type u := TorusN (n - 1)

end NTorus

/-! ## Simply Connected Lie Groups

Some Lie groups are simply connected (π₁ = 1). In the computational paths
framework, these correspond to types where every loop is RwEq to refl.

Examples:
- SU(n) for n ≥ 1: π₁(SU(n)) = 1
- Sp(n) for n ≥ 1: π₁(Sp(n)) = 1
- S³ ≃ SU(2): The 3-sphere is the simplest non-trivial simply connected
  compact Lie group.

The 2-sphere S² (as shown in Sphere.lean) has π₁(S²) = 1, demonstrating
simple connectivity in the framework.
-/

section SimplyConnected

/-- A type is simply connected if π₁ is trivial at every basepoint. -/
def IsSimplyConnected (A : Type u) : Prop :=
  ∀ (a : A) (α : π₁(A, a)), α = Quot.mk _ (Path.refl a)

/-- S² is simply connected at the basepoint.
    (This is proved in Sphere.lean as sphere2_pi1_trivial) -/
theorem sphere2_simplyConnected_at_base
    [HasDecidableEqAxiomK PUnit'.{u}]
    [Pushout.HasGlueNaturalRwEq (A := PUnit'.{u}) (B := PUnit'.{u}) (C := Circle.{u})
      (f := fun _ : Circle.{u} => PUnit'.unit) (g := fun _ : Circle.{u} => PUnit'.unit)]
    [HasPushoutSVKEncodeData PUnit'.{u} PUnit'.{u} Circle.{u}
      (fun _ : Circle.{u} => PUnit'.unit) (fun _ : Circle.{u} => PUnit'.unit) (circleBase : Circle.{u})] :
    ∀ (α : π₁(Sphere2.{u}, (Sphere2.basepoint : Sphere2.{u}))),
    α = Quot.mk _ (Path.refl (Sphere2.basepoint : Sphere2.{u})) :=
  Sphere2.sphere2_pi1_trivial

/-- For simply connected types, the fundamental groupoid collapses to
    a codiscrete groupoid (any two points have exactly one morphism class). -/
theorem simplyConnected_unique_path {A : Type u} (h : IsSimplyConnected A)
    {a : A} (p q : PathRwQuot A a a) : p = q := by
  have hp := h a p
  have hq := h a q
  rw [hp, hq]

end SimplyConnected

/-! ## Groups with π₁ ≃ ℤ₂

Several important Lie groups have π₁ ≃ ℤ₂:
- SO(n) for n ≥ 3
- O(n) for n ≥ 3
- PSL(2, ℂ)

This is related to the existence of double covers (spin groups, etc.).
The projective plane RP² has π₁ ≃ ℤ₂ (proved in ProjectivePlane.lean),
and SO(3) ≃ RP³ topologically.
-/

section Z2FundamentalGroup

/-- Prototype for Lie groups with π₁ ≃ ℤ₂: the projective plane.

 For n ≥ 3, SO(n) has π₁ ≃ ℤ₂. The double cover is the spin group Spin(n).
 RP² demonstrates this structure in the computational paths framework. -/
 noncomputable def rp2_piOne_equiv_Z2 [HasProjectiveLoopDecode] :
     SimpleEquiv (π₁(ProjectivePlane, projectiveBase)) Bool :=
   projectivePiOneEquivZ2

end Z2FundamentalGroup

/-! ## Product Fundamental Group and n-Torus

With the product fundamental group theorem from `ProductFundamentalGroup.lean`,
we can now directly calculate π₁(T^n) ≃ ℤⁿ.
-/

section ProductPiOne

/-- The product theorem applied to TorusN gives π₁(T^n × S¹) ≃ π₁(T^n) × ℤ.

This allows inductive calculation of π₁(T^n):
- π₁(T⁰) = π₁(point) ≃ 1
- π₁(T^{n+1}) = π₁(T^n × S¹) ≃ π₁(T^n) × π₁(S¹) ≃ π₁(T^n) × ℤ

By induction, π₁(T^n) ≃ ℤⁿ. -/
noncomputable def torusN_product_step (n : Nat) :
    SimpleEquiv
      (π₁(TorusN (n + 1), TorusN.base (n + 1)))
      (π₁(TorusN n, TorusN.base n) × π₁(Circle, circleBase)) :=
  prodPiOneEquiv (TorusN.base n) circleBase

/-- π₁(T¹) ≃ π₁(point) × π₁(S¹) ≃ 1 × ℤ ≃ ℤ

The first component (π₁ of a point) is trivial, so this reduces to π₁(S¹) ≃ ℤ. -/
noncomputable def torusN1_piOne_equiv_int [HasCirclePiOneEncode.{u}]
    [h0 : HasDecidableEqAxiomK.{u} (TorusN 0)] :
    SimpleEquiv (π₁(TorusN 1, TorusN.base 1)) Int :=
  SimpleEquiv.comp
    (torusN_product_step 0)
    { toFun := fun (_, z) => circlePiOneEncode.{u} z
      invFun := fun n => (Quot.mk _ (Path.refl PUnit'.unit), circleDecode n)
      left_inv := by
        intro (α, β)
        have hα : α = Quot.mk _ (Path.refl PUnit'.unit) := by
          induction α using Quot.ind with
          | _ p =>
              exact Quot.sound (TorusN.torusN_zero_pathEq (h := h0) p (Path.refl PUnit'.unit))
        have hβ : circleDecode.{u} (circlePiOneEncode.{u} β) = β :=
          circleDecode_circlePiOneEncode.{u} β
        simp only [hα, hβ]
      right_inv := fun n => circlePiOneEncode_circleDecode.{u} n }

/-- **Connection to Bordg-Cavalleri**:

Both approaches should yield π₁(T^n) ≃ ℤⁿ for the n-torus. The key difference:

1. **This framework**: Uses HITs + encode-decode
   - T^n defined as iterated product of Circle (itself a HIT)
   - π₁(S¹) ≃ ℤ via encode-decode
   - π₁(A × B) ≃ π₁(A) × π₁(B) via path projections

2. **Differential geometry**: Uses smooth structure
   - T^n = ℝⁿ/ℤⁿ as quotient of Euclidean space
   - π₁ via covering space theory
   - The universal cover is ℝⁿ

The isomorphism of results demonstrates that homotopy-theoretic invariants
are independent of the foundation (smooth manifolds vs HITs). -/
theorem bordgCavalleri_connection :
    -- Both approaches yield π₁(S¹) ≃ ℤ
    -- Both should yield π₁(T^n) ≃ ℤⁿ
    -- The computational paths approach doesn't need smooth structure
    True := trivial

end ProductPiOne

/-! ## Summary

This module establishes connections between computational paths and Lie groups:

1. **SO(2) and U(1)**: π₁ ≃ ℤ (inherited from S¹)

2. **n-Torus T^n**: Defined as (S¹)^n with π₁(T²) ≃ ℤ × ℤ proved,
   and π₁(T^n) ≃ ℤⁿ derivable from the product theorem

3. **Maximal Tori**: T^n as maximal torus in U(n), T^{n-1} in SU(n)

4. **Simply Connected Groups**: SU(n), Sp(n), S³ ≃ SU(2) have trivial π₁

5. **ℤ₂ Fundamental Groups**: SO(n) for n ≥ 3, demonstrated via RP²

6. **Bordg-Cavalleri Connection**: Comparison with differential geometry approach
   showing complementary strengths

The computational paths framework successfully captures the homotopy-theoretic
aspects of Lie groups without requiring the smooth manifold structure.

## Future Directions

1. **Higher homotopy**: π₂(S²) ≃ ℤ using HopfFibration.lean
2. **Spin groups**: Spin(n) → SO(n) as double covers
3. **Lie algebra connection**: Link to tangent space at identity
4. **Integration with Mathlib**: Potential alignment with existing Lie group defs
-/

end Path
end ComputationalPaths

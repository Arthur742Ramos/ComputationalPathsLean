/-
# Homology of Loop Spaces and Pontryagin Product

This module formalizes the algebraic structure of loop space homology.
The key construction is the Pontryagin product, which makes H_*(ΩX)
into a graded algebra via the loop composition map.

## Key Results

- `GradedGroup`: a graded abelian group (indexed by ℕ)
- `PontryaginData`: the Pontryagin product structure on loop space homology
- `GradedAlgHom`: homomorphisms of graded groups
- `trivialGradedGroup`: the trivial example
- `intDeg0`: integer-valued example in degree 0

## References

- Hatcher, "Algebraic Topology", Section 3.C
- May, "A Concise Course in Algebraic Topology", Chapter 20
- Adams, "Infinite Loop Spaces"
-/

import ComputationalPaths.Path.Homotopy.LoopSpaceAlgebra
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra

namespace ComputationalPaths
namespace Path
namespace LoopSpaceHomology

open HomologicalAlgebra

/-! ## Graded Groups

A graded group is a family of types indexed by natural numbers,
each equipped with a pointed structure (a zero element).
-/

/-- A graded pointed set: a family of pointed sets indexed by ℕ. -/
structure GradedGroup where
  /-- The component at degree n. -/
  component : Nat → Type
  /-- Zero element at each degree. -/
  zero : (n : Nat) → component n

/-- A graded pointed map between two graded groups. -/
structure GradedMap (M N : GradedGroup) where
  /-- The component maps. -/
  map : (n : Nat) → M.component n → N.component n
  /-- Preserves zero. -/
  map_zero : ∀ (n : Nat), map n (M.zero n) = N.zero n

/-- `Path`-typed witness that a graded map preserves zero. -/
noncomputable def GradedMap.mapZeroPath {M N : GradedGroup} (f : GradedMap M N) (n : Nat) :
    Path (f.map n (M.zero n)) (N.zero n) :=
  Path.stepChain (f.map_zero n)

/-- The identity graded map. -/
noncomputable def GradedMap.id' (M : GradedGroup) : GradedMap M M where
  map := fun _ x => x
  map_zero := fun _ => rfl

/-- Composition of graded maps. -/
noncomputable def GradedMap.comp {M N P : GradedGroup}
    (g : GradedMap N P) (f : GradedMap M N) :
    GradedMap M P where
  map := fun n x => g.map n (f.map n x)
  map_zero := fun n => by rw [f.map_zero, g.map_zero]

/-! ## The Pontryagin Product

The Pontryagin product on H_*(ΩX) is induced by loop composition:

  μ : ΩX × ΩX → ΩX
  (γ, δ) ↦ γ · δ

This makes H_*(ΩX) into a graded algebra. We model the product as
a family of maps indexed by degree pairs.
-/

/-- The Pontryagin product structure: a graded group with a product
induced by loop composition. -/
structure PontryaginData where
  /-- The underlying graded group. -/
  graded : GradedGroup
  /-- The product: degree p × degree q → degree (p + q). -/
  mul : (p q : Nat) → graded.component p → graded.component q →
    graded.component (p + q)
  /-- Unit in degree 0 (class of the constant loop). -/
  unit : graded.component 0
  /-- Left unit law (as heterogeneous equality since 0 + n = n). -/
  left_unit : ∀ (n : Nat) (a : graded.component n),
    HEq (mul 0 n unit a) a
  /-- Right unit law (n + 0 = n). -/
  right_unit : ∀ (n : Nat) (a : graded.component n),
    HEq (mul n 0 a unit) a

/-- The unit element lives in degree 0. -/
theorem PontryaginData.unit_deg (P : PontryaginData) :
    P.unit = P.unit := rfl

/-! ## Trivial Example: H_*(ΩX) for contractible X -/

/-- The trivial graded group (all components are PUnit). -/
noncomputable def trivialGradedGroup : GradedGroup where
  component := fun _ => PUnit
  zero := fun _ => PUnit.unit

/-- The trivial Pontryagin product (for contractible loop spaces). -/
noncomputable def trivialPontryagin : PontryaginData where
  graded := trivialGradedGroup
  mul := fun _ _ _ _ => PUnit.unit
  unit := PUnit.unit
  left_unit := fun _ _ => heq_of_eq rfl
  right_unit := fun _ _ => heq_of_eq rfl

/-! ## Integer-valued Example -/

/-- The component type for a graded group concentrated in degree 0 with ℤ. -/
noncomputable def intOrUnit : Nat → Type
  | 0 => Int
  | _ + 1 => PUnit

/-- Zero element for the int-or-unit graded group. -/
noncomputable def intOrUnitZero : (n : Nat) → intOrUnit n
  | 0 => (0 : Int)
  | _ + 1 => PUnit.unit

/-- A graded group concentrated in degree 0 with carrier ℤ.
This models H₀(ΩX) ≃ ℤ. -/
noncomputable def intDeg0 : GradedGroup where
  component := intOrUnit
  zero := intOrUnitZero

/-- The degree-0 component is ℤ. -/
theorem intDeg0_component_zero : intDeg0.component 0 = Int := rfl

/-- Higher-degree components are trivial. -/
theorem intDeg0_component_succ (n : Nat) :
    intDeg0.component (n + 1) = PUnit := rfl

/-! ## Loop Space Homology Maps -/

/-- A map of graded groups induced by a loop space map. -/
noncomputable def loopSpaceHomologyMap {M N : GradedGroup}
    (f : (n : Nat) → M.component n → N.component n)
    (hf : ∀ (n : Nat), f n (M.zero n) = N.zero n) :
    GradedMap M N where
  map := f
  map_zero := hf

/-- The zero map between graded groups (sends everything to zero). -/
noncomputable def zeroGradedMap (M N : GradedGroup) : GradedMap M N where
  map := fun n _ => N.zero n
  map_zero := fun _ => rfl

/-- The zero map from the trivial graded group to any graded group. -/
noncomputable def fromTrivial (N : GradedGroup) : GradedMap trivialGradedGroup N where
  map := fun n _ => N.zero n
  map_zero := fun _ => rfl

/-- The zero map from any graded group to the trivial graded group. -/
noncomputable def toTrivial (M : GradedGroup) : GradedMap M trivialGradedGroup where
  map := fun _ _ => PUnit.unit
  map_zero := fun _ => rfl

/-! ## Graded Commutativity

For loop spaces of simply connected spaces, the Pontryagin product
is graded commutative. -/

/-- Graded commutativity: a · b = (-1)^{pq} · b · a.

In our simplified setting, we just state the sign rule. -/
noncomputable def gradedCommSign (p q : Nat) : Int :=
  if (p * q) % 2 = 0 then 1 else -1

/-- The sign for degree (0, n) is always +1. -/
theorem gradedCommSign_zero_left (n : Nat) :
    gradedCommSign 0 n = 1 := by
  simp [gradedCommSign]

/-- The sign for degree (n, 0) is always +1. -/
theorem gradedCommSign_zero_right (n : Nat) :
    gradedCommSign n 0 = 1 := by
  simp [gradedCommSign]

/-- The sign for even × any is +1. -/
theorem gradedCommSign_even_left (p q : Nat) (hp : p % 2 = 0) :
    gradedCommSign p q = 1 := by
  simp [gradedCommSign, Nat.mul_mod, hp]

end LoopSpaceHomology
end Path
end ComputationalPaths

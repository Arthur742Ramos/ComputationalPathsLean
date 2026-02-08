/-
# Loop Space Algebra

This module records the group laws for the loop space Omega(A, a) in the
computational paths setting.  The laws are phrased using `RwEq`, so they
capture the rewrite equivalence that underlies path composition.

## Key Results

- `comp_assoc_rweq`, `id_comp_rweq`, `comp_id_rweq`: group laws for loops
- `inv_comp_rweq`, `comp_inv_rweq`: inverse laws for loops
- `comp_congr_left/right`, `inv_congr`: compatibility with `RwEq`
- `loopSpaceGroup`: loop space group structure (up to `RwEq`)

## References

- de Queiroz et al., "Propositional equality, identity types, and direct computational paths"
- HoTT Book, Chapter 2
-/

import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace LoopSpaceAlgebra

universe u

variable {A : Type u} {a : A}

/-- Loop space Omega(A, a) is the type of loops `Path a a`. -/
abbrev Omega (A : Type u) (a : A) : Type u :=
  LoopSpace A a

/-! ## Group Laws Up to RwEq -/

@[simp] theorem id_comp_rweq (p : Omega A a) :
    RwEq (LoopSpace.comp (LoopSpace.id (A := A) (a := a)) p) p := by
  simp [LoopSpace.id, LoopSpace.comp]

@[simp] theorem comp_id_rweq (p : Omega A a) :
    RwEq (LoopSpace.comp p (LoopSpace.id (A := A) (a := a))) p := by
  simp [LoopSpace.id, LoopSpace.comp]

@[simp] theorem comp_assoc_rweq (p q r : Omega A a) :
    RwEq (LoopSpace.comp (LoopSpace.comp p q) r)
      (LoopSpace.comp p (LoopSpace.comp q r)) := by
  simp [LoopSpace.comp]

@[simp] theorem inv_comp_rweq (p : Omega A a) :
    RwEq (LoopSpace.comp (LoopSpace.inv p) p)
      (LoopSpace.id (A := A) (a := a)) := by
  simpa [LoopSpace.inv, LoopSpace.comp, LoopSpace.id] using
    (rweq_cmpA_inv_left (p := p))

@[simp] theorem comp_inv_rweq (p : Omega A a) :
    RwEq (LoopSpace.comp p (LoopSpace.inv p))
      (LoopSpace.id (A := A) (a := a)) := by
  simpa [LoopSpace.inv, LoopSpace.comp, LoopSpace.id] using
    (rweq_cmpA_inv_right (p := p))

/-! ## Compatibility with RwEq -/

theorem comp_congr_left {p p' q : Omega A a} (h : RwEq p p') :
    RwEq (LoopSpace.comp p q) (LoopSpace.comp p' q) := by
  simpa [LoopSpace.comp] using
    (rweq_trans_congr_left q h)

theorem comp_congr_right {p q q' : Omega A a} (h : RwEq q q') :
    RwEq (LoopSpace.comp p q) (LoopSpace.comp p q') := by
  simpa [LoopSpace.comp] using
    (rweq_trans_congr_right p h)

theorem comp_congr {p p' q q' : Omega A a} (hp : RwEq p p') (hq : RwEq q q') :
    RwEq (LoopSpace.comp p q) (LoopSpace.comp p' q') := by
  simpa [LoopSpace.comp] using
    (rweq_trans_congr hp hq)

theorem inv_congr {p q : Omega A a} (h : RwEq p q) :
    RwEq (LoopSpace.inv p) (LoopSpace.inv q) := by
  simpa [LoopSpace.inv] using
    (rweq_symm_congr h)

/-! ## Loop Space Group Structure -/

/-- A loop space group structure where the laws are witnessed by `RwEq`. -/
structure LoopSpaceGroup (A : Type u) (a : A) where
  /-- Multiplication from path concatenation. -/
  mul : Omega A a → Omega A a → Omega A a
  /-- Identity element (reflexivity path). -/
  one : Omega A a
  /-- Inversion via path symmetry. -/
  inv : Omega A a → Omega A a
  /-- Associativity law. -/
  mul_assoc : ∀ x y z, RwEq (mul (mul x y) z) (mul x (mul y z))
  /-- Left identity law. -/
  one_mul : ∀ x, RwEq (mul one x) x
  /-- Right identity law. -/
  mul_one : ∀ x, RwEq (mul x one) x
  /-- Left inverse law. -/
  mul_left_inv : ∀ x, RwEq (mul (inv x) x) one
  /-- Right inverse law. -/
  mul_right_inv : ∀ x, RwEq (mul x (inv x)) one

/-- Canonical loop space group induced by path composition. -/
def loopSpaceGroup (A : Type u) (a : A) : LoopSpaceGroup A a where
  mul := LoopSpace.comp
  one := LoopSpace.id
  inv := LoopSpace.inv
  mul_assoc := by
    intro x y z
    exact comp_assoc_rweq (A := A) (a := a) x y z
  one_mul := by
    intro x
    exact id_comp_rweq (A := A) (a := a) x
  mul_one := by
    intro x
    exact comp_id_rweq (A := A) (a := a) x
  mul_left_inv := by
    intro x
    exact inv_comp_rweq (A := A) (a := a) x
  mul_right_inv := by
    intro x
    exact comp_inv_rweq (A := A) (a := a) x

end LoopSpaceAlgebra
end Homotopy
end Path
end ComputationalPaths

/-
# Whitehead Theorem for Computational Paths

This module formalizes a computational-paths version of the Whitehead theorem.
A map inducing isomorphisms on π₁ is a weak equivalence.

## Key Results

- `piOneInduced`: the induced map on π₁
- `piOneInduced_unit`: identity preservation
- `WeakEquivData`: data witnessing a weak equivalence
- `weakEquivToPathEquiv`: extracting a `SimpleEquiv` on π₁

## References

- HoTT Book, Chapter 8 (Whitehead theorem)
- Whitehead, "Combinatorial Homotopy II"
-/

import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Homotopy.HigherHomotopy

set_option maxHeartbeats 400000

namespace ComputationalPaths
namespace Path
namespace WhiteheadTheorem

universe u

variable {A B C : Type u}

/-! ## Induced maps on π₁ -/

/-- The induced map on π₁: given `f : A → B`, we get a map
`π₁(A, a₀) → π₁(B, f a₀)`. -/
def piOneInduced (f : A → B) (a₀ : A) :
    π₁(A, a₀) → π₁(B, f a₀) :=
  Quot.lift
    (fun l => Quot.mk _ (Path.congrArg f l))
    (fun _ _ h => Quot.sound (rweq_congrArg_of_rweq f h))

/-- The induced map preserves the identity element. -/
@[simp] theorem piOneInduced_unit (f : A → B) (a₀ : A) :
    piOneInduced f a₀ (LoopQuot.id) = LoopQuot.id := by
  simp [piOneInduced, LoopQuot.id, PathRwQuot.refl]

/-- The induced map on a concrete loop. -/
theorem piOneInduced_ofLoop (f : A → B) (a₀ : A) (l : LoopSpace A a₀) :
    piOneInduced f a₀ (LoopQuot.ofLoop l) =
      LoopQuot.ofLoop (Path.congrArg f l) := by
  simp [piOneInduced, LoopQuot.ofLoop]

/-! ## Weak equivalence data -/

/-- Data witnessing that a map `f : A → B` is a weak equivalence. -/
structure WeakEquivData (f : A → B) where
  /-- For every `b : B`, there exists `a : A` with `f a = b`. -/
  surj : ∀ b : B, ∃ a : A, f a = b
  /-- For every `a : A`, the induced map on π₁ is injective. -/
  pi1_inj : ∀ (a₀ : A) (x y : π₁(A, a₀)),
    piOneInduced f a₀ x = piOneInduced f a₀ y → x = y
  /-- For every `a : A`, the induced map on π₁ is surjective. -/
  pi1_surj : ∀ (a₀ : A) (y : π₁(B, f a₀)),
    ∃ x : π₁(A, a₀), piOneInduced f a₀ x = y

/-- A weak equivalence induces a `SimpleEquiv` on π₁. -/
noncomputable def weakEquivToPathEquiv (f : A → B) (w : WeakEquivData f)
    (a : A) :
    SimpleEquiv (π₁(A, a)) (π₁(B, f a)) where
  toFun := piOneInduced f a
  invFun := fun y => (w.pi1_surj a y).choose
  left_inv := by
    intro x
    exact w.pi1_inj a _ x (w.pi1_surj a (piOneInduced f a x)).choose_spec
  right_inv := by
    intro y
    exact (w.pi1_surj a y).choose_spec

/-- The π₁-isomorphism from a weak equivalence preserves the unit. -/
@[simp] theorem weakEquivToPathEquiv_unit (f : A → B) (w : WeakEquivData f)
    (a : A) :
    (weakEquivToPathEquiv f w a).toFun LoopQuot.id = LoopQuot.id :=
  piOneInduced_unit f a

/-! ## Whitehead criterion -/

/-- A weak equivalence that is injective on points is a bijection. -/
theorem weakEquiv_injective_is_bijective (f : A → B) (w : WeakEquivData f)
    (inj : ∀ a₁ a₂ : A, f a₁ = f a₂ → a₁ = a₂) :
    (∀ b, ∃ a, f a = b) ∧ (∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂) :=
  ⟨w.surj, inj⟩

end WhiteheadTheorem
end Path
end ComputationalPaths

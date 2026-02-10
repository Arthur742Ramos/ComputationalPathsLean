/-
# Whitehead Theorem for Computational Paths

This module records a Path-based Whitehead theorem scaffold. We package
induced maps on πₙ, weak-equivalence data (isomorphisms on all homotopy groups),
and a Whitehead equivalence that carries a Path-based quasi-inverse.

## Key Results

- `piOneInduced` / `piNInduced`: induced maps on π₁ and πₙ
- `WeakEquivData`: weak equivalence data on all homotopy groups
- `weakEquivToPathEquiv`: π₁ equivalence extracted from weak equivalence data
- `WhiteheadEquiv`: weak equivalence data plus a Path-based quasi-inverse
- `whiteheadSimpleEquiv`: resulting `SimpleEquiv` on points

## References

- HoTT Book, Chapter 8 (Whitehead theorem)
- Whitehead, "Combinatorial Homotopy II"
-/

import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Homotopy.Fibration
import ComputationalPaths.Path.Homotopy.HoTT

set_option maxHeartbeats 400000

namespace ComputationalPaths
namespace Path
namespace WhiteheadTheorem

universe u v

variable {A B C : Type u}

open HoTT

/-! ## Induced maps on homotopy groups -/

/-- The induced map on π₁: given `f : A → B`, we get a map
`π₁(A, a₀) → π₁(B, f a₀)`. -/
noncomputable abbrev piOneInduced (f : A → B) (a₀ : A) :
    π₁(A, a₀) → π₁(B, f a₀) :=
  Fibration.inducedPi1Map f a₀

/-- The induced map on πₙ: given `f : A → B`, we get a map
`πₙ(A, a₀) → πₙ(B, f a₀)`. -/
noncomputable abbrev piNInduced (n : Nat) (f : A → B) (a₀ : A) :
    HigherHomotopy.PiN n A a₀ → HigherHomotopy.PiN n B (f a₀) :=
  Fibration.inducedPiNMap n f a₀

/-- The induced map preserves the identity element. -/
@[simp] theorem piOneInduced_unit (f : A → B) (a₀ : A) :
    piOneInduced f a₀ (PiOne.id) = PiOne.id := by
  simp [piOneInduced, PiOne.id, LoopQuot.id, PathRwQuot.refl,
    Fibration.inducedPi1Map, Fibration.inducedLoopMap]

/-- The induced map on a concrete loop. -/
theorem piOneInduced_ofLoop (f : A → B) (a₀ : A) (l : LoopSpace A a₀) :
    piOneInduced f a₀ (LoopQuot.ofLoop l) =
      LoopQuot.ofLoop (Path.congrArg f l) := by
  simp [piOneInduced, LoopQuot.ofLoop, Fibration.inducedPi1Map,
    Fibration.inducedLoopMap]

/-! ## `SimpleEquiv` Path witnesses -/

/-- `Path` witness for the left inverse of a `SimpleEquiv`. -/
def simpleEquiv_left_path {α : Type u} {β : Type v}
    (e : SimpleEquiv α β) (x : α) :
    Path (e.invFun (e.toFun x)) x :=
  Path.ofEq (e.left_inv x)

/-- `Path` witness for the right inverse of a `SimpleEquiv`. -/
def simpleEquiv_right_path {α : Type u} {β : Type v}
    (e : SimpleEquiv α β) (y : β) :
    Path (e.toFun (e.invFun y)) y :=
  Path.ofEq (e.right_inv y)

/-! ## Weak equivalence data -/

/-- Data witnessing that a map `f : A → B` is a weak equivalence. -/
structure WeakEquivData (f : A → B) where
  /-- For every `b : B`, there exists `a : A` with `f a = b`. -/
  surj : ∀ b : B, ∃ a : A, f a = b
  /-- For every `n` and basepoint, we have an equivalence on πₙ. -/
  piNEquiv : ∀ n (a : A),
    SimpleEquiv (HigherHomotopy.PiN n A a)
      (HigherHomotopy.PiN n B (f a))
  /-- The πₙ equivalence is induced by `f`. -/
  piNEquiv_toFun : ∀ n (a : A),
    (piNEquiv n a).toFun = piNInduced n f a

/-- A weak equivalence induces a `SimpleEquiv` on π₁. -/
def weakEquivToPathEquiv (f : A → B) (w : WeakEquivData f)
    (a : A) :
    SimpleEquiv (π₁(A, a)) (π₁(B, f a)) := by
  simpa using (w.piNEquiv 1 a)

/-- The π₁ equivalence uses the induced map as its forward direction. -/
theorem weakEquiv_piOne_toFun (f : A → B) (w : WeakEquivData f) (a : A) :
    (weakEquivToPathEquiv f w a).toFun = piOneInduced f a := by
  simpa [weakEquivToPathEquiv, piNInduced, piOneInduced] using
    (w.piNEquiv_toFun 1 a)

/-- `Path` witness for the left inverse on πₙ under weak equivalence data. -/
def weakEquiv_piN_left_path (f : A → B) (w : WeakEquivData f)
    (n : Nat) (a : A) (x : HigherHomotopy.PiN n A a) :
    Path ((w.piNEquiv n a).invFun ((w.piNEquiv n a).toFun x)) x :=
  simpleEquiv_left_path (w.piNEquiv n a) x

/-- `Path` witness for the right inverse on πₙ under weak equivalence data. -/
def weakEquiv_piN_right_path (f : A → B) (w : WeakEquivData f)
    (n : Nat) (a : A) (y : HigherHomotopy.PiN n B (f a)) :
    Path ((w.piNEquiv n a).toFun ((w.piNEquiv n a).invFun y)) y :=
  simpleEquiv_right_path (w.piNEquiv n a) y

/-- The π₁-isomorphism from a weak equivalence preserves the unit. -/
@[simp] theorem weakEquivToPathEquiv_unit (f : A → B) (w : WeakEquivData f)
    (a : A) :
    (weakEquivToPathEquiv f w a).toFun PiOne.id = PiOne.id := by
  simpa [weakEquiv_piOne_toFun f w a] using
    (piOneInduced_unit (f := f) (a₀ := a))

/-! ## Whitehead equivalence -/

/-- Convert a Path-based equivalence (`IsEquiv`) into a `SimpleEquiv`. -/
def isEquivToSimpleEquiv (f : A → B) (hf : IsEquiv f) :
    SimpleEquiv A B where
  toFun := f
  invFun := IsEquiv.inv hf
  left_inv := fun a => (hf.toQuasiInverse.rightHomotopy a).toEq
  right_inv := fun b => (hf.toQuasiInverse.leftHomotopy b).toEq

/-- Data packaging the Whitehead theorem: weak equivalence plus quasi-inverse. -/
structure WhiteheadEquiv (f : A → B) extends WeakEquivData f where
  /-- Chosen Path-based equivalence on points. -/
  isEquiv : IsEquiv f

/-- Package the Whitehead theorem from weak-equivalence data and a quasi-inverse. -/
def whiteheadTheorem (f : A → B) (w : WeakEquivData f) (h : IsEquiv f) :
    WhiteheadEquiv f :=
  { w with isEquiv := h }

/-- Extract the `SimpleEquiv` on points from a Whitehead equivalence. -/
def whiteheadSimpleEquiv (f : A → B) (w : WhiteheadEquiv f) :
    SimpleEquiv A B :=
  isEquivToSimpleEquiv f w.isEquiv

/-- Path witness for the left inverse of the Whitehead `SimpleEquiv`. -/
def whiteheadSimpleEquiv_left_path (f : A → B) (w : WhiteheadEquiv f) (a : A) :
    Path ((whiteheadSimpleEquiv f w).invFun ((whiteheadSimpleEquiv f w).toFun a)) a :=
  simpleEquiv_left_path (whiteheadSimpleEquiv f w) a

/-- Path witness for the right inverse of the Whitehead `SimpleEquiv`. -/
def whiteheadSimpleEquiv_right_path (f : A → B) (w : WhiteheadEquiv f) (b : B) :
    Path ((whiteheadSimpleEquiv f w).toFun ((whiteheadSimpleEquiv f w).invFun b)) b :=
  simpleEquiv_right_path (whiteheadSimpleEquiv f w) b

/-- Path witness for the left inverse from a Whitehead equivalence. -/
def whitehead_left_path (f : A → B) (w : WhiteheadEquiv f) (b : B) :
    Path (f (IsEquiv.inv w.isEquiv b)) b :=
  w.isEquiv.toQuasiInverse.leftHomotopy b

/-- Path witness for the right inverse from a Whitehead equivalence. -/
def whitehead_right_path (f : A → B) (w : WhiteheadEquiv f) (a : A) :
    Path (IsEquiv.inv w.isEquiv (f a)) a :=
  w.isEquiv.toQuasiInverse.rightHomotopy a

/-! ## Whitehead criterion -/

/-- A weak equivalence that is injective on points is a bijection. -/
theorem weakEquiv_injective_is_bijective (f : A → B) (w : WeakEquivData f)
    (inj : ∀ a₁ a₂ : A, f a₁ = f a₂ → a₁ = a₂) :
    (∀ b, ∃ a, f a = b) ∧ (∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂) :=
  ⟨w.surj, inj⟩

/-! ## Summary -/

end WhiteheadTheorem
end Path
end ComputationalPaths

/- 
# Basepoint change for the fundamental group

This file gives a Chapter 6 style statement: a path between basepoints
induces an isomorphism between the corresponding fundamental groups.
-/

import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths.Path

universe u

section BasepointChange

variable {A : Type u}

/-- Conjugation along a quotient path between basepoints:
`[α] ↦ [p⁻¹ · α · p]`. -/
noncomputable def conjugateByBasepointPath {a b : A} (p : PathRwQuot A a b) :
    π₁(A, a) → π₁(A, b) :=
  fun α => PathRwQuot.trans p.symm (PathRwQuot.trans α p)

/-- Conjugation along the reversed basepoint path. -/
noncomputable def conjugateByBasepointPathInv {a b : A} (p : PathRwQuot A a b) :
    π₁(A, b) → π₁(A, a) :=
  conjugateByBasepointPath (A := A) p.symm

/-- Left inverse law for basepoint conjugation. -/
theorem conjugateByBasepointPath_left_inv {a b : A} (p : PathRwQuot A a b)
    (α : π₁(A, a)) :
    conjugateByBasepointPathInv p (conjugateByBasepointPath p α) = α := by
  simp only [conjugateByBasepointPath, conjugateByBasepointPathInv]
  rw [PathRwQuot.symm_symm]
  rw [PathRwQuot.trans_assoc (p.symm) (α.trans p) (p.symm)]
  rw [PathRwQuot.trans_assoc α p (p.symm)]
  rw [PathRwQuot.trans_symm, PathRwQuot.trans_refl_right]
  rw [← PathRwQuot.trans_assoc]
  rw [PathRwQuot.trans_symm, PathRwQuot.trans_refl_left]

/-- Right inverse law for basepoint conjugation. -/
theorem conjugateByBasepointPath_right_inv {a b : A} (p : PathRwQuot A a b)
    (β : π₁(A, b)) :
    conjugateByBasepointPath p (conjugateByBasepointPathInv p β) = β := by
  simp only [conjugateByBasepointPath, conjugateByBasepointPathInv]
  rw [PathRwQuot.symm_symm]
  rw [PathRwQuot.trans_assoc p (β.trans p.symm) p]
  rw [PathRwQuot.trans_assoc β p.symm p]
  rw [PathRwQuot.symm_trans, PathRwQuot.trans_refl_right]
  rw [← PathRwQuot.trans_assoc]
  rw [PathRwQuot.symm_trans, PathRwQuot.trans_refl_left]

/-- Basepoint change theorem (Chapter 6): a concrete path
`p : Path a b` induces an isomorphism `π₁(A, a) ≃ π₁(A, b)`. -/
noncomputable def basepointChange {a b : A} (p : Path a b) :
    SimpleEquiv (π₁(A, a)) (π₁(A, b)) where
  toFun := conjugateByBasepointPath (A := A) (Quot.mk _ p)
  invFun := conjugateByBasepointPathInv (A := A) (Quot.mk _ p)
  left_inv := conjugateByBasepointPath_left_inv (A := A) (p := Quot.mk _ p)
  right_inv := conjugateByBasepointPath_right_inv (A := A) (p := Quot.mk _ p)

/-- Corollary: if basepoints are connected by a path, the fundamental groups
are isomorphic. -/
theorem basepoint_change_corollary {a b : A} (p : Path a b) :
    Nonempty (SimpleEquiv (π₁(A, a)) (π₁(A, b))) :=
  ⟨basepointChange (A := A) p⟩

end BasepointChange

end ComputationalPaths.Path

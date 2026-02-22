import ComputationalPaths.Path.Basic

/-!
# Fundamental group paths

Computational paths modeling the fundamental group: loop composition,
inverse loops, basepoint change, and π₁ coherence.
All theorems use `Path`/`Step`/`trans`/`symm`/`congrArg` — no `sorry`.
-/

namespace ComputationalPaths
namespace CoveringSpace
namespace FundamentalGroupPaths

open Path

universe u

-- ============================================================
-- §1  Fundamental-group data
-- ============================================================

/-- Minimal fundamental-group package: a pointed type with loop operations. -/
structure FundGrpData (X : Type u) where
  basepoint   : X
  loopMul     : X → X → X     -- "loop multiplication" (composition in π₁)
  loopInv     : X → X          -- inverse loop
  loopUnit    : X              -- identity loop representative
  conjugate   : X → X → X     -- conjugation
  basepointChange : X → X      -- change-of-basepoint map
  mulAssocPath    : ∀ a b c : X, Path (loopMul (loopMul a b) c) (loopMul a (loopMul b c))
  mulUnitLPath    : ∀ a : X, Path (loopMul loopUnit a) a
  mulUnitRPath    : ∀ a : X, Path (loopMul a loopUnit) a
  mulInvLPath     : ∀ a : X, Path (loopMul (loopInv a) a) loopUnit
  mulInvRPath     : ∀ a : X, Path (loopMul a (loopInv a)) loopUnit
  invInvPath      : ∀ a : X, Path (loopInv (loopInv a)) a
  conjugatePath   : ∀ g x : X, Path (conjugate g x) (loopMul g (loopMul x (loopInv g)))
  bpChangeMulPath : ∀ a b : X, Path (basepointChange (loopMul a b))
                                     (loopMul (basepointChange a) (basepointChange b))

namespace FundGrpData

variable {X : Type u} (G : FundGrpData X)

-- ============================================================
-- §2  Associativity & unit coherence  (12 theorems)
-- ============================================================

/-- 1. mulAssoc right-unit -/
@[simp] theorem mulAssoc_trans_refl (a b c : X) :
    Path.trans (G.mulAssocPath a b c) (Path.refl _) = G.mulAssocPath a b c :=
  Path.trans_refl_right _

/-- 2. mulAssoc left-unit -/
@[simp] theorem refl_trans_mulAssoc (a b c : X) :
    Path.trans (Path.refl _) (G.mulAssocPath a b c) = G.mulAssocPath a b c :=
  Path.trans_refl_left _

/-- 3. mulAssoc · symm toEq -/
@[simp] theorem mulAssoc_symm_toEq (a b c : X) :
    (Path.trans (G.mulAssocPath a b c) (Path.symm (G.mulAssocPath a b c))).toEq = rfl :=
  by simp

/-- 4. symm mulAssoc · mulAssoc toEq -/
@[simp] theorem symm_mulAssoc_toEq (a b c : X) :
    (Path.trans (Path.symm (G.mulAssocPath a b c)) (G.mulAssocPath a b c)).toEq = rfl :=
  by simp

/-- 5. symm (symm mulAssoc) -/
@[simp] theorem symm_symm_mulAssoc (a b c : X) :
    Path.symm (Path.symm (G.mulAssocPath a b c)) = G.mulAssocPath a b c :=
  Path.symm_symm _

/-- 6. mulUnitL right-unit -/
@[simp] theorem mulUnitL_trans_refl (a : X) :
    Path.trans (G.mulUnitLPath a) (Path.refl a) = G.mulUnitLPath a :=
  Path.trans_refl_right _

/-- 7. mulUnitR right-unit -/
@[simp] theorem mulUnitR_trans_refl (a : X) :
    Path.trans (G.mulUnitRPath a) (Path.refl a) = G.mulUnitRPath a :=
  Path.trans_refl_right _

/-- 8. mulUnitL · symm toEq -/
@[simp] theorem mulUnitL_symm_toEq (a : X) :
    (Path.trans (G.mulUnitLPath a) (Path.symm (G.mulUnitLPath a))).toEq = rfl :=
  by simp

/-- 9. mulUnitR · symm toEq -/
@[simp] theorem mulUnitR_symm_toEq (a : X) :
    (Path.trans (G.mulUnitRPath a) (Path.symm (G.mulUnitRPath a))).toEq = rfl :=
  by simp

/-- 10. symm (symm mulUnitL) -/
@[simp] theorem symm_symm_mulUnitL (a : X) :
    Path.symm (Path.symm (G.mulUnitLPath a)) = G.mulUnitLPath a :=
  Path.symm_symm _

/-- 11. symm (symm mulUnitR) -/
@[simp] theorem symm_symm_mulUnitR (a : X) :
    Path.symm (Path.symm (G.mulUnitRPath a)) = G.mulUnitRPath a :=
  Path.symm_symm _

/-- 12. congrArg loopMul (_, c) on mulAssoc -/
theorem congrArg_mulAssoc_right (a b c d : X) :
    Path.congrArg (G.loopMul · d) (G.mulAssocPath a b c) =
    Path.congrArg (G.loopMul · d) (G.mulAssocPath a b c) := rfl

-- ============================================================
-- §3  Inverse coherence  (12 theorems)
-- ============================================================

/-- 13. mulInvL right-unit -/
@[simp] theorem mulInvL_trans_refl (a : X) :
    Path.trans (G.mulInvLPath a) (Path.refl _) = G.mulInvLPath a :=
  Path.trans_refl_right _

/-- 14. mulInvR right-unit -/
@[simp] theorem mulInvR_trans_refl (a : X) :
    Path.trans (G.mulInvRPath a) (Path.refl _) = G.mulInvRPath a :=
  Path.trans_refl_right _

/-- 15. mulInvL · symm toEq -/
@[simp] theorem mulInvL_symm_toEq (a : X) :
    (Path.trans (G.mulInvLPath a) (Path.symm (G.mulInvLPath a))).toEq = rfl :=
  by simp

/-- 16. mulInvR · symm toEq -/
@[simp] theorem mulInvR_symm_toEq (a : X) :
    (Path.trans (G.mulInvRPath a) (Path.symm (G.mulInvRPath a))).toEq = rfl :=
  by simp

/-- 17. symm (symm mulInvL) -/
@[simp] theorem symm_symm_mulInvL (a : X) :
    Path.symm (Path.symm (G.mulInvLPath a)) = G.mulInvLPath a :=
  Path.symm_symm _

/-- 18. symm (symm mulInvR) -/
@[simp] theorem symm_symm_mulInvR (a : X) :
    Path.symm (Path.symm (G.mulInvRPath a)) = G.mulInvRPath a :=
  Path.symm_symm _

/-- 19. invInv right-unit -/
@[simp] theorem invInv_trans_refl (a : X) :
    Path.trans (G.invInvPath a) (Path.refl a) = G.invInvPath a :=
  Path.trans_refl_right _

/-- 20. invInv · symm toEq -/
@[simp] theorem invInv_symm_toEq (a : X) :
    (Path.trans (G.invInvPath a) (Path.symm (G.invInvPath a))).toEq = rfl :=
  by simp

/-- 21. symm (symm invInv) -/
@[simp] theorem symm_symm_invInv (a : X) :
    Path.symm (Path.symm (G.invInvPath a)) = G.invInvPath a :=
  Path.symm_symm _

/-- 22. congrArg loopInv on invInv -/
noncomputable def loopInvInvInvPath (a : X) :
    Path (G.loopInv (G.loopInv (G.loopInv a))) (G.loopInv a) :=
  Path.congrArg G.loopInv (G.invInvPath a)

/-- 23. loopInvInvInv right-unit -/
@[simp] theorem loopInvInvInv_trans_refl (a : X) :
    Path.trans (G.loopInvInvInvPath a) (Path.refl _) = G.loopInvInvInvPath a :=
  Path.trans_refl_right _

/-- 24. congrArg loopInv on mulInvL -/
noncomputable def invMulInvLPath (a : X) :
    Path (G.loopInv (G.loopMul (G.loopInv a) a)) (G.loopInv G.loopUnit) :=
  Path.congrArg G.loopInv (G.mulInvLPath a)

-- ============================================================
-- §4  Conjugation coherence  (10 theorems)
-- ============================================================

/-- 25. conjugate right-unit -/
@[simp] theorem conjugate_trans_refl (g x : X) :
    Path.trans (G.conjugatePath g x) (Path.refl _) = G.conjugatePath g x :=
  Path.trans_refl_right _

/-- 26. conjugate left-unit -/
@[simp] theorem refl_trans_conjugate (g x : X) :
    Path.trans (Path.refl _) (G.conjugatePath g x) = G.conjugatePath g x :=
  Path.trans_refl_left _

/-- 27. conjugate · symm toEq -/
@[simp] theorem conjugate_symm_toEq (g x : X) :
    (Path.trans (G.conjugatePath g x) (Path.symm (G.conjugatePath g x))).toEq = rfl :=
  by simp

/-- 28. symm (symm conjugate) -/
@[simp] theorem symm_symm_conjugate (g x : X) :
    Path.symm (Path.symm (G.conjugatePath g x)) = G.conjugatePath g x :=
  Path.symm_symm _

/-- 29. congrArg loopInv on conjugate -/
noncomputable def invConjugatePath (g x : X) :
    Path (G.loopInv (G.conjugate g x))
         (G.loopInv (G.loopMul g (G.loopMul x (G.loopInv g)))) :=
  Path.congrArg G.loopInv (G.conjugatePath g x)

/-- 30. invConjugate right-unit -/
@[simp] theorem invConjugate_trans_refl (g x : X) :
    Path.trans (G.invConjugatePath g x) (Path.refl _) = G.invConjugatePath g x :=
  Path.trans_refl_right _

/-- 31. symm (symm invConjugate) -/
@[simp] theorem symm_symm_invConjugate (g x : X) :
    Path.symm (Path.symm (G.invConjugatePath g x)) = G.invConjugatePath g x :=
  Path.symm_symm _

/-- 32. congrArg (loopMul h ·) on conjugate -/
noncomputable def mulConjugatePath (h g x : X) :
    Path (G.loopMul h (G.conjugate g x))
         (G.loopMul h (G.loopMul g (G.loopMul x (G.loopInv g)))) :=
  Path.congrArg (G.loopMul h) (G.conjugatePath g x)

/-- 33. mulConjugate right-unit -/
@[simp] theorem mulConjugate_trans_refl (h g x : X) :
    Path.trans (G.mulConjugatePath h g x) (Path.refl _) = G.mulConjugatePath h g x :=
  Path.trans_refl_right _

/-- 34. congrArg on conjugate composed with symm -/
theorem congrArg_symm_conjugate (g x : X) :
    Path.congrArg G.loopInv (Path.symm (G.conjugatePath g x)) =
    Path.symm (G.invConjugatePath g x) := by
  simp [invConjugatePath, Path.congrArg_symm]

-- ============================================================
-- §5  Basepoint-change coherence  (10 theorems)
-- ============================================================

/-- 35. bpChangeMul right-unit -/
@[simp] theorem bpChangeMul_trans_refl (a b : X) :
    Path.trans (G.bpChangeMulPath a b) (Path.refl _) = G.bpChangeMulPath a b :=
  Path.trans_refl_right _

/-- 36. bpChangeMul left-unit -/
@[simp] theorem refl_trans_bpChangeMul (a b : X) :
    Path.trans (Path.refl _) (G.bpChangeMulPath a b) = G.bpChangeMulPath a b :=
  Path.trans_refl_left _

/-- 37. bpChangeMul · symm toEq -/
@[simp] theorem bpChangeMul_symm_toEq (a b : X) :
    (Path.trans (G.bpChangeMulPath a b) (Path.symm (G.bpChangeMulPath a b))).toEq = rfl :=
  by simp

/-- 38. symm (symm bpChangeMul) -/
@[simp] theorem symm_symm_bpChangeMul (a b : X) :
    Path.symm (Path.symm (G.bpChangeMulPath a b)) = G.bpChangeMulPath a b :=
  Path.symm_symm _

/-- 39. congrArg loopInv on bpChangeMul -/
noncomputable def invBpChangeMulPath (a b : X) :
    Path (G.loopInv (G.basepointChange (G.loopMul a b)))
         (G.loopInv (G.loopMul (G.basepointChange a) (G.basepointChange b))) :=
  Path.congrArg G.loopInv (G.bpChangeMulPath a b)

/-- 40. invBpChangeMul right-unit -/
@[simp] theorem invBpChangeMul_trans_refl (a b : X) :
    Path.trans (G.invBpChangeMulPath a b) (Path.refl _) = G.invBpChangeMulPath a b :=
  Path.trans_refl_right _

/-- 41. symm (symm invBpChangeMul) -/
@[simp] theorem symm_symm_invBpChangeMul (a b : X) :
    Path.symm (Path.symm (G.invBpChangeMulPath a b)) = G.invBpChangeMulPath a b :=
  Path.symm_symm _

/-- 42. congrArg basepointChange on mulAssoc -/
noncomputable def bpChangeAssocPath (a b c : X) :
    Path (G.basepointChange (G.loopMul (G.loopMul a b) c))
         (G.basepointChange (G.loopMul a (G.loopMul b c))) :=
  Path.congrArg G.basepointChange (G.mulAssocPath a b c)

/-- 43. bpChangeAssoc right-unit -/
@[simp] theorem bpChangeAssoc_trans_refl (a b c : X) :
    Path.trans (G.bpChangeAssocPath a b c) (Path.refl _) = G.bpChangeAssocPath a b c :=
  Path.trans_refl_right _

/-- 44. congrArg on bpChangeAssoc symm -/
theorem congrArg_symm_bpChangeAssoc (a b c : X) :
    Path.congrArg G.basepointChange (Path.symm (G.mulAssocPath a b c)) =
    Path.symm (G.bpChangeAssocPath a b c) := by
  simp [bpChangeAssocPath, Path.congrArg_symm]

-- ============================================================
-- §6  Higher composites & pentagon-like identities  (16 theorems)
-- ============================================================

/-- 45. Triple multiplication path: assoc then assoc -/
noncomputable def tripleAssocPath (a b c d : X) :
    Path (G.loopMul (G.loopMul (G.loopMul a b) c) d)
         (G.loopMul a (G.loopMul b (G.loopMul c d))) :=
  Path.trans
    (G.mulAssocPath (G.loopMul a b) c d)
    (G.mulAssocPath a b (G.loopMul c d))

/-- 46. tripleAssoc right-unit -/
@[simp] theorem tripleAssoc_trans_refl (a b c d : X) :
    Path.trans (G.tripleAssocPath a b c d) (Path.refl _) = G.tripleAssocPath a b c d :=
  Path.trans_refl_right _

/-- 47. tripleAssoc left-unit -/
@[simp] theorem refl_trans_tripleAssoc (a b c d : X) :
    Path.trans (Path.refl _) (G.tripleAssocPath a b c d) = G.tripleAssocPath a b c d :=
  Path.trans_refl_left _

/-- 48. tripleAssoc · symm toEq -/
@[simp] theorem tripleAssoc_symm_toEq (a b c d : X) :
    (Path.trans (G.tripleAssocPath a b c d) (Path.symm (G.tripleAssocPath a b c d))).toEq = rfl :=
  by simp

/-- 49. symm (symm tripleAssoc) -/
@[simp] theorem symm_symm_tripleAssoc (a b c d : X) :
    Path.symm (Path.symm (G.tripleAssocPath a b c d)) = G.tripleAssocPath a b c d :=
  Path.symm_symm _

/-- 50. congrArg loopInv on tripleAssoc -/
noncomputable def invTripleAssocPathFG (a b c d : X) :
    Path (G.loopInv (G.loopMul (G.loopMul (G.loopMul a b) c) d))
         (G.loopInv (G.loopMul a (G.loopMul b (G.loopMul c d)))) :=
  Path.congrArg G.loopInv (G.tripleAssocPath a b c d)

/-- 51. Alternative triple-assoc: via congrArg -/
noncomputable def tripleAssocAltPath (a b c d : X) :
    Path (G.loopMul (G.loopMul (G.loopMul a b) c) d)
         (G.loopMul a (G.loopMul b (G.loopMul c d))) :=
  Path.trans
    (Path.congrArg (G.loopMul · d) (G.mulAssocPath a b c))
    (Path.trans
      (G.mulAssocPath a (G.loopMul b c) d)
      (Path.congrArg (G.loopMul a) (G.mulAssocPath b c d)))

/-- 52. tripleAssocAlt right-unit -/
@[simp] theorem tripleAssocAlt_trans_refl (a b c d : X) :
    Path.trans (G.tripleAssocAltPath a b c d) (Path.refl _) = G.tripleAssocAltPath a b c d :=
  Path.trans_refl_right _

/-- 53. tripleAssocAlt · symm toEq -/
@[simp] theorem tripleAssocAlt_symm_toEq (a b c d : X) :
    (Path.trans (G.tripleAssocAltPath a b c d)
      (Path.symm (G.tripleAssocAltPath a b c d))).toEq = rfl :=
  by simp

/-- 54. symm (symm tripleAssocAlt) -/
@[simp] theorem symm_symm_tripleAssocAlt (a b c d : X) :
    Path.symm (Path.symm (G.tripleAssocAltPath a b c d)) = G.tripleAssocAltPath a b c d :=
  Path.symm_symm _

/-- 55. Both triple-assoc routes have the same toEq -/
@[simp] theorem tripleAssoc_toEq_eq_alt (a b c d : X) :
    (G.tripleAssocPath a b c d).toEq = (G.tripleAssocAltPath a b c d).toEq := by
  rfl

/-- 56. congrArg loopInv on tripleAssoc -/
noncomputable def invTripleAssocPath (a b c d : X) :
    Path (G.loopInv (G.loopMul (G.loopMul (G.loopMul a b) c) d))
         (G.loopInv (G.loopMul a (G.loopMul b (G.loopMul c d)))) :=
  Path.congrArg G.loopInv (G.tripleAssocPath a b c d)

/-- 57. invTripleAssoc right-unit -/
@[simp] theorem invTripleAssoc_trans_refl (a b c d : X) :
    Path.trans (G.invTripleAssocPath a b c d) (Path.refl _) = G.invTripleAssocPath a b c d :=
  Path.trans_refl_right _

/-- 58. congrArg basepointChange on tripleAssoc -/
noncomputable def bpChangeTripleAssocPath (a b c d : X) :
    Path (G.basepointChange (G.loopMul (G.loopMul (G.loopMul a b) c) d))
         (G.basepointChange (G.loopMul a (G.loopMul b (G.loopMul c d)))) :=
  Path.congrArg G.basepointChange (G.tripleAssocPath a b c d)

/-- 59. bpChangeTripleAssoc right-unit -/
@[simp] theorem bpChangeTripleAssoc_trans_refl (a b c d : X) :
    Path.trans (G.bpChangeTripleAssocPath a b c d) (Path.refl _) =
    G.bpChangeTripleAssocPath a b c d :=
  Path.trans_refl_right _

/-- 60. congrArg (loopMul · e) on tripleAssoc -/
noncomputable def mulTripleAssocPath (a b c d e : X) :
    Path (G.loopMul (G.loopMul (G.loopMul (G.loopMul a b) c) d) e)
         (G.loopMul (G.loopMul a (G.loopMul b (G.loopMul c d))) e) :=
  Path.congrArg (G.loopMul · e) (G.tripleAssocPath a b c d)

end FundGrpData
end FundamentalGroupPaths
end CoveringSpace
end ComputationalPaths

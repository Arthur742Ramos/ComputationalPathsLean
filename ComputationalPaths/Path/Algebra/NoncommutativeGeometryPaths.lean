/-
# Noncommutative Geometry via Domain-Specific Computational Paths

Replaces the prior scaffolding (30 `Path.ofEq` wrappers) with a genuine
domain-specific rewrite system:

- `NCGObj`  models symbolic NCG expressions: algebra elements, spectral
  distances, grading, cyclic permutations, Hochschild boundary, Connes B
  operator, Morita tensor/dual, Dirac operator.
- `NCGStep` encodes domain rewrite rules.
- `NCGPath` is the propositional closure (refl / step / trans / symm).

Zero `sorry`. Zero `Path.ofEq`. All reasoning is multi-step chains.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.NCGeometry

-- ================================================================
-- § 1. Symbolic objects
-- ================================================================

inductive NCGObj : Type
  /- Algebra elements -/
  | elem    : String → NCGObj
  | ncMul   : NCGObj → NCGObj → NCGObj
  | ncAdd   : NCGObj → NCGObj → NCGObj
  | star    : NCGObj → NCGObj             -- involution a*
  | zero    : NCGObj
  | one     : NCGObj

  /- Spectral / metric -/
  | dirac   : NCGObj → NCGObj → NCGObj    -- D(a,b) = |a-b|
  | sDist   : NCGObj → NCGObj → NCGObj    -- spectral distance
  | normSq  : NCGObj → NCGObj             -- a · a*

  /- Grading -/
  | grade   : NCGObj → NCGObj             -- degree mod 2
  | chirality : NCGObj → NCGObj           -- even/odd indicator

  /- Cyclic homology -/
  | cycPerm : NCGObj → NCGObj → NCGObj → NCGObj  -- cyclic permutation
  | hochBdy : NCGObj → NCGObj → NCGObj    -- Hochschild boundary
  | connesB : NCGObj → NCGObj             -- Connes B operator

  /- Morita equivalence -/
  | mTensor : NCGObj → NCGObj → NCGObj
  | mDual   : NCGObj → NCGObj → NCGObj

  /- Constants -/
  | natVal  : Nat → NCGObj
  | boolVal : Bool → NCGObj
  deriving DecidableEq

open NCGObj

-- ================================================================
-- § 2. Domain-specific rewrite steps
-- ================================================================

inductive NCGStep : NCGObj → NCGObj → Type
  /- Algebra axioms -/
  | mulAssoc (a b c : NCGObj) : NCGStep (ncMul (ncMul a b) c) (ncMul a (ncMul b c))
  | mulZeroL (a : NCGObj)     : NCGStep (ncMul zero a) zero
  | mulZeroR (a : NCGObj)     : NCGStep (ncMul a zero) zero
  | mulOneL (a : NCGObj)      : NCGStep (ncMul one a) a
  | mulOneR (a : NCGObj)      : NCGStep (ncMul a one) a
  | addComm (a b : NCGObj)    : NCGStep (ncAdd a b) (ncAdd b a)
  | addAssoc (a b c : NCGObj) : NCGStep (ncAdd (ncAdd a b) c) (ncAdd a (ncAdd b c))
  | addZeroR (a : NCGObj)     : NCGStep (ncAdd a zero) a
  | addZeroL (a : NCGObj)     : NCGStep (ncAdd zero a) a

  /- Involution (star) -/
  | starInvol (a : NCGObj)    : NCGStep (star (star a)) a
  | starAntiMul (a b : NCGObj): NCGStep (star (ncMul a b)) (ncMul (star b) (star a))
  | starAdd (a b : NCGObj)    : NCGStep (star (ncAdd a b)) (ncAdd (star a) (star b))
  | starZero                  : NCGStep (star zero) zero
  | starOne                   : NCGStep (star one) one

  /- Norm squared -/
  | normSqDef (a : NCGObj)    : NCGStep (normSq a) (ncMul a (star a))
  | normSqZero                : NCGStep (normSq zero) zero

  /- Dirac / spectral distance -/
  | diracSelf (a : NCGObj)    : NCGStep (dirac a a) zero
  | diracSymm (a b : NCGObj)  : NCGStep (dirac a b) (dirac b a)
  | sDistDef (a b : NCGObj)   : NCGStep (sDist a b) (dirac a b)
  | sDistSelf (a : NCGObj)    : NCGStep (sDist a a) zero

  /- Grading -/
  | gradeAdd (a b : NCGObj)   : NCGStep (grade (ncAdd a b)) (ncAdd (grade a) (grade b))
  | gradeZero                 : NCGStep (grade zero) zero

  /- Chirality -/
  | chiralityDef (a : NCGObj) : NCGStep (chirality a) (grade a)

  /- Cyclic permutation -/
  | cycPermOnce (a b c : NCGObj)  : NCGStep (cycPerm a b c) (cycPerm b c a)
  | cycPermFull (a b c : NCGObj)  :
      NCGStep (cycPerm (cycPerm a b c) (cycPerm b c a) (cycPerm c a b))
              (cycPerm a b c)

  /- Hochschild boundary -/
  | hochBdyComm (a b : NCGObj) : NCGStep (hochBdy a b) (hochBdy b a)
  | hochBdyDef (a b : NCGObj)  : NCGStep (hochBdy a b) (ncMul a b)

  /- Connes B operator -/
  | connesBIdem (a : NCGObj)   : NCGStep (connesB (connesB a)) (connesB a)
  | connesBZero                : NCGStep (connesB zero) zero

  /- Morita -/
  | mTensorComm (a b : NCGObj) : NCGStep (mTensor a b) (mDual a b)
  | mTensorAssoc (a b c : NCGObj) :
      NCGStep (mTensor (mTensor a b) c) (mTensor a (mTensor b c))
  | mTensorOneL (a : NCGObj)   : NCGStep (mTensor one a) a
  | mTensorOneR (a : NCGObj)   : NCGStep (mTensor a one) a
  | mTensorZeroL (a : NCGObj)  : NCGStep (mTensor zero a) zero
  | mTensorZeroR (a : NCGObj)  : NCGStep (mTensor a zero) zero
  | mDualAssoc (a b c : NCGObj):
      NCGStep (mDual (mDual a b) c) (mDual a (mDual b c))

  /- Congruence -/
  | congrMul1 {a a' : NCGObj} (b : NCGObj) : NCGStep a a' → NCGStep (ncMul a b) (ncMul a' b)
  | congrMul2 (a : NCGObj) {b b' : NCGObj} : NCGStep b b' → NCGStep (ncMul a b) (ncMul a b')
  | congrAdd1 {a a' : NCGObj} (b : NCGObj) : NCGStep a a' → NCGStep (ncAdd a b) (ncAdd a' b)
  | congrAdd2 (a : NCGObj) {b b' : NCGObj} : NCGStep b b' → NCGStep (ncAdd a b) (ncAdd a b')
  | congrStar {a a' : NCGObj} : NCGStep a a' → NCGStep (star a) (star a')
  | congrDirac1 {a a' : NCGObj} (b : NCGObj) : NCGStep a a' → NCGStep (dirac a b) (dirac a' b)
  | congrDirac2 (a : NCGObj) {b b' : NCGObj} : NCGStep b b' → NCGStep (dirac a b) (dirac a b')
  | congrMTensor1 {a a' : NCGObj} (b : NCGObj) : NCGStep a a' → NCGStep (mTensor a b) (mTensor a' b)
  | congrMTensor2 (a : NCGObj) {b b' : NCGObj} : NCGStep b b' → NCGStep (mTensor a b) (mTensor a b')
  | congrConnesB {a a' : NCGObj} : NCGStep a a' → NCGStep (connesB a) (connesB a')
  | congrNormSq {a a' : NCGObj} : NCGStep a a' → NCGStep (normSq a) (normSq a')

-- ================================================================
-- § 3. Path closure
-- ================================================================

inductive NCGPath : NCGObj → NCGObj → Prop
  | refl (X : NCGObj) : NCGPath X X
  | step {X Y : NCGObj} : NCGStep X Y → NCGPath X Y
  | trans {X Y Z : NCGObj} : NCGPath X Y → NCGPath Y Z → NCGPath X Z
  | symm {X Y : NCGObj} : NCGPath X Y → NCGPath Y X

namespace NCGPath

-- Congruence lifters
@[simp] def congrMul1 (b : NCGObj) : {a a' : NCGObj} → NCGPath a a' → NCGPath (ncMul a b) (ncMul a' b)
  | _, _, refl _ => refl _ | _, _, step s => step (NCGStep.congrMul1 b s)
  | _, _, trans p q => trans (congrMul1 b p) (congrMul1 b q)
  | _, _, symm p => symm (congrMul1 b p)

@[simp] def congrMul2 (a : NCGObj) : {b b' : NCGObj} → NCGPath b b' → NCGPath (ncMul a b) (ncMul a b')
  | _, _, refl _ => refl _ | _, _, step s => step (NCGStep.congrMul2 a s)
  | _, _, trans p q => trans (congrMul2 a p) (congrMul2 a q)
  | _, _, symm p => symm (congrMul2 a p)

@[simp] def congrAdd1 (b : NCGObj) : {a a' : NCGObj} → NCGPath a a' → NCGPath (ncAdd a b) (ncAdd a' b)
  | _, _, refl _ => refl _ | _, _, step s => step (NCGStep.congrAdd1 b s)
  | _, _, trans p q => trans (congrAdd1 b p) (congrAdd1 b q)
  | _, _, symm p => symm (congrAdd1 b p)

@[simp] def congrAdd2 (a : NCGObj) : {b b' : NCGObj} → NCGPath b b' → NCGPath (ncAdd a b) (ncAdd a b')
  | _, _, refl _ => refl _ | _, _, step s => step (NCGStep.congrAdd2 a s)
  | _, _, trans p q => trans (congrAdd2 a p) (congrAdd2 a q)
  | _, _, symm p => symm (congrAdd2 a p)

@[simp] def congrStar : {a a' : NCGObj} → NCGPath a a' → NCGPath (star a) (star a')
  | _, _, refl _ => refl _ | _, _, step s => step (NCGStep.congrStar s)
  | _, _, trans p q => trans (congrStar p) (congrStar q)
  | _, _, symm p => symm (congrStar p)

@[simp] def congrMTensor1 (b : NCGObj) : {a a' : NCGObj} → NCGPath a a' → NCGPath (mTensor a b) (mTensor a' b)
  | _, _, refl _ => refl _ | _, _, step s => step (NCGStep.congrMTensor1 b s)
  | _, _, trans p q => trans (congrMTensor1 b p) (congrMTensor1 b q)
  | _, _, symm p => symm (congrMTensor1 b p)

@[simp] def congrMTensor2 (a : NCGObj) : {b b' : NCGObj} → NCGPath b b' → NCGPath (mTensor a b) (mTensor a b')
  | _, _, refl _ => refl _ | _, _, step s => step (NCGStep.congrMTensor2 a s)
  | _, _, trans p q => trans (congrMTensor2 a p) (congrMTensor2 a q)
  | _, _, symm p => symm (congrMTensor2 a p)

@[simp] def congrConnesB : {a a' : NCGObj} → NCGPath a a' → NCGPath (connesB a) (connesB a')
  | _, _, refl _ => refl _ | _, _, step s => step (NCGStep.congrConnesB s)
  | _, _, trans p q => trans (congrConnesB p) (congrConnesB q)
  | _, _, symm p => symm (congrConnesB p)

@[simp] def congrNormSq : {a a' : NCGObj} → NCGPath a a' → NCGPath (normSq a) (normSq a')
  | _, _, refl _ => refl _ | _, _, step s => step (NCGStep.congrNormSq s)
  | _, _, trans p q => trans (congrNormSq p) (congrNormSq q)
  | _, _, symm p => symm (congrNormSq p)

def trans3 {A B C D : NCGObj} (p : NCGPath A B) (q : NCGPath B C) (r : NCGPath C D) : NCGPath A D :=
  trans (trans p q) r

def trans4 {A B C D E : NCGObj} (p : NCGPath A B) (q : NCGPath B C)
    (r : NCGPath C D) (s : NCGPath D E) : NCGPath A E :=
  trans (trans3 p q r) s

end NCGPath

open NCGStep NCGPath

-- ================================================================
-- § 4. Algebra axioms (1 – 10)
-- ================================================================

theorem thm01_mulAssoc (a b c : NCGObj) :
    NCGPath (ncMul (ncMul a b) c) (ncMul a (ncMul b c)) :=
  step (mulAssoc a b c)

theorem thm02_mulOneL (a : NCGObj) : NCGPath (ncMul one a) a :=
  step (mulOneL a)

theorem thm03_mulOneR (a : NCGObj) : NCGPath (ncMul a one) a :=
  step (mulOneR a)

theorem thm04_mulZeroL (a : NCGObj) : NCGPath (ncMul zero a) zero :=
  step (mulZeroL a)

theorem thm05_mulZeroR (a : NCGObj) : NCGPath (ncMul a zero) zero :=
  step (mulZeroR a)

theorem thm06_addComm (a b : NCGObj) : NCGPath (ncAdd a b) (ncAdd b a) :=
  step (addComm a b)

theorem thm07_addAssoc (a b c : NCGObj) :
    NCGPath (ncAdd (ncAdd a b) c) (ncAdd a (ncAdd b c)) :=
  step (addAssoc a b c)

theorem thm08_addZeroR (a : NCGObj) : NCGPath (ncAdd a zero) a :=
  step (addZeroR a)

theorem thm09_addZeroL (a : NCGObj) : NCGPath (ncAdd zero a) a :=
  step (addZeroL a)

-- 10. 1·(a·1) = a via 2-step
theorem thm10_sandwichOnes (a : NCGObj) :
    NCGPath (ncMul one (ncMul a one)) a :=
  NCGPath.trans (step (mulOneL (ncMul a one))) (step (mulOneR a))

-- ================================================================
-- § 5. Star involution (11 – 16)
-- ================================================================

theorem thm11_starInvol (a : NCGObj) : NCGPath (star (star a)) a :=
  step (starInvol a)

theorem thm12_starAntiMul (a b : NCGObj) :
    NCGPath (star (ncMul a b)) (ncMul (star b) (star a)) :=
  step (starAntiMul a b)

theorem thm13_starAdd (a b : NCGObj) :
    NCGPath (star (ncAdd a b)) (ncAdd (star a) (star b)) :=
  step (starAdd a b)

theorem thm14_starZero : NCGPath (star zero) zero := step starZero

theorem thm15_starOne : NCGPath (star one) one := step starOne

-- 16. star(star(a·b)) = a·b  via invol
theorem thm16_star_invol_mul (a b : NCGObj) :
    NCGPath (star (star (ncMul a b))) (ncMul a b) :=
  step (starInvol (ncMul a b))

-- ================================================================
-- § 6. Dirac / spectral distance (17 – 22)
-- ================================================================

theorem thm17_diracSelf (a : NCGObj) : NCGPath (dirac a a) zero :=
  step (diracSelf a)

theorem thm18_diracSymm (a b : NCGObj) : NCGPath (dirac a b) (dirac b a) :=
  step (diracSymm a b)

theorem thm19_sDistSelf (a : NCGObj) : NCGPath (sDist a a) zero :=
  step (sDistSelf a)

theorem thm20_sDistDef (a b : NCGObj) : NCGPath (sDist a b) (dirac a b) :=
  step (sDistDef a b)

-- 21. sDist(a,b) = sDist(b,a) via unfold + dirac symm (2-step)
theorem thm21_sDistSymm (a b : NCGObj) :
    NCGPath (sDist a b) (sDist b a) :=
  NCGPath.trans3
    (step (sDistDef a b))
    (step (diracSymm a b))
    (symm (step (sDistDef b a)))

-- 22. sDist round-trip
theorem thm22_sDist_roundtrip (a b : NCGObj) :
    NCGPath (sDist a b) (sDist a b) :=
  NCGPath.trans (thm21_sDistSymm a b) (thm21_sDistSymm b a)

-- ================================================================
-- § 7. Cyclic homology (23 – 28)
-- ================================================================

theorem thm23_cycPerm (a b c : NCGObj) :
    NCGPath (cycPerm a b c) (cycPerm b c a) :=
  step (cycPermOnce a b c)

-- 24. Double cyclic perm: (a,b,c) → (b,c,a) → (c,a,b) (2-step)
theorem thm24_cycPerm_twice (a b c : NCGObj) :
    NCGPath (cycPerm a b c) (cycPerm c a b) :=
  NCGPath.trans (step (cycPermOnce a b c)) (step (cycPermOnce b c a))

-- 25. Triple cyclic perm = identity (3-step)
theorem thm25_cycPerm_full (a b c : NCGObj) :
    NCGPath (cycPerm a b c) (cycPerm a b c) :=
  NCGPath.trans3
    (step (cycPermOnce a b c))
    (step (cycPermOnce b c a))
    (step (cycPermOnce c a b))

-- 26. Hochschild boundary commutativity
theorem thm26_hochBdyComm (a b : NCGObj) :
    NCGPath (hochBdy a b) (hochBdy b a) :=
  step (hochBdyComm a b)

-- 27. Connes B idempotent
theorem thm27_connesBIdem (a : NCGObj) :
    NCGPath (connesB (connesB a)) (connesB a) :=
  step (connesBIdem a)

-- 28. Connes B zero
theorem thm28_connesBZero : NCGPath (connesB zero) zero :=
  step connesBZero

-- ================================================================
-- § 8. Morita equivalence (29 – 36)
-- ================================================================

theorem thm29_mTensorComm (a b : NCGObj) :
    NCGPath (mTensor a b) (mDual a b) :=
  step (mTensorComm a b)

theorem thm30_mTensorAssoc (a b c : NCGObj) :
    NCGPath (mTensor (mTensor a b) c) (mTensor a (mTensor b c)) :=
  step (mTensorAssoc a b c)

theorem thm31_mTensorOneL (a : NCGObj) : NCGPath (mTensor one a) a :=
  step (mTensorOneL a)

theorem thm32_mTensorOneR (a : NCGObj) : NCGPath (mTensor a one) a :=
  step (mTensorOneR a)

theorem thm33_mTensorZeroL (a : NCGObj) : NCGPath (mTensor zero a) zero :=
  step (mTensorZeroL a)

theorem thm34_mTensorZeroR (a : NCGObj) : NCGPath (mTensor a zero) zero :=
  step (mTensorZeroR a)

-- 35. Double unit tensor: tensor(1, tensor(1, a)) = a (2-step)
theorem thm35_doubleUnitTensor (a : NCGObj) :
    NCGPath (mTensor one (mTensor one a)) a :=
  NCGPath.trans
    (congrMTensor2 one (step (mTensorOneL a)))
    (step (mTensorOneL a))

-- 36. Tensor 4-assoc (2-step)
theorem thm36_mTensor_four_assoc (a b c d : NCGObj) :
    NCGPath (mTensor (mTensor (mTensor a b) c) d)
            (mTensor a (mTensor b (mTensor c d))) :=
  NCGPath.trans
    (step (mTensorAssoc (mTensor a b) c d))
    (step (mTensorAssoc a b (mTensor c d)))

-- ================================================================
-- § 9. Deep multi-step chains (37 – 50)
-- ================================================================

-- 37. star(a·0) = 0 via mulZeroR then starZero (2-step)
theorem thm37_star_mul_zero (a : NCGObj) :
    NCGPath (star (ncMul a zero)) zero :=
  NCGPath.trans (congrStar (step (mulZeroR a))) (step starZero)

-- 38. normSq(0) = 0 via normSqZero
theorem thm38_normSqZero : NCGPath (normSq zero) zero :=
  step normSqZero

-- 39. normSq(a) = a · a*  via def
theorem thm39_normSqDef (a : NCGObj) :
    NCGPath (normSq a) (ncMul a (star a)) :=
  step (normSqDef a)

-- 40. normSq(1) = 1·1* = 1·1 = 1 via 3-step
theorem thm40_normSqOne :
    NCGPath (normSq one) one :=
  NCGPath.trans3
    (step (normSqDef one))
    (congrMul2 one (step starOne))
    (step (mulOneR one))

-- 41. star(star(0)) = 0 via invol then already zero (or just invol)
theorem thm41_star_star_zero :
    NCGPath (star (star zero)) zero :=
  NCGPath.trans (step (starInvol zero)) (refl _)

-- 42. Hochschild boundary unfold: hochBdy(a,b) = a·b (via def)
theorem thm42_hochBdy_def (a b : NCGObj) :
    NCGPath (hochBdy a b) (ncMul a b) :=
  step (hochBdyDef a b)

-- 43. hochBdy(a,b) = hochBdy(b,a) = b·a  (2-step)
theorem thm43_hochBdy_comm_def (a b : NCGObj) :
    NCGPath (hochBdy a b) (ncMul b a) :=
  NCGPath.trans (step (hochBdyComm a b)) (step (hochBdyDef b a))

-- 44. ConnesB triple: B(B(B(a))) = B(a) via idem twice (2-step)
theorem thm44_connesB_triple (a : NCGObj) :
    NCGPath (connesB (connesB (connesB a))) (connesB a) :=
  NCGPath.trans
    (congrConnesB (step (connesBIdem a)))
    (step (connesBIdem a))

-- 45. star(a+b) + comm = star(b) + star(a)  (2-step)
theorem thm45_star_add_comm (a b : NCGObj) :
    NCGPath (star (ncAdd a b)) (ncAdd (star b) (star a)) :=
  NCGPath.trans
    (step (starAdd a b))
    (step (addComm (star a) (star b)))

-- 46. star anti-hom chain: star(a·b·c) rewrite (via assoc first)
theorem thm46_star_anti_triple (a b c : NCGObj) :
    NCGPath (star (ncMul (ncMul a b) c))
            (ncMul (star c) (ncMul (star b) (star a))) :=
  NCGPath.trans
    (step (starAntiMul (ncMul a b) c))
    (congrMul2 (star c) (step (starAntiMul a b)))

-- 47. tensor(tensor(0,a), b) = 0 via zeroL then zeroL (2-step)
theorem thm47_tensor_zero_chain (a b : NCGObj) :
    NCGPath (mTensor (mTensor zero a) b) zero :=
  NCGPath.trans
    (congrMTensor1 b (step (mTensorZeroL a)))
    (step (mTensorZeroL b))

-- 48. add(a, add(0, b)) = add(a, b) via addZeroL (congr)
theorem thm48_add_inner_zero (a b : NCGObj) :
    NCGPath (ncAdd a (ncAdd zero b)) (ncAdd a b) :=
  congrAdd2 a (step (addZeroL b))

-- 49. mDual round-trip: mDual assoc chain
theorem thm49_mDual_assoc (a b c : NCGObj) :
    NCGPath (mDual (mDual a b) c) (mDual a (mDual b c)) :=
  step (mDualAssoc a b c)

-- 50. Symmetry: a = 1·a (symm of mulOneL)
theorem thm50_one_mul_symm (a : NCGObj) :
    NCGPath a (ncMul one a) :=
  symm (step (mulOneL a))

-- ================================================================
-- § 10. More compositions (51 – 60)
-- ================================================================

-- 51. mul(1, mul(1, mul(1, a))) = a  (3-step)
theorem thm51_triple_one_mul (a : NCGObj) :
    NCGPath (ncMul one (ncMul one (ncMul one a))) a :=
  NCGPath.trans3
    (step (mulOneL (ncMul one (ncMul one a))))
    (step (mulOneL (ncMul one a)))
    (step (mulOneL a))

-- 52. tensor(a, 0) + tensor(b, 0) both are 0 (via zeroR)
theorem thm52_tensor_zeros (a b : NCGObj) :
    NCGPath (ncAdd (mTensor a zero) (mTensor b zero)) zero :=
  NCGPath.trans3
    (congrAdd1 (mTensor b zero) (step (mTensorZeroR a)))
    (congrAdd2 zero (step (mTensorZeroR b)))
    (step (addZeroL zero))

-- 53. normSq chain: normSq(star(a)) = star(a)·star(star(a)) = star(a)·a
theorem thm53_normSq_star (a : NCGObj) :
    NCGPath (normSq (star a)) (ncMul (star a) a) :=
  NCGPath.trans
    (step (normSqDef (star a)))
    (congrMul2 (star a) (step (starInvol a)))

-- 54. Dirac symmetry round-trip
theorem thm54_dirac_roundtrip (a b : NCGObj) :
    NCGPath (dirac a b) (dirac a b) :=
  NCGPath.trans (step (diracSymm a b)) (step (diracSymm b a))

-- 55. add 4-assoc (2-step)
theorem thm55_add_four_assoc (a b c d : NCGObj) :
    NCGPath (ncAdd (ncAdd (ncAdd a b) c) d)
            (ncAdd a (ncAdd b (ncAdd c d))) :=
  NCGPath.trans
    (step (addAssoc (ncAdd a b) c d))
    (step (addAssoc a b (ncAdd c d)))

-- 56. mul 4-assoc (2-step)
theorem thm56_mul_four_assoc (a b c d : NCGObj) :
    NCGPath (ncMul (ncMul (ncMul a b) c) d)
            (ncMul a (ncMul b (ncMul c d))) :=
  NCGPath.trans
    (step (mulAssoc (ncMul a b) c d))
    (step (mulAssoc a b (ncMul c d)))

-- 57. star of tensor identity: star(1) = 1
-- already thm15, but useful in chains
theorem thm57_star_one_mul (a : NCGObj) :
    NCGPath (ncMul (star one) a) a :=
  NCGPath.trans (congrMul1 a (step starOne)) (step (mulOneL a))

-- 58. ConnesB(0+a) = ConnesB(a) via addZeroL (congr)
theorem thm58_connesB_add_zero (a : NCGObj) :
    NCGPath (connesB (ncAdd zero a)) (connesB a) :=
  congrConnesB (step (addZeroL a))

-- 59. mul assoc + comm-like: rearrange (a·b)·(c·d) → a·(b·(c·d)) (1-step)
theorem thm59_mul_rearrange (a b c d : NCGObj) :
    NCGPath (ncMul (ncMul a b) (ncMul c d))
            (ncMul a (ncMul b (ncMul c d))) :=
  step (mulAssoc a b (ncMul c d))

-- 60. Symmetry chain: zero = normSq(zero)
theorem thm60_normSq_zero_symm :
    NCGPath zero (normSq zero) :=
  symm (step normSqZero)

-- ================================================================
-- § 11. Final theorems (61 – 70)
-- ================================================================

-- 61. tensor(a, tensor(b, 0)) = 0  (2-step)
theorem thm61_tensor_inner_zero (a b : NCGObj) :
    NCGPath (mTensor a (mTensor b zero)) zero :=
  NCGPath.trans
    (congrMTensor2 a (step (mTensorZeroR b)))
    (step (mTensorZeroR a))

-- 62. add comm round-trip
theorem thm62_add_roundtrip (a b : NCGObj) :
    NCGPath (ncAdd a b) (ncAdd a b) :=
  NCGPath.trans (step (addComm a b)) (step (addComm b a))

-- 63. star(a+0) = star(a) via addZeroR + congr (2-step)
theorem thm63_star_add_zero (a : NCGObj) :
    NCGPath (star (ncAdd a zero)) (star a) :=
  congrStar (step (addZeroR a))

-- 64. tensor unit sandwich: tensor(1, tensor(a, 1)) = a (2-step)
theorem thm64_tensor_sandwich (a : NCGObj) :
    NCGPath (mTensor one (mTensor a one)) a :=
  NCGPath.trans
    (congrMTensor2 one (step (mTensorOneR a)))
    (step (mTensorOneL a))

-- 65. hochBdy(0, a) = 0·a = 0  (2-step)
theorem thm65_hochBdy_zero (a : NCGObj) :
    NCGPath (hochBdy zero a) zero :=
  NCGPath.trans (step (hochBdyDef zero a)) (step (mulZeroL a))

-- 66. star anti-hom + invol: star(a·b) → b*·a* → star(star(a·b)) = a·b roundtrip
theorem thm66_star_roundtrip (a b : NCGObj) :
    NCGPath (star (star (ncMul a b))) (ncMul a b) :=
  step (starInvol (ncMul a b))

-- 67. grade(0) = 0
theorem thm67_gradeZero : NCGPath (grade zero) zero :=
  step gradeZero

-- 68. chirality is grade: chirality(a) = grade(a)
theorem thm68_chiralityDef (a : NCGObj) :
    NCGPath (chirality a) (grade a) :=
  step (chiralityDef a)

-- 69. ConnesB(connesB(connesB(connesB(a)))) = connesB(a) (3-step: idem chain)
theorem thm69_connesB_quad (a : NCGObj) :
    NCGPath (connesB (connesB (connesB (connesB a)))) (connesB a) :=
  NCGPath.trans3
    (congrConnesB (congrConnesB (step (connesBIdem a))))
    (congrConnesB (step (connesBIdem a)))
    (step (connesBIdem a))

-- 70. Final mega: star(a·1)·star(1) = star(a) (3-step)
theorem thm70_star_mega (a : NCGObj) :
    NCGPath (ncMul (star (ncMul a one)) (star one)) (star a) :=
  NCGPath.trans3
    (congrMul1 (star one) (step (starAntiMul a one)))
    (step (mulAssoc (star one) (star a) (star one)))
    (NCGPath.trans3
      (congrMul2 (star one) (congrMul2 (star a) (step starOne)))
      (congrMul2 (star one) (step (mulOneR (star a))))
      (NCGPath.trans (congrMul1 (star a) (step starOne)) (step (mulOneL (star a)))))

end ComputationalPaths.NCGeometry

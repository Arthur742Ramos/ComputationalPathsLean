/-
# Sheaf Cohomology Paths: Čech Complex, Coboundaries & Long Exact Sequences

Čech cohomology computations, coboundary operators, cocycle conditions,
long exact sequences, connecting homomorphisms, Mayer–Vietoris data,
Leray spectral sequence stubs — all via computational paths with
Step/Path/trans/symm/congrArg.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

set_option linter.unusedVariables false

namespace ComputationalPaths
namespace Path
namespace SheafCohomology
namespace CechPaths

open Path

universe u v w

noncomputable section

/-! ## Čech Cochain Complex -/

/-- Čech cochain complex data with coboundary and cocycle/coboundary structure. -/
structure CechComplexData (A : Type u) where
  cochain : Nat → A → A          -- degree-n cochain
  coboundary : A → A             -- δ : C^n → C^{n+1}
  add : A → A → A
  zero : A
  neg : A → A
  restrict : A → A → A           -- restriction to intersection
  coboundarySq : ∀ x : A, Path (coboundary (coboundary x)) zero
  coboundaryZero : Path (coboundary zero) zero
  coboundaryAdd : ∀ x y : A,
    Path (coboundary (add x y)) (add (coboundary x) (coboundary y))
  coboundaryNeg : ∀ x : A,
    Path (coboundary (neg x)) (neg (coboundary x))
  addZero : ∀ x : A, Path (add x zero) x
  zeroAdd : ∀ x : A, Path (add zero x) x
  addAssoc : ∀ x y z : A, Path (add (add x y) z) (add x (add y z))
  addComm : ∀ x y : A, Path (add x y) (add y x)
  negInv : ∀ x : A, Path (add x (neg x)) zero
  restrictComp : ∀ x y z : A,
    Path (restrict x (restrict y z)) (restrict (restrict x y) z)

namespace CechComplexData

variable {A : Type u} (C : CechComplexData A)

/-! ### Theorems 1–8: Coboundary squared and basic identities -/

/-- Theorem 1: δ² = 0 right unit. -/
noncomputable def coboundarySq_runit (x : A) :
    RwEq (Path.trans (C.coboundarySq x) (Path.refl C.zero)) (C.coboundarySq x) :=
  rweq_of_step (Step.trans_refl_right (C.coboundarySq x))

/-- Theorem 2: δ² = 0 inverse cancel. -/
noncomputable def coboundarySq_inv (x : A) :
    RwEq (Path.trans (C.coboundarySq x) (Path.symm (C.coboundarySq x)))
         (Path.refl (C.coboundary (C.coboundary x))) :=
  rweq_of_step (Step.trans_symm (C.coboundarySq x))

/-- Theorem 3: δ(0) = 0 left unit. -/
noncomputable def coboundaryZero_lunit :
    RwEq (Path.trans (Path.refl (C.coboundary C.zero)) C.coboundaryZero)
         C.coboundaryZero :=
  rweq_of_step (Step.trans_refl_left C.coboundaryZero)

/-- Theorem 4: δ preserves addition right unit. -/
noncomputable def coboundaryAdd_runit (x y : A) :
    RwEq (Path.trans (C.coboundaryAdd x y)
                     (Path.refl (C.add (C.coboundary x) (C.coboundary y))))
         (C.coboundaryAdd x y) :=
  rweq_of_step (Step.trans_refl_right (C.coboundaryAdd x y))

/-- Theorem 5: δ preserves negation inverse cancel (left). -/
noncomputable def coboundaryNeg_inv_left (x : A) :
    RwEq (Path.trans (Path.symm (C.coboundaryNeg x)) (C.coboundaryNeg x))
         (Path.refl (C.neg (C.coboundary x))) :=
  rweq_of_step (Step.symm_trans (C.coboundaryNeg x))

/-- Theorem 6: Congruence of coboundary. -/
noncomputable def coboundary_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (C.coboundary x₁) (C.coboundary x₂) :=
  congrArg C.coboundary p

/-- Theorem 7: Congruence of add in first argument. -/
noncomputable def add_congr_left {x₁ x₂ : A} (p : Path x₁ x₂) (y : A) :
    Path (C.add x₁ y) (C.add x₂ y) :=
  congrArg (C.add · y) p

/-- Theorem 8: Congruence of add in second argument. -/
noncomputable def add_congr_right (x : A) {y₁ y₂ : A} (q : Path y₁ y₂) :
    Path (C.add x y₁) (C.add x y₂) :=
  congrArg (C.add x ·) q

/-! ### Theorems 9–15: Cocycle and coboundary group paths -/

/-- Theorem 9: A cocycle satisfies δx = 0. Cocycle path is just coboundarySq composed. -/
noncomputable def cocycle_from_coboundary (x : A) :
    Path (C.coboundary (C.coboundary x)) C.zero :=
  C.coboundarySq x

/-- Theorem 10: Cocycle addition: δ(x+y)=0 from δx=0, δy=0 composed. -/
noncomputable def cocycle_add_closed (x y : A)
    (hx : Path (C.coboundary x) C.zero) (hy : Path (C.coboundary y) C.zero) :
    Path (C.coboundary (C.add x y)) C.zero :=
  Path.trans (C.coboundaryAdd x y)
    (Path.trans (Path.trans (congrArg (C.add · (C.coboundary y)) hx)
                            (congrArg (C.add C.zero ·) hy))
               (C.zeroAdd C.zero))

/-- Theorem 11: Cocycle negation maps to neg(zero). -/
noncomputable def cocycle_neg_map (x : A) (hx : Path (C.coboundary x) C.zero) :
    Path (C.coboundary (C.neg x)) (C.neg C.zero) :=
  Path.trans (C.coboundaryNeg x) (congrArg C.neg hx)

/-- Theorem 12: Coboundary is exact image: δ(δx) relates. -/
noncomputable def exact_image (x : A) :
    Path (C.add (C.coboundary (C.coboundary x)) (C.coboundary x)) (C.coboundary x) :=
  Path.trans (congrArg (C.add · (C.coboundary x)) (C.coboundarySq x))
             (C.zeroAdd (C.coboundary x))

/-- Theorem 13: Negation cancel. -/
noncomputable def neg_cancel (x : A) :
    Path (C.add x (C.neg x)) C.zero :=
  C.negInv x

/-- Theorem 14: Addition associativity triple. -/
noncomputable def add_assoc_triple (a b c d : A) :
    Path (C.add (C.add (C.add a b) c) d) (C.add (C.add a b) (C.add c d)) :=
  C.addAssoc (C.add a b) c d

/-- Theorem 15: Restriction composition path. -/
noncomputable def restrictComp_runit (x y z : A) :
    RwEq (Path.trans (C.restrictComp x y z) (Path.refl _)) (C.restrictComp x y z) :=
  rweq_of_step (Step.trans_refl_right (C.restrictComp x y z))

end CechComplexData

/-! ## Long Exact Sequence Data -/

/-- Long exact sequence connecting cohomology groups. -/
structure LongExactSeqData (A : Type u) where
  cohom : Nat → A              -- H^n
  connect : A → A              -- connecting homomorphism δ
  incl : A → A                 -- inclusion i
  proj : A → A                 -- projection p
  add : A → A → A
  zero : A
  exactnessIncl : ∀ x : A, Path (proj (incl x)) zero
  exactnessProj : ∀ x : A, Path (incl (connect x)) zero  -- not used but here for
  connectIncl : ∀ x : A, Path (connect (incl x)) zero
  inclZero : Path (incl zero) zero
  projZero : Path (proj zero) zero
  connectZero : Path (connect zero) zero
  addZero : ∀ x : A, Path (add x zero) x
  zeroAdd : ∀ x : A, Path (add zero x) x
  addAssoc : ∀ x y z : A, Path (add (add x y) z) (add x (add y z))
  inclAdd : ∀ x y : A, Path (incl (add x y)) (add (incl x) (incl y))
  projAdd : ∀ x y : A, Path (proj (add x y)) (add (proj x) (proj y))
  connectAdd : ∀ x y : A, Path (connect (add x y)) (add (connect x) (connect y))

namespace LongExactSeqData

variable {A : Type u} (L : LongExactSeqData A)

/-! ### Theorems 16–25: Exactness and connecting homomorphism -/

/-- Theorem 16: Exactness at inclusion right unit. -/
noncomputable def exactIncl_runit (x : A) :
    RwEq (Path.trans (L.exactnessIncl x) (Path.refl L.zero)) (L.exactnessIncl x) :=
  rweq_of_step (Step.trans_refl_right (L.exactnessIncl x))

/-- Theorem 17: Exactness at projection inverse cancel. -/
noncomputable def exactProj_inv (x : A) :
    RwEq (Path.trans (L.exactnessProj x) (Path.symm (L.exactnessProj x)))
         (Path.refl (L.incl (L.connect x))) :=
  rweq_of_step (Step.trans_symm (L.exactnessProj x))

/-- Theorem 18: Connect ∘ incl = 0 left unit. -/
noncomputable def connectIncl_lunit (x : A) :
    RwEq (Path.trans (Path.refl (L.connect (L.incl x))) (L.connectIncl x))
         (L.connectIncl x) :=
  rweq_of_step (Step.trans_refl_left (L.connectIncl x))

/-- Theorem 19: Inclusion of zero right unit. -/
noncomputable def inclZero_runit :
    RwEq (Path.trans L.inclZero (Path.refl L.zero)) L.inclZero :=
  rweq_of_step (Step.trans_refl_right L.inclZero)

/-- Theorem 20: Projection of zero inverse cancel (left). -/
noncomputable def projZero_inv_left :
    RwEq (Path.trans (Path.symm L.projZero) L.projZero) (Path.refl L.zero) :=
  rweq_of_step (Step.symm_trans L.projZero)

/-- Theorem 21: Congruence of inclusion. -/
noncomputable def incl_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (L.incl x₁) (L.incl x₂) :=
  congrArg L.incl p

/-- Theorem 22: Congruence of projection. -/
noncomputable def proj_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (L.proj x₁) (L.proj x₂) :=
  congrArg L.proj p

/-- Theorem 23: Congruence of connecting homomorphism. -/
noncomputable def connect_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (L.connect x₁) (L.connect x₂) :=
  congrArg L.connect p

/-- Theorem 24: Exactness at incl composed with connectIncl. -/
noncomputable def exact_connect_compose (x : A) :
    Path (L.proj (L.incl (L.connect x))) L.zero :=
  Path.trans (congrArg L.proj (L.exactnessProj x)) L.projZero

/-- Theorem 25: Incl additive then zero. -/
noncomputable def incl_add_zero (x : A) :
    Path (L.add (L.incl L.zero) (L.incl x)) (L.incl x) :=
  Path.trans (congrArg (L.add · (L.incl x)) L.inclZero) (L.zeroAdd (L.incl x))

end LongExactSeqData

/-! ## Mayer–Vietoris Data -/

/-- Mayer–Vietoris sequence data for a cover U ∪ V. -/
structure MayerVietorisData (A : Type u) where
  restrict_U : A → A
  restrict_V : A → A
  restrict_UV : A → A
  diff : A → A → A             -- difference map
  connect : A → A
  add : A → A → A
  zero : A
  neg : A → A
  mvExact : ∀ x : A,
    Path (diff (restrict_U x) (restrict_V x)) (restrict_UV x)
  mvConnect : ∀ x : A,
    Path (connect (restrict_UV x)) zero
  diffZero : Path (diff zero zero) zero
  addZero : ∀ x : A, Path (add x zero) x
  zeroAdd : ∀ x : A, Path (add zero x) x
  negInv : ∀ x : A, Path (add x (neg x)) zero
  diffLinear : ∀ x₁ x₂ y₁ y₂ : A,
    Path (diff (add x₁ x₂) (add y₁ y₂))
         (add (diff x₁ y₁) (diff x₂ y₂))
  restrictUZero : Path (restrict_U zero) zero
  restrictVZero : Path (restrict_V zero) zero

namespace MayerVietorisData

variable {A : Type u} (MV : MayerVietorisData A)

/-! ### Theorems 26–35: Mayer–Vietoris identities -/

/-- Theorem 26: MV exactness right unit. -/
noncomputable def mvExact_runit (x : A) :
    RwEq (Path.trans (MV.mvExact x) (Path.refl (MV.restrict_UV x))) (MV.mvExact x) :=
  rweq_of_step (Step.trans_refl_right (MV.mvExact x))

/-- Theorem 27: MV connecting map inverse cancel. -/
noncomputable def mvConnect_inv (x : A) :
    RwEq (Path.trans (MV.mvConnect x) (Path.symm (MV.mvConnect x)))
         (Path.refl (MV.connect (MV.restrict_UV x))) :=
  rweq_of_step (Step.trans_symm (MV.mvConnect x))

/-- Theorem 28: diff(0,0) = 0 left unit. -/
noncomputable def diffZero_lunit :
    RwEq (Path.trans (Path.refl (MV.diff MV.zero MV.zero)) MV.diffZero) MV.diffZero :=
  rweq_of_step (Step.trans_refl_left MV.diffZero)

/-- Theorem 29: Congruence of restrict_U. -/
noncomputable def restrictU_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (MV.restrict_U x₁) (MV.restrict_U x₂) :=
  congrArg MV.restrict_U p

/-- Theorem 30: Congruence of restrict_V. -/
noncomputable def restrictV_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (MV.restrict_V x₁) (MV.restrict_V x₂) :=
  congrArg MV.restrict_V p

/-- Theorem 31: Congruence of diff in both arguments. -/
noncomputable def diff_congr {x₁ x₂ y₁ y₂ : A} (p : Path x₁ x₂) (q : Path y₁ y₂) :
    Path (MV.diff x₁ y₁) (MV.diff x₂ y₂) :=
  Path.trans (congrArg (MV.diff · y₁) p) (congrArg (MV.diff x₂ ·) q)

/-- Theorem 32: MV exactness at zero. -/
noncomputable def mvExact_zero :
    Path (MV.diff (MV.restrict_U MV.zero) (MV.restrict_V MV.zero)) (MV.restrict_UV MV.zero) :=
  MV.mvExact MV.zero

/-- Theorem 33: Difference linearity right unit. -/
noncomputable def diffLinear_runit (x₁ x₂ y₁ y₂ : A) :
    RwEq (Path.trans (MV.diffLinear x₁ x₂ y₁ y₂) (Path.refl _))
         (MV.diffLinear x₁ x₂ y₁ y₂) :=
  rweq_of_step (Step.trans_refl_right (MV.diffLinear x₁ x₂ y₁ y₂))

/-- Theorem 34: Restrict U zero + exactness compose. -/
noncomputable def restrictU_zero_exact :
    Path (MV.diff MV.zero (MV.restrict_V MV.zero)) (MV.restrict_UV MV.zero) :=
  Path.trans (congrArg (MV.diff · (MV.restrict_V MV.zero)) (Path.symm MV.restrictUZero))
             (MV.mvExact MV.zero)

/-- Theorem 35: Negation cancel via add. -/
noncomputable def mv_neg_cancel (x : A) :
    Path (MV.add x (MV.neg x)) MV.zero :=
  MV.negInv x

end MayerVietorisData

/-! ## Derived Functor Data -/

/-- Derived functor / spectral sequence page data. -/
structure DerivedFunctorData (A : Type u) where
  differential : A → A          -- d_r
  add : A → A → A
  zero : A
  diffSq : ∀ x : A, Path (differential (differential x)) zero
  diffZero : Path (differential zero) zero
  diffAdd : ∀ x y : A, Path (differential (add x y)) (add (differential x) (differential y))
  addZero : ∀ x : A, Path (add x zero) x
  zeroAdd : ∀ x : A, Path (add zero x) x
  addAssoc : ∀ x y z : A, Path (add (add x y) z) (add x (add y z))
  addComm : ∀ x y : A, Path (add x y) (add y x)

namespace DerivedFunctorData

variable {A : Type u} (D : DerivedFunctorData A)

/-! ### Theorems 36–45: Spectral sequence / derived functor -/

/-- Theorem 36: d² = 0 right unit. -/
noncomputable def diffSq_runit (x : A) :
    RwEq (Path.trans (D.diffSq x) (Path.refl D.zero)) (D.diffSq x) :=
  rweq_of_step (Step.trans_refl_right (D.diffSq x))

/-- Theorem 37: d(0) = 0 inverse cancel. -/
noncomputable def diffZero_inv :
    RwEq (Path.trans D.diffZero (Path.symm D.diffZero))
         (Path.refl (D.differential D.zero)) :=
  rweq_of_step (Step.trans_symm D.diffZero)

/-- Theorem 38: Differential additive left unit. -/
noncomputable def diffAdd_lunit (x y : A) :
    RwEq (Path.trans (Path.refl _) (D.diffAdd x y)) (D.diffAdd x y) :=
  rweq_of_step (Step.trans_refl_left (D.diffAdd x y))

/-- Theorem 39: Congruence of differential. -/
noncomputable def diff_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (D.differential x₁) (D.differential x₂) :=
  congrArg D.differential p

/-- Theorem 40: d² composed with d-additive. -/
noncomputable def diffSq_add (x y : A) :
    Path (D.differential (D.differential (D.add x y))) D.zero :=
  Path.trans (congrArg D.differential (D.diffAdd x y))
    (Path.trans (D.diffAdd (D.differential x) (D.differential y))
      (Path.trans (congrArg (D.add · (D.differential (D.differential y)))
                            (D.diffSq x))
                  (Path.trans (congrArg (D.add D.zero ·) (D.diffSq y))
                              (D.zeroAdd D.zero))))

/-- Theorem 41: Diff congruence right unit. -/
noncomputable def diff_congr_runit {x₁ x₂ : A} (p : Path x₁ x₂) :
    RwEq (Path.trans (D.diff_congr p) (Path.refl _)) (D.diff_congr p) :=
  rweq_of_step (Step.trans_refl_right (D.diff_congr p))

/-- Theorem 42: Diff add then addZero. -/
noncomputable def diff_add_zero (x : A) :
    Path (D.add (D.differential x) D.zero) (D.differential x) :=
  D.addZero (D.differential x)

/-- Theorem 43: d(x+0) = d(x) via addZero then congruence. -/
noncomputable def diff_addZero (x : A) :
    Path (D.differential (D.add x D.zero)) (D.differential x) :=
  congrArg D.differential (D.addZero x)

/-- Theorem 44: Associativity of add triple. -/
noncomputable def add_assoc3 (a b c d : A) :
    Path (D.add (D.add (D.add a b) c) d) (D.add (D.add a b) (D.add c d)) :=
  D.addAssoc (D.add a b) c d

/-- Theorem 45: Diff of zero-add. -/
noncomputable def diff_zeroAdd (x : A) :
    Path (D.differential (D.add D.zero x)) (D.differential x) :=
  congrArg D.differential (D.zeroAdd x)

end DerivedFunctorData

end
end CechPaths
end SheafCohomology
end Path
end ComputationalPaths

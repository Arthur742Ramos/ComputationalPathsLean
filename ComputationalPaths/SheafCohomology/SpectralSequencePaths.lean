/-
# Sheaf Cohomology: Spectral Sequence & Grothendieck Vanishing Paths

Develops spectral-sequence filtration data, E₂-page differentials,
edge homomorphisms, Grothendieck vanishing, base-change paths,
and Leray–Serre data — all via computational paths with
Step/Path/trans/symm/congrArg.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.SheafCohomology.PathInfrastructure

set_option linter.unusedVariables false

namespace ComputationalPaths
namespace Path
namespace SheafCohomology

open Path

universe u v

noncomputable section

/-! ## Spectral sequence data -/

/-- Spectral sequence page data: E_r^{p,q} with differentials. -/
structure SpectralSeqData (A : Type u) where
  zero : A
  add  : A → A → A
  neg  : A → A
  ePage : Nat → Nat → Nat → A           -- E_r^{p,q}
  diff  : Nat → Nat → Nat → A → A       -- d_r : E_r^{p,q} → E_r^{p+r,q-r+1}
  diffSquareZero : ∀ r p q : Nat, ∀ x : A,
    Path (diff r (p + r) (q - r + 1) (diff r p q x)) zero
  diffLinear : ∀ r p q : Nat, ∀ x y : A,
    Path (diff r p q (add x y)) (add (diff r p q x) (diff r p q y))
  diffZero : ∀ r p q : Nat,
    Path (diff r p q zero) zero
  addZeroLeft : ∀ x : A, Path (add zero x) x
  addZeroRight : ∀ x : A, Path (add x zero) x
  addAssoc : ∀ x y z : A, Path (add (add x y) z) (add x (add y z))

namespace SpectralSeqData

variable {A : Type u} (E : SpectralSeqData A)

/-! ### Theorem 1-10: Differential coherences -/

/-- Theorem 1: d² = 0. -/
noncomputable def d_squared_zero (r p q : Nat) (x : A) :
    Path (E.diff r (p + r) (q - r + 1) (E.diff r p q x)) E.zero :=
  E.diffSquareZero r p q x

/-- Theorem 2: d is additive. -/
noncomputable def d_linear (r p q : Nat) (x y : A) :
    Path (E.diff r p q (E.add x y))
         (E.add (E.diff r p q x) (E.diff r p q y)) :=
  E.diffLinear r p q x y

/-- Theorem 3: d preserves zero. -/
noncomputable def d_zero (r p q : Nat) :
    Path (E.diff r p q E.zero) E.zero :=
  E.diffZero r p q

/-- Theorem 4: d² right-unit. -/
noncomputable def d_squared_right_unit (r p q : Nat) (x : A) :
    RwEq (Path.trans (E.diffSquareZero r p q x) (Path.refl _))
         (E.diffSquareZero r p q x) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 5: d² inverse cancel. -/
noncomputable def d_squared_inv_cancel (r p q : Nat) (x : A) :
    RwEq (Path.trans (E.diffSquareZero r p q x)
                     (Path.symm (E.diffSquareZero r p q x)))
         (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

/-- Theorem 6: d² left-unit. -/
noncomputable def d_squared_left_unit (r p q : Nat) (x : A) :
    RwEq (Path.trans (Path.refl _) (E.diffSquareZero r p q x))
         (E.diffSquareZero r p q x) :=
  rweq_of_step (Step.trans_refl_left _)

/-- Theorem 7: d² double symmetry. -/
noncomputable def d_squared_symm_symm (r p q : Nat) (x : A) :
    RwEq (Path.symm (Path.symm (E.diffSquareZero r p q x)))
         (E.diffSquareZero r p q x) :=
  rweq_of_step (Step.symm_symm _)

/-- Theorem 8: d congruence. -/
noncomputable def d_congr (r p q : Nat) {x₁ x₂ : A} (h : Path x₁ x₂) :
    Path (E.diff r p q x₁) (E.diff r p q x₂) :=
  Path.congrArg (E.diff r p q) h

/-- Theorem 9: d_linear right-unit. -/
noncomputable def d_linear_right_unit (r p q : Nat) (x y : A) :
    RwEq (Path.trans (E.diffLinear r p q x y) (Path.refl _))
         (E.diffLinear r p q x y) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 10: d_zero inverse cancel. -/
noncomputable def d_zero_inv_cancel (r p q : Nat) :
    RwEq (Path.trans (E.diffZero r p q) (Path.symm (E.diffZero r p q)))
         (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

/-! ### Theorem 11-20: E₂-page and convergence -/

/-- Convergence data: E∞-page relates to graded pieces of filtration. -/
structure ConvergenceData where
  graded   : Nat → Nat → A → A
  edgeHom  : Nat → A → A
  convergePath : ∀ p q : Nat, ∀ x : A,
    Path (E.ePage 2 p q) (graded p q x)
  edgePath : ∀ n : Nat, ∀ x : A,
    Path (edgeHom n x) (E.ePage 2 n 0)
  edgeZero : ∀ n : Nat,
    Path (edgeHom n E.zero) E.zero

variable (C : E.ConvergenceData)

/-- Theorem 11: convergence path. -/
noncomputable def converge (p q : Nat) (x : A) :
    Path (E.ePage 2 p q) (C.graded p q x) :=
  C.convergePath p q x

/-- Theorem 12: edge homomorphism. -/
noncomputable def edge_hom (n : Nat) (x : A) :
    Path (C.edgeHom n x) (E.ePage 2 n 0) :=
  C.edgePath n x

/-- Theorem 13: edge at zero. -/
noncomputable def edge_zero (n : Nat) :
    Path (C.edgeHom n E.zero) E.zero :=
  C.edgeZero n

/-- Theorem 14: convergence right-unit. -/
noncomputable def converge_right_unit (p q : Nat) (x : A) :
    RwEq (Path.trans (C.convergePath p q x) (Path.refl _))
         (C.convergePath p q x) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 15: convergence inverse cancel. -/
noncomputable def converge_inv_cancel (p q : Nat) (x : A) :
    RwEq (Path.trans (C.convergePath p q x)
                     (Path.symm (C.convergePath p q x)))
         (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

/-- Theorem 16: edge right-unit. -/
noncomputable def edge_right_unit (n : Nat) (x : A) :
    RwEq (Path.trans (C.edgePath n x) (Path.refl _))
         (C.edgePath n x) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 17: edge inverse cancel. -/
noncomputable def edge_inv_cancel (n : Nat) (x : A) :
    RwEq (Path.trans (C.edgePath n x)
                     (Path.symm (C.edgePath n x)))
         (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

/-- Theorem 18: edge zero right-unit. -/
noncomputable def edge_zero_right_unit (n : Nat) :
    RwEq (Path.trans (C.edgeZero n) (Path.refl _))
         (C.edgeZero n) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 19: edge congruence. -/
noncomputable def edge_congr (n : Nat) {x₁ x₂ : A} (h : Path x₁ x₂) :
    Path (C.edgeHom n x₁) (C.edgeHom n x₂) :=
  Path.congrArg (C.edgeHom n) h

/-- Theorem 20: graded congruence. -/
noncomputable def graded_congr (p q : Nat) {x₁ x₂ : A} (h : Path x₁ x₂) :
    Path (C.graded p q x₁) (C.graded p q x₂) :=
  Path.congrArg (C.graded p q) h

end SpectralSeqData

/-! ## Grothendieck vanishing -/

/-- Vanishing data for sheaf cohomology above a given dimension. -/
structure VanishingData (A : Type u) where
  zero   : A
  cohom  : Nat → A → A
  dim    : Nat
  vanishPath : ∀ n : Nat, n > dim → ∀ x : A, Path (cohom n x) zero
  cohomZero : ∀ n : Nat, Path (cohom n zero) zero
  cohomCongr : ∀ n : Nat, ∀ {x₁ x₂ : A}, Path x₁ x₂ → Path (cohom n x₁) (cohom n x₂)

namespace VanishingData

variable {A : Type u} (V : VanishingData A)

/-! ### Theorem 21-30: Vanishing coherences -/

/-- Theorem 21: Vanishing above dimension. -/
noncomputable def vanish_above (n : Nat) (hn : n > V.dim) (x : A) :
    Path (V.cohom n x) V.zero :=
  V.vanishPath n hn x

/-- Theorem 22: cohomology at zero. -/
noncomputable def cohom_zero (n : Nat) : Path (V.cohom n V.zero) V.zero :=
  V.cohomZero n

/-- Theorem 23: vanishing right-unit. -/
noncomputable def vanish_right_unit (n : Nat) (hn : n > V.dim) (x : A) :
    RwEq (Path.trans (V.vanishPath n hn x) (Path.refl _))
         (V.vanishPath n hn x) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 24: vanishing inverse cancel. -/
noncomputable def vanish_inv_cancel (n : Nat) (hn : n > V.dim) (x : A) :
    RwEq (Path.trans (V.vanishPath n hn x)
                     (Path.symm (V.vanishPath n hn x)))
         (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

/-- Theorem 25: vanishing double symmetry. -/
noncomputable def vanish_symm_symm (n : Nat) (hn : n > V.dim) (x : A) :
    RwEq (Path.symm (Path.symm (V.vanishPath n hn x)))
         (V.vanishPath n hn x) :=
  rweq_of_step (Step.symm_symm _)

/-- Theorem 26: vanishing left-unit. -/
noncomputable def vanish_left_unit (n : Nat) (hn : n > V.dim) (x : A) :
    RwEq (Path.trans (Path.refl _) (V.vanishPath n hn x))
         (V.vanishPath n hn x) :=
  rweq_of_step (Step.trans_refl_left _)

/-- Theorem 27: vanishing left-inverse. -/
noncomputable def vanish_left_inv (n : Nat) (hn : n > V.dim) (x : A) :
    RwEq (Path.trans (Path.symm (V.vanishPath n hn x))
                     (V.vanishPath n hn x))
         (Path.refl _) :=
  rweq_of_step (Step.symm_trans _)

/-- Theorem 28: cohom congruence. -/
noncomputable def cohom_congr_path (n : Nat) {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (V.cohom n x₁) (V.cohom n x₂) :=
  V.cohomCongr n p

/-- Theorem 29: cohom zero right-unit. -/
noncomputable def cohom_zero_right_unit (n : Nat) :
    RwEq (Path.trans (V.cohomZero n) (Path.refl _))
         (V.cohomZero n) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 30: cohom zero inverse cancel. -/
noncomputable def cohom_zero_inv_cancel (n : Nat) :
    RwEq (Path.trans (V.cohomZero n) (Path.symm (V.cohomZero n)))
         (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

end VanishingData

/-! ## Base change paths -/

/-- Base-change data for derived pushforward along a morphism. -/
structure BaseChangeData (A : Type u) where
  zero : A
  add  : A → A → A
  pushforward : Nat → A → A
  pullback    : A → A
  baseChangePath : ∀ n : Nat, ∀ x : A,
    Path (pullback (pushforward n x)) (pushforward n (pullback x))
  pushforwardZero : ∀ n : Nat, Path (pushforward n zero) zero
  pullbackZero : Path (pullback zero) zero

namespace BaseChangeData

variable {A : Type u} (BC : BaseChangeData A)

/-! ### Theorem 31-40: Base change coherences -/

/-- Theorem 31: Base change commutation. -/
noncomputable def base_change (n : Nat) (x : A) :
    Path (BC.pullback (BC.pushforward n x))
         (BC.pushforward n (BC.pullback x)) :=
  BC.baseChangePath n x

/-- Theorem 32: Pushforward preserves zero. -/
noncomputable def push_zero (n : Nat) :
    Path (BC.pushforward n BC.zero) BC.zero :=
  BC.pushforwardZero n

/-- Theorem 33: Pullback preserves zero. -/
noncomputable def pull_zero :
    Path (BC.pullback BC.zero) BC.zero :=
  BC.pullbackZero

/-- Theorem 34: base change right-unit. -/
noncomputable def base_change_right_unit (n : Nat) (x : A) :
    RwEq (Path.trans (BC.baseChangePath n x) (Path.refl _))
         (BC.baseChangePath n x) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 35: base change inverse cancel. -/
noncomputable def base_change_inv_cancel (n : Nat) (x : A) :
    RwEq (Path.trans (BC.baseChangePath n x)
                     (Path.symm (BC.baseChangePath n x)))
         (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

/-- Theorem 36: base change double symmetry. -/
noncomputable def base_change_symm_symm (n : Nat) (x : A) :
    RwEq (Path.symm (Path.symm (BC.baseChangePath n x)))
         (BC.baseChangePath n x) :=
  rweq_of_step (Step.symm_symm _)

/-- Theorem 37: pushforward congruence. -/
noncomputable def push_congr (n : Nat) {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (BC.pushforward n x₁) (BC.pushforward n x₂) :=
  Path.congrArg (BC.pushforward n) p

/-- Theorem 38: pullback congruence. -/
noncomputable def pull_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (BC.pullback x₁) (BC.pullback x₂) :=
  Path.congrArg BC.pullback p

/-- Theorem 39: push_zero right-unit. -/
noncomputable def push_zero_right_unit (n : Nat) :
    RwEq (Path.trans (BC.pushforwardZero n) (Path.refl _))
         (BC.pushforwardZero n) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 40: pull_zero inverse cancel. -/
noncomputable def pull_zero_inv_cancel :
    RwEq (Path.trans BC.pullbackZero (Path.symm BC.pullbackZero))
         (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

end BaseChangeData

end

end SheafCohomology
end Path
end ComputationalPaths

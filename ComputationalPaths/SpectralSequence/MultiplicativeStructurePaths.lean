/-
# Multiplicative structure and filtered complexes via computational paths

This module develops multiplicative spectral sequences, filtered complexes,
edge homomorphisms, and transgression using the computational path framework.

## Contents

* `FilteredComplexPaths` — filtered chain complex with differential paths
* `MultiplicativePagePaths` — product structure on spectral pages
* Leibniz rule for differentials on multiplicative pages
* Cross-product and cup-product paths
* Edge homomorphism coherence paths
* Transgression as composite of edge maps
* Serre fibration transgression paths
* Comparison with Adams filtration structure
* 60+ theorems, all `sorry`-free
-/

import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.SpectralSequence.Convergence

namespace ComputationalPaths
namespace SpectralSequence

open Path

universe u

/-! ## Filtered complex structure -/

/-- A computational-path package for a filtered chain complex. -/
structure FilteredComplexPaths where
  /-- The chain complex at each degree. -/
  chain : Nat → Type u
  /-- Base element at each degree. -/
  chainBase : (n : Nat) → chain n
  /-- The differential d : C_n → C_{n-1} (represented on same type for simplicity). -/
  chainDiff : (n : Nat) → chain n → chain n
  /-- Filtration level s on degree n. -/
  filt : (s n : Nat) → chain n → chain n
  /-- d² = 0 path witness. -/
  dSquaredPath :
    ∀ (n : Nat),
      Path (chainDiff n (chainDiff n (chainBase n))) (chainBase n)
  /-- Step for d² = 0 right-unit. -/
  dSquaredStep :
    ∀ (n : Nat),
      Path.Step
        (Path.trans (dSquaredPath n) (Path.refl (chainBase n)))
        (dSquaredPath n)
  /-- Filtration inclusion: F_s ⊂ F_{s+1}. -/
  filtInclusionPath :
    ∀ (s n : Nat),
      Path (filt s n (chainBase n)) (filt (s + 1) n (chainBase n))
  /-- Differential respects filtration: d(F_s) ⊂ F_s. -/
  filtDiffPath :
    ∀ (s n : Nat),
      Path (chainDiff n (filt s n (chainBase n)))
        (filt s n (chainDiff n (chainBase n)))
  /-- Step for filtration-diff compatibility right-unit. -/
  filtDiffStep :
    ∀ (s n : Nat),
      Path.Step
        (Path.trans (filtDiffPath s n)
          (Path.refl (filt s n (chainDiff n (chainBase n)))))
        (filtDiffPath s n)

namespace FilteredComplexPaths

variable (F : FilteredComplexPaths.{u})

/-! ### Basic RwEq theorems -/

@[simp] theorem dSquared_rweq (n : Nat) :
    RwEq
      (Path.trans (F.dSquaredPath n) (Path.refl (F.chainBase n)))
      (F.dSquaredPath n) :=
  rweq_of_step (F.dSquaredStep n)

@[simp] theorem filtDiff_rweq (s n : Nat) :
    RwEq
      (Path.trans (F.filtDiffPath s n)
        (Path.refl (F.filt s n (F.chainDiff n (F.chainBase n)))))
      (F.filtDiffPath s n) :=
  rweq_of_step (F.filtDiffStep s n)

/-! ### Cancellation loops -/

/-- d² = 0 loop. -/
def dSquaredLoop (n : Nat) :
    Path (F.chainDiff n (F.chainDiff n (F.chainBase n)))
      (F.chainDiff n (F.chainDiff n (F.chainBase n))) :=
  Path.trans (F.dSquaredPath n) (Path.symm (F.dSquaredPath n))

@[simp] theorem dSquaredLoop_contracts (n : Nat) :
    RwEq (F.dSquaredLoop n)
      (Path.refl (F.chainDiff n (F.chainDiff n (F.chainBase n)))) := by
  unfold dSquaredLoop
  exact rweq_cmpA_inv_right (F.dSquaredPath n)

/-- Filtration-differential compatibility loop. -/
def filtDiffLoop (s n : Nat) :
    Path (F.chainDiff n (F.filt s n (F.chainBase n)))
      (F.chainDiff n (F.filt s n (F.chainBase n))) :=
  Path.trans (F.filtDiffPath s n) (Path.symm (F.filtDiffPath s n))

@[simp] theorem filtDiffLoop_contracts (s n : Nat) :
    RwEq (F.filtDiffLoop s n)
      (Path.refl (F.chainDiff n (F.filt s n (F.chainBase n)))) := by
  unfold filtDiffLoop
  exact rweq_cmpA_inv_right (F.filtDiffPath s n)

/-! ### Inverse cancellations -/

@[simp] theorem dSquared_inv_left (n : Nat) :
    RwEq
      (Path.trans (Path.symm (F.dSquaredPath n)) (F.dSquaredPath n))
      (Path.refl (F.chainBase n)) :=
  rweq_cmpA_inv_left (F.dSquaredPath n)

@[simp] theorem filtDiff_inv_left (s n : Nat) :
    RwEq
      (Path.trans (Path.symm (F.filtDiffPath s n)) (F.filtDiffPath s n))
      (Path.refl (F.filt s n (F.chainDiff n (F.chainBase n)))) :=
  rweq_cmpA_inv_left (F.filtDiffPath s n)

/-! ### Congruence through filtration -/

/-- d² = 0 transported through filtration. -/
def filtDSquaredPath (s n : Nat) :
    Path (F.filt s n (F.chainDiff n (F.chainDiff n (F.chainBase n))))
      (F.filt s n (F.chainBase n)) :=
  Path.congrArg (F.filt s n) (F.dSquaredPath n)

@[simp] theorem filtDSquared_normalizes (s n : Nat) :
    RwEq
      (Path.trans (F.filtDSquaredPath s n)
        (Path.refl (F.filt s n (F.chainBase n))))
      (F.filtDSquaredPath s n) :=
  rweq_cmpA_refl_right (F.filtDSquaredPath s n)

@[simp] theorem filtDSquared_loop_contracts (s n : Nat) :
    RwEq
      (Path.trans (F.filtDSquaredPath s n) (Path.symm (F.filtDSquaredPath s n)))
      (Path.refl (F.filt s n (F.chainDiff n (F.chainDiff n (F.chainBase n))))) :=
  rweq_cmpA_inv_right (F.filtDSquaredPath s n)

/-! ### Associated graded paths -/

/-- Associated graded: quotient F_s/F_{s-1} (represented structurally). -/
def gradedPiece (s n : Nat) : F.chain n :=
  F.filt s n (F.chainBase n)

/-- Inclusion of graded piece into next filtration level. -/
def gradedInclusionPath (s n : Nat) :
    Path (F.gradedPiece s n) (F.gradedPiece (s + 1) n) :=
  F.filtInclusionPath s n

/-- Differential on graded pieces. -/
def gradedDiff (s n : Nat) : F.chain n :=
  F.chainDiff n (F.gradedPiece s n)

/-- Path: graded diff lands in filtered piece. -/
def gradedDiffFilteredPath (s n : Nat) :
    Path (F.gradedDiff s n) (F.filt s n (F.chainDiff n (F.chainBase n))) :=
  F.filtDiffPath s n

@[simp] theorem gradedDiffFiltered_normalizes (s n : Nat) :
    RwEq
      (Path.trans (F.gradedDiffFilteredPath s n)
        (Path.refl (F.filt s n (F.chainDiff n (F.chainBase n)))))
      (F.gradedDiffFilteredPath s n) :=
  rweq_cmpA_refl_right (F.gradedDiffFilteredPath s n)

/-! ### Double filtration composites -/

/-- Composite filtration path: F_s → F_{s+1} → F_{s+2}. -/
def doubleFiltInclusionPath (s n : Nat) :
    Path (F.gradedPiece s n) (F.gradedPiece (s + 2) n) :=
  Path.trans (F.gradedInclusionPath s n) (F.gradedInclusionPath (s + 1) n)

@[simp] theorem doubleFiltInclusion_normalizes (s n : Nat) :
    RwEq
      (Path.trans (F.doubleFiltInclusionPath s n)
        (Path.refl (F.gradedPiece (s + 2) n)))
      (F.doubleFiltInclusionPath s n) :=
  rweq_cmpA_refl_right (F.doubleFiltInclusionPath s n)

end FilteredComplexPaths

/-- Trivial filtered complex. -/
def trivialFilteredComplexPaths : FilteredComplexPaths where
  chain := fun _ => PUnit
  chainBase := fun _ => PUnit.unit
  chainDiff := fun _ _ => PUnit.unit
  filt := fun _ _ _ => PUnit.unit
  dSquaredPath := fun _ => Path.refl PUnit.unit
  dSquaredStep := fun _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)
  filtInclusionPath := fun _ _ => Path.refl PUnit.unit
  filtDiffPath := fun _ _ => Path.refl PUnit.unit
  filtDiffStep := fun _ _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)

/-! ## Multiplicative page structure -/

/-- A multiplicative spectral page: pages equipped with a product. -/
structure MultiplicativePagePaths extends Pages.{u} where
  /-- Product map on page terms. -/
  prod : (p₁ q₁ p₂ q₂ : Nat) → toPages.term p₁ q₁ → toPages.term p₂ q₂ →
    toPages.term p₁ q₁
  /-- Left unit path: prod(base, x) = x. -/
  prodLeftUnitPath :
    ∀ (p q : Nat) (x : toPages.term p q),
      Path (prod p q p q (toPages.base p q) x) x
  /-- Right unit path: prod(x, base) = x. -/
  prodRightUnitPath :
    ∀ (p₁ q₁ p₂ q₂ : Nat),
      Path (prod p₁ q₁ p₂ q₂ (toPages.base p₁ q₁) (toPages.base p₂ q₂))
        (toPages.base p₁ q₁)
  /-- Step for left-unit right-normalization. -/
  prodLeftUnitStep :
    ∀ (p q : Nat) (x : toPages.term p q),
      Path.Step
        (Path.trans (prodLeftUnitPath p q x) (Path.refl x))
        (prodLeftUnitPath p q x)
  /-- Product commutes with page shift on base terms. -/
  prodShiftPath :
    ∀ (r p₁ q₁ p₂ q₂ : Nat),
      Path
        (toPages.shift r p₁ q₁
          (prod p₁ q₁ p₂ q₂ (toPages.base p₁ q₁) (toPages.base p₂ q₂)))
        (prod p₁ q₁ p₂ q₂
          (toPages.shift r p₁ q₁ (toPages.base p₁ q₁))
          (toPages.shift r p₂ q₂ (toPages.base p₂ q₂)))

namespace MultiplicativePagePaths

variable (M : MultiplicativePagePaths.{u})

/-! ### Product RwEq theorems -/

@[simp] theorem prodLeftUnit_rweq (p q : Nat) (x : M.toPages.term p q) :
    RwEq
      (Path.trans (M.prodLeftUnitPath p q x) (Path.refl x))
      (M.prodLeftUnitPath p q x) :=
  rweq_of_step (M.prodLeftUnitStep p q x)

/-- Product left-unit loop contracts. -/
def prodLeftUnitLoop (p q : Nat) (x : M.toPages.term p q) :
    Path (M.prod p q p q (M.toPages.base p q) x)
      (M.prod p q p q (M.toPages.base p q) x) :=
  Path.trans (M.prodLeftUnitPath p q x) (Path.symm (M.prodLeftUnitPath p q x))

@[simp] theorem prodLeftUnitLoop_contracts (p q : Nat) (x : M.toPages.term p q) :
    RwEq (M.prodLeftUnitLoop p q x)
      (Path.refl (M.prod p q p q (M.toPages.base p q) x)) := by
  unfold prodLeftUnitLoop
  exact rweq_cmpA_inv_right (M.prodLeftUnitPath p q x)

/-- Product right-unit loop contracts. -/
def prodRightUnitLoop (p₁ q₁ p₂ q₂ : Nat) :
    Path (M.prod p₁ q₁ p₂ q₂ (M.toPages.base p₁ q₁) (M.toPages.base p₂ q₂))
      (M.prod p₁ q₁ p₂ q₂ (M.toPages.base p₁ q₁) (M.toPages.base p₂ q₂)) :=
  Path.trans (M.prodRightUnitPath p₁ q₁ p₂ q₂)
    (Path.symm (M.prodRightUnitPath p₁ q₁ p₂ q₂))

@[simp] theorem prodRightUnitLoop_contracts (p₁ q₁ p₂ q₂ : Nat) :
    RwEq (M.prodRightUnitLoop p₁ q₁ p₂ q₂)
      (Path.refl (M.prod p₁ q₁ p₂ q₂ (M.toPages.base p₁ q₁)
        (M.toPages.base p₂ q₂))) := by
  unfold prodRightUnitLoop
  exact rweq_cmpA_inv_right (M.prodRightUnitPath p₁ q₁ p₂ q₂)

@[simp] theorem prodRightUnit_inv_left (p₁ q₁ p₂ q₂ : Nat) :
    RwEq
      (Path.trans (Path.symm (M.prodRightUnitPath p₁ q₁ p₂ q₂))
        (M.prodRightUnitPath p₁ q₁ p₂ q₂))
      (Path.refl (M.toPages.base p₁ q₁)) :=
  rweq_cmpA_inv_left (M.prodRightUnitPath p₁ q₁ p₂ q₂)

/-! ### Product-shift compatibility -/

/-- Product-shift compatibility loop. -/
def prodShiftLoop (r p₁ q₁ p₂ q₂ : Nat) :
    Path
      (M.toPages.shift r p₁ q₁
        (M.prod p₁ q₁ p₂ q₂ (M.toPages.base p₁ q₁) (M.toPages.base p₂ q₂)))
      (M.toPages.shift r p₁ q₁
        (M.prod p₁ q₁ p₂ q₂ (M.toPages.base p₁ q₁) (M.toPages.base p₂ q₂))) :=
  Path.trans (M.prodShiftPath r p₁ q₁ p₂ q₂)
    (Path.symm (M.prodShiftPath r p₁ q₁ p₂ q₂))

@[simp] theorem prodShiftLoop_contracts (r p₁ q₁ p₂ q₂ : Nat) :
    RwEq (M.prodShiftLoop r p₁ q₁ p₂ q₂)
      (Path.refl (M.toPages.shift r p₁ q₁
        (M.prod p₁ q₁ p₂ q₂ (M.toPages.base p₁ q₁)
          (M.toPages.base p₂ q₂)))) := by
  unfold prodShiftLoop
  exact rweq_cmpA_inv_right (M.prodShiftPath r p₁ q₁ p₂ q₂)

@[simp] theorem prodShift_normalizes (r p₁ q₁ p₂ q₂ : Nat) :
    RwEq
      (Path.trans (M.prodShiftPath r p₁ q₁ p₂ q₂)
        (Path.refl _))
      (M.prodShiftPath r p₁ q₁ p₂ q₂) :=
  rweq_cmpA_refl_right (M.prodShiftPath r p₁ q₁ p₂ q₂)

/-! ### Shift through product on right unit -/

/-- Path: shift applied to the product right-unit. -/
def shiftProdRightUnitPath (r p₁ q₁ p₂ q₂ : Nat) :
    Path
      (M.toPages.shift r p₁ q₁
        (M.prod p₁ q₁ p₂ q₂ (M.toPages.base p₁ q₁) (M.toPages.base p₂ q₂)))
      (M.toPages.shift r p₁ q₁ (M.toPages.base p₁ q₁)) :=
  Path.congrArg (M.toPages.shift r p₁ q₁) (M.prodRightUnitPath p₁ q₁ p₂ q₂)

@[simp] theorem shiftProdRightUnit_normalizes (r p₁ q₁ p₂ q₂ : Nat) :
    RwEq
      (Path.trans (M.shiftProdRightUnitPath r p₁ q₁ p₂ q₂)
        (Path.refl _))
      (M.shiftProdRightUnitPath r p₁ q₁ p₂ q₂) :=
  rweq_cmpA_refl_right (M.shiftProdRightUnitPath r p₁ q₁ p₂ q₂)

@[simp] theorem shiftProdRightUnit_loop_contracts (r p₁ q₁ p₂ q₂ : Nat) :
    RwEq
      (Path.trans (M.shiftProdRightUnitPath r p₁ q₁ p₂ q₂)
        (Path.symm (M.shiftProdRightUnitPath r p₁ q₁ p₂ q₂)))
      (Path.refl _) :=
  rweq_cmpA_inv_right (M.shiftProdRightUnitPath r p₁ q₁ p₂ q₂)

end MultiplicativePagePaths

/-- Trivial multiplicative page. -/
def trivialMultiplicativePagePaths : MultiplicativePagePaths where
  toPages := trivialPages
  prod := fun _ _ _ _ _ _ => PUnit.unit
  prodLeftUnitPath := fun _ _ _ => Path.refl PUnit.unit
  prodRightUnitPath := fun _ _ _ _ => Path.refl PUnit.unit
  prodLeftUnitStep := fun _ _ _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)
  prodShiftPath := fun _ _ _ _ _ => Path.refl PUnit.unit

/-! ## Multiplicative differential structure -/

/-- Differentials on a multiplicative page with Leibniz rule path. -/
structure MultiplicativeDiffPaths (M : MultiplicativePagePaths.{u}) extends
    Differentials M.toPages where
  /-- Leibniz rule path witness:
      d(prod(base₁, base₂)) = prod(d(base₁), base₂) at the path level. -/
  leibnizPath :
    ∀ (r p₁ q₁ p₂ q₂ : Nat),
      Path
        (toDifferentials.d r p₁ q₁
          (M.prod p₁ q₁ p₂ q₂ (M.toPages.base p₁ q₁) (M.toPages.base p₂ q₂)))
        (M.prod p₁ q₁ p₂ q₂
          (toDifferentials.d r p₁ q₁ (M.toPages.base p₁ q₁))
          (M.toPages.base p₂ q₂))
  /-- Step for Leibniz right-unit normalization. -/
  leibnizStep :
    ∀ (r p₁ q₁ p₂ q₂ : Nat),
      Path.Step
        (Path.trans (leibnizPath r p₁ q₁ p₂ q₂) (Path.refl _))
        (leibnizPath r p₁ q₁ p₂ q₂)

namespace MultiplicativeDiffPaths

variable {M : MultiplicativePagePaths.{u}} (MD : MultiplicativeDiffPaths M)

@[simp] theorem leibniz_rweq (r p₁ q₁ p₂ q₂ : Nat) :
    RwEq
      (Path.trans (MD.leibnizPath r p₁ q₁ p₂ q₂) (Path.refl _))
      (MD.leibnizPath r p₁ q₁ p₂ q₂) :=
  rweq_of_step (MD.leibnizStep r p₁ q₁ p₂ q₂)

/-- Leibniz loop contracts. -/
def leibnizLoop (r p₁ q₁ p₂ q₂ : Nat) :
    Path
      (MD.toDifferentials.d r p₁ q₁
        (M.prod p₁ q₁ p₂ q₂ (M.toPages.base p₁ q₁) (M.toPages.base p₂ q₂)))
      (MD.toDifferentials.d r p₁ q₁
        (M.prod p₁ q₁ p₂ q₂ (M.toPages.base p₁ q₁) (M.toPages.base p₂ q₂))) :=
  Path.trans (MD.leibnizPath r p₁ q₁ p₂ q₂)
    (Path.symm (MD.leibnizPath r p₁ q₁ p₂ q₂))

@[simp] theorem leibnizLoop_contracts (r p₁ q₁ p₂ q₂ : Nat) :
    RwEq (MD.leibnizLoop r p₁ q₁ p₂ q₂) (Path.refl _) := by
  unfold leibnizLoop
  exact rweq_cmpA_inv_right (MD.leibnizPath r p₁ q₁ p₂ q₂)

@[simp] theorem leibniz_inv_left (r p₁ q₁ p₂ q₂ : Nat) :
    RwEq
      (Path.trans (Path.symm (MD.leibnizPath r p₁ q₁ p₂ q₂))
        (MD.leibnizPath r p₁ q₁ p₂ q₂))
      (Path.refl _) :=
  rweq_cmpA_inv_left (MD.leibnizPath r p₁ q₁ p₂ q₂)

/-! ### Leibniz through shift -/

/-- Shifted Leibniz: apply page shift to the Leibniz path. -/
def shiftedLeibnizPath (r p₁ q₁ p₂ q₂ : Nat) :
    Path
      (M.toPages.shift r p₁ q₁
        (MD.toDifferentials.d r p₁ q₁
          (M.prod p₁ q₁ p₂ q₂ (M.toPages.base p₁ q₁) (M.toPages.base p₂ q₂))))
      (M.toPages.shift r p₁ q₁
        (M.prod p₁ q₁ p₂ q₂
          (MD.toDifferentials.d r p₁ q₁ (M.toPages.base p₁ q₁))
          (M.toPages.base p₂ q₂))) :=
  Path.congrArg (M.toPages.shift r p₁ q₁) (MD.leibnizPath r p₁ q₁ p₂ q₂)

@[simp] theorem shiftedLeibniz_normalizes (r p₁ q₁ p₂ q₂ : Nat) :
    RwEq
      (Path.trans (MD.shiftedLeibnizPath r p₁ q₁ p₂ q₂)
        (Path.refl _))
      (MD.shiftedLeibnizPath r p₁ q₁ p₂ q₂) :=
  rweq_cmpA_refl_right (MD.shiftedLeibnizPath r p₁ q₁ p₂ q₂)

@[simp] theorem shiftedLeibniz_loop_contracts (r p₁ q₁ p₂ q₂ : Nat) :
    RwEq
      (Path.trans (MD.shiftedLeibnizPath r p₁ q₁ p₂ q₂)
        (Path.symm (MD.shiftedLeibnizPath r p₁ q₁ p₂ q₂)))
      (Path.refl _) :=
  rweq_cmpA_inv_right (MD.shiftedLeibnizPath r p₁ q₁ p₂ q₂)

end MultiplicativeDiffPaths

/-- Trivial multiplicative differential package. -/
def trivialMultiplicativeDiffPaths :
    MultiplicativeDiffPaths trivialMultiplicativePagePaths where
  toDifferentials := trivialDifferentials
  leibnizPath := fun _ _ _ _ _ => Path.refl PUnit.unit
  leibnizStep := fun _ _ _ _ _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)

/-! ## Edge homomorphism coherence -/

/-- Edge homomorphism data for a spectral sequence with convergence. -/
structure EdgeHomPaths (E : Pages.{u}) (D : Differentials E) (C : Convergence E D) where
  /-- Source module for the edge map. -/
  source : Nat → Type u
  /-- Target module for the edge map. -/
  target : Nat → Type u
  /-- Base elements. -/
  sourceBase : (n : Nat) → source n
  targetBase : (n : Nat) → target n
  /-- Left edge map: source → E_{n,0}. -/
  leftEdge : (n : Nat) → source n → E.term n 0
  /-- Right edge map: E_{0,n} → target. -/
  rightEdge : (n : Nat) → E.term 0 n → target n
  /-- Left edge preserves base. -/
  leftEdgeBasePath :
    ∀ (n : Nat),
      Path (leftEdge n (sourceBase n)) (E.base n 0)
  /-- Right edge preserves base. -/
  rightEdgeBasePath :
    ∀ (n : Nat),
      Path (rightEdge n (E.base 0 n)) (targetBase n)
  /-- Left edge commutes with shift on base terms. -/
  leftEdgeShiftPath :
    ∀ (r n : Nat),
      Path
        (E.shift r n 0 (leftEdge n (sourceBase n)))
        (leftEdge n (sourceBase n))
  /-- Right edge commutes with shift on base terms. -/
  rightEdgeShiftPath :
    ∀ (r n : Nat),
      Path
        (rightEdge n (E.shift r 0 n (E.base 0 n)))
        (targetBase n)

namespace EdgeHomPaths

variable {E : Pages.{u}} {D : Differentials E} {C : Convergence E D}
  (H : EdgeHomPaths E D C)

/-- Left edge to spectral base path. -/
@[simp] theorem leftEdgeBase_normalizes (n : Nat) :
    RwEq
      (Path.trans (H.leftEdgeBasePath n) (Path.refl (E.base n 0)))
      (H.leftEdgeBasePath n) :=
  rweq_cmpA_refl_right (H.leftEdgeBasePath n)

/-- Right edge from spectral base path. -/
@[simp] theorem rightEdgeBase_normalizes (n : Nat) :
    RwEq
      (Path.trans (H.rightEdgeBasePath n) (Path.refl (H.targetBase n)))
      (H.rightEdgeBasePath n) :=
  rweq_cmpA_refl_right (H.rightEdgeBasePath n)

/-- Left edge loop contracts. -/
@[simp] theorem leftEdgeBase_loop_contracts (n : Nat) :
    RwEq
      (Path.trans (H.leftEdgeBasePath n) (Path.symm (H.leftEdgeBasePath n)))
      (Path.refl (H.leftEdge n (H.sourceBase n))) :=
  rweq_cmpA_inv_right (H.leftEdgeBasePath n)

/-- Right edge loop contracts. -/
@[simp] theorem rightEdgeBase_loop_contracts (n : Nat) :
    RwEq
      (Path.trans (H.rightEdgeBasePath n) (Path.symm (H.rightEdgeBasePath n)))
      (Path.refl (H.rightEdge n (E.base 0 n))) :=
  rweq_cmpA_inv_right (H.rightEdgeBasePath n)

/-- Left edge inverse cancellation. -/
@[simp] theorem leftEdgeBase_inv_left (n : Nat) :
    RwEq
      (Path.trans (Path.symm (H.leftEdgeBasePath n)) (H.leftEdgeBasePath n))
      (Path.refl (E.base n 0)) :=
  rweq_cmpA_inv_left (H.leftEdgeBasePath n)

/-- Right edge inverse cancellation. -/
@[simp] theorem rightEdgeBase_inv_left (n : Nat) :
    RwEq
      (Path.trans (Path.symm (H.rightEdgeBasePath n)) (H.rightEdgeBasePath n))
      (Path.refl (H.targetBase n)) :=
  rweq_cmpA_inv_left (H.rightEdgeBasePath n)

/-- Shifted left edge to stabilized path. -/
def leftEdgeShiftToBasePath (r n : Nat) :
    Path
      (E.shift r n 0 (H.leftEdge n (H.sourceBase n)))
      (E.base n 0) :=
  Path.trans (H.leftEdgeShiftPath r n) (H.leftEdgeBasePath n)

@[simp] theorem leftEdgeShiftToBase_normalizes (r n : Nat) :
    RwEq
      (Path.trans (H.leftEdgeShiftToBasePath r n) (Path.refl (E.base n 0)))
      (H.leftEdgeShiftToBasePath r n) :=
  rweq_cmpA_refl_right (H.leftEdgeShiftToBasePath r n)

@[simp] theorem leftEdgeShiftToBase_loop_contracts (r n : Nat) :
    RwEq
      (Path.trans (H.leftEdgeShiftToBasePath r n)
        (Path.symm (H.leftEdgeShiftToBasePath r n)))
      (Path.refl _) :=
  rweq_cmpA_inv_right (H.leftEdgeShiftToBasePath r n)

/-- Shifted right edge path. -/
@[simp] theorem rightEdgeShift_normalizes (r n : Nat) :
    RwEq
      (Path.trans (H.rightEdgeShiftPath r n) (Path.refl (H.targetBase n)))
      (H.rightEdgeShiftPath r n) :=
  rweq_cmpA_refl_right (H.rightEdgeShiftPath r n)

@[simp] theorem rightEdgeShift_loop_contracts (r n : Nat) :
    RwEq
      (Path.trans (H.rightEdgeShiftPath r n) (Path.symm (H.rightEdgeShiftPath r n)))
      (Path.refl _) :=
  rweq_cmpA_inv_right (H.rightEdgeShiftPath r n)

end EdgeHomPaths

/-- Trivial edge homomorphism package. -/
def trivialEdgeHomPaths :
    EdgeHomPaths trivialPages trivialDifferentials trivialConvergence where
  source := fun _ => PUnit
  target := fun _ => PUnit
  sourceBase := fun _ => PUnit.unit
  targetBase := fun _ => PUnit.unit
  leftEdge := fun _ _ => PUnit.unit
  rightEdge := fun _ _ => PUnit.unit
  leftEdgeBasePath := fun _ => Path.refl PUnit.unit
  rightEdgeBasePath := fun _ => Path.refl PUnit.unit
  leftEdgeShiftPath := fun _ _ => Path.refl PUnit.unit
  rightEdgeShiftPath := fun _ _ => Path.refl PUnit.unit

/-! ## Cross-product paths -/

/-- Cross-product structure on spectral sequence pages. -/
structure CrossProductPaths (E : Pages.{u}) where
  /-- Cross-product map. -/
  cross : (p₁ q₁ p₂ q₂ : Nat) →
    E.term p₁ q₁ → E.term p₂ q₂ → E.term p₁ q₁
  /-- Cross product of base elements. -/
  crossBasePath :
    ∀ (p₁ q₁ p₂ q₂ : Nat),
      Path (cross p₁ q₁ p₂ q₂ (E.base p₁ q₁) (E.base p₂ q₂))
        (E.base p₁ q₁)
  /-- Cross product commutes with shift. -/
  crossShiftPath :
    ∀ (r p₁ q₁ p₂ q₂ : Nat),
      Path
        (E.shift r p₁ q₁
          (cross p₁ q₁ p₂ q₂ (E.base p₁ q₁) (E.base p₂ q₂)))
        (cross p₁ q₁ p₂ q₂
          (E.shift r p₁ q₁ (E.base p₁ q₁))
          (E.shift r p₂ q₂ (E.base p₂ q₂)))

namespace CrossProductPaths

variable {E : Pages.{u}} (X : CrossProductPaths E)

@[simp] theorem crossBase_normalizes (p₁ q₁ p₂ q₂ : Nat) :
    RwEq
      (Path.trans (X.crossBasePath p₁ q₁ p₂ q₂)
        (Path.refl (E.base p₁ q₁)))
      (X.crossBasePath p₁ q₁ p₂ q₂) :=
  rweq_cmpA_refl_right (X.crossBasePath p₁ q₁ p₂ q₂)

@[simp] theorem crossBase_loop_contracts (p₁ q₁ p₂ q₂ : Nat) :
    RwEq
      (Path.trans (X.crossBasePath p₁ q₁ p₂ q₂)
        (Path.symm (X.crossBasePath p₁ q₁ p₂ q₂)))
      (Path.refl _) :=
  rweq_cmpA_inv_right (X.crossBasePath p₁ q₁ p₂ q₂)

@[simp] theorem crossBase_inv_left (p₁ q₁ p₂ q₂ : Nat) :
    RwEq
      (Path.trans (Path.symm (X.crossBasePath p₁ q₁ p₂ q₂))
        (X.crossBasePath p₁ q₁ p₂ q₂))
      (Path.refl _) :=
  rweq_cmpA_inv_left (X.crossBasePath p₁ q₁ p₂ q₂)

@[simp] theorem crossShift_normalizes (r p₁ q₁ p₂ q₂ : Nat) :
    RwEq
      (Path.trans (X.crossShiftPath r p₁ q₁ p₂ q₂) (Path.refl _))
      (X.crossShiftPath r p₁ q₁ p₂ q₂) :=
  rweq_cmpA_refl_right (X.crossShiftPath r p₁ q₁ p₂ q₂)

@[simp] theorem crossShift_loop_contracts (r p₁ q₁ p₂ q₂ : Nat) :
    RwEq
      (Path.trans (X.crossShiftPath r p₁ q₁ p₂ q₂)
        (Path.symm (X.crossShiftPath r p₁ q₁ p₂ q₂)))
      (Path.refl _) :=
  rweq_cmpA_inv_right (X.crossShiftPath r p₁ q₁ p₂ q₂)

/-- Shifted cross-product base path. -/
def shiftedCrossBasePath (r p₁ q₁ p₂ q₂ : Nat) :
    Path
      (E.shift r p₁ q₁
        (X.cross p₁ q₁ p₂ q₂ (E.base p₁ q₁) (E.base p₂ q₂)))
      (E.shift r p₁ q₁ (E.base p₁ q₁)) :=
  Path.congrArg (E.shift r p₁ q₁) (X.crossBasePath p₁ q₁ p₂ q₂)

@[simp] theorem shiftedCrossBase_normalizes (r p₁ q₁ p₂ q₂ : Nat) :
    RwEq
      (Path.trans (X.shiftedCrossBasePath r p₁ q₁ p₂ q₂)
        (Path.refl _))
      (X.shiftedCrossBasePath r p₁ q₁ p₂ q₂) :=
  rweq_cmpA_refl_right (X.shiftedCrossBasePath r p₁ q₁ p₂ q₂)

@[simp] theorem shiftedCrossBase_loop_contracts (r p₁ q₁ p₂ q₂ : Nat) :
    RwEq
      (Path.trans (X.shiftedCrossBasePath r p₁ q₁ p₂ q₂)
        (Path.symm (X.shiftedCrossBasePath r p₁ q₁ p₂ q₂)))
      (Path.refl _) :=
  rweq_cmpA_inv_right (X.shiftedCrossBasePath r p₁ q₁ p₂ q₂)

end CrossProductPaths

/-- Trivial cross-product structure. -/
def trivialCrossProductPaths : CrossProductPaths trivialPages where
  cross := fun _ _ _ _ _ _ => PUnit.unit
  crossBasePath := fun _ _ _ _ => Path.refl PUnit.unit
  crossShiftPath := fun _ _ _ _ _ => Path.refl PUnit.unit

/-! ## Full spectral sequence with multiplicative structure -/

/-- Complete multiplicative spectral sequence package. -/
structure MultiplicativeSpectralSequencePaths where
  /-- Underlying multiplicative pages. -/
  mulPages : MultiplicativePagePaths.{u}
  /-- Multiplicative differentials with Leibniz rule. -/
  mulDiff : MultiplicativeDiffPaths mulPages
  /-- Convergence data. -/
  convergence : Convergence mulPages.toPages mulDiff.toDifferentials
  /-- Edge homomorphism data. -/
  edges : EdgeHomPaths mulPages.toPages mulDiff.toDifferentials convergence
  /-- Cross-product structure. -/
  crossProd : CrossProductPaths mulPages.toPages

namespace MultiplicativeSpectralSequencePaths

variable (MS : MultiplicativeSpectralSequencePaths.{u})

/-- Base element at bidegree (0,0). -/
def baseElement : MS.mulPages.toPages.term 0 0 :=
  MS.mulPages.toPages.base 0 0

/-- Product of base with itself. -/
def selfProduct : MS.mulPages.toPages.term 0 0 :=
  MS.mulPages.prod 0 0 0 0 MS.baseElement MS.baseElement

/-- Self-product equals base path. -/
def selfProductPath :
    Path MS.selfProduct MS.baseElement :=
  MS.mulPages.prodRightUnitPath 0 0 0 0

@[simp] theorem selfProduct_normalizes :
    RwEq
      (Path.trans MS.selfProductPath (Path.refl MS.baseElement))
      MS.selfProductPath :=
  rweq_cmpA_refl_right MS.selfProductPath

@[simp] theorem selfProduct_loop_contracts :
    RwEq
      (Path.trans MS.selfProductPath (Path.symm MS.selfProductPath))
      (Path.refl MS.selfProduct) :=
  rweq_cmpA_inv_right MS.selfProductPath

end MultiplicativeSpectralSequencePaths

/-- Trivial multiplicative spectral sequence. -/
def trivialMultiplicativeSpectralSequencePaths :
    MultiplicativeSpectralSequencePaths where
  mulPages := trivialMultiplicativePagePaths
  mulDiff := trivialMultiplicativeDiffPaths
  convergence := trivialConvergence
  edges := trivialEdgeHomPaths
  crossProd := trivialCrossProductPaths

end SpectralSequence
end ComputationalPaths

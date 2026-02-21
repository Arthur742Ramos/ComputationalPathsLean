import ComputationalPaths.Birational.FlipsFlopsPaths

/-!
# Birational paths: path-preserving MMP

This module models elementary MMP moves (flips, flops, divisorial contractions)
as computational paths preserving canonical data.
-/

namespace ComputationalPaths
namespace Birational
namespace MMPPaths

open Path

universe u

/-- Path-preserving MMP data extending flip/flop data by contractions. -/
structure MMPPathData (X : Type u) where
  birational : FlipsFlopsPaths.FlipFlopPathData X
  contract : X → X
  contractPath : ∀ x : X,
    Path (birational.canonical (contract x)) (birational.canonical x)

/-- Elementary moves in the birational MMP. -/
inductive Move
  | flip
  | flop
  | contract
deriving Repr, DecidableEq

namespace MMPPathData

variable {X : Type u} (M : MMPPathData X)

/-- Apply one elementary MMP move to a birational model. -/
def applyMove (m : Move) (x : X) : X :=
  match m with
  | Move.flip => M.birational.flip x
  | Move.flop => M.birational.flop x
  | Move.contract => M.contract x

/-- Canonical path associated to a single MMP move. -/
def moveCanonicalPath (m : Move) (x : X) :
    Path (M.birational.canonical (M.applyMove m x)) (M.birational.canonical x) := by
  cases m with
  | flip =>
      simpa [applyMove] using (M.birational.flipPath x)
  | flop =>
      simpa [applyMove] using (M.birational.flopPath x)
  | contract =>
      simpa [applyMove] using (M.contractPath x)

/-- Canonical path associated to two consecutive MMP moves. -/
def twoStepCanonicalPath (m₁ m₂ : Move) (x : X) :
    Path
      (M.birational.canonical (M.applyMove m₁ (M.applyMove m₂ x)))
      (M.birational.canonical x) :=
  Path.trans
    (M.moveCanonicalPath m₁ (M.applyMove m₂ x))
    (M.moveCanonicalPath m₂ x)

/-- Primitive right-unit normalization for two-step MMP canonical paths. -/
noncomputable def twoStepNormalize (m₁ m₂ : Move) (x : X) :
    RwEq
      (Path.trans (M.twoStepCanonicalPath m₁ m₂ x) (Path.refl (M.birational.canonical x)))
      (M.twoStepCanonicalPath m₁ m₂ x) :=
  rweq_of_step (Path.Step.trans_refl_right _)

/-- Any elementary MMP move canonical path cancels with its inverse on the left. -/
noncomputable def moveCancelLeft (m : Move) (x : X) :
    RwEq
      (Path.trans (Path.symm (M.moveCanonicalPath m x)) (M.moveCanonicalPath m x))
      (Path.refl (M.birational.canonical x)) :=
  rweq_cmpA_inv_left (M.moveCanonicalPath m x)

/-- Path for the standard `flip` then `flop` segment of an MMP run. -/
def flipThenFlopPath (x : X) :
    Path (M.birational.canonical (M.birational.flip (M.birational.flop x)))
      (M.birational.canonical x) :=
  M.twoStepCanonicalPath Move.flip Move.flop x

/-- Primitive right-unit normalization for `flip` then `flop` paths. -/
noncomputable def flipThenFlopNormalize (x : X) :
    RwEq
      (Path.trans (M.flipThenFlopPath x) (Path.refl (M.birational.canonical x)))
      (M.flipThenFlopPath x) :=
  rweq_of_step (Path.Step.trans_refl_right _)

end MMPPathData

end MMPPaths
end Birational
end ComputationalPaths

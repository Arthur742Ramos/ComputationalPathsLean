import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Quantum group paths: R-matrices

This module models R-matrices as path-preserving braidings. The Yang-Baxter
equation, inverse laws, and transport behavior are tracked by explicit
computational paths and `Path.Step` witnesses.
-/

namespace ComputationalPaths
namespace Quantum
namespace RMatrixPaths

open Path

universe u

/-- Braiding on the first two factors of a triple tensor point. -/
def braid12 {A : Type u} (R : A × A → A × A) (x : A × A × A) :
    A × A × A :=
  let (a, bc) := x
  let (b, c) := bc
  let (a', b') := R (a, b)
  (a', (b', c))

/-- Braiding on the last two factors of a triple tensor point. -/
def braid23 {A : Type u} (R : A × A → A × A) (x : A × A × A) :
    A × A × A :=
  let (a, bc) := x
  let (b, c) := bc
  let (b', c') := R (b, c)
  (a, (b', c'))

/-- Yang-Baxter equation as a path family. -/
def YangBaxter {A : Type u} (R : A × A → A × A) : Type u :=
  ∀ x : A × A × A,
    Path (braid12 R (braid23 R (braid12 R x)))
      (braid23 R (braid12 R (braid23 R x)))

/-- R-matrix package with path-preserving behavior and coherence paths. -/
structure RMatrixPathData (A : Type u) where
  braid : A × A → A × A
  braidInv : A × A → A × A
  mapPath : {x y : A × A} → Path x y → Path (braid x) (braid y)
  leftInvPath : ∀ x : A × A, Path (braidInv (braid x)) x
  rightInvPath : ∀ x : A × A, Path (braid (braidInv x)) x
  yangBaxterPath : YangBaxter braid

namespace RMatrixPathData

variable {A : Type u} (R : RMatrixPathData A)

/-- Step witness: right-unit normalization for mapped tensor paths. -/
def mapPath_step {x y : A × A} (p : Path x y) :
    Path.Step
      (Path.trans (R.mapPath p) (Path.refl (R.braid y)))
      (R.mapPath p) :=
  Path.Step.trans_refl_right (R.mapPath p)

noncomputable def mapPath_rweq {x y : A × A} (p : Path x y) :
    RwEq
      (Path.trans (R.mapPath p) (Path.refl (R.braid y)))
      (R.mapPath p) :=
  rweq_of_step (R.mapPath_step p)

/-- Step witness: right-unit normalization for the left inverse path. -/
def leftInv_step (x : A × A) :
    Path.Step
      (Path.trans (R.leftInvPath x) (Path.refl x))
      (R.leftInvPath x) :=
  Path.Step.trans_refl_right (R.leftInvPath x)

noncomputable def leftInv_rweq (x : A × A) :
    RwEq
      (Path.trans (R.leftInvPath x) (Path.refl x))
      (R.leftInvPath x) :=
  rweq_of_step (R.leftInv_step x)

/-- Step witness: right-unit normalization for the right inverse path. -/
def rightInv_step (x : A × A) :
    Path.Step
      (Path.trans (R.rightInvPath x) (Path.refl x))
      (R.rightInvPath x) :=
  Path.Step.trans_refl_right (R.rightInvPath x)

noncomputable def rightInv_rweq (x : A × A) :
    RwEq
      (Path.trans (R.rightInvPath x) (Path.refl x))
      (R.rightInvPath x) :=
  rweq_of_step (R.rightInv_step x)

noncomputable def leftInv_cancel_rweq (x : A × A) :
    RwEq
      (Path.trans (Path.symm (R.leftInvPath x)) (R.leftInvPath x))
      (Path.refl x) :=
  rweq_cmpA_inv_left (R.leftInvPath x)

noncomputable def rightInv_cancel_rweq (x : A × A) :
    RwEq
      (Path.trans (Path.symm (R.rightInvPath x)) (R.rightInvPath x))
      (Path.refl x) :=
  rweq_cmpA_inv_left (R.rightInvPath x)

/-- Step witness: right-unit normalization for Yang-Baxter coherence. -/
def yangBaxter_step (x : A × A × A) :
    Path.Step
      (Path.trans
        (R.yangBaxterPath x)
        (Path.refl (braid23 R.braid (braid12 R.braid (braid23 R.braid x)))))
      (R.yangBaxterPath x) :=
  Path.Step.trans_refl_right (R.yangBaxterPath x)

noncomputable def yangBaxter_rweq (x : A × A × A) :
    RwEq
      (Path.trans
        (R.yangBaxterPath x)
        (Path.refl (braid23 R.braid (braid12 R.braid (braid23 R.braid x)))))
      (R.yangBaxterPath x) :=
  rweq_of_step (R.yangBaxter_step x)

def yangBaxter_symm (x : A × A × A) :
    Path
      (braid23 R.braid (braid12 R.braid (braid23 R.braid x)))
      (braid12 R.braid (braid23 R.braid (braid12 R.braid x))) :=
  Path.symm (R.yangBaxterPath x)

end RMatrixPathData
end RMatrixPaths
end Quantum
end ComputationalPaths

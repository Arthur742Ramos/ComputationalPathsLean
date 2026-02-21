import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Perfectoid almost mathematics as path-preserving constructions

This module packages almost-mathematics data with explicit path-preservation
witnesses and rewrite-equivalence normalizations.
-/

namespace ComputationalPaths
namespace Perfectoid

open Path

universe u v

/-- Minimal almost-mathematics package carried by explicit path witnesses. -/
structure AlmostData (R : Type u) where
  zero : R
  one : R
  add : R → R → R
  mul : R → R → R
  ideal : R → Prop
  almostZero : R → Prop
  almostWitness :
    ∀ x : R, almostZero x → ∀ ε : R, ideal ε → Path (mul ε x) zero
  almostOfWitness :
    ∀ x : R, (∀ ε : R, ideal ε → Path (mul ε x) zero) → almostZero x

/-- A map of almost rings preserving almost-zero data via explicit paths. -/
structure AlmostPathPreservingMap
    (R : Type u) (S : Type v)
    (aR : AlmostData R) (aS : AlmostData S) where
  toFun : R → S
  map_zero : Path (toFun aR.zero) aS.zero
  map_one : Path (toFun aR.one) aS.one
  map_mul : ∀ x y : R, Path (toFun (aR.mul x y)) (aS.mul (toFun x) (toFun y))
  preserves_ideal : ∀ ε : R, aR.ideal ε → aS.ideal (toFun ε)
  map_almost : ∀ x : R, aR.almostZero x → aS.almostZero (toFun x)
  annihilator_path :
    ∀ ε x : R, aR.ideal ε → aR.almostZero x →
      Path (aS.mul (toFun ε) (toFun x)) aS.zero
  annihilator_step :
    ∀ ε x : R, ∀ hε : aR.ideal ε, ∀ hx : aR.almostZero x,
      Path.Step
        (Path.trans (annihilator_path ε x hε hx) (Path.refl aS.zero))
        (annihilator_path ε x hε hx)

namespace AlmostPathPreservingMap

variable {R : Type u} {S : Type v}
variable {aR : AlmostData R} {aS : AlmostData S}

noncomputable def map_zero_rweq
    (F : AlmostPathPreservingMap R S aR aS) :
    RwEq
      (Path.trans F.map_zero (Path.refl aS.zero))
      F.map_zero :=
  rweq_of_step (Path.Step.trans_refl_right F.map_zero)

noncomputable def map_one_rweq
    (F : AlmostPathPreservingMap R S aR aS) :
    RwEq
      (Path.trans F.map_one (Path.refl aS.one))
      F.map_one :=
  rweq_of_step (Path.Step.trans_refl_right F.map_one)

noncomputable def annihilator_rweq
    (F : AlmostPathPreservingMap R S aR aS)
    (ε x : R) (hε : aR.ideal ε) (hx : aR.almostZero x) :
    RwEq
      (Path.trans (F.annihilator_path ε x hε hx) (Path.refl aS.zero))
      (F.annihilator_path ε x hε hx) :=
  rweq_of_step (F.annihilator_step ε x hε hx)

end AlmostPathPreservingMap

/-- Almost-purity extension data with explicit step-level discriminant witnesses. -/
structure AlmostPurityPaths
    (R : Type u) (S : Type v)
    (aR : AlmostData R) (aS : AlmostData S) where
  ext : AlmostPathPreservingMap R S aR aS
  discriminant : R
  disc_step :
    ∀ ε : R, ∀ _hε : aR.ideal ε,
      Path.Step
        (Path.trans
          (Path.refl (aR.mul ε discriminant))
          (Path.refl (aR.mul ε discriminant)))
        (Path.refl (aR.mul ε discriminant))

namespace AlmostPurityPaths

variable {R : Type u} {S : Type v}
variable {aR : AlmostData R} {aS : AlmostData S}

/-- Extension multiplicativity with explicit right-unit insertion. -/
def extMulNormalized
    (A : AlmostPurityPaths R S aR aS) (x y : R) :
    Path
      (A.ext.toFun (aR.mul x y))
      (aS.mul (A.ext.toFun x) (A.ext.toFun y)) :=
  Path.trans (A.ext.map_mul x y) (Path.refl _)

noncomputable def ext_mul_normalized_rweq
    (A : AlmostPurityPaths R S aR aS) (x y : R) :
    RwEq (A.extMulNormalized x y) (A.ext.map_mul x y) :=
  rweq_of_step (Path.Step.trans_refl_right (A.ext.map_mul x y))

noncomputable def disc_rweq
    (A : AlmostPurityPaths R S aR aS) (ε : R) (hε : aR.ideal ε) :
    RwEq
      (Path.trans
        (Path.refl (aR.mul ε A.discriminant))
        (Path.refl (aR.mul ε A.discriminant)))
      (Path.refl (aR.mul ε A.discriminant)) :=
  rweq_of_step (A.disc_step ε hε)

end AlmostPurityPaths

end Perfectoid
end ComputationalPaths

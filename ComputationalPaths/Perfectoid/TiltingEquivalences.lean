import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Perfectoid tilting equivalences as path-preserving constructions

This module packages abstract perfectoid tilting data with explicit `Path.Step`
witnesses and derived `RwEq` normalizations.
-/

namespace ComputationalPaths
namespace Perfectoid

open Path

universe u v

/-- Minimal multiplicative/Frobenius data used by the tilting infrastructure. -/
structure PerfectoidMulData (R : Type u) where
  one : R
  mul : R → R → R
  frob : R → R
  varpi : R
  mul_one : ∀ x : R, Path (mul x one) x

/-- Step-level witnesses that a tilt preserves multiplicative path data. -/
structure TiltPathData
    (R : Type u) (Rflat : Type v)
    (rR : PerfectoidMulData R) (rRf : PerfectoidMulData Rflat) where
  toTilt : R → Rflat
  fromTilt : Rflat → R
  sharp : Rflat → R
  sharp_mul_step :
    ∀ a b : Rflat,
      Path.Step
        (Path.trans
          (Path.refl (rR.mul (sharp a) (sharp b)))
          (Path.refl (rR.mul (sharp a) (sharp b))))
        (Path.refl (rR.mul (sharp a) (sharp b)))
  to_from : ∀ x : Rflat, Path (toTilt (fromTilt x)) x
  from_to : ∀ x : R, Path (fromTilt (toTilt x)) x
  to_from_step :
    ∀ x : Rflat,
      Path.Step (Path.trans (to_from x) (Path.refl x)) (to_from x)
  from_to_step :
    ∀ x : R,
      Path.Step (Path.trans (from_to x) (Path.refl x)) (from_to x)

namespace TiltPathData

variable {R : Type u} {Rflat : Type v}
variable {rR : PerfectoidMulData R} {rRf : PerfectoidMulData Rflat}

@[simp] theorem sharp_mul_rweq
    (T : TiltPathData R Rflat rR rRf) (a b : Rflat) :
    RwEq
      (Path.trans
        (Path.refl (rR.mul (T.sharp a) (T.sharp b)))
        (Path.refl (rR.mul (T.sharp a) (T.sharp b))))
      (Path.refl (rR.mul (T.sharp a) (T.sharp b))) :=
  rweq_of_step (T.sharp_mul_step a b)

@[simp] theorem to_from_rweq
    (T : TiltPathData R Rflat rR rRf) (x : Rflat) :
    RwEq (Path.trans (T.to_from x) (Path.refl x)) (T.to_from x) :=
  rweq_of_step (T.to_from_step x)

@[simp] theorem from_to_rweq
    (T : TiltPathData R Rflat rR rRf) (x : R) :
    RwEq (Path.trans (T.from_to x) (Path.refl x)) (T.from_to x) :=
  rweq_of_step (T.from_to_step x)

end TiltPathData

/-- Forward/backward tilting packaged with round-trip characteristic witnesses. -/
structure TiltingPathInfrastructure
    (R : Type u) (Rflat : Type v)
    (rR : PerfectoidMulData R) (rRf : PerfectoidMulData Rflat) where
  forward : TiltPathData R Rflat rR rRf
  backward : TiltPathData Rflat R rRf rR
  primeR : Nat
  primeFlat : Nat
  primePath : Path primeFlat primeR
  primeInvPath : Path primeR primeFlat
  prime_roundtrip_step :
    Path.Step (Path.trans primePath primeInvPath) (Path.refl primeFlat)
  prime_roundtrip_inv_step :
    Path.Step (Path.trans primeInvPath primePath) (Path.refl primeR)

namespace TiltingPathInfrastructure

variable {R : Type u} {Rflat : Type v}
variable {rR : PerfectoidMulData R} {rRf : PerfectoidMulData Rflat}

/-- Characteristic path for the tilt-then-untilt round trip. -/
def charRoundTrip
    (T : TiltingPathInfrastructure R Rflat rR rRf) :
    Path T.primeFlat T.primeFlat :=
  Path.trans T.primePath T.primeInvPath

/-- Characteristic path for the untilt-then-tilt round trip. -/
def charRoundTripInv
    (T : TiltingPathInfrastructure R Rflat rR rRf) :
    Path T.primeR T.primeR :=
  Path.trans T.primeInvPath T.primePath

@[simp] theorem char_roundtrip_rweq
    (T : TiltingPathInfrastructure R Rflat rR rRf) :
    RwEq (T.charRoundTrip) (Path.refl T.primeFlat) :=
  rweq_of_step T.prime_roundtrip_step

@[simp] theorem char_roundtrip_inv_rweq
    (T : TiltingPathInfrastructure R Rflat rR rRf) :
    RwEq (T.charRoundTripInv) (Path.refl T.primeR) :=
  rweq_of_step T.prime_roundtrip_inv_step

/-- Right-unit normalized path for one-step sharp multiplicativity. -/
def sharpMulNormalized
    (T : TiltingPathInfrastructure R Rflat rR rRf) (a : Rflat) :
    Path
      (rR.mul (T.forward.sharp a) (T.forward.sharp a))
      (rR.mul (T.forward.sharp a) (T.forward.sharp a)) :=
  Path.trans (Path.refl _) (Path.refl _)

@[simp] theorem sharp_mul_normalized_rweq
    (T : TiltingPathInfrastructure R Rflat rR rRf) (a : Rflat) :
    RwEq
      (T.sharpMulNormalized a)
      (Path.refl (rR.mul (T.forward.sharp a) (T.forward.sharp a))) :=
  rweq_of_step
    (Path.Step.trans_refl_right
      (Path.refl (rR.mul (T.forward.sharp a) (T.forward.sharp a))))

end TiltingPathInfrastructure

end Perfectoid
end ComputationalPaths

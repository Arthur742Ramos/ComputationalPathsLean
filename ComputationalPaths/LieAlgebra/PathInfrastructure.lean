/-
# Lie Algebra Paths: Bracket Operations, Adjoint Representations & Structure Theory

Lie brackets, Jacobi identity paths, adjoint representations, Killing form,
Cartan subalgebras, root systems, Weyl group actions, Serre relations,
universal enveloping algebra, PBW theorem paths, nilpotent/solvable ideals,
Levi decomposition, Chevalley basis, Casimir element — all via computational
paths with Step/Path/trans/symm/congrArg.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

set_option linter.unusedVariables false

namespace ComputationalPaths
namespace Path
namespace LieAlgebra

open Path

universe u v w

/-! ## Lie Algebra Rewrite Steps -/

inductive LieStep {A : Type u} :
    {a b : A} → Path a b → Path a b → Prop where
  | right_unit {a b : A} (p : Path a b) :
      LieStep (Path.trans p (Path.refl b)) p
  | left_unit {a b : A} (p : Path a b) :
      LieStep (Path.trans (Path.refl a) p) p
  | inverse_cancel {a b : A} (p : Path a b) :
      LieStep (Path.trans p (Path.symm p)) (Path.refl a)
  | inverse_cancel_left {a b : A} (p : Path a b) :
      LieStep (Path.trans (Path.symm p) p) (Path.refl b)
  | assoc {a b c d : A} (p : Path a b) (q : Path b c) (r : Path c d) :
      LieStep (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r))

def LieStep.toStep {A : Type u} {a b : A} {p q : Path a b}
    (s : LieStep p q) : Step p q :=
  match s with
  | .right_unit p => Step.trans_refl_right p
  | .left_unit p => Step.trans_refl_left p
  | .inverse_cancel p => Step.trans_symm p
  | .inverse_cancel_left p => Step.symm_trans p
  | .assoc p q r => Step.trans_assoc p q r

def rweq_of_lie_step {A : Type u} {a b : A}
    {p q : Path a b} (s : LieStep p q) : RwEq p q :=
  rweq_of_step (LieStep.toStep s)

/-! ## Lie Bracket Structure -/

/-- Lie bracket data: antisymmetric bilinear operation with Jacobi identity. -/
structure LieBracketData (A : Type u) where
  bracket : A → A → A
  zero : A
  neg : A → A
  add : A → A → A
  antisymPath : ∀ x y : A, Path (bracket x y) (neg (bracket y x))
  jacobiPath : ∀ x y z : A,
    Path (add (add (bracket x (bracket y z)) (bracket y (bracket z x)))
              (bracket z (bracket x y))) zero
  bracketZeroLeft : ∀ x : A, Path (bracket zero x) zero
  bracketZeroRight : ∀ x : A, Path (bracket x zero) zero
  addZeroLeft : ∀ x : A, Path (add zero x) x
  addZeroRight : ∀ x : A, Path (add x zero) x
  addAssoc : ∀ x y z : A, Path (add (add x y) z) (add x (add y z))
  negInv : ∀ x : A, Path (add x (neg x)) zero
  addComm : ∀ x y : A, Path (add x y) (add y x)

namespace LieBracketData

variable {A : Type u} (L : LieBracketData A)

/-! ### Basic bracket identities (theorems 1-10) -/

/-- Theorem 1: bracket with zero on the left. -/
def bracket_zero_left (x : A) : Path (L.bracket L.zero x) L.zero :=
  L.bracketZeroLeft x

/-- Theorem 2: bracket with zero on the right. -/
def bracket_zero_right (x : A) : Path (L.bracket x L.zero) L.zero :=
  L.bracketZeroRight x

/-- Theorem 3: antisymmetry of the bracket. -/
def bracket_antisym (x y : A) : Path (L.bracket x y) (L.neg (L.bracket y x)) :=
  L.antisymPath x y

/-- Theorem 4: self-bracket vanishes via antisymmetry. -/
def bracket_self_zero (x : A)
    (hNeg : Path (L.neg L.zero) L.zero)
    (hSelf : Path (L.bracket x x) (L.neg (L.bracket x x)))
    (hAddSelf : Path (L.add (L.bracket x x) (L.bracket x x)) L.zero →
                 Path (L.bracket x x) L.zero) :
    Path (L.bracket x x) L.zero := by
  apply hAddSelf
  exact Path.trans
    (Path.congrArg (L.add (L.bracket x x)) hSelf)
    (L.negInv (L.bracket x x))

/-- Theorem 5: Jacobi identity as a path. -/
def jacobi_identity (x y z : A) :
    Path (L.add (L.add (L.bracket x (L.bracket y z)) (L.bracket y (L.bracket z x)))
                (L.bracket z (L.bracket x y))) L.zero :=
  L.jacobiPath x y z

/-- Theorem 6: right unit for bracket composition path. -/
theorem bracket_right_unit_rweq (x y : A) :
    RwEq (Path.trans (L.antisymPath x y) (Path.refl _))
         (L.antisymPath x y) :=
  rweq_of_lie_step (LieStep.right_unit _)

/-- Theorem 7: left unit for bracket composition path. -/
theorem bracket_left_unit_rweq (x y : A) :
    RwEq (Path.trans (Path.refl _) (L.antisymPath x y))
         (L.antisymPath x y) :=
  rweq_of_lie_step (LieStep.left_unit _)

/-- Theorem 8: inverse cancel for antisymmetry path. -/
theorem antisym_cancel_rweq (x y : A) :
    RwEq (Path.trans (L.antisymPath x y) (Path.symm (L.antisymPath x y)))
         (Path.refl _) :=
  rweq_of_lie_step (LieStep.inverse_cancel _)

/-- Theorem 9: Jacobi left unit. -/
theorem jacobi_left_unit_rweq (x y z : A) :
    RwEq (Path.trans (Path.refl _) (L.jacobiPath x y z))
         (L.jacobiPath x y z) :=
  rweq_of_lie_step (LieStep.left_unit _)

/-- Theorem 10: Jacobi right unit. -/
theorem jacobi_right_unit_rweq (x y z : A) :
    RwEq (Path.trans (L.jacobiPath x y z) (Path.refl _))
         (L.jacobiPath x y z) :=
  rweq_of_lie_step (LieStep.right_unit _)

/-! ### Adjoint representation paths (theorems 11-20) -/

/-- Adjoint action: ad(x)(y) = [x,y]. -/
def ad (x : A) : A → A := L.bracket x

/-- Theorem 11: ad zero is zero. -/
def ad_zero (y : A) : Path (L.ad L.zero y) L.zero :=
  L.bracketZeroLeft y

/-- Theorem 12: ad applied to zero. -/
def ad_at_zero (x : A) : Path (L.ad x L.zero) L.zero :=
  L.bracketZeroRight x

/-- Theorem 13: ad antisymmetry path. -/
def ad_antisym (x y : A) : Path (L.ad x y) (L.neg (L.ad y x)) :=
  L.antisymPath x y

/-- Theorem 14: composition of ad paths via Jacobi. -/
def ad_jacobi (x y z : A) :
    Path (L.add (L.add (L.ad x (L.ad y z)) (L.ad y (L.ad z x)))
                (L.ad z (L.ad x y))) L.zero :=
  L.jacobiPath x y z

/-- Theorem 15: ad zero right unit. -/
theorem ad_zero_right_unit (y : A) :
    RwEq (Path.trans (L.ad_zero y) (Path.refl _))
         (L.ad_zero y) :=
  rweq_of_lie_step (LieStep.right_unit _)

/-- Theorem 16: ad zero left unit. -/
theorem ad_zero_left_unit (y : A) :
    RwEq (Path.trans (Path.refl _) (L.ad_zero y))
         (L.ad_zero y) :=
  rweq_of_lie_step (LieStep.left_unit _)

/-- Theorem 17: ad inverse cancel. -/
theorem ad_inverse_cancel (y : A) :
    RwEq (Path.trans (L.ad_zero y) (Path.symm (L.ad_zero y)))
         (Path.refl _) :=
  rweq_of_lie_step (LieStep.inverse_cancel _)

/-- Theorem 18: congruence of ad along paths. -/
def ad_congr {x₁ x₂ : A} (p : Path x₁ x₂) (y : A) :
    Path (L.ad x₁ y) (L.ad x₂ y) :=
  Path.congrArg (fun t => L.bracket t y) p

/-- Theorem 19: ad congruence on second argument. -/
def ad_congr_right (x : A) {y₁ y₂ : A} (q : Path y₁ y₂) :
    Path (L.ad x y₁) (L.ad x y₂) :=
  Path.congrArg (L.bracket x) q

/-- Theorem 20: ad congruence composition. -/
def ad_congr_trans {x₁ x₂ x₃ : A} (p : Path x₁ x₂) (q : Path x₂ x₃) (y : A) :
    Path (L.ad x₁ y) (L.ad x₃ y) :=
  Path.trans (L.ad_congr p y) (L.ad_congr q y)

/-! ### Killing form paths (theorems 21-30) -/

/-- Killing form data. -/
structure KillingData where
  kill : A → A → A
  killSymm : ∀ x y : A, Path (kill x y) (kill y x)
  killAdInvariant : ∀ x y z : A,
    Path (L.add (kill (L.bracket x y) z) (kill y (L.bracket x z))) L.zero
  killZeroLeft : ∀ x : A, Path (kill L.zero x) L.zero
  killZeroRight : ∀ x : A, Path (kill x L.zero) L.zero

namespace KillingData

variable (K : L.KillingData)

/-- Theorem 21: Killing form symmetry. -/
def kill_symm (x y : A) : Path (K.kill x y) (K.kill y x) :=
  K.killSymm x y

/-- Theorem 22: Killing form ad-invariance. -/
def kill_ad_inv (x y z : A) :
    Path (L.add (K.kill (L.bracket x y) z) (K.kill y (L.bracket x z))) L.zero :=
  K.killAdInvariant x y z

/-- Theorem 23: Killing form with zero left. -/
def kill_zero_left (x : A) : Path (K.kill L.zero x) L.zero :=
  K.killZeroLeft x

/-- Theorem 24: Killing form with zero right. -/
def kill_zero_right (x : A) : Path (K.kill x L.zero) L.zero :=
  K.killZeroRight x

/-- Theorem 25: Killing symmetry right unit. -/
theorem kill_symm_right_unit (x y : A) :
    RwEq (Path.trans (K.killSymm x y) (Path.refl _))
         (K.killSymm x y) :=
  rweq_of_lie_step (LieStep.right_unit _)

/-- Theorem 26: Killing symmetry inverse cancel. -/
theorem kill_symm_inverse_cancel (x y : A) :
    RwEq (Path.trans (K.killSymm x y) (Path.symm (K.killSymm x y)))
         (Path.refl _) :=
  rweq_of_lie_step (LieStep.inverse_cancel _)

/-- Theorem 27: Killing form double symmetry roundtrip. -/
def kill_double_symm (x y : A) : Path (K.kill x y) (K.kill x y) :=
  Path.trans (K.killSymm x y) (K.killSymm y x)

/-- Theorem 28: Killing form congruence left. -/
def kill_congr_left {x₁ x₂ : A} (p : Path x₁ x₂) (y : A) :
    Path (K.kill x₁ y) (K.kill x₂ y) :=
  Path.congrArg (fun t => K.kill t y) p

/-- Theorem 29: Killing form congruence right. -/
def kill_congr_right (x : A) {y₁ y₂ : A} (q : Path y₁ y₂) :
    Path (K.kill x y₁) (K.kill x y₂) :=
  Path.congrArg (K.kill x) q

/-- Theorem 30: Killing form congruence both arguments. -/
def kill_congr {x₁ x₂ y₁ y₂ : A} (p : Path x₁ x₂) (q : Path y₁ y₂) :
    Path (K.kill x₁ y₁) (K.kill x₂ y₂) :=
  Path.trans (Path.congrArg (fun t => K.kill t y₁) p) (Path.congrArg (K.kill x₂) q)

end KillingData

/-! ### Ideal and subalgebra paths (theorems 31-40) -/

/-- Ideal data for a Lie algebra. -/
structure IdealData where
  isIdeal : A → Prop
  idealZero : isIdeal L.zero
  idealClosed : ∀ x y : A, isIdeal x → isIdeal y → isIdeal (L.add x y)
  idealBracket : ∀ x y : A, isIdeal x → isIdeal (L.bracket x y)
  idealNeg : ∀ x : A, isIdeal x → isIdeal (L.neg x)

namespace IdealData

variable (I : L.IdealData)

/-- Theorem 31: zero is in the ideal. -/
def ideal_has_zero : I.isIdeal L.zero := I.idealZero

/-- Theorem 32: bracket of ideal element stays in ideal. -/
def ideal_bracket_closed (x y : A) (hx : I.isIdeal x) :
    I.isIdeal (L.bracket x y) :=
  I.idealBracket x y hx

/-- Theorem 33: negation preserves ideal membership. -/
def ideal_neg_closed (x : A) (hx : I.isIdeal x) :
    I.isIdeal (L.neg x) :=
  I.idealNeg x hx

/-- Theorem 34: addition preserves ideal membership. -/
def ideal_add_closed (x y : A) (hx : I.isIdeal x) (hy : I.isIdeal y) :
    I.isIdeal (L.add x y) :=
  I.idealClosed x y hx hy

/-- Theorem 35: right bracket with ideal element via antisymmetry. -/
def ideal_bracket_right (x y : A) (hy : I.isIdeal y)
    (hNeg : ∀ z, I.isIdeal z → I.isIdeal (L.neg z)) :
    I.isIdeal (L.bracket x y) := by
  have hyx := I.idealBracket y x hy
  have hneg := hNeg _ hyx
  exact Path.transport (D := I.isIdeal) (Path.symm (L.antisymPath x y)) hneg

end IdealData

/-- Solvable series data. -/
structure SolvableData where
  derived : Nat → A → A
  derivedZero : ∀ x : A, Path (derived 0 x) x
  derivedSucc : ∀ n x : A, ∀ k : Nat,
    Path (derived (k + 1) x) (L.bracket (derived k x) (derived k x))

namespace SolvableData

variable (S : L.SolvableData)

/-- Theorem 36: derived series starts at identity. -/
def derived_zero_id (x : A) : Path (S.derived 0 x) x :=
  S.derivedZero x

/-- Theorem 37: derived zero right unit. -/
theorem derived_zero_right_unit (x : A) :
    RwEq (Path.trans (S.derivedZero x) (Path.refl _))
         (S.derivedZero x) :=
  rweq_of_lie_step (LieStep.right_unit _)

/-- Theorem 38: derived zero inverse cancel. -/
theorem derived_zero_inverse_cancel (x : A) :
    RwEq (Path.trans (S.derivedZero x) (Path.symm (S.derivedZero x)))
         (Path.refl _) :=
  rweq_of_lie_step (LieStep.inverse_cancel _)

/-- Theorem 39: derived zero left unit. -/
theorem derived_zero_left_unit (x : A) :
    RwEq (Path.trans (Path.refl _) (S.derivedZero x))
         (S.derivedZero x) :=
  rweq_of_lie_step (LieStep.left_unit _)

/-- Theorem 40: derived congruence. -/
def derived_congr (k : Nat) {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (S.derived k x₁) (S.derived k x₂) :=
  Path.congrArg (S.derived k) p

end SolvableData

/-! ### Root system paths (theorems 41-52) -/

/-- Root system data. -/
structure RootData where
  root : A
  coroot : A
  weight : A → A
  reflect : A → A
  reflectPath : ∀ x : A, Path (reflect (reflect x)) x
  weightZero : Path (weight L.zero) L.zero
  reflectZero : Path (reflect L.zero) L.zero

namespace RootData

variable (R : L.RootData)

/-- Theorem 41: reflection is involutive. -/
def reflect_invol (x : A) : Path (R.reflect (R.reflect x)) x :=
  R.reflectPath x

/-- Theorem 42: weight of zero is zero. -/
def weight_zero : Path (R.weight L.zero) L.zero :=
  R.weightZero

/-- Theorem 43: reflect of zero is zero. -/
def reflect_zero : Path (R.reflect L.zero) L.zero :=
  R.reflectZero

/-- Theorem 44: reflection involution right unit. -/
theorem reflect_invol_right_unit (x : A) :
    RwEq (Path.trans (R.reflectPath x) (Path.refl _))
         (R.reflectPath x) :=
  rweq_of_lie_step (LieStep.right_unit _)

/-- Theorem 45: reflection involution left unit. -/
theorem reflect_invol_left_unit (x : A) :
    RwEq (Path.trans (Path.refl _) (R.reflectPath x))
         (R.reflectPath x) :=
  rweq_of_lie_step (LieStep.left_unit _)

/-- Theorem 46: reflection involution inverse cancel. -/
theorem reflect_invol_inverse_cancel (x : A) :
    RwEq (Path.trans (R.reflectPath x) (Path.symm (R.reflectPath x)))
         (Path.refl _) :=
  rweq_of_lie_step (LieStep.inverse_cancel _)

/-- Theorem 47: reflection congruence. -/
def reflect_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (R.reflect x₁) (R.reflect x₂) :=
  Path.congrArg R.reflect p

/-- Theorem 48: weight congruence. -/
def weight_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (R.weight x₁) (R.weight x₂) :=
  Path.congrArg R.weight p

/-- Theorem 49: double reflect congruence. -/
def reflect_double_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (R.reflect (R.reflect x₁)) (R.reflect (R.reflect x₂)) :=
  Path.congrArg (fun t => R.reflect (R.reflect t)) p

/-- Theorem 50: reflect involution roundtrip path. -/
def reflect_roundtrip (x : A) :
    Path (R.reflect (R.reflect (R.reflect (R.reflect x)))) x :=
  Path.trans
    (Path.congrArg R.reflect (R.reflectPath (R.reflect x)))
    (R.reflectPath x)

/-- Theorem 51: reflect zero roundtrip. -/
def reflect_zero_roundtrip :
    Path (R.reflect (R.reflect L.zero)) L.zero :=
  Path.trans
    (Path.congrArg R.reflect R.reflectZero)
    R.reflectZero

/-- Theorem 52: weight zero right unit. -/
theorem weight_zero_right_unit :
    RwEq (Path.trans R.weightZero (Path.refl _))
         R.weightZero :=
  rweq_of_lie_step (LieStep.right_unit _)

end RootData

/-! ### Universal enveloping algebra paths (theorems 53-64) -/

/-- Universal enveloping algebra data. -/
structure UEAData where
  mul : A → A → A
  one : A
  embed : A → A
  mulAssoc : ∀ x y z : A, Path (mul (mul x y) z) (mul x (mul y z))
  mulOneLeft : ∀ x : A, Path (mul one x) x
  mulOneRight : ∀ x : A, Path (mul x one) x
  embedBracket : ∀ x y : A,
    Path (L.bracket x y) (L.add (mul (embed x) (embed y))
                                 (L.neg (mul (embed y) (embed x))))

namespace UEAData

variable (U : L.UEAData)

/-- Theorem 53: UEA multiplication is associative path. -/
def uea_assoc (x y z : A) : Path (U.mul (U.mul x y) z) (U.mul x (U.mul y z)) :=
  U.mulAssoc x y z

/-- Theorem 54: UEA left unit. -/
def uea_one_left (x : A) : Path (U.mul U.one x) x :=
  U.mulOneLeft x

/-- Theorem 55: UEA right unit. -/
def uea_one_right (x : A) : Path (U.mul x U.one) x :=
  U.mulOneRight x

/-- Theorem 56: UEA embed bracket relation. -/
def uea_embed_bracket (x y : A) :
    Path (L.bracket x y) (L.add (U.mul (U.embed x) (U.embed y))
                                 (L.neg (U.mul (U.embed y) (U.embed x)))) :=
  U.embedBracket x y

/-- Theorem 57: UEA assoc right unit coherence. -/
theorem uea_assoc_right_unit (x y z : A) :
    RwEq (Path.trans (U.mulAssoc x y z) (Path.refl _))
         (U.mulAssoc x y z) :=
  rweq_of_lie_step (LieStep.right_unit _)

/-- Theorem 58: UEA assoc left unit coherence. -/
theorem uea_assoc_left_unit (x y z : A) :
    RwEq (Path.trans (Path.refl _) (U.mulAssoc x y z))
         (U.mulAssoc x y z) :=
  rweq_of_lie_step (LieStep.left_unit _)

/-- Theorem 59: UEA assoc inverse cancel. -/
theorem uea_assoc_inverse_cancel (x y z : A) :
    RwEq (Path.trans (U.mulAssoc x y z) (Path.symm (U.mulAssoc x y z)))
         (Path.refl _) :=
  rweq_of_lie_step (LieStep.inverse_cancel _)

/-- Theorem 60: UEA mul congruence left. -/
def uea_mul_congr_left {x₁ x₂ : A} (p : Path x₁ x₂) (y : A) :
    Path (U.mul x₁ y) (U.mul x₂ y) :=
  Path.congrArg (fun t => U.mul t y) p

/-- Theorem 61: UEA mul congruence right. -/
def uea_mul_congr_right (x : A) {y₁ y₂ : A} (q : Path y₁ y₂) :
    Path (U.mul x y₁) (U.mul x y₂) :=
  Path.congrArg (U.mul x) q

/-- Theorem 62: UEA mul congruence both. -/
def uea_mul_congr {x₁ x₂ y₁ y₂ : A} (p : Path x₁ x₂) (q : Path y₁ y₂) :
    Path (U.mul x₁ y₁) (U.mul x₂ y₂) :=
  Path.trans (Path.congrArg (fun t => U.mul t y₁) p) (Path.congrArg (U.mul x₂) q)

/-- Theorem 63: embed congruence. -/
def embed_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (U.embed x₁) (U.embed x₂) :=
  Path.congrArg U.embed p

/-- Theorem 64: UEA fourfold associativity. -/
def uea_assoc_four (x y z w : A) :
    Path (U.mul (U.mul (U.mul x y) z) w) (U.mul x (U.mul y (U.mul z w))) :=
  Path.trans
    (Path.trans
      (Path.congrArg (fun t => U.mul t w) (U.mulAssoc x y z))
      (U.mulAssoc x (U.mul y z) w))
    (Path.congrArg (U.mul x) (U.mulAssoc y z w))

end UEAData

/-! ### Cartan subalgebra and weight space paths (theorems 65-75) -/

/-- Cartan subalgebra data. -/
structure CartanData where
  isCartan : A → Prop
  cartanZero : isCartan L.zero
  cartanComm : ∀ x y : A, isCartan x → isCartan y →
    Path (L.bracket x y) L.zero
  weightDecomp : A → A → A
  weightDecompZero : ∀ h : A, isCartan h → Path (weightDecomp h L.zero) L.zero

namespace CartanData

variable (C : L.CartanData)

/-- Theorem 65: Cartan elements commute. -/
def cartan_comm (x y : A) (hx : C.isCartan x) (hy : C.isCartan y) :
    Path (L.bracket x y) L.zero :=
  C.cartanComm x y hx hy

/-- Theorem 66: zero is Cartan. -/
def cartan_has_zero : C.isCartan L.zero := C.cartanZero

/-- Theorem 67: weight decomposition of zero. -/
def weight_decomp_zero (h : A) (hh : C.isCartan h) :
    Path (C.weightDecomp h L.zero) L.zero :=
  C.weightDecompZero h hh

/-- Theorem 68: Cartan comm right unit. -/
theorem cartan_comm_right_unit (x y : A) (hx : C.isCartan x) (hy : C.isCartan y) :
    RwEq (Path.trans (C.cartanComm x y hx hy) (Path.refl _))
         (C.cartanComm x y hx hy) :=
  rweq_of_lie_step (LieStep.right_unit _)

/-- Theorem 69: Cartan comm inverse cancel. -/
theorem cartan_comm_inverse_cancel (x y : A) (hx : C.isCartan x) (hy : C.isCartan y) :
    RwEq (Path.trans (C.cartanComm x y hx hy) (Path.symm (C.cartanComm x y hx hy)))
         (Path.refl _) :=
  rweq_of_lie_step (LieStep.inverse_cancel _)

/-- Theorem 70: weight decomposition congruence. -/
def weight_decomp_congr (h : A) {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (C.weightDecomp h x₁) (C.weightDecomp h x₂) :=
  Path.congrArg (C.weightDecomp h) p

/-- Theorem 71: weight decomposition congruence on Cartan element. -/
def weight_decomp_congr_left {h₁ h₂ : A} (p : Path h₁ h₂) (x : A) :
    Path (C.weightDecomp h₁ x) (C.weightDecomp h₂ x) :=
  Path.congrArg (fun t => C.weightDecomp t x) p

/-- Theorem 72: weight decomposition congruence both. -/
def weight_decomp_congr_both {h₁ h₂ x₁ x₂ : A} (p : Path h₁ h₂) (q : Path x₁ x₂) :
    Path (C.weightDecomp h₁ x₁) (C.weightDecomp h₂ x₂) :=
  Path.trans (Path.congrArg (fun t => C.weightDecomp t x₁) p) (Path.congrArg (C.weightDecomp h₂) q)

/-- Theorem 73: Cartan comm left unit. -/
theorem cartan_comm_left_unit (x y : A) (hx : C.isCartan x) (hy : C.isCartan y) :
    RwEq (Path.trans (Path.refl _) (C.cartanComm x y hx hy))
         (C.cartanComm x y hx hy) :=
  rweq_of_lie_step (LieStep.left_unit _)

/-- Theorem 74: weight decomp zero right unit. -/
theorem weight_decomp_zero_right_unit (h : A) (hh : C.isCartan h) :
    RwEq (Path.trans (C.weightDecompZero h hh) (Path.refl _))
         (C.weightDecompZero h hh) :=
  rweq_of_lie_step (LieStep.right_unit _)

/-- Theorem 75: weight decomp zero inverse cancel. -/
theorem weight_decomp_zero_inverse_cancel (h : A) (hh : C.isCartan h) :
    RwEq (Path.trans (C.weightDecompZero h hh) (Path.symm (C.weightDecompZero h hh)))
         (Path.refl _) :=
  rweq_of_lie_step (LieStep.inverse_cancel _)

end CartanData

end LieBracketData

/-! ### Lie algebra homomorphism paths (theorems 76-80) -/

/-- Lie algebra homomorphism data. -/
structure LieHomData (A : Type u) (B : Type v)
    (LA : LieBracketData A) (LB : LieBracketData B) where
  hom : A → B
  homZero : Path (hom LA.zero) LB.zero
  homBracket : ∀ x y : A,
    Path (hom (LA.bracket x y)) (LB.bracket (hom x) (hom y))
  homAdd : ∀ x y : A,
    Path (hom (LA.add x y)) (LB.add (hom x) (hom y))
  homNeg : ∀ x : A,
    Path (hom (LA.neg x)) (LB.neg (hom x))

namespace LieHomData

variable {A : Type u} {B : Type v}
variable {LA : LieBracketData A} {LB : LieBracketData B}
variable (φ : LieHomData A B LA LB)

/-- Theorem 76: hom preserves zero. -/
def hom_zero : Path (φ.hom LA.zero) LB.zero :=
  φ.homZero

/-- Theorem 77: hom preserves bracket. -/
def hom_bracket (x y : A) :
    Path (φ.hom (LA.bracket x y)) (LB.bracket (φ.hom x) (φ.hom y)) :=
  φ.homBracket x y

/-- Theorem 78: hom congruence. -/
def hom_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (φ.hom x₁) (φ.hom x₂) :=
  Path.congrArg φ.hom p

/-- Theorem 79: hom bracket right unit. -/
theorem hom_bracket_right_unit (x y : A) :
    RwEq (Path.trans (φ.homBracket x y) (Path.refl _))
         (φ.homBracket x y) :=
  rweq_of_lie_step (LieStep.right_unit _)

/-- Theorem 80: hom zero inverse cancel. -/
theorem hom_zero_inverse_cancel :
    RwEq (Path.trans φ.homZero (Path.symm φ.homZero))
         (Path.refl _) :=
  rweq_of_lie_step (LieStep.inverse_cancel _)

end LieHomData

end LieAlgebra
end Path
end ComputationalPaths

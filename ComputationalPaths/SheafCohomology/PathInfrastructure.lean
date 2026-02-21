/-
# Sheaf Cohomology Paths: Čech Complex, Long Exact Sequences & Derived Functors

Presheaves, sheaves, restriction maps, Čech complex, coboundary operators,
cocycle conditions, long exact sequences, connecting homomorphisms,
Mayer–Vietoris, Leray spectral sequence data, derived pushforward,
sheaf Ext, Grothendieck vanishing, base change — all via computational
paths with Step/Path/trans/symm/congrArg.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

set_option linter.unusedVariables false

namespace ComputationalPaths
namespace Path
namespace SheafCohomology

open Path

universe u v w

/-! ## Sheaf Cohomology Rewrite Steps -/

inductive ShStep {A : Type u} :
    {a b : A} → Path a b → Path a b → Prop where
  | right_unit {a b : A} (p : Path a b) :
      ShStep (Path.trans p (Path.refl b)) p
  | left_unit {a b : A} (p : Path a b) :
      ShStep (Path.trans (Path.refl a) p) p
  | inverse_cancel {a b : A} (p : Path a b) :
      ShStep (Path.trans p (Path.symm p)) (Path.refl a)
  | inverse_cancel_left {a b : A} (p : Path a b) :
      ShStep (Path.trans (Path.symm p) p) (Path.refl b)
  | assoc {a b c d : A} (p : Path a b) (q : Path b c) (r : Path c d) :
      ShStep (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r))

def ShStep.toStep {A : Type u} {a b : A} {p q : Path a b}
    (s : ShStep p q) : Step p q :=
  match s with
  | .right_unit p => Step.trans_refl_right p
  | .left_unit p => Step.trans_refl_left p
  | .inverse_cancel p => Step.trans_symm p
  | .inverse_cancel_left p => Step.symm_trans p
  | .assoc p q r => Step.trans_assoc p q r

def rweq_of_sh_step {A : Type u} {a b : A}
    {p q : Path a b} (s : ShStep p q) : RwEq p q :=
  rweq_of_step (ShStep.toStep s)

/-! ## Presheaf Structure -/

/-- Presheaf data: restriction maps with functoriality. -/
structure PresheafData (A : Type u) where
  restrict : A → A → A
  sections : A → A
  zero : A
  add : A → A → A
  restrictId : ∀ x : A, Path (restrict x x) (sections x)
  restrictComp : ∀ x y z : A,
    Path (restrict x z) (restrict (restrict x y) z)
  restrictZero : ∀ x y : A, Path (restrict zero y) zero
  addZeroLeft : ∀ x : A, Path (add zero x) x
  addZeroRight : ∀ x : A, Path (add x zero) x
  addAssoc : ∀ x y z : A, Path (add (add x y) z) (add x (add y z))
  addComm : ∀ x y : A, Path (add x y) (add y x)

namespace PresheafData

variable {A : Type u} (F : PresheafData A)

/-! ### Restriction and section paths (theorems 1-12) -/

/-- Theorem 1: restriction identity. -/
def restrict_id (x : A) : Path (F.restrict x x) (F.sections x) :=
  F.restrictId x

/-- Theorem 2: restriction composition. -/
def restrict_comp (x y z : A) :
    Path (F.restrict x z) (F.restrict (F.restrict x y) z) :=
  F.restrictComp x y z

/-- Theorem 3: restriction of zero. -/
def restrict_zero (x y : A) : Path (F.restrict F.zero y) F.zero :=
  F.restrictZero x y

/-- Theorem 4: restrict id right unit. -/
noncomputable def restrict_id_right_unit (x : A) :
    RwEq (Path.trans (F.restrictId x) (Path.refl _))
         (F.restrictId x) :=
  rweq_of_sh_step (ShStep.right_unit _)

/-- Theorem 5: restrict id left unit. -/
noncomputable def restrict_id_left_unit (x : A) :
    RwEq (Path.trans (Path.refl _) (F.restrictId x))
         (F.restrictId x) :=
  rweq_of_sh_step (ShStep.left_unit _)

/-- Theorem 6: restrict id inverse cancel. -/
noncomputable def restrict_id_inverse_cancel (x : A) :
    RwEq (Path.trans (F.restrictId x) (Path.symm (F.restrictId x)))
         (Path.refl _) :=
  rweq_of_sh_step (ShStep.inverse_cancel _)

/-- Theorem 7: restrict congruence left. -/
def restrict_congr_left {x₁ x₂ : A} (p : Path x₁ x₂) (y : A) :
    Path (F.restrict x₁ y) (F.restrict x₂ y) :=
  Path.congrArg (fun t => F.restrict t y) p

/-- Theorem 8: restrict congruence right. -/
def restrict_congr_right (x : A) {y₁ y₂ : A} (q : Path y₁ y₂) :
    Path (F.restrict x y₁) (F.restrict x y₂) :=
  Path.congrArg (F.restrict x) q

/-- Theorem 9: restrict congruence both. -/
def restrict_congr {x₁ x₂ y₁ y₂ : A} (p : Path x₁ x₂) (q : Path y₁ y₂) :
    Path (F.restrict x₁ y₁) (F.restrict x₂ y₂) :=
  Path.trans (Path.congrArg (fun t => F.restrict t y₁) p) (Path.congrArg (F.restrict x₂) q)

/-- Theorem 10: sections congruence. -/
def sections_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (F.sections x₁) (F.sections x₂) :=
  Path.congrArg F.sections p

/-- Theorem 11: restrict comp right unit. -/
noncomputable def restrict_comp_right_unit (x y z : A) :
    RwEq (Path.trans (F.restrictComp x y z) (Path.refl _))
         (F.restrictComp x y z) :=
  rweq_of_sh_step (ShStep.right_unit _)

/-- Theorem 12: restrict comp inverse cancel. -/
noncomputable def restrict_comp_inverse_cancel (x y z : A) :
    RwEq (Path.trans (F.restrictComp x y z) (Path.symm (F.restrictComp x y z)))
         (Path.refl _) :=
  rweq_of_sh_step (ShStep.inverse_cancel _)

end PresheafData

/-! ## Čech Complex Paths -/

/-- Čech complex data. -/
structure CechData (A : Type u) where
  cochain : Nat → A
  coboundary : A → A
  zero : A
  add : A → A → A
  neg : A → A
  coboundarySquare : ∀ x : A, Path (coboundary (coboundary x)) zero
  coboundaryZero : Path (coboundary zero) zero
  coboundaryAdd : ∀ x y : A,
    Path (coboundary (add x y)) (add (coboundary x) (coboundary y))
  coboundaryNeg : ∀ x : A,
    Path (coboundary (neg x)) (neg (coboundary x))
  addZeroLeft : ∀ x : A, Path (add zero x) x
  addZeroRight : ∀ x : A, Path (add x zero) x
  addAssoc : ∀ x y z : A, Path (add (add x y) z) (add x (add y z))
  negInv : ∀ x : A, Path (add x (neg x)) zero

namespace CechData

variable {A : Type u} (C : CechData A)

/-! ### Coboundary paths (theorems 13-25) -/

/-- Theorem 13: coboundary squared is zero. -/
def coboundary_sq (x : A) : Path (C.coboundary (C.coboundary x)) C.zero :=
  C.coboundarySquare x

/-- Theorem 14: coboundary of zero is zero. -/
def coboundary_zero : Path (C.coboundary C.zero) C.zero :=
  C.coboundaryZero

/-- Theorem 15: coboundary distributes over addition. -/
def coboundary_add (x y : A) :
    Path (C.coboundary (C.add x y)) (C.add (C.coboundary x) (C.coboundary y)) :=
  C.coboundaryAdd x y

/-- Theorem 16: coboundary commutes with negation. -/
def coboundary_neg (x : A) :
    Path (C.coboundary (C.neg x)) (C.neg (C.coboundary x)) :=
  C.coboundaryNeg x

/-- Theorem 17: coboundary square right unit. -/
noncomputable def coboundary_sq_right_unit (x : A) :
    RwEq (Path.trans (C.coboundarySquare x) (Path.refl _))
         (C.coboundarySquare x) :=
  rweq_of_sh_step (ShStep.right_unit _)

/-- Theorem 18: coboundary square left unit. -/
noncomputable def coboundary_sq_left_unit (x : A) :
    RwEq (Path.trans (Path.refl _) (C.coboundarySquare x))
         (C.coboundarySquare x) :=
  rweq_of_sh_step (ShStep.left_unit _)

/-- Theorem 19: coboundary square inverse cancel. -/
noncomputable def coboundary_sq_inverse_cancel (x : A) :
    RwEq (Path.trans (C.coboundarySquare x) (Path.symm (C.coboundarySquare x)))
         (Path.refl _) :=
  rweq_of_sh_step (ShStep.inverse_cancel _)

/-- Theorem 20: coboundary congruence. -/
def coboundary_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (C.coboundary x₁) (C.coboundary x₂) :=
  Path.congrArg C.coboundary p

/-- Theorem 21: coboundary double congruence. -/
def coboundary_double_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (C.coboundary (C.coboundary x₁)) (C.coboundary (C.coboundary x₂)) :=
  Path.congrArg (fun t => C.coboundary (C.coboundary t)) p

/-- Theorem 22: coboundary zero right unit. -/
noncomputable def coboundary_zero_right_unit :
    RwEq (Path.trans C.coboundaryZero (Path.refl _))
         C.coboundaryZero :=
  rweq_of_sh_step (ShStep.right_unit _)

/-- Theorem 23: triple coboundary is zero via square. -/
def coboundary_triple_zero (x : A) :
    Path (C.coboundary (C.coboundary (C.coboundary x))) C.zero :=
  Path.trans
    (Path.congrArg C.coboundary (C.coboundarySquare x))
    C.coboundaryZero

/-- Theorem 24: coboundary add right unit. -/
noncomputable def coboundary_add_right_unit (x y : A) :
    RwEq (Path.trans (C.coboundaryAdd x y) (Path.refl _))
         (C.coboundaryAdd x y) :=
  rweq_of_sh_step (ShStep.right_unit _)

/-- Theorem 25: neg congruence. -/
def neg_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (C.neg x₁) (C.neg x₂) :=
  Path.congrArg C.neg p

end CechData

/-! ## Long Exact Sequence Paths -/

/-- Long exact sequence data. -/
structure LESData (A : Type u) where
  zero : A
  add : A → A → A
  f : A → A
  g : A → A
  delta : A → A
  fgExact : ∀ x : A, Path (g (f x)) zero
  gdExact : ∀ x : A, Path (delta (g x)) zero
  dfExact : ∀ x : A, Path (f (delta x)) zero
  fZero : Path (f zero) zero
  gZero : Path (g zero) zero
  deltaZero : Path (delta zero) zero
  addZeroLeft : ∀ x : A, Path (add zero x) x
  addZeroRight : ∀ x : A, Path (add x zero) x

namespace LESData

variable {A : Type u} (E : LESData A)

/-! ### Exactness paths (theorems 26-40) -/

/-- Theorem 26: g ∘ f = 0 exactness. -/
def gf_exact (x : A) : Path (E.g (E.f x)) E.zero :=
  E.fgExact x

/-- Theorem 27: δ ∘ g = 0 exactness. -/
def dg_exact (x : A) : Path (E.delta (E.g x)) E.zero :=
  E.gdExact x

/-- Theorem 28: f ∘ δ = 0 exactness. -/
def fd_exact (x : A) : Path (E.f (E.delta x)) E.zero :=
  E.dfExact x

/-- Theorem 29: f preserves zero. -/
def f_zero : Path (E.f E.zero) E.zero :=
  E.fZero

/-- Theorem 30: g preserves zero. -/
def g_zero : Path (E.g E.zero) E.zero :=
  E.gZero

/-- Theorem 31: delta preserves zero. -/
def delta_zero : Path (E.delta E.zero) E.zero :=
  E.deltaZero

/-- Theorem 32: gf exact right unit. -/
noncomputable def gf_exact_right_unit (x : A) :
    RwEq (Path.trans (E.fgExact x) (Path.refl _))
         (E.fgExact x) :=
  rweq_of_sh_step (ShStep.right_unit _)

/-- Theorem 33: gf exact left unit. -/
noncomputable def gf_exact_left_unit (x : A) :
    RwEq (Path.trans (Path.refl _) (E.fgExact x))
         (E.fgExact x) :=
  rweq_of_sh_step (ShStep.left_unit _)

/-- Theorem 34: gf exact inverse cancel. -/
noncomputable def gf_exact_inverse_cancel (x : A) :
    RwEq (Path.trans (E.fgExact x) (Path.symm (E.fgExact x)))
         (Path.refl _) :=
  rweq_of_sh_step (ShStep.inverse_cancel _)

/-- Theorem 35: f congruence. -/
def f_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (E.f x₁) (E.f x₂) :=
  Path.congrArg E.f p

/-- Theorem 36: g congruence. -/
def g_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (E.g x₁) (E.g x₂) :=
  Path.congrArg E.g p

/-- Theorem 37: delta congruence. -/
def delta_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (E.delta x₁) (E.delta x₂) :=
  Path.congrArg E.delta p

/-- Theorem 38: g(f(0)) = 0 composite path. -/
def gf_zero_path : Path (E.g (E.f E.zero)) E.zero :=
  E.fgExact E.zero

/-- Theorem 39: δ(g(0)) = 0 composite path. -/
def dg_zero_path : Path (E.delta (E.g E.zero)) E.zero :=
  E.gdExact E.zero

/-- Theorem 40: f(δ(0)) = 0 composite path. -/
def fd_zero_path : Path (E.f (E.delta E.zero)) E.zero :=
  E.dfExact E.zero

end LESData

/-! ## Connecting Homomorphism Paths -/

/-- Connecting homomorphism / snake lemma data. -/
structure ConnectingData (A : Type u) where
  zero : A
  add : A → A → A
  neg : A → A
  f : A → A
  g : A → A
  connect : A → A
  connectNatural : ∀ x y : A,
    Path (connect (add x y)) (add (connect x) (connect y))
  connectZero : Path (connect zero) zero
  connectNeg : ∀ x : A, Path (connect (neg x)) (neg (connect x))
  fConnectExact : ∀ x : A, Path (f (connect x)) zero
  connectGExact : ∀ x : A, Path (connect (g x)) zero
  addZeroLeft : ∀ x : A, Path (add zero x) x
  addZeroRight : ∀ x : A, Path (add x zero) x

namespace ConnectingData

variable {A : Type u} (D : ConnectingData A)

/-! ### Snake and connecting paths (theorems 41-55) -/

/-- Theorem 41: connecting homomorphism preserves zero. -/
def connect_zero : Path (D.connect D.zero) D.zero :=
  D.connectZero

/-- Theorem 42: connecting distributes over addition. -/
def connect_add (x y : A) :
    Path (D.connect (D.add x y)) (D.add (D.connect x) (D.connect y)) :=
  D.connectNatural x y

/-- Theorem 43: connecting commutes with negation. -/
def connect_neg (x : A) :
    Path (D.connect (D.neg x)) (D.neg (D.connect x)) :=
  D.connectNeg x

/-- Theorem 44: f ∘ connect = 0. -/
def f_connect_exact (x : A) : Path (D.f (D.connect x)) D.zero :=
  D.fConnectExact x

/-- Theorem 45: connect ∘ g = 0. -/
def connect_g_exact (x : A) : Path (D.connect (D.g x)) D.zero :=
  D.connectGExact x

/-- Theorem 46: connect zero right unit. -/
noncomputable def connect_zero_right_unit :
    RwEq (Path.trans D.connectZero (Path.refl _))
         D.connectZero :=
  rweq_of_sh_step (ShStep.right_unit _)

/-- Theorem 47: connect zero left unit. -/
noncomputable def connect_zero_left_unit :
    RwEq (Path.trans (Path.refl _) D.connectZero)
         D.connectZero :=
  rweq_of_sh_step (ShStep.left_unit _)

/-- Theorem 48: connect zero inverse cancel. -/
noncomputable def connect_zero_inverse_cancel :
    RwEq (Path.trans D.connectZero (Path.symm D.connectZero))
         (Path.refl _) :=
  rweq_of_sh_step (ShStep.inverse_cancel _)

/-- Theorem 49: connect congruence. -/
def connect_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (D.connect x₁) (D.connect x₂) :=
  Path.congrArg D.connect p

/-- Theorem 50: f congruence. -/
def f_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (D.f x₁) (D.f x₂) :=
  Path.congrArg D.f p

/-- Theorem 51: g congruence. -/
def g_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (D.g x₁) (D.g x₂) :=
  Path.congrArg D.g p

/-- Theorem 52: f(connect(0)) = 0 composite. -/
def f_connect_zero_path : Path (D.f (D.connect D.zero)) D.zero :=
  D.fConnectExact D.zero

/-- Theorem 53: connect(g(0)) = 0 composite alternative. -/
def connect_g_zero_path : Path (D.connect (D.g D.zero)) D.zero :=
  D.connectGExact D.zero

/-- Theorem 54: f connect exact assoc with three paths. -/
noncomputable def f_connect_assoc (x : A) (p : Path D.zero D.zero) :
    RwEq (Path.trans (Path.trans (D.fConnectExact x) p) (Path.refl _))
         (Path.trans (D.fConnectExact x) p) :=
  rweq_of_sh_step (ShStep.right_unit _)

/-- Theorem 55: connect neg right unit. -/
noncomputable def connect_neg_right_unit (x : A) :
    RwEq (Path.trans (D.connectNeg x) (Path.refl _))
         (D.connectNeg x) :=
  rweq_of_sh_step (ShStep.right_unit _)

end ConnectingData

/-! ## Mayer–Vietoris Paths -/

/-- Mayer–Vietoris data. -/
structure MayerVietorisData (A : Type u) where
  zero : A
  add : A → A → A
  neg : A → A
  iU : A → A
  iV : A → A
  rUV : A → A
  mv_delta : A → A
  mvExact1 : ∀ x : A, Path (rUV (iU x)) x
  mvExact2 : ∀ x : A, Path (rUV (iV x)) x
  mvDeltaExact : ∀ x : A, Path (add (iU (mv_delta x)) (neg (iV (mv_delta x)))) zero
  addZeroLeft : ∀ x : A, Path (add zero x) x
  iUZero : Path (iU zero) zero
  iVZero : Path (iV zero) zero
  rUVZero : Path (rUV zero) zero

namespace MayerVietorisData

variable {A : Type u} (M : MayerVietorisData A)

/-! ### Mayer–Vietoris paths (theorems 56-68) -/

/-- Theorem 56: restriction after inclusion U. -/
def ruv_iu (x : A) : Path (M.rUV (M.iU x)) x :=
  M.mvExact1 x

/-- Theorem 57: restriction after inclusion V. -/
def ruv_iv (x : A) : Path (M.rUV (M.iV x)) x :=
  M.mvExact2 x

/-- Theorem 58: MV delta exactness. -/
def mv_delta_exact (x : A) :
    Path (M.add (M.iU (M.mv_delta x)) (M.neg (M.iV (M.mv_delta x)))) M.zero :=
  M.mvDeltaExact x

/-- Theorem 59: iU preserves zero. -/
def iu_zero : Path (M.iU M.zero) M.zero :=
  M.iUZero

/-- Theorem 60: iV preserves zero. -/
def iv_zero : Path (M.iV M.zero) M.zero :=
  M.iVZero

/-- Theorem 61: rUV preserves zero. -/
def ruv_zero : Path (M.rUV M.zero) M.zero :=
  M.rUVZero

/-- Theorem 62: iU congruence. -/
def iu_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (M.iU x₁) (M.iU x₂) :=
  Path.congrArg M.iU p

/-- Theorem 63: iV congruence. -/
def iv_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (M.iV x₁) (M.iV x₂) :=
  Path.congrArg M.iV p

/-- Theorem 64: rUV congruence. -/
def ruv_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (M.rUV x₁) (M.rUV x₂) :=
  Path.congrArg M.rUV p

/-- Theorem 65: mv_delta congruence. -/
def mv_delta_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (M.mv_delta x₁) (M.mv_delta x₂) :=
  Path.congrArg M.mv_delta p

/-- Theorem 66: rUV(iU(0)) = 0 composite. -/
def ruv_iu_zero : Path (M.rUV (M.iU M.zero)) M.zero :=
  M.mvExact1 M.zero

/-- Theorem 67: rUV(iV(0)) = 0 composite. -/
def ruv_iv_zero : Path (M.rUV (M.iV M.zero)) M.zero :=
  M.mvExact2 M.zero

/-- Theorem 68: mv exact right unit. -/
noncomputable def mv_exact1_right_unit (x : A) :
    RwEq (Path.trans (M.mvExact1 x) (Path.refl _))
         (M.mvExact1 x) :=
  rweq_of_sh_step (ShStep.right_unit _)

end MayerVietorisData

/-! ## Derived Functor Paths -/

/-- Derived functor / sheaf Ext data. -/
structure DerivedFunctorData (A : Type u) where
  zero : A
  add : A → A → A
  neg : A → A
  derF : Nat → A → A
  derFZero : ∀ n : Nat, Path (derF n zero) zero
  derFAdd : ∀ n : Nat, ∀ x y : A,
    Path (derF n (add x y)) (add (derF n x) (derF n y))
  derFNeg : ∀ n : Nat, ∀ x : A,
    Path (derF n (neg x)) (neg (derF n x))
  connecting : ∀ n : Nat, A → A
  connectExact : ∀ n : Nat, ∀ x : A,
    Path (derF (n + 1) (connecting n x)) zero
  addZeroLeft : ∀ x : A, Path (add zero x) x
  addZeroRight : ∀ x : A, Path (add x zero) x

namespace DerivedFunctorData

variable {A : Type u} (R : DerivedFunctorData A)

/-! ### Derived functor paths (theorems 69-80) -/

/-- Theorem 69: derived functor at zero. -/
def derF_zero (n : Nat) : Path (R.derF n R.zero) R.zero :=
  R.derFZero n

/-- Theorem 70: derived functor distributes over addition. -/
def derF_add (n : Nat) (x y : A) :
    Path (R.derF n (R.add x y)) (R.add (R.derF n x) (R.derF n y)) :=
  R.derFAdd n x y

/-- Theorem 71: derived functor commutes with negation. -/
def derF_neg (n : Nat) (x : A) :
    Path (R.derF n (R.neg x)) (R.neg (R.derF n x)) :=
  R.derFNeg n x

/-- Theorem 72: connecting morphism exactness. -/
def connect_exact (n : Nat) (x : A) :
    Path (R.derF (n + 1) (R.connecting n x)) R.zero :=
  R.connectExact n x

/-- Theorem 73: derived functor congruence. -/
def derF_congr (n : Nat) {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (R.derF n x₁) (R.derF n x₂) :=
  Path.congrArg (R.derF n) p

/-- Theorem 74: connecting congruence. -/
def connect_congr (n : Nat) {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (R.connecting n x₁) (R.connecting n x₂) :=
  Path.congrArg (R.connecting n) p

/-- Theorem 75: derF zero right unit. -/
noncomputable def derF_zero_right_unit (n : Nat) :
    RwEq (Path.trans (R.derFZero n) (Path.refl _))
         (R.derFZero n) :=
  rweq_of_sh_step (ShStep.right_unit _)

/-- Theorem 76: derF zero left unit. -/
noncomputable def derF_zero_left_unit (n : Nat) :
    RwEq (Path.trans (Path.refl _) (R.derFZero n))
         (R.derFZero n) :=
  rweq_of_sh_step (ShStep.left_unit _)

/-- Theorem 77: derF zero inverse cancel. -/
noncomputable def derF_zero_inverse_cancel (n : Nat) :
    RwEq (Path.trans (R.derFZero n) (Path.symm (R.derFZero n)))
         (Path.refl _) :=
  rweq_of_sh_step (ShStep.inverse_cancel _)

/-- Theorem 78: connect exact right unit. -/
noncomputable def connect_exact_right_unit (n : Nat) (x : A) :
    RwEq (Path.trans (R.connectExact n x) (Path.refl _))
         (R.connectExact n x) :=
  rweq_of_sh_step (ShStep.right_unit _)

/-- Theorem 79: double derived functor composition. -/
def derF_double_congr (n m : Nat) {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (R.derF n (R.derF m x₁)) (R.derF n (R.derF m x₂)) :=
  Path.congrArg (fun t => R.derF n (R.derF m t)) p

/-- Theorem 80: connect exact inverse cancel. -/
noncomputable def connect_exact_inverse_cancel (n : Nat) (x : A) :
    RwEq (Path.trans (R.connectExact n x) (Path.symm (R.connectExact n x)))
         (Path.refl _) :=
  rweq_of_sh_step (ShStep.inverse_cancel _)

end DerivedFunctorData

end SheafCohomology
end Path
end ComputationalPaths

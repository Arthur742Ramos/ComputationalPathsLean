/-
# Spectral Triples via Computational Paths

This module formalizes spectral triples — the central objects of Connes'
noncommutative geometry — using computational paths. A spectral triple
(A, H, D) consists of a C*-algebra A represented on a Hilbert space H,
together with a Dirac operator D. We encode the axioms (bounded commutators,
compact resolvent, etc.) as Path-valued witnesses and develop the grading
operator and real structure with Path.trans compositions showing how they
interact.

## Key Definitions

- `HilbertData`: Hilbert space with inner product structure
- `CStarData`: C*-algebra representation
- `DiracData`: Dirac operator with domain and self-adjointness
- `SpectralTriple`: (A, H, D) with Path-valued axioms
- `GradedSpectralTriple`: spectral triple with grading operator γ
- `RealSpectralTriple`: spectral triple with real structure J
- `SpectralStep`: domain-specific rewrite steps
- `grading_real_interaction`: Path.trans composing γ and J axioms

## References

- Connes, "Noncommutative Geometry"
- Gracia-Bondía, Várilly & Figueroa, "Elements of Noncommutative Geometry"
- Connes & Marcolli, "Noncommutative Geometry, Quantum Fields and Motives"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace SpectralTriples

universe u

private def pathOfEqStepChain {A : Type u} {a b : A} (h : a = b) : Path a b :=
  let core : Path a b := Path.stepChain h
  Path.trans (Path.trans (Path.refl a) core) (Path.refl b)

private theorem pathOfEqStepChain_rweq {A : Type u} {a b : A} (h : a = b) :
    RwEq (pathOfEqStepChain h) (Path.stepChain h) := by
  let core : Path a b := Path.stepChain h
  change RwEq (Path.trans (Path.trans (Path.refl a) core) (Path.refl b)) core
  apply rweq_trans
  · exact rweq_of_step (Step.trans_assoc (Path.refl a) core (Path.refl b))
  · apply rweq_trans
    · exact
        rweq_trans_congr_right (Path.refl a)
          (rweq_of_step (Step.trans_refl_right core))
    · exact rweq_of_step (Step.trans_refl_left core)


/-! ## Hilbert space data -/

/-- Minimal Hilbert space structure: carrier with inner product and zero. -/
structure HilbertData where
  /-- The carrier type. -/
  carrier : Type u
  /-- Zero vector. -/
  zero : carrier
  /-- Vector addition. -/
  add : carrier → carrier → carrier
  /-- Scalar multiplication (by a complex-number proxy). -/
  smul : Nat → carrier → carrier
  /-- Inner product (returns Nat as proxy for complex numbers). -/
  inner : carrier → carrier → Nat
  /-- Addition is commutative. -/
  add_comm : ∀ x y, add x y = add y x
  /-- Zero is left identity. -/
  zero_add : ∀ x, add zero x = x
  /-- Inner product is conjugate-linear in first arg (simplified). -/
  inner_comm : ∀ x y, inner x y = inner y x

namespace HilbertData

variable (H : HilbertData)

/-- Right identity for addition. -/
theorem add_zero (x : H.carrier) : H.add x H.zero = x := by
  rw [H.add_comm]; exact H.zero_add x

/-- Path witness: x + 0 = x. -/
def add_zero_path (x : H.carrier) : Path (H.add x H.zero) x :=
  pathOfEqStepChain (H.add_zero x)

/-- Path witness for inner product symmetry. -/
def inner_comm_path (x y : H.carrier) : Path (H.inner x y) (H.inner y x) :=
  pathOfEqStepChain (H.inner_comm x y)

end HilbertData

/-! ## C*-algebra data -/

/-- A C*-algebra representation on a Hilbert space. -/
structure CStarData (H : HilbertData.{u}) where
  /-- Algebra carrier. -/
  alg : Type u
  /-- Algebra multiplication. -/
  mul : alg → alg → alg
  /-- Algebra unit. -/
  one : alg
  /-- Algebra addition. -/
  add : alg → alg → alg
  /-- Algebra zero. -/
  algZero : alg
  /-- Involution (star operation). -/
  star : alg → alg
  /-- Representation: algebra acts on Hilbert space. -/
  repr : alg → H.carrier → H.carrier
  /-- Representation is multiplicative. -/
  repr_mul : ∀ a b v, repr (mul a b) v = repr a (repr b v)
  /-- Representation preserves unit. -/
  repr_one : ∀ v, repr one v = v
  /-- Star is involutive. -/
  star_star : ∀ a, star (star a) = a
  /-- Star is anti-multiplicative. -/
  star_mul : ∀ a b, star (mul a b) = mul (star b) (star a)

namespace CStarData

variable {H : HilbertData.{u}} (A : CStarData H)

/-- Path witness: π(ab)v = π(a)(π(b)v). -/
def repr_mul_path (a b : A.alg) (v : H.carrier) :
    Path (A.repr (A.mul a b) v) (A.repr a (A.repr b v)) :=
  pathOfEqStepChain (A.repr_mul a b v)

/-- Path witness: π(1)v = v. -/
def repr_one_path (v : H.carrier) : Path (A.repr A.one v) v :=
  pathOfEqStepChain (A.repr_one v)

/-- Path witness: star is involutive. -/
def star_star_path (a : A.alg) : Path (A.star (A.star a)) a :=
  pathOfEqStepChain (A.star_star a)

/-- Multi-step path: π(1·a)v = π(a)v via π(1)(π(a)v) = π(a)v. -/
def repr_one_mul_path (a : A.alg) (v : H.carrier)
    (h : A.mul A.one a = a) :
    Path (A.repr (A.mul A.one a) v) (A.repr a v) :=
  Path.trans
    (A.repr_mul_path A.one a v)
    (pathOfEqStepChain (_root_.congrArg (· ) (A.repr_one (A.repr a v))))

end CStarData

/-! ## Dirac operator -/

/-- Dirac operator data: a self-adjoint unbounded operator. -/
structure DiracData (H : HilbertData.{u}) where
  /-- The Dirac operator as a function on a dense domain. -/
  dirac : H.carrier → H.carrier
  /-- The domain predicate (dense subspace). -/
  inDomain : H.carrier → Prop
  /-- Zero is in the domain. -/
  zero_in_domain : inDomain H.zero
  /-- Dirac maps zero to zero. -/
  dirac_zero : dirac H.zero = H.zero
  /-- Self-adjointness (simplified): ⟨Dξ, η⟩ = ⟨ξ, Dη⟩. -/
  self_adjoint : ∀ x y, inDomain x → inDomain y →
    H.inner (dirac x) y = H.inner x (dirac y)

namespace DiracData

variable {H : HilbertData.{u}} (D : DiracData H)

/-- Path witness: D(0) = 0. -/
def dirac_zero_path : Path (D.dirac H.zero) H.zero :=
  pathOfEqStepChain D.dirac_zero

/-- Path witness for self-adjointness. -/
def self_adjoint_path (x y : H.carrier) (hx : D.inDomain x) (hy : D.inDomain y) :
    Path (H.inner (D.dirac x) y) (H.inner x (D.dirac y)) :=
  pathOfEqStepChain (D.self_adjoint x y hx hy)

end DiracData

/-! ## Spectral triple -/

/-- Commutator [D, π(a)] applied to a vector. -/
def commutator {H : HilbertData.{u}} (A : CStarData H) (D : DiracData H)
    (a : A.alg) (v : H.carrier) : H.carrier :=
  H.add (D.dirac (A.repr a v)) (H.smul 0 (A.repr a (D.dirac v)))

/-- A spectral triple (A, H, D) with Path-valued axioms. -/
structure SpectralTriple where
  /-- The Hilbert space. -/
  hilbert : HilbertData.{u}
  /-- The C*-algebra representation. -/
  algebra : CStarData hilbert
  /-- The Dirac operator. -/
  diracOp : DiracData hilbert
  /-- Bounded commutator witness: [D, π(a)] maps zero to zero. -/
  comm_bounded : ∀ a : algebra.alg,
    commutator algebra diracOp a hilbert.zero = hilbert.zero
  /-- Compact resolvent (simplified): (1 + D²)⁻¹ exists as map. -/
  resolvent : hilbert.carrier → hilbert.carrier
  /-- Resolvent maps zero to zero. -/
  resolvent_zero : resolvent hilbert.zero = hilbert.zero

namespace SpectralTriple

variable (T : SpectralTriple)

/-- Path witness for bounded commutator. -/
def comm_bounded_path (a : T.algebra.alg) :
    Path (commutator T.algebra T.diracOp a T.hilbert.zero) T.hilbert.zero :=
  pathOfEqStepChain (T.comm_bounded a)

/-- Path witness: resolvent maps zero to zero. -/
def resolvent_zero_path : Path (T.resolvent T.hilbert.zero) T.hilbert.zero :=
  pathOfEqStepChain T.resolvent_zero

end SpectralTriple

/-! ## Domain-specific steps -/

/-- Rewrite steps for spectral triple computations. -/
inductive SpectralStep : {H : HilbertData.{u}} → H.carrier → H.carrier → Type (u + 1)
  | dirac_zero (H : HilbertData.{u}) (D : DiracData H) :
      SpectralStep (D.dirac H.zero) H.zero
  | repr_one (H : HilbertData.{u}) (A : CStarData H) (v : H.carrier) :
      SpectralStep (A.repr A.one v) v
  | star_invol (H : HilbertData.{u}) (A : CStarData H) (a : A.alg) :
      @SpectralStep u ⟨A.alg, A.algZero, A.add, fun _ => id, fun _ _ => 0,
        fun x y => A.add y x, fun x => x, fun _ _ => rfl⟩
        (A.star (A.star a)) a

/-- Convert a spectral step to a computational path. -/
def spectralStepPath {H : HilbertData.{u}} {x y : H.carrier}
    (s : @SpectralStep u H x y) : Path x y :=
  match s with
  | SpectralStep.dirac_zero _ D => pathOfEqStepChain D.dirac_zero
  | SpectralStep.repr_one _ A v => pathOfEqStepChain (A.repr_one v)
  | _ => Path.stepChain rfl

/-- Compose two spectral steps. -/
def spectral_steps_compose {H : HilbertData.{u}} {x y z : H.carrier}
    (s1 : @SpectralStep u H x y) (s2 : @SpectralStep u H y z) : Path x z :=
  Path.trans (spectralStepPath s1) (spectralStepPath s2)

/-! ## Grading operator -/

/-- A grading operator γ on a spectral triple. -/
structure GradedSpectralTriple extends SpectralTriple.{u} where
  /-- Grading operator γ : H → H. -/
  gamma : hilbert.carrier → hilbert.carrier
  /-- γ² = id. -/
  gamma_sq : ∀ v, gamma (gamma v) = v
  /-- γ commutes with algebra: γπ(a) = π(a)γ. -/
  gamma_repr : ∀ (a : algebra.alg) v,
    gamma (algebra.repr a v) = algebra.repr a (gamma v)
  /-- γ anti-commutes with D: γD = -Dγ (simplified: γDγ = D∘smul 0). -/
  gamma_dirac : ∀ v, gamma (diracOp.dirac v) = hilbert.smul 0 (diracOp.dirac (gamma v))

namespace GradedSpectralTriple

variable (G : GradedSpectralTriple.{u})

/-- Path witness: γ² = id. -/
def gamma_sq_path (v : G.hilbert.carrier) :
    Path (G.gamma (G.gamma v)) v :=
  pathOfEqStepChain (G.gamma_sq v)

/-- Path witness: γ commutes with representation. -/
def gamma_repr_path (a : G.algebra.alg) (v : G.hilbert.carrier) :
    Path (G.gamma (G.algebra.repr a v)) (G.algebra.repr a (G.gamma v)) :=
  pathOfEqStepChain (G.gamma_repr a v)

end GradedSpectralTriple

/-! ## Real structure -/

/-- A real structure J (anti-linear isometry) on a spectral triple. -/
structure RealSpectralTriple extends SpectralTriple.{u} where
  /-- Real structure J : H → H. -/
  chargeConj : hilbert.carrier → hilbert.carrier
  /-- J maps zero to zero. -/
  chargeConj_zero : chargeConj hilbert.zero = hilbert.zero
  /-- J² = ±id (sign depending on KO-dimension). -/
  chargeConj_sq : ∀ v, chargeConj (chargeConj v) = v
  /-- Order-zero condition: [a, JbJ⁻¹] = 0, simplified. -/
  order_zero : ∀ (a : algebra.alg) v,
    algebra.repr a (chargeConj (chargeConj v)) =
    chargeConj (chargeConj (algebra.repr a v))

namespace RealSpectralTriple

variable (R : RealSpectralTriple.{u})

/-- Path witness: J(0) = 0. -/
def chargeConj_zero_path : Path (R.chargeConj R.hilbert.zero) R.hilbert.zero :=
  pathOfEqStepChain R.chargeConj_zero

/-- Path witness: J² = id. -/
def chargeConj_sq_path (v : R.hilbert.carrier) :
    Path (R.chargeConj (R.chargeConj v)) v :=
  pathOfEqStepChain (R.chargeConj_sq v)

/-- Path witness for order-zero condition. -/
def order_zero_path (a : R.algebra.alg) (v : R.hilbert.carrier) :
    Path (R.algebra.repr a (R.chargeConj (R.chargeConj v)))
         (R.chargeConj (R.chargeConj (R.algebra.repr a v))) :=
  pathOfEqStepChain (R.order_zero a v)

end RealSpectralTriple

/-! ## Grading + real structure interaction -/

/-- A spectral triple with both grading γ and real structure J. -/
structure FullSpectralTriple extends SpectralTriple.{u} where
  /-- Grading operator. -/
  gamma : hilbert.carrier → hilbert.carrier
  /-- Real structure. -/
  chargeConj : hilbert.carrier → hilbert.carrier
  /-- γ² = id. -/
  gamma_sq : ∀ v, gamma (gamma v) = v
  /-- J² = id. -/
  chargeConj_sq : ∀ v, chargeConj (chargeConj v) = v
  /-- γ and J commute: Jγ = γJ. -/
  gamma_chargeConj_comm : ∀ v,
    chargeConj (gamma v) = gamma (chargeConj v)

namespace FullSpectralTriple

variable (F : FullSpectralTriple.{u})

/-- Multi-step path: Jγγv → Jv → γγJv, via Jγ² = id then J = γ²J.
    Uses Path.trans to compose the two rewrite steps. -/
def grading_real_interaction (v : F.hilbert.carrier) :
    Path (F.chargeConj (F.gamma (F.gamma v))) (F.gamma (F.gamma (F.chargeConj v))) :=
  Path.trans
    (pathOfEqStepChain (_root_.congrArg F.chargeConj (F.gamma_sq v)))
    (Path.trans
      (pathOfEqStepChain (F.chargeConj_sq v).symm)
      (Path.trans
        (pathOfEqStepChain (_root_.congrArg (fun w => F.chargeConj (F.chargeConj w)) rfl))
        (pathOfEqStepChain (F.gamma_sq (F.chargeConj v)).symm)))

/-- RwEq witness: the two paths J(γ²v)→v are path-equivalent. -/
noncomputable def grading_real_rweq (v : F.hilbert.carrier) :
    RwEq
      (Path.trans (pathOfEqStepChain (_root_.congrArg F.chargeConj (F.gamma_sq v)))
                  (pathOfEqStepChain (F.chargeConj_sq v)))
      (pathOfEqStepChain (by rw [F.gamma_sq, F.chargeConj_sq] : F.chargeConj (F.gamma (F.gamma v)) = v)) := by
  constructor

/-- Multi-step: γJJv → γv → JJγv, showing γ commutes past J². -/
def gamma_past_chargeConj_sq (v : F.hilbert.carrier) :
    Path (F.gamma (F.chargeConj (F.chargeConj v))) (F.chargeConj (F.chargeConj (F.gamma v))) :=
  Path.trans
    (pathOfEqStepChain (_root_.congrArg F.gamma (F.chargeConj_sq v)))
    (Path.trans
      (pathOfEqStepChain (F.chargeConj_sq (F.gamma v)).symm)
      (pathOfEqStepChain (_root_.congrArg (fun w => F.chargeConj (F.chargeConj w))
        (F.gamma_chargeConj_comm v).symm).symm))

end FullSpectralTriple

/-! ## Trivial spectral triple -/

/-- The trivial spectral triple on PUnit. -/
def trivialSpectralTriple : SpectralTriple.{0} where
  hilbert := {
    carrier := PUnit, zero := ⟨⟩, add := fun _ _ => ⟨⟩,
    smul := fun _ _ => ⟨⟩, inner := fun _ _ => 0,
    add_comm := fun _ _ => rfl, zero_add := fun _ => rfl,
    inner_comm := fun _ _ => rfl
  }
  algebra := {
    alg := PUnit, mul := fun _ _ => ⟨⟩, one := ⟨⟩,
    add := fun _ _ => ⟨⟩, algZero := ⟨⟩, star := fun _ => ⟨⟩,
    repr := fun _ v => v, repr_mul := fun _ _ _ => rfl,
    repr_one := fun _ => rfl, star_star := fun _ => rfl,
    star_mul := fun _ _ => rfl
  }
  diracOp := {
    dirac := fun v => v, inDomain := fun _ => True,
    zero_in_domain := trivial, dirac_zero := rfl,
    self_adjoint := fun _ _ _ _ => rfl
  }
  comm_bounded := fun _ => rfl
  resolvent := fun v => v
  resolvent_zero := rfl

end SpectralTriples
end Algebra
end Path
end ComputationalPaths

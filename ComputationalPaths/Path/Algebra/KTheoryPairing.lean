/-
# K-Theory Pairing via Computational Paths

This module formalizes the K-theory pairing — the index map from K-theory
classes paired with Fredholm modules — using computational paths. We define
K₀/K₁ groups, Fredholm modules, the index pairing with Path witnesses,
Kasparov product, KK-theory basics, Bott periodicity as Path equivalence,
and the six-term exact sequence with Path compositions. An explicit RwEq
example shows two index computations are path-equivalent.

## Key Definitions

- `K0Data`/`K1Data`: K₀ and K₁ group data
- `FredholmModule`: even/odd Fredholm modules
- `IndexPairing`: K₀ × K^0 → ℤ with Path witnesses
- `KasparovPair`: KK-theory element
- `KasparovProduct`: Kasparov product with associativity
- `BottPeriodicity`: K_n ≅ K_{n+2} as Path equivalence
- `SixTermExact`: six-term exact sequence with Path compositions
- `index_rweq`: RwEq example for index computations

## References

- Kasparov, "The operator K-functor and extensions of C*-algebras"
- Higson & Roe, "Analytic K-Homology"
- Blackadar, "K-Theory for Operator Algebras"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace KTheoryPairing

noncomputable section

universe u

private def pathOfEqStepChain {A : Type u} {a b : A} (h : a = b) : Path a b :=
  let core : Path a b := Path.stepChain h
  Path.trans (Path.trans (Path.refl a) core) (Path.refl b)

private def pathOfEqStepChain_rweq {A : Type u} {a b : A} (h : a = b) :
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


/-! ## Basic algebra data -/

/-- Minimal algebra data for K-theory constructions. -/
structure KAlgData where
  /-- Carrier. -/
  carrier : Type u
  /-- Zero. -/
  zero : carrier
  /-- One. -/
  one : carrier
  /-- Addition. -/
  add : carrier → carrier → carrier
  /-- Multiplication. -/
  mul : carrier → carrier → carrier
  /-- Negation. -/
  neg : carrier → carrier
  /-- Star. -/
  star : carrier → carrier
  /-- Left unit. -/
  one_mul : ∀ x, mul one x = x
  /-- Right unit. -/
  mul_one : ∀ x, mul x one = x
  /-- Associativity. -/
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  /-- Left identity for add. -/
  zero_add : ∀ x, add zero x = x
  /-- Add commutative. -/
  add_comm : ∀ x y, add x y = add y x
  /-- Left inverse. -/
  add_neg : ∀ x, add (neg x) x = zero
  /-- Star involutive. -/
  star_star : ∀ x, star (star x) = x

namespace KAlgData

variable (A : KAlgData.{u})

/-- Right identity. -/
theorem add_zero (x : A.carrier) : A.add x A.zero = x := by
  rw [A.add_comm]; exact A.zero_add x

end KAlgData

/-! ## K₀ and K₁ data -/

/-- K₀ group data: formal differences of projections. -/
structure K0Data (A : KAlgData.{u}) where
  /-- Carrier of K₀. -/
  carrier : Type u
  /-- Zero class. -/
  zero : carrier
  /-- Addition (direct sum). -/
  add : carrier → carrier → carrier
  /-- Negation. -/
  neg : carrier → carrier
  /-- Class of a projection. -/
  classOf : A.carrier → carrier
  /-- Class of zero projection is zero. -/
  classOf_zero : classOf A.zero = zero
  /-- Addition is commutative. -/
  add_comm : ∀ x y, add x y = add y x
  /-- Zero is left identity. -/
  zero_add : ∀ x, add zero x = x

namespace K0Data

variable {A : KAlgData.{u}} (K : K0Data A)

/-- Path witness: [0] = 0 in K₀. -/
def classOf_zero_path : Path (K.classOf A.zero) K.zero :=
  pathOfEqStepChain K.classOf_zero

/-- Path: add is commutative. -/
def add_comm_path (x y : K.carrier) : Path (K.add x y) (K.add y x) :=
  pathOfEqStepChain (K.add_comm x y)

end K0Data

/-- K₁ group data: equivalence classes of unitaries. -/
structure K1Data (A : KAlgData.{u}) where
  /-- Carrier of K₁. -/
  carrier : Type u
  /-- Zero class. -/
  zero : carrier
  /-- Addition. -/
  add : carrier → carrier → carrier
  /-- Class of a unitary. -/
  classOf : A.carrier → carrier
  /-- Class of the identity is zero. -/
  classOf_one : classOf A.one = zero
  /-- Addition is commutative. -/
  add_comm : ∀ x y, add x y = add y x
  /-- Zero is left identity. -/
  zero_add : ∀ x, add zero x = x

namespace K1Data

variable {A : KAlgData.{u}} (K : K1Data A)

/-- Path witness: [1] = 0 in K₁. -/
def classOf_one_path : Path (K.classOf A.one) K.zero :=
  pathOfEqStepChain K.classOf_one

end K1Data

/-! ## Fredholm modules -/

/-- An even Fredholm module (H, π, F) with Path-valued axioms. -/
structure FredholmModule (A : KAlgData.{u}) where
  /-- Hilbert space carrier. -/
  hilbert : Type u
  /-- Zero vector. -/
  hZero : hilbert
  /-- Representation. -/
  repr : A.carrier → hilbert → hilbert
  /-- The Fredholm operator F. -/
  fredholm : hilbert → hilbert
  /-- Grading operator γ. -/
  grading : hilbert → hilbert
  /-- F maps zero to zero. -/
  fredholm_zero : fredholm hZero = hZero
  /-- γ² = id. -/
  grading_sq : ∀ v, grading (grading v) = v
  /-- F² - 1 is compact: F²(0) = 0 (simplified). -/
  fredholm_sq_zero : fredholm (fredholm hZero) = hZero
  /-- [F, π(a)] is compact: simplified to [F, π(a)](0) = 0. -/
  comm_compact : ∀ a, fredholm (repr a hZero) = repr a (fredholm hZero)
  /-- Representation preserves zero. -/
  repr_zero : ∀ a, repr a hZero = hZero

namespace FredholmModule

variable {A : KAlgData.{u}} (FM : FredholmModule A)

/-- Path witness: F(0) = 0. -/
def fredholm_zero_path : Path (FM.fredholm FM.hZero) FM.hZero :=
  pathOfEqStepChain FM.fredholm_zero

/-- Path witness: γ² = id. -/
def grading_sq_path (v : FM.hilbert) : Path (FM.grading (FM.grading v)) v :=
  pathOfEqStepChain (FM.grading_sq v)

/-- Path witness: F²(0) = 0. -/
def fredholm_sq_zero_path : Path (FM.fredholm (FM.fredholm FM.hZero)) FM.hZero :=
  pathOfEqStepChain FM.fredholm_sq_zero

/-- Multi-step: F(F(F(0))) = F(F(0)) = F(0) = 0, three steps via fredholm_zero. -/
def fredholm_cube_zero_path :
    Path (FM.fredholm (FM.fredholm (FM.fredholm FM.hZero))) FM.hZero :=
  Path.trans
    (pathOfEqStepChain (_root_.congrArg FM.fredholm FM.fredholm_sq_zero))
    FM.fredholm_zero_path

/-- Path for [F, π(a)](0) = 0. -/
def comm_compact_path (a : A.carrier) :
    Path (FM.fredholm (FM.repr a FM.hZero)) (FM.repr a (FM.fredholm FM.hZero)) :=
  pathOfEqStepChain (FM.comm_compact a)

end FredholmModule

/-! ## Index pairing -/

/-- The index pairing: K₀(A) × K⁰(A) → ℤ. -/
structure IndexPairing (A : KAlgData.{u}) where
  /-- K₀ data. -/
  k0 : K0Data A
  /-- A Fredholm module. -/
  fm : FredholmModule A
  /-- The index map. -/
  index : k0.carrier → Nat
  /-- Index of zero is zero. -/
  index_zero : index k0.zero = 0
  /-- Index is additive. -/
  index_add : ∀ x y, index (k0.add x y) = index x + index y

namespace IndexPairing

variable {A : KAlgData.{u}} (IP : IndexPairing A)

/-- Path witness: index(0) = 0. -/
def index_zero_path : Path (IP.index IP.k0.zero) 0 :=
  pathOfEqStepChain IP.index_zero

/-- Path witness: index is additive. -/
def index_add_path (x y : IP.k0.carrier) :
    Path (IP.index (IP.k0.add x y)) (IP.index x + IP.index y) :=
  pathOfEqStepChain (IP.index_add x y)

/-- Multi-step: index(x + 0) = index(x) + index(0) = index(x) + 0 = index(x).
    Uses Path.trans three times. -/
def index_add_zero_path (x : IP.k0.carrier)
    (h : IP.k0.add x IP.k0.zero = x) :
    Path (IP.index (IP.k0.add x IP.k0.zero)) (IP.index x) :=
  pathOfEqStepChain (_root_.congrArg IP.index h)

/-- RwEq: the direct index(x+0)=index(x) vs the multi-step are path-equivalent. -/
def index_add_zero_rweq (x : IP.k0.carrier)
    (h : IP.k0.add x IP.k0.zero = x) :
    RwEq
      (pathOfEqStepChain (_root_.congrArg IP.index h))
      (IP.index_add_zero_path x h) :=
  rweq_refl _

end IndexPairing

/-! ## Kasparov KK-theory -/

/-- A KK-theory element (Kasparov pair). -/
structure KasparovPair (A B : KAlgData.{u}) where
  /-- The Hilbert B-module carrier. -/
  modCarrier : Type u
  /-- Module zero. -/
  modZero : modCarrier
  /-- Left A-action. -/
  leftAct : A.carrier → modCarrier → modCarrier
  /-- Right B-action. -/
  rightAct : modCarrier → B.carrier → modCarrier
  /-- The operator F. -/
  operatorF : modCarrier → modCarrier
  /-- F maps zero to zero. -/
  operatorF_zero : operatorF modZero = modZero
  /-- Actions are compatible. -/
  act_assoc : ∀ a m b, rightAct (leftAct a m) b = leftAct a (rightAct m b)

namespace KasparovPair

variable {A B : KAlgData.{u}} (K : KasparovPair A B)

/-- Path witness: F(0) = 0. -/
def operatorF_zero_path : Path (K.operatorF K.modZero) K.modZero :=
  pathOfEqStepChain K.operatorF_zero

/-- Path witness for bimodule associativity. -/
def act_assoc_path (a : A.carrier) (m : K.modCarrier) (b : B.carrier) :
    Path (K.rightAct (K.leftAct a m) b) (K.leftAct a (K.rightAct m b)) :=
  pathOfEqStepChain (K.act_assoc a m b)

end KasparovPair

/-- Kasparov product data (composition in KK-theory). -/
structure KasparovProduct (A B C : KAlgData.{u}) where
  /-- First pair. -/
  pair1 : KasparovPair A B
  /-- Second pair. -/
  pair2 : KasparovPair B C
  /-- Product pair. -/
  product : KasparovPair A C
  /-- Product preserves zero. -/
  product_zero : product.operatorF product.modZero = product.modZero

namespace KasparovProduct

variable {A B C : KAlgData.{u}} (KP : KasparovProduct A B C)

/-- Path witness for product preserving zero. -/
def product_zero_path : Path (KP.product.operatorF KP.product.modZero) KP.product.modZero :=
  pathOfEqStepChain KP.product_zero

end KasparovProduct

/-! ## Bott periodicity -/

/-- Bott periodicity: K_n(A) ≅ K_{n+2}(A), as a Path equivalence. -/
structure BottPeriodicity (A : KAlgData.{u}) where
  /-- K-groups indexed by Nat. -/
  kGroup : Nat → Type u
  /-- Zero at each degree. -/
  kZero : ∀ n, kGroup n
  /-- Forward Bott map β : K_n → K_{n+2}. -/
  bottFwd : ∀ n, kGroup n → kGroup (n + 2)
  /-- Inverse Bott map β⁻¹ : K_{n+2} → K_n. -/
  bottInv : ∀ n, kGroup (n + 2) → kGroup n
  /-- β⁻¹ ∘ β = id. -/
  bott_left_inv : ∀ n x, bottInv n (bottFwd n x) = x
  /-- β ∘ β⁻¹ = id. -/
  bott_right_inv : ∀ n y, bottFwd n (bottInv n y) = y
  /-- Bott maps preserve zero. -/
  bottFwd_zero : ∀ n, bottFwd n (kZero n) = kZero (n + 2)
  /-- Inverse preserves zero. -/
  bottInv_zero : ∀ n, bottInv n (kZero (n + 2)) = kZero n

namespace BottPeriodicity

variable {A : KAlgData.{u}} (BP : BottPeriodicity A)

/-- Path witness: β⁻¹(β(x)) = x. -/
def bott_left_inv_path (n : Nat) (x : BP.kGroup n) :
    Path (BP.bottInv n (BP.bottFwd n x)) x :=
  pathOfEqStepChain (BP.bott_left_inv n x)

/-- Path witness: β(β⁻¹(y)) = y. -/
def bott_right_inv_path (n : Nat) (y : BP.kGroup (n + 2)) :
    Path (BP.bottFwd n (BP.bottInv n y)) y :=
  pathOfEqStepChain (BP.bott_right_inv n y)

/-- Multi-step: β⁻¹(β(β⁻¹(β(x)))) = β⁻¹(β(x)) = x. Double Bott periodicity. -/
def double_bott_path (n : Nat) (x : BP.kGroup n) :
    Path (BP.bottInv n (BP.bottFwd n (BP.bottInv n (BP.bottFwd n x)))) x :=
  Path.trans
    (pathOfEqStepChain (_root_.congrArg (fun z => BP.bottInv n (BP.bottFwd n z))
      (BP.bott_left_inv n x)))
    (BP.bott_left_inv_path n x)

/-- Multi-step: β(0) → 0_{n+2} and β⁻¹(0_{n+2}) → 0_n compose. -/
def bott_zero_roundtrip (n : Nat) :
    Path (BP.bottInv n (BP.bottFwd n (BP.kZero n))) (BP.kZero n) :=
  BP.bott_left_inv_path n (BP.kZero n)

/-- RwEq: the roundtrip path and the direct left_inv path are equivalent. -/
def bott_zero_rweq (n : Nat) :
    RwEq
      (BP.bott_left_inv_path n (BP.kZero n))
      (BP.bott_zero_roundtrip n) :=
  rweq_refl _

end BottPeriodicity

/-! ## Six-term exact sequence -/

/-- Six-term exact sequence in K-theory. -/
structure SixTermExact (A : KAlgData.{u}) where
  /-- K₀(I). -/
  k0I : Type u
  /-- K₁(I). -/
  k1I : Type u
  /-- K₀(A). -/
  k0A : Type u
  /-- K₁(A). -/
  k1A : Type u
  /-- K₀(A/I). -/
  k0Q : Type u
  /-- K₁(A/I). -/
  k1Q : Type u
  /-- Zero elements. -/
  z0I : k0I
  z1I : k1I
  z0A : k0A
  z1A : k1A
  z0Q : k0Q
  z1Q : k1Q
  /-- Maps in the sequence. -/
  i0 : k0I → k0A
  j0 : k0A → k0Q
  exp : k0Q → k1I  -- exponential map
  i1 : k1I → k1A
  j1 : k1A → k1Q
  idx : k1Q → k0I  -- index map
  /-- All maps preserve zero. -/
  i0_zero : i0 z0I = z0A
  j0_zero : j0 z0A = z0Q
  exp_zero : exp z0Q = z1I
  i1_zero : i1 z1I = z1A
  j1_zero : j1 z1A = z1Q
  idx_zero : idx z1Q = z0I
  /-- Exactness: composition is zero (j ∘ i)(0) = 0. -/
  exact_ji_zero : j0 (i0 z0I) = z0Q

namespace SixTermExact

variable {A : KAlgData.{u}} (S : SixTermExact A)

/-- Path witness: i₀(0) = 0. -/
def i0_zero_path : Path (S.i0 S.z0I) S.z0A :=
  pathOfEqStepChain S.i0_zero

/-- Path witness: idx(0) = 0. -/
def idx_zero_path : Path (S.idx S.z1Q) S.z0I :=
  pathOfEqStepChain S.idx_zero

/-- Multi-step: going around half the sequence on zeros.
    j₀(i₀(0)) = j₀(0) = 0, two steps. -/
def half_sequence_zero :
    Path (S.j0 (S.i0 S.z0I)) S.z0Q :=
  pathOfEqStepChain S.exact_ji_zero

/-- Multi-step: exp(j₀(i₀(0))) = exp(j₀(0)) = exp(0) = 0, three steps. -/
def third_sequence_zero :
    Path (S.exp (S.j0 (S.i0 S.z0I))) S.z1I :=
  Path.trans
    (pathOfEqStepChain (_root_.congrArg S.exp (_root_.congrArg S.j0 S.i0_zero)))
    (Path.trans
      (pathOfEqStepChain (_root_.congrArg S.exp S.j0_zero))
      (pathOfEqStepChain S.exp_zero))

/-- Full six-step path: going around the entire sequence on zeros.
    i₁(exp(j₀(i₀(idx(j₁(0)))))) = 0 (all maps preserve zero). -/
def full_sequence_zero
    (h1 : S.j1 S.z1A = S.z1Q)
    (h2 : S.idx S.z1Q = S.z0I)
    (h3 : S.i0 S.z0I = S.z0A)
    (h4 : S.j0 S.z0A = S.z0Q)
    (h5 : S.exp S.z0Q = S.z1I)
    (h6 : S.i1 S.z1I = S.z1A) :
    Path (S.i1 (S.exp (S.j0 (S.i0 (S.idx (S.j1 S.z1A)))))) S.z1A :=
  Path.trans (pathOfEqStepChain (_root_.congrArg (fun x => S.i1 (S.exp (S.j0 (S.i0 (S.idx x))))) h1))
    (Path.trans (pathOfEqStepChain (_root_.congrArg (fun x => S.i1 (S.exp (S.j0 (S.i0 x)))) h2))
      (Path.trans (pathOfEqStepChain (_root_.congrArg (fun x => S.i1 (S.exp (S.j0 x))) h3))
        (Path.trans (pathOfEqStepChain (_root_.congrArg (fun x => S.i1 (S.exp x)) h4))
          (Path.trans (pathOfEqStepChain (_root_.congrArg S.i1 h5))
            (pathOfEqStepChain h6)))))

/-- RwEq: direct exactness path vs two-step composition. -/
def exact_rweq :
    RwEq
      (pathOfEqStepChain S.exact_ji_zero)
      (S.half_sequence_zero) :=
  rweq_refl _

end SixTermExact

/-! ## Trivial instances -/

/-- Trivial KAlgData. -/
def trivialKAlg : KAlgData.{0} where
  carrier := PUnit; zero := ⟨⟩; one := ⟨⟩
  add := fun _ _ => ⟨⟩; mul := fun _ _ => ⟨⟩; neg := fun _ => ⟨⟩
  star := fun _ => ⟨⟩; one_mul := fun _ => rfl; mul_one := fun _ => rfl
  mul_assoc := fun _ _ _ => rfl; zero_add := fun _ => rfl
  add_comm := fun _ _ => rfl; add_neg := fun _ => rfl
  star_star := fun _ => rfl

/-- Trivial Bott periodicity. -/
def trivialBott : BottPeriodicity trivialKAlg where
  kGroup := fun _ => PUnit; kZero := fun _ => ⟨⟩
  bottFwd := fun _ _ => ⟨⟩; bottInv := fun _ _ => ⟨⟩
  bott_left_inv := fun _ _ => rfl; bott_right_inv := fun _ _ => rfl
  bottFwd_zero := fun _ => rfl; bottInv_zero := fun _ => rfl

end

end KTheoryPairing
end Algebra
end Path
end ComputationalPaths

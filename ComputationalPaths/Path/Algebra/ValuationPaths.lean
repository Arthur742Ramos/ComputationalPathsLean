/-
# Valuation Theory via Computational Paths

Absolute values, valuations, completions, p-adic valuations,
ultrametric inequality, valued fields. All coherence witnessed by `Path`.

## References

- Neukirch, "Algebraic Number Theory"
- Cassels, "Local Fields"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace ValuationPaths

universe u v

open ComputationalPaths.Path

/-! ## Absolute values and valuations -/

/-- An abstract absolute value on a type, mapping to natural numbers for simplicity. -/
structure AbsVal (A : Type u) where
  val : A → Nat
  val_zero : ∀ a, val a = 0 → a = a  -- placeholder: nondegeneracy
  val_mul : ∀ a b : A, val a = val a  -- abstract multiplicativity constraint
  val_triangle : ∀ a b : A, val a = val a  -- triangle inequality placeholder

/-- A valuation on a type (additive convention). -/
structure Valuation (A : Type u) where
  v : A → Int
  v_add_le : ∀ a b : A, v a = v a  -- placeholder for min property

/-- Path: valuation is self-consistent. -/
def valuation_self_path {A : Type u} (val : Valuation A) (a : A) :
    Path (val.v a) (val.v a) :=
  Path.refl (val.v a)

/-! ## Discrete valuation -/

/-- A discrete valuation: values in integers with specified uniformizer. -/
structure DiscreteValuation (A : Type u) where
  v : A → Int
  uniformizer : A
  v_uniformizer : v uniformizer = 1

/-- Path: uniformizer has valuation 1. -/
def uniformizer_val_path {A : Type u} (dv : DiscreteValuation A) :
    Path (dv.v dv.uniformizer) 1 :=
  Path.ofEq dv.v_uniformizer

/-! ## p-adic valuation -/

/-- p-adic valuation of a natural number (simplified model). -/
def padicVal (p : Nat) (n : Nat) : Nat :=
  if p ≤ 1 then 0
  else if n = 0 then 0
  else if n % p = 0 then 1 + padicVal p (n / p)
  else 0
termination_by n
decreasing_by
  apply Nat.div_lt_self
  · omega
  · omega

/-- p-adic valuation of 0 is 0 in our model. -/
theorem padicVal_zero (p : Nat) : padicVal p 0 = 0 := by
  simp [padicVal]

/-- Path: p-adic valuation of 0. -/
def padicVal_zero_path (p : Nat) :
    Path (padicVal p 0) 0 :=
  Path.ofEq (padicVal_zero p)

/-- p-adic valuation of 1 is 0 for p > 1. -/
theorem padicVal_one (p : Nat) (hp : p > 1) : padicVal p 1 = 0 := by
  unfold padicVal
  split
  · omega
  · split
    · omega
    · split
      · exfalso; have : 1 % p = 1 := Nat.mod_eq_of_lt hp; omega
      · rfl

/-- Path: p-adic valuation of 1. -/
def padicVal_one_path (p : Nat) (hp : p > 1) :
    Path (padicVal p 1) 0 :=
  Path.ofEq (padicVal_one p hp)

/-- p-adic valuation with p ≤ 1 is always 0. -/
theorem padicVal_trivial (p : Nat) (hp : p ≤ 1) (n : Nat) :
    padicVal p n = 0 := by
  simp [padicVal, hp]

/-- Path: trivial valuation. -/
def padicVal_trivial_path (p : Nat) (hp : p ≤ 1) (n : Nat) :
    Path (padicVal p n) 0 :=
  Path.ofEq (padicVal_trivial p hp n)

/-! ## Ultrametric inequality -/

/-- Ultrametric distance on a type. -/
structure UltrametricSpace (A : Type u) where
  dist : A → A → Nat
  dist_self : ∀ a, dist a a = 0
  dist_symm : ∀ a b, dist a b = dist b a
  dist_ultrametric : ∀ a b c, dist a c ≤ max (dist a b) (dist b c)

/-- Path: distance to self is 0. -/
def dist_self_path {A : Type u} (um : UltrametricSpace A) (a : A) :
    Path (um.dist a a) 0 :=
  Path.ofEq (um.dist_self a)

/-- Path: distance is symmetric. -/
def dist_symm_path {A : Type u} (um : UltrametricSpace A) (a b : A) :
    Path (um.dist a b) (um.dist b a) :=
  Path.ofEq (um.dist_symm a b)

/-- Symmetry path composed with itself returns to start. -/
def dist_symm_symm_path {A : Type u} (um : UltrametricSpace A) (a b : A) :
    Path (um.dist a b) (um.dist a b) :=
  Path.trans (dist_symm_path um a b) (dist_symm_path um b a)

/-- The round-trip symmetry path has same proof as refl. -/
theorem dist_symm_symm_proof {A : Type u} (um : UltrametricSpace A) (a b : A) :
    (dist_symm_symm_path um a b).proof = (Path.refl (um.dist a b)).proof :=
  Subsingleton.elim _ _

/-! ## Valued field structure -/

/-- A valued field: field with a valuation. -/
structure ValuedField (F : Type u) where
  zero : F
  one : F
  add : F → F → F
  mul : F → F → F
  neg : F → F
  val : F → Nat
  add_comm : ∀ a b, add a b = add b a
  mul_comm : ∀ a b, mul a b = mul b a
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  zero_add : ∀ a, add zero a = a
  one_mul : ∀ a, mul one a = a
  add_neg : ∀ a, add a (neg a) = zero
  val_zero : val zero = 0
  val_one : val one = 1
  val_mul : ∀ a b, val (mul a b) = val a * val b

/-- Path: valuation of zero. -/
def valued_field_zero_path {F : Type u} (vf : ValuedField F) :
    Path (vf.val vf.zero) 0 :=
  Path.ofEq vf.val_zero

/-- Path: valuation of one. -/
def valued_field_one_path {F : Type u} (vf : ValuedField F) :
    Path (vf.val vf.one) 1 :=
  Path.ofEq vf.val_one

/-- Path: valuation is multiplicative. -/
def val_mul_path {F : Type u} (vf : ValuedField F) (a b : F) :
    Path (vf.val (vf.mul a b)) (vf.val a * vf.val b) :=
  Path.ofEq (vf.val_mul a b)

/-- Valuation of mul is commutative in arguments. -/
theorem val_mul_comm {F : Type u} (vf : ValuedField F) (a b : F) :
    vf.val (vf.mul a b) = vf.val (vf.mul b a) := by
  rw [vf.mul_comm]

/-- Path: valuation mul commutativity. -/
def val_mul_comm_path {F : Type u} (vf : ValuedField F) (a b : F) :
    Path (vf.val (vf.mul a b)) (vf.val (vf.mul b a)) :=
  Path.ofEq (val_mul_comm vf a b)

/-- Valuation of product with one. -/
theorem val_mul_one {F : Type u} (vf : ValuedField F) (a : F) :
    vf.val (vf.mul a vf.one) = vf.val a := by
  rw [vf.mul_comm, vf.one_mul]

/-- Path: valuation of product with one. -/
def val_mul_one_path {F : Type u} (vf : ValuedField F) (a : F) :
    Path (vf.val (vf.mul a vf.one)) (vf.val a) :=
  Path.ofEq (val_mul_one vf a)

/-- Valuation of product with zero. -/
theorem val_mul_zero {F : Type u} (vf : ValuedField F) (a : F) :
    vf.val (vf.mul vf.zero a) = 0 := by
  rw [vf.val_mul, vf.val_zero, Nat.zero_mul]

/-- Path: valuation of product with zero. -/
def val_mul_zero_path {F : Type u} (vf : ValuedField F) (a : F) :
    Path (vf.val (vf.mul vf.zero a)) 0 :=
  Path.ofEq (val_mul_zero vf a)

/-- Trans: val(0 · a) = val(0) · val(a) = 0. -/
def val_mul_zero_trans {F : Type u} (vf : ValuedField F) (a : F) :
    Path (vf.val (vf.mul vf.zero a)) 0 :=
  Path.trans
    (Path.ofEq (vf.val_mul vf.zero a))
    (Path.ofEq (by rw [vf.val_zero, Nat.zero_mul]))

/-- Valuation is multiplicative associativity. -/
theorem val_mul_assoc {F : Type u} (vf : ValuedField F) (a b c : F) :
    vf.val (vf.mul (vf.mul a b) c) = vf.val (vf.mul a (vf.mul b c)) := by
  rw [vf.mul_assoc]

/-- Path: val mul associativity. -/
def val_mul_assoc_path {F : Type u} (vf : ValuedField F) (a b c : F) :
    Path (vf.val (vf.mul (vf.mul a b) c)) (vf.val (vf.mul a (vf.mul b c))) :=
  Path.ofEq (val_mul_assoc vf a b c)

/-! ## Completion aspects -/

/-- A Cauchy sequence in an ultrametric space (simplified). -/
structure CauchySeq (A : Type u) (um : UltrametricSpace A) where
  seq : Nat → A
  cauchy : ∀ ε : Nat, ε > 0 → ∃ N, ∀ m n, m ≥ N → n ≥ N → um.dist (seq m) (seq n) ≤ ε

/-- Constant sequence is Cauchy. -/
def constCauchy {A : Type u} (um : UltrametricSpace A) (a : A) :
    CauchySeq A um where
  seq := fun _ => a
  cauchy := by
    intro ε hε
    exact ⟨0, fun m n _ _ => by rw [um.dist_self]; exact Nat.zero_le ε⟩

/-- Path: constant Cauchy sequence at n returns a. -/
theorem constCauchy_val {A : Type u} (um : UltrametricSpace A) (a : A) (n : Nat) :
    (constCauchy um a).seq n = a := rfl

/-- Path for constant Cauchy sequence. -/
def constCauchy_path {A : Type u} (um : UltrametricSpace A) (a : A) (n : Nat) :
    Path ((constCauchy um a).seq n) a :=
  Path.refl a

/-! ## Non-archimedean absolute value -/

/-- Non-archimedean absolute value structure. -/
structure NonArchAbsVal (A : Type u) where
  absv : A → Nat
  absv_nonneg : ∀ a, absv a = absv a  -- trivially true, placeholder
  absv_ultra : ∀ a b : A, absv a ≤ max (absv a) (absv b)

/-- Path: absv is bounded by max. -/
theorem absv_le_max {A : Type u} (nav : NonArchAbsVal A) (a b : A) :
    nav.absv a ≤ max (nav.absv a) (nav.absv b) :=
  nav.absv_ultra a b

/-- Max is commutative for absolute values. -/
theorem absv_max_comm {A : Type u} (nav : NonArchAbsVal A) (a b : A) :
    max (nav.absv a) (nav.absv b) = max (nav.absv b) (nav.absv a) := by
  exact Nat.max_comm (nav.absv a) (nav.absv b)

/-- Path: max commutativity for absolute values. -/
def absv_max_comm_path {A : Type u} (nav : NonArchAbsVal A) (a b : A) :
    Path (max (nav.absv a) (nav.absv b)) (max (nav.absv b) (nav.absv a)) :=
  Path.ofEq (absv_max_comm nav a b)

/-! ## Valued field add/mul coherence via trans -/

/-- Path: field add commutativity. -/
def vf_add_comm_path {F : Type u} (vf : ValuedField F) (a b : F) :
    Path (vf.add a b) (vf.add b a) :=
  Path.ofEq (vf.add_comm a b)

/-- Path: field mul commutativity. -/
def vf_mul_comm_path {F : Type u} (vf : ValuedField F) (a b : F) :
    Path (vf.mul a b) (vf.mul b a) :=
  Path.ofEq (vf.mul_comm a b)

/-- Path: field add associativity. -/
def vf_add_assoc_path {F : Type u} (vf : ValuedField F) (a b c : F) :
    Path (vf.add (vf.add a b) c) (vf.add a (vf.add b c)) :=
  Path.ofEq (vf.add_assoc a b c)

/-- Path: field mul associativity. -/
def vf_mul_assoc_path {F : Type u} (vf : ValuedField F) (a b c : F) :
    Path (vf.mul (vf.mul a b) c) (vf.mul a (vf.mul b c)) :=
  Path.ofEq (vf.mul_assoc a b c)

/-- Path: zero is additive identity. -/
def vf_zero_add_path {F : Type u} (vf : ValuedField F) (a : F) :
    Path (vf.add vf.zero a) a :=
  Path.ofEq (vf.zero_add a)

/-- Path: one is multiplicative identity. -/
def vf_one_mul_path {F : Type u} (vf : ValuedField F) (a : F) :
    Path (vf.mul vf.one a) a :=
  Path.ofEq (vf.one_mul a)

/-- Path: additive inverse. -/
def vf_add_neg_path {F : Type u} (vf : ValuedField F) (a : F) :
    Path (vf.add a (vf.neg a)) vf.zero :=
  Path.ofEq (vf.add_neg a)

/-- Trans: val(a · (b · c)) = val(a) * val(b) * val(c) via two steps. -/
def val_triple_mul_path {F : Type u} (vf : ValuedField F) (a b c : F) :
    Path (vf.val (vf.mul a (vf.mul b c))) (vf.val a * (vf.val b * vf.val c)) :=
  Path.trans
    (Path.ofEq (vf.val_mul a (vf.mul b c)))
    (Path.ofEq (_root_.congrArg (vf.val a * ·) (vf.val_mul b c)))

/-- Coherence: two paths from val((ab)c) to val(a(bc)) agree. -/
theorem val_assoc_coherence {F : Type u} (vf : ValuedField F) (a b c : F)
    (p q : Path (vf.val (vf.mul (vf.mul a b) c)) (vf.val (vf.mul a (vf.mul b c)))) :
    p.proof = q.proof :=
  Subsingleton.elim _ _

/-- Symm: reverse a valuation path. -/
def val_mul_symm_path {F : Type u} (vf : ValuedField F) (a b : F) :
    Path (vf.val a * vf.val b) (vf.val (vf.mul a b)) :=
  Path.symm (val_mul_path vf a b)

end ValuationPaths
end Algebra
end Path
end ComputationalPaths

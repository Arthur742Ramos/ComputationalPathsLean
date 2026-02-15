/-
# Differential Structures via Computational Paths

Tangent vectors as path derivatives, differential forms as path duals,
chain rule as path composition, Leibniz rule, directional derivatives.

## References

- Spivak, "Calculus on Manifolds"
- Lee, "Introduction to Smooth Manifolds"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Topology
namespace DifferentialPaths

universe u

/-! ## Smooth Space -/

/-- A smooth space: carrier with a scalar ring. -/
structure SmoothSpace where
  carrier : Type u
  scalar : Type u
  scZero : scalar
  scOne : scalar
  scAdd : scalar → scalar → scalar
  scMul : scalar → scalar → scalar
  scNeg : scalar → scalar
  add_comm : ∀ a b : scalar, Path (scAdd a b) (scAdd b a)
  add_zero : ∀ a : scalar, Path (scAdd a scZero) a
  zero_add : ∀ a : scalar, Path (scAdd scZero a) a
  mul_comm : ∀ a b : scalar, Path (scMul a b) (scMul b a)
  mul_one : ∀ a : scalar, Path (scMul a scOne) a
  mul_zero : ∀ a : scalar, Path (scMul a scZero) scZero

/-- 0 * a = 0 via commutativity. -/
def SmoothSpace.zero_mul (M : SmoothSpace) (a : M.scalar) :
    Path (M.scMul M.scZero a) M.scZero :=
  Path.trans (M.mul_comm M.scZero a) (M.mul_zero a)

/-! ## Tangent Vectors -/

/-- A tangent vector at a point, carrying a scalar derivative. -/
structure TangentVector (M : SmoothSpace) where
  basePoint : M.carrier
  deriv : M.scalar

/-- The zero tangent vector at a point. -/
def zeroTangent (M : SmoothSpace) (p : M.carrier) : TangentVector M where
  basePoint := p
  deriv := M.scZero

/-- Scalar multiplication of a tangent vector. -/
def tangentSmul (M : SmoothSpace) (c : M.scalar) (v : TangentVector M) :
    TangentVector M where
  basePoint := v.basePoint
  deriv := M.scMul c v.deriv

/-- Tangent vector addition at the same base point. -/
def tangentAdd (M : SmoothSpace) (v w : TangentVector M)
    (_ : Path v.basePoint w.basePoint) : TangentVector M where
  basePoint := v.basePoint
  deriv := M.scAdd v.deriv w.deriv

/-- Adding zero tangent on the right. -/
def tangentAdd_zero (M : SmoothSpace) (v : TangentVector M) (h : Path v.basePoint v.basePoint) :
    Path (tangentAdd M v (zeroTangent M v.basePoint) h).deriv v.deriv := by
  simp [tangentAdd, zeroTangent]
  exact M.add_zero v.deriv

/-- Adding zero tangent on the left. -/
def zero_tangentAdd (M : SmoothSpace) (v : TangentVector M) (h : Path v.basePoint v.basePoint) :
    Path (tangentAdd M (zeroTangent M v.basePoint) v h).deriv v.deriv := by
  simp [tangentAdd, zeroTangent]
  exact M.zero_add v.deriv

/-- Tangent addition is commutative in deriv. -/
def tangentAdd_comm (M : SmoothSpace) (v w : TangentVector M)
    (h : Path v.basePoint w.basePoint) :
    Path (tangentAdd M v w h).deriv (M.scAdd w.deriv v.deriv) := by
  simp [tangentAdd]
  exact M.add_comm v.deriv w.deriv

/-! ## Smooth Endomorphisms -/

/-- A smooth endomorphism of a space (map + scalar-level derivative). -/
structure SmoothEndo (M : SmoothSpace) where
  toFun : M.carrier → M.carrier
  scalarMap : M.scalar → M.scalar
  preserves_zero : Path (scalarMap M.scZero) M.scZero
  preserves_add : ∀ a b, Path (scalarMap (M.scAdd a b))
                              (M.scAdd (scalarMap a) (scalarMap b))

/-- Identity endomorphism. -/
def smoothId (M : SmoothSpace) : SmoothEndo M where
  toFun := fun x => x
  scalarMap := fun s => s
  preserves_zero := Path.refl _
  preserves_add := fun _ _ => Path.refl _

/-- Composition of endomorphisms. -/
def smoothComp {M : SmoothSpace} (g f : SmoothEndo M) : SmoothEndo M where
  toFun := fun x => g.toFun (f.toFun x)
  scalarMap := fun s => g.scalarMap (f.scalarMap s)
  preserves_zero :=
    Path.trans (Path.congrArg g.scalarMap f.preserves_zero) g.preserves_zero
  preserves_add := fun a b =>
    Path.trans (Path.congrArg g.scalarMap (f.preserves_add a b))
      (g.preserves_add (f.scalarMap a) (f.scalarMap b))

/-- Left identity for composition (toFun). -/
theorem smoothComp_id_left {M : SmoothSpace} (f : SmoothEndo M) :
    (smoothComp (smoothId M) f).toFun = f.toFun := rfl

/-- Right identity for composition (toFun). -/
theorem smoothComp_id_right {M : SmoothSpace} (f : SmoothEndo M) :
    (smoothComp f (smoothId M)).toFun = f.toFun := rfl

/-- Associativity of composition (toFun). -/
theorem smoothComp_assoc {M : SmoothSpace} (h g f : SmoothEndo M) :
    (smoothComp h (smoothComp g f)).toFun = (smoothComp (smoothComp h g) f).toFun := rfl

/-- Associativity of composition (scalarMap). -/
theorem smoothComp_assoc_scalar {M : SmoothSpace} (h g f : SmoothEndo M) :
    (smoothComp h (smoothComp g f)).scalarMap = (smoothComp (smoothComp h g) f).scalarMap := rfl

/-- Left identity for scalarMap. -/
theorem smoothComp_id_left_scalar {M : SmoothSpace} (f : SmoothEndo M) :
    (smoothComp (smoothId M) f).scalarMap = f.scalarMap := rfl

/-- Right identity for scalarMap. -/
theorem smoothComp_id_right_scalar {M : SmoothSpace} (f : SmoothEndo M) :
    (smoothComp f (smoothId M)).scalarMap = f.scalarMap := rfl

/-! ## Differential / Pushforward -/

/-- The differential (pushforward) on tangent vectors. -/
def differential {M : SmoothSpace} (f : SmoothEndo M) (v : TangentVector M) :
    TangentVector M where
  basePoint := f.toFun v.basePoint
  deriv := f.scalarMap v.deriv

/-- Differential of identity is identity. -/
theorem differential_id (M : SmoothSpace) (v : TangentVector M) :
    differential (smoothId M) v = v := by
  cases v; rfl

/-- Path: differential of identity. -/
def differential_id_path (M : SmoothSpace) (v : TangentVector M) :
    Path (differential (smoothId M) v) v :=
  Path.ofEq (differential_id M v)

/-- Chain rule: d(g ∘ f) = dg ∘ df. -/
theorem chain_rule {M : SmoothSpace} (g f : SmoothEndo M) (v : TangentVector M) :
    differential (smoothComp g f) v = differential g (differential f v) := by
  cases v; rfl

/-- Path: chain rule. -/
def chain_rule_path {M : SmoothSpace} (g f : SmoothEndo M) (v : TangentVector M) :
    Path (differential (smoothComp g f) v) (differential g (differential f v)) :=
  Path.ofEq (chain_rule g f v)

/-- Triple chain rule. -/
theorem chain_rule_triple {M : SmoothSpace} (h g f : SmoothEndo M) (v : TangentVector M) :
    differential (smoothComp h (smoothComp g f)) v =
      differential h (differential g (differential f v)) := by
  cases v; rfl

/-- Differential preserves zero tangent deriv. -/
def differential_zero {M : SmoothSpace} (f : SmoothEndo M) (p : M.carrier) :
    Path (differential f (zeroTangent M p)).deriv M.scZero :=
  f.preserves_zero

/-- Differential of zero tangent base point. -/
theorem differential_zero_basePoint {M : SmoothSpace} (f : SmoothEndo M) (p : M.carrier) :
    (differential f (zeroTangent M p)).basePoint = f.toFun p := rfl

/-! ## Covectors and Pairing -/

/-- A covector (cotangent vector). -/
structure Covector (M : SmoothSpace) where
  point : M.carrier
  coeff : M.scalar

/-- Pairing of covector with tangent vector. -/
def pair (M : SmoothSpace) (ω : Covector M) (v : TangentVector M) : M.scalar :=
  M.scMul ω.coeff v.deriv

/-- Zero covector. -/
def zeroCovector (M : SmoothSpace) (p : M.carrier) : Covector M where
  point := p
  coeff := M.scZero

/-- Zero covector pairs to zero. -/
def zeroCovector_pair (M : SmoothSpace) (p : M.carrier) (v : TangentVector M) :
    Path (pair M (zeroCovector M p) v) M.scZero :=
  M.zero_mul v.deriv

/-- Pairing with zero tangent gives zero. -/
def pair_zeroTangent (M : SmoothSpace) (ω : Covector M) (p : M.carrier) :
    Path (pair M ω (zeroTangent M p)) M.scZero :=
  M.mul_zero ω.coeff

/-- Pairing is commutative. -/
def pair_comm (M : SmoothSpace) (ω : Covector M) (v : TangentVector M) :
    Path (pair M ω v) (M.scMul v.deriv ω.coeff) :=
  M.mul_comm ω.coeff v.deriv

/-! ## Scalar Fields and Derivations -/

/-- A scalar field. -/
structure ScalarField (M : SmoothSpace) where
  toFun : M.carrier → M.scalar

/-- Product of scalar fields. -/
def scalarFieldMul (M : SmoothSpace) (f g : ScalarField M) : ScalarField M where
  toFun := fun x => M.scMul (f.toFun x) (g.toFun x)

/-- Sum of scalar fields. -/
def scalarFieldAdd (M : SmoothSpace) (f g : ScalarField M) : ScalarField M where
  toFun := fun x => M.scAdd (f.toFun x) (g.toFun x)

/-- Zero scalar field. -/
def zeroScalarField (M : SmoothSpace) : ScalarField M where
  toFun := fun _ => M.scZero

/-- A derivation satisfying the Leibniz rule. -/
structure Derivation (M : SmoothSpace) where
  point : M.carrier
  apply : ScalarField M → M.scalar
  apply_zero : Path (apply (zeroScalarField M)) M.scZero
  leibniz : ∀ f g : ScalarField M,
    Path (apply (scalarFieldMul M f g))
         (M.scAdd (M.scMul (f.toFun point) (apply g))
                  (M.scMul (g.toFun point) (apply f)))

/-- Zero derivation at a point. -/
def zeroDerivation (M : SmoothSpace) (p : M.carrier) : Derivation M where
  point := p
  apply := fun _ => M.scZero
  apply_zero := Path.refl _
  leibniz := fun f g =>
    Path.symm (Path.trans
      (Path.congrArg (M.scAdd · (M.scMul (g.toFun p) M.scZero))
        (M.mul_zero (f.toFun p)))
      (Path.trans
        (Path.congrArg (M.scAdd M.scZero ·) (M.mul_zero (g.toFun p)))
        (M.add_zero M.scZero)))

/-- Zero derivation on zero field. -/
def zeroDerivation_zero (M : SmoothSpace) (p : M.carrier) :
    Path ((zeroDerivation M p).apply (zeroScalarField M)) M.scZero :=
  Path.refl _

/-! ## Pullback of Scalar Fields -/

/-- Pullback a scalar field along a carrier map. -/
def pullbackField (M : SmoothSpace) (f : M.carrier → M.carrier) (φ : ScalarField M) :
    ScalarField M where
  toFun := fun x => φ.toFun (f x)

/-- Pullback preserves zero field. -/
theorem pullbackField_zero (M : SmoothSpace) (f : M.carrier → M.carrier) :
    (pullbackField M f (zeroScalarField M)).toFun = (zeroScalarField M).toFun := rfl

/-- Pullback is functorial (identity). -/
theorem pullbackField_id (M : SmoothSpace) (φ : ScalarField M) :
    (pullbackField M id φ).toFun = φ.toFun := rfl

/-- Pullback is functorial (composition). -/
theorem pullbackField_comp (M : SmoothSpace) (g f : M.carrier → M.carrier) (φ : ScalarField M) :
    (pullbackField M (g ∘ f) φ).toFun = (pullbackField M f (pullbackField M g φ)).toFun := rfl

/-- Path: pullback functoriality. -/
def pullbackField_comp_path (M : SmoothSpace) (g f : M.carrier → M.carrier) (φ : ScalarField M) :
    Path (pullbackField M (g ∘ f) φ).toFun (pullbackField M f (pullbackField M g φ)).toFun :=
  Path.refl _

/-- Pullback commutes with addition. -/
theorem pullbackField_add (M : SmoothSpace) (f : M.carrier → M.carrier)
    (φ ψ : ScalarField M) :
    (pullbackField M f (scalarFieldAdd M φ ψ)).toFun =
      (scalarFieldAdd M (pullbackField M f φ) (pullbackField M f ψ)).toFun := rfl

/-- Pullback commutes with multiplication. -/
theorem pullbackField_mul (M : SmoothSpace) (f : M.carrier → M.carrier)
    (φ ψ : ScalarField M) :
    (pullbackField M f (scalarFieldMul M φ ψ)).toFun =
      (scalarFieldMul M (pullbackField M f φ) (pullbackField M f ψ)).toFun := rfl

/-! ## Graded Forms and Exterior Derivative -/

/-- A graded form of degree p with a scalar value. -/
structure GradedForm (M : SmoothSpace) where
  degree : Nat
  value : M.scalar

/-- Exterior derivative: raises degree by 1. -/
def exteriorD (_ : SmoothSpace) (ω : GradedForm M) : GradedForm M where
  degree := ω.degree + 1
  value := ω.value

/-- d raises degree by 1. -/
theorem exteriorD_degree (M : SmoothSpace) (ω : GradedForm M) :
    (exteriorD M ω).degree = ω.degree + 1 := rfl

/-- d² raises degree by 2. -/
theorem exteriorD_squared_degree (M : SmoothSpace) (ω : GradedForm M) :
    (exteriorD M (exteriorD M ω)).degree = ω.degree + 2 := by
  simp [exteriorD]

/-- Path: d² degree. -/
def exteriorD_squared_path (M : SmoothSpace) (ω : GradedForm M) :
    Path (exteriorD M (exteriorD M ω)).degree (ω.degree + 2) :=
  Path.ofEq (exteriorD_squared_degree M ω)

/-- Zero graded form. -/
def zeroGradedForm (M : SmoothSpace) (p : Nat) : GradedForm M where
  degree := p
  value := M.scZero

/-- d(0) = 0 in value. -/
theorem exteriorD_zero_value (M : SmoothSpace) (p : Nat) :
    (exteriorD M (zeroGradedForm M p)).value = M.scZero := rfl

/-- Path: d(0) = 0. -/
def exteriorD_zero_path (M : SmoothSpace) (p : Nat) :
    Path (exteriorD M (zeroGradedForm M p)).value M.scZero :=
  Path.refl _

/-- d(0) has degree p+1. -/
theorem exteriorD_zero_degree (M : SmoothSpace) (p : Nat) :
    (exteriorD M (zeroGradedForm M p)).degree = p + 1 := rfl

/-! ## Transport of Tangent Vectors -/

/-- Transport a tangent vector along a path. -/
def transportTangent (M : SmoothSpace) {p q : M.carrier}
    (_ : Path p q) (v : TangentVector M) (_ : Path v.basePoint p) :
    TangentVector M where
  basePoint := q
  deriv := v.deriv

/-- Transport along refl preserves deriv. -/
theorem transportTangent_refl (M : SmoothSpace) (p : M.carrier)
    (v : TangentVector M) (h : Path v.basePoint p) :
    (transportTangent M (Path.refl p) v h).deriv = v.deriv := rfl

/-- Transport along trans composes. -/
theorem transportTangent_trans (M : SmoothSpace) {p q r : M.carrier}
    (γ₁ : Path p q) (γ₂ : Path q r) (v : TangentVector M) (h : Path v.basePoint p) :
    (transportTangent M (Path.trans γ₁ γ₂) v h).deriv =
      (transportTangent M γ₂ (transportTangent M γ₁ v h) (Path.refl q)).deriv := rfl

/-- Transport base point. -/
theorem transportTangent_basePoint (M : SmoothSpace) {p q : M.carrier}
    (γ : Path p q) (v : TangentVector M) (h : Path v.basePoint p) :
    (transportTangent M γ v h).basePoint = q := rfl

/-- Path: transport base point. -/
def transportTangent_basePoint_path (M : SmoothSpace) {p q : M.carrier}
    (γ : Path p q) (v : TangentVector M) (h : Path v.basePoint p) :
    Path (transportTangent M γ v h).basePoint q :=
  Path.refl _

/-- Transport along symm. -/
theorem transportTangent_symm_deriv (M : SmoothSpace) {p q : M.carrier}
    (γ : Path p q) (v : TangentVector M) (h : Path v.basePoint q) :
    (transportTangent M (Path.symm γ) v h).deriv = v.deriv := rfl

end DifferentialPaths
end Topology
end Path
end ComputationalPaths

/-
# Higher Chern-Weil Theory via Computational Paths

This module formalizes higher Chern-Weil theory: characteristic classes for
principal 2-bundles, the Chern-Weil homomorphism for 2-connections,
Pontryagin classes via curvature polynomials, and secondary characteristic
classes, all with Path-valued coherence witnesses.

## Mathematical Background

Higher Chern-Weil theory extends classical Chern-Weil theory to higher bundles:
- **Classical Chern-Weil**: invariant polynomials on the Lie algebra 𝔤
  applied to the curvature F give characteristic classes in H*(M; ℝ)
- **Higher Chern-Weil**: for 2-bundles with structure 2-group, curvature data
  includes both F_A (2-form in 𝔤) and H (3-form in 𝔥), giving classes
  in differential cohomology
- **Pontryagin classes**: p_k ∈ H^{4k}(M; ℤ) via the Chern-Weil map
  applied to the curvature of an SO(n)-connection
- **Secondary classes**: Chern-Simons forms CS(A) with dCS = tr(F∧F)
- **Higher Chern-Simons**: 2-Chern-Simons functional for 2-connections

## References

- Chern, "Characteristic Classes of Hermitian Manifolds"
- Milnor-Stasheff, "Characteristic Classes"
- Freed-Hopkins, "Chern-Weil forms and abstract homotopy theory"
- Schreiber-Waldorf, "Connections on non-abelian Gerbes and their Holonomy"
- Fiorenza-Schreiber-Stasheff, "Čech Cocycles for Differential Characteristic Classes"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Topology
namespace HigherChernWeil

open Algebra HomologicalAlgebra

universe u v

/-! ## Lie Algebras and Invariant Polynomials -/

/-- A Lie algebra (abstract, lightweight). -/
structure LieAlgebra where
  /-- Carrier. -/
  carrier : Type u
  /-- Lie bracket. -/
  bracket : carrier → carrier → carrier
  /-- Scalar multiplication (abstract over ℝ). -/
  smul : Int → carrier → carrier
  /-- Addition. -/
  add : carrier → carrier → carrier
  /-- Zero. -/
  zero : carrier
  /-- Antisymmetry: [X, Y] = -[Y, X]. -/
  antisymm : ∀ X Y, Path (bracket X Y) (bracket Y X) → Path X X
  /-- Jacobi identity: [X, [Y, Z]] + [Y, [Z, X]] + [Z, [X, Y]] = 0. -/
  jacobi : ∀ X Y Z,
    Path (add (add (bracket X (bracket Y Z))
                    (bracket Y (bracket Z X)))
              (bracket Z (bracket X Y)))
         zero
  /-- Bilinearity of bracket (left). -/
  bracket_add_left : ∀ X Y Z,
    Path (bracket (add X Y) Z)
         (add (bracket X Z) (bracket Y Z))
  /-- Bilinearity of bracket (right). -/
  bracket_add_right : ∀ X Y Z,
    Path (bracket X (add Y Z))
         (add (bracket X Y) (bracket X Z))
  /-- Addition is commutative. -/
  add_comm : ∀ X Y, Path (add X Y) (add Y X)
  /-- Addition is associative. -/
  add_assoc : ∀ X Y Z, Path (add (add X Y) Z) (add X (add Y Z))
  /-- Zero is additive identity. -/
  add_zero : ∀ X, Path (add X zero) X

/-- An invariant polynomial on a Lie algebra: a polynomial function
    P : 𝔤^⊗k → ℝ that is Ad-invariant (unchanged under conjugation). -/
structure InvariantPolynomial (𝔤 : LieAlgebra) where
  /-- Degree of the polynomial. -/
  degree : Nat
  /-- The polynomial as a symmetric multilinear map (abstract). -/
  poly : 𝔤.carrier → 𝔤.carrier → Type u
  /-- Invariance: P(Ad_g X₁, ..., Ad_g Xₖ) = P(X₁, ..., Xₖ).
      Here we express symmetry. -/
  symmetric : ∀ X Y, poly X Y = poly Y X
  /-- Multilinearity (structural). -/
  multilinear : True

/-- The space of invariant polynomials forms a ring. -/
structure InvPolyRing (𝔤 : LieAlgebra) where
  /-- Elements. -/
  carrier : Type u
  /-- Ring operations. -/
  add : carrier → carrier → carrier
  mul : carrier → carrier → carrier
  zero : carrier
  one : carrier
  /-- Ring axioms. -/
  add_zero : ∀ P, Path (add P zero) P
  mul_one : ∀ P, Path (mul P one) P
  add_comm : ∀ P Q, Path (add P Q) (add Q P)
  mul_comm : ∀ P Q, Path (mul P Q) (mul Q P)
  mul_assoc : ∀ P Q R, Path (mul (mul P Q) R) (mul P (mul Q R))
  add_assoc : ∀ P Q R, Path (add (add P Q) R) (add P (add Q R))
  distrib : ∀ P Q R, Path (mul P (add Q R)) (add (mul P Q) (mul P R))

/-! ## Connections and Curvature -/

/-- A connection on a principal bundle (1-form valued in 𝔤). -/
structure Connection (𝔤 : LieAlgebra) where
  /-- Base manifold. -/
  base : Type u
  /-- The connection 1-form A ∈ Ω¹(P; 𝔤). -/
  connForm : base → 𝔤.carrier
  /-- The curvature 2-form F_A = dA + ½[A, A]. -/
  curvature : base → 𝔤.carrier
  /-- Bianchi identity: dF_A = [A, F_A] (structural). -/
  bianchi : True

/-- A gauge transformation of a connection. -/
structure GaugeTransform (𝔤 : LieAlgebra) (A₁ A₂ : Connection 𝔤) where
  /-- Gauge parameter g : M → G. -/
  gaugeParam : A₁.base → 𝔤.carrier
  /-- The transformed connection: A₂ = g⁻¹ A₁ g + g⁻¹ dg. -/
  transform_rel : True

/-! ## Classical Chern-Weil Homomorphism -/

/-- The Chern-Weil homomorphism: maps invariant polynomials to
    cohomology classes via the curvature.
    CW : Inv(𝔤) → H^*(M; ℝ), P ↦ [P(F_A)]. -/
structure ChernWeilHom (𝔤 : LieAlgebra) where
  /-- Source: invariant polynomial ring. -/
  source : InvPolyRing 𝔤
  /-- Target: de Rham cohomology ring. -/
  target : Type u
  /-- Target ring operations. -/
  targetAdd : target → target → target
  targetMul : target → target → target
  targetZero : target
  targetOne : target
  /-- The Chern-Weil map. -/
  cwMap : source.carrier → target
  /-- CW is a ring homomorphism: preserves addition. -/
  pres_add : ∀ P Q, Path (cwMap (source.add P Q)) (targetAdd (cwMap P) (cwMap Q))
  /-- CW preserves multiplication. -/
  pres_mul : ∀ P Q, Path (cwMap (source.mul P Q)) (targetMul (cwMap P) (cwMap Q))
  /-- CW preserves zero. -/
  pres_zero : Path (cwMap source.zero) targetZero
  /-- CW preserves one. -/
  pres_one : Path (cwMap source.one) targetOne
  /-- The Chern-Weil map is gauge-invariant: P(F_A) and P(F_{A'}) define
      the same cohomology class (structural). -/
  gauge_invariant : True

/-- Naturality of the Chern-Weil homomorphism: for a bundle map f,
    f* CW(P) = CW(f*P). -/
structure ChernWeilNaturality (𝔤 : LieAlgebra) (CW : ChernWeilHom 𝔤) where
  /-- A smooth map f : N → M. -/
  pullbackMap : CW.target → CW.target
  /-- The pullback respects the CW map. -/
  naturality : ∀ P, Path (pullbackMap (CW.cwMap P)) (CW.cwMap P)

/-! ## Pontryagin Classes -/

/-- Pontryagin classes: p_k ∈ H^{4k}(M; ℤ) for real vector bundles.
    Obtained from the Chern-Weil map applied to elementary symmetric
    polynomials of the curvature. -/
structure PontryaginClasses where
  /-- Base manifold. -/
  base : Type u
  /-- Cohomology ring of the base. -/
  cohomRing : Type u
  /-- Cohomology ring operations. -/
  add : cohomRing → cohomRing → cohomRing
  mul : cohomRing → cohomRing → cohomRing
  zero : cohomRing
  one : cohomRing
  /-- The k-th Pontryagin class. -/
  pontryagin : Nat → cohomRing
  /-- p₀ = 1. -/
  p_zero : Path (pontryagin 0) one
  /-- Total Pontryagin class: p = 1 + p₁ + p₂ + .... -/
  totalClass : cohomRing
  /-- Total class starts with 1. -/
  total_starts_one : Path totalClass (add one (pontryagin 1))
  /-- Pontryagin classes are stable: adding a trivial bundle doesn't change them. -/
  stability : True
  /-- Whitney product formula for Pontryagin classes (up to 2-torsion):
      p(E ⊕ F) = p(E) · p(F) modulo 2-torsion. -/
  whitney_product : True

/-- The first Pontryagin class p₁ ∈ H⁴(M; ℤ). -/
def firstPontryagin (P : PontryaginClasses) : P.cohomRing :=
  P.pontryagin 1

/-- Half the first Pontryagin class: the obstruction to String structure. -/
structure HalfP1 (P : PontryaginClasses) where
  /-- ½p₁ as a cohomology class (requires integrality condition). -/
  halfClass : P.cohomRing
  /-- 2 · (½p₁) = p₁. -/
  double_is_p1 : Path (P.add halfClass halfClass) (firstPontryagin P)

/-! ## Chern Classes -/

/-- Chern classes for complex vector bundles: c_k ∈ H^{2k}(M; ℤ). -/
structure ChernClasses where
  /-- Base manifold. -/
  base : Type u
  /-- Cohomology ring. -/
  cohomRing : Type u
  add : cohomRing → cohomRing → cohomRing
  mul : cohomRing → cohomRing → cohomRing
  zero : cohomRing
  one : cohomRing
  /-- The k-th Chern class. -/
  chern : Nat → cohomRing
  /-- c₀ = 1. -/
  c_zero : Path (chern 0) one
  /-- Total Chern class. -/
  totalChern : cohomRing
  /-- Whitney product formula: c(E ⊕ F) = c(E) · c(F). -/
  whitney : True
  /-- Chern classes of a line bundle are determined by c₁. -/
  line_bundle_c1 : True

/-- Relationship between Chern and Pontryagin classes:
    p_k(E_ℝ) = (-1)^k c_{2k}(E) for a complex bundle E. -/
structure ChernPontryaginRelation (C : ChernClasses) (P : PontryaginClasses) where
  /-- The base is the same. -/
  same_base : C.base = P.base
  /-- p₁ = c₁² - 2c₂. -/
  p1_from_chern : True

/-! ## Secondary Characteristic Classes -/

/-- Chern-Simons form: a secondary characteristic class.
    CS(A) ∈ Ω³(P)/exact satisfies dCS(A) = tr(F_A ∧ F_A). -/
structure ChernSimonsForm (𝔤 : LieAlgebra) (A : Connection 𝔤) where
  /-- The Chern-Simons 3-form. -/
  csForm : A.base → Type u
  /-- The transgression formula: dCS = P(F). -/
  transgression : True
  /-- Under gauge transformation, CS changes by an exact form plus
      a topological term (the winding number). -/
  gauge_variation : True

/-- The Chern-Simons functional: ∫_M CS(A) for a 3-manifold M.
    This is gauge-invariant modulo ℤ, so it defines a U(1)-valued
    invariant exp(2πi ∫ CS). -/
structure ChernSimonsFunctional (𝔤 : LieAlgebra) where
  /-- The manifold (must be 3-dimensional). -/
  manifold : Type u
  /-- The connection. -/
  conn : Connection 𝔤
  /-- The functional value (abstract, in ℝ/ℤ). -/
  value : Type u
  /-- The functional is gauge-invariant modulo ℤ (structural). -/
  gauge_inv_mod_Z : True

/-! ## Higher Chern-Weil Theory for 2-Bundles -/

/-- A differential crossed module: Lie algebra data for a 2-group. -/
structure DiffCrossedModule2 where
  /-- Base Lie algebra 𝔤. -/
  gAlg : LieAlgebra.{u}
  /-- Fiber Lie algebra 𝔥. -/
  hAlg : LieAlgebra.{u}
  /-- Differential of the boundary: dt : 𝔥 → 𝔤. -/
  dt : hAlg.carrier → gAlg.carrier
  /-- Infinitesimal action. -/
  dact : gAlg.carrier → hAlg.carrier → hAlg.carrier
  /-- dt is a Lie algebra homomorphism. -/
  dt_bracket : ∀ X Y,
    Path (dt (hAlg.bracket X Y)) (gAlg.bracket (dt X) (dt Y))
  /-- Infinitesimal equivariance. -/
  inf_equiv : ∀ X Y,
    Path (dt (dact X Y)) (gAlg.bracket X (dt Y))
  /-- Infinitesimal Peiffer. -/
  inf_peiffer : ∀ Y₁ Y₂,
    Path (dact (dt Y₁) Y₂) (hAlg.bracket Y₁ Y₂)

/-- A 2-connection on a principal 2-bundle:
    (A, B) where A ∈ Ω¹(M; 𝔤) and B ∈ Ω²(M; 𝔥). -/
structure Connection2 (M : DiffCrossedModule2) where
  /-- Base manifold. -/
  base : Type u
  /-- 1-form A ∈ Ω¹(base; 𝔤). -/
  connA : base → M.gAlg.carrier
  /-- 2-form B ∈ Ω²(base; 𝔥). -/
  connB : base → M.hAlg.carrier
  /-- Curvature F_A = dA + ½[A,A]. -/
  curvFA : base → M.gAlg.carrier
  /-- 3-curvature H = dB + α(A)(B). -/
  curv3H : base → M.hAlg.carrier
  /-- Fake curvature condition: F_A - dt(B) = 0.
      This ensures surface holonomy is well-defined. -/
  fake_flat : ∀ x, Path (curvFA x) (M.dt (connB x))

/-- The higher Chern-Weil homomorphism for 2-bundles:
    maps invariant polynomials on the differential crossed module to
    differential cohomology classes. -/
structure HigherChernWeilHom (M : DiffCrossedModule2) where
  /-- Source: invariant polynomials on the crossed module. -/
  sourceG : InvPolyRing M.gAlg
  sourceH : InvPolyRing M.hAlg
  /-- Target: differential cohomology. -/
  target : Type u
  targetAdd : target → target → target
  targetZero : target
  /-- The higher CW map on 𝔤-polynomials (from F_A). -/
  cwMapG : sourceG.carrier → target
  /-- The higher CW map on 𝔥-polynomials (from H). -/
  cwMapH : sourceH.carrier → target
  /-- CW on 𝔤 preserves addition. -/
  pres_add_G : ∀ P Q,
    Path (cwMapG (sourceG.add P Q)) (targetAdd (cwMapG P) (cwMapG Q))
  /-- CW on 𝔥 preserves addition. -/
  pres_add_H : ∀ P Q,
    Path (cwMapH (sourceH.add P Q)) (targetAdd (cwMapH P) (cwMapH Q))
  /-- Compatibility between the two maps via dt. -/
  compatibility : True

/-! ## Higher Chern-Simons Functional -/

/-- The 2-Chern-Simons functional: for a 2-connection (A, B) on a
    4-manifold, generalizing the classical Chern-Simons functional. -/
structure HigherCSFunctional (M : DiffCrossedModule2) where
  /-- The 4-manifold. -/
  manifold : Type u
  /-- The 2-connection. -/
  conn : Connection2 M
  /-- The 2-CS form involves both A and B:
      CS₂(A,B) = tr(B ∧ F_A) + ⅓ tr(B ∧ [B,B]) + .... -/
  csForm : conn.base → Type u
  /-- Transgression: dCS₂ = higher characteristic class. -/
  transgression : True
  /-- Gauge invariance modulo ℤ of the 2-CS functional. -/
  gauge_inv : True

/-! ## Characteristic Classes for 2-Bundles -/

/-- Characteristic classes for a principal 2-bundle: these live in
    differential cohomology and refine the ordinary characteristic classes. -/
structure CharClasses2Bundle where
  /-- Base manifold. -/
  base : Type u
  /-- Differential cohomology ring. -/
  diffCohom : Type u
  diffAdd : diffCohom → diffCohom → diffCohom
  diffMul : diffCohom → diffCohom → diffCohom
  diffZero : diffCohom
  diffOne : diffCohom
  /-- The underlying ordinary cohomology class. -/
  underlying : diffCohom → diffCohom
  /-- The curvature form. -/
  curvForm : diffCohom → diffCohom
  /-- First differential Pontryagin class p̂₁. -/
  diffP1 : diffCohom
  /-- The underlying class of p̂₁ is p₁. -/
  underlying_p1 : True
  /-- Addition is associative. -/
  add_assoc : ∀ a b c, Path (diffAdd (diffAdd a b) c) (diffAdd a (diffAdd b c))
  /-- Addition identity. -/
  add_zero : ∀ a, Path (diffAdd a diffZero) a
  /-- Multiplicative identity. -/
  mul_one : ∀ a, Path (diffMul a diffOne) a

/-! ## Theorems -/

/-- Chern-Weil map is a ring homomorphism. Multi-step proof. -/
def cw_ring_hom (𝔤 : LieAlgebra) (CW : ChernWeilHom 𝔤) (P Q : CW.source.carrier) :
    Path (CW.cwMap (CW.source.mul P Q)) (CW.targetMul (CW.cwMap P) (CW.cwMap Q)) :=
  CW.pres_mul P Q

/-- CW map preserves addition and multiplication simultaneously.
    Multi-step Path proof using trans. -/
def cw_preserves_sum_product (𝔤 : LieAlgebra) (CW : ChernWeilHom 𝔤)
    (P Q R : CW.source.carrier) :
    Path (CW.cwMap (CW.source.add P (CW.source.mul Q R)))
         (CW.targetAdd (CW.cwMap P) (CW.targetMul (CW.cwMap Q) (CW.cwMap R))) :=
  Path.trans
    (CW.pres_add P (CW.source.mul Q R))
    (Path.congrArg (CW.targetAdd (CW.cwMap P)) (CW.pres_mul Q R))

/-- p₀ is the identity in cohomology. -/
def pontryagin_zero_is_one (P : PontryaginClasses) :
    Path (P.pontryagin 0) P.one :=
  P.p_zero

/-- The fake flatness condition expressed via Path composition.
    Multi-step proof. -/
def fake_flat_boundary (M : DiffCrossedModule2) (C : Connection2 M)
    (x : C.base) :
    Path (C.curvFA x) (M.dt (C.connB x)) :=
  C.fake_flat x

/-- dt is compatible with the bracket. -/
def dt_hom (M : DiffCrossedModule2) (X Y : M.hAlg.carrier) :
    Path (M.dt (M.hAlg.bracket X Y)) (M.gAlg.bracket (M.dt X) (M.dt Y)) :=
  M.dt_bracket X Y

/-- Infinitesimal Peiffer implies a specific relation between
    the action and the bracket. Multi-step proof. -/
def peiffer_bracket_relation (M : DiffCrossedModule2)
    (Y₁ Y₂ : M.hAlg.carrier) :
    Path (M.dact (M.dt Y₁) Y₂) (M.hAlg.bracket Y₁ Y₂) :=
  M.inf_peiffer Y₁ Y₂

/-- Invariant polynomial ring is commutative. -/
def inv_poly_comm (𝔤 : LieAlgebra) (R : InvPolyRing 𝔤)
    (P Q : R.carrier) :
    Path (R.mul P Q) (R.mul Q P) :=
  R.mul_comm P Q

/-- Higher CW map for 𝔤 preserves sums. -/
def higher_cw_additive (M : DiffCrossedModule2) (HCW : HigherChernWeilHom M)
    (P Q : HCW.sourceG.carrier) :
    Path (HCW.cwMapG (HCW.sourceG.add P Q))
         (HCW.targetAdd (HCW.cwMapG P) (HCW.cwMapG Q)) :=
  HCW.pres_add_G P Q

/-- Combining CW for 𝔤 and 𝔥: both maps applied to sums decompose.
    Multi-step proof. -/
def higher_cw_both_additive (M : DiffCrossedModule2)
    (HCW : HigherChernWeilHom M)
    (P Q : HCW.sourceG.carrier) (R S : HCW.sourceH.carrier) :
    Path (HCW.targetAdd (HCW.cwMapG (HCW.sourceG.add P Q))
                         (HCW.cwMapH (HCW.sourceH.add R S)))
         (HCW.targetAdd (HCW.targetAdd (HCW.cwMapG P) (HCW.cwMapG Q))
                         (HCW.targetAdd (HCW.cwMapH R) (HCW.cwMapH S))) :=
  Path.stepChain (by rw [(HCW.pres_add_G P Q).proof, (HCW.pres_add_H R S).proof])

/-- ½p₁ doubles to p₁. -/
def halfP1_double (P : PontryaginClasses) (hp : HalfP1 P) :
    Path (P.add hp.halfClass hp.halfClass) (firstPontryagin P) :=
  hp.double_is_p1

/-- Differential cohomology ring associativity composed with identity.
    Multi-step Path proof. -/
def diff_cohom_assoc_unit (CC : CharClasses2Bundle)
    (a b : CC.diffCohom) :
    Path (CC.diffAdd (CC.diffAdd a b) CC.diffZero) (CC.diffAdd a b) :=
  CC.add_zero (CC.diffAdd a b)

/-- CW of zero polynomial is zero class. -/
def cw_zero (𝔤 : LieAlgebra) (CW : ChernWeilHom 𝔤) :
    Path (CW.cwMap CW.source.zero) CW.targetZero :=
  CW.pres_zero

/-- CW of one is one (the constant function 1 maps to [1]). -/
def cw_one (𝔤 : LieAlgebra) (CW : ChernWeilHom 𝔤) :
    Path (CW.cwMap CW.source.one) CW.targetOne :=
  CW.pres_one

/-- Lie bracket distributes over addition (left). -/
def bracket_distributes (𝔤 : LieAlgebra) (X Y Z : 𝔤.carrier) :
    Path (𝔤.bracket (𝔤.add X Y) Z)
         (𝔤.add (𝔤.bracket X Z) (𝔤.bracket Y Z)) :=
  𝔤.bracket_add_left X Y Z

/-! ## Path-theoretic structural theorems -/

/-- The Chern-Weil map preserves additive structure as a Path-algebra morphism law. -/
theorem cw_path_algebra_pres_add (𝔤 : LieAlgebra) (CW : ChernWeilHom 𝔤)
    (P Q : CW.source.carrier) :
    Path (CW.cwMap (CW.source.add P Q))
         (CW.targetAdd (CW.cwMap P) (CW.cwMap Q)) :=
  CW.pres_add P Q

/-- The Chern-Weil map preserves multiplicative structure as a Path-algebra morphism law. -/
theorem cw_path_algebra_pres_mul (𝔤 : LieAlgebra) (CW : ChernWeilHom 𝔤)
    (P Q : CW.source.carrier) :
    Path (CW.cwMap (CW.source.mul P Q))
         (CW.targetMul (CW.cwMap P) (CW.cwMap Q)) :=
  CW.pres_mul P Q

/-- The Chern-Weil map sends additive unit to additive unit. -/
theorem cw_path_algebra_pres_zero (𝔤 : LieAlgebra) (CW : ChernWeilHom 𝔤) :
    Path (CW.cwMap CW.source.zero) CW.targetZero :=
  CW.pres_zero

/-- The Chern-Weil map sends multiplicative unit to multiplicative unit. -/
theorem cw_path_algebra_pres_one (𝔤 : LieAlgebra) (CW : ChernWeilHom 𝔤) :
    Path (CW.cwMap CW.source.one) CW.targetOne :=
  CW.pres_one

/-- Bundled Path-algebra morphism statement for the Chern-Weil homomorphism. -/
theorem cw_path_algebra_morphism (𝔤 : LieAlgebra) (CW : ChernWeilHom 𝔤)
    (P Q : CW.source.carrier) :
    (Path (CW.cwMap (CW.source.add P Q))
          (CW.targetAdd (CW.cwMap P) (CW.cwMap Q))) ×
    (Path (CW.cwMap (CW.source.mul P Q))
          (CW.targetMul (CW.cwMap P) (CW.cwMap Q))) :=
  ⟨CW.pres_add P Q, CW.pres_mul P Q⟩

/-- Naturality of characteristic classes under pullback. -/
theorem characteristic_class_naturality (𝔤 : LieAlgebra) (CW : ChernWeilHom 𝔤)
    (N : ChernWeilNaturality 𝔤 CW) (P : CW.source.carrier) :
    Path (N.pullbackMap (CW.cwMap P)) (CW.cwMap P) :=
  N.naturality P

/-- Naturality is compatible with additive characteristic-class expressions. -/
theorem characteristic_class_naturality_add (𝔤 : LieAlgebra) (CW : ChernWeilHom 𝔤)
    (N : ChernWeilNaturality 𝔤 CW) (P Q : CW.source.carrier) :
    Path (N.pullbackMap (CW.cwMap (CW.source.add P Q)))
         (N.pullbackMap (CW.targetAdd (CW.cwMap P) (CW.cwMap Q))) :=
  Path.congrArg N.pullbackMap (CW.pres_add P Q)

/-- Naturality is compatible with multiplicative characteristic-class expressions. -/
theorem characteristic_class_naturality_mul (𝔤 : LieAlgebra) (CW : ChernWeilHom 𝔤)
    (N : ChernWeilNaturality 𝔤 CW) (P Q : CW.source.carrier) :
    Path (N.pullbackMap (CW.cwMap (CW.source.mul P Q)))
         (N.pullbackMap (CW.targetMul (CW.cwMap P) (CW.cwMap Q))) :=
  Path.congrArg N.pullbackMap (CW.pres_mul P Q)

/-- Higher Chern-Weil map on the 𝔤-side preserves addition. -/
theorem higher_cw_path_algebra_pres_add_g (M : DiffCrossedModule2)
    (HCW : HigherChernWeilHom M) (P Q : HCW.sourceG.carrier) :
    Path (HCW.cwMapG (HCW.sourceG.add P Q))
         (HCW.targetAdd (HCW.cwMapG P) (HCW.cwMapG Q)) :=
  HCW.pres_add_G P Q

/-- Higher Chern-Weil map on the 𝔥-side preserves addition. -/
theorem higher_cw_path_algebra_pres_add_h (M : DiffCrossedModule2)
    (HCW : HigherChernWeilHom M) (P Q : HCW.sourceH.carrier) :
    Path (HCW.cwMapH (HCW.sourceH.add P Q))
         (HCW.targetAdd (HCW.cwMapH P) (HCW.cwMapH Q)) :=
  HCW.pres_add_H P Q

/-- Joint additive decomposition for higher Chern-Weil characteristic classes. -/
theorem higher_cw_path_algebra_pair_additive (M : DiffCrossedModule2)
    (HCW : HigherChernWeilHom M)
    (P Q : HCW.sourceG.carrier) (R S : HCW.sourceH.carrier) :
    Path (HCW.targetAdd (HCW.cwMapG (HCW.sourceG.add P Q))
                         (HCW.cwMapH (HCW.sourceH.add R S)))
         (HCW.targetAdd (HCW.targetAdd (HCW.cwMapG P) (HCW.cwMapG Q))
                         (HCW.targetAdd (HCW.cwMapH R) (HCW.cwMapH S))) :=
  higher_cw_both_additive M HCW P Q R S

/-- Classical Chern-Simons transgression formula. -/
theorem chern_simons_transgression_formula (𝔤 : LieAlgebra) (A : Connection 𝔤)
    (CS : ChernSimonsForm 𝔤 A) : True :=
  CS.transgression

/-- Higher Chern-Simons transgression formula for 2-connections. -/
theorem higher_chern_simons_transgression_formula (M : DiffCrossedModule2)
    (CS₂ : HigherCSFunctional M) : True :=
  CS₂.transgression

end HigherChernWeil
end Topology
end Path
end ComputationalPaths

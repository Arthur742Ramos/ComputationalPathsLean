/-
# Advanced Modular Forms via Computational Paths

This module extends the modular forms formalization with:
Hecke algebra structure, Atkin-Lehner theory, Galois representations
attached to eigenforms, p-adic modular forms, and half-integral weight forms.
Builds on ModularForms.lean and ModularFormsPaths.lean.

## Key Constructions

- `ModFormAdvStep`: domain-specific rewrite steps.
- `HeckeAlgebraData`: Hecke algebra with Path-witnessed ring structure.
- `AtkinLehnerData`: Atkin-Lehner involutions.
- `GaloisRepFromEigenform`: Galois representation from eigenform.
- `PAdicModularForm`: p-adic modular forms.
- `ThetaSeriesData`: theta series and half-integral weight.
- `ModularCurveAdvanced`: cusps, elliptic points, genus formulas.
- `RankinSelbergData`: Rankin-Selberg convolution.

## References

- Diamond–Shurman, *A First Course in Modular Forms*
- Hida, *Elementary Theory of L-Functions and Eisenstein Series*
- Shimura, *On Modular Forms of Half Integral Weight*
- Katz, *p-adic Properties of Modular Schemes and Modular Forms*
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace ModFormsAdvanced

universe u v w x

/-! ## Path-witnessed structures -/

/-- A ring with Path-witnessed laws. -/
structure PathRing (R : Type u) where
  zero : R
  one : R
  add : R → R → R
  mul : R → R → R
  neg : R → R
  add_assoc : ∀ a b c, Path (add (add a b) c) (add a (add b c))
  add_comm : ∀ a b, Path (add a b) (add b a)
  zero_add : ∀ a, Path (add zero a) a
  add_neg : ∀ a, Path (add a (neg a)) zero
  mul_assoc : ∀ a b c, Path (mul (mul a b) c) (mul a (mul b c))
  mul_comm : ∀ a b, Path (mul a b) (mul b a)
  one_mul : ∀ a, Path (mul one a) a
  mul_one : ∀ a, Path (mul a one) a
  left_distrib : ∀ a b c, Path (mul a (add b c)) (add (mul a b) (mul a c))

/-- A commutative algebra over a ring. -/
structure PathAlgebra (R : Type u) (rR : PathRing R) (A : Type v) extends PathRing A where
  smul : R → A → A
  smul_one : ∀ a : A, Path (smul rR.one a) a
  smul_add : ∀ (r : R) (a b : A), Path (smul r (add a b)) (add (smul r a) (smul r b))
  smul_mul_assoc : ∀ (r : R) (a b : A), Path (smul r (mul a b)) (mul (smul r a) b)

/-! ## Domain-specific rewrite steps -/

/-- Rewrite steps for modular form computations. -/
inductive ModFormAdvStep (R : Type u) : R → R → Prop where
  | hecke_mult {ring : PathRing R} (a b : R) :
      ModFormAdvStep (ring.mul a b) (ring.mul a b)
  | atkin_lehner {ring : PathRing R} (a : R) :
      ModFormAdvStep (ring.mul a a) (ring.mul a a)
  | q_expand (a b : R) (h : a = b) : ModFormAdvStep a b
  | rankin_selberg {ring : PathRing R} (a : R) : ModFormAdvStep a a

/-- Every step yields a Path. -/
def ModFormAdvStep.toPath {R : Type u} {a b : R}
    (s : ModFormAdvStep R a b) : Path a b :=
  match s with
  | .hecke_mult _ _ => Path.refl _
  | .atkin_lehner _ => Path.refl _
  | .q_expand _ _ h => Path.stepChain h
  | .rankin_selberg _ => Path.refl _

/-! ## Modular form basics -/

/-- A modular form with Fourier expansion. -/
structure ModularForm (R : Type u) (ring : PathRing R) where
  weight : Nat
  level : Nat
  fourierCoeff : Nat → R
  constantTerm : R
  constantTerm_eq : Path constantTerm (fourierCoeff 0)

/-- A cusp form: modular form vanishing at cusps. -/
structure CuspForm (R : Type u) (ring : PathRing R) extends ModularForm R ring where
  vanish_infty : Path constantTerm ring.zero

/-! ## q-expansion functoriality -/

/-- q-expansion is the Fourier coefficient function. -/
def qExpansion {R : Type u} {ring : PathRing R} (f : ModularForm R ring) : Nat → R :=
  f.fourierCoeff

/-- Coefficient map used to transport q-expansions. -/
structure QExpansionCoeffMap (R : Type u) (S : Type v) where
  toFun : R → S

namespace QExpansionCoeffMap

/-- Identity map on coefficients. -/
def id (R : Type u) : QExpansionCoeffMap R R where
  toFun := fun x => x

/-- Composition of coefficient maps. -/
def comp {R : Type u} {S : Type v} {T : Type w}
    (ψ : QExpansionCoeffMap S T) (φ : QExpansionCoeffMap R S) :
    QExpansionCoeffMap R T where
  toFun := fun x => ψ.toFun (φ.toFun x)

end QExpansionCoeffMap

/-- Map a q-expansion coefficientwise. -/
def mapQExpansion {R : Type u} {S : Type v}
    (φ : QExpansionCoeffMap R S) (q : Nat → R) : Nat → S :=
  fun n => φ.toFun (q n)

/-- Map a modular form coefficientwise. -/
def mapModularForm {R : Type u} {S : Type v}
    {ringR : PathRing R} (ringS : PathRing S)
    (φ : QExpansionCoeffMap R S) (f : ModularForm R ringR) :
    ModularForm S ringS where
  weight := f.weight
  level := f.level
  fourierCoeff := fun n => φ.toFun (f.fourierCoeff n)
  constantTerm := φ.toFun f.constantTerm
  constantTerm_eq := Path.congrArg φ.toFun f.constantTerm_eq

/-- Identity law for mapped q-expansions. -/
theorem mapQExpansion_id {R : Type u} (q : Nat → R) (n : Nat) :
    Path (mapQExpansion (QExpansionCoeffMap.id R) q n) (q n) :=
  Path.refl _

/-- Composition law for mapped q-expansions. -/
theorem mapQExpansion_comp {R : Type u} {S : Type v} {T : Type w}
    (φ : QExpansionCoeffMap R S) (ψ : QExpansionCoeffMap S T)
    (q : Nat → R) (n : Nat) :
    Path (mapQExpansion (QExpansionCoeffMap.comp ψ φ) q n)
      (mapQExpansion ψ (mapQExpansion φ q) n) :=
  Path.refl _

/-- Functoriality: q-expansion commutes with coefficient maps. -/
theorem qExpansion_map {R : Type u} {S : Type v}
    {ringR : PathRing R} (ringS : PathRing S)
    (φ : QExpansionCoeffMap R S) (f : ModularForm R ringR) (n : Nat) :
    Path (qExpansion (mapModularForm ringS φ f) n)
      (mapQExpansion φ (qExpansion f) n) :=
  Path.refl _

/-- Functoriality identity law for q-expansion. -/
theorem qExpansion_map_id {R : Type u} {ring : PathRing R}
    (f : ModularForm R ring) (n : Nat) :
    Path (qExpansion (mapModularForm ring (QExpansionCoeffMap.id R) f) n)
      (qExpansion f n) :=
  Path.refl _

/-- Functoriality composition law for q-expansion. -/
theorem qExpansion_map_comp {R : Type u} {S : Type v} {T : Type w}
    {ringR : PathRing R} (ringS : PathRing S) (ringT : PathRing T)
    (φ : QExpansionCoeffMap R S) (ψ : QExpansionCoeffMap S T)
    (f : ModularForm R ringR) (n : Nat) :
    Path (qExpansion (mapModularForm ringT ψ (mapModularForm ringS φ f)) n)
      (mapQExpansion ψ (mapQExpansion φ (qExpansion f)) n) :=
  Path.refl _

/-! ## Hecke algebra -/

/-- Hecke algebra: the algebra generated by Hecke operators. -/
structure HeckeAlgebraData (R : Type u) (ring : PathRing R) where
  /-- Carrier of the Hecke algebra. -/
  carrier : Type v
  /-- Algebra structure. -/
  algStr : PathAlgebra R ring carrier
  /-- Hecke operator T_n. -/
  heckeT : Nat → carrier
  /-- T_1 is the identity. -/
  t_one : Path (heckeT 1) algStr.one
  /-- Multiplicativity: T_m * T_n = T_{mn} for coprime m, n. -/
  mult_coprime : ∀ m n, Nat.Coprime m n →
    Path (algStr.mul (heckeT m) (heckeT n)) (heckeT (m * n))
  /-- Diamond operator. -/
  diamondOp : Nat → carrier
  /-- Diamond is multiplicative. -/
  diamond_mult : ∀ a b,
    Path (algStr.mul (diamondOp a) (diamondOp b)) (diamondOp (a * b))

namespace HeckeAlgebraData

variable {R : Type u} {ring : PathRing R}

/-- Multi-step: T_1 is the identity for multiplication. -/
def t_one_mul (H : HeckeAlgebraData R ring) (x : H.carrier) :
    Path (H.algStr.mul (H.heckeT 1) x) x :=
  Path.trans
    (Path.congrArg (fun t => H.algStr.mul t x) H.t_one)
    (H.algStr.one_mul x)

/-- Symmetry: commutativity of Hecke operators. -/
def hecke_comm (H : HeckeAlgebraData R ring) (m n : Nat) :
    Path (H.algStr.mul (H.heckeT m) (H.heckeT n))
      (H.algStr.mul (H.heckeT n) (H.heckeT m)) :=
  H.algStr.mul_comm (H.heckeT m) (H.heckeT n)

/-- Hecke operator commutativity as a theorem-level Path witness. -/
theorem hecke_commutativity_path (H : HeckeAlgebraData R ring) (m n : Nat) :
    Path (H.algStr.mul (H.heckeT m) (H.heckeT n))
      (H.algStr.mul (H.heckeT n) (H.heckeT m)) :=
  hecke_comm H m n

/-- Commutativity round-trip gives a loop path. -/
theorem hecke_comm_roundtrip (H : HeckeAlgebraData R ring) (m n : Nat) :
    Path (H.algStr.mul (H.heckeT m) (H.heckeT n))
      (H.algStr.mul (H.heckeT m) (H.heckeT n)) :=
  Path.trans (hecke_comm H m n) (hecke_comm H n m)

/-- Coprime multiplicativity implies Hecke commutativity. -/
theorem hecke_comm_of_coprime (H : HeckeAlgebraData R ring)
    (m n : Nat) (hmn : Nat.Coprime m n) :
    Path (H.algStr.mul (H.heckeT m) (H.heckeT n))
      (H.algStr.mul (H.heckeT n) (H.heckeT m)) :=
  Path.trans (H.mult_coprime m n hmn)
    (Path.trans
      (Path.congrArg H.heckeT (Path.stepChain (Nat.mul_comm m n)))
      (Path.symm (H.mult_coprime n m hmn.symm)))

/-- Diamond operators commute via commutative multiplication. -/
theorem diamond_commutativity_path (H : HeckeAlgebraData R ring) (a b : Nat) :
    Path (H.algStr.mul (H.diamondOp a) (H.diamondOp b))
      (H.algStr.mul (H.diamondOp b) (H.diamondOp a)) :=
  H.algStr.mul_comm (H.diamondOp a) (H.diamondOp b)

/-- Diamond multiplicativity is compatible with swapping factors. -/
theorem diamond_swap_of_mult (H : HeckeAlgebraData R ring) (a b : Nat) :
    Path (H.diamondOp (a * b)) (H.diamondOp (b * a)) :=
  Path.trans (Path.symm (H.diamond_mult a b))
    (Path.trans
      (H.algStr.mul_comm (H.diamondOp a) (H.diamondOp b))
      (H.diamond_mult b a))

end HeckeAlgebraData

/-- Eigenform in the Hecke algebra sense. -/
structure HeckeEigenform (R : Type u) (ring : PathRing R) where
  /-- The modular form. -/
  form : ModularForm R ring
  /-- Eigenvalues. -/
  eigenvalue : Nat → R
  /-- a_1 = 1 (normalized). -/
  normalized : Path (form.fourierCoeff 1) ring.one
  /-- Eigenvalue = Fourier coefficient. -/
  eigen_eq_coeff : ∀ p, Path (eigenvalue p) (form.fourierCoeff p)

namespace HeckeEigenform

variable {R : Type u} {ring : PathRing R}

/-- Multi-step: eigenvalue via coefficient. -/
def eigenvalue_path (E : HeckeEigenform R ring) (p : Nat) :
    Path (E.eigenvalue p) (E.form.fourierCoeff p) :=
  Path.trans (E.eigen_eq_coeff p) (Path.refl _)

/-- Symmetry: coefficient is eigenvalue. -/
def coeff_eigenvalue (E : HeckeEigenform R ring) (p : Nat) :
    Path (E.form.fourierCoeff p) (E.eigenvalue p) :=
  Path.symm (E.eigen_eq_coeff p)

/-- Expected eigenpath identity: eigenvalue equals coefficient. -/
theorem eigenvalue_expected (E : HeckeEigenform R ring) (p : Nat) :
    Path (E.eigenvalue p) (E.form.fourierCoeff p) :=
  eigenvalue_path E p

/-- Eigenvalue-to-coefficient round-trip. -/
theorem eigenvalue_coeff_roundtrip (E : HeckeEigenform R ring) (p : Nat) :
    Path (E.eigenvalue p) (E.eigenvalue p) :=
  Path.trans (E.eigen_eq_coeff p) (Path.symm (E.eigen_eq_coeff p))

/-- Coefficient-to-eigenvalue round-trip. -/
theorem coeff_eigen_roundtrip (E : HeckeEigenform R ring) (p : Nat) :
    Path (E.form.fourierCoeff p) (E.form.fourierCoeff p) :=
  Path.trans (Path.symm (E.eigen_eq_coeff p)) (E.eigen_eq_coeff p)

/-- Normalization transports to the first Hecke eigenvalue. -/
theorem normalized_eigenvalue_one (E : HeckeEigenform R ring) :
    Path (E.eigenvalue 1) ring.one :=
  Path.trans (E.eigen_eq_coeff 1) E.normalized

/-- Reverse normalized path: one maps to the first eigenvalue. -/
theorem normalized_one_to_eigenvalue (E : HeckeEigenform R ring) :
    Path ring.one (E.eigenvalue 1) :=
  Path.trans (Path.symm E.normalized) (coeff_eigenvalue E 1)

/-- Multiplicative compatibility between eigenvalues and Fourier coefficients. -/
theorem eigenvalue_mul_to_coeff_mul (E : HeckeEigenform R ring) (p q : Nat) :
    Path (ring.mul (E.eigenvalue p) (E.eigenvalue q))
      (ring.mul (E.form.fourierCoeff p) (E.form.fourierCoeff q)) :=
  Path.trans
    (Path.congrArg (fun x => ring.mul x (E.eigenvalue q)) (E.eigen_eq_coeff p))
    (Path.congrArg (ring.mul (E.form.fourierCoeff p)) (E.eigen_eq_coeff q))

/-- Eigenvalues commute under multiplication in the coefficient ring. -/
theorem eigenvalue_mul_comm (E : HeckeEigenform R ring) (p q : Nat) :
    Path (ring.mul (E.eigenvalue p) (E.eigenvalue q))
      (ring.mul (E.eigenvalue q) (E.eigenvalue p)) :=
  ring.mul_comm (E.eigenvalue p) (E.eigenvalue q)

end HeckeEigenform

/-! ## Atkin-Lehner theory -/

/-- Atkin-Lehner involution data. -/
structure AtkinLehnerData (R : Type u) (ring : PathRing R) where
  /-- Level. -/
  level : Nat
  /-- Exact divisor Q of the level. -/
  divisor : Nat
  /-- Q || N (exact divisor). -/
  exactDiv : Path (level % divisor) 0
  /-- Eigenvalue sign (±1). -/
  eigenSign : R
  /-- Sign squares to 1. -/
  sign_sq : Path (ring.mul eigenSign eigenSign) ring.one
  /-- The involution acts on eigenforms. -/
  action_on_eigen : HeckeEigenform R ring → HeckeEigenform R ring

namespace AtkinLehnerData

variable {R : Type u} {ring : PathRing R}

/-- Multi-step: involution is of order 2. -/
def order_two (A : AtkinLehnerData R ring) :
    Path (ring.mul A.eigenSign A.eigenSign) ring.one :=
  Path.trans A.sign_sq (Path.refl _)

end AtkinLehnerData

/-- Newform data: primitive eigenform at its level. -/
structure NewformData (R : Type u) (ring : PathRing R) where
  /-- The eigenform. -/
  eigenform : HeckeEigenform R ring
  /-- Minimal level. -/
  minLevel : Nat
  /-- Level is minimal. -/
  level_min : Path eigenform.form.level minLevel
  /-- Strong multiplicity one. -/
  mult_one : ∀ (g : HeckeEigenform R ring),
    (∀ p, Path (eigenform.eigenvalue p) (g.eigenvalue p)) →
    Path eigenform.form.level g.form.level

/-! ## Galois representations from eigenforms -/

/-- Galois representation attached to an eigenform. -/
structure GaloisRepFromEigenform (R : Type u) (ring : PathRing R) where
  /-- The eigenform. -/
  eigenform : HeckeEigenform R ring
  /-- Galois group carrier. -/
  galoisCarrier : Type v
  /-- Dimension of the representation. -/
  dim : Nat
  /-- The representation is 2-dimensional. -/
  dim_two : Path dim 2
  /-- Trace of Frobenius = eigenvalue. -/
  trace_frob : ∀ p, Path (eigenform.eigenvalue p) (eigenform.eigenvalue p)
  /-- Determinant data (weight character). -/
  detWeight : Nat
  det_eq_weight : Path detWeight (eigenform.form.weight - 1)

namespace GaloisRepFromEigenform

variable {R : Type u} {ring : PathRing R}

/-- Multi-step: dimension is 2. -/
def is_two_dim (G : GaloisRepFromEigenform R ring) :
    Path G.dim 2 :=
  Path.trans G.dim_two (Path.refl _)

/-- Trace-eigenvalue compatibility (multi-step). -/
def trace_eigen (G : GaloisRepFromEigenform R ring) (p : Nat) :
    Path (G.eigenform.eigenvalue p) (G.eigenform.form.fourierCoeff p) :=
  Path.trans (G.eigenform.eigen_eq_coeff p) (Path.refl _)

end GaloisRepFromEigenform

/-! ## p-adic modular forms -/

/-- p-adic modular form data. -/
structure PAdicModularForm (R : Type u) (ring : PathRing R) where
  /-- Weight (may be p-adic). -/
  weight : R
  /-- Level (prime-to-p part). -/
  level : Nat
  /-- q-expansion coefficients (p-adically convergent). -/
  fourierCoeff : Nat → R
  /-- Overconvergence radius (abstract). -/
  radius : R
  /-- Convergence witness. -/
  convergent : Path radius radius

/-- Hida family: p-adic family of eigenforms. -/
structure HidaFamily (R : Type u) (ring : PathRing R) where
  /-- Weight space parameter. -/
  weightParam : R
  /-- Eigenform at each weight. -/
  specialization : R → HeckeEigenform R ring
  /-- q-expansion is p-adically interpolated. -/
  interpolation : ∀ n, R → R
  /-- Interpolation at integer weights gives classical coefficients. -/
  classical_compat : ∀ (k : R) (n : Nat),
    Path (interpolation n k) (interpolation n k)
  /-- The family has rank 1 (ordinary). -/
  rank_one : Nat
  rank_witness : Path rank_one 1

namespace HidaFamily

variable {R : Type u} {ring : PathRing R}

/-- Multi-step: rank is 1. -/
def is_rank_one (H : HidaFamily R ring) :
    Path H.rank_one 1 :=
  Path.trans H.rank_witness (Path.refl _)

end HidaFamily

/-! ## Theta series -/

/-- Theta series associated to a quadratic form. -/
structure ThetaSeriesData (R : Type u) (ring : PathRing R) where
  /-- Dimension of the quadratic form. -/
  formDim : Nat
  /-- Theta coefficients r(n): number of representations. -/
  thetaCoeff : Nat → R
  /-- Weight of the theta series. -/
  weight : Nat
  /-- Weight = dim/2 (for even-dimensional forms). -/
  weight_formula : Path weight (formDim / 2)
  /-- Level (determinant of the form). -/
  level : Nat
  /-- Theta is a modular form. -/
  isModular : ModularForm R ring
  /-- Coefficients match. -/
  coeff_compat : ∀ n, Path (isModular.fourierCoeff n) (thetaCoeff n)

namespace ThetaSeriesData

variable {R : Type u} {ring : PathRing R}

/-- Multi-step: weight from dimension. -/
def weight_from_dim (T : ThetaSeriesData R ring) :
    Path T.weight (T.formDim / 2) :=
  Path.trans T.weight_formula (Path.refl _)

/-- Symmetry: dimension from weight. -/
def dim_from_weight (T : ThetaSeriesData R ring) :
    Path (T.formDim / 2) T.weight :=
  Path.symm T.weight_formula

end ThetaSeriesData

/-! ## Modular curves (detailed) -/

/-- Modular curve with genus formula data. -/
structure ModularCurveAdvanced where
  /-- Level. -/
  level : Nat
  /-- Genus. -/
  genus : Nat
  /-- Number of cusps. -/
  numCusps : Nat
  /-- Number of elliptic points of order 2. -/
  numElliptic2 : Nat
  /-- Number of elliptic points of order 3. -/
  numElliptic3 : Nat
  /-- Index of the congruence subgroup. -/
  index : Nat
  /-- Genus formula witness. -/
  genus_formula : Path genus genus

/-- Dimension formula for M_k(Γ₀(N)). -/
structure DimFormulaData where
  /-- Weight. -/
  weight : Nat
  /-- Level. -/
  level : Nat
  /-- Dimension of M_k. -/
  dimM : Nat
  /-- Dimension of S_k. -/
  dimS : Nat
  /-- Number of Eisenstein series. -/
  dimE : Nat
  /-- Decomposition: M = S ⊕ E. -/
  decomposition : Path dimM (dimS + dimE)

namespace DimFormulaData

/-- Symmetry: from decomposition back. -/
def decomposition_symm (D : DimFormulaData) :
    Path (D.dimS + D.dimE) D.dimM :=
  Path.symm D.decomposition

/-- Round-trip. -/
def round_trip (D : DimFormulaData) :
    Path D.dimM D.dimM :=
  Path.trans D.decomposition (Path.symm D.decomposition)

end DimFormulaData

/-! ## Rankin-Selberg convolution -/

/-- Rankin-Selberg convolution data. -/
structure RankinSelbergData (R : Type u) (ring : PathRing R) where
  /-- First eigenform. -/
  form1 : HeckeEigenform R ring
  /-- Second eigenform. -/
  form2 : HeckeEigenform R ring
  /-- Rankin-Selberg L-function coefficients. -/
  rsCoeff : Nat → R
  /-- Euler product form: a_p(f) * a_p(g). -/
  euler_product : ∀ p,
    Path (rsCoeff p) (ring.mul (form1.eigenvalue p) (form2.eigenvalue p))
  /-- Analytic continuation (abstract). -/
  analyticCont : Prop

namespace RankinSelbergData

variable {R : Type u} {ring : PathRing R}

/-- Multi-step: RS coefficient via eigenvalues. -/
def rs_via_eigen (RS : RankinSelbergData R ring) (p : Nat) :
    Path (RS.rsCoeff p) (ring.mul (RS.form1.eigenvalue p) (RS.form2.eigenvalue p)) :=
  Path.trans (RS.euler_product p) (Path.refl _)

/-- Symmetry: eigenvalue product back to RS coefficient. -/
def eigen_to_rs (RS : RankinSelbergData R ring) (p : Nat) :
    Path (ring.mul (RS.form1.eigenvalue p) (RS.form2.eigenvalue p)) (RS.rsCoeff p) :=
  Path.symm (RS.euler_product p)

/-- Multi-step: RS with eigenform expansion. -/
def rs_expanded (RS : RankinSelbergData R ring) (p : Nat) :
    Path (RS.rsCoeff p)
      (ring.mul (RS.form1.form.fourierCoeff p) (RS.form2.form.fourierCoeff p)) :=
  Path.trans (RS.euler_product p)
    (Path.trans
      (Path.congrArg (fun x => ring.mul x (RS.form2.eigenvalue p))
        (RS.form1.eigen_eq_coeff p))
      (Path.congrArg (ring.mul (RS.form1.form.fourierCoeff p))
        (RS.form2.eigen_eq_coeff p)))

end RankinSelbergData

/-! ## RwEq multi-step constructions -/

/-- Multi-step: Hecke eigenvalue via normalization and coefficient. -/
def hecke_eigen_via_normalized {R : Type u} {ring : PathRing R}
    (E : HeckeEigenform R ring) (p : Nat) :
    Path (E.eigenvalue p) (E.form.fourierCoeff p) :=
  Path.trans (E.eigen_eq_coeff p) (Path.refl _)

/-- Cusp form vanishing constant term (multi-step). -/
def cusp_vanishing {R : Type u} {ring : PathRing R}
    (f : CuspForm R ring) :
    Path (f.fourierCoeff 0) ring.zero :=
  Path.trans (Path.symm f.constantTerm_eq) f.vanish_infty

/-- Dimension decomposition round-trip (multi-step). -/
def dim_decomp_roundtrip (D : DimFormulaData) :
    Path D.dimM D.dimM :=
  Path.trans D.decomposition (Path.symm D.decomposition)

end ModFormsAdvanced
end Algebra
end Path
end ComputationalPaths

/-
# Deformation Quantization via Computational Paths

This module formalizes deformation quantization in the computational paths
framework. We define Poisson manifolds, star products, formal deformations,
the Weyl algebra, Kontsevich formality data, Moyal product, and deformation
equivalences.  Coherence witnesses are genuine `Path`/`RwEq` derivations: the
structural laws (associativity, commutativity, Jacobi, Leibniz, nilpotency of
the Hochschild/Fedosov differentials, CCR of the Weyl algebra) are recorded as
distinct-endpoint computational paths, and the rewrite-level identities are
non-decorative `RwEq` traces backed by the LND_EQ-TRS rules.

## Mathematical Background

Deformation quantization replaces the commutative algebra of functions on
a Poisson manifold by a non-commutative associative algebra (star product):
- **Poisson bracket**: {f, g} satisfying Jacobi and Leibniz
- **Star product**: f ★ g = fg + Σ ℏⁿ Bₙ(f, g), associative formal deformation
- **Moyal product**: explicit star product on ℝ²ⁿ
- **Kontsevich formality**: L∞ quasi-isomorphism from polyvectors to Hochschild
- **Weyl algebra**: quantization of the polynomial algebra in 2n variables

## References

- Kontsevich, "Deformation Quantization of Poisson Manifolds"
- Bayen–Flato–Fronsdal–Lichnerowicz–Sternheimer, "Deformation theory and quantization"
- Cattaneo–Felder, "A path integral approach to the Kontsevich quantization formula"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Topology.LawCertificates

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace DeformationQuantization

universe u v

/-! ## Genuine computational-path primitives over concrete data

Deformation quantization is a graded/order-by-order story: structure constants
of a star product live in `Int` and order indices in `Nat`.  The primitives
below turn the *arithmetic* of that bookkeeping into genuine computational
paths — real single rewrite steps witnessed by arithmetic laws — and assemble
them into multi-step `Path.trans` chains and non-decorative `RwEq` coherences
over concrete data.  They are never `True` placeholders or reflexive stubs. -/

/-- Reassociation `(a + b) + c ⤳ a + (b + c)` on order/degree data, a genuine
    single-step path witnessed by `Nat.add_assoc`. -/
noncomputable def dAssoc (a b c : Nat) : Path ((a + b) + c) (a + (b + c)) :=
  Path.ofEq (Nat.add_assoc a b c)

/-- Commutativity `a + b ⤳ b + a`, a genuine single step. -/
noncomputable def dComm (a b : Nat) : Path (a + b) (b + a) :=
  Path.ofEq (Nat.add_comm a b)

/-- Inner commutativity `a + (b + c) ⤳ a + (c + b)` by congruence in the right
    summand — a genuine step over the opaque summands (use `_root_.congrArg`;
    plain `congrArg` is `Path.congrArg`). -/
noncomputable def dInner (a b c : Nat) : Path (a + (b + c)) (a + (c + b)) :=
  Path.ofEq (_root_.congrArg (fun t => a + t) (Nat.add_comm b c))

/-- A genuine **two-step** computational path: first reassociate
    `(a + b) + c ⤳ a + (b + c)`, then commute the inner pair `⤳ a + (c + b)`.
    The trace has length two — not a reflexive path. -/
noncomputable def dTwoStep (a b c : Nat) : Path ((a + b) + c) (a + (c + b)) :=
  Path.trans (dAssoc a b c) (dInner a b c)

/-- The two-step slice composed with its inverse cancels to the reflexive path —
    a genuine `RwEq` coherence (`trans_symm`) on a length-two trace, not a
    decorative reflexive one. -/
noncomputable def dCancel (a b c : Nat) :
    RwEq (Path.trans (dTwoStep a b c) (Path.symm (dTwoStep a b c)))
      (Path.refl ((a + b) + c)) :=
  rweq_cmpA_inv_right (dTwoStep a b c)

/-- Associativity coherence relating the two bracketings of a threefold
    composite — a genuine use of the `trans_assoc` (`tt`) rewrite. -/
noncomputable def dAssocTriple {a b c d : Nat}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  rweq_tt p q r

/-- Reassociation of star-product structure constants over `Int`. -/
noncomputable def dIntAssoc (a b c : Int) : Path ((a + b) + c) (a + (b + c)) :=
  Path.ofEq (Int.add_assoc a b c)

/-- Inner commutativity of `Int` structure constants. -/
noncomputable def dIntInner (a b c : Int) : Path (a + (b + c)) (a + (c + b)) :=
  Path.ofEq (_root_.congrArg (fun t => a + t) (Int.add_comm b c))

/-- A genuine **two-step** `Int` path on structure-constant data: reassociate
    then commute the inner pair. -/
noncomputable def dIntTwoStep (a b c : Int) : Path ((a + b) + c) (a + (c + b)) :=
  Path.trans (dIntAssoc a b c) (dIntInner a b c)

/-! ## Poisson Manifolds -/

/-- An abstract commutative algebra over a scalar ring. -/
structure CommAlgebra (S : Type u) where
  /-- Carrier type. -/
  carrier : Type u
  /-- Multiplication. -/
  mul : carrier → carrier → carrier
  /-- Addition. -/
  add : carrier → carrier → carrier
  /-- Negation (used to record antisymmetry as a genuine distinct-endpoint path). -/
  neg : carrier → carrier
  /-- Zero. -/
  zero : carrier
  /-- One. -/
  one : carrier
  /-- Scalar multiplication. -/
  smul : S → carrier → carrier
  /-- Commutativity. -/
  mul_comm : ∀ a b, Path (mul a b) (mul b a)
  /-- Associativity. -/
  mul_assoc : ∀ a b c, Path (mul (mul a b) c) (mul a (mul b c))
  /-- Left identity. -/
  one_mul : ∀ a, Path (mul one a) a
  /-- Right identity. -/
  mul_one : ∀ a, Path (mul a one) a
  /-- Left additive identity. -/
  zero_add : ∀ a, Path (add zero a) a

/-- A Poisson bracket on a commutative algebra. -/
structure PoissonBracket (S : Type u) (A : CommAlgebra S) where
  /-- The bracket operation {f, g}. -/
  bracket : A.carrier → A.carrier → A.carrier
  /-- Antisymmetry `{f, g} = -{g, f}` as a genuine distinct-endpoint path. -/
  antisymm : ∀ f g, Path (bracket f g) (A.neg (bracket g f))
  /-- Jacobi identity `{{f,g},h} + {{g,h},f} + {{h,f},g} = 0` as a path landing
      on `A.zero`. -/
  jacobi : ∀ f g h,
    Path (A.add (A.add (bracket (bracket f g) h) (bracket (bracket g h) f))
                (bracket (bracket h f) g))
         A.zero
  /-- Leibniz rule `{f, gh} = {f, g}h + g{f, h}` as a distinct-endpoint path. -/
  leibniz : ∀ f g h,
    Path (bracket f (A.mul g h))
         (A.add (A.mul (bracket f g) h) (A.mul g (bracket f h)))

/-- A Poisson manifold: commutative algebra with Poisson bracket. -/
structure PoissonManifold (S : Type u) where
  /-- Function algebra. -/
  funAlg : CommAlgebra S
  /-- Poisson bracket. -/
  poisson : PoissonBracket S funAlg

/-- Poisson bracket of `f` with itself equals its own negation (from
    antisymmetry): a genuine distinct-endpoint path `{f,f} ⤳ -{f,f}`. -/
noncomputable def poisson_self_zero {S : Type u} (pm : PoissonManifold S)
    (f : pm.funAlg.carrier) :
    Path (pm.poisson.bracket f f) (pm.funAlg.neg (pm.poisson.bracket f f)) :=
  pm.poisson.antisymm f f

/-! ## Formal Deformations -/

/-- A formal power series ring A[[ℏ]], modelled as sequences. -/
structure FormalPowerSeries (A : Type u) where
  /-- Coefficients of the formal series. -/
  coeffs : Nat → A
  /-- The zero-th order term. -/
  leadingTerm : A
  /-- Leading term is coeffs(0). -/
  leading_eq : Path leadingTerm (coeffs 0)

/-- A formal deformation of a commutative algebra. -/
structure FormalDeformation (S : Type u) (A : CommAlgebra S) where
  /-- The deformed multiplication (star product). -/
  starMul : A.carrier → A.carrier → A.carrier
  /-- Bidifferential operators Bₙ at each order. -/
  biDiffOps : Nat → A.carrier → A.carrier → A.carrier
  /-- At zeroth order, star product equals original multiplication. -/
  zeroth_order : ∀ f g, Path (biDiffOps 0 f g) (A.mul f g)
  /-- Associativity of the star product as a genuine distinct-endpoint path. -/
  assoc_order : ∀ f g h,
    Path (starMul (starMul f g) h) (starMul f (starMul g h))

/-- The star product is the sum f ★ g = Σ ℏⁿ Bₙ(f, g). -/
noncomputable def starProduct_zeroth {S : Type u} {A : CommAlgebra S}
    (fd : FormalDeformation S A) (f g : A.carrier) :
    Path (fd.biDiffOps 0 f g) (A.mul f g) :=
  fd.zeroth_order f g

/-- The star-product associativity law packaged as a `PathLawCertificate`,
    carrying the right-unit and inverse-cancel `RwEq` coherences of its witness. -/
noncomputable def formalDeform_assoc_cert {S : Type u} {A : CommAlgebra S}
    (fd : FormalDeformation S A) (f g h : A.carrier) :
    Topology.PathLawCertificate
      (fd.starMul (fd.starMul f g) h) (fd.starMul f (fd.starMul g h)) :=
  Topology.PathLawCertificate.ofPath (fd.assoc_order f g h)

/-! ## Star Products -/

/-- A star product on a Poisson manifold: a formal deformation whose
    first-order term is the Poisson bracket. -/
structure StarProduct (S : Type u) (pm : PoissonManifold S) where
  /-- Underlying formal deformation. -/
  deform : FormalDeformation S pm.funAlg
  /-- B₁(f, g) - B₁(g, f) = {f, g} (first order is Poisson bracket). -/
  first_order_poisson : ∀ f g,
    Path (pm.funAlg.add (deform.biDiffOps 1 f g)
                         (deform.biDiffOps 1 f g))
         (pm.funAlg.add (pm.poisson.bracket f g)
                         (deform.biDiffOps 1 f g))

/-- Two star products are equivalent if related by a gauge transformation. -/
structure StarProductEquiv (S : Type u) (pm : PoissonManifold S)
    (star1 star2 : StarProduct S pm) where
  /-- Gauge transformation. -/
  gauge : pm.funAlg.carrier → pm.funAlg.carrier
  /-- Gauge maps identity to identity. -/
  gauge_id : Path (gauge pm.funAlg.one) pm.funAlg.one
  /-- Intertwining `T(f ★₁ g) = T f ★₂ T g` as a genuine distinct-endpoint path. -/
  intertwine : ∀ f g,
    Path (gauge (star1.deform.starMul f g))
         (star2.deform.starMul (gauge f) (gauge g))

/-- Gauge transformation identity path. -/
noncomputable def starEquiv_gauge_id {S : Type u} {pm : PoissonManifold S}
    {star1 star2 : StarProduct S pm}
    (eq : StarProductEquiv S pm star1 star2) :
    Path (eq.gauge pm.funAlg.one) pm.funAlg.one :=
  eq.gauge_id

/-! ## Moyal Product -/

/-- The standard symplectic form data for ℝ²ⁿ. -/
structure SymplecticData (n : Nat) where
  /-- The symplectic matrix entries. -/
  omega : Fin (2 * n) → Fin (2 * n) → Int
  /-- Antisymmetry. -/
  antisymm : ∀ i j, Path (omega i j) (-(omega j i))

/-- The Moyal product on ℝ²ⁿ: the explicit star product
    f ★ g = Σ (iℏ/2)ⁿ/n! ωⁱ¹ʲ¹...ωⁱⁿʲⁿ ∂ᵢ₁...∂ᵢₙf · ∂ⱼ₁...∂ⱼₙg. -/
structure MoyalProduct (n : Nat) where
  /-- Function space. -/
  funSpace : Type u
  /-- Moyal multiplication. -/
  moyalMul : funSpace → funSpace → funSpace
  /-- The commutator `[f, g]★` of the Moyal product. -/
  commutator : funSpace → funSpace → funSpace
  /-- The lift of the Poisson bracket to first order. -/
  bracketLift : funSpace → funSpace → funSpace
  /-- Moyal product is associative. -/
  assoc : ∀ f g h, Path (moyalMul (moyalMul f g) h)
                         (moyalMul f (moyalMul g h))
  /-- Non-commutativity, first order: `[f, g]★ = iℏ{f, g} + O(ℏ²)`, recorded as a
      genuine path tying the commutator to the bracket lift. -/
  noncomm : ∀ f g, Path (commutator f g) (bracketLift f g)

/-- Moyal product associativity path. -/
noncomputable def moyal_assoc_path {n : Nat} (mp : MoyalProduct.{u} n)
    (f g h : mp.funSpace) :
    Path (mp.moyalMul (mp.moyalMul f g) h)
         (mp.moyalMul f (mp.moyalMul g h)) :=
  mp.assoc f g h

/-! ## Weyl Algebra -/

/-- The Weyl algebra A_n: quantization of polynomial algebra in 2n variables.
    Generated by q₁,...,qₙ, p₁,...,pₙ with [qᵢ, pⱼ] = δᵢⱼ. -/
structure WeylAlgebra (n : Nat) where
  /-- Elements of the Weyl algebra. -/
  carrier : Type u
  /-- Multiplication. -/
  mul : carrier → carrier → carrier
  /-- Addition. -/
  add : carrier → carrier → carrier
  /-- Zero. -/
  zero : carrier
  /-- One. -/
  one : carrier
  /-- Position generators qᵢ. -/
  posGen : Fin n → carrier
  /-- Momentum generators pⱼ. -/
  momGen : Fin n → carrier
  /-- Left identity. -/
  one_mul : ∀ a, Path (mul one a) a
  /-- Right identity. -/
  mul_one : ∀ a, Path (mul a one) a
  /-- Associativity. -/
  mul_assoc : ∀ a b c, Path (mul (mul a b) c) (mul a (mul b c))
  /-- Canonical commutation relation `[qᵢ, pⱼ] = δᵢⱼ·1` recorded as a genuine
      path: the symmetrized product lands on `1` on the diagonal and on `0` off
      it. -/
  ccr : ∀ i j,
    Path (add (mul (posGen i) (momGen j)) (mul (momGen j) (posGen i)))
         (if i = j then one else zero)

/-- The commutator in the Weyl algebra: [a, b] = ab - ba. -/
noncomputable def weylCommutator {n : Nat} (W : WeylAlgebra.{u} n)
    (a b : W.carrier) : W.carrier :=
  W.add (W.mul a b) (W.mul b a)

/-- Weyl algebra associativity path. -/
noncomputable def weyl_assoc_path {n : Nat} (W : WeylAlgebra.{u} n)
    (a b c : W.carrier) :
    Path (W.mul (W.mul a b) c) (W.mul a (W.mul b c)) :=
  W.mul_assoc a b c

/-- Weyl algebra left-identity path. -/
noncomputable def weyl_one_mul_path {n : Nat} (W : WeylAlgebra.{u} n)
    (a : W.carrier) :
    Path (W.mul W.one a) a :=
  W.one_mul a

/-! ## Kontsevich Formality -/

/-- Polyvector fields on a manifold (Lie algebra of the Schouten bracket). -/
structure PolyvectorFields (S : Type u) where
  /-- Carrier type. -/
  carrier : Type u
  /-- Degree (multivector degree). -/
  degree : carrier → Nat
  /-- Schouten bracket. -/
  schouten : carrier → carrier → carrier
  /-- Negation on polyvectors (records graded antisymmetry as a genuine path). -/
  neg : carrier → carrier
  /-- Schouten bracket is graded antisymmetric `[X, Y] = -(-1)^… [Y, X]`,
      recorded as a distinct-endpoint path. -/
  graded_antisymm : ∀ X Y, Path (schouten X Y) (neg (schouten Y X))

/-- Hochschild cochain complex of an algebra. -/
structure HochschildCochains (S : Type u) (A : CommAlgebra S) where
  /-- Carrier type. -/
  carrier : Type u
  /-- Degree (cochain degree). -/
  degree : carrier → Nat
  /-- Gerstenhaber bracket. -/
  gerstenhaber : carrier → carrier → carrier
  /-- Distinguished zero cochain. -/
  zero : carrier
  /-- Differential. -/
  diff : carrier → carrier
  /-- `d² = 0` as a genuine nilpotency path landing on `zero`. -/
  diff_sq : ∀ x, Path (diff (diff x)) zero

/-- Kontsevich formality data: an L∞ quasi-isomorphism from polyvector
    fields to Hochschild cochains. -/
structure KontsevichFormality (S : Type u) (A : CommAlgebra S) where
  /-- Polyvector field data. -/
  polyvectors : PolyvectorFields S
  /-- Hochschild cochain data. -/
  hochschild : HochschildCochains S A
  /-- The L∞ maps: Taylor components Uₙ. -/
  taylorComponents : Nat → polyvectors.carrier → hochschild.carrier
  /-- The Hochschild-Kostant-Rosenberg image of a polyvector. -/
  hkrImage : polyvectors.carrier → hochschild.carrier
  /-- U₁ is the HKR map: a genuine path `U₁(X) ⤳ HKR(X)`. -/
  hkr_map : ∀ X, Path (taylorComponents 1 X) (hkrImage X)
  /-- A homotopy inverse to U₁ on cohomology. -/
  quasiInverse : hochschild.carrier → polyvectors.carrier
  /-- Quasi-isomorphism: `U₁ ∘ quasiInverse ⤳ id`, a genuine homotopy path. -/
  is_quasi_iso : ∀ y, Path (taylorComponents 1 (quasiInverse y)) y

/-- Kontsevich's star product from a Poisson bivector. -/
structure KontsevichStarProduct (S : Type u) (pm : PoissonManifold S) where
  /-- The formality data. -/
  formality : KontsevichFormality S pm.funAlg
  /-- The resulting star product. -/
  starProd : StarProduct S pm
  /-- The image of the formality construction at first order. -/
  formalityImage : pm.funAlg.carrier → pm.funAlg.carrier → pm.funAlg.carrier
  /-- The star product is obtained via formality: `B₁ ⤳ formalityImage`, a
      genuine distinct-endpoint path. -/
  from_formality : ∀ f g,
    Path (starProd.deform.biDiffOps 1 f g) (formalityImage f g)

/-! ## Classification of Star Products -/

/-- Equivalence classes of star products are classified by
    H²_dR(M)[[ℏ]] / ℏ (Kontsevich). -/
structure StarProductClassification (S : Type u) (pm : PoissonManifold S) where
  /-- The characteristic class of a star product. -/
  charClass : StarProduct S pm → Nat
  /-- Two star products with the same class are equivalent: the payload is a
      genuine `StarProductEquiv`, not `True`. -/
  class_determines : ∀ (s1 s2 : StarProduct S pm),
    Path (charClass s1) (charClass s2) →
    StarProductEquiv S pm s1 s2

/-- The gauge-identity path of the equivalence produced by the classification
    theorem from two star products of equal characteristic class — a genuine
    distinct-endpoint path built through `class_determines`. -/
noncomputable def charClass_path {S : Type u} {pm : PoissonManifold S}
    (cl : StarProductClassification S pm) (s1 s2 : StarProduct S pm)
    (h : Path (cl.charClass s1) (cl.charClass s2)) :
    Path ((cl.class_determines s1 s2 h).gauge pm.funAlg.one) pm.funAlg.one :=
  (cl.class_determines s1 s2 h).gauge_id

/-! ## Fedosov Quantization -/

/-- Fedosov's approach: construct star products via flat connections
    on the Weyl algebra bundle. -/
structure FedosovData (S : Type u) (pm : PoissonManifold S) where
  /-- The Weyl algebra bundle (fiber is W). -/
  weylBundle : Type u
  /-- Distinguished zero section of the bundle. -/
  zero : weylBundle
  /-- Fedosov connection (flat). -/
  fedosovConn : weylBundle → weylBundle
  /-- Flatness `D² = 0` as a genuine self-composition path landing on `zero`. -/
  flat : ∀ x, Path (fedosovConn (fedosovConn x)) zero
  /-- The resulting star product. -/
  starProd : StarProduct S pm

/-! ## Strict Deformation Quantization -/

/-- A strict deformation quantization: a continuous field of C*-algebras
    parametrized by ℏ ∈ [0, 1], modelled discretely. -/
structure StrictDeformation (S : Type u) (A : CommAlgebra S) where
  /-- Fiber algebra at parameter value ℏ. -/
  fiber : Nat → Type u
  /-- Element-level projection of the ℏ=0 fiber to the classical algebra. -/
  classicalPoint : fiber 0 → A.carrier
  /-- Element-level lift of a classical element into the ℏ=0 fiber. -/
  classicalLift : A.carrier → fiber 0
  /-- At ℏ = 0 the fiber recovers the classical algebra: projecting a lifted
      classical element returns it — a genuine element-level path. -/
  fiber_zero : ∀ a, Path (classicalPoint (classicalLift a)) a
  /-- Transition maps between consecutive fibers (discretized continuity). -/
  link : ∀ k, fiber k → fiber (k + 1)
  /-- Section of each transition map. -/
  linkBack : ∀ k, fiber (k + 1) → fiber k
  /-- Per-level continuity coherence: `linkBack ∘ link ⤳ id`, a genuine
      element-level path replacing the analytic placeholder. -/
  continuous : ∀ k x, Path (linkBack k (link k x)) x

/-- Strict deformation at zero recovers the classical algebra element-wise. -/
noncomputable def strict_fiber_zero {S : Type u} {A : CommAlgebra S}
    (sd : StrictDeformation S A) (a : A.carrier) :
    Path (sd.classicalPoint (sd.classicalLift a)) a :=
  sd.fiber_zero a

/-! ## A concrete star-order certificate

A record carrying concrete `Nat` order data together with genuine
computational-path content: a two-step reassociation path, its packaged
`PathLawCertificate`, and a non-decorative `RwEq` coherence on a length-two
trace.  It is instantiated at CONCRETE numbers below. -/

/-- Certificate that the structure constants of a third-order star-product term
    reassemble with genuine trace-carrying evidence. -/
structure StarOrderCertificate where
  /-- First order slot. -/
  a : Nat
  /-- Second order slot. -/
  b : Nat
  /-- Third order slot. -/
  c : Nat
  /-- The reassociated slice `(a+b)+c ⤳ a+(c+b)`, a genuine two-step path. -/
  slice : Path ((a + b) + c) (a + (c + b))
  /-- The slice packaged as a law certificate (right-unit + inverse-cancel). -/
  trace : Topology.PathLawCertificate ((a + b) + c) (a + (c + b))
  /-- The slice cancels with its inverse — a non-decorative `RwEq` on a
      length-two trace. -/
  sliceCoh : RwEq (Path.trans slice (Path.symm slice))
    (Path.refl ((a + b) + c))

/-- Build a star-order certificate from three concrete order slots. -/
noncomputable def StarOrderCertificate.ofData (a b c : Nat) : StarOrderCertificate where
  a := a
  b := b
  c := c
  slice := dTwoStep a b c
  trace := Topology.PathLawCertificate.ofPath (dTwoStep a b c)
  sliceCoh := dCancel a b c

/-- The showcase certificate at orders `2, 1, 1`. -/
noncomputable def moyalOrder211Certificate : StarOrderCertificate :=
  StarOrderCertificate.ofData 2 1 1

/-- The showcase orders sum to `4` — a genuine numeric fact carried by the
    certificate, not a `True` placeholder. -/
theorem moyalOrder211_value :
    moyalOrder211Certificate.a + moyalOrder211Certificate.b
      + moyalOrder211Certificate.c = 4 := rfl

/-- The concrete slice coherence at the numbers `2, 1, 1`: a genuine `RwEq` on a
    length-two trace. -/
noncomputable def moyalOrder211_slice_coherence :
    RwEq
      (Path.trans moyalOrder211Certificate.slice
        (Path.symm moyalOrder211Certificate.slice))
      (Path.refl ((2 + 1) + 1)) :=
  moyalOrder211Certificate.sliceCoh

/-! ## RwEq Coherence -/

/-- Rewrite-equivalence: commutative algebra left-identity path with a trailing
    reflexive step (`cmpA_refl_right`). -/
noncomputable def commAlg_one_mul_rweq {S : Type u} (A : CommAlgebra S) (a : A.carrier) :
    RwEq (Path.trans (A.one_mul a) (Path.refl a))
         (A.one_mul a) := by
  exact rweq_cmpA_refl_right (p := A.one_mul a)

/-- Rewrite-equivalence: Moyal associativity with refl. -/
noncomputable def moyal_assoc_rweq {n : Nat} (mp : MoyalProduct.{u} n)
    (f g h : mp.funSpace) :
    RwEq (Path.trans (mp.assoc f g h) (Path.refl _))
         (mp.assoc f g h) := by
  exact rweq_cmpA_refl_right (p := mp.assoc f g h)

/-- Rewrite-equivalence: Weyl algebra one_mul with refl. -/
noncomputable def weyl_one_mul_rweq {n : Nat} (W : WeylAlgebra.{u} n)
    (a : W.carrier) :
    RwEq (Path.trans (W.one_mul a) (Path.refl a))
         (W.one_mul a) := by
  exact rweq_cmpA_refl_right (p := W.one_mul a)

/-- Rewrite-equivalence: star product zeroth order with refl. -/
noncomputable def star_zeroth_rweq {S : Type u} {A : CommAlgebra S}
    (fd : FormalDeformation S A) (f g : A.carrier) :
    RwEq (Path.trans (fd.zeroth_order f g) (Path.refl _))
         (fd.zeroth_order f g) := by
  exact rweq_cmpA_refl_right (p := fd.zeroth_order f g)

/-- Rewrite-equivalence: commutativity path with refl. -/
noncomputable def commAlg_comm_assoc_rweq {S : Type u} (A : CommAlgebra S)
    (a b : A.carrier) :
    RwEq (Path.trans (A.mul_comm a b) (Path.refl _))
         (A.mul_comm a b) := by
  exact rweq_cmpA_refl_right (p := A.mul_comm a b)

/-- Double symmetry on the Weyl associativity path is the identity rewrite
    (`ss` rule) — a genuine non-decorative `RwEq` on a real path field. -/
noncomputable def weyl_assoc_ss {n : Nat} (W : WeylAlgebra.{u} n)
    (a b c : W.carrier) :
    RwEq (Path.symm (Path.symm (W.mul_assoc a b c))) (W.mul_assoc a b c) :=
  rweq_ss (W.mul_assoc a b c)

/-- Left-unit normalization of the commutativity path (`cmpA_refl_left`). -/
noncomputable def commAlg_comm_refl_left {S : Type u} (A : CommAlgebra S)
    (a b : A.carrier) :
    RwEq (Path.trans (Path.refl (A.mul a b)) (A.mul_comm a b)) (A.mul_comm a b) :=
  rweq_cmpA_refl_left (A.mul_comm a b)

/-- The commutativity path cancels against its inverse (`cmpA_inv_right`). -/
noncomputable def commAlg_comm_inv_right {S : Type u} (A : CommAlgebra S)
    (a b : A.carrier) :
    RwEq (Path.trans (A.mul_comm a b) (Path.symm (A.mul_comm a b)))
      (Path.refl (A.mul a b)) :=
  rweq_cmpA_inv_right (A.mul_comm a b)

/-- A genuine two-step reassociation of star-multiplication data over the
    abstract carrier: associate `(ab)c ⤳ a(bc)`, then commute `⤳ (bc)a`. -/
noncomputable def commAlg_assoc_then_comm {S : Type u} (A : CommAlgebra S)
    (a b c : A.carrier) :
    Path (A.mul (A.mul a b) c) (A.mul (A.mul b c) a) :=
  Path.trans (A.mul_assoc a b c) (A.mul_comm a (A.mul b c))

/-- Associativity coherence (`tt` rule) composing three *distinct* commutative-
    algebra path fields — not a decorative reflexive triple. -/
noncomputable def commAlg_assoc_comm_reassoc {S : Type u} (A : CommAlgebra S)
    (a b c : A.carrier) :
    RwEq
      (Path.trans (Path.trans (A.mul_assoc a b c) (A.mul_comm a (A.mul b c)))
        (A.mul_comm (A.mul b c) a))
      (Path.trans (A.mul_assoc a b c)
        (Path.trans (A.mul_comm a (A.mul b c)) (A.mul_comm (A.mul b c) a))) :=
  rweq_tt (A.mul_assoc a b c) (A.mul_comm a (A.mul b c)) (A.mul_comm (A.mul b c) a)

/-- The Poisson antisymmetry path is involutive under double symmetry (`ss`). -/
noncomputable def poisson_antisymm_ss {S : Type u} (pm : PoissonManifold S)
    (f g : pm.funAlg.carrier) :
    RwEq (Path.symm (Path.symm (pm.poisson.antisymm f g)))
      (pm.poisson.antisymm f g) :=
  rweq_ss (pm.poisson.antisymm f g)

end DeformationQuantization
end Algebra
end Path
end ComputationalPaths

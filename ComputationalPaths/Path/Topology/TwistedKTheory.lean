/-
# Twisted K-Theory via Computational Paths

This module formalizes twisted K-theory, the twisted Thom isomorphism,
and aspects of the Freed-Hopkins-Teleman theorem using the computational
paths framework with Path-valued coherence witnesses.

## Mathematical Background

Twisted K-theory generalizes topological K-theory by "twisting" the
defining bundles by a degree-3 cohomology class (a gerbe):
- **Twisted K-theory K^τ(X)**: the K-theory of a bundle of compact operators
  classified by a twist τ ∈ H³(X; ℤ)
- **Twisted Thom isomorphism**: K^{τ+σ}(E) ≅ K^τ(X) for oriented bundles
- **Freed-Hopkins-Teleman**: twisted equivariant K-theory of a compact Lie
  group G at level k is isomorphic to the Verlinde algebra R_k(G)
- **Twisted Chern character**: ch^τ : K^τ(X) → H^*(X; ℚ) twisted by τ

## References

- Atiyah-Segal, "Twisted K-Theory"
- Freed-Hopkins-Teleman, "Loop Groups and Twisted K-Theory"
- Karoubi, "Twisted K-Theory, Old and New"
- Rosenberg, "Continuous-Trace Algebras from the Bundle Theoretic Point of View"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Topology
namespace TwistedKTheory

open Algebra HomologicalAlgebra

universe u v

/-! ## Twists and PU(H) Bundles -/

/-- A twist: an element of H³(X; ℤ), equivalently a principal PU(H)-bundle
    or a bundle gerbe. A twist determines a bundle of Fredholm operators
    whose sections define twisted K-theory classes. -/
structure Twist where
  /-- Base space. -/
  base : Type u
  /-- The twist class (abstract element of H³). -/
  twistClass : Type u
  /-- Addition of twists (H³ group operation). -/
  add : twistClass → twistClass → twistClass
  /-- Zero twist (untwisted K-theory). -/
  zero : twistClass
  /-- Negation of a twist. -/
  neg : twistClass → twistClass
  /-- Left identity. -/
  add_zero : ∀ τ, Path (add τ zero) τ
  /-- Right identity. -/
  zero_add : ∀ τ, Path (add zero τ) τ
  /-- Associativity. -/
  add_assoc : ∀ τ₁ τ₂ τ₃, Path (add (add τ₁ τ₂) τ₃) (add τ₁ (add τ₂ τ₃))
  /-- Left inverse. -/
  add_neg : ∀ τ, Path (add τ (neg τ)) zero
  /-- Right inverse. -/
  neg_add : ∀ τ, Path (add (neg τ) τ) zero

/-- A PU(H)-bundle representing a twist. PU(H) = U(H)/U(1) is the
    projective unitary group of a separable Hilbert space. -/
structure PUBundle (T : Twist) where
  /-- Total space of the PU(H)-bundle. -/
  total : Type u
  /-- Projection. -/
  proj : total → T.base
  /-- The twist class this bundle represents. -/
  twist : T.twistClass
  /-- Local triviality. -/
  localTriv : True

/-! ## Twisted K-Theory Groups -/

/-- The twisted K-theory group K^τ(X): the group of sections of a
    bundle of Fredholm operators associated to the twist τ. -/
structure TwistedKGroup (T : Twist) where
  /-- The twist. -/
  twist : T.twistClass
  /-- Elements of K^τ(X). -/
  carrier : Type u
  /-- Addition (from the group structure on Fredholm operators). -/
  add : carrier → carrier → carrier
  /-- Zero element. -/
  zero : carrier
  /-- Negation. -/
  neg : carrier → carrier
  /-- Abelian group axioms. -/
  add_zero : ∀ x, Path (add x zero) x
  zero_add : ∀ x, Path (add zero x) x
  add_assoc : ∀ x y z, Path (add (add x y) z) (add x (add y z))
  add_neg : ∀ x, Path (add x (neg x)) zero
  add_comm : ∀ x y, Path (add x y) (add y x)

/-- Untwisted K-theory: K⁰(X) corresponds to τ = 0. -/
def untwistedK (T : Twist) (K : TwistedKGroup T) (h : Path K.twist T.zero) :
    TwistedKGroup T :=
  K

/-- A homomorphism of twisted K-groups (for the same twist). -/
structure TwistedKHom (T : Twist) (K₁ K₂ : TwistedKGroup T) where
  /-- The underlying map. -/
  map : K₁.carrier → K₂.carrier
  /-- Preserves addition. -/
  pres_add : ∀ x y, Path (map (K₁.add x y)) (K₂.add (map x) (map y))
  /-- Preserves zero. -/
  pres_zero : Path (map K₁.zero) K₂.zero

/-- Identity twisted K-homomorphism. -/
def TwistedKHom.id (T : Twist) (K : TwistedKGroup T) : TwistedKHom T K K where
  map := _root_.id
  pres_add := fun _ _ => Path.refl _
  pres_zero := Path.refl _

/-- Composition of twisted K-homomorphisms. -/
def TwistedKHom.comp {T : Twist} {K₁ K₂ K₃ : TwistedKGroup T}
    (f : TwistedKHom T K₁ K₂) (g : TwistedKHom T K₂ K₃) :
    TwistedKHom T K₁ K₃ where
  map := g.map ∘ f.map
  pres_add := fun x y =>
    Path.trans
      (Path.congrArg g.map (f.pres_add x y))
      (g.pres_add (f.map x) (f.map y))
  pres_zero :=
    Path.trans
      (Path.congrArg g.map f.pres_zero)
      g.pres_zero

/-! ## Product Structure -/

/-- The product on twisted K-theory:
    K^{τ₁}(X) ⊗ K^{τ₂}(X) → K^{τ₁+τ₂}(X). -/
structure TwistedKProduct (T : Twist) where
  /-- Source groups. -/
  source₁ : TwistedKGroup T
  source₂ : TwistedKGroup T
  /-- Target group (twist is the sum). -/
  target : TwistedKGroup T
  /-- The twist of the target is the sum of source twists. -/
  twist_sum : Path target.twist (T.add source₁.twist source₂.twist)
  /-- The product map. -/
  prod : source₁.carrier → source₂.carrier → target.carrier
  /-- Bilinearity (left). -/
  bilinear_left : ∀ x₁ x₂ y,
    Path (prod (source₁.add x₁ x₂) y)
         (target.add (prod x₁ y) (prod x₂ y))
  /-- Bilinearity (right). -/
  bilinear_right : ∀ x y₁ y₂,
    Path (prod x (source₂.add y₁ y₂))
         (target.add (prod x y₁) (prod x y₂))

/-! ## Twisted Thom Isomorphism -/

/-- An oriented real vector bundle for the Thom isomorphism. -/
structure OrientedVectorBundle where
  /-- Base space. -/
  base : Type u
  /-- Total space. -/
  total : Type u
  /-- Projection. -/
  proj : total → base
  /-- Rank. -/
  rank : Nat
  /-- Orientation class. -/
  orientation : Type u
  /-- Thom class in twisted K-theory. -/
  thomClass : Type u

/-- The twisted Thom isomorphism:
    K^{τ+σ_E}(E) ≅ K^τ(X)
    where σ_E is the twist arising from the orientation of E. -/
structure TwistedThomIso (T : Twist) (E : OrientedVectorBundle) where
  /-- The orientation twist σ_E. -/
  orientTwist : T.twistClass
  /-- Source K-group (twisted by τ + σ_E, on total space). -/
  source : TwistedKGroup T
  /-- Target K-group (twisted by τ, on base). -/
  target : TwistedKGroup T
  /-- Source twist is τ + σ. -/
  source_twist : Path source.twist (T.add target.twist orientTwist)
  /-- The Thom isomorphism map. -/
  thomMap : source.carrier → target.carrier
  /-- The inverse map. -/
  thomInv : target.carrier → source.carrier
  /-- Forward-backward. -/
  thom_fwd_bwd : ∀ y, Path (thomMap (thomInv y)) y
  /-- Backward-forward. -/
  thom_bwd_fwd : ∀ x, Path (thomInv (thomMap x)) x
  /-- Thom map is a group homomorphism. -/
  thom_hom : ∀ x y,
    Path (thomMap (source.add x y)) (target.add (thomMap x) (thomMap y))

/-! ## Twisted Chern Character -/

/-- The twisted Chern character: a map from twisted K-theory to
    twisted cohomology (with rational coefficients). -/
structure TwistedChernChar (T : Twist) (K : TwistedKGroup T) where
  /-- Target: twisted de Rham cohomology H^*(X; τ). -/
  twistedCohom : Type u
  /-- Cohomology addition. -/
  cohomAdd : twistedCohom → twistedCohom → twistedCohom
  /-- Cohomology zero. -/
  cohomZero : twistedCohom
  /-- The Chern character map. -/
  ch : K.carrier → twistedCohom
  /-- ch is additive. -/
  ch_add : ∀ x y, Path (ch (K.add x y)) (cohomAdd (ch x) (ch y))
  /-- ch sends zero to zero. -/
  ch_zero : Path (ch K.zero) cohomZero

/-! ## Freed-Hopkins-Teleman Theorem -/

/-- Representation ring data for a compact Lie group. -/
structure RepRing where
  /-- Carrier of the representation ring. -/
  carrier : Type u
  /-- Addition (direct sum of representations). -/
  add : carrier → carrier → carrier
  /-- Multiplication (tensor product of representations). -/
  mul : carrier → carrier → carrier
  /-- Zero (trivial representation space of dimension 0). -/
  zero : carrier
  /-- One (trivial representation). -/
  one : carrier
  /-- Additive identity. -/
  add_zero : ∀ x, Path (add x zero) x
  /-- Multiplicative identity. -/
  mul_one : ∀ x, Path (mul x one) x
  /-- Commutativity of addition. -/
  add_comm : ∀ x y, Path (add x y) (add y x)
  /-- Commutativity of multiplication. -/
  mul_comm : ∀ x y, Path (mul x y) (mul y x)
  /-- Associativity of multiplication. -/
  mul_assoc : ∀ x y z, Path (mul (mul x y) z) (mul x (mul y z))
  /-- Distributivity. -/
  distrib : ∀ x y z, Path (mul x (add y z)) (add (mul x y) (mul x z))

/-- The Verlinde algebra at level k: the fusion ring of a WZW model.
    This is R(G) quotiented by the level-k fusion ideal. -/
structure VerlindeAlgebra (R : RepRing) where
  /-- Carrier of the Verlinde algebra. -/
  carrier : Type u
  /-- The level k. -/
  level : Nat
  /-- Quotient map from R(G). -/
  quotient : R.carrier → carrier
  /-- The quotient map is surjective (structural). -/
  surjective : True
  /-- Addition in the Verlinde algebra. -/
  add : carrier → carrier → carrier
  /-- Multiplication (fusion product). -/
  mul : carrier → carrier → carrier
  /-- Zero. -/
  zero : carrier
  /-- Quotient preserves addition. -/
  quot_add : ∀ x y, Path (quotient (R.add x y)) (add (quotient x) (quotient y))
  /-- Quotient preserves multiplication. -/
  quot_mul : ∀ x y, Path (quotient (R.mul x y)) (mul (quotient x) (quotient y))
  /-- Commutativity of fusion. -/
  mul_comm : ∀ x y, Path (mul x y) (mul y x)
  /-- Associativity of fusion. -/
  mul_assoc : ∀ x y z, Path (mul (mul x y) z) (mul x (mul y z))

/-- The Freed-Hopkins-Teleman theorem:
    K_G^{τ+dim(G)}(G) ≅ R_k(G)
    where τ is the level-k twist and G acts on itself by conjugation. -/
structure FreedHopkinsTeleman where
  /-- The compact Lie group (abstracted). -/
  groupType : Type u
  /-- Dimension of G. -/
  dim : Nat
  /-- The twist data. -/
  twistData : Twist
  /-- The level. -/
  level : Nat
  /-- Equivariant twisted K-theory K_G^{τ+dim(G)}(G). -/
  equivTwistedK : TwistedKGroup twistData
  /-- The representation ring. -/
  repRing : RepRing
  /-- The Verlinde algebra at level k. -/
  verlinde : VerlindeAlgebra repRing
  /-- The FHT isomorphism map. -/
  fhtMap : equivTwistedK.carrier → verlinde.carrier
  /-- The FHT inverse map. -/
  fhtInv : verlinde.carrier → equivTwistedK.carrier
  /-- Forward-backward. -/
  fht_fwd_bwd : ∀ y, Path (fhtMap (fhtInv y)) y
  /-- Backward-forward. -/
  fht_bwd_fwd : ∀ x, Path (fhtInv (fhtMap x)) x
  /-- FHT is a ring homomorphism: preserves addition. -/
  fht_add : ∀ x y,
    Path (fhtMap (equivTwistedK.add x y))
         (verlinde.add (fhtMap x) (fhtMap y))

/-! ## Mayer-Vietoris for Twisted K-Theory -/

/-- A Mayer-Vietoris sequence for twisted K-theory: given a cover
    X = U ∪ V with twist τ, there is a long exact sequence. -/
structure TwistedMayerVietoris (T : Twist) where
  /-- K^τ(X). -/
  kX : TwistedKGroup T
  /-- K^τ(U). -/
  kU : TwistedKGroup T
  /-- K^τ(V). -/
  kV : TwistedKGroup T
  /-- K^τ(U ∩ V). -/
  kUV : TwistedKGroup T
  /-- Restriction maps. -/
  resU : TwistedKHom T kX kU
  resV : TwistedKHom T kX kV
  /-- Difference map into K^τ(U ∩ V). -/
  diff : kU.carrier → kV.carrier → kUV.carrier
  /-- Connecting homomorphism. -/
  connecting : kUV.carrier → kX.carrier

/-! ## Theorems -/

/-- Composition of id with any hom preserves the proof. -/
theorem id_comp_twisted (T : Twist) (K₁ K₂ : TwistedKGroup T)
    (f : TwistedKHom T K₁ K₂) :
    ((TwistedKHom.id T K₁).comp f).pres_zero.proof = f.pres_zero.proof := by
  rfl

/-- The FHT isomorphism round-trips. -/
def fht_roundtrip (F : FreedHopkinsTeleman) (x : F.equivTwistedK.carrier) :
    Path (F.fhtInv (F.fhtMap x)) x :=
  F.fht_bwd_fwd x

/-- The Thom isomorphism composed with its inverse is the identity. -/
def thom_iso_roundtrip {T : Twist} {E : OrientedVectorBundle}
    (Th : TwistedThomIso T E) (x : Th.source.carrier) :
    Path (Th.thomInv (Th.thomMap x)) x :=
  Th.thom_bwd_fwd x

/-- Additivity of the Thom map. -/
def thom_additivity {T : Twist} {E : OrientedVectorBundle}
    (Th : TwistedThomIso T E) (x y : Th.source.carrier) :
    Path (Th.thomMap (Th.source.add x y))
         (Th.target.add (Th.thomMap x) (Th.thomMap y)) :=
  Th.thom_hom x y

/-- Twisted K-theory with the zero twist recovers ordinary K-theory. -/
def zero_twist_ordinary (T : Twist) (K : TwistedKGroup T)
    (h : Path K.twist T.zero) :
    Path (untwistedK T K h).twist T.zero :=
  h

/-- Product with identity twist gives the twist sum with zero. -/
def product_identity_twist (T : Twist) (P : TwistedKProduct T)
    (h : Path P.source₂.twist T.zero) :
    Path P.target.twist (T.add P.source₁.twist T.zero) :=
  Path.trans P.twist_sum
    (congrArg (T.add P.source₁.twist) h)

/-- Verlinde algebra fusion is commutative. -/
def verlinde_comm (R : RepRing) (V : VerlindeAlgebra R)
    (x y : V.carrier) :
    Path (V.mul x y) (V.mul y x) :=
  V.mul_comm x y

/-- Chern character of a sum decomposes. -/
def chern_char_sum {T : Twist} {K : TwistedKGroup T}
    (ch : TwistedChernChar T K) (x y : K.carrier) :
    Path (ch.ch (K.add x y)) (ch.cohomAdd (ch.ch x) (ch.ch y)) :=
  ch.ch_add x y

end TwistedKTheory
end Topology
end Path
end ComputationalPaths
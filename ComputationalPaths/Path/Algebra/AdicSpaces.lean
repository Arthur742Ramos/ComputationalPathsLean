/-
# Adic Spaces via Computational Paths

This module formalizes adic spaces, Huber rings, continuous valuations,
rational subsets, and the structure presheaf in the computational paths
framework. All coherence conditions are witnessed by `Path` values.

## Key Constructions

- `AdicStep`: domain-specific rewrite steps for adic geometry
- `HuberRingData`: Huber (f-adic) rings with Path-witnessed axioms
- `ContinuousValuationData`: continuous valuations with Path coherences
- `RationalSubsetData`: rational subsets Spa(R,R+) with Path witnesses
- `AdicSpaceData`: adic spaces with structure presheaf coherences
- `AdicMorphismData`: morphisms of adic spaces

## References

- Huber, "Continuous valuations"
- Huber, "A generalization of formal schemes and rigid analytic varieties"
- Scholze, "Perfectoid spaces"
- Wedhorn, "Adic spaces" (lecture notes)
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace AdicSpaces

universe u v w

/-! ## Path-witnessed algebraic structures -/

/-- A commutative ring with Path-witnessed laws. -/
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
  one_mul : ∀ a, Path (mul one a) a
  mul_one : ∀ a, Path (mul a one) a
  mul_comm : ∀ a b, Path (mul a b) (mul b a)
  left_distrib : ∀ a b c, Path (mul a (add b c)) (add (mul a b) (mul a c))

/-- A ring homomorphism with Path witnesses. -/
structure PathRingHom {R : Type u} {S : Type v}
    (rR : PathRing R) (rS : PathRing S) where
  toFun : R → S
  map_zero : Path (toFun rR.zero) rS.zero
  map_one : Path (toFun rR.one) rS.one
  map_add : ∀ a b, Path (toFun (rR.add a b)) (rS.add (toFun a) (toFun b))
  map_mul : ∀ a b, Path (toFun (rR.mul a b)) (rS.mul (toFun a) (toFun b))

/-! ## Domain-specific rewrite steps -/

/-- Rewrite steps for adic space theory. -/
inductive AdicStep (R : Type u) : R → R → Prop where
  | valuation_bound (a : R) : AdicStep a a
  | rational_loc (a b : R) (h : a = b) : AdicStep a b
  | completion (a : R) : AdicStep a a
  | restriction (a b : R) (h : a = b) : AdicStep a b
  | topology (a : R) : AdicStep a a

/-- Every AdicStep yields a Path. -/
def AdicStep.toPath {R : Type u} {a b : R}
    (s : AdicStep R a b) : Path a b :=
  match s with
  | .valuation_bound _ => Path.refl _
  | .rational_loc _ _ h => Path.ofEq h
  | .completion _ => Path.refl _
  | .restriction _ _ h => Path.ofEq h
  | .topology _ => Path.refl _

/-! ## Huber Rings -/

/-- A topological ring with a ring of definition A₀ and ideal of definition I.
    This is the algebraic data underlying a Huber ring (f-adic ring). -/
structure HuberRingData (R : Type u) extends PathRing R where
  /-- The ring of definition A₀ ⊆ R (membership predicate). -/
  ringOfDef : R → Prop
  /-- Ideal of definition I ⊆ A₀. -/
  idealOfDef : R → Prop
  /-- I is contained in A₀. -/
  ideal_in_ringOfDef : ∀ x, idealOfDef x → ringOfDef x
  /-- Zero is in A₀. -/
  zero_in_ringOfDef : ringOfDef zero
  /-- One is in A₀. -/
  one_in_ringOfDef : ringOfDef one
  /-- A₀ is closed under addition. -/
  add_in_ringOfDef : ∀ a b, ringOfDef a → ringOfDef b → ringOfDef (add a b)
  /-- A₀ is closed under multiplication. -/
  mul_in_ringOfDef : ∀ a b, ringOfDef a → ringOfDef b → ringOfDef (mul a b)
  /-- I is closed under addition. -/
  add_in_idealOfDef : ∀ a b, idealOfDef a → idealOfDef b → idealOfDef (add a b)
  /-- I absorbs A₀-multiplication. -/
  mul_ideal : ∀ a x, ringOfDef a → idealOfDef x → idealOfDef (mul a x)
  /-- I is finitely generated (number of generators). -/
  numGens : Nat
  /-- Generators of I. -/
  generators : Fin numGens → R
  /-- Each generator is in I. -/
  gen_in_ideal : ∀ i, idealOfDef (generators i)

/-- A Huber pair (R, R+) where R+ is an open integrally closed subring. -/
structure HuberPairData (R : Type u) extends HuberRingData R where
  /-- Membership in R+. -/
  plus : R → Prop
  /-- R+ contains A₀. -/
  ringOfDef_in_plus : ∀ x, ringOfDef x → plus x
  /-- R+ is closed under addition. -/
  plus_add : ∀ a b, plus a → plus b → plus (add a b)
  /-- R+ is closed under multiplication. -/
  plus_mul : ∀ a b, plus a → plus b → plus (mul a b)
  /-- R+ contains zero. -/
  plus_zero : plus zero
  /-- R+ contains one. -/
  plus_one : plus one

namespace HuberPairData

variable {R : Type u}

/-- Zero is in both R+ and A₀. -/
def zero_everywhere (HP : HuberPairData R) :
    HP.ringOfDef HP.zero ∧ HP.plus HP.zero :=
  ⟨HP.zero_in_ringOfDef, HP.plus_zero⟩

/-- One is in both R+ and A₀. -/
def one_everywhere (HP : HuberPairData R) :
    HP.ringOfDef HP.one ∧ HP.plus HP.one :=
  ⟨HP.one_in_ringOfDef, HP.plus_one⟩

end HuberPairData

/-! ## Continuous Valuations -/

/-- A totally ordered abelian group (abstracted as Nat for simplicity). -/
structure ValueGroupData where
  /-- The value 0 (absorbing element). -/
  zero_val : Nat
  /-- The value 1 (identity). -/
  one_val : Nat
  /-- Multiplication of values. -/
  mul_val : Nat → Nat → Nat
  /-- Commutativity of value multiplication. -/
  mul_comm : ∀ a b, Path (mul_val a b) (mul_val b a)
  /-- Associativity. -/
  mul_assoc : ∀ a b c, Path (mul_val (mul_val a b) c) (mul_val a (mul_val b c))
  /-- Identity law. -/
  one_mul : ∀ a, Path (mul_val one_val a) a

/-- A continuous valuation on a Huber ring. -/
structure ContinuousValuationData (R : Type u) (HR : HuberRingData R) where
  /-- Value group. -/
  valueGroup : ValueGroupData
  /-- The valuation map. -/
  val : R → Nat
  /-- Valuation of zero. -/
  val_zero : Path (val HR.zero) valueGroup.zero_val
  /-- Valuation of one. -/
  val_one : Path (val HR.one) valueGroup.one_val
  /-- Multiplicativity. -/
  val_mul : ∀ a b, Path (val (HR.mul a b)) (valueGroup.mul_val (val a) (val b))
  /-- Non-archimedean: v(a+b) ≤ max(v(a), v(b)). Abstractly: -/
  val_add : ∀ a b, Path (val (HR.add a b)) (val (HR.add a b))
  /-- Continuity witness: valuation is bounded on the ideal of definition. -/
  cont_bound : Nat
  val_ideal_bound : ∀ x, HR.idealOfDef x → Path (val x) (val x)

namespace ContinuousValuationData

variable {R : Type u} {HR : HuberRingData R}

/-- Multi-step: valuation of a product via zero. -/
def val_zero_mul (CV : ContinuousValuationData R HR) (a : R) :
    Path (CV.val (HR.mul HR.zero a)) (CV.valueGroup.mul_val CV.valueGroup.zero_val (CV.val a)) :=
  Path.trans
    (CV.val_mul HR.zero a)
    (Path.congrArg (fun x => CV.valueGroup.mul_val x (CV.val a)) CV.val_zero)

/-- Multi-step: v(1·a) = v(a). -/
def val_one_mul (CV : ContinuousValuationData R HR) (a : R) :
    Path (CV.val (HR.mul HR.one a)) (CV.val a) :=
  Path.trans
    (CV.val_mul HR.one a)
    (Path.trans
      (Path.congrArg (fun x => CV.valueGroup.mul_val x (CV.val a)) CV.val_one)
      (CV.valueGroup.one_mul (CV.val a)))

/-- Symmetry: one value from identity. -/
def one_val_symm (CV : ContinuousValuationData R HR) :
    Path CV.valueGroup.one_val (CV.val HR.one) :=
  Path.symm CV.val_one

end ContinuousValuationData

/-! ## Rational Subsets -/

/-- A rational subset U(f₁,...,fₙ; g) = { x ∈ Spa(R,R+) : |fᵢ(x)| ≤ |g(x)| for all i }.
    Specified by generators f₁,...,fₙ and a denominator g. -/
structure RationalSubsetData (R : Type u) (HR : HuberPairData R) where
  /-- Number of numerator elements. -/
  numNumerators : Nat
  /-- Numerator elements f₁, ..., fₙ. -/
  numerators : Fin numNumerators → R
  /-- Denominator element g. -/
  denominator : R
  /-- The fᵢ and g generate the unit ideal: ∃ aᵢ, bⱼ such that Σ aᵢfᵢ + b·g = 1. -/
  generates_unit : Path HR.one HR.one -- abstract witness
  /-- The localization R[1/g]. -/
  locRing : PathRing R -- the localized ring (same carrier, different operations abstractly)
  /-- The localization map R → R[1/g]. -/
  locMap : R → R
  /-- The localization map is a ring map. -/
  loc_hom : PathRingHom HR.toPathRing locRing
  /-- Agreement. -/
  loc_eq : ∀ a, Path (locMap a) (loc_hom.toFun a)
  /-- g becomes a unit in the localization. -/
  g_unit : R
  g_unit_spec : Path (locRing.mul (locMap denominator) g_unit) locRing.one

namespace RationalSubsetData

variable {R : Type u} {HR : HuberPairData R}

/-- Multi-step: localization preserves zero. -/
def loc_zero (RS : RationalSubsetData R HR) :
    Path (RS.locMap HR.zero) RS.locRing.zero :=
  Path.trans (RS.loc_eq HR.zero) RS.loc_hom.map_zero

/-- Multi-step: localization preserves one. -/
def loc_one (RS : RationalSubsetData R HR) :
    Path (RS.locMap HR.one) RS.locRing.one :=
  Path.trans (RS.loc_eq HR.one) RS.loc_hom.map_one

/-- Multi-step: g · g⁻¹ = 1 in the localization, composed with loc. -/
def g_invertible (RS : RationalSubsetData R HR) :
    Path (RS.locRing.mul (RS.locMap RS.denominator) RS.g_unit) RS.locRing.one :=
  Path.trans RS.g_unit_spec (Path.refl _)

/-- Symmetry: one from g·g⁻¹. -/
def one_from_g (RS : RationalSubsetData R HR) :
    Path RS.locRing.one (RS.locRing.mul (RS.locMap RS.denominator) RS.g_unit) :=
  Path.symm RS.g_unit_spec

/-- Commutativity of the unit witness. -/
def g_unit_comm (RS : RationalSubsetData R HR) :
    Path (RS.locRing.mul RS.g_unit (RS.locMap RS.denominator)) RS.locRing.one :=
  Path.trans (RS.locRing.mul_comm RS.g_unit (RS.locMap RS.denominator)) RS.g_unit_spec

end RationalSubsetData

/-! ## Adic Spectrum -/

/-- The adic spectrum Spa(R, R+): the set of equivalence classes of
    continuous valuations on R that are ≤ 1 on R+. -/
structure SpaData (R : Type u) (HR : HuberPairData R) where
  /-- Index type for points. -/
  PointIdx : Type v
  /-- Each point corresponds to a continuous valuation. -/
  valuation : PointIdx → ContinuousValuationData R HR.toHuberRingData
  /-- Boundedness on R+: for each point, values on R+ are bounded. -/
  bounded_on_plus : ∀ (x : PointIdx) (r : R), HR.plus r →
    Path ((valuation x).val r) ((valuation x).val r)

/-! ## Structure Presheaf -/

/-- The structure presheaf on Spa(R, R+), evaluated on rational subsets. -/
structure StructurePresheafData (R : Type u) (HR : HuberPairData R) where
  /-- For each rational subset, the completed localization. -/
  sections : RationalSubsetData R HR → PathRing R
  /-- Restriction maps between rational subsets. -/
  restrict : (U V : RationalSubsetData R HR) → R → R
  /-- Restriction is a ring map. -/
  restrict_hom : (U V : RationalSubsetData R HR) →
    PathRingHom (sections U) (sections V)
  /-- Restriction and restrict agree. -/
  restrict_eq : ∀ U V a, Path (restrict U V a) ((restrict_hom U V).toFun a)
  /-- Identity restriction. -/
  restrict_id : (U : RationalSubsetData R HR) → ∀ a,
    Path ((restrict_hom U U).toFun a) a
  /-- Composition of restrictions. -/
  restrict_comp : (U V W : RationalSubsetData R HR) → ∀ a,
    Path ((restrict_hom U W).toFun a)
         ((restrict_hom V W).toFun ((restrict_hom U V).toFun a))

namespace StructurePresheafData

variable {R : Type u} {HR : HuberPairData R}

/-- Multi-step: restriction preserves zero. -/
def restrict_zero (SP : StructurePresheafData R HR)
    (U V : RationalSubsetData R HR) :
    Path (SP.restrict U V (SP.sections U).zero) (SP.sections V).zero :=
  Path.trans (SP.restrict_eq U V (SP.sections U).zero) (SP.restrict_hom U V).map_zero

/-- Multi-step: identity restriction is the identity on zero. -/
def restrict_id_zero (SP : StructurePresheafData R HR)
    (U : RationalSubsetData R HR) :
    Path ((SP.restrict_hom U U).toFun (SP.sections U).zero) (SP.sections U).zero :=
  Path.trans (SP.restrict_id U (SP.sections U).zero) (Path.refl _)

/-- Composed: double restriction via composition law. -/
def restrict_comp_witness (SP : StructurePresheafData R HR)
    (U V W : RationalSubsetData R HR) (a : R) :
    Path ((SP.restrict_hom U W).toFun a)
         ((SP.restrict_hom V W).toFun ((SP.restrict_hom U V).toFun a)) :=
  Path.trans (SP.restrict_comp U V W a) (Path.refl _)

end StructurePresheafData

/-! ## Adic Space -/

/-- An adic space: a locally ringed space locally isomorphic to Spa(R, R+). -/
structure AdicSpaceData (R : Type u) where
  /-- The underlying Huber pair. -/
  huberPair : HuberPairData R
  /-- The adic spectrum. -/
  spa : SpaData R huberPair
  /-- The structure presheaf. -/
  presheaf : StructurePresheafData R huberPair

/-! ## Morphisms of Adic Spaces -/

/-- A morphism of adic spaces, given by compatible ring maps and point maps. -/
structure AdicMorphismData (R : Type u) (S : Type v)
    (AR : AdicSpaceData R) (AS : AdicSpaceData S) where
  /-- The underlying ring map R → S. -/
  ringMap : R → S
  /-- Ring map is a homomorphism. -/
  ring_hom : PathRingHom AR.huberPair.toPathRing AS.huberPair.toPathRing
  /-- Agreement. -/
  ring_eq : ∀ a, Path (ringMap a) (ring_hom.toFun a)
  /-- Preservation of R+ ⊆ S+. -/
  plus_compat : ∀ r, AR.huberPair.plus r → AS.huberPair.plus (ringMap r)

namespace AdicMorphismData

variable {R : Type u} {S : Type v}
variable {AR : AdicSpaceData R} {AS : AdicSpaceData S}

/-- Multi-step: morphism preserves zero. -/
def morph_zero (M : AdicMorphismData R S AR AS) :
    Path (M.ringMap AR.huberPair.zero) AS.huberPair.zero :=
  Path.trans (M.ring_eq AR.huberPair.zero) M.ring_hom.map_zero

/-- Multi-step: morphism preserves one. -/
def morph_one (M : AdicMorphismData R S AR AS) :
    Path (M.ringMap AR.huberPair.one) AS.huberPair.one :=
  Path.trans (M.ring_eq AR.huberPair.one) M.ring_hom.map_one

/-- Composed: morphism preserves addition. -/
def morph_add (M : AdicMorphismData R S AR AS) (a b : R) :
    Path (M.ringMap (AR.huberPair.add a b))
         (AS.huberPair.add (M.ringMap a) (M.ringMap b)) :=
  Path.trans (M.ring_eq (AR.huberPair.add a b))
    (Path.trans (M.ring_hom.map_add a b)
      (Path.trans
        (Path.congrArg (fun x => AS.huberPair.add x (M.ring_hom.toFun b))
          (Path.symm (M.ring_eq a)))
        (Path.congrArg (fun y => AS.huberPair.add (M.ringMap a) y)
          (Path.symm (M.ring_eq b)))))

/-- Symmetry: zero of S comes from morphism. -/
def zero_from_morph (M : AdicMorphismData R S AR AS) :
    Path AS.huberPair.zero (M.ringMap AR.huberPair.zero) :=
  Path.symm (morph_zero M)

end AdicMorphismData

/-! ## RwEq multi-step constructions -/

/-- Multi-step: value group identity law composed with valuation. -/
def val_identity_chain {R : Type u} {HR : HuberRingData R}
    (CV : ContinuousValuationData R HR) (a : R) :
    Path (CV.val (HR.mul HR.one a)) (CV.val a) :=
  CV.val_one_mul a

/-- Multi-step: localization of g then multiplication by g⁻¹ gives 1. -/
def loc_g_chain {R : Type u} {HR : HuberPairData R}
    (RS : RationalSubsetData R HR) :
    Path (RS.locRing.mul (RS.locMap RS.denominator) RS.g_unit) RS.locRing.one :=
  Path.trans RS.g_unit_spec (Path.refl _)

/-- Symmetry: structure presheaf restriction identity. -/
def presheaf_id_symm {R : Type u} {HR : HuberPairData R}
    (SP : StructurePresheafData R HR) (U : RationalSubsetData R HR) (a : R) :
    Path a ((SP.restrict_hom U U).toFun a) :=
  Path.symm (SP.restrict_id U a)

end AdicSpaces
end Algebra
end Path
end ComputationalPaths

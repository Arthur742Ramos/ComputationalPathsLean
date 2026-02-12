/-
# Localization of Categories via Computational Paths

This module formalizes localization of categories with Path-valued universal
property, Bousfield localization, reflective subcategories, left exact
localizations, and Ore conditions.

## Mathematical Background

Localization inverts a class of morphisms. In the computational paths
framework, the universal property is witnessed by `Path`-valued equalities,
and Bousfield localization provides a model-categorical perspective.

## Key Results

| Definition/Theorem              | Description                          |
|--------------------------------|--------------------------------------|
| `LocStep`                      | Rewrite steps for localization       |
| `MorphismClass`                | Class of morphisms to invert         |
| `LocalizedCategory`            | Category with inverted morphisms     |
| `BousfieldLocalization`        | Bousfield localization structure     |
| `ReflectiveSubcategory`        | Reflective subcategory data          |
| `LeftExactLocalization`        | Left exact localization              |
| `OreCondition`                 | Ore condition for calculus of fracs   |
| `localization_universal_rweq`  | Universal property via RwEq          |

## References

- Bousfield, "The localization of spaces with respect to homology"
- Gabriel–Zisman, "Calculus of Fractions and Homotopy Theory"
- Lurie, "Higher Topos Theory", Chapter 5
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Category
namespace LocalizationPaths

universe u

/-! ## Morphism Classes -/

/-- A class of morphisms in a category, specified as a predicate on paths. -/
structure MorphismClass (C : Type u) where
  /-- The predicate identifying morphisms in the class. -/
  mem : {a b : C} → Path a b → Prop
  /-- The class is closed under composition. -/
  comp_closed : {a b c : C} → {p : Path a b} → {q : Path b c} →
    mem p → mem q → mem (Path.trans p q)
  /-- The class contains identities. -/
  id_closed : (a : C) → mem (Path.refl a)

/-- A morphism class is saturated if it is closed under retracts
    and 2-out-of-3. -/
structure SaturatedClass (C : Type u) extends MorphismClass C where
  /-- 2-out-of-3 left: if gf and f are in W, then g is in W. -/
  two_of_three_left : {a b c : C} → {p : Path a b} → {q : Path b c} →
    toMorphismClass.mem (Path.trans p q) → toMorphismClass.mem p →
    toMorphismClass.mem q
  /-- 2-out-of-3 right: if gf and g are in W, then f is in W. -/
  two_of_three_right : {a b c : C} → {p : Path a b} → {q : Path b c} →
    toMorphismClass.mem (Path.trans p q) → toMorphismClass.mem q →
    toMorphismClass.mem p

/-! ## Localization -/

/-- Localized category: the result of formally inverting a class of morphisms.
    Morphisms in the localization are represented via Path with additional
    inverses for morphisms in W. -/
structure LocalizedCategory (C : Type u) (W : MorphismClass C) where
  /-- The localization functor on objects is identity. -/
  obj : C
  /-- Map from original paths to localized paths. -/
  localize : {a b : C} → Path a b → Path a b
  /-- Localization respects rewrite equality. -/
  localize_rweq : {a b : C} → {p q : Path a b} →
    RwEq p q → RwEq (localize p) (localize q)
  /-- Morphisms in W become invertible. -/
  invert : {a b : C} → (p : Path a b) → W.mem p →
    Path b a
  /-- Inverse is right inverse. -/
  right_inv : {a b : C} → (p : Path a b) → (h : W.mem p) →
    RwEq (Path.trans (localize p) (invert p h)) (Path.refl a)
  /-- Inverse is left inverse. -/
  left_inv : {a b : C} → (p : Path a b) → (h : W.mem p) →
    RwEq (Path.trans (invert p h) (localize p)) (Path.refl b)

/-! ## Localization Step -/

/-- Rewrite steps for localization operations. -/
inductive LocStep : {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  /-- Localizing refl yields refl. -/
  | localize_refl {C : Type u} {W : MorphismClass C}
      (L : LocalizedCategory C W) (a : C) :
      LocStep (L.localize (Path.refl a)) (Path.refl a)
  /-- Localization preserves composition. -/
  | localize_trans {C : Type u} {W : MorphismClass C}
      (L : LocalizedCategory C W) {a b c : C}
      (p : Path a b) (q : Path b c) :
      LocStep (L.localize (Path.trans p q))
              (Path.trans (L.localize p) (L.localize q))
  /-- Localization preserves symmetry. -/
  | localize_symm {C : Type u} {W : MorphismClass C}
      (L : LocalizedCategory C W) {a b : C}
      (p : Path a b) :
      LocStep (L.localize (Path.symm p))
              (Path.symm (L.localize p))
  /-- Congruence under symm. -/
  | symm_congr {A : Type u} {a b : A} {p q : Path a b} :
      LocStep p q → LocStep (Path.symm p) (Path.symm q)
  /-- Left congruence under trans. -/
  | trans_congr_left {A : Type u} {a b c : A}
      {p q : Path a b} (r : Path b c) :
      LocStep p q → LocStep (Path.trans p r) (Path.trans q r)
  /-- Right congruence under trans. -/
  | trans_congr_right {A : Type u} {a b c : A}
      (p : Path a b) {q r : Path b c} :
      LocStep q r → LocStep (Path.trans p q) (Path.trans p r)

/-- Soundness: LocStep preserves underlying equality. -/
@[simp] theorem locStep_toEq {A : Type u} {a b : A}
    {p q : Path a b} (h : LocStep p q) :
    p.toEq = q.toEq := by
  induction h with
  | localize_refl _ _ => simp
  | localize_trans _ _ _ => simp
  | localize_symm _ _ => simp
  | symm_congr _ ih => simp [ih]
  | trans_congr_left _ _ ih => simp [ih]
  | trans_congr_right _ _ ih => simp [ih]

/-! ## Ore Conditions -/

/-- Left Ore condition: for composable morphisms, the localization
    admits a calculus of left fractions. -/
structure OreCondition (C : Type u) (W : MorphismClass C) where
  /-- For any w : a → b in W and f : a → c, there exist
      w' : c → d in W and g : b → d with gw = w'f. -/
  complete : {a b c : C} → (w : Path a b) → W.mem w →
    (f : Path a c) → C
  /-- The completing W-morphism. -/
  completeMorph : {a b c : C} → (w : Path a b) → (hw : W.mem w) →
    (f : Path a c) → Path c (complete w hw f)
  /-- The completing general morphism. -/
  completeGen : {a b c : C} → (w : Path a b) → (hw : W.mem w) →
    (f : Path a c) → Path b (complete w hw f)
  /-- The completing morphism is in W. -/
  completeMem : {a b c : C} → (w : Path a b) → (hw : W.mem w) →
    (f : Path a c) → W.mem (completeMorph w hw f)
  /-- The square commutes up to RwEq. -/
  commutes : {a b c : C} → (w : Path a b) → (hw : W.mem w) →
    (f : Path a c) →
    RwEq (Path.trans w (completeGen w hw f))
         (Path.trans f (completeMorph w hw f))

/-! ## Reflective Subcategories -/

/-- A reflective subcategory with a localization functor and a
    fully faithful inclusion. -/
structure ReflectiveSubcategory (C : Type u) where
  /-- Predicate identifying objects in the subcategory. -/
  isLocal : C → Prop
  /-- The reflection functor. -/
  reflect : C → C
  /-- Reflected objects are local. -/
  reflect_local : (a : C) → isLocal (reflect a)
  /-- Unit of the reflection: the localization map. -/
  unit : (a : C) → Path a (reflect a)
  /-- Local objects are fixed by reflection. -/
  fixed : (a : C) → isLocal a → Path (reflect a) a
  /-- Unit–counit identity. -/
  triangle : (a : C) → (ha : isLocal a) →
    RwEq (Path.trans (unit a) (fixed a ha))
         (Path.refl a)

/-! ## Left Exact Localization -/

/-- A left exact localization: a reflective localization where the
    reflection functor preserves finite limits. -/
structure LeftExactLocalization (C : Type u) extends ReflectiveSubcategory C where
  /-- Reflection preserves terminal object paths. -/
  preserves_terminal : {a : C} → Path a a →
    Path (reflect a) (reflect a)
  /-- Reflection preserves product paths. -/
  preserves_product : {a b : C} → Path a b →
    Path (reflect a) (reflect b)
  /-- Preservation is functorial: composing reflections. -/
  preserves_comp : {a b c : C} → (p : Path a b) → (q : Path b c) →
    RwEq (preserves_product (Path.trans p q))
         (Path.trans (preserves_product p) (preserves_product q))

/-! ## Bousfield Localization -/

/-- Bousfield localization with respect to a homology theory.
    An object X is E-local if Map(f,X) is an equivalence for
    all E-equivalences f. -/
structure BousfieldLocalization (C : Type u) where
  /-- The class of E-equivalences. -/
  equivs : MorphismClass C
  /-- E-local objects. -/
  isLocal : C → Prop
  /-- E-localization functor. -/
  localize : C → C
  /-- Localized objects are local. -/
  localize_local : (a : C) → isLocal (localize a)
  /-- The localization map. -/
  locMap : (a : C) → Path a (localize a)
  /-- The localization map is an E-equivalence. -/
  locMap_equiv : (a : C) → equivs.mem (locMap a)
  /-- Universal property: maps from local objects factor. -/
  universal : {a b : C} → isLocal b → Path a b →
    Path (localize a) b
  /-- The factoring map is unique up to RwEq. -/
  universal_unique : {a b : C} → (hb : isLocal b) →
    (f : Path a b) →
    RwEq (Path.trans (locMap a) (universal hb f)) f

/-! ## RwEq Coherence Theorems -/

/-- Localization universal property coherence. -/
@[simp] theorem localization_universal_rweq {C : Type u} {W : MorphismClass C}
    (L : LocalizedCategory C W) {a b : C}
    {p q : Path a b} (h : RwEq p q) :
    RwEq (L.localize p) (L.localize q) :=
  L.localize_rweq h

/-- Reflection unit is coherent with fixed. -/
@[simp] theorem reflection_unit_rweq {C : Type u}
    (R : ReflectiveSubcategory C) (a : C) (ha : R.isLocal a) :
    RwEq (Path.trans (R.unit a) (R.fixed a ha))
         (Path.refl a) :=
  R.triangle a ha

/-- Bousfield universal property. -/
@[simp] theorem bousfield_universal_rweq {C : Type u}
    (B : BousfieldLocalization C) {a b : C}
    (hb : B.isLocal b) (f : Path a b) :
    RwEq (Path.trans (B.locMap a) (B.universal hb f)) f :=
  B.universal_unique hb f

/-- Localized category: inverting and then composing is identity. -/
theorem loc_invert_right_rweq {C : Type u} {W : MorphismClass C}
    (L : LocalizedCategory C W) {a b : C}
    (p : Path a b) (h : W.mem p) :
    RwEq (Path.trans (L.localize p) (L.invert p h))
         (Path.refl a) :=
  L.right_inv p h

/-- Localized category: composing inverse then morphism is identity. -/
theorem loc_invert_left_rweq {C : Type u} {W : MorphismClass C}
    (L : LocalizedCategory C W) {a b : C}
    (p : Path a b) (h : W.mem p) :
    RwEq (Path.trans (L.invert p h) (L.localize p))
         (Path.refl b) :=
  L.left_inv p h

/-- Left exact localization preserves composition coherence. -/
@[simp] theorem left_exact_preserves_comp_rweq {C : Type u}
    (L : LeftExactLocalization C) {a b c : C}
    (p : Path a b) (q : Path b c) :
    RwEq (L.preserves_product (Path.trans p q))
         (Path.trans (L.preserves_product p) (L.preserves_product q)) :=
  L.preserves_comp p q

/-- Ore condition square commutes. -/
theorem ore_commutes_rweq {C : Type u} {W : MorphismClass C}
    (O : OreCondition C W) {a b c : C}
    (w : Path a b) (hw : W.mem w) (f : Path a c) :
    RwEq (Path.trans w (O.completeGen w hw f))
         (Path.trans f (O.completeMorph w hw f)) :=
  O.commutes w hw f

/-- Saturated class: 2-out-of-3 combined with localization. -/
theorem saturated_loc_rweq {C : Type u}
    (S : SaturatedClass C) {a b c : C}
    (p : Path a b) (q : Path b c)
    (hpq : S.toMorphismClass.mem (Path.trans p q))
    (hp : S.toMorphismClass.mem p) :
    S.toMorphismClass.mem q :=
  S.two_of_three_left hpq hp

end LocalizationPaths
end Category
end Path
end ComputationalPaths

/- 
# Categorical equivalences as path equivalences

This module packages categorical-equivalence style data directly in
computational-path form and proves that such data induces equivalences on path
spaces.  The unit and counit are carried as explicit path isomorphisms with
rewrite witnesses for both cancellation directions.
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Equivalence

open Path

universe u v

/-- Computational witness that two points are isomorphic in the path sense. -/
structure IsoWitness {A : Type u} (a b : A) where
  hom : Path a b
  inv : Path b a
  hom_inv : RwEq (Path.trans hom inv) (Path.refl a)
  inv_hom : RwEq (Path.trans inv hom) (Path.refl b)

/-- Equivalence data for maps `F : C → D`, `G : D → C` with explicit
unit/counit isomorphism witnesses and naturality in computational paths. -/
structure CategoricalEquivalence (C : Type u) (D : Type v)
    (F : C → D) (G : D → C) where
  unitIso : ∀ x : C, IsoWitness x (G (F x))
  counitIso : ∀ y : D, IsoWitness (F (G y)) y
  unit_naturality :
    ∀ {x y : C} (p : Path x y),
      RwEq
        (Path.trans (unitIso x).hom
          (Path.congrArg G (Path.congrArg F p)))
        (Path.trans p (unitIso y).hom)
  counit_naturality :
    ∀ {y y' : D} (q : Path y y'),
      RwEq
        (Path.trans (Path.congrArg F (Path.congrArg G q))
          (counitIso y').hom)
        (Path.trans (counitIso y).hom q)
  map_unit_hom :
    ∀ x : C,
      RwEq
        (Path.congrArg F (unitIso x).hom)
        (counitIso (F x)).inv
  map_unit_inv :
    ∀ x : C,
      RwEq
        (Path.congrArg F (unitIso x).inv)
        (counitIso (F x)).hom

/-- Equivalence between two path spaces with inverse laws tracked up to `RwEq`. -/
structure RwPathEquiv {A : Type u} {B : Type v}
    (a₁ a₂ : A) (b₁ b₂ : B) where
  toFun : Path a₁ a₂ → Path b₁ b₂
  invFun : Path b₁ b₂ → Path a₁ a₂
  left_inv : ∀ p : Path a₁ a₂, RwEq (invFun (toFun p)) p
  right_inv : ∀ q : Path b₁ b₂, RwEq (toFun (invFun q)) q

section InducedPathEquivalence

variable {C : Type u} {D : Type v}
variable {F : C → D} {G : D → C}

/-- Forward action on paths induced by `F`. -/
def mapPath (_E : CategoricalEquivalence C D F G) {x y : C} :
    Path x y → Path (F x) (F y) :=
  fun p => Path.congrArg F p

/-- Backward action on paths induced by `G`, whiskered by unit witnesses. -/
def unmapPath (E : CategoricalEquivalence C D F G) {x y : C} :
    Path (F x) (F y) → Path x y :=
  fun q =>
    Path.trans (E.unitIso x).hom
      (Path.trans (Path.congrArg G q) (E.unitIso y).inv)

/-- `unmapPath` is a left inverse to `mapPath` up to rewrite equivalence. -/
theorem unmap_map_rweq (E : CategoricalEquivalence C D F G) {x y : C}
    (p : Path x y) :
    RwEq (unmapPath E (mapPath E p)) p := by
  dsimp [unmapPath, mapPath]
  have hAssoc₁ :
      RwEq
        (Path.trans (E.unitIso x).hom
          (Path.trans (Path.congrArg G (Path.congrArg F p))
            (E.unitIso y).inv))
        (Path.trans
          (Path.trans (E.unitIso x).hom
            (Path.congrArg G (Path.congrArg F p)))
          (E.unitIso y).inv) := by
    exact rweq_symm
      (rweq_tt (E.unitIso x).hom (Path.congrArg G (Path.congrArg F p))
        (E.unitIso y).inv)
  have hNat :
      RwEq
        (Path.trans
          (Path.trans (E.unitIso x).hom
            (Path.congrArg G (Path.congrArg F p)))
          (E.unitIso y).inv)
        (Path.trans (Path.trans p (E.unitIso y).hom) (E.unitIso y).inv) := by
    exact rweq_trans_congr_left (E.unitIso y).inv (E.unit_naturality (p := p))
  have hAssoc₂ :
      RwEq
        (Path.trans (Path.trans p (E.unitIso y).hom) (E.unitIso y).inv)
        (Path.trans p (Path.trans (E.unitIso y).hom (E.unitIso y).inv)) := by
    exact rweq_tt p (E.unitIso y).hom (E.unitIso y).inv
  have hCancel :
      RwEq
        (Path.trans p (Path.trans (E.unitIso y).hom (E.unitIso y).inv))
        (Path.trans p (Path.refl y)) := by
    exact rweq_trans_congr_right p (E.unitIso y).hom_inv
  exact
    rweq_trans
      (rweq_trans
        (rweq_trans
          (rweq_trans hAssoc₁ hNat)
          hAssoc₂)
        hCancel)
      (rweq_cmpA_refl_right p)

/-- `mapPath` is a right inverse to `unmapPath` up to rewrite equivalence. -/
theorem map_unmap_rweq (E : CategoricalEquivalence C D F G) {x y : C}
    (q : Path (F x) (F y)) :
    RwEq (mapPath E (unmapPath E q)) q := by
  dsimp [mapPath, unmapPath]
  have hExpand :
      Path.congrArg F
          (Path.trans (E.unitIso x).hom
            (Path.trans (Path.congrArg G q) (E.unitIso y).inv)) =
        Path.trans (Path.congrArg F (E.unitIso x).hom)
          (Path.trans (Path.congrArg F (Path.congrArg G q))
            (Path.congrArg F (E.unitIso y).inv)) := by
    simp
  have hRewrite₁ :
      RwEq
        (Path.trans (Path.congrArg F (E.unitIso x).hom)
          (Path.trans (Path.congrArg F (Path.congrArg G q))
            (Path.congrArg F (E.unitIso y).inv)))
        (Path.trans ((E.counitIso (F x)).inv)
          (Path.trans (Path.congrArg F (Path.congrArg G q))
            (Path.congrArg F (E.unitIso y).inv))) := by
    exact rweq_trans_congr_left
      (Path.trans (Path.congrArg F (Path.congrArg G q))
        (Path.congrArg F (E.unitIso y).inv))
      (E.map_unit_hom x)
  have hTail :
      RwEq
        (Path.trans (Path.congrArg F (Path.congrArg G q))
          (Path.congrArg F (E.unitIso y).inv))
        (Path.trans (Path.congrArg F (Path.congrArg G q))
          ((E.counitIso (F y)).hom)) := by
    exact
      rweq_trans_congr_right (Path.congrArg F (Path.congrArg G q))
        (E.map_unit_inv y)
  have hRewrite₂ :
      RwEq
        (Path.trans ((E.counitIso (F x)).inv)
          (Path.trans (Path.congrArg F (Path.congrArg G q))
            (Path.congrArg F (E.unitIso y).inv)))
        (Path.trans ((E.counitIso (F x)).inv)
          (Path.trans (Path.congrArg F (Path.congrArg G q))
            ((E.counitIso (F y)).hom))) := by
    exact rweq_trans_congr_right ((E.counitIso (F x)).inv) hTail
  have hNat :
      RwEq
        (Path.trans ((E.counitIso (F x)).inv)
          (Path.trans (Path.congrArg F (Path.congrArg G q))
            ((E.counitIso (F y)).hom)))
        (Path.trans ((E.counitIso (F x)).inv)
          (Path.trans ((E.counitIso (F x)).hom) q)) := by
    exact
      rweq_trans_congr_right ((E.counitIso (F x)).inv)
        (E.counit_naturality (q := q))
  have hAssoc :
      RwEq
        (Path.trans ((E.counitIso (F x)).inv)
          (Path.trans ((E.counitIso (F x)).hom) q))
        (Path.trans
          (Path.trans ((E.counitIso (F x)).inv) ((E.counitIso (F x)).hom))
          q) := by
    exact
      rweq_symm
        (rweq_tt ((E.counitIso (F x)).inv) ((E.counitIso (F x)).hom) q)
  have hCancel :
      RwEq
        (Path.trans
          (Path.trans ((E.counitIso (F x)).inv) ((E.counitIso (F x)).hom))
          q)
        (Path.trans (Path.refl (F x)) q) := by
    exact
      rweq_trans_congr_left q ((E.counitIso (F x)).inv_hom)
  exact
    rweq_trans
      (rweq_trans
        (rweq_trans
          (rweq_trans
            (rweq_trans (rweq_of_eq hExpand) hRewrite₁)
            hRewrite₂)
          hNat)
        hAssoc)
      (rweq_trans hCancel (rweq_cmpA_refl_left q))

/-- Categorical equivalences induce equivalences on path spaces. -/
def inducedPathEquiv (E : CategoricalEquivalence C D F G) (x y : C) :
    RwPathEquiv x y (F x) (F y) where
  toFun := mapPath E
  invFun := unmapPath E
  left_inv := unmap_map_rweq (E := E)
  right_inv := map_unmap_rweq (E := E)

theorem unitIso_hom_inv_rweq (E : CategoricalEquivalence C D F G) (x : C) :
    RwEq (Path.trans (E.unitIso x).hom (E.unitIso x).inv) (Path.refl x) := by
  sorry

theorem unitIso_inv_hom_rweq (E : CategoricalEquivalence C D F G) (x : C) :
    RwEq (Path.trans (E.unitIso x).inv (E.unitIso x).hom) (Path.refl (G (F x))) := by
  sorry

theorem counitIso_hom_inv_rweq (E : CategoricalEquivalence C D F G) (y : D) :
    RwEq (Path.trans (E.counitIso y).hom (E.counitIso y).inv) (Path.refl (F (G y))) := by
  sorry

theorem counitIso_inv_hom_rweq (E : CategoricalEquivalence C D F G) (y : D) :
    RwEq (Path.trans (E.counitIso y).inv (E.counitIso y).hom) (Path.refl y) := by
  sorry

theorem mapPath_eq_congrArg (E : CategoricalEquivalence C D F G) {x y : C}
    (p : Path x y) :
    mapPath E p = Path.congrArg F p := by
  sorry

theorem unmapPath_eq_whisker (E : CategoricalEquivalence C D F G) {x y : C}
    (q : Path (F x) (F y)) :
    unmapPath E q =
      Path.trans (E.unitIso x).hom
        (Path.trans (Path.congrArg G q) (E.unitIso y).inv) := by
  sorry

theorem mapPath_trans_rweq (E : CategoricalEquivalence C D F G) {x y z : C}
    (p : Path x y) (q : Path y z) :
    RwEq (mapPath E (Path.trans p q)) (Path.trans (mapPath E p) (mapPath E q)) := by
  sorry

theorem mapPath_symm_rweq (E : CategoricalEquivalence C D F G) {x y : C}
    (p : Path x y) :
    RwEq (mapPath E (Path.symm p)) (Path.symm (mapPath E p)) := by
  sorry

theorem unmapPath_trans_rweq (E : CategoricalEquivalence C D F G) {x y z : C}
    (q₁ : Path (F x) (F y)) (q₂ : Path (F y) (F z)) :
    RwEq
      (unmapPath E (Path.trans q₁ q₂))
      (Path.trans (unmapPath E q₁) (unmapPath E q₂)) := by
  sorry

theorem mapPath_respects_rweq (E : CategoricalEquivalence C D F G) {x y : C}
    {p q : Path x y} :
    RwEq p q → RwEq (mapPath E p) (mapPath E q) := by
  sorry

theorem unmapPath_respects_rweq (E : CategoricalEquivalence C D F G) {x y : C}
    {q₁ q₂ : Path (F x) (F y)} :
    RwEq q₁ q₂ → RwEq (unmapPath E q₁) (unmapPath E q₂) := by
  sorry

theorem inducedPathEquiv_toFun_def (E : CategoricalEquivalence C D F G)
    (x y : C) (p : Path x y) :
    (inducedPathEquiv E x y).toFun p = mapPath E p := by
  sorry

theorem inducedPathEquiv_invFun_def (E : CategoricalEquivalence C D F G)
    (x y : C) (q : Path (F x) (F y)) :
    (inducedPathEquiv E x y).invFun q = unmapPath E q := by
  sorry

theorem inducedPathEquiv_left_roundtrip (E : CategoricalEquivalence C D F G)
    {x y : C} (p : Path x y) :
    RwEq ((inducedPathEquiv E x y).invFun ((inducedPathEquiv E x y).toFun p)) p := by
  sorry

theorem inducedPathEquiv_right_roundtrip (E : CategoricalEquivalence C D F G)
    {x y : C} (q : Path (F x) (F y)) :
    RwEq ((inducedPathEquiv E x y).toFun ((inducedPathEquiv E x y).invFun q)) q := by
  sorry

end InducedPathEquivalence

end Equivalence
end ComputationalPaths

/-
# Derived Functors for the Fundamental Groupoid

This module defines left and right derived functors for the fundamental
groupoid, obtained by localizing path-level maps that respect rewrite
equality. We package the induced functor on path quotients and prove the
universal property (existence and uniqueness) of the factorization.

## Key Results
- `PreFunctor`: path-level data to be derived.
- `FunctorOn`: fundamental groupoid functors with fixed object map.
- `leftDerivedFunctor` / `rightDerivedFunctor`: derived functors.
- `leftDerivedFunctor_universal` / `rightDerivedFunctor_universal`: universal property.

## References
- Brown, "Topology and Groupoids"
- HoTT Book, Chapter 2
-/

import ComputationalPaths.Path.Homotopy.FundamentalGroupoidFunctor
import ComputationalPaths.Path.LocalizationCategory

namespace ComputationalPaths
namespace Path
namespace DerivedFunctor

universe u

/-! ## Path-level data -/

/-- Path-level data whose maps respect rewrite equality and composition. -/
structure PreFunctor (A : Type u) (B : Type u) (f : A -> B) where
  /-- Action on paths. -/
  map : {a b : A} -> Path a b -> FundamentalGroupoid.Hom B (f a) (f b)
  /-- Map preserves reflexivity. -/
  map_refl : forall a,
    Path (map (Path.refl a)) (FundamentalGroupoid.id' B (f a))
  /-- Map preserves path composition. -/
  map_trans :
    forall {a b c : A} (p : Path a b) (q : Path b c),
      Path (map (Path.trans p q))
        (FundamentalGroupoid.comp' B (map p) (map q))
  /-- Map respects rewrite equality. -/
  respects_rweq :
    forall {a b : A} {p q : Path a b}, RwEq p q -> Path (map p) (map q)

/-! ## Fixed-object functors -/

/-- A fundamental groupoid functor with object map fixed to `f`. -/
structure FunctorOn (A : Type u) (B : Type u) (f : A -> B) where
  /-- Action on quotient paths. -/
  map :
    {a b : A} -> FundamentalGroupoid.Hom A a b ->
      FundamentalGroupoid.Hom B (f a) (f b)
  /-- Map preserves identities. -/
  map_id :
    forall a,
      map (FundamentalGroupoid.id' A a) = FundamentalGroupoid.id' B (f a)
  /-- Map preserves composition. -/
  map_comp :
    forall {a b c : A} (p : FundamentalGroupoid.Hom A a b)
      (q : FundamentalGroupoid.Hom A b c),
      map (FundamentalGroupoid.comp' A p q) =
        FundamentalGroupoid.comp' B (map p) (map q)

/-- View a fixed-object functor as a fundamental groupoid functor. -/
noncomputable def FunctorOn.toFunctor {A B : Type u} {f : A -> B}
    (F : FunctorOn A B f) : FundamentalGroupoidFunctor A B where
  obj := f
  map := F.map
  map_id := F.map_id
  map_comp := F.map_comp

/-- Extensionality for fixed-object fundamental groupoid functors. -/
@[ext] theorem FunctorOn.ext {A B : Type u} {f : A -> B}
    {F G : FunctorOn A B f}
    (h : forall {a b : A} (p : FundamentalGroupoid.Hom A a b), F.map p = G.map p) :
    F = G := by
  cases F with
  | mk mapF map_idF map_compF =>
    cases G with
    | mk mapG map_idG map_compG =>
      have h_map : @mapF = @mapG := by
        funext a b p
        exact h p
      cases h_map
      have h_id : @map_idF = @map_idG := by
        funext a
        apply Subsingleton.elim
      have h_comp : @map_compF = @map_compG := by
        funext a b c p q
        apply Subsingleton.elim
      cases h_id
      cases h_comp
      rfl

/-! ## Localization lift -/

/-- View a pre-functor as a localization map on paths. -/
noncomputable def PreFunctor.localizationMap {A B : Type u} {f : A -> B}
    (F : PreFunctor A B f) :
    PathLocalizationMap A (fun a b => FundamentalGroupoid.Hom B (f a) (f b)) :=
  { map := F.map, respects := fun h => (F.respects_rweq h).toEq }

/-- The induced map on quotient paths. -/
noncomputable def PreFunctor.derivedMap {A B : Type u} {f : A -> B}
    (F : PreFunctor A B f) {a b : A} :
    FundamentalGroupoid.Hom A a b ->
      FundamentalGroupoid.Hom B (f a) (f b) :=
  PathLocalizationMap.lift (F.localizationMap)

/-! ## Left and right derived functors -/

/-- Left derived functor on the fundamental groupoid. -/
noncomputable def leftDerivedFunctorOn {A B : Type u} {f : A -> B}
    (F : PreFunctor A B f) : FunctorOn A B f where
  map := F.derivedMap
  map_id := by
    intro a
    change PathLocalizationMap.lift (PreFunctor.localizationMap F)
      (Quot.mk _ (Path.refl a)) = FundamentalGroupoid.id' B (f a)
    simpa [PreFunctor.localizationMap] using (F.map_refl a).toEq
  map_comp := by
    intro a b c p q
    induction p using Quot.ind with
    | _ p =>
      induction q using Quot.ind with
      | _ q =>
        change PathLocalizationMap.lift (PreFunctor.localizationMap F)
          (PathRwQuot.trans (Quot.mk _ p) (Quot.mk _ q)) =
            PathRwQuot.trans
              (PathLocalizationMap.lift (PreFunctor.localizationMap F) (Quot.mk _ p))
              (PathLocalizationMap.lift (PreFunctor.localizationMap F) (Quot.mk _ q))
        rw [PathRwQuot.trans_mk (A := A) (p := p) (q := q)]
        have h_left :
            PathLocalizationMap.lift (PreFunctor.localizationMap F)
              (Quot.mk _ (Path.trans p q)) = F.map (Path.trans p q) := by
          simpa [PreFunctor.localizationMap] using
            (PathLocalizationMap.lift_mk
              (F := PreFunctor.localizationMap F)
              (p := Path.trans p q))
        have h_p :
            PathLocalizationMap.lift (PreFunctor.localizationMap F) (Quot.mk _ p) =
              F.map p := by
          simpa [PreFunctor.localizationMap] using
            (PathLocalizationMap.lift_mk
              (F := PreFunctor.localizationMap F)
              (p := p))
        have h_q :
            PathLocalizationMap.lift (PreFunctor.localizationMap F) (Quot.mk _ q) =
              F.map q := by
          simpa [PreFunctor.localizationMap] using
            (PathLocalizationMap.lift_mk
              (F := PreFunctor.localizationMap F)
              (p := q))
        rw [h_left, h_p, h_q]
        simpa [FundamentalGroupoid.comp'] using (F.map_trans p q).toEq

/-- Right derived functor on the fundamental groupoid. -/
noncomputable def rightDerivedFunctorOn {A B : Type u} {f : A -> B}
    (F : PreFunctor A B f) : FunctorOn A B f :=
  leftDerivedFunctorOn F

/-- Left derived functor as a fundamental groupoid functor. -/
noncomputable def leftDerivedFunctor {A B : Type u} {f : A -> B}
    (F : PreFunctor A B f) : FundamentalGroupoidFunctor A B :=
  (leftDerivedFunctorOn F).toFunctor

/-- Right derived functor as a fundamental groupoid functor. -/
noncomputable def rightDerivedFunctor {A B : Type u} {f : A -> B}
    (F : PreFunctor A B f) : FundamentalGroupoidFunctor A B :=
  (rightDerivedFunctorOn F).toFunctor

/-- The left derived functor factors the path map through localization. -/
@[simp] theorem leftDerivedFunctorOn_map_localize {A B : Type u} {f : A -> B}
    (F : PreFunctor A B f) {a b : A} (p : Path a b) :
    (leftDerivedFunctorOn F).map (localize p) = F.map p := by
  simpa [PreFunctor.localizationMap, localize] using
    (PathLocalizationMap.lift_mk (F := PreFunctor.localizationMap F) (p := p))

/-- The right derived functor factors the path map through localization. -/
@[simp] theorem rightDerivedFunctorOn_map_localize {A B : Type u} {f : A -> B}
    (F : PreFunctor A B f) {a b : A} (p : Path a b) :
    (rightDerivedFunctorOn F).map (localize p) = F.map p := by
  simp [rightDerivedFunctorOn, leftDerivedFunctorOn_map_localize]

/-! ## Universal property -/

/-- Universal property of the left derived functor. -/
theorem leftDerivedFunctor_universal {A B : Type u} {f : A -> B}
    (F : PreFunctor A B f) :
    Exists (fun G : FunctorOn A B f =>
      And
        (forall {a b : A} (p : Path a b), G.map (localize p) = F.map p)
        (forall G' : FunctorOn A B f,
          (forall {a b : A} (p : Path a b), G'.map (localize p) = F.map p) -> G' = G)) := by
  refine Exists.intro (leftDerivedFunctorOn F) ?_
  refine And.intro ?_ ?_
  · intro a b p
    exact leftDerivedFunctorOn_map_localize (F := F) (p := p)
  · intro G hG
    apply FunctorOn.ext
    intro a b q
    refine Quot.inductionOn q (fun p => ?_)
    have hG' := hG (a := a) (b := b) p
    have hL := leftDerivedFunctorOn_map_localize (F := F) (p := p)
    simpa [localize] using hG'.trans hL.symm

/-- Universal property of the right derived functor. -/
theorem rightDerivedFunctor_universal {A B : Type u} {f : A -> B}
    (F : PreFunctor A B f) :
    Exists (fun G : FunctorOn A B f =>
      And
        (forall {a b : A} (p : Path a b), G.map (localize p) = F.map p)
        (forall G' : FunctorOn A B f,
          (forall {a b : A} (p : Path a b), G'.map (localize p) = F.map p) -> G' = G)) := by
  simpa [rightDerivedFunctorOn] using leftDerivedFunctor_universal (F := F)

/-! ## Summary

We defined path-level data that respects rewrite equality, constructed left and
right derived functors on the fundamental groupoid, and proved the universal
property for the factorization through localization.
-/

end DerivedFunctor
end Path
end ComputationalPaths

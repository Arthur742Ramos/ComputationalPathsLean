import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Enriched functors and natural transformations as computational paths

This module develops the path-level theory of enriched functors and enriched
natural transformations, building directly on Path/Step/RwEq infrastructure
without depending on external enriched category structures.

The hom-objects of the path-enriched category are just `Path a b`, with
composition `Path.trans` and identity `Path.refl`. We call these
`HomObj`, `homComp`, `homId` for clarity.

## Key results
- `EnrichedFunctorData`: functors between path-enriched categories
- Functoriality: preservation of identity and composition as RwEq
- `EnrichedNatTransData`: natural transformations
- Vertical composition, whiskering
- Functor preserves symm, associativity
-/

namespace ComputationalPaths
namespace Enriched

open Path

universe u

-- ============================================================
-- § 0. Hom-object abbreviations
-- ============================================================

/-- Hom-objects in the path-enriched setting. -/
abbrev HomObj (A : Type u) (a b : A) : Type u := Path a b

/-- Enriched identity. -/
@[simp] noncomputable abbrev homId {A : Type u} (a : A) : HomObj A a a := Path.refl a

/-- Enriched composition. -/
@[simp] noncomputable abbrev homComp {A : Type u} {a b c : A}
    (p : HomObj A a b) (q : HomObj A b c) : HomObj A a c := Path.trans p q

-- ============================================================
-- § 1. Enriched functor data
-- ============================================================

/-- An enriched functor between path-enriched categories. -/
structure EnrichedFunctorData (A B : Type u) where
  obj : A → B
  mapHom : ∀ {a b : A}, HomObj A a b → HomObj B (obj a) (obj b)
  mapId : ∀ (a : A), RwEq (mapHom (homId a)) (homId (obj a))
  mapComp : ∀ {a b c : A} (p : HomObj A a b) (q : HomObj A b c),
    RwEq (mapHom (homComp p q)) (homComp (mapHom p) (mapHom q))
  mapStep : ∀ {a b : A} {p q : HomObj A a b}, Path.Step p q → RwEq (mapHom p) (mapHom q)

namespace EnrichedFunctorData

variable {A B C : Type u}

-- ============================================================
-- § 2. Functor preserves RwEq
-- ============================================================

/-- An enriched functor maps RwEq to RwEq (for congrArg-based functors). -/
noncomputable def mapRwEq (EF : EnrichedFunctorData A B)
    {a b : A} {p q : HomObj A a b}
    (h : RwEq p q) :
    RwEq (EF.mapHom p) (EF.mapHom q) := by
  induction h with
  | refl p =>
      let t := EF.mapHom p
      change RwEq t t
      exact rweq_trans (rweq_symm (rweq_cmpA_refl_right t)) (rweq_cmpA_refl_right t)
  | step s => exact EF.mapStep s
  | symm _ ih => exact rweq_symm ih
  | trans _ _ ih1 ih2 => exact rweq_trans ih1 ih2

-- ============================================================
-- § 3. Identity enriched functor
-- ============================================================

/-- The identity enriched functor. -/
noncomputable def idFunctor (A : Type u) : EnrichedFunctorData A A where
  obj := id
  mapHom := id
  mapId := by
    intro a
    let t := homId a
    change RwEq t t
    exact rweq_trans (rweq_symm (rweq_cmpA_refl_right t)) (rweq_cmpA_refl_right t)
  mapComp := by
    intro a b c p q
    let t := homComp p q
    change RwEq t t
    exact rweq_trans (rweq_symm (rweq_cmpA_refl_right t)) (rweq_cmpA_refl_right t)
  mapStep := fun s => rweq_of_step s

-- ============================================================
-- § 3. Composition of enriched functors
-- ============================================================

/-- Composition of enriched functors. -/
noncomputable def compFunctor
    (EF : EnrichedFunctorData A B) (EG : EnrichedFunctorData B C) :
    EnrichedFunctorData A C where
  obj := fun a => EG.obj (EF.obj a)
  mapHom := fun p => EG.mapHom (EF.mapHom p)
  mapId := by
    intro a
    exact rweq_trans (EG.mapRwEq (EF.mapId a)) (EG.mapId (EF.obj a))
  mapComp := by
    intro a b c p q
    exact rweq_trans (EG.mapRwEq (EF.mapComp p q)) (EG.mapComp (EF.mapHom p) (EF.mapHom q))
  mapStep := by
    intro a b p q s
    exact EG.mapRwEq (EF.mapStep s)

-- ============================================================
-- § 5. CongrArg-based enriched functor
-- ============================================================

/-- Build an enriched functor from a plain function via congrArg. -/
noncomputable def ofFunction (f : A → B) : EnrichedFunctorData A B where
  obj := f
  mapHom := Path.congrArg f
  mapId := fun a => rweq_congrArg_refl f a
  mapComp := fun p q => rweq_congrArg_trans f p q
  mapStep := fun s => rweq_congrArg_of_rweq f (rweq_of_step s)

/-- CongrArg-based functor preserves RwEq. -/
noncomputable def ofFunction_mapRwEq (f : A → B)
    {a b : A} {p q : HomObj A a b}
    (h : RwEq p q) :
    RwEq (Path.congrArg f p) (Path.congrArg f q) :=
  rweq_congrArg_of_rweq f h

/-- CongrArg-based functor preserves symm. -/
noncomputable def ofFunction_mapSymm (f : A → B)
    {a b : A} (p : HomObj A a b) :
    RwEq (Path.congrArg f (Path.symm p))
         (Path.symm (Path.congrArg f p)) :=
  rweq_congrArg_symm f p

/-- CongrArg-based functor preserves associativity. -/
noncomputable def ofFunction_mapAssoc (f : A → B)
    {a b c d : A} (p : HomObj A a b) (q : HomObj A b c) (r : HomObj A c d) :
    RwEq (Path.congrArg f (homComp (homComp p q) r))
         (homComp (Path.congrArg f p)
                  (homComp (Path.congrArg f q) (Path.congrArg f r))) := by
  exact rweq_trans
    (rweq_congrArg_trans f (homComp p q) r)
    (rweq_trans_congr_left (Path.congrArg f r)
      (rweq_congrArg_trans f p q))
  |> fun h => rweq_trans h
    (rweq_of_step (Step.trans_assoc
      (Path.congrArg f p) (Path.congrArg f q) (Path.congrArg f r)))

/-- Composition of congrArg-based functors. -/
noncomputable def ofFunction_comp (f : A → B) (g : B → C) :
    EnrichedFunctorData A C :=
  compFunctor (ofFunction (A := A) (B := B) f) (ofFunction (A := B) (B := C) g)

-- ============================================================
-- § 6. Enriched natural transformation
-- ============================================================

/-- An enriched natural transformation between enriched functors. -/
structure EnrichedNatTransData (EF EG : EnrichedFunctorData A B) where
  component : ∀ (a : A), HomObj B (EF.obj a) (EG.obj a)
  naturality : ∀ {a b : A} (p : HomObj A a b),
    RwEq (homComp (EF.mapHom p) (component b))
         (homComp (component a) (EG.mapHom p))

-- ============================================================
-- § 7. Identity natural transformation
-- ============================================================

/-- Identity enriched natural transformation. -/
noncomputable def idNatTrans (EF : EnrichedFunctorData A B) :
    EnrichedNatTransData EF EF where
  component := fun a => homId (EF.obj a)
  naturality := by
    intro a b p
    exact rweq_trans
      (rweq_cmpA_refl_right (EF.mapHom p))
      (rweq_symm (rweq_cmpA_refl_left (EF.mapHom p)))

-- ============================================================
-- § 8. Vertical composition
-- ============================================================

/-- Vertical composition of enriched natural transformations. -/
noncomputable def vcompNatTrans
    {EF EG EH : EnrichedFunctorData A B}
    (α : EnrichedNatTransData EF EG) (β : EnrichedNatTransData EG EH) :
    EnrichedNatTransData EF EH where
  component := fun a => homComp (α.component a) (β.component a)
  naturality := by
    intro a b p
    -- Need: (EF.map p) · (αb · βb) ↝ (αa · βa) · (EH.map p)
    exact rweq_trans
      (rweq_symm (rweq_of_step (Step.trans_assoc (EF.mapHom p) (α.component b) (β.component b))))
      (rweq_trans
        (rweq_trans_congr_left (β.component b) (α.naturality p))
        (rweq_trans
          (rweq_of_step (Step.trans_assoc (α.component a) (EG.mapHom p) (β.component b)))
          (rweq_trans
            (rweq_trans_congr_right (α.component a) (β.naturality p))
            (rweq_symm (rweq_of_step (Step.trans_assoc (α.component a) (β.component a) (EH.mapHom p)))))))

-- ============================================================
-- § 9. Left whiskering
-- ============================================================

/-- Left whiskering: pre-compose a nat trans with a functor. -/
noncomputable def whiskerLeft
    {EF EG : EnrichedFunctorData A B}
    (EH : EnrichedFunctorData B C)
    (α : EnrichedNatTransData EF EG) :
    EnrichedNatTransData (compFunctor EF EH) (compFunctor EG EH) where
  component := fun a => EH.mapHom (α.component a)
  naturality := by
    intro a b p
    -- Need: EH(EF.map p) · EH(αb) ↝ EH(αa) · EH(EG.map p)
    exact rweq_trans
      (rweq_symm (EH.mapComp (EF.mapHom p) (α.component b)))
      (rweq_trans
        (EH.mapRwEq (α.naturality p))
        (EH.mapComp (α.component a) (EG.mapHom p)))

-- ============================================================
-- § 10. Right whiskering
-- ============================================================

/-- Right whiskering: post-compose with a functor. -/
noncomputable def whiskerRight
    (EH : EnrichedFunctorData C A)
    {EF EG : EnrichedFunctorData A B}
    (α : EnrichedNatTransData EF EG) :
    EnrichedNatTransData (compFunctor EH EF) (compFunctor EH EG) where
  component := fun c => α.component (EH.obj c)
  naturality := by
    intro c d p
    exact α.naturality (EH.mapHom p)

-- ============================================================
-- § 11. Naturality square
-- ============================================================

/-- The naturality square commutes up to RwEq. -/
noncomputable def naturality_square
    {EF EG : EnrichedFunctorData A B}
    (α : EnrichedNatTransData EF EG)
    {a b : A} (p : HomObj A a b) :
    RwEq (homComp (EF.mapHom p) (α.component b))
         (homComp (α.component a) (EG.mapHom p)) :=
  α.naturality p

/-- Naturality square is symmetric. -/
noncomputable def naturality_square_symm
    {EF EG : EnrichedFunctorData A B}
    (α : EnrichedNatTransData EF EG)
    {a b : A} (p : HomObj A a b) :
    RwEq (homComp (α.component a) (EG.mapHom p))
         (homComp (EF.mapHom p) (α.component b)) :=
  rweq_symm (α.naturality p)

-- ============================================================
-- § 12. Functorial action aliases
-- ============================================================

/-- Enriched functor preserves refl. -/
noncomputable def mapHom_refl (EF : EnrichedFunctorData A B) (a : A) :
    RwEq (EF.mapHom (Path.refl a)) (Path.refl (EF.obj a)) :=
  EF.mapId a

/-- Enriched functor preserves trans. -/
noncomputable def mapHom_trans (EF : EnrichedFunctorData A B)
    {a b c : A} (p : HomObj A a b) (q : HomObj A b c) :
    RwEq (EF.mapHom (Path.trans p q))
         (Path.trans (EF.mapHom p) (EF.mapHom q)) :=
  EF.mapComp p q

-- ============================================================
-- § 13. Enriched functor from congrArg preserves inverse
-- ============================================================

/-- CongrArg functor: inverse cancellation left. -/
noncomputable def ofFunction_inv_cancel_left (f : A → B) {a b : A}
    (p : HomObj A a b) :
    RwEq (homComp (Path.congrArg f (Path.symm p)) (Path.congrArg f p))
         (homId (f b)) := by
  exact rweq_trans
    (rweq_symm (rweq_congrArg_trans f (Path.symm p) p))
    (rweq_trans
      (rweq_congrArg_of_rweq f (rweq_cmpA_inv_left p))
      (rweq_congrArg_refl f b))

/-- CongrArg functor: inverse cancellation right. -/
noncomputable def ofFunction_inv_cancel_right (f : A → B) {a b : A}
    (p : HomObj A a b) :
    RwEq (homComp (Path.congrArg f p) (Path.congrArg f (Path.symm p)))
         (homId (f a)) := by
  exact rweq_trans
    (rweq_symm (rweq_congrArg_trans f p (Path.symm p)))
    (rweq_trans
      (rweq_congrArg_of_rweq f (rweq_cmpA_inv_right p))
      (rweq_congrArg_refl f a))

end EnrichedFunctorData

end Enriched
end ComputationalPaths

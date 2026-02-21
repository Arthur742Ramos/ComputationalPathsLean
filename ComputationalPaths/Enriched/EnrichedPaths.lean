import ComputationalPaths.Path.Category.EnrichedCategory

/-!
# Enriched hom-object paths from computational steps

This module deepens enriched-category path infrastructure by exposing explicit
`Step` witnesses showing that hom-object composition respects the enrichment
structure.
-/

namespace ComputationalPaths
namespace Enriched

open Path
open Path.Category

universe u

/-- Hom-objects in the path-enriched setting. -/
abbrev EnrichedHomObj (A : Type u) (a b : A) : Type u :=
  EnrichedHom A a b

/-- Enriched identity on hom-objects. -/
@[simp] abbrev homId {A : Type u} (a : A) : EnrichedHomObj A a a :=
  enrichedId a

/-- Enriched composition on hom-objects. -/
@[simp] abbrev homComp {A : Type u} {a b c : A}
    (p : EnrichedHomObj A a b) (q : EnrichedHomObj A b c) :
    EnrichedHomObj A a c :=
  enrichedComp p q

/-- Associativity of enriched composition as a primitive computational step. -/
@[simp] theorem homComp_assoc_step {A : Type u} {a b c d : A}
    (p : EnrichedHomObj A a b) (q : EnrichedHomObj A b c) (r : EnrichedHomObj A c d) :
    Path.Step (homComp (homComp p q) r) (homComp p (homComp q r)) :=
  Path.Step.trans_assoc p q r

/-- Left unit for enriched composition as a primitive computational step. -/
@[simp] theorem homComp_left_unit_step {A : Type u} {a b : A}
    (p : EnrichedHomObj A a b) :
    Path.Step (homComp (homId a) p) p :=
  Path.Step.trans_refl_left p

/-- Right unit for enriched composition as a primitive computational step. -/
@[simp] theorem homComp_right_unit_step {A : Type u} {a b : A}
    (p : EnrichedHomObj A a b) :
    Path.Step (homComp p (homId b)) p :=
  Path.Step.trans_refl_right p

/-- Left inverse cancellation for enriched composition as a primitive step. -/
@[simp] theorem homComp_inv_left_step {A : Type u} {a b : A}
    (p : EnrichedHomObj A a b) :
    Path.Step (homComp (Path.symm p) p) (homId b) :=
  Path.Step.symm_trans p

/-- Right inverse cancellation for enriched composition as a primitive step. -/
@[simp] theorem homComp_inv_right_step {A : Type u} {a b : A}
    (p : EnrichedHomObj A a b) :
    Path.Step (homComp p (Path.symm p)) (homId a) :=
  Path.Step.trans_symm p

/-- Symmetry of enriched composition as a primitive computational step. -/
@[simp] theorem homComp_symm_step {A : Type u} {a b c : A}
    (p : EnrichedHomObj A a b) (q : EnrichedHomObj A b c) :
    Path.Step (Path.symm (homComp p q)) (homComp (Path.symm q) (Path.symm p)) :=
  Path.Step.symm_trans_congr p q

/-- A primitive left hom-object step is preserved by enriched composition. -/
@[simp] theorem homComp_respects_step_left {A : Type u} {a b c : A}
    {p p' : EnrichedHomObj A a b} (q : EnrichedHomObj A b c)
    (h : Path.Step p p') :
    Path.Step (homComp p q) (homComp p' q) :=
  Path.Step.trans_congr_left q h

/-- A primitive right hom-object step is preserved by enriched composition. -/
@[simp] theorem homComp_respects_step_right {A : Type u} {a b c : A}
    (p : EnrichedHomObj A a b) {q q' : EnrichedHomObj A b c}
    (h : Path.Step q q') :
    Path.Step (homComp p q) (homComp p q') :=
  Path.Step.trans_congr_right p h

/-- Enriched composition respects simultaneous primitive steps in both arguments. -/
@[simp] theorem homComp_respects_steps {A : Type u} {a b c : A}
    {p p' : EnrichedHomObj A a b} {q q' : EnrichedHomObj A b c}
    (hp : Path.Step p p') (hq : Path.Step q q') :
    RwEq (homComp p q) (homComp p' q') := by
  exact rweq_trans
    (rweq_of_step (homComp_respects_step_left (q := q) hp))
    (rweq_of_step (homComp_respects_step_right (p := p') hq))

/-- Enriched composition respects rewrite equivalence on hom-objects. -/
@[simp] theorem homComp_respects_rweq {A : Type u} {a b c : A}
    {p p' : EnrichedHomObj A a b} {q q' : EnrichedHomObj A b c}
    (hp : RwEq p p') (hq : RwEq q q') :
    RwEq (homComp p q) (homComp p' q') :=
  rweq_trans_congr hp hq

/-- Compatibility with the packaged enriched-category composition. -/
@[simp] theorem pathEnriched_comp_respects_steps {A : Type u} {a b c : A}
    {p p' : (pathEnrichedCategory A).Hom a b}
    {q q' : (pathEnrichedCategory A).Hom b c}
    (hp : Path.Step p p') (hq : Path.Step q q') :
    RwEq ((pathEnrichedCategory A).comp p q)
      ((pathEnrichedCategory A).comp p' q') := by
  simpa using homComp_respects_steps (A := A) (hp := hp) (hq := hq)

/-- Compatibility with the packaged enriched-category composition under `RwEq`. -/
@[simp] theorem pathEnriched_comp_respects_rweq {A : Type u} {a b c : A}
    {p p' : (pathEnrichedCategory A).Hom a b}
    {q q' : (pathEnrichedCategory A).Hom b c}
    (hp : RwEq p p') (hq : RwEq q q') :
    RwEq ((pathEnrichedCategory A).comp p q)
      ((pathEnrichedCategory A).comp p' q') := by
  simpa using homComp_respects_rweq (A := A) (hp := hp) (hq := hq)

end Enriched
end ComputationalPaths

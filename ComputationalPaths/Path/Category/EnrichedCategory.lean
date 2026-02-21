/-
# Enriched categories of computational paths

This module packages a lightweight enriched category whose hom-objects are
computational paths.  The `Path` structure carries a rewrite trace (`steps`)
and a propositional equality witness (`proof`), and we use the rewrite system
(`RwEq`) to provide associativity and unit coherence.

## Key Results

- `EnrichedHom`: hom-objects as `Path` types
- `enrichedComp`/`enrichedId`: composition and identities via `trans`/`refl`
- `enrichedComp_steps`/`enrichedComp_respects`: trace and congruence laws
- `enriched_assoc`/`enriched_left_unit`/`enriched_right_unit`: RwEq coherence
- `pathEnrichedCategory`: groupoid-enriched structure from `pathGroupoidEnriched`
- `enriched_assoc_path`/`enriched_left_unit_path`/`enriched_right_unit_path`
-/

import ComputationalPaths.Path.EnrichedCategory
import ComputationalPaths.Path.MonoidalCoherence

namespace ComputationalPaths
namespace Path
namespace Category

universe u

/-! ## Enriched hom-objects -/

/-- Enriched hom-objects are computational paths. -/
abbrev EnrichedHom (A : Type u) (a b : A) : Type u :=
  Path a b

/-- Enriched composition is path concatenation. -/
@[simp] abbrev enrichedComp {A : Type u} {a b c : A}
    (p : EnrichedHom A a b) (q : EnrichedHom A b c) : EnrichedHom A a c :=
  Path.trans p q

/-- Enriched identity is the reflexive path. -/
@[simp] abbrev enrichedId {A : Type u} (a : A) : EnrichedHom A a a :=
  Path.refl a

/-- The trace stored by an enriched identity is empty. -/
@[simp] theorem enrichedId_steps {A : Type u} (a : A) :
    (enrichedId (A := A) a).steps = [] := rfl

/-- The proof stored by an enriched identity is reflexivity. -/
@[simp] theorem enrichedId_proof {A : Type u} (a : A) :
    (enrichedId (A := A) a).proof = rfl := rfl

/-- Enriched composition matches the monoidal tensor on paths. -/
@[simp] theorem enrichedComp_eq_tensor {A : Type u} {a b c : A}
    (p : EnrichedHom A a b) (q : EnrichedHom A b c) :
    enrichedComp p q = MonoidalCoherence.tensorPath p q := rfl

/-- Enriched composition concatenates the computational traces. -/
@[simp] theorem enrichedComp_steps {A : Type u} {a b c : A}
    (p : EnrichedHom A a b) (q : EnrichedHom A b c) :
    (enrichedComp p q).steps = p.steps ++ q.steps := rfl

/-- Enriched composition composes the underlying equality witnesses. -/
@[simp] theorem enrichedComp_toEq {A : Type u} {a b c : A}
    (p : EnrichedHom A a b) (q : EnrichedHom A b c) :
    (enrichedComp p q).toEq = (p.toEq).trans (q.toEq) := rfl

/-! ## Primitive computational steps on hom-objects -/

/-- Symmetry of enriched composition rewrites by the primitive trans-symm rule. -/
@[simp] theorem enrichedComp_symm_step {A : Type u} {a b c : A}
    (p : EnrichedHom A a b) (q : EnrichedHom A b c) :
    Step (Path.symm (enrichedComp p q))
      (enrichedComp (Path.symm q) (Path.symm p)) :=
  Step.symm_trans_congr p q

/-- Symmetry of enriched composition, lifted to rewrite equivalence. -/
@[simp] theorem enrichedComp_symm {A : Type u} {a b c : A}
    (p : EnrichedHom A a b) (q : EnrichedHom A b c) :
    RwEq (Path.symm (enrichedComp p q))
      (enrichedComp (Path.symm q) (Path.symm p)) :=
  rweq_of_step (enrichedComp_symm_step p q)

/-- Primitive left inverse step for enriched composition. -/
@[simp] theorem enrichedComp_inv_left_step {A : Type u} {a b : A}
    (p : EnrichedHom A a b) :
    Step (enrichedComp (Path.symm p) p) (enrichedId b) :=
  Step.symm_trans p

/-- Primitive right inverse step for enriched composition. -/
@[simp] theorem enrichedComp_inv_right_step {A : Type u} {a b : A}
    (p : EnrichedHom A a b) :
    Step (enrichedComp p (Path.symm p)) (enrichedId a) :=
  Step.trans_symm p

/-- Left inverse coherence for enriched composition via rewrite equivalence. -/
@[simp] theorem enrichedComp_inv_left {A : Type u} {a b : A}
    (p : EnrichedHom A a b) :
    RwEq (enrichedComp (Path.symm p) p) (enrichedId b) :=
  rweq_of_step (enrichedComp_inv_left_step p)

/-- Right inverse coherence for enriched composition via rewrite equivalence. -/
@[simp] theorem enrichedComp_inv_right {A : Type u} {a b : A}
    (p : EnrichedHom A a b) :
    RwEq (enrichedComp p (Path.symm p)) (enrichedId a) :=
  rweq_of_step (enrichedComp_inv_right_step p)

/-- A primitive step in the left hom-object argument lifts through composition. -/
@[simp] theorem enrichedComp_respects_step_left {A : Type u} {a b c : A}
    {p p' : EnrichedHom A a b} (q : EnrichedHom A b c)
    (h : Step p p') :
    Step (enrichedComp p q) (enrichedComp p' q) :=
  Step.trans_congr_left q h

/-- A primitive step in the right hom-object argument lifts through composition. -/
@[simp] theorem enrichedComp_respects_step_right {A : Type u} {a b c : A}
    (p : EnrichedHom A a b) {q q' : EnrichedHom A b c}
    (h : Step q q') :
    Step (enrichedComp p q) (enrichedComp p q') :=
  Step.trans_congr_right p h

/-- Two primitive hom-object steps induce a rewrite-equivalent composite. -/
@[simp] theorem enrichedComp_respects_steps {A : Type u} {a b c : A}
    {p p' : EnrichedHom A a b} {q q' : EnrichedHom A b c}
    (hp : Step p p') (hq : Step q q') :
    RwEq (enrichedComp p q) (enrichedComp p' q') := by
  exact rweq_trans
    (rweq_of_step (enrichedComp_respects_step_left (q := q) hp))
    (rweq_of_step (enrichedComp_respects_step_right (p := p') hq))

/-! ## RwEq coherence -/

/-- Primitive associativity rewrite step for enriched composition. -/
@[simp] theorem enriched_assoc_step {A : Type u} {a b c d : A}
    (p : EnrichedHom A a b) (q : EnrichedHom A b c) (r : EnrichedHom A c d) :
    Step (enrichedComp (enrichedComp p q) r)
      (enrichedComp p (enrichedComp q r)) :=
  Step.trans_assoc p q r

/-- Associativity coherence for enriched composition. -/
@[simp] theorem enriched_assoc {A : Type u} {a b c d : A}
    (p : EnrichedHom A a b) (q : EnrichedHom A b c) (r : EnrichedHom A c d) :
    RwEq (enrichedComp (enrichedComp p q) r)
      (enrichedComp p (enrichedComp q r)) :=
  rweq_of_step (enriched_assoc_step p q r)

/-- Primitive left-unit rewrite step for enriched composition. -/
@[simp] theorem enriched_left_unit_step {A : Type u} {a b : A}
    (p : EnrichedHom A a b) :
    Step (enrichedComp (enrichedId a) p) p :=
  Step.trans_refl_left p

/-- Left unit coherence for enriched composition. -/
@[simp] theorem enriched_left_unit {A : Type u} {a b : A}
    (p : EnrichedHom A a b) :
    RwEq (enrichedComp (enrichedId a) p) p :=
  rweq_of_step (enriched_left_unit_step p)

/-- Primitive right-unit rewrite step for enriched composition. -/
@[simp] theorem enriched_right_unit_step {A : Type u} {a b : A}
    (p : EnrichedHom A a b) :
    Step (enrichedComp p (enrichedId b)) p :=
  Step.trans_refl_right p

/-- Right unit coherence for enriched composition. -/
@[simp] theorem enriched_right_unit {A : Type u} {a b : A}
    (p : EnrichedHom A a b) :
    RwEq (enrichedComp p (enrichedId b)) p :=
  rweq_of_step (enriched_right_unit_step p)

/-- Enriched composition is congruent in the left hom-object argument. -/
@[simp] theorem enrichedComp_respects_left {A : Type u} {a b c : A}
    {p p' : EnrichedHom A a b} (q : EnrichedHom A b c)
    (h : RwEq p p') :
    RwEq (enrichedComp p q) (enrichedComp p' q) :=
  rweq_trans_congr_left q h

/-- Enriched composition is congruent in the right hom-object argument. -/
@[simp] theorem enrichedComp_respects_right {A : Type u} {a b c : A}
    (p : EnrichedHom A a b) {q q' : EnrichedHom A b c}
    (h : RwEq q q') :
    RwEq (enrichedComp p q) (enrichedComp p q') :=
  rweq_trans_congr_right p h

/-- Enriched composition respects rewrite equivalence in both arguments. -/
@[simp] theorem enrichedComp_respects {A : Type u} {a b c : A}
    {p p' : EnrichedHom A a b} {q q' : EnrichedHom A b c}
    (hp : RwEq p p') (hq : RwEq q q') :
    RwEq (enrichedComp p q) (enrichedComp p' q') :=
  rweq_trans_congr hp hq

/-! ## Path-level equalities -/

/-- Associativity as a path equality. -/
@[simp] theorem enriched_assoc_path {A : Type u} {a b c d : A}
    (p : EnrichedHom A a b) (q : EnrichedHom A b c) (r : EnrichedHom A c d) :
    enrichedComp (enrichedComp p q) r = enrichedComp p (enrichedComp q r) :=
  trans_assoc p q r

/-- Left unit as a path equality. -/
@[simp] theorem enriched_left_unit_path {A : Type u} {a b : A}
    (p : EnrichedHom A a b) :
    enrichedComp (enrichedId a) p = p :=
  trans_refl_left p

/-- Right unit as a path equality. -/
@[simp] theorem enriched_right_unit_path {A : Type u} {a b : A}
    (p : EnrichedHom A a b) :
    enrichedComp p (enrichedId b) = p :=
  trans_refl_right p

/-! ## Groupoid-enriched structure -/

/-- The path-enriched category packaged as a groupoid-enriched category. -/
def pathEnrichedCategory (A : Type u) : GroupoidEnrichedCategory (Obj := A) :=
  pathGroupoidEnriched A

/-- Hom-objects in the enriched category are paths. -/
@[simp] theorem pathEnrichedCategory_hom (A : Type u) (a b : A) :
    (pathEnrichedCategory A).Hom a b = EnrichedHom A a b := rfl

/-- Composition in the enriched category is path concatenation. -/
@[simp] theorem pathEnrichedCategory_comp {A : Type u} {a b c : A}
    (p : EnrichedHom A a b) (q : EnrichedHom A b c) :
    (pathEnrichedCategory A).comp p q = enrichedComp p q := rfl

/-- Identities in the enriched category are reflexive paths. -/
@[simp] theorem pathEnrichedCategory_id {A : Type u} (a : A) :
    (pathEnrichedCategory A).id₁ a = enrichedId a := rfl

/-- The associator agrees with `enriched_assoc` (proof-irrelevant). -/
@[simp] theorem pathEnrichedCategory_assoc {A : Type u} {a b c d : A}
    (p : EnrichedHom A a b) (q : EnrichedHom A b c) (r : EnrichedHom A c d) :
    (pathEnrichedCategory A).assoc p q r = enriched_assoc p q r := by
  apply subsingleton_eq_by_cases

/-- The left unitor agrees with `enriched_left_unit` (proof-irrelevant). -/
@[simp] theorem pathEnrichedCategory_leftUnitor {A : Type u} {a b : A}
    (p : EnrichedHom A a b) :
    (pathEnrichedCategory A).leftUnitor p = enriched_left_unit p := by
  apply subsingleton_eq_by_cases

/-- The right unitor agrees with `enriched_right_unit` (proof-irrelevant). -/
@[simp] theorem pathEnrichedCategory_rightUnitor {A : Type u} {a b : A}
    (p : EnrichedHom A a b) :
    (pathEnrichedCategory A).rightUnitor p = enriched_right_unit p := by
  apply subsingleton_eq_by_cases

/-! ## Summary -/

/-!
We defined a path-enriched category whose hom-objects are computational paths,
with composition and identity given by `Path.trans`/`Path.refl`, and coherence
provided by `RwEq` lemmas and proof irrelevance.
-/

end Category
end Path
end ComputationalPaths

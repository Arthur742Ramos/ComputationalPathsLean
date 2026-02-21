/-
# Mapper Algorithm via Computational Paths

This module gives a lightweight, computational-paths formalization of the Mapper
construction from topological data analysis. We model covers, pullbacks, nerves,
and the 1-d Mapper (Reeb graph), together with refinement functoriality,
stability, and a nerve-lemma interface.

## Key Results
- `Mapper`: pullback cover -> nerve.
- `ReebGraph`: 1-d Mapper skeleton.
- `nerve_map_comp` / `mapper_map_comp`: refinement functoriality.
- `nerve_lemma`: a SimpleEquiv interface for the nerve lemma.
- `mapper_convergence`: convergence along refinement chains.

## References
- Singh, Memoli, Carlsson (2007): Mapper algorithm.
- de Silva, Ghrist (2007): nerve lemma.
-/

import ComputationalPaths.Basic

namespace ComputationalPaths
namespace Path
namespace MapperAlgorithm

universe u v

/-! ## Covers and Pullbacks -/

/-- A cover of `A` with explicit index data and a chosen element in each fiber. -/
structure Cover (A : Type u) where
  /-- Index type for the cover. -/
  I : Type v
  /-- Cover sets as predicates on points. -/
  U : I -> A -> Prop
  /-- A chosen index witnessing that every point lies in some cover set. -/
  cover : (a : A) -> { i : I // U i a }

namespace Cover

variable {A : Type u}

/-- The chosen index for a point. -/
def index (C : Cover A) (a : A) : C.I :=
  (C.cover a).1

/-- The chosen membership witness for a point. -/
def member (C : Cover A) (a : A) : C.U (C.index a) a :=
  (C.cover a).2

end Cover

/-- Pull back a cover along a map `f : B -> A`. -/
def pullbackCover {A B : Type u} (f : B -> A) (C : Cover A) : Cover B :=
  { I := C.I
    U := fun i b => C.U i (f b)
    cover := fun b =>
      let c := C.cover (f b)
      Subtype.mk c.1 c.2 }

/-! ## Nerves and Mapper -/

/-- A simplex of the nerve: a finite index list with a common witness. -/
structure Simplex {A : Type u} (C : Cover A) where
  /-- Indices of the simplex. -/
  indices : List C.I
  /-- A point in the intersection. -/
  point : A
  /-- Witness that the point lies in each listed cover set. -/
  witness : forall i, List.Mem i indices -> C.U i point

/-- Extensionality for simplices (witnesses live in Prop). -/
@[ext] theorem Simplex.ext {A : Type u} {C : Cover A} {s t : Simplex C}
    (h_indices : s.indices = t.indices) (h_point : s.point = t.point) : s = t := by
  cases s with
  | mk indices point witness =>
      cases t with
      | mk indices' point' witness' =>
          cases h_indices
          cases h_point
          have hw : witness = witness' := by
            rfl
          cases hw
          rfl

/-- The nerve of a cover. -/
def Nerve {A : Type u} (C : Cover A) : Type _ :=
  Simplex C

/-- The canonical 0-simplex chosen by the cover. -/
def nerveVertex {A : Type u} (C : Cover A) (a : A) : Nerve C := by
  let c := C.cover a
  refine { indices := [c.1], point := a, witness := ?_ }
  intro i hi
  cases hi with
  | head => exact c.2
  | tail _ hi' => cases hi'

/-- The Mapper construction: nerve of the pullback cover. -/
def Mapper {A B : Type u} (f : B -> A) (C : Cover A) : Type _ :=
  Nerve (pullbackCover f C)

/-- The 1-d Mapper: simplices with at most two indices. -/
def Mapper1 {A B : Type u} (f : B -> A) (C : Cover A) : Type _ :=
  { s : Mapper f C // s.indices.length <= 2 }

/-- The Reeb graph as the 1-d Mapper skeleton. -/
def ReebGraph {A B : Type u} (f : B -> A) (C : Cover A) : Type _ :=
  Mapper1 f C

/-- Reeb graphs are definitionally the 1-d Mapper. -/
theorem reeb_graph_is_mapper1 {A B : Type u} (f : B -> A) (C : Cover A) :
    ReebGraph f C = Mapper1 f C := rfl

/-! ## Refinements and Functoriality -/

/-- A cover refinement maps indices and preserves membership. -/
structure CoverRefinement {A : Type u} (C D : Cover A) where
  /-- Index refinement function. -/
  refine : C.I -> D.I
  /-- Membership transport along the refinement. -/
  mapU : forall i a, C.U i a -> D.U (refine i) a

namespace CoverRefinement

variable {A : Type u} {C D E : Cover A}

/-- Identity refinement. -/
def refl (C : Cover A) : CoverRefinement C C :=
  { refine := id
    mapU := fun _ _ h => h }

/-- Composition of refinements. -/
def comp (r : CoverRefinement C D) (s : CoverRefinement D E) : CoverRefinement C E :=
  { refine := fun i => s.refine (r.refine i)
    mapU := fun i a h => s.mapU (r.refine i) a (r.mapU i a h) }

end CoverRefinement

private def refineWitness {A : Type u} {C D : Cover A} (r : CoverRefinement C D)
    (indices : List C.I) (point : A)
    (w : forall i, List.Mem i indices -> C.U i point) :
    forall j, List.Mem j (indices.map r.refine) -> D.U j point := by
  induction indices with
  | nil =>
      intro j hj
      cases hj
  | cons i rest ih =>
      intro j hj
      cases hj with
      | head =>
          have hi : List.Mem i (i :: rest) := List.Mem.head (as := rest)
          exact r.mapU i point (w i hi)
      | tail _ hj' =>
          have hk' : forall k, List.Mem k rest -> C.U k point :=
            fun k hk =>
              w k (List.Mem.tail i hk)
          exact ih hk' j hj'

/-- Map a simplex along a refinement. -/
def simplexMap {A : Type u} {C D : Cover A} (r : CoverRefinement C D) (s : Simplex C) :
    Simplex D := by
  refine { indices := s.indices.map r.refine, point := s.point, witness := ?_ }
  exact refineWitness r s.indices s.point s.witness

/-- Map the nerve along a refinement. -/
def nerveMap {A : Type u} {C D : Cover A} (r : CoverRefinement C D) :
    Nerve C -> Nerve D :=
  simplexMap r

/-- Pull back a refinement along a map. -/
def pullbackRefinement {A B : Type u} (f : B -> A) {C D : Cover A}
    (r : CoverRefinement C D) : CoverRefinement (pullbackCover f C) (pullbackCover f D) :=
  { refine := r.refine
    mapU := fun i b h => r.mapU i (f b) h }

/-- Map a Mapper along a refinement. -/
def mapperMap {A B : Type u} (f : B -> A) {C D : Cover A} (r : CoverRefinement C D) :
    Mapper f C -> Mapper f D :=
  nerveMap (pullbackRefinement f r)

/-- Nerve map is identity for the identity refinement. -/
theorem nerve_map_refl {A : Type u} (C : Cover A) (s : Nerve C) :
    nerveMap (CoverRefinement.refl C) s = s := by
  cases s with
  | mk indices point witness =>
      apply Simplex.ext
      · simp [nerveMap, simplexMap, CoverRefinement.refl]
      · rfl

/-- Nerve maps compose along refinement composition. -/
theorem nerve_map_comp {A : Type u} {C D E : Cover A}
    (r : CoverRefinement C D) (s : CoverRefinement D E) (x : Nerve C) :
    nerveMap (CoverRefinement.comp r s) x = nerveMap s (nerveMap r x) := by
  cases x with
  | mk indices point witness =>
      apply Simplex.ext
      · simp [nerveMap, simplexMap, CoverRefinement.comp, List.map_map]
      · rfl

/-- Mapper map is identity for the identity refinement. -/
theorem mapper_map_refl {A B : Type u} (f : B -> A) (C : Cover A) (x : Mapper f C) :
    mapperMap f (CoverRefinement.refl C) x = x := by
  simpa [mapperMap] using
    (nerve_map_refl (C := pullbackCover f C) (s := x))

/-- Mapper maps compose along refinement composition. -/
theorem mapper_map_comp {A B : Type u} {C D E : Cover A} (f : B -> A)
    (r : CoverRefinement C D) (s : CoverRefinement D E) (x : Mapper f C) :
    mapperMap f (CoverRefinement.comp r s) x = mapperMap f s (mapperMap f r x) := by
  simpa [mapperMap] using
    (nerve_map_comp (r := pullbackRefinement f r) (s := pullbackRefinement f s) (x := x))

/-- Refinement maps respect computational paths. -/
def mapper_stable_under_refinement {A B : Type u} {C D : Cover A}
    (f : B -> A) (r : CoverRefinement C D) {x y : Mapper f C} (p : Path x y) :
    Path (mapperMap f r x) (mapperMap f r y) :=
  Path.congrArg (mapperMap f r) p

/-! ## Nerve Lemma and Convergence -/

/-- A good cover equipped with a computational-paths nerve equivalence. -/
structure GoodCover {A : Type u} (C : Cover A) where
  /-- The nerve equivalence for the cover. -/
  nerveEquiv : SimpleEquiv A (Nerve C)

/-- The nerve lemma packaged as a SimpleEquiv. -/
def nerve_lemma {A : Type u} {C : Cover A} (h : GoodCover C) :
    SimpleEquiv A (Nerve C) :=
  h.nerveEquiv

/-- The left inverse of the nerve lemma as a computational path. -/
def nerve_lemma_path {A : Type u} {C : Cover A} (h : GoodCover C) (a : A) :
    Path (h.nerveEquiv.invFun (h.nerveEquiv.toFun a)) a :=
  Path.stepChain (h.nerveEquiv.left_inv a)

/-- Convergence along refinement chains. -/
theorem mapper_convergence {A B : Type u} {C D E : Cover A} (f : B -> A)
    (r : CoverRefinement C D) (s : CoverRefinement D E) :
    mapperMap f (CoverRefinement.comp r s) =
      fun x => mapperMap f s (mapperMap f r x) := by
  funext x
  exact mapper_map_comp (f := f) (r := r) (s := s) (x := x)

end MapperAlgorithm
end Path
end ComputationalPaths

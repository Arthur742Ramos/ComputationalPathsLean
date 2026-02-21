/- 
# Simplicial path coherence via horn filling

This module packages horn filling and Kan conditions as path-preserving
operations in the computational-path framework. A simplicial map transports horn
data and horn fillers, and the transported face equalities are exposed as
`Path`, `Step`, and `RwEq` witnesses.
-/

import ComputationalPaths.Path.Homotopy.KanComplex
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Simplicial
namespace PathCoherence

open Path
open Path.Homotopy.KanComplex

universe u

/-- A simplicial map equipped with explicit path action on each degree. -/
structure PathPreservingSSetMap (S T : SSetData.{u}) where
  map : ∀ n, S.obj n → T.obj n
  map_face : ∀ (n : Nat) (i : Fin (n + 2)) (x : S.obj (n + 1)),
    map n (S.face n i x) = T.face n i (map (n + 1) x)
  map_degen : ∀ (n : Nat) (i : Fin (n + 1)) (x : S.obj n),
    map (n + 1) (S.degen n i x) = T.degen n i (map n x)

namespace PathPreservingSSetMap

variable {S T U : SSetData.{u}}

/-- Identity simplicial map with path-preserving structure. -/
def id (S : SSetData) : PathPreservingSSetMap S S where
  map := fun _ x => x
  map_face := by
    intro n i x
    rfl
  map_degen := by
    intro n i x
    rfl

/-- Composition of path-preserving simplicial maps. -/
def comp (F : PathPreservingSSetMap S T) (G : PathPreservingSSetMap T U) :
    PathPreservingSSetMap S U where
  map := fun n x => G.map n (F.map n x)
  map_face := by
    intro n i x
    calc
      G.map n (F.map n (S.face n i x))
          = G.map n (T.face n i (F.map (n + 1) x)) := by
              exact congrArg (G.map n) (F.map_face n i x)
      _ = U.face n i (G.map (n + 1) (F.map (n + 1) x)) :=
            G.map_face n i (F.map (n + 1) x)
  map_degen := by
    intro n i x
    calc
      G.map (n + 1) (F.map (n + 1) (S.degen n i x))
          = G.map (n + 1) (T.degen n i (F.map n x)) := by
              exact congrArg (G.map (n + 1)) (F.map_degen n i x)
      _ = U.degen n i (G.map n (F.map n x)) :=
            G.map_degen n i (F.map n x)

/-- Action on computational paths with an explicit trailing identity segment. -/
def mapPath (F : PathPreservingSSetMap S T) {n : Nat} {x y : S.obj n}
    (p : Path x y) : Path (F.map n x) (F.map n y) :=
  Path.trans (Path.congrArg (F.map n) p) (Path.refl (F.map n y))

/-- `mapPath` reduces to plain `congrArg` in one rewrite step. -/
theorem mapPath_step (F : PathPreservingSSetMap S T) {n : Nat} {x y : S.obj n}
    (p : Path x y) :
    Path.Step (F.mapPath p) (Path.congrArg (F.map n) p) := by
  simpa [mapPath] using Path.Step.trans_refl_right (Path.congrArg (F.map n) p)

/-- `mapPath` reduction witness lifted to rewrite equivalence. -/
noncomputable def mapPath_rweq (F : PathPreservingSSetMap S T) {n : Nat} {x y : S.obj n}
    (p : Path x y) :
    RwEq (F.mapPath p) (Path.congrArg (F.map n) p) :=
  rweq_of_step (F.mapPath_step p)

/-- Path action respects rewrite equivalence. -/
noncomputable def mapPath_respects_rweq (F : PathPreservingSSetMap S T)
    {n : Nat} {x y : S.obj n} {p q : Path x y} :
    RwEq p q → RwEq (F.mapPath p) (F.mapPath q) := by
  intro h
  have hmap :
      RwEq (Path.congrArg (F.map n) p) (Path.congrArg (F.map n) q) :=
    rweq_congrArg_of_rweq (A := S.obj n) (f := F.map n) h
  exact rweq_trans
    (F.mapPath_rweq p)
    (rweq_trans
      hmap
      (rweq_symm (F.mapPath_rweq q)))

/-- Transport horn data along a path-preserving simplicial map. -/
def mapHorn (F : PathPreservingSSetMap S T) {n : Nat}
    {k : Fin (n + 2)} (horn : HornData S n k) : HornData T n k where
  faces := fun i hi => F.map n (horn.faces i hi)
  compat := by
    intro i j hi hj hij m hm
    trivial

/-- Transport a horn filler along a path-preserving simplicial map. -/
def mapHornFiller (F : PathPreservingSSetMap S T) {n : Nat}
    {k : Fin (n + 2)} (horn : HornData S n k)
    (filler : HornFiller S n k horn) :
    HornFiller T n k (F.mapHorn horn) where
  simplex := F.map (n + 1) filler.simplex
  face_match := by
    intro i hi
    calc
      T.face n i (F.map (n + 1) filler.simplex)
          = F.map n (S.face n i filler.simplex) := by
              simpa using (F.map_face n i filler.simplex).symm
      _ = F.map n (horn.faces i hi) := by
            exact congrArg (F.map n) (filler.face_match i hi)
      _ = (F.mapHorn horn).faces i hi := rfl

/-- Horn filling on mapped horns induced by a Kan filler on the source. -/
def fillMappedHorn (F : PathPreservingSSetMap S T)
    (kan : KanFillerProperty S)
    (n : Nat) (k : Fin (n + 2)) (horn : HornData S n k) :
    HornFiller T n k (F.mapHorn horn) :=
  F.mapHornFiller horn (kan.fill n k horn)

/-- Inner-horn filling on mapped horns induced by source inner-Kan fillers. -/
def fillMappedInnerHorn (F : PathPreservingSSetMap S T)
    (kan : InnerKanProperty S)
    (n : Nat) (k : Fin (n + 2)) (hk : InnerHorn n k)
    (horn : HornData S n k) :
    HornFiller T n k (F.mapHorn horn) :=
  F.mapHornFiller horn (kan.fill n k hk horn)

/-- Face equations of transported fillers as computational paths. -/
def mappedFacePath (F : PathPreservingSSetMap S T)
    (kan : KanFillerProperty S)
    {n : Nat} {k : Fin (n + 2)} (horn : HornData S n k)
    (i : Fin (n + 2)) (hi : i ≠ k) :
    Path (T.face n i (F.fillMappedHorn kan n k horn).simplex)
         ((F.mapHorn horn).faces i hi) :=
  Path.stepChain ((F.fillMappedHorn kan n k horn).face_match i hi)

/-- A direct `Step` witness for normalization of transported face paths. -/
theorem mappedFacePath_step (F : PathPreservingSSetMap S T)
    (kan : KanFillerProperty S)
    {n : Nat} {k : Fin (n + 2)} (horn : HornData S n k)
    (i : Fin (n + 2)) (hi : i ≠ k) :
    Path.Step
      (Path.trans (F.mappedFacePath kan horn i hi)
        (Path.refl ((F.mapHorn horn).faces i hi)))
      (F.mappedFacePath kan horn i hi) :=
  Path.Step.trans_refl_right (F.mappedFacePath kan horn i hi)

/-- Rewrite-equivalence form of `mappedFacePath_step`. -/
noncomputable def mappedFacePath_rweq (F : PathPreservingSSetMap S T)
    (kan : KanFillerProperty S)
    {n : Nat} {k : Fin (n + 2)} (horn : HornData S n k)
    (i : Fin (n + 2)) (hi : i ≠ k) :
    RwEq
      (Path.trans (F.mappedFacePath kan horn i hi)
        (Path.refl ((F.mapHorn horn).faces i hi)))
      (F.mappedFacePath kan horn i hi) :=
  rweq_of_step (F.mappedFacePath_step kan horn i hi)

end PathPreservingSSetMap

/-- Kan fillers on mapped horns induced by a path-preserving simplicial map. -/
structure ImageKanCondition {S T : SSetData.{u}}
    (F : PathPreservingSSetMap S T) where
  fill :
    ∀ (n : Nat) (k : Fin (n + 2)) (horn : HornData S n k),
      HornFiller T n k (F.mapHorn horn)

/-- Inner-Kan fillers on mapped inner horns induced by a path-preserving map. -/
structure ImageInnerKanCondition {S T : SSetData.{u}}
    (F : PathPreservingSSetMap S T) where
  fill :
    ∀ (n : Nat) (k : Fin (n + 2)),
      InnerHorn n k →
      (horn : HornData S n k) →
      HornFiller T n k (F.mapHorn horn)

namespace ImageKanCondition

variable {S T : SSetData.{u}} (F : PathPreservingSSetMap S T)

/-- Any source Kan structure induces mapped-horn Kan fillers. -/
def ofKan (kan : KanFillerProperty S) : ImageKanCondition F where
  fill := fun n k horn => F.fillMappedHorn kan n k horn

/-- Mapped-horn Kan fillers restrict to mapped inner-horn fillers. -/
def toInner (K : ImageKanCondition F) : ImageInnerKanCondition F where
  fill := by
    intro n k _ horn
    exact K.fill n k horn

end ImageKanCondition

namespace ImageInnerKanCondition

variable {S T : SSetData.{u}} (F : PathPreservingSSetMap S T)

/-- Any source inner-Kan structure induces mapped inner-horn fillers. -/
def ofInnerKan (kan : InnerKanProperty S) : ImageInnerKanCondition F where
  fill := fun n k hk horn => F.fillMappedInnerHorn kan n k hk horn

/-- Full source Kan structure induces mapped inner-Kan fillers. -/
def ofKan (kan : KanFillerProperty S) : ImageInnerKanCondition F :=
  (ImageKanCondition.ofKan F kan).toInner

end ImageInnerKanCondition

end PathCoherence
end Simplicial
end ComputationalPaths

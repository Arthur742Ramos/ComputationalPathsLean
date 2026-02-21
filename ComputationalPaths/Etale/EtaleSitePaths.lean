import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Etale cohomology paths: etale sites

This module packages a minimal etale-site interface with explicit computational
paths. Pullback and restriction compatibilities are represented by `Path`,
normalized using `Path.Step`, and compared using `RwEq`.
-/

namespace ComputationalPaths
namespace Etale
namespace EtaleSitePaths

open Path

universe u

/-- Domain-specific rewrite tags for etale-site coherence moves. -/
inductive EtaleSiteStep : Type
  | pullbackAssoc
  | coverCompose
  | restrictionTransport

/-- Minimal data for an etale site with path-preserving pullback and restriction. -/
structure EtaleSitePathData (Obj Cover : Type u) where
  source : Cover → Obj
  target : Cover → Obj
  pullbackObj : Obj → Obj → Obj
  composeCover : Cover → Cover → Cover
  baseObj : Obj
  pullbackAssocPath :
    ∀ U V W : Obj,
      Path (pullbackObj (pullbackObj U V) W) (pullbackObj U (pullbackObj V W))
  coverComposePath :
    ∀ f g : Cover,
      Path (source (composeCover f g)) (source f)
  restrictionPath :
    ∀ U : Obj,
      Path (pullbackObj U baseObj) U
  restrictionMap :
    {U V : Obj} → Path U V → Path (pullbackObj U baseObj) (pullbackObj V baseObj)

namespace EtaleSitePathData

variable {Obj Cover : Type u} (S : EtaleSitePathData Obj Cover)

/-- Step witness: right-unit normalization for pullback associativity. -/
def pullbackAssoc_step (U V W : Obj) :
    Path.Step
      (Path.trans (S.pullbackAssocPath U V W)
        (Path.refl (S.pullbackObj U (S.pullbackObj V W))))
      (S.pullbackAssocPath U V W) :=
  Path.Step.trans_refl_right (S.pullbackAssocPath U V W)

noncomputable def pullbackAssoc_rweq (U V W : Obj) :
    RwEq
      (Path.trans (S.pullbackAssocPath U V W)
        (Path.refl (S.pullbackObj U (S.pullbackObj V W))))
      (S.pullbackAssocPath U V W) :=
  rweq_of_step (S.pullbackAssoc_step U V W)

/-- Step witness: left-unit normalization for cover composition. -/
def coverCompose_step (f g : Cover) :
    Path.Step
      (Path.trans (Path.refl (S.source (S.composeCover f g))) (S.coverComposePath f g))
      (S.coverComposePath f g) :=
  Path.Step.trans_refl_left (S.coverComposePath f g)

noncomputable def coverCompose_rweq (f g : Cover) :
    RwEq
      (Path.trans (Path.refl (S.source (S.composeCover f g))) (S.coverComposePath f g))
      (S.coverComposePath f g) :=
  rweq_of_step (S.coverCompose_step f g)

/-- Step witness: right-unit normalization for restriction transport. -/
def restrictionMap_step {U V : Obj} (p : Path U V) :
    Path.Step
      (Path.trans (S.restrictionMap p)
        (Path.refl (S.pullbackObj V S.baseObj)))
      (S.restrictionMap p) :=
  Path.Step.trans_refl_right (S.restrictionMap p)

noncomputable def restrictionMap_rweq {U V : Obj} (p : Path U V) :
    RwEq
      (Path.trans (S.restrictionMap p)
        (Path.refl (S.pullbackObj V S.baseObj)))
      (S.restrictionMap p) :=
  rweq_of_step (S.restrictionMap_step p)

noncomputable def restriction_cancel_rweq (U : Obj) :
    RwEq
      (Path.trans (Path.symm (S.restrictionPath U)) (S.restrictionPath U))
      (Path.refl U) :=
  rweq_cmpA_inv_left (S.restrictionPath U)

end EtaleSitePathData

/-- Trivial etale-site path package on `PUnit`. -/
def trivialEtaleSitePathData : EtaleSitePathData PUnit PUnit where
  source := fun _ => PUnit.unit
  target := fun _ => PUnit.unit
  pullbackObj := fun _ _ => PUnit.unit
  composeCover := fun _ _ => PUnit.unit
  baseObj := PUnit.unit
  pullbackAssocPath := fun _ _ _ => Path.refl PUnit.unit
  coverComposePath := fun _ _ => Path.refl PUnit.unit
  restrictionPath := fun _ => Path.refl PUnit.unit
  restrictionMap := fun _ => Path.refl PUnit.unit

end EtaleSitePaths
end Etale
end ComputationalPaths

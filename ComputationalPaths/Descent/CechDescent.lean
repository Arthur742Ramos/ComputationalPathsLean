/-
# Čech descent and hypercover coherence via computational paths

This module packages Čech nerve descent and hypercover data with
computational-path witnesses. The Čech complex arises from a covering
family and encodes gluing conditions; hypercovers generalize this to
higher-dimensional descent. All coherence is tracked by `Path`, `Step`,
and `RwEq`.
-/

import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Descent.PathCoherence

namespace ComputationalPaths
namespace Descent
namespace CechDescent

open Path

universe u v

/-- Covering family data with restriction maps and explicit path
witnesses for the compatibility conditions. -/
structure CoveringData (X : Type u) (Idx : Type v) where
  /-- Open sets / patches. -/
  patch : Idx → Type u
  /-- Restriction to a patch. -/
  restrict : (i : Idx) → X → patch i
  /-- Double overlap: patch i ×_X patch j. -/
  overlap : Idx → Idx → Type u
  /-- Projection from overlap to first patch. -/
  pr₁ : {i j : Idx} → overlap i j → patch i
  /-- Projection from overlap to second patch. -/
  pr₂ : {i j : Idx} → overlap i j → patch j
  /-- Symmetry of overlaps. -/
  overlapSymm : {i j : Idx} → overlap i j → overlap j i
  /-- Symmetry-symmetry is identity. -/
  overlapSymm_symm : {i j : Idx} → (x : overlap i j) →
    Path (overlapSymm (overlapSymm x)) x

namespace CoveringData

variable {X : Type u} {Idx : Type v} (C : CoveringData X Idx)

/-- overlapSymm_symm right-cancels. -/
noncomputable def overlapSymm_symm_cancel_right {i j : Idx} (x : C.overlap i j) :
    RwEq (Path.trans (C.overlapSymm_symm x) (Path.symm (C.overlapSymm_symm x)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (C.overlapSymm_symm x)

/-- overlapSymm_symm left-cancels. -/
noncomputable def overlapSymm_symm_cancel_left {i j : Idx} (x : C.overlap i j) :
    RwEq (Path.trans (Path.symm (C.overlapSymm_symm x)) (C.overlapSymm_symm x))
         (Path.refl _) :=
  rweq_cmpA_inv_left (C.overlapSymm_symm x)

/-- overlapSymm_symm right-unit. -/
noncomputable def overlapSymm_symm_refl_right {i j : Idx} (x : C.overlap i j) :
    RwEq (Path.trans (C.overlapSymm_symm x) (Path.refl _))
         (C.overlapSymm_symm x) :=
  rweq_cmpA_refl_right (C.overlapSymm_symm x)

/-- overlapSymm_symm left-unit. -/
noncomputable def overlapSymm_symm_refl_left {i j : Idx} (x : C.overlap i j) :
    RwEq (Path.trans (Path.refl _) (C.overlapSymm_symm x))
         (C.overlapSymm_symm x) :=
  rweq_cmpA_refl_left (C.overlapSymm_symm x)

/-- overlapSymm_symm involution (double-symm). -/
noncomputable def overlapSymm_symm_involution {i j : Idx} (x : C.overlap i j) :
    RwEq (Path.symm (Path.symm (C.overlapSymm_symm x)))
         (C.overlapSymm_symm x) :=
  rweq_of_step (Step.symm_symm (C.overlapSymm_symm x))

end CoveringData

/-- Čech descent datum: sections on overlaps with gluing coherence. -/
structure CechDescentDatum (X : Type u) (Idx : Type v)
    (C : CoveringData X Idx) (F : Type u) where
  /-- Local section on each patch. -/
  section_ : (i : Idx) → C.patch i → F
  /-- Gluing condition: sections agree on overlaps. -/
  gluing : {i j : Idx} → (x : C.overlap i j) →
    Path (section_ i (C.pr₁ x)) (section_ j (C.pr₂ x))
  /-- Symmetry coherence: gluing on (i,j) reverses on (j,i). -/
  gluing_symm : {i j : Idx} → (x : C.overlap i j) →
    RwEq (Path.symm (gluing x))
         (Path.trans (Path.congrArg (section_ j) (Path.refl (C.pr₂ x)))
                     (Path.symm (gluing (C.overlapSymm x))))

namespace CechDescentDatum

variable {X : Type u} {Idx : Type v} {C : CoveringData X Idx} {F : Type u}
         (D : CechDescentDatum X Idx C F)

/-- Gluing right-cancels. -/
noncomputable def gluing_cancel_right {i j : Idx} (x : C.overlap i j) :
    RwEq (Path.trans (D.gluing x) (Path.symm (D.gluing x)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (D.gluing x)

/-- Gluing left-cancels. -/
noncomputable def gluing_cancel_left {i j : Idx} (x : C.overlap i j) :
    RwEq (Path.trans (Path.symm (D.gluing x)) (D.gluing x))
         (Path.refl _) :=
  rweq_cmpA_inv_left (D.gluing x)

/-- Gluing right-unit. -/
noncomputable def gluing_refl_right {i j : Idx} (x : C.overlap i j) :
    RwEq (Path.trans (D.gluing x) (Path.refl _))
         (D.gluing x) :=
  rweq_cmpA_refl_right (D.gluing x)

/-- Gluing left-unit. -/
noncomputable def gluing_refl_left {i j : Idx} (x : C.overlap i j) :
    RwEq (Path.trans (Path.refl _) (D.gluing x))
         (D.gluing x) :=
  rweq_cmpA_refl_left (D.gluing x)

/-- Gluing symm-symm. -/
noncomputable def gluing_symm_symm {i j : Idx} (x : C.overlap i j) :
    RwEq (Path.symm (Path.symm (D.gluing x)))
         (D.gluing x) :=
  rweq_of_step (Step.symm_symm (D.gluing x))

end CechDescentDatum

/-- Triple overlap data for the Čech 2-cocycle condition. -/
structure TripleOverlapData (X : Type u) (Idx : Type v)
    (C : CoveringData X Idx) where
  /-- Triple overlaps. -/
  triple : Idx → Idx → Idx → Type u
  /-- Projections to double overlaps. -/
  pr₁₂ : {i j k : Idx} → triple i j k → C.overlap i j
  pr₂₃ : {i j k : Idx} → triple i j k → C.overlap j k
  pr₁₃ : {i j k : Idx} → triple i j k → C.overlap i k

/-- Čech 2-cocycle condition with path-level coherence. -/
structure CechCocycleCondition (X : Type u) (Idx : Type v)
    (C : CoveringData X Idx) (T : TripleOverlapData X Idx C)
    (F : Type u) (D : CechDescentDatum X Idx C F) where
  /-- Cocycle: g_{ij} g_{jk} = g_{ik} on triple overlaps. -/
  cocycle : {i j k : Idx} → (x : T.triple i j k) →
    RwEq (Path.trans (D.gluing (T.pr₁₂ x)) (D.gluing (T.pr₂₃ x)))
         (D.gluing (T.pr₁₃ x))

namespace CechCocycleCondition

variable {X : Type u} {Idx : Type v} {C : CoveringData X Idx}
         {T : TripleOverlapData X Idx C} {F : Type u}
         {D : CechDescentDatum X Idx C F}

/-- Cocycle composed with unit is still cocycle. -/
noncomputable def cocycle_refl_right (CC : CechCocycleCondition X Idx C T F D)
    {i j k : Idx} (x : T.triple i j k) :
    RwEq (Path.trans (D.gluing (T.pr₁₃ x)) (Path.refl _))
         (D.gluing (T.pr₁₃ x)) :=
  rweq_cmpA_refl_right (D.gluing (T.pr₁₃ x))

end CechCocycleCondition

/-- Hypercover data: higher-dimensional extension of Čech descent. -/
structure HypercoverData (X : Type u) (Idx : Type v)
    (C : CoveringData X Idx) where
  /-- n-fold overlap at each cosimplicial level. -/
  level : Nat → Type u
  /-- Coface maps between levels. -/
  coface : (n : Nat) → Fin (n + 2) → level n → level (n + 1)
  /-- Codegeneracy maps between levels. -/
  codegen : (n : Nat) → Fin (n + 1) → level (n + 1) → level n
  /-- Cosimplicial identity: coface commutation. -/
  coface_comm : (n : Nat) → (i j : Fin (n + 2)) → (x : level n) →
    i.val ≤ j.val →
    Path (coface (n + 1) i.castSucc (coface n j x))
         (coface (n + 1) j.succ (coface n i x))

namespace HypercoverData

variable {X : Type u} {Idx : Type v} {C : CoveringData X Idx}
         (H : HypercoverData X Idx C)

/-- Coface commutation right-cancels. -/
noncomputable def coface_comm_cancel_right (n : Nat) (i j : Fin (n + 2))
    (x : H.level n) (h : i.val ≤ j.val) :
    RwEq (Path.trans (H.coface_comm n i j x h)
                     (Path.symm (H.coface_comm n i j x h)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (H.coface_comm n i j x h)

/-- Coface commutation symm-symm. -/
noncomputable def coface_comm_symm_symm (n : Nat) (i j : Fin (n + 2))
    (x : H.level n) (h : i.val ≤ j.val) :
    RwEq (Path.symm (Path.symm (H.coface_comm n i j x h)))
         (H.coface_comm n i j x h) :=
  rweq_of_step (Step.symm_symm (H.coface_comm n i j x h))

/-- Coface commutation right-unit. -/
noncomputable def coface_comm_refl_right (n : Nat) (i j : Fin (n + 2))
    (x : H.level n) (h : i.val ≤ j.val) :
    RwEq (Path.trans (H.coface_comm n i j x h) (Path.refl _))
         (H.coface_comm n i j x h) :=
  rweq_cmpA_refl_right (H.coface_comm n i j x h)

/-- Coface commutation left-unit. -/
noncomputable def coface_comm_refl_left (n : Nat) (i j : Fin (n + 2))
    (x : H.level n) (h : i.val ≤ j.val) :
    RwEq (Path.trans (Path.refl _) (H.coface_comm n i j x h))
         (H.coface_comm n i j x h) :=
  rweq_cmpA_refl_left (H.coface_comm n i j x h)

/-- Coface commutation left-cancels. -/
noncomputable def coface_comm_cancel_left (n : Nat) (i j : Fin (n + 2))
    (x : H.level n) (h : i.val ≤ j.val) :
    RwEq (Path.trans (Path.symm (H.coface_comm n i j x h))
                     (H.coface_comm n i j x h))
         (Path.refl _) :=
  rweq_cmpA_inv_left (H.coface_comm n i j x h)

end HypercoverData

end CechDescent
end Descent
end ComputationalPaths

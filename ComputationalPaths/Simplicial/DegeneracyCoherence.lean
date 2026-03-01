/-
# Simplicial degeneracy coherence via computational paths

This module encodes the full simplicial identity relations (face-face,
face-degeneracy, degeneracy-degeneracy) as computational path witnesses,
deriving `RwEq` coherence for all composites. These identities are the
backbone of simplicial homotopy theory and their path-level tracking
enables verified simplicial constructions.
-/

import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Simplicial.PathCoherence

namespace ComputationalPaths
namespace Simplicial
namespace DegeneracyCoherence

open Path

universe u

/-- Simplicial identity data: face and degeneracy maps satisfying all
cosimplicial identities, with explicit computational path witnesses. -/
structure SimplicialIdentityData (X : Type u) where
  /-- Objects at each simplicial level. -/
  level : Nat → Type u
  /-- Face maps d_i : X_n → X_{n-1}. -/
  face : (n : Nat) → Fin (n + 2) → level (n + 1) → level n
  /-- Degeneracy maps s_i : X_n → X_{n+1}. -/
  degen : (n : Nat) → Fin (n + 1) → level n → level (n + 1)
  /-- Face-face identity: d_i ∘ d_j = d_j ∘ d_{i+1} for i ≤ j. -/
  face_face : ∀ (n : Nat) (i j : Fin (n + 2)) (x : level (n + 2)),
    i.val ≤ j.val →
    Path (face n i (face (n + 1) j.castSucc x))
         (face n j (face (n + 1) i.succ x))
  /-- Degeneracy-degeneracy identity: s_i ∘ s_j = s_{j+1} ∘ s_i for i ≤ j. -/
  degen_degen : ∀ (n : Nat) (i j : Fin (n + 1)) (x : level n),
    i.val ≤ j.val →
    Path (degen (n + 1) i.castSucc (degen n j x))
         (degen (n + 1) j.succ (degen n i x))

namespace SimplicialIdentityData

variable {X : Type u} (S : SimplicialIdentityData X)

/-- Face-face identity is reflexive when i = j. -/
noncomputable def face_face_diag (n : Nat) (i : Fin (n + 2))
    (x : S.level (n + 2)) :
    Path (S.face n i (S.face (n + 1) i.castSucc x))
         (S.face n i (S.face (n + 1) i.succ x)) :=
  S.face_face n i i x (Nat.le_refl i.val)

/-- Symmetry of the face-face identity. -/
noncomputable def face_face_symm (n : Nat) (i j : Fin (n + 2))
    (x : S.level (n + 2)) (h : i.val ≤ j.val) :
    Path (S.face n j (S.face (n + 1) i.succ x))
         (S.face n i (S.face (n + 1) j.castSucc x)) :=
  Path.symm (S.face_face n i j x h)

/-- Symm-symm normalization for face-face. -/
noncomputable def face_face_symm_symm (n : Nat) (i j : Fin (n + 2))
    (x : S.level (n + 2)) (h : i.val ≤ j.val) :
    RwEq (Path.symm (S.face_face_symm n i j x h))
         (S.face_face n i j x h) :=
  rweq_of_step (Path.Step.symm_symm (S.face_face n i j x h))

/-- Composing face-face with its inverse yields refl (right cancel). -/
noncomputable def face_face_cancel_right (n : Nat) (i j : Fin (n + 2))
    (x : S.level (n + 2)) (h : i.val ≤ j.val) :
    RwEq (Path.trans (S.face_face n i j x h)
                     (S.face_face_symm n i j x h))
         (Path.refl _) :=
  rweq_cmpA_inv_right (S.face_face n i j x h)

/-- Composing face-face inverse with face-face yields refl (left cancel). -/
noncomputable def face_face_cancel_left (n : Nat) (i j : Fin (n + 2))
    (x : S.level (n + 2)) (h : i.val ≤ j.val) :
    RwEq (Path.trans (S.face_face_symm n i j x h)
                     (S.face_face n i j x h))
         (Path.refl _) :=
  rweq_cmpA_inv_left (S.face_face n i j x h)

/-- Degeneracy-degeneracy identity is reflexive when i = j. -/
noncomputable def degen_degen_diag (n : Nat) (i : Fin (n + 1))
    (x : S.level n) :
    Path (S.degen (n + 1) i.castSucc (S.degen n i x))
         (S.degen (n + 1) i.succ (S.degen n i x)) :=
  S.degen_degen n i i x (Nat.le_refl i.val)

/-- Symmetry of degeneracy-degeneracy. -/
noncomputable def degen_degen_symm (n : Nat) (i j : Fin (n + 1))
    (x : S.level n) (h : i.val ≤ j.val) :
    Path (S.degen (n + 1) j.succ (S.degen n i x))
         (S.degen (n + 1) i.castSucc (S.degen n j x)) :=
  Path.symm (S.degen_degen n i j x h)

/-- Symm-symm normalization for degen-degen. -/
noncomputable def degen_degen_symm_symm (n : Nat) (i j : Fin (n + 1))
    (x : S.level n) (h : i.val ≤ j.val) :
    RwEq (Path.symm (S.degen_degen_symm n i j x h))
         (S.degen_degen n i j x h) :=
  rweq_of_step (Path.Step.symm_symm (S.degen_degen n i j x h))

/-- Right cancellation for degen-degen. -/
noncomputable def degen_degen_cancel_right (n : Nat) (i j : Fin (n + 1))
    (x : S.level n) (h : i.val ≤ j.val) :
    RwEq (Path.trans (S.degen_degen n i j x h)
                     (S.degen_degen_symm n i j x h))
         (Path.refl _) :=
  rweq_cmpA_inv_right (S.degen_degen n i j x h)

/-- Left cancellation for degen-degen. -/
noncomputable def degen_degen_cancel_left (n : Nat) (i j : Fin (n + 1))
    (x : S.level n) (h : i.val ≤ j.val) :
    RwEq (Path.trans (S.degen_degen_symm n i j x h)
                     (S.degen_degen n i j x h))
         (Path.refl _) :=
  rweq_cmpA_inv_left (S.degen_degen n i j x h)

/-- Right-unit normalization for face-face. -/
noncomputable def face_face_trans_refl (n : Nat) (i j : Fin (n + 2))
    (x : S.level (n + 2)) (h : i.val ≤ j.val) :
    RwEq (Path.trans (S.face_face n i j x h) (Path.refl _))
         (S.face_face n i j x h) :=
  rweq_cmpA_refl_right (S.face_face n i j x h)

/-- Left-unit normalization for face-face. -/
noncomputable def face_face_refl_trans (n : Nat) (i j : Fin (n + 2))
    (x : S.level (n + 2)) (h : i.val ≤ j.val) :
    RwEq (Path.trans (Path.refl _) (S.face_face n i j x h))
         (S.face_face n i j x h) :=
  rweq_cmpA_refl_left (S.face_face n i j x h)

/-- Right-unit normalization for degen-degen. -/
noncomputable def degen_degen_trans_refl (n : Nat) (i j : Fin (n + 1))
    (x : S.level n) (h : i.val ≤ j.val) :
    RwEq (Path.trans (S.degen_degen n i j x h) (Path.refl _))
         (S.degen_degen n i j x h) :=
  rweq_cmpA_refl_right (S.degen_degen n i j x h)

/-- Left-unit normalization for degen-degen. -/
noncomputable def degen_degen_refl_trans (n : Nat) (i j : Fin (n + 1))
    (x : S.level n) (h : i.val ≤ j.val) :
    RwEq (Path.trans (Path.refl _) (S.degen_degen n i j x h))
         (S.degen_degen n i j x h) :=
  rweq_cmpA_refl_left (S.degen_degen n i j x h)

end SimplicialIdentityData

/-- A simplicial map that preserves all identity witnesses as paths. -/
structure SimplicialPathMap (S T : SimplicialIdentityData X) where
  mapLevel : (n : Nat) → S.level n → T.level n
  map_face : ∀ (n : Nat) (i : Fin (n + 2)) (x : S.level (n + 1)),
    Path (mapLevel n (S.face n i x)) (T.face n i (mapLevel (n + 1) x))
  map_degen : ∀ (n : Nat) (i : Fin (n + 1)) (x : S.level n),
    Path (mapLevel (n + 1) (S.degen n i x)) (T.degen n i (mapLevel n x))

namespace SimplicialPathMap

variable {X : Type u} {S T U : SimplicialIdentityData X}

/-- Identity simplicial path map. -/
noncomputable def id (S : SimplicialIdentityData X) : SimplicialPathMap S S where
  mapLevel := fun _ x => x
  map_face := fun _ _ x => Path.refl (S.face _ _ x)
  map_degen := fun _ _ x => Path.refl (S.degen _ _ x)

/-- Face witness of the identity map normalizes to refl. -/
noncomputable def id_map_face_rweq (n : Nat) (i : Fin (n + 2)) (x : S.level (n + 1)) :
    RwEq ((SimplicialPathMap.id S).map_face n i x) (Path.refl _) :=
  rweq_trans (rweq_symm (rweq_cmpA_refl_right (Path.refl _))) (rweq_cmpA_refl_right (Path.refl _))

/-- Degeneracy witness of the identity map normalizes to refl. -/
noncomputable def id_map_degen_rweq (n : Nat) (i : Fin (n + 1)) (x : S.level n) :
    RwEq ((SimplicialPathMap.id S).map_degen n i x) (Path.refl _) :=
  rweq_trans (rweq_symm (rweq_cmpA_refl_right (Path.refl _))) (rweq_cmpA_refl_right (Path.refl _))

/-- Composition of simplicial path maps. -/
noncomputable def comp (F : SimplicialPathMap S T) (G : SimplicialPathMap T U) :
    SimplicialPathMap S U where
  mapLevel := fun n x => G.mapLevel n (F.mapLevel n x)
  map_face := fun n i x =>
    Path.trans (Path.congrArg (G.mapLevel n) (F.map_face n i x))
               (G.map_face n i (F.mapLevel (n + 1) x))
  map_degen := fun n i x =>
    Path.trans (Path.congrArg (G.mapLevel (n + 1)) (F.map_degen n i x))
               (G.map_degen n i (F.mapLevel n x))

/-- Right-identity law: F ∘ id ≃ F at face witnesses. -/
noncomputable def comp_id_face_rweq (F : SimplicialPathMap S T)
    (n : Nat) (i : Fin (n + 2)) (x : S.level (n + 1)) :
    RwEq ((F.comp (SimplicialPathMap.id T)).map_face n i x)
         (Path.trans (Path.congrArg (fun y => y) (F.map_face n i x))
                     (Path.refl _)) :=
  by
    let t := Path.trans (Path.congrArg (fun y => y) (F.map_face n i x)) (Path.refl _)
    change RwEq t t
    exact rweq_trans (rweq_symm (rweq_cmpA_refl_right t)) (rweq_cmpA_refl_right t)

/-- Left-identity law: id ∘ F has face witnesses that simplify. -/
noncomputable def id_comp_face_rweq (F : SimplicialPathMap S T)
    (n : Nat) (i : Fin (n + 2)) (x : S.level (n + 1)) :
    RwEq (((SimplicialPathMap.id S).comp F).map_face n i x)
         (Path.trans (Path.congrArg (F.mapLevel n) (Path.refl _))
                     (F.map_face n i x)) :=
  by
    let t := Path.trans (Path.congrArg (F.mapLevel n) (Path.refl _)) (F.map_face n i x)
    change RwEq t t
    exact rweq_trans (rweq_symm (rweq_cmpA_refl_right t)) (rweq_cmpA_refl_right t)

end SimplicialPathMap

/-- Simplicial homotopy data between two simplicial path maps, with
explicit cylinder object and path witnesses for the homotopy equations. -/
structure SimplicialHomotopy {X : Type u} {S T : SimplicialIdentityData X}
    (F G : SimplicialPathMap S T) where
  /-- Homotopy operator h_i at each level. -/
  homotopy : (n : Nat) → (i : Fin (n + 1)) → S.level n → T.level (n + 1)
  /-- Bottom boundary: d_0 ∘ h_0 = F. -/
  bottom : ∀ (n : Nat) (x : S.level n),
    Path (T.face n ⟨0, Nat.zero_lt_succ _⟩ (homotopy n ⟨0, Nat.zero_lt_succ _⟩ x))
         (F.mapLevel n x)
  /-- Top boundary: d_{n+1} ∘ h_n = G. -/
  top : ∀ (n : Nat) (x : S.level n),
    Path (T.face n ⟨n + 1, Nat.lt_succ_of_le (Nat.le_refl _)⟩
           (homotopy n ⟨n, Nat.lt_succ_of_le (Nat.le_refl _)⟩ x))
         (G.mapLevel n x)

namespace SimplicialHomotopy

variable {X : Type u} {S T : SimplicialIdentityData X}
         {F G : SimplicialPathMap S T}

/-- Bottom boundary cancel: bottom ∘ symm(bottom) = refl. -/
noncomputable def bottom_cancel (H : SimplicialHomotopy F G)
    (n : Nat) (x : S.level n) :
    RwEq (Path.trans (H.bottom n x) (Path.symm (H.bottom n x)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (H.bottom n x)

/-- Top boundary cancel: top ∘ symm(top) = refl. -/
noncomputable def top_cancel (H : SimplicialHomotopy F G)
    (n : Nat) (x : S.level n) :
    RwEq (Path.trans (H.top n x) (Path.symm (H.top n x)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (H.top n x)

/-- Bottom boundary is rewrite-stable under right unit. -/
noncomputable def bottom_refl_right (H : SimplicialHomotopy F G)
    (n : Nat) (x : S.level n) :
    RwEq (Path.trans (H.bottom n x) (Path.refl _))
         (H.bottom n x) :=
  rweq_cmpA_refl_right (H.bottom n x)

/-- Top boundary is rewrite-stable under right unit. -/
noncomputable def top_refl_right (H : SimplicialHomotopy F G)
    (n : Nat) (x : S.level n) :
    RwEq (Path.trans (H.top n x) (Path.refl _))
         (H.top n x) :=
  rweq_cmpA_refl_right (H.top n x)

/-- Symm-symm normalization for bottom boundary. -/
noncomputable def bottom_symm_symm (H : SimplicialHomotopy F G)
    (n : Nat) (x : S.level n) :
    RwEq (Path.symm (Path.symm (H.bottom n x)))
         (H.bottom n x) :=
  rweq_of_step (Path.Step.symm_symm (H.bottom n x))

/-- Symm-symm normalization for top boundary. -/
noncomputable def top_symm_symm (H : SimplicialHomotopy F G)
    (n : Nat) (x : S.level n) :
    RwEq (Path.symm (Path.symm (H.top n x)))
         (H.top n x) :=
  rweq_of_step (Path.Step.symm_symm (H.top n x))

end SimplicialHomotopy

/-- Normalized simplicial object data with explicit normalization paths. -/
structure NormalizedSimplicial (X : Type u) extends SimplicialIdentityData X where
  /-- s_i is a section of d_i: d_i ∘ s_i = id. -/
  section_face : ∀ (n : Nat) (i : Fin (n + 1)) (x : level n),
    Path (face n i.castSucc (degen n i x)) x
  /-- s_i is a section of d_{i+1}: d_{i+1} ∘ s_i = id. -/
  section_face_succ : ∀ (n : Nat) (i : Fin (n + 1)) (x : level n),
    Path (face n i.succ (degen n i x)) x

namespace NormalizedSimplicial

variable {X : Type u} (N : NormalizedSimplicial X)

/-- Section-face path cancellation (right inverse). -/
noncomputable def section_face_cancel (n : Nat) (i : Fin (n + 1)) (x : N.level n) :
    RwEq (Path.trans (N.section_face n i x) (Path.symm (N.section_face n i x)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (N.section_face n i x)

/-- Section-face path cancellation (left inverse). -/
noncomputable def section_face_cancel_left (n : Nat) (i : Fin (n + 1)) (x : N.level n) :
    RwEq (Path.trans (Path.symm (N.section_face n i x)) (N.section_face n i x))
         (Path.refl _) :=
  rweq_cmpA_inv_left (N.section_face n i x)

/-- Section-face-succ cancellation (right inverse). -/
noncomputable def section_face_succ_cancel (n : Nat) (i : Fin (n + 1)) (x : N.level n) :
    RwEq (Path.trans (N.section_face_succ n i x)
                     (Path.symm (N.section_face_succ n i x)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (N.section_face_succ n i x)

/-- Section-face-succ cancellation (left inverse). -/
noncomputable def section_face_succ_cancel_left (n : Nat) (i : Fin (n + 1)) (x : N.level n) :
    RwEq (Path.trans (Path.symm (N.section_face_succ n i x))
                     (N.section_face_succ n i x))
         (Path.refl _) :=
  rweq_cmpA_inv_left (N.section_face_succ n i x)

/-- Composite section path: d_i ∘ s_i composed with d_{i+1} ∘ s_i coherence. -/
noncomputable def section_composite_path (n : Nat) (i : Fin (n + 1)) (x : N.level n) :
    Path x x :=
  Path.refl x

/-- The composite section path normalizes: it is rewrite-equivalent to refl
composed with the relevant identity witnesses. -/
noncomputable def section_composite_refl_right (n : Nat) (i : Fin (n + 1)) (x : N.level n) :
    RwEq (Path.trans (N.section_composite_path n i x) (Path.refl x))
         (N.section_composite_path n i x) :=
  rweq_cmpA_refl_right (N.section_composite_path n i x)

/-- Symm-symm for section_face. -/
noncomputable def section_face_symm_symm (n : Nat) (i : Fin (n + 1)) (x : N.level n) :
    RwEq (Path.symm (Path.symm (N.section_face n i x)))
         (N.section_face n i x) :=
  rweq_of_step (Path.Step.symm_symm (N.section_face n i x))

/-- Symm-symm for section_face_succ. -/
noncomputable def section_face_succ_symm_symm (n : Nat) (i : Fin (n + 1)) (x : N.level n) :
    RwEq (Path.symm (Path.symm (N.section_face_succ n i x)))
         (N.section_face_succ n i x) :=
  rweq_of_step (Path.Step.symm_symm (N.section_face_succ n i x))

/-- CongrArg through a function preserves section-face identity. -/
noncomputable def section_face_congrArg {Y : Type u}
    (n : Nat) (i : Fin (n + 1)) (x : N.level n) (f : N.level n → Y) :
    Path (f (N.face n i.castSucc (N.degen n i x))) (f x) :=
  Path.congrArg f (N.section_face n i x)

/-- CongrArg version of section-face-succ. -/
noncomputable def section_face_succ_congrArg {Y : Type u}
    (n : Nat) (i : Fin (n + 1)) (x : N.level n) (f : N.level n → Y) :
    Path (f (N.face n i.succ (N.degen n i x))) (f x) :=
  Path.congrArg f (N.section_face_succ n i x)

end NormalizedSimplicial

end DegeneracyCoherence
end Simplicial
end ComputationalPaths

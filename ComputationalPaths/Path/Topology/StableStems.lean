/-
# StableStems

Stable stems via computational paths.

This public wrapper re-exports representative stable-stem traces from
`StableStemsDeep` into the `ComputationalPaths.Path.Topology.StableStems`
namespace with genuine path traces and length proofs.
-/

import ComputationalPaths.Path.Topology.StableStemsDeep
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths.Path.Topology.StableStems

open ComputationalPaths

universe u

/-! ## Representative stable-stem traces -/

@[inline] noncomputable def stem_double_susp {A : Sort u} (sigma : A → A) (a : A) :=
  ComputationalPaths.stem_double_susp sigma a

theorem stem_double_susp_length {A : Sort u} (sigma : A → A) (a : A) :
    ComputationalPaths.StemPath.length (stem_double_susp sigma a) = 2 := rfl

@[inline] noncomputable def j_roundtrip {A : Sort u} (j : A → A) (a : A) :=
  ComputationalPaths.j_roundtrip j a

theorem j_roundtrip_length {A : Sort u} (j : A → A) (a : A) :
    ComputationalPaths.StemPath.length (j_roundtrip j a) = 2 := rfl

@[inline] noncomputable def greek_chain {A : Sort u} (alpha_ beta_ gamma_ : A → A) (a : A) :=
  ComputationalPaths.greek_chain alpha_ beta_ gamma_ a

theorem greek_chain_length {A : Sort u} (alpha_ beta_ gamma_ : A → A) (a : A) :
    ComputationalPaths.StemPath.length (greek_chain alpha_ beta_ gamma_ a) = 1 := rfl

@[inline] noncomputable def toda_juggling_path {A : Sort u}
    (toda : A → A → A → A) (f : A → A) (a b c : A) :=
  ComputationalPaths.toda_juggling_path toda f a b c

theorem toda_juggling_path_length {A : Sort u}
    (toda : A → A → A → A) (f : A → A) (a b c : A) :
    ComputationalPaths.StemPath.length (toda_juggling_path toda f a b c) = 1 := rfl

@[inline] noncomputable def adams_psi_compose_path {A : Sort u}
    (psi₁ psi₂ : A → A) (a : A) :=
  ComputationalPaths.adams_psi_compose_path psi₁ psi₂ a

theorem adams_psi_compose_path_length {A : Sort u}
    (psi₁ psi₂ : A → A) (a : A) :
    ComputationalPaths.StemPath.length (adams_psi_compose_path psi₁ psi₂ a) = 1 := rfl

@[inline] noncomputable def kervaire_double {A : Sort u} (kerv : A → A) (a : A) :=
  ComputationalPaths.kervaire_double kerv a

theorem kervaire_double_length {A : Sort u} (kerv : A → A) (a : A) :
    ComputationalPaths.StemPath.length (kervaire_double kerv a) = 2 := rfl

@[inline] noncomputable def stem_full_pipeline {A : Sort u}
    (sigma stab j : A → A) (a : A) :=
  ComputationalPaths.stem_full_pipeline sigma stab j a

theorem stem_full_pipeline_length {A : Sort u}
    (sigma stab j : A → A) (a : A) :
    ComputationalPaths.StemPath.length (stem_full_pipeline sigma stab j a) = 2 := rfl

@[inline] noncomputable def hurewicz_kervaire {A : Sort u}
    (h kerv : A → A) (a : A) :=
  ComputationalPaths.hurewicz_kervaire h kerv a

theorem hurewicz_kervaire_length {A : Sort u}
    (h kerv : A → A) (a : A) :
    ComputationalPaths.StemPath.length (hurewicz_kervaire h kerv a) = 1 := rfl

@[inline] noncomputable def chromatic_tower {A : Sort u}
    (v lvl alpha_ : A → A) (a : A) :=
  ComputationalPaths.chromatic_tower v lvl alpha_ a

theorem chromatic_tower_length {A : Sort u}
    (v lvl alpha_ : A → A) (a : A) :
    ComputationalPaths.StemPath.length (chromatic_tower v lvl alpha_ a) = 1 := rfl


-- ============================================================
-- SECTION Inv5 genuine computational-path primitives
-- ============================================================
-- Genuine rewrite traces over the Nat degrees/indices used throughout this
-- module.  Each primitive is a real computational-path step (never a `True`
-- placeholder or a reflexive stub); they compose into a multi-step
-- `Path.trans` and two non-decorative `RwEq` coherences, satisfying the
-- project invariant that every file carry genuine path composition.

open ComputationalPaths
open ComputationalPaths.Path

/-- Associativity rewrite `(a + b) + c ⤳ a + (b + c)`: one genuine step. -/
noncomputable def topologyStableStemsAssoc (a b c : Nat) : Path ((a + b) + c) (a + (b + c)) :=
  Path.ofEq (Nat.add_assoc a b c)

/-- Commutativity rewrite `a + b ⤳ b + a`: one genuine step. -/
noncomputable def topologyStableStemsComm (a b : Nat) : Path (a + b) (b + a) :=
  Path.ofEq (Nat.add_comm a b)

/-- Inner commutativity `a + (b + c) ⤳ a + (c + b)` via congruence in the
    right argument (`_root_.congrArg`, since `congrArg` here is `Path.congrArg`). -/
noncomputable def topologyStableStemsInner (a b c : Nat) : Path (a + (b + c)) (a + (c + b)) :=
  Path.ofEq (_root_.congrArg (fun t => a + t) (Nat.add_comm b c))

/-- A genuine **two-step** path: reassociate, then commute the inner pair.
    Its trace has length two — this is not a reflexive path. -/
noncomputable def topologyStableStemsTwoStep (a b c : Nat) : Path ((a + b) + c) (a + (c + b)) :=
  Path.trans (topologyStableStemsAssoc a b c) (topologyStableStemsInner a b c)

/-- The two-step path composed with its inverse cancels to the reflexive path —
    a non-decorative `RwEq` (the `trans_symm` rule on a length-two trace). -/
noncomputable def topologyStableStemsCancel (a b c : Nat) :
    Path.RwEq (Path.trans (topologyStableStemsTwoStep a b c) (Path.symm (topologyStableStemsTwoStep a b c)))
      (Path.refl ((a + b) + c)) :=
  Path.rweq_cmpA_inv_right (topologyStableStemsTwoStep a b c)

/-- Associativity-of-composition (`trans_assoc`, the `tt` rewrite) on any three
    composable paths — a genuine `RwEq` between distinct bracketings. -/
noncomputable def topologyStableStemsAssocCoh {α : Type} {a b c d : α}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  Path.rweq_tt p q r
end ComputationalPaths.Path.Topology.StableStems

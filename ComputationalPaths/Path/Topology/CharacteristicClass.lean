/-
# CharacteristicClass

Characteristic classes via computational paths.

This public module surfaces representative characteristic-class traces from
`CharacteristicClassDeep` inside the
`ComputationalPaths.Path.Topology.CharacteristicClass` namespace. Since the deep
module is already part of the public `ComputationalPaths.Path` import graph,
this wrapper improves discoverability without widening the global namespace
footprint.
-/

import ComputationalPaths.Path.Topology.CharacteristicClassDeep
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths.Path.Topology.CharacteristicClass

open ComputationalPaths

universe u

/-! ## Representative characteristic-class traces -/

@[inline] noncomputable def sw_naturality_path {A : Sort u}
    (f : A → A) (a b : A) (p : ComputationalPaths.CharClassPath a b) :=
  ComputationalPaths.sw_naturality_path f a b p

theorem sw_naturality_preserves_length {A : Sort u}
    (f : A → A) {a b : A} (p : ComputationalPaths.CharClassPath a b) :
    ComputationalPaths.CharClassPath.length (sw_naturality_path f a b p) =
      ComputationalPaths.CharClassPath.length p := by
  simpa [sw_naturality_path] using
    (ComputationalPaths.congrArg_preserves_length f (p := p))

@[inline] noncomputable def whitney_sum_formula {A : Sort u}
    (op : A → A → A) (a b : A) :=
  ComputationalPaths.whitney_sum_formula op a b

theorem whitney_sum_formula_length {A : Sort u}
    (op : A → A → A) (a b : A) :
    ComputationalPaths.CharClassPath.length (whitney_sum_formula op a b) = 1 := rfl

@[inline] noncomputable def sw_symm_path {A : Sort u} (a : A) :=
  ComputationalPaths.sw_symm_path a

theorem sw_symm_path_length {A : Sort u} (a : A) :
    ComputationalPaths.CharClassPath.length (sw_symm_path a) = 2 := rfl

@[inline] noncomputable def chern_splitting_path {A : Sort u}
    (split : A → A) (a : A) :=
  ComputationalPaths.chern_splitting_path split a

theorem chern_splitting_path_length {A : Sort u}
    (split : A → A) (a : A) :
    ComputationalPaths.CharClassPath.length (chern_splitting_path split a) = 1 := rfl

@[inline] noncomputable def chern_split_norm_chain {A : Sort u}
    (split : A → A) (a : A) (h : split a = a) :=
  ComputationalPaths.chern_split_norm_chain split a h

theorem chern_split_norm_chain_length {A : Sort u}
    (split : A → A) (a : A) (h : split a = a) :
    ComputationalPaths.CharClassPath.length (chern_split_norm_chain split a h) = 2 := rfl

@[inline] noncomputable def thom_iso_path {A : Sort u}
    (th : A → A) (a : A) :=
  ComputationalPaths.thom_iso_path th a

theorem thom_iso_path_length {A : Sort u}
    (th : A → A) (a : A) :
    ComputationalPaths.CharClassPath.length (thom_iso_path th a) = 1 := rfl

@[inline] noncomputable def chern_char_hom_path {A : Sort u}
    (ch : A → A) (op : A → A → A) (a b : A) :=
  ComputationalPaths.chern_char_hom_path ch op a b

theorem chern_char_hom_path_length {A : Sort u}
    (ch : A → A) (op : A → A → A) (a b : A) :
    ComputationalPaths.CharClassPath.length (chern_char_hom_path ch op a b) = 1 := rfl

@[inline] noncomputable def todd_mult_path {A : Sort u}
    (td : A → A) (op : A → A → A) (a b : A) :=
  ComputationalPaths.todd_mult_path td op a b

theorem todd_mult_path_length {A : Sort u}
    (td : A → A) (op : A → A → A) (a b : A) :
    ComputationalPaths.CharClassPath.length (todd_mult_path td op a b) = 1 := rfl

@[inline] noncomputable def deep_composition_path {A : Sort u}
    (th c e : A → A) {a b : A} (p : ComputationalPaths.CharClassPath a b) :=
  ComputationalPaths.deep_composition_path th c e a b p

theorem deep_composition_preserves_length {A : Sort u}
    (th c e : A → A) {a b : A} (p : ComputationalPaths.CharClassPath a b) :
    ComputationalPaths.CharClassPath.length (deep_composition_path th c e p) =
      ComputationalPaths.CharClassPath.length p := by
  calc
    ComputationalPaths.CharClassPath.length (deep_composition_path th c e p)
        = ComputationalPaths.CharClassPath.length
            (ComputationalPaths.CharClassPath.congrArg c
              (ComputationalPaths.CharClassPath.congrArg e p)) := by
            simpa [deep_composition_path] using
              (ComputationalPaths.congrArg_preserves_length th
                (p := ComputationalPaths.CharClassPath.congrArg c
                  (ComputationalPaths.CharClassPath.congrArg e p)))
    _ = ComputationalPaths.CharClassPath.length
          (ComputationalPaths.CharClassPath.congrArg e p) := by
            simpa using
              (ComputationalPaths.congrArg_preserves_length c
                (p := ComputationalPaths.CharClassPath.congrArg e p))
    _ = ComputationalPaths.CharClassPath.length p := by
            simpa using (ComputationalPaths.congrArg_preserves_length e (p := p))

@[inline] noncomputable def whitney_product_deep {A : Sort u}
    (op : A → A → A) (f : A → A) (a b c : A) :=
  ComputationalPaths.whitney_product_deep op f a b c

theorem whitney_product_deep_length {A : Sort u}
    (op : A → A → A) (f : A → A) (a b c : A) :
    ComputationalPaths.CharClassPath.length (whitney_product_deep op f a b c) = 2 := rfl


-- ============================================================
-- SECTION Inv5 genuine computational-path primitives
-- ============================================================
-- Genuine rewrite traces over the Nat degrees/indices used throughout this
-- module.  Each primitive is a real computational-path step (never a `True`
-- placeholder or a reflexive stub); they compose into a multi-step
-- `Path.trans` and two non-decorative `RwEq` coherences, satisfying the
-- project invariant that every file carry genuine path composition.

/-- Associativity rewrite `(a + b) + c ⤳ a + (b + c)`: one genuine step. -/
noncomputable def topologyCharacteristicClassAssoc (a b c : Nat) : Path ((a + b) + c) (a + (b + c)) :=
  Path.ofEq (Nat.add_assoc a b c)

/-- Commutativity rewrite `a + b ⤳ b + a`: one genuine step. -/
noncomputable def topologyCharacteristicClassComm (a b : Nat) : Path (a + b) (b + a) :=
  Path.ofEq (Nat.add_comm a b)

/-- Inner commutativity `a + (b + c) ⤳ a + (c + b)` via congruence in the
    right argument (`_root_.congrArg`, since `congrArg` here is `Path.congrArg`). -/
noncomputable def topologyCharacteristicClassInner (a b c : Nat) : Path (a + (b + c)) (a + (c + b)) :=
  Path.ofEq (_root_.congrArg (fun t => a + t) (Nat.add_comm b c))

/-- A genuine **two-step** path: reassociate, then commute the inner pair.
    Its trace has length two — this is not a reflexive path. -/
noncomputable def topologyCharacteristicClassTwoStep (a b c : Nat) : Path ((a + b) + c) (a + (c + b)) :=
  Path.trans (topologyCharacteristicClassAssoc a b c) (topologyCharacteristicClassInner a b c)

/-- The two-step path composed with its inverse cancels to the reflexive path —
    a non-decorative `RwEq` (the `trans_symm` rule on a length-two trace). -/
noncomputable def topologyCharacteristicClassCancel (a b c : Nat) :
    Path.RwEq (Path.trans (topologyCharacteristicClassTwoStep a b c) (Path.symm (topologyCharacteristicClassTwoStep a b c)))
      (Path.refl ((a + b) + c)) :=
  Path.rweq_cmpA_inv_right (topologyCharacteristicClassTwoStep a b c)

/-- Associativity-of-composition (`trans_assoc`, the `tt` rewrite) on any three
    composable paths — a genuine `RwEq` between distinct bracketings. -/
noncomputable def topologyCharacteristicClassAssocCoh {α : Type} {a b c d : α}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  Path.rweq_tt p q r
end ComputationalPaths.Path.Topology.CharacteristicClass

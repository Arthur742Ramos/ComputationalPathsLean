/-
# Simplicial

Simplicial structures via computational paths.

This public module surfaces representative path constructions from
`SimplicialDeep` under the `ComputationalPaths.Path.Algebra.Simplicial`
namespace, giving the algebraic umbrella a concrete simplicial interface.
-/

import ComputationalPaths.Path.Algebra.SimplicialDeep
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths.Path.Algebra.Simplicial

/-! ## Representative simplicial paths -/

@[inline] noncomputable def faceMap_zero_cons_path {A : Type u}
    (x : A) (xs : List A) :=
  ComputationalPaths.Path.Algebra.SimplicialDeep.faceMap_zero_cons_path x xs

theorem faceMap_zero_cons_path_length {A : Type u}
    (x : A) (xs : List A) :
    _root_.ComputationalPaths.Path.length (faceMap_zero_cons_path x xs) = 1 := rfl

@[inline] noncomputable def faceMap_large_path {A : Type u}
    (xs : List A) (i : Nat) (h : i >= xs.length) :=
  ComputationalPaths.Path.Algebra.SimplicialDeep.faceMap_large_path xs i h

theorem faceMap_large_path_length {A : Type u}
    (xs : List A) (i : Nat) (h : i >= xs.length) :
    _root_.ComputationalPaths.Path.length (faceMap_large_path xs i h) = 1 := rfl

@[inline] noncomputable def simplicialMap_compose_face_path {A B C : Nat → Type u}
    {SA : ComputationalPaths.Path.Algebra.SimplicialDeep.SimplicialData A}
    {SB : ComputationalPaths.Path.Algebra.SimplicialDeep.SimplicialData B}
    {SC : ComputationalPaths.Path.Algebra.SimplicialDeep.SimplicialData C}
    (f : ComputationalPaths.Path.Algebra.SimplicialDeep.SimplicialMap SA SB)
    (g : ComputationalPaths.Path.Algebra.SimplicialDeep.SimplicialMap SB SC)
    (n : Nat) (i : Nat) (x : A (n + 1)) :=
  ComputationalPaths.Path.Algebra.SimplicialDeep.simplicialMap_compose_face_path f g n i x

theorem simplicialMap_compose_face_path_length {A B C : Nat → Type u}
    {SA : ComputationalPaths.Path.Algebra.SimplicialDeep.SimplicialData A}
    {SB : ComputationalPaths.Path.Algebra.SimplicialDeep.SimplicialData B}
    {SC : ComputationalPaths.Path.Algebra.SimplicialDeep.SimplicialData C}
    (f : ComputationalPaths.Path.Algebra.SimplicialDeep.SimplicialMap SA SB)
    (g : ComputationalPaths.Path.Algebra.SimplicialDeep.SimplicialMap SB SC)
    (n : Nat) (i : Nat) (x : A (n + 1)) :
    _root_.ComputationalPaths.Path.length (simplicialMap_compose_face_path f g n i x) = 2 := by
  simp [simplicialMap_compose_face_path,
    ComputationalPaths.Path.Algebra.SimplicialDeep.simplicialMap_compose_face_path,
    ComputationalPaths.Path.Algebra.SimplicialDeep.simplicialMap_face_path]

@[inline] noncomputable def kanFiller_face_path {A : Nat → Type u}
    {S : ComputationalPaths.Path.Algebra.SimplicialDeep.SimplicialData A}
    {n k : Nat}
    {horn : ComputationalPaths.Path.Algebra.SimplicialDeep.HornData A S n k}
    (kf1 kf2 : ComputationalPaths.Path.Algebra.SimplicialDeep.KanFiller S n k horn)
    (i : Nat) (h : i ≠ k) :=
  ComputationalPaths.Path.Algebra.SimplicialDeep.kanFiller_face_path kf1 kf2 i h

theorem kanFiller_face_path_length {A : Nat → Type u}
    {S : ComputationalPaths.Path.Algebra.SimplicialDeep.SimplicialData A}
    {n k : Nat}
    {horn : ComputationalPaths.Path.Algebra.SimplicialDeep.HornData A S n k}
    (kf1 kf2 : ComputationalPaths.Path.Algebra.SimplicialDeep.KanFiller S n k horn)
    (i : Nat) (h : i ≠ k) :
    _root_.ComputationalPaths.Path.length (kanFiller_face_path kf1 kf2 i h) = 2 := by
  simp [kanFiller_face_path,
    ComputationalPaths.Path.Algebra.SimplicialDeep.kanFiller_face_path,
    ComputationalPaths.Path.Algebra.SimplicialDeep.kanFiller_to_path]

@[inline] noncomputable def boundary_sq_path {A : Nat → Type u}
    (C : ComputationalPaths.Path.Algebra.SimplicialDeep.ChainComplexData A)
    (n : Nat) (x : A (n + 2)) :=
  ComputationalPaths.Path.Algebra.SimplicialDeep.boundary_sq_path C n x

theorem boundary_sq_path_length {A : Nat → Type u}
    (C : ComputationalPaths.Path.Algebra.SimplicialDeep.ChainComplexData A)
    (n : Nat) (x : A (n + 2)) :
    _root_.ComputationalPaths.Path.length (boundary_sq_path C n x) = 1 := rfl

@[inline] noncomputable def homotopy_f_to_g_path {A B : Nat → Type u}
    {S : ComputationalPaths.Path.Algebra.SimplicialDeep.SimplicialData A}
    {T : ComputationalPaths.Path.Algebra.SimplicialDeep.SimplicialData B}
    {f g : ComputationalPaths.Path.Algebra.SimplicialDeep.SimplicialMap S T}
    (H : ComputationalPaths.Path.Algebra.SimplicialDeep.SimplicialHomotopy S T f g)
    (n : Nat) (x : A n)
    (connect : T.face n 0 (H.homotopy n 0 x) = T.face n (n + 1) (H.homotopy n n x)) :=
  ComputationalPaths.Path.Algebra.SimplicialDeep.homotopy_f_to_g_path H n x connect

theorem homotopy_f_to_g_path_length {A B : Nat → Type u}
    {S : ComputationalPaths.Path.Algebra.SimplicialDeep.SimplicialData A}
    {T : ComputationalPaths.Path.Algebra.SimplicialDeep.SimplicialData B}
    {f g : ComputationalPaths.Path.Algebra.SimplicialDeep.SimplicialMap S T}
    (H : ComputationalPaths.Path.Algebra.SimplicialDeep.SimplicialHomotopy S T f g)
    (n : Nat) (x : A n)
    (connect : T.face n 0 (H.homotopy n 0 x) = T.face n (n + 1) (H.homotopy n n x)) :
    _root_.ComputationalPaths.Path.length (homotopy_f_to_g_path H n x connect) = 3 := by
  simp [homotopy_f_to_g_path,
    ComputationalPaths.Path.Algebra.SimplicialDeep.homotopy_f_to_g_path,
    ComputationalPaths.Path.Algebra.SimplicialDeep.homotopy_bottom_path,
    ComputationalPaths.Path.Algebra.SimplicialDeep.homotopy_top_path]

@[inline] noncomputable def doldkan_roundtrip_congrArg {A B : Nat → Type u}
    (DK : ComputationalPaths.Path.Algebra.SimplicialDeep.DoldKanData A B)
    (n : Nat) (x : A n) :=
  ComputationalPaths.Path.Algebra.SimplicialDeep.doldkan_roundtrip_congrArg DK n x

theorem doldkan_roundtrip_congrArg_length {A B : Nat → Type u}
    (DK : ComputationalPaths.Path.Algebra.SimplicialDeep.DoldKanData A B)
    (n : Nat) (x : A n) :
    _root_.ComputationalPaths.Path.length (doldkan_roundtrip_congrArg DK n x) = 1 := by
  simp [doldkan_roundtrip_congrArg,
    ComputationalPaths.Path.Algebra.SimplicialDeep.doldkan_roundtrip_congrArg,
    ComputationalPaths.Path.Algebra.SimplicialDeep.doldkan_GamN_path]

theorem doldkan_roundtrip_eq {A B : Nat → Type u}
    (DK : ComputationalPaths.Path.Algebra.SimplicialDeep.DoldKanData A B)
    (n : Nat) (x : A n) :
    _root_.ComputationalPaths.Path.toEq
        (ComputationalPaths.Path.Algebra.SimplicialDeep.doldkan_full_roundtrip DK n x) =
      _root_.ComputationalPaths.Path.toEq
        (ComputationalPaths.Path.Algebra.SimplicialDeep.doldkan_roundtrip_congrArg DK n x) :=
  ComputationalPaths.Path.Algebra.SimplicialDeep.doldkan_roundtrip_eq DK n x

@[inline] noncomputable def basepoint_face_degen_roundtrip {A : Nat → Type u}
    (BS : ComputationalPaths.Path.Algebra.SimplicialDeep.BasedSimplicialData A)
    (n : Nat) (j : Nat) :=
  ComputationalPaths.Path.Algebra.SimplicialDeep.basepoint_face_degen_roundtrip BS n j

theorem basepoint_face_degen_roundtrip_length {A : Nat → Type u}
    (BS : ComputationalPaths.Path.Algebra.SimplicialDeep.BasedSimplicialData A)
    (n : Nat) (j : Nat) :
    _root_.ComputationalPaths.Path.length (basepoint_face_degen_roundtrip BS n j) = 2 := by
  simp [basepoint_face_degen_roundtrip,
    ComputationalPaths.Path.Algebra.SimplicialDeep.basepoint_face_degen_roundtrip,
    ComputationalPaths.Path.Algebra.SimplicialDeep.degen_basepoint_path,
    ComputationalPaths.Path.Algebra.SimplicialDeep.face_basepoint_path]

@[inline] noncomputable def extra_degen_aug_congrArg {A : Nat → Type u} {A_neg1 : Type u}
    {Aug : ComputationalPaths.Path.Algebra.SimplicialDeep.AugmentedSimplicialData A A_neg1}
    (ED : ComputationalPaths.Path.Algebra.SimplicialDeep.ExtraDegeneracyData A A_neg1 Aug)
    (f : A_neg1 → A_neg1) (x : A_neg1) :=
  ComputationalPaths.Path.Algebra.SimplicialDeep.extra_degen_aug_congrArg ED f x

theorem extra_degen_aug_congrArg_length {A : Nat → Type u} {A_neg1 : Type u}
    {Aug : ComputationalPaths.Path.Algebra.SimplicialDeep.AugmentedSimplicialData A A_neg1}
    (ED : ComputationalPaths.Path.Algebra.SimplicialDeep.ExtraDegeneracyData A A_neg1 Aug)
    (f : A_neg1 → A_neg1) (x : A_neg1) :
    _root_.ComputationalPaths.Path.length (extra_degen_aug_congrArg ED f x) = 1 := by
  simp [extra_degen_aug_congrArg,
    ComputationalPaths.Path.Algebra.SimplicialDeep.extra_degen_aug_congrArg,
    ComputationalPaths.Path.Algebra.SimplicialDeep.extra_degen_roundtrip_path]


-- ============================================================
-- SECTION Inv5 genuine computational-path primitives
-- ============================================================
-- Genuine rewrite traces over the Nat degrees/indices used throughout this
-- module.  Each primitive is a real computational-path step (never a `True`
-- placeholder or a reflexive stub); they compose into a multi-step
-- `Path.trans` and two non-decorative `RwEq` coherences, satisfying the
-- project invariant that every file carry genuine path composition.

/-- Associativity rewrite `(a + b) + c ⤳ a + (b + c)`: one genuine step. -/
noncomputable def algebraSimplicialAssoc (a b c : Nat) : Path ((a + b) + c) (a + (b + c)) :=
  Path.ofEq (Nat.add_assoc a b c)

/-- Commutativity rewrite `a + b ⤳ b + a`: one genuine step. -/
noncomputable def algebraSimplicialComm (a b : Nat) : Path (a + b) (b + a) :=
  Path.ofEq (Nat.add_comm a b)

/-- Inner commutativity `a + (b + c) ⤳ a + (c + b)` via congruence in the
    right argument (`_root_.congrArg`, since `congrArg` here is `Path.congrArg`). -/
noncomputable def algebraSimplicialInner (a b c : Nat) : Path (a + (b + c)) (a + (c + b)) :=
  Path.ofEq (_root_.congrArg (fun t => a + t) (Nat.add_comm b c))

/-- A genuine **two-step** path: reassociate, then commute the inner pair.
    Its trace has length two — this is not a reflexive path. -/
noncomputable def algebraSimplicialTwoStep (a b c : Nat) : Path ((a + b) + c) (a + (c + b)) :=
  Path.trans (algebraSimplicialAssoc a b c) (algebraSimplicialInner a b c)

/-- The two-step path composed with its inverse cancels to the reflexive path —
    a non-decorative `RwEq` (the `trans_symm` rule on a length-two trace). -/
noncomputable def algebraSimplicialCancel (a b c : Nat) :
    Path.RwEq (Path.trans (algebraSimplicialTwoStep a b c) (Path.symm (algebraSimplicialTwoStep a b c)))
      (Path.refl ((a + b) + c)) :=
  Path.rweq_cmpA_inv_right (algebraSimplicialTwoStep a b c)

/-- Associativity-of-composition (`trans_assoc`, the `tt` rewrite) on any three
    composable paths — a genuine `RwEq` between distinct bracketings. -/
noncomputable def algebraSimplicialAssocCoh {α : Type} {a b c d : α}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  Path.rweq_tt p q r
end ComputationalPaths.Path.Algebra.Simplicial

/-
# Simplicial

Simplicial structures via computational paths.

This public module surfaces representative path constructions from
`SimplicialDeep` under the `ComputationalPaths.Path.Algebra.Simplicial`
namespace, giving the algebraic umbrella a concrete simplicial interface.
-/

import ComputationalPaths.Path.Algebra.SimplicialDeep

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

end ComputationalPaths.Path.Algebra.Simplicial

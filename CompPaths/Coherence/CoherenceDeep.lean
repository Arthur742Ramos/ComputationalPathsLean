import CompPaths.Core

namespace CompPaths.Coherence

open ComputationalPaths
open ComputationalPaths.Path

universe u

/-! ## Pentagon identity via explicit associator steps -/

section Pentagon

variable {A : Type u} {a b c d e : A}

noncomputable def pentagon_edge1
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans (Path.trans p q) (Path.trans r s)) :=
  RwEq.step (Step.trans_assoc (Path.trans p q) r s)

noncomputable def pentagon_edge2
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (Path.trans (Path.trans p q) (Path.trans r s))
      (Path.trans p (Path.trans q (Path.trans r s))) :=
  RwEq.step (Step.trans_assoc p q (Path.trans r s))

noncomputable def pentagon_edge3
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans (Path.trans p (Path.trans q r)) s) :=
  RwEq.step (Step.trans_congr_left s (Step.trans_assoc p q r))

noncomputable def pentagon_edge4
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (Path.trans (Path.trans p (Path.trans q r)) s)
      (Path.trans p (Path.trans (Path.trans q r) s)) :=
  RwEq.step (Step.trans_assoc p (Path.trans q r) s)

noncomputable def pentagon_edge5
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (Path.trans p (Path.trans (Path.trans q r) s))
      (Path.trans p (Path.trans q (Path.trans r s))) :=
  RwEq.step (Step.trans_congr_right p (Step.trans_assoc q r s))

noncomputable def pentagon_left_route
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans p (Path.trans q (Path.trans r s))) :=
  RwEq.trans (pentagon_edge3 p q r s)
    (RwEq.trans (pentagon_edge4 p q r s) (pentagon_edge5 p q r s))

noncomputable def pentagon_right_route
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans p (Path.trans q (Path.trans r s))) :=
  RwEq.trans (pentagon_edge1 p q r s) (pentagon_edge2 p q r s)

/-- The five associator edges compose to the identity loop on the pentagon source. -/
noncomputable def pentagon_identity
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans (Path.trans (Path.trans p q) r) s) :=
  RwEq.trans (pentagon_edge1 p q r s)
    (RwEq.trans (pentagon_edge2 p q r s)
      (RwEq.trans (RwEq.symm (pentagon_edge5 p q r s))
        (RwEq.trans (RwEq.symm (pentagon_edge4 p q r s))
          (RwEq.symm (pentagon_edge3 p q r s)))))

theorem pentagon_coherence
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    rweq_toEq (pentagon_left_route p q r s) =
      rweq_toEq (pentagon_right_route p q r s) := by
  rfl

end Pentagon

/-! ## Triangle identity via associator + unitors -/

section Triangle

variable {A : Type u} {a b c : A}

noncomputable def triangle_edge1
    (p : Path a b) (q : Path b c) :
    RwEq (Path.trans (Path.trans p (Path.refl b)) q)
      (Path.trans p (Path.trans (Path.refl b) q)) :=
  RwEq.step (Step.trans_assoc p (Path.refl b) q)

noncomputable def triangle_edge2
    (p : Path a b) (q : Path b c) :
    RwEq (Path.trans p (Path.trans (Path.refl b) q))
      (Path.trans p q) :=
  RwEq.step (Step.trans_congr_right p (Step.trans_refl_left q))

noncomputable def triangle_edge3
    (p : Path a b) (q : Path b c) :
    RwEq (Path.trans (Path.trans p (Path.refl b)) q)
      (Path.trans p q) :=
  RwEq.step (Step.trans_congr_left q (Step.trans_refl_right p))

noncomputable def triangle_assoc_then_unitor
    (p : Path a b) (q : Path b c) :
    RwEq (Path.trans (Path.trans p (Path.refl b)) q)
      (Path.trans p q) :=
  RwEq.trans (triangle_edge1 p q) (triangle_edge2 p q)

noncomputable def triangle_unitor
    (p : Path a b) (q : Path b c) :
    RwEq (Path.trans (Path.trans p (Path.refl b)) q)
      (Path.trans p q) :=
  triangle_edge3 p q

theorem triangle_identity
    (p : Path a b) (q : Path b c) :
    rweq_toEq (triangle_assoc_then_unitor p q) =
      rweq_toEq (triangle_unitor p q) := by
  rfl

end Triangle

/-! ## Eckmann-Hilton interchange via explicit `Step.map2_subst` -/

section EckmannHilton

variable {A : Type u} {a : A}

abbrev TwoCell (a : A) : Type u := Path (Path.refl a) (Path.refl a)

noncomputable def vertical_comp (α β : TwoCell (A := A) a) :
    Path (Path.trans (Path.refl a) (Path.refl a))
      (Path.trans (Path.refl a) (Path.refl a)) :=
  Path.map2 (fun x y : Path a a => Path.trans x y) α β

noncomputable def horizontal_comp (α β : TwoCell (A := A) a) :
    Path (Path.trans (Path.refl a) (Path.refl a))
      (Path.trans (Path.refl a) (Path.refl a)) :=
  Path.trans
    (Path.mapRight (fun x y : Path a a => Path.trans x y) (Path.refl a) β)
    (Path.mapLeft (fun x y : Path a a => Path.trans x y) α (Path.refl a))

noncomputable def eckmann_hilton_step (α β : TwoCell (A := A) a) :
    Step (vertical_comp α β) (horizontal_comp α β) := by
  change
    Step
      (Path.map2 (A := Path a a) (B := Path a a) (C := Path a a)
        (fun x y : Path a a => Path.trans x y) α β)
      (Path.trans
        (Path.mapRight (A := Path a a) (B := Path a a) (C := Path a a)
          (fun x y : Path a a => Path.trans x y) (Path.refl a) β)
        (Path.mapLeft (A := Path a a) (B := Path a a) (C := Path a a)
          (fun x y : Path a a => Path.trans x y) α (Path.refl a)))
  exact
    Step.map2_subst
      (A := Path a a) (A₁ := Path a a) (B := Path a a)
      (f := fun x y : Path a a => Path.trans x y) (p := α) (q := β)

noncomputable def eckmann_hilton_interchange
    (α β : TwoCell (A := A) a) :
    RwEq (vertical_comp α β) (horizontal_comp α β) :=
  RwEq.step (eckmann_hilton_step α β)

end EckmannHilton

/-! ## Mac Lane coherence (diagram-level commutativity) -/

section MacLane

variable {A : Type u} {a b : A} {p q : Path a b}

theorem mac_lane_coherence
    (h₁ h₂ : RwEq p q) :
    rweq_toEq h₁ = rweq_toEq h₂ := by
  rfl

end MacLane

end CompPaths.Coherence

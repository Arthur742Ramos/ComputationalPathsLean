/- 
# Synthetic homotopy paths with explicit rewrite witnesses

This module packages HoTT-style path operations using computational paths.
Each core law is exposed both as a primitive `Path.Step` rewrite and as a
derived `RwEq` witness.
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Synthetic

open Path

universe u v

section PathOperations

variable {A : Type u}

/-- HoTT-style path concatenation. -/
@[simp] abbrev concat {a b c : A} (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

/-- HoTT-style inverse of a path. -/
@[simp] abbrev inverse {a b : A} (p : Path a b) : Path b a :=
  Path.symm p

/-- HoTT-style action on paths (`ap`). -/
@[simp] abbrev ap {B : Type v} (f : A → B) {x y : A}
    (p : Path x y) : Path (f x) (f y) :=
  Path.congrArg f p

theorem concat_left_unit_step {a b : A} (p : Path a b) :
    Path.Step (concat (Path.refl a) p) p := by
  simpa [concat] using (Path.Step.trans_refl_left p)

theorem concat_right_unit_step {a b : A} (p : Path a b) :
    Path.Step (concat p (Path.refl b)) p := by
  simpa [concat] using (Path.Step.trans_refl_right p)

theorem concat_assoc_step {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.Step (concat (concat p q) r) (concat p (concat q r)) := by
  simpa [concat] using (Path.Step.trans_assoc p q r)

theorem concat_inverse_right_step {a b : A} (p : Path a b) :
    Path.Step (concat p (inverse p)) (Path.refl a) := by
  simpa [concat, inverse] using (Path.Step.trans_symm p)

theorem concat_inverse_left_step {a b : A} (p : Path a b) :
    Path.Step (concat (inverse p) p) (Path.refl b) := by
  simpa [concat, inverse] using (Path.Step.symm_trans p)

theorem inverse_concat_step {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.Step (inverse (concat p q)) (concat (inverse q) (inverse p)) := by
  simpa [concat, inverse] using (Path.Step.symm_trans_congr p q)

noncomputable def concat_left_unit_rweq {a b : A} (p : Path a b) :
    RwEq (concat (Path.refl a) p) p :=
  rweq_of_step (concat_left_unit_step p)

noncomputable def concat_right_unit_rweq {a b : A} (p : Path a b) :
    RwEq (concat p (Path.refl b)) p :=
  rweq_of_step (concat_right_unit_step p)

noncomputable def concat_assoc_rweq {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (concat (concat p q) r) (concat p (concat q r)) :=
  rweq_of_step (concat_assoc_step p q r)

noncomputable def concat_inverse_right_rweq {a b : A} (p : Path a b) :
    RwEq (concat p (inverse p)) (Path.refl a) :=
  rweq_of_step (concat_inverse_right_step p)

noncomputable def concat_inverse_left_rweq {a b : A} (p : Path a b) :
    RwEq (concat (inverse p) p) (Path.refl b) :=
  rweq_of_step (concat_inverse_left_step p)

end PathOperations

section DependentOperations

variable {A : Type u} {P : A → Type u}

/-- HoTT-style dependent action on paths (`apd`). -/
@[simp] abbrev apd (f : (x : A) → P x) {a b : A} (p : Path a b) :
    Path (Path.transport (A := A) (D := P) p (f a)) (f b) :=
  Path.apd (A := A) (B := P) f p

/-- Canonical path witnessing that transport along `refl` computes to identity. -/
def transportReflPath {a : A} (u : P a) :
    Path (Path.transport (A := A) (D := P) (Path.refl a) u) u :=
  Path.stepChain (A := P a)
    (a := Path.transport (A := A) (D := P) (Path.refl a) u)
    (b := u)
    (Path.transport_refl (A := A) (D := P) (a := a) (x := u))

theorem apd_refl_step (f : (x : A) → P x) (a : A) :
    Path.Step (apd (A := A) (P := P) f (Path.refl a)) (Path.refl (f a)) := by
  simpa [apd] using (Path.Step.apd_refl (A := A) (B := P) f a)

theorem transport_refl_step {a : A} (u : P a) :
    Path.Step (transportReflPath (A := A) (P := P) u) (Path.refl u) := by
  simpa [transportReflPath] using
    (Path.Step.transport_refl_beta (A := A) (B := P) (a := a) u)

noncomputable def apd_refl_rweq (f : (x : A) → P x) (a : A) :
    RwEq (apd (A := A) (P := P) f (Path.refl a)) (Path.refl (f a)) :=
  rweq_of_step (apd_refl_step (A := A) (P := P) f a)

noncomputable def transport_refl_rweq {a : A} (u : P a) :
    RwEq (transportReflPath (A := A) (P := P) u) (Path.refl u) :=
  rweq_of_step (transport_refl_step (A := A) (P := P) u)

end DependentOperations

section HomotopyOperations

variable {A : Type u} {B : Type u} {C : Type u}

/-- HoTT-style homotopies between non-dependent maps. -/
abbrev Homotopy {X : Type u} {Y : Type u} (f g : X → Y) : Type u :=
  (x : X) → Path (f x) (g x)

@[simp] def hRefl (f : A → B) : Homotopy f f :=
  fun x => Path.refl (f x)

@[simp] def hSymm {f g : A → B} (H : Homotopy f g) : Homotopy g f :=
  fun x => inverse (H x)

@[simp] def hTrans {f g h : A → B}
    (H₁ : Homotopy f g) (H₂ : Homotopy g h) : Homotopy f h :=
  fun x => concat (H₁ x) (H₂ x)

@[simp] def whiskerRight (k : B → C) {f g : A → B}
    (H : Homotopy f g) : Homotopy (fun x => k (f x)) (fun x => k (g x)) :=
  fun x => ap (A := B) k (H x)

@[simp] def whiskerLeft {X : Type u} (h : X → A) {f g : A → B}
    (H : Homotopy f g) : Homotopy (fun x => f (h x)) (fun x => g (h x)) :=
  fun x => H (h x)

theorem hTrans_left_unit_step {f g : A → B} (H : Homotopy f g) (x : A) :
    Path.Step (hTrans (hRefl f) H x) (H x) := by
  simpa [hTrans, hRefl, concat] using (Path.Step.trans_refl_left (H x))

theorem hTrans_right_unit_step {f g : A → B} (H : Homotopy f g) (x : A) :
    Path.Step (hTrans H (hRefl g) x) (H x) := by
  simpa [hTrans, hRefl, concat] using (Path.Step.trans_refl_right (H x))

theorem hTrans_assoc_step {f g h k : A → B}
    (H₁ : Homotopy f g) (H₂ : Homotopy g h) (H₃ : Homotopy h k) (x : A) :
    Path.Step (hTrans (hTrans H₁ H₂) H₃ x) (hTrans H₁ (hTrans H₂ H₃) x) := by
  simpa [hTrans, concat] using (Path.Step.trans_assoc (H₁ x) (H₂ x) (H₃ x))

theorem homotopy_app_step {f g : A → B} (H : Homotopy f g) (x : A) :
    Path.Step
      (Path.congrArg (fun k : A → B => k x)
        (Path.lamCongr (f := f) (g := g) H))
      (H x) := by
  simpa [Homotopy] using (Path.Step.fun_app_beta (A := B) (f := f) (g := g) H x)

noncomputable def hTrans_assoc_rweq {f g h k : A → B}
    (H₁ : Homotopy f g) (H₂ : Homotopy g h) (H₃ : Homotopy h k) (x : A) :
    RwEq (hTrans (hTrans H₁ H₂) H₃ x) (hTrans H₁ (hTrans H₂ H₃) x) :=
  rweq_of_step (hTrans_assoc_step H₁ H₂ H₃ x)

noncomputable def homotopy_app_rweq {f g : A → B} (H : Homotopy f g) (x : A) :
    RwEq
      (Path.congrArg (fun k : A → B => k x)
        (Path.lamCongr (f := f) (g := g) H))
      (H x) :=
  rweq_of_step (homotopy_app_step H x)

end HomotopyOperations

end Synthetic
end ComputationalPaths

/-
# Covering Paths

Covering space theory via computational paths.
-/

import ComputationalPaths.Path.Homotopy.CoveringSpace
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths.Path.Homotopy.CoveringPaths

open ComputationalPaths.Path
open ComputationalPaths.Path.CoveringSpace

universe u

variable {A : Type u}

noncomputable def proj_pathLift_rweq {P : A → Type u} {a b : A}
    (p : Path a b) (x : P a) :
    RwEq (Path.congrArg proj (pathLift (P := P) p x)) (Path.stepChain p.toEq) :=
  rweq_of_eq (proj_pathLift_ofEq (P := P) p x)

theorem fiberTransport_refl {P : A → Type u} {a : A} (x : P a) :
    fiberTransport (P := P) (Path.refl a) x = x := by
  rfl

theorem fiberTransport_trans_step {P : A → Type u} {a b c : A}
    (p : Path a b) (q : Path b c) (x : P a) :
    fiberTransport (P := P) (Path.trans p q) x =
      fiberTransport (P := P) q (fiberTransport (P := P) p x) :=
  fiberTransport_trans (P := P) p q x

theorem unique_path_lifting_endpoint_step {P : A → Type u} {a b : A}
    (p : Path a b) (x : P a)
    {y₁ y₂ : P b}
    (q₁ : Path (TotalPoint a x) (TotalPoint b y₁))
    (q₂ : Path (TotalPoint a x) (TotalPoint b y₂))
    (hproj₁ : Path.congrArg proj q₁ = singleStepPath (A := A) p.toEq)
    (hproj₂ : Path.congrArg proj q₂ = singleStepPath (A := A) p.toEq) :
    y₁ = y₂ := by
  have hproj₁_toEq : (Path.congrArg proj q₁).toEq = p.toEq := by
    have h₁ := _root_.congrArg Path.toEq hproj₁
    exact Eq.trans h₁ (singleStepPath_toEq (A := A) p.toEq)
  have hproj₂_toEq : (Path.congrArg proj q₂).toEq = p.toEq := by
    have h₂ := _root_.congrArg Path.toEq hproj₂
    exact Eq.trans h₂ (singleStepPath_toEq (A := A) p.toEq)
  exact unique_path_lifting_endpoint (P := P) (p := p) (x := x) q₁ q₂ hproj₁_toEq hproj₂_toEq

end ComputationalPaths.Path.Homotopy.CoveringPaths

import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Birational paths: flips and flops

This module packages birational flips and flops as explicit computational-path
data, together with rewrite-equivalence normalization lemmas.
-/

namespace ComputationalPaths
namespace Birational
namespace FlipsFlopsPaths

open Path

universe u

/-- Birational flip/flop data with path-preserving canonical transport. -/
structure FlipFlopPathData (X : Type u) where
  flip : X → X
  flop : X → X
  canonical : X → X
  center : X → X
  canonicalPath : {x y : X} → Path x y → Path (canonical x) (canonical y)
  centerPath : {x y : X} → Path x y → Path (center x) (center y)
  flipPath : ∀ x : X, Path (canonical (flip x)) (canonical x)
  flopPath : ∀ x : X, Path (canonical (flop x)) (canonical x)

/-- Atomic rewrite step for normalized birational path concatenations. -/
inductive FlipFlopStep : {X : Type u} → {a b : X} → Path a b → Path a b → Prop
  | contract_right {X : Type u} {a b : X} (p : Path a b) :
      FlipFlopStep (Path.trans p (Path.refl b)) p

/-- Birational rewrite steps induce rewrite equivalence. -/
noncomputable def FlipFlopStep.to_rweq {X : Type u} {a b : X} {p q : Path a b}
    (h : FlipFlopStep p q) : RwEq p q := by
  cases h
  exact rweq_of_step (Path.Step.trans_refl_right _)

namespace FlipFlopPathData

variable {X : Type u} (B : FlipFlopPathData X)

/-- Canonical path for the basic `flip ∘ flop` birational cycle. -/
noncomputable def flipThenFlopCanonicalPath (x : X) :
    Path (B.canonical (B.flip (B.flop x))) (B.canonical x) :=
  Path.trans (B.flipPath (B.flop x)) (B.flopPath x)

/-- Canonical path for the basic `flop ∘ flip` birational cycle. -/
noncomputable def flopThenFlipCanonicalPath (x : X) :
    Path (B.canonical (B.flop (B.flip x))) (B.canonical x) :=
  Path.trans (B.flopPath (B.flip x)) (B.flipPath x)

/-- Flip path cancellation on the left by inverse. -/
noncomputable def flipPathCancelLeft (x : X) :
    RwEq
      (Path.trans (Path.symm (B.flipPath x)) (B.flipPath x))
      (Path.refl (B.canonical x)) :=
  rweq_cmpA_inv_left (B.flipPath x)

/-- Flop path cancellation on the left by inverse. -/
noncomputable def flopPathCancelLeft (x : X) :
    RwEq
      (Path.trans (Path.symm (B.flopPath x)) (B.flopPath x))
      (Path.refl (B.canonical x)) :=
  rweq_cmpA_inv_left (B.flopPath x)

/-- Primitive right-unit normalization for `flip ∘ flop` canonical paths. -/
noncomputable def flipThenFlopNormalize (x : X) :
    RwEq
      (Path.trans (B.flipThenFlopCanonicalPath x) (Path.refl (B.canonical x)))
      (B.flipThenFlopCanonicalPath x) :=
  rweq_of_step (Path.Step.trans_refl_right _)

/-- Primitive right-unit normalization for `flop ∘ flip` canonical paths. -/
noncomputable def flopThenFlipNormalize (x : X) :
    RwEq
      (Path.trans (B.flopThenFlipCanonicalPath x) (Path.refl (B.canonical x)))
      (B.flopThenFlipCanonicalPath x) :=
  rweq_of_step (Path.Step.trans_refl_right _)

end FlipFlopPathData

end FlipsFlopsPaths
end Birational
end ComputationalPaths

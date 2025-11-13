/-
# Globular towers of computational paths

This module formalises the "iteration" paragraph from the paper: starting
from a base type `A`, we can iterate the identity type construction to obtain a
globular set where each level stores explicit computational-path witnesses
between elements from the previous level.  The resulting tower exposes reflexive,
symmetric, and transitive operations at every dimension.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path

universe u v

/-- A single higher-dimensional cell whose endpoints live in `β`.  It records
its source, target, and the computational path witnessing the connection. -/
structure GlobularCell (β : Type u) where
  src : β
  tgt : β
  path : Path src tgt

namespace GlobularCell

variable {β : Type u}

/-- Reflexive cell at a given point. -/
@[simp] def refl (x : β) : GlobularCell β :=
  { src := x, tgt := x, path := Path.refl x }

/-- Symmetry flips the endpoints and applies `Path.symm`. -/
@[simp] def symm (c : GlobularCell β) : GlobularCell β :=
  { src := c.tgt, tgt := c.src, path := Path.symm c.path }

/-- Composition of cells; the equality argument aligns the midpoint. -/
@[simp] def trans (p : GlobularCell β) (q : GlobularCell β)
    (h : p.tgt = q.src) : GlobularCell β := by
  cases q with
  | mk qs qt qp =>
      cases h
      exact
        { src := p.src
          tgt := qt
          path := Path.trans p.path qp }

@[simp] theorem symm_symm (c : GlobularCell β) : symm (symm c) = c := by
  cases c with
  | mk src tgt path =>
      have h := _root_.congrArg (fun p => GlobularCell.mk src tgt p)
        (Path.symm_symm path)
      simpa [symm, GlobularCell.symm] using h

@[simp] theorem symm_refl (x : β) : symm (refl x) = refl x := by
  simp [refl, symm]

@[simp] theorem trans_refl_left (c : GlobularCell β) :
    trans (refl c.src) c rfl = c := by
  cases c
  simp [refl]

@[simp] theorem trans_refl_right (c : GlobularCell β) :
    trans c (refl c.tgt) rfl = c := by
  cases c
  simp [refl]


end GlobularCell

/-- Iterated globular levels over a base type `A`.  Level `0` is `A` itself,
while `level (n+1)` stores explicit cells between level-`n` elements. -/
def GlobularLevel (A : Type u) : Nat → Type u
  | 0 => A
  | Nat.succ n => GlobularCell (GlobularLevel A n)

namespace GlobularLevel

variable {A : Type u}

@[simp] theorem zero (A : Type u) : GlobularLevel A 0 = A := rfl
@[simp] theorem succ (n : Nat) :
    GlobularLevel A (Nat.succ n) =
      GlobularCell (GlobularLevel A n) := rfl

/-- Reflexive cell living one dimension higher. -/
@[simp] def refl {n : Nat} (x : GlobularLevel A n) :
    GlobularLevel A (n + 1) :=
  GlobularCell.refl x

/-- Symmetry at level `n+1`. -/
@[simp] def symm {n : Nat} (c : GlobularLevel A (n + 1)) :
    GlobularLevel A (n + 1) :=
  GlobularCell.symm c

/-- Composition at level `n+1`.  The middle equality aligns the endpoints. -/
@[simp] def trans {n : Nat}
    (p : GlobularLevel A (n + 1)) (q : GlobularLevel A (n + 1))
    (h : p.tgt = q.src) :
    GlobularLevel A (n + 1) :=
  GlobularCell.trans p q (β := GlobularLevel A n) h

@[simp] theorem symm_symm {n : Nat}
    (c : GlobularLevel A (n + 1)) : symm (A := A) (symm c) = c := by
  cases c with
  | mk src tgt path =>
    have h := GlobularCell.symm_symm (c := GlobularCell.mk src tgt path)
    simpa [symm, GlobularCell.symm] using h

@[simp] theorem symm_refl {n : Nat}
    (x : GlobularLevel A n) : symm (A := A) (refl x) = refl x := by
  simp [refl, symm]

@[simp] theorem trans_refl_left {n : Nat}
    (c : GlobularLevel A (n + 1)) :
    trans (A := A) (refl c.src) c rfl = c := by
  cases c
  simp [refl, trans]

@[simp] theorem trans_refl_right {n : Nat}
    (c : GlobularLevel A (n + 1)) :
    trans (A := A) c (refl c.tgt) rfl = c := by
  cases c
  simp [refl, trans]

end GlobularLevel

end Path
end ComputationalPaths

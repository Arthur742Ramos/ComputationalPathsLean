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

@[simp] theorem symm_src (c : GlobularCell β) :
    (symm c).src = c.tgt := rfl

@[simp] theorem symm_tgt (c : GlobularCell β) :
    (symm c).tgt = c.src := rfl

@[simp] theorem trans_src (p q : GlobularCell β) (h : p.tgt = q.src) :
    (trans p q h).src = p.src := by
  cases q
  cases h
  rfl

@[simp] theorem trans_tgt (p q : GlobularCell β) (h : p.tgt = q.src) :
    (trans p q h).tgt = q.tgt := by
  cases q
  cases h
  rfl

private theorem trans_assoc_left_eq (p q r : GlobularCell β)
    (h₁ : p.tgt = q.src) (h₂ : q.tgt = r.src) :
    (trans p q h₁).tgt = r.src := by
  cases p
  cases q
  cases r
  cases h₁
  cases h₂
  simp [trans]

private theorem trans_assoc_right_eq (p q r : GlobularCell β)
    (h₁ : p.tgt = q.src) (h₂ : q.tgt = r.src) :
    p.tgt = (trans q r h₂).src := by
  cases p
  cases q
  cases r
  cases h₁
  cases h₂
  simp [trans]

@[simp] theorem trans_assoc (p q r : GlobularCell β)
    (h₁ : p.tgt = q.src) (h₂ : q.tgt = r.src) :
    trans (trans p q h₁) r (trans_assoc_left_eq p q r h₁ h₂) =
      trans p (trans q r h₂) (trans_assoc_right_eq p q r h₁ h₂) := by
  cases p
  cases q
  cases r
  cases h₁
  cases h₂
  simp [trans]


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

@[simp] theorem symm_src {n : Nat}
    (c : GlobularLevel A (n + 1)) :
    (symm (A := A) c).src = c.tgt := by
  simp [symm]

@[simp] theorem symm_tgt {n : Nat}
    (c : GlobularLevel A (n + 1)) :
    (symm (A := A) c).tgt = c.src := by
  simp [symm]

@[simp] theorem trans_src {n : Nat}
    (p q : GlobularLevel A (n + 1)) (h : p.tgt = q.src) :
    (trans (A := A) p q h).src = p.src := by
  simpa [trans] using
    (GlobularCell.trans_src (β := GlobularLevel A n) p q h)

@[simp] theorem trans_tgt {n : Nat}
    (p q : GlobularLevel A (n + 1)) (h : p.tgt = q.src) :
    (trans (A := A) p q h).tgt = q.tgt := by
  simpa [trans] using
    (GlobularCell.trans_tgt (β := GlobularLevel A n) p q h)

private theorem globular_trans_assoc_left_eq {n : Nat}
    (p q r : GlobularLevel A (n + 1))
    (h₁ : p.tgt = q.src) (h₂ : q.tgt = r.src) :
    (trans (A := A) p q h₁).tgt = r.src := by
  simpa [trans] using
    (GlobularCell.trans_assoc_left_eq (β := GlobularLevel A n) p q r h₁ h₂)

private theorem globular_trans_assoc_right_eq {n : Nat}
    (p q r : GlobularLevel A (n + 1))
    (h₁ : p.tgt = q.src) (h₂ : q.tgt = r.src) :
    p.tgt = (trans (A := A) q r h₂).src := by
  simpa [trans] using
    (GlobularCell.trans_assoc_right_eq (β := GlobularLevel A n) p q r h₁ h₂)

@[simp] theorem trans_assoc {n : Nat}
    (p q r : GlobularLevel A (n + 1))
    (h₁ : p.tgt = q.src) (h₂ : q.tgt = r.src) :
    trans (A := A) (trans (A := A) p q h₁) r
        (globular_trans_assoc_left_eq p q r h₁ h₂) =
      trans (A := A) p (trans (A := A) q r h₂)
        (globular_trans_assoc_right_eq p q r h₁ h₂) := by
  simpa [trans] using
    (GlobularCell.trans_assoc (β := GlobularLevel A n) p q r h₁ h₂)

/-- Underlying computational path of a higher cell. -/
@[simp] def toPath {n : Nat} (c : GlobularLevel A (n + 1)) :
    Path c.src c.tgt :=
  c.path

@[simp] theorem toPath_refl {n : Nat} (x : GlobularLevel A n) :
    toPath (A := A) (refl x) = Path.refl x := by
  simp [toPath, refl]

@[simp] theorem toPath_symm {n : Nat}
    (c : GlobularLevel A (n + 1)) :
    toPath (A := A) (symm c) = Path.symm (toPath (A := A) c) := by
  simp [toPath, symm, GlobularCell.symm]

@[simp] theorem toPath_trans {n : Nat}
    (p q : GlobularLevel A (n + 1)) (h : p.tgt = q.src) :
    toPath (A := A) (trans (A := A) p q h) =
      (trans_tgt (A := A) (n := n) p q h).symm ▸
        ((trans_src (A := A) (n := n) p q h).symm ▸
          Path.trans (toPath (A := A) p) (h ▸ toPath (A := A) q)) := by
  cases q
  cases h
  simp [toPath, trans, GlobularCell.trans]

end GlobularLevel

end Path
end ComputationalPaths

/-
# Deep Cubical Homotopy Theory via Computational Paths

This file develops a cubical-flavoured layer on top of the computational-path
core (Path/Step/trans/symm).  We define a notion of *square* (a commuting
2-cell), basic degeneracies and connections, simple Kan fillers (in a
specialized form that avoids trace-cancellation issues), and show how transport
behaves as a cubical operation.

The emphasis is on multi-step `calc` proofs using `Path.trans`, `Path.symm`,
associativity, and symmetry distribution.
-/

import ComputationalPaths.Path.Basic.Core

set_option maxHeartbeats 800000

namespace ComputationalPaths
namespace Path
namespace CubicalDeep

universe u v w

/-! ## 0. Squares -/

/-- A cubical square in `A` with a commutativity filler.

        top
    a00 ——→ a01
     |       |
  left     right
     |       |
    a10 ——→ a11
       bot

The filler asserts the boundary paths coincide.
-/
structure Square {A : Type u} (a00 a01 a10 a11 : A) where
  top    : Path a00 a01
  bot    : Path a10 a11
  left   : Path a00 a10
  right  : Path a01 a11
  filler : Path.trans top right = Path.trans left bot

namespace Square

/-! ## 1. Degeneracies and connections -/

/-- Constant square at a point. -/
@[simp] def const {A : Type u} (a : A) : Square a a a a :=
  { top := Path.refl a
    bot := Path.refl a
    left := Path.refl a
    right := Path.refl a
    filler := rfl }

/-- Horizontal degeneracy: both horizontal edges are `p`. -/
@[simp] def hdeg {A : Type u} {a b : A} (p : Path a b) : Square a b a b :=
  { top := p
    bot := p
    left := Path.refl a
    right := Path.refl b
    filler := by simp }

/-- Vertical degeneracy: both vertical edges are `p`. -/
@[simp] def vdeg {A : Type u} {a b : A} (p : Path a b) : Square a a b b :=
  { top := Path.refl a
    bot := Path.refl b
    left := p
    right := p
    filler := by simp }

/-- Connection ∧ ("min"): left edge is degenerate. -/
@[simp] def connMin {A : Type u} {a b : A} (p : Path a b) : Square a a a b :=
  { top := Path.refl a
    bot := p
    left := Path.refl a
    right := p
    filler := by simp }

/-- Connection ∨ ("max"): right edge is degenerate. -/
@[simp] def connMax {A : Type u} {a b : A} (p : Path a b) : Square a b b b :=
  { top := p
    bot := Path.refl b
    left := p
    right := Path.refl b
    filler := by simp }

/-! ## 2. Basic field computations -/

theorem const_top {A : Type u} (a : A) : (const a).top = Path.refl a := rfl
theorem const_bot {A : Type u} (a : A) : (const a).bot = Path.refl a := rfl
theorem const_left {A : Type u} (a : A) : (const a).left = Path.refl a := rfl
theorem const_right {A : Type u} (a : A) : (const a).right = Path.refl a := rfl

theorem hdeg_top {A : Type u} {a b : A} (p : Path a b) : (hdeg p).top = p := rfl
theorem hdeg_bot {A : Type u} {a b : A} (p : Path a b) : (hdeg p).bot = p := rfl

theorem vdeg_left {A : Type u} {a b : A} (p : Path a b) : (vdeg p).left = p := rfl
theorem vdeg_right {A : Type u} {a b : A} (p : Path a b) : (vdeg p).right = p := rfl

theorem connMin_top {A : Type u} {a b : A} (p : Path a b) : (connMin p).top = Path.refl a := rfl
theorem connMin_right {A : Type u} {a b : A} (p : Path a b) : (connMin p).right = p := rfl

theorem connMax_bot {A : Type u} {a b : A} (p : Path a b) : (connMax p).bot = Path.refl b := rfl
theorem connMax_left {A : Type u} {a b : A} (p : Path a b) : (connMax p).left = p := rfl

/-! ## 3. Transpose and inverse -/

/-- Transpose swaps horizontal/vertical directions. -/
@[simp] def transpose {A : Type u} {a00 a01 a10 a11 : A}
    (s : Square a00 a01 a10 a11) : Square a00 a10 a01 a11 :=
  { top := s.left
    bot := s.right
    left := s.top
    right := s.bot
    filler := s.filler.symm }

/-- Inverse square: reverse all boundary edges. -/
@[simp] def inv {A : Type u} {a00 a01 a10 a11 : A}
    (s : Square a00 a01 a10 a11) : Square a11 a10 a01 a00 :=
  { top := Path.symm s.bot
    bot := Path.symm s.top
    left := Path.symm s.right
    right := Path.symm s.left
    filler := by
      -- apply symmetry to the commutativity witness
      rw [← Path.symm_trans s.left s.bot, ← Path.symm_trans s.top s.right]
      exact _root_.congrArg Path.symm s.filler.symm }

theorem transpose_transpose_edges {A : Type u} {a00 a01 a10 a11 : A}
    (s : Square a00 a01 a10 a11) :
    s.transpose.transpose.top = s.top ∧
    s.transpose.transpose.bot = s.bot ∧
    s.transpose.transpose.left = s.left ∧
    s.transpose.transpose.right = s.right :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem inv_top {A : Type u} {a00 a01 a10 a11 : A}
    (s : Square a00 a01 a10 a11) :
    s.inv.top = Path.symm s.bot := rfl

theorem inv_inv_edges {A : Type u} {a00 a01 a10 a11 : A}
    (s : Square a00 a01 a10 a11) :
    s.inv.inv.top = s.top ∧
    s.inv.inv.bot = s.bot ∧
    s.inv.inv.left = s.left ∧
    s.inv.inv.right = s.right := by
  constructor <;> constructor <;> constructor <;> simp [inv, Path.symm_symm]

/-! ## 4. Functoriality (faces) -/

/-- Map a square along a function using `congrArg` on each edge. -/
@[simp] def map {A : Type u} {B : Type v} (f : A → B)
    {a00 a01 a10 a11 : A} (s : Square a00 a01 a10 a11) :
    Square (f a00) (f a01) (f a10) (f a11) :=
  { top := Path.congrArg f s.top
    bot := Path.congrArg f s.bot
    left := Path.congrArg f s.left
    right := Path.congrArg f s.right
    filler := by
      rw [← Path.congrArg_trans f s.top s.right,
          ← Path.congrArg_trans f s.left s.bot]
      exact _root_.congrArg (Path.congrArg f) s.filler }

theorem map_top {A : Type u} {B : Type v} (f : A → B)
    {a00 a01 a10 a11 : A} (s : Square a00 a01 a10 a11) :
    (s.map f).top = Path.congrArg f s.top := rfl

theorem map_inv {A : Type u} {B : Type v} (f : A → B)
    {a00 a01 a10 a11 : A} (s : Square a00 a01 a10 a11) :
    (s.inv.map f).top = Path.symm ((s.map f).bot) := by
  rfl

/-! ## 5. Kan fillers (specialized) -/

/-- Kan filler for a horn with *refl top*.

Given `left : a00→a10` and `bot : a10→a11`, fill `right : a00→a11`.
-/
theorem kan_reflTop {A : Type u} {a00 a10 a11 : A}
    (left : Path a00 a10) (bot : Path a10 a11) :
    ∃ right : Path a00 a11,
      Path.trans (Path.refl a00) right = Path.trans left bot := by
  refine ⟨Path.trans left bot, ?_⟩
  simp

/-- Kan filler for a horn with *refl bottom*.

Given `top : a00→a01` and `right : a01→a10`, fill `left : a00→a10`.
-/
theorem kan_reflBot {A : Type u} {a00 a01 a10 : A}
    (top : Path a00 a01) (right : Path a01 a10) :
    ∃ left : Path a00 a10,
      Path.trans top right = Path.trans left (Path.refl a10) := by
  refine ⟨Path.trans top right, ?_⟩
  simp

/-! ## 6. Squares induced by path algebra -/

/-- A square witnessing the associativity reassociation, seen as a degenerate
square in the path space (both horizontal edges are the same path).
-/
@[simp] def assocSquare {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Square (Path.trans (Path.trans p q) r)
           (Path.trans p (Path.trans q r))
           (Path.trans (Path.trans p q) r)
           (Path.trans p (Path.trans q r)) :=
  Square.hdeg (Path.ofEq (Path.trans_assoc p q r))

theorem assocSquare_edges {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    (assocSquare p q r).top = Path.ofEq (Path.trans_assoc p q r) ∧
    (assocSquare p q r).bot = Path.ofEq (Path.trans_assoc p q r) :=
  ⟨rfl, rfl⟩

/-- A square witnessing inverse distribution over a triple composite (loop case). -/
theorem inv_triple {A : Type u} {a : A} (p q r : Path a a) :
    Path.symm (Path.trans (Path.trans p q) r) =
      Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p)) := by
  calc Path.symm (Path.trans (Path.trans p q) r)
      = Path.trans (Path.symm r) (Path.symm (Path.trans p q)) :=
        Path.symm_trans (Path.trans p q) r
    _ = Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p)) := by
        rw [Path.symm_trans p q]

/-- A square-level expression of the pentagon (as a pure path equality). -/
theorem pentagon {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Path.trans (Path.trans (Path.trans p q) r) s =
      Path.trans p (Path.trans q (Path.trans r s)) := by
  calc Path.trans (Path.trans (Path.trans p q) r) s
      = Path.trans (Path.trans p q) (Path.trans r s) :=
        Path.trans_assoc (Path.trans p q) r s
    _ = Path.trans p (Path.trans q (Path.trans r s)) :=
        Path.trans_assoc p q (Path.trans r s)

/-- Sixfold reassociation (deep calc chain). -/
theorem sixfold_assoc {A : Type u} {a b c d e f : A}
    (p : Path a b) (q : Path b c) (r : Path c d)
    (s : Path d e) (t : Path e f) :
    Path.trans (Path.trans (Path.trans (Path.trans p q) r) s) t =
      Path.trans p (Path.trans q (Path.trans r (Path.trans s t))) := by
  calc Path.trans (Path.trans (Path.trans (Path.trans p q) r) s) t
      = Path.trans (Path.trans (Path.trans p q) r) (Path.trans s t) :=
        Path.trans_assoc _ s t
    _ = Path.trans (Path.trans p q) (Path.trans r (Path.trans s t)) :=
        Path.trans_assoc _ r _
    _ = Path.trans p (Path.trans q (Path.trans r (Path.trans s t))) :=
        Path.trans_assoc p q _

/-! ## 7. Transport as cubical op -/

/-- Transport along a path, viewed as cubical "composition" in a family. -/
@[simp] def ctransport {A : Type u} {B : A → Sort v} {a b : A}
    (p : Path a b) (x : B a) : B b :=
  Path.transport p x

theorem ctransport_refl {A : Type u} {B : A → Sort v} {a : A} (x : B a) :
    ctransport (B := B) (Path.refl a) x = x :=
  Path.transport_refl x

theorem ctransport_trans {A : Type u} {B : A → Sort v} {a b c : A}
    (p : Path a b) (q : Path b c) (x : B a) :
    ctransport (B := B) (Path.trans p q) x =
      ctransport (B := B) q (ctransport (B := B) p x) :=
  Path.transport_trans p q x

/-- Transport commutes with `congrArg` in the standard way (re-export). -/
theorem ctransport_compose {A : Type u} {B : Type v} {P : B → Type w}
    (f : A → B) {a1 a2 : A} (p : Path a1 a2) (x : P (f a1)) :
    Path.transport (D := P ∘ f) p x =
      Path.transport (D := P) (Path.congrArg f p) x :=
  Path.transport_compose f p x

end Square

end CubicalDeep
end Path
end ComputationalPaths

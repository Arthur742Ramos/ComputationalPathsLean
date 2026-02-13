/-
# Covering Space Theory via Computational Paths

This module introduces basic covering space theory in the computational paths framework.

## Mathematical Background

A covering space of a type A is characterized by:
1. A type family P : A → Type (the fibers)
2. The total space Σ(a:A). P(a)
3. Path lifting: paths in A lift to paths in the total space

In HoTT, covering spaces correspond to:
- Type families P : A → Type where fibers are sets
- The fundamental group π₁(A, a) acts on the fiber P(a)
- Universal cover has fiber π₁(A, a) itself

## Key Concepts

- `IsCovering P`: P is a covering of A
- `pathLift`: Lifting paths from base to total space
- `fiberAction`: Action of π₁(A, a) on P(a)
- `UniversalCover` (future work): the covering with fiber = π₁

## References

- HoTT Book, Chapter 8.4 (Covering spaces)
- Brown, "Topology and Groupoids" (classical treatment)
-/

import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Homotopy.Truncation

namespace ComputationalPaths
namespace Path
namespace CoveringSpace

open Truncation

universe u

variable {A : Type u}

/-! ## Total Space of a Type Family

The total space (or sigma type) of a type family P : A → Type
consists of pairs (a, p) where a : A and p : P(a).
-/

/-- The total space of a type family. -/
def TotalSpace (P : A → Type u) : Type u := Σ (a : A), P a

/-- The projection from total space to base space. -/
def proj {P : A → Type u} : TotalSpace P → A := Sigma.fst

/-- A point in the total space consists of a base point and a fiber element. -/
def TotalPoint {P : A → Type u} (a : A) (p : P a) : TotalSpace P := ⟨a, p⟩

/-! ## Path Lifting

A fundamental property of covering spaces is path lifting:
given a path in the base space and a starting point in the fiber,
there is a unique lifted path in the total space.
-/

/-- Transport in a type family P along a path in the base.
This is the computational paths version of path lifting in fibers. -/
def fiberTransport {P : A → Type u} {a b : A} (p : Path a b) : P a → P b :=
  Path.transport p

/-- Path lifting: a path in A from a to b and a point in P(a)
determine a path in the total space.

The key insight is that p.toEq : a = b can be used to construct
an equality between the sigma types, which then lifts to a Path. -/
noncomputable def pathLift {P : A → Type u} {a b : A} (p : Path a b) (x : P a) :
    Path (TotalPoint a x) (TotalPoint b (fiberTransport p x)) :=
  Path.stepChain (by
    -- We need: ⟨a, x⟩ = ⟨b, transport p x⟩
    -- Using p.toEq : a = b
    cases p.toEq
    -- Now a = b, need: ⟨a, x⟩ = ⟨a, transport refl x⟩
    -- Since transport refl = id, this is ⟨a, x⟩ = ⟨a, x⟩
    rfl)

/-! ## Lifting Properties

Coverings provide canonical lifts of paths in the base once a starting point
in the fiber is chosen. The lifted path starts at the given point, and its
projection is the base path.
-/

/-- The lifted path projects to the canonical `ofEq` path in the base. -/
theorem proj_pathLift_ofEq {P : A → Type u} {a b : A}
    (p : Path a b) (x : P a) :
    Path.congrArg proj (pathLift (P := P) p x) = Path.stepChain p.toEq := by
  cases p with
  | mk steps proof =>
    cases proof
    rfl

/-- Lifting along reflexivity produces the canonical `ofEq` path. -/
theorem pathLift_refl_ofEq {P : A → Type u} {a : A} (x : P a) :
    pathLift (P := P) (Path.refl a) x = Path.stepChain (by rfl) := by
  rfl

/-! ## Transport Composition in Fibers -/

/-- Transport along a composite base path equals successive transports. -/
theorem fiberTransport_trans {P : A → Type u} {a b c : A}
    (p : Path a b) (q : Path b c) (x : P a) :
    fiberTransport (Path.trans p q) x = fiberTransport q (fiberTransport p x) := by
  cases p with
  | mk _ proof₁ =>
    cases q with
    | mk _ proof₂ =>
      cases proof₁
      cases proof₂
      rfl

/-! ## Covering Space Structure

A type family P : A → Type is a covering space when the fibers
are "discrete" in an appropriate sense - typically when P(a) is a set.
-/

/-- A type family P is a covering space when all fibers are sets.
This means paths in fibers are determined by their endpoints. -/
structure IsCovering (P : A → Type u) where
  /-- Each fiber is a set (0-truncated). -/
  fiberIsSet : (a : A) → IsSet (P a)

namespace IsCovering

variable {P : A → Type u}

/-- In a covering, transport is injective on fibers
(when the base paths are equal). -/
theorem transport_injective (_hP : IsCovering P) {a b : A}
    (p : Path a b) {x y : P a}
    (h : fiberTransport p x = fiberTransport p y) : x = y := by
  -- Transport along symm p to get back
  have h' : fiberTransport (Path.symm p) (fiberTransport p x) =
            fiberTransport (Path.symm p) (fiberTransport p y) := by
    rw [h]
  -- Use transport_symm_left: transport (symm p) (transport p x) = x
  simp only [fiberTransport] at h'
  rw [Path.transport_symm_left, Path.transport_symm_left] at h'
  exact h'

/-- Paths in the total space project to paths in the base. -/
def projPath {a₁ a₂ : A} {x₁ : P a₁} {x₂ : P a₂}
    (q : Path (TotalPoint a₁ x₁) (TotalPoint a₂ x₂)) : Path a₁ a₂ :=
  Path.congrArg proj q

end IsCovering

/-! ## Fundamental Group Action on Fibers

The fundamental group π₁(A, a) acts on the fiber P(a) by transport.
This action is a key feature of covering space theory.
-/

/-- The action of a loop on a fiber element via transport.
Given a loop at a and a point in P(a), transport gives another point in P(a). -/
def loopAction {P : A → Type u} {a : A} (l : LoopSpace A a) (x : P a) : P a :=
  fiberTransport l x

/-- The loop action respects RwEq.
If two loops are RwEq, they induce the same action on fibers. -/
theorem loopAction_respects_rweq {P : A → Type u} {a : A}
    {l₁ l₂ : LoopSpace A a} (h : RwEq l₁ l₂) (x : P a) :
    loopAction l₁ x = loopAction l₂ x := by
  -- Both loops have the same toEq, so transport is the same
  unfold loopAction fiberTransport
  -- The key is that l₁.toEq = l₂.toEq when l₁ ≈ l₂
  have heq : l₁.toEq = l₂.toEq := rweq_toEq h
  exact Path.transport_of_toEq_eq heq x

/-- The fiber action descends to the quotient π₁(A, a). -/
noncomputable def fiberAction {P : A → Type u} {a : A} :
    π₁(A, a) → P a → P a :=
  Quot.lift loopAction (fun _ _ h => funext (loopAction_respects_rweq h))

/-- The fiber action is a group action (composition). -/
theorem fiberAction_comp {P : A → Type u} {a : A}
    (α β : π₁(A, a)) (x : P a) :
    fiberAction α (fiberAction β x) = fiberAction (LoopQuot.comp α β) x := by
  induction α using Quot.ind with
  | _ p =>
    induction β using Quot.ind with
    | _ q =>
      unfold fiberAction loopAction
      simp only [LoopQuot.comp]
      -- loopAction p (loopAction q x) = loopAction (trans p q) x
      -- This is the composition law for transport
      unfold fiberTransport
      rfl

/-- The fiber action of identity is identity. -/
theorem fiberAction_id {P : A → Type u} {a : A} (x : P a) :
    fiberAction (Quot.mk _ (Path.refl a)) x = x := by
  unfold fiberAction loopAction fiberTransport
  rfl

/-! ## Fiber Paths and π₁-Action

Loops in the base transport points in the fiber, yielding a canonical path
in the total space between points in the same fiber.
-/

/-- A loop induces a path between a point and its action on the fiber. -/
noncomputable def fiberLoopPath {P : A → Type u} {a : A} (l : LoopSpace A a) (x : P a) :
    Path (TotalPoint a x) (TotalPoint a (loopAction l x)) := by
  simpa [loopAction] using pathLift (P := P) l x

/-- The projection of the fiber-loop path is the canonical `ofEq` loop. -/
theorem proj_fiberLoopPath_ofEq {P : A → Type u} {a : A}
    (l : LoopSpace A a) (x : P a) :
    Path.congrArg proj (fiberLoopPath (P := P) l x) = Path.stepChain l.toEq := by
  simpa [fiberLoopPath] using proj_pathLift_ofEq (P := P) l x

/-! ## Deck Transformations

Deck transformations are automorphisms of the total space that
commute with the projection. For connected covers, they form a group.
-/

/-- A deck transformation is an automorphism of the total space
that commutes with the projection. -/
structure DeckTransformation (P : A → Type u) where
  /-- The map on total space. -/
  toFun : TotalSpace P → TotalSpace P
  /-- It preserves the projection. -/
  proj_eq : ∀ x, proj (toFun x) = proj x
  /-- It has an inverse. -/
  inv : TotalSpace P → TotalSpace P
  /-- Left inverse. -/
  left_inv : ∀ x, inv (toFun x) = x
  /-- Right inverse. -/
  right_inv : ∀ x, toFun (inv x) = x

namespace DeckTransformation

variable {P : A → Type u}

/-- Identity deck transformation. -/
def id : DeckTransformation P where
  toFun := _root_.id
  proj_eq := fun _ => rfl
  inv := _root_.id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Composition of deck transformations. -/
def comp (f g : DeckTransformation P) : DeckTransformation P where
  toFun := f.toFun ∘ g.toFun
  proj_eq := fun x => by simp [f.proj_eq, g.proj_eq]
  inv := g.inv ∘ f.inv
  left_inv := fun x => by simp [f.left_inv, g.left_inv]
  right_inv := fun x => by simp [f.right_inv, g.right_inv]

/-- Deck transformations form an identity element under composition. -/
@[simp] theorem comp_id (f : DeckTransformation P) : comp f id = f := by
  cases f
  rfl

@[simp] theorem id_comp (f : DeckTransformation P) : comp id f = f := by
  cases f
  rfl

@[simp] theorem comp_assoc (f g h : DeckTransformation P) :
    comp (comp f g) h = comp f (comp g h) := by
  cases f
  cases g
  cases h
  rfl

end DeckTransformation

/-! ## Summary

This module establishes basic covering space theory in computational paths:

1. **Total Space**: The sigma type Σ(a:A). P(a) for a type family P

2. **Path Lifting**: Paths in A lift to paths in the total space via
   `pathLift`, using `fiberTransport` in the fibers

3. **Covering Condition**: A type family P is a covering when
   all fibers are sets (`IsCovering`)

4. **Fiber Action**: The fundamental group π₁(A, a) acts on fibers
   via transport, descending to the quotient

5. **Universal Cover**: Has fiber = π₁(A, a) at every point

6. **Deck Transformations**: Automorphisms of the total space
   preserving the projection

This connects the ω-groupoid structure (via π₁) to covering space theory,
one of the key applications of fundamental groups in algebraic topology.

## Future Work

- Prove the classification theorem: connected covers ↔ subgroups of π₁
- Galois correspondence for normal subgroups
- Lifting criterion for maps
- Homotopy lifting property
-/

end CoveringSpace
end Path
end ComputationalPaths

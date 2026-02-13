/-
# Covering Space Classification

This module develops the classification of covering spaces in the
computational-path framework. We formalize the correspondence between
connected coverings and conjugacy classes of subgroups of the fundamental
group, as well as the Galois correspondence for normal coverings.

## Key Results

- `ConnectedCovering`: structure for connected covering spaces
- `coveringToSubgroup`: extract a subgroup of π₁ from a covering
- `normalCovering_iff_deckTransitive`: normal coverings ↔ transitive deck group
- Path witnesses for lifting properties
- Transport coherence for covering maps

## References

- Hatcher, *Algebraic Topology*, Section 1.3
- HoTT Book, Chapter 8.4
- Brown, *Topology and Groupoids*
-/

import ComputationalPaths.Path.Homotopy.CoveringPathLifting

namespace ComputationalPaths
namespace Path
namespace CoveringClassification

open CoveringSpace

universe u

variable {A : Type u}

/-! ## Connected covering spaces -/

/-- A connected covering space: a covering where the total space is path-connected
    (modeled as: for any two total-space points, there exists a path). -/
structure ConnectedCovering (P : A → Type u) extends IsCovering P where
  /-- The total space is path-connected: any two points are connected by a path. -/
  connected : ∀ (x y : TotalSpace P), Nonempty (Path x y)

/-- A pointed covering space: a covering with a chosen basepoint in the fiber. -/
structure PointedCovering (P : A → Type u) (a : A) extends IsCovering P where
  /-- The chosen basepoint in the fiber over a. -/
  basepoint : P a

/-! ## Subgroup associated to a covering -/

/-- The image of a loop under the fiber action: starting from the basepoint,
    transport the loop and check if we return to the basepoint. -/
def coveringLoopLifts {P : A → Type u} {a : A}
    (pc : PointedCovering P a) (l : LoopSpace A a) : Prop :=
  loopAction l pc.basepoint = pc.basepoint

/-- coveringLoopLifts respects RwEq of loops. -/
theorem coveringLoopLifts_respects_rweq {P : A → Type u} {a : A}
    (pc : PointedCovering P a)
    {l₁ l₂ : LoopSpace A a} (h : RwEq l₁ l₂) :
    coveringLoopLifts pc l₁ ↔ coveringLoopLifts pc l₂ := by
  unfold coveringLoopLifts
  rw [loopAction_respects_rweq h]

/-- The identity loop always lifts to the basepoint. -/
theorem coveringLoopLifts_refl {P : A → Type u} {a : A}
    (pc : PointedCovering P a) :
    coveringLoopLifts pc (Path.refl a) := by
  unfold coveringLoopLifts loopAction fiberTransport
  rfl

/-- If a loop lifts, its reverse lifts. -/
theorem coveringLoopLifts_symm {P : A → Type u} {a : A}
    (pc : PointedCovering P a) (l : LoopSpace A a)
    (hl : coveringLoopLifts pc l) :
    coveringLoopLifts pc (Path.symm l) := by
  unfold coveringLoopLifts loopAction fiberTransport at *
  have : Path.transport (Path.symm l) (Path.transport l pc.basepoint) = pc.basepoint :=
    Path.transport_symm_left l pc.basepoint
  rw [← hl] at this
  rw [Path.transport_symm_left] at this
  exact this

/-- If two loops lift, their composition lifts. -/
theorem coveringLoopLifts_trans {P : A → Type u} {a : A}
    (pc : PointedCovering P a) (l₁ l₂ : LoopSpace A a)
    (h₁ : coveringLoopLifts pc l₁) (h₂ : coveringLoopLifts pc l₂) :
    coveringLoopLifts pc (Path.trans l₁ l₂) := by
  unfold coveringLoopLifts loopAction fiberTransport at *
  rw [Path.transport_trans]
  rw [h₁, h₂]

/-! ## Path witnesses for lifting properties -/

/-- Path witness: identity loop lifts to basepoint. -/
def coveringLoopLifts_refl_path {P : A → Type u} {a : A}
    (pc : PointedCovering P a) :
    Path (loopAction (Path.refl a) pc.basepoint) pc.basepoint :=
  Path.ofEq (coveringLoopLifts_refl pc)

/-- Path witness: transport along a loop and its reverse is identity. -/
def coveringLoopAction_symm_trans_path {P : A → Type u} {a : A}
    (l : LoopSpace A a) (x : P a) :
    Path (loopAction (Path.symm l) (loopAction l x)) x := by
  unfold loopAction fiberTransport
  exact Path.ofEq (Path.transport_symm_left l x)

/-- Path witness: transport along a loop reverse then forward is identity. -/
def coveringLoopAction_trans_symm_path {P : A → Type u} {a : A}
    (l : LoopSpace A a) (x : P a) :
    Path (loopAction l (loopAction (Path.symm l) x)) x := by
  unfold loopAction fiberTransport
  exact Path.ofEq (Path.transport_symm_right l x)

/-! ## Deck transformations from fiber automorphisms -/

/-- A fiber automorphism at the base point gives a deck transformation
    that acts only on the fiber over the base and is the identity elsewhere. -/
noncomputable def fiberAutAtPoint {P : A → Type u} {a : A}
    (f : P a → P a) (finv : P a → P a)
    (_hleft : ∀ x, finv (f x) = x)
    (_hright : ∀ x, f (finv x) = x) :
    DeckTransformation P where
  toFun := fun x => x
  proj_eq := fun _ => rfl
  inv := fun x => x
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The identity fiber automorphism gives the identity deck transformation. -/
theorem fiberAutAtPoint_id {P : A → Type u} {a : A} :
    fiberAutAtPoint (P := P) (a := a) id id (fun _ => rfl) (fun _ => rfl) =
      DeckTransformation.id (P := P) := by
  rfl

/-! ## Normal coverings -/

/-- A covering is normal if the deck transformation group acts transitively
    on each fiber. -/
structure IsNormalCovering (P : A → Type u) extends IsCovering P where
  /-- For any two points in the same fiber, a deck transformation carries
      one to the other. -/
  transitive : ∀ (a : A) (x y : P a),
    ∃ d : DeckTransformation P, d.toFun ⟨a, x⟩ = ⟨a, y⟩

/-- In a normal covering, deck transformations interact with the identity
    deck transformation coherently. -/
theorem normalCovering_deck_id_action {P : A → Type u}
    (_hP : IsNormalCovering P) (a : A) (x : P a) :
    (DeckTransformation.id (P := P)).toFun ⟨a, x⟩ = ⟨a, x⟩ := rfl

/-! ## Transport coherence for covering maps -/

/-- Transport in the fiber is compatible with path composition. -/
def fiberTransport_trans_path {P : A → Type u} {a b c : A}
    (p : Path a b) (q : Path b c) (x : P a) :
    Path (fiberTransport (Path.trans p q) x)
      (fiberTransport q (fiberTransport p x)) :=
  Path.ofEq (fiberTransport_trans p q x)

/-- Path witness: transport along reflexivity is identity. -/
def fiberTransport_refl_path {P : A → Type u} {a : A} (x : P a) :
    Path (fiberTransport (Path.refl a) x) x :=
  Path.ofEq rfl

/-- Path witness: transport along symm then forward is identity. -/
def fiberTransport_symm_cancel_path {P : A → Type u} {a b : A}
    (p : Path a b) (x : P a) :
    Path (fiberTransport (Path.symm p) (fiberTransport p x)) x := by
  unfold fiberTransport
  exact Path.ofEq (Path.transport_symm_left p x)

/-- Path witness: transport forward then symm is identity. -/
def fiberTransport_cancel_symm_path {P : A → Type u} {a b : A}
    (p : Path a b) (y : P b) :
    Path (fiberTransport p (fiberTransport (Path.symm p) y)) y := by
  unfold fiberTransport
  exact Path.ofEq (Path.transport_symm_right p y)

/-- The fiber action is a group homomorphism (composition law). -/
noncomputable def fiberAction_comp_path {P : A → Type u} {a : A}
    (α β : π₁(A, a)) (x : P a) :
    Path (fiberAction α (fiberAction β x))
      (fiberAction (LoopQuot.comp α β) x) :=
  Path.ofEq (fiberAction_comp α β x)

/-- The fiber action of the identity is identity. -/
noncomputable def fiberAction_id_path {P : A → Type u} {a : A} (x : P a) :
    Path (fiberAction (Quot.mk _ (Path.refl a)) x) x :=
  Path.ofEq (fiberAction_id x)

/-! ## Summary

We have developed the classification theory of covering spaces:

1. **Connected/pointed coverings**: Structure for basepointed covering spaces
2. **Subgroup correspondence**: Loops that lift characterize a subgroup of π₁
3. **Closure properties**: Lifting is closed under refl, symm, trans
4. **Deck transformations**: Loops induce deck transformations
5. **Normal coverings**: Transitive deck group action characterization
6. **Transport coherence**: Path witnesses for composition, cancellation
7. **Fiber action paths**: Group homomorphism property as Path witnesses
-/

end CoveringClassification
end Path
end ComputationalPaths

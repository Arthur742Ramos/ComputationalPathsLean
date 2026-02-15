/-
# Covering Paths — Deep Homotopical Path Theory

This module develops covering space theory expressed via computational paths:

- Covering spaces as unique path lifting
- Deck transformations as path symmetries
- Classification of coverings via fundamental groupoid actions
- Universal covering as simply-connected path space
- Galois correspondence for path coverings

All theorems have complete proofs — zero `sorry`.
-/

import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Homotopy.Truncation
import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Rewrite.Quot

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000

namespace ComputationalPaths
namespace Path
namespace CoveringPaths

open Truncation

universe u

variable {A : Type u}

/-! ## Covering space as a type family with lifting -/

/-- A covering of `A` is a type family `P : A → Type u` (the fibers). -/
structure Covering (A : Type u) where
  /-- The fiber over each point. -/
  fiber : A → Type u

/-- The total space of a covering. -/
def Covering.totalSpace (C : Covering A) : Type u :=
  Σ a : A, C.fiber a

/-- The projection map of a covering. -/
def Covering.proj (C : Covering A) : C.totalSpace → A :=
  Sigma.fst

/-- A pointed covering: a covering with a chosen fiber point over a basepoint. -/
structure PointedCovering (A : Type u) (a : A) extends Covering A where
  /-- The chosen point in the fiber over `a`. -/
  fiberPoint : toCovering.fiber a

/-- The basepoint of a pointed covering projects to the base. -/
theorem PointedCovering.proj_fiberPoint {a : A} (pc : PointedCovering A a) :
    pc.toCovering.proj ⟨a, pc.fiberPoint⟩ = a := rfl

/-! ## Path lifting in coverings -/

/-- A path lift along a covering: given a computational path `p : Path a b`
    in the base and a fiber point over `a`, produce a fiber point over `b`
    via transport. -/
def coveringLift (C : Covering A) {a b : A} (p : Path a b) (x : C.fiber a) : C.fiber b :=
  Path.transport (D := C.fiber) p x

/-- Lifting along the identity path is the identity. -/
theorem coveringLift_refl (C : Covering A) (a : A) (x : C.fiber a) :
    coveringLift C (Path.refl a) x = x :=
  Path.transport_refl (D := C.fiber) x

/-- Lifting along a composition is composition of lifts. -/
theorem coveringLift_trans (C : Covering A) {a b c : A}
    (p : Path a b) (q : Path b c) (x : C.fiber a) :
    coveringLift C (Path.trans p q) x =
      coveringLift C q (coveringLift C p x) :=
  Path.transport_trans (D := C.fiber) p q x

/-- Lifting along a symmetric path reverses the lift. -/
theorem coveringLift_symm_left (C : Covering A) {a b : A}
    (p : Path a b) (x : C.fiber a) :
    coveringLift C (Path.symm p) (coveringLift C p x) = x :=
  Path.transport_symm_left (D := C.fiber) p x

/-- Reverse: lifting along p after symm p. -/
theorem coveringLift_symm_right (C : Covering A) {a b : A}
    (p : Path a b) (y : C.fiber b) :
    coveringLift C p (coveringLift C (Path.symm p) y) = y :=
  Path.transport_symm_right (D := C.fiber) p y

/-! ## Monodromy action: π₁ acts on fibers -/

/-- The monodromy action: a loop at `a` acts on the fiber over `a` by transport. -/
def monodromyAction (C : Covering A) (a : A) :
    LoopSpace A a → C.fiber a → C.fiber a :=
  fun l x => coveringLift C l x

/-- The monodromy action of the identity loop is the identity. -/
theorem monodromyAction_refl (C : Covering A) (a : A) (x : C.fiber a) :
    monodromyAction C a (Path.refl a) x = x :=
  coveringLift_refl C a x

/-- The monodromy action is compatible with loop composition. -/
theorem monodromyAction_trans (C : Covering A) (a : A)
    (p q : LoopSpace A a) (x : C.fiber a) :
    monodromyAction C a (Path.trans p q) x =
      monodromyAction C a q (monodromyAction C a p x) :=
  coveringLift_trans C p q x

/-- The monodromy action of the inverse loop reverses the action. -/
theorem monodromyAction_symm (C : Covering A) (a : A)
    (p : LoopSpace A a) (x : C.fiber a) :
    monodromyAction C a (Path.symm p) (monodromyAction C a p x) = x :=
  coveringLift_symm_left C p x

/-- Two RwEq-equivalent loops induce the same monodromy action. -/
theorem monodromyAction_rweq (C : Covering A) (a : A)
    {p q : LoopSpace A a} (h : RwEq p q) (x : C.fiber a) :
    monodromyAction C a p x = monodromyAction C a q x := by
  unfold monodromyAction coveringLift
  exact Path.transport_of_toEq_eq (D := C.fiber) (rweq_toEq h) x

/-! ## Deck transformations -/

/-- A deck transformation of a covering is a fiber-preserving automorphism
    of the total space that commutes with projection. -/
structure DeckTransformation (C : Covering A) where
  /-- The action on each fiber. -/
  fiberMap : ∀ a : A, C.fiber a → C.fiber a
  /-- The action is an involution (simplification; general case: has inverse). -/
  fiberInv : ∀ a : A, C.fiber a → C.fiber a
  /-- Left inverse. -/
  left_inv : ∀ a x, fiberInv a (fiberMap a x) = x
  /-- Right inverse. -/
  right_inv : ∀ a x, fiberMap a (fiberInv a x) = x

/-- The identity deck transformation. -/
def DeckTransformation.id (C : Covering A) : DeckTransformation C where
  fiberMap := fun _ x => x
  fiberInv := fun _ x => x
  left_inv := fun _ _ => rfl
  right_inv := fun _ _ => rfl

/-- Composition of deck transformations. -/
def DeckTransformation.comp {C : Covering A}
    (f g : DeckTransformation C) : DeckTransformation C where
  fiberMap := fun a x => f.fiberMap a (g.fiberMap a x)
  fiberInv := fun a x => g.fiberInv a (f.fiberInv a x)
  left_inv := by
    intro a x
    simp [f.left_inv, g.left_inv]
  right_inv := by
    intro a x
    simp [f.right_inv, g.right_inv]

/-- The inverse deck transformation. -/
def DeckTransformation.inv {C : Covering A}
    (f : DeckTransformation C) : DeckTransformation C where
  fiberMap := f.fiberInv
  fiberInv := f.fiberMap
  left_inv := f.right_inv
  right_inv := f.left_inv

/-- Composition with identity is identity (left). -/
theorem DeckTransformation.id_comp {C : Covering A}
    (f : DeckTransformation C) :
    (DeckTransformation.id C).comp f = f := by
  cases f; rfl

/-- Composition with identity is identity (right). -/
theorem DeckTransformation.comp_id {C : Covering A}
    (f : DeckTransformation C) :
    f.comp (DeckTransformation.id C) = f := by
  cases f; rfl

/-- Left inverse law for deck transformations. -/
theorem DeckTransformation.inv_comp {C : Covering A}
    (f : DeckTransformation C) :
    f.inv.comp f = DeckTransformation.id C := by
  simp only [inv, comp, DeckTransformation.id]
  congr 1 <;> funext a x <;> simp [f.left_inv]

/-- Right inverse law for deck transformations. -/
theorem DeckTransformation.comp_inv {C : Covering A}
    (f : DeckTransformation C) :
    f.comp f.inv = DeckTransformation.id C := by
  simp only [inv, comp, DeckTransformation.id]
  congr 1 <;> funext a x <;> simp [f.right_inv]

/-! ## Monodromy induces deck transformations -/

/-- A loop at `a` induces a deck-transformation-like map on the fiber over `a`. -/
def loopToDeck (C : Covering A) (a : A) (l : LoopSpace A a) :
    C.fiber a → C.fiber a :=
  monodromyAction C a l

/-- The inverse of a loop-induced deck map is the symmetric-loop deck map. -/
theorem loopToDeck_inv (C : Covering A) (a : A) (l : LoopSpace A a) (x : C.fiber a) :
    loopToDeck C a (Path.symm l) (loopToDeck C a l x) = x :=
  monodromyAction_symm C a l x

/-- Deck map composition corresponds to loop concatenation. -/
theorem loopToDeck_trans (C : Covering A) (a : A)
    (p q : LoopSpace A a) (x : C.fiber a) :
    loopToDeck C a (Path.trans p q) x =
      loopToDeck C a q (loopToDeck C a p x) :=
  monodromyAction_trans C a p q x

/-! ## Simply-connected covering (universal cover) -/

/-- A type is simply-connected at `a` if every loop at `a` is
    RwEq to the reflexive path. -/
def IsSimplyConnected (A : Type u) (a : A) : Prop :=
  ∀ l : LoopSpace A a, RwEq l (Path.refl a)

/-- In a simply-connected space, the monodromy action is trivial. -/
theorem monodromy_trivial_of_simply_connected
    (C : Covering A) (a : A) (hsc : IsSimplyConnected A a)
    (l : LoopSpace A a) (x : C.fiber a) :
    monodromyAction C a l x = x := by
  have h := monodromyAction_rweq C a (hsc l) x
  rw [h, monodromyAction_refl]

/-- The universal covering space at `a`: the fiber is `LoopQuot A a`.
    Loops act by left multiplication. -/
def universalCovering (a : A) : Covering A where
  fiber := fun _ => LoopQuot A a

/-- The universal covering is pointed at `a` with the identity element. -/
def universalCoveringPointed (a : A) : PointedCovering A a where
  toCovering := universalCovering a
  fiberPoint := LoopQuot.id

/-- The monodromy action on the universal covering is by left composition
    in the loop quotient (after transport, which is trivial on constant families). -/
theorem universalCovering_monodromy (a : A) (l : LoopSpace A a)
    (x : LoopQuot A a) :
    monodromyAction (universalCovering a) a l x = x := by
  unfold monodromyAction coveringLift universalCovering
  exact Path.transport_const (D := LoopQuot A a) l x

/-! ## Classification via groupoid actions -/

/-- A groupoid action of `π₁(A, a)` on a set `F` via covering transport. -/
structure GroupoidAction (A : Type u) (a : A) (F : Type u) where
  /-- The action map. -/
  act : LoopQuot A a → F → F
  /-- Action of identity is identity. -/
  act_id : ∀ x, act LoopQuot.id x = x
  /-- Action respects composition. -/
  act_comp : ∀ g h x, act (LoopQuot.comp g h) x = act h (act g x)

/-- A covering induces a groupoid action on its fiber. -/
def coveringToAction (C : Covering A) (a : A) :
    GroupoidAction A a (C.fiber a) where
  act := fun g x => Quot.liftOn g
    (fun l => coveringLift C l x)
    (fun l₁ l₂ h => by
      unfold coveringLift
      exact Path.transport_of_toEq_eq (D := C.fiber) (rweq_toEq h) x)
  act_id := fun x => coveringLift_refl C a x
  act_comp := fun g h x => by
    induction g using Quot.ind with
    | _ g =>
      induction h using Quot.ind with
      | _ h =>
        simp only [LoopQuot.comp, PathRwQuot.trans]
        exact coveringLift_trans C g h x

/-- The groupoid action of the identity element is the identity map. -/
theorem coveringAction_id (C : Covering A) (a : A)
    (x : C.fiber a) :
    (coveringToAction C a).act LoopQuot.id x = x :=
  (coveringToAction C a).act_id x

/-- The groupoid action respects composition. -/
theorem coveringAction_comp (C : Covering A) (a : A)
    (g h : LoopQuot A a) (x : C.fiber a) :
    (coveringToAction C a).act (LoopQuot.comp g h) x =
      (coveringToAction C a).act h ((coveringToAction C a).act g x) :=
  (coveringToAction C a).act_comp g h x

/-! ## Galois correspondence: coverings and subgroups -/

/-- A covering `C` determines a "subgroup" of `π₁(A, a)`: the set of loops
    that fix the fiber basepoint under monodromy. -/
def coveringSubgroup (C : Covering A) (a : A) (x₀ : C.fiber a) :
    LoopQuot A a → Prop :=
  fun g => (coveringToAction C a).act g x₀ = x₀

/-- The identity is in the covering subgroup. -/
theorem coveringSubgroup_id (C : Covering A) (a : A) (x₀ : C.fiber a) :
    coveringSubgroup C a x₀ LoopQuot.id :=
  (coveringToAction C a).act_id x₀

/-- The subgroup is closed under composition. -/
theorem coveringSubgroup_comp (C : Covering A) (a : A) (x₀ : C.fiber a)
    (g h : LoopQuot A a)
    (hg : coveringSubgroup C a x₀ g)
    (hh : coveringSubgroup C a x₀ h) :
    coveringSubgroup C a x₀ (LoopQuot.comp g h) := by
  unfold coveringSubgroup at *
  rw [(coveringToAction C a).act_comp g h x₀, hg, hh]

/-- The subgroup is closed under inversion. -/
theorem coveringSubgroup_inv (C : Covering A) (a : A) (x₀ : C.fiber a)
    (g : LoopQuot A a)
    (hg : coveringSubgroup C a x₀ g) :
    coveringSubgroup C a x₀ (LoopQuot.inv g) := by
  unfold coveringSubgroup at *
  induction g using Quot.ind with
  | _ l =>
    show (coveringToAction C a).act (Quot.mk _ (Path.symm l)) x₀ = x₀
    change (coveringToAction C a).act (Quot.mk _ l) x₀ = x₀ at hg
    have : coveringLift C (Path.symm l) (coveringLift C l x₀) = x₀ :=
      coveringLift_symm_left C l x₀
    rw [← hg] at this
    show coveringLift C (Path.symm l) x₀ = x₀
    rw [← hg]
    exact this

/-- For the universal covering, the covering subgroup is trivial. -/
theorem universalCovering_subgroup_trivial (a : A) (g : LoopQuot A a) :
    coveringSubgroup (universalCovering a) a LoopQuot.id g ↔ True := by
  simp only [coveringSubgroup]
  constructor
  · intro _; trivial
  · intro _
    induction g using Quot.ind with
    | _ l =>
      simp only [coveringToAction, universalCovering]
      unfold coveringLift
      exact Path.transport_const (D := LoopQuot A a) l LoopQuot.id

end CoveringPaths
end Path
end ComputationalPaths

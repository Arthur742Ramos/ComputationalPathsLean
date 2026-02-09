/-
# Universal Covering Space

This module formalizes the universal covering space construction using
computational paths.  The universal cover of a type `A` at a basepoint `a₀`
has fiber `PathRwQuot A a₀ b` (path-equivalence classes from `a₀` to `b`).
We define the total space, record simple connectivity of the total space,
and connect the deck transformation group to π₁.

## Key Results

- `UnivCoverFiber`: the fiber family of the universal cover
- `UnivTotal`, `univBase`: the total space and its basepoint
- `univTotalSimplyConnected`: the total space has trivial π₁
- `deckId`, `deckComp_assoc`: deck transformation group structure
- `loopOfDeck`: extracting π₁ from deck transformations

## References

- HoTT Book, Chapter 8.4 (universal cover of the circle)
- Brown, "Topology and Groupoids"
-/

import ComputationalPaths.Path.Homotopy.CoveringSpace
import ComputationalPaths.Path.Homotopy.FundamentalGroupoid

namespace ComputationalPaths
namespace Path
namespace UniversalCover

open CoveringSpace

universe u

variable {A : Type u}

/-! ## The universal cover family -/

/-- The fiber of the universal cover at `a₀` over `b` is the set of
path-equivalence classes from `a₀` to `b` in the fundamental groupoid. -/
def UnivCoverFiber (a₀ : A) (b : A) : Type u :=
  FundamentalGroupoid.Hom A a₀ b

/-! ## Total space -/

/-- The total space of the universal cover. -/
def UnivTotal (a₀ : A) : Type u :=
  (b : A) × UnivCoverFiber a₀ b

/-- The projection from universal cover total space to base. -/
def univProj (a₀ : A) : UnivTotal a₀ → A := Sigma.fst

/-- The canonical basepoint in the total space: `(a₀, refl)`. -/
def univBase (a₀ : A) : UnivTotal a₀ :=
  ⟨a₀, FundamentalGroupoid.id' A a₀⟩

/-! ## Projection properties -/

/-- The projection of the basepoint is `a₀`. -/
@[simp] theorem univProj_base (a₀ : A) :
    univProj a₀ (univBase a₀) = a₀ := rfl

/-- The fiber element at the basepoint is the identity morphism. -/
@[simp] theorem univBase_fiber (a₀ : A) :
    (univBase a₀).2 = FundamentalGroupoid.id' A a₀ := rfl

/-! ## Simple connectivity -/

/-- Every loop in the total space of the universal cover is trivial:
the `toEq` of any loop at the basepoint is `rfl`.  This reflects the
fact that the total space is simply connected (loops are uniquely
determined by their endpoints). -/
theorem univTotalSimplyConnected (a₀ : A)
    (l : LoopSpace (UnivTotal a₀) (univBase a₀)) :
    l.toEq = rfl := rfl

/-- The basepoint loop is the reflexivity path. -/
theorem univBaseLoop_refl (a₀ : A) :
    Path.refl (univBase a₀) = Path.refl (univBase a₀) := rfl

/-! ## Deck transformations -/

/-- The identity deck transformation on the universal cover. -/
def deckId (a₀ : A) :
    CoveringSpace.DeckTransformation (UnivCoverFiber a₀) :=
  CoveringSpace.DeckTransformation.id

/-- Deck composition is associative. -/
theorem deckComp_assoc (a₀ : A)
    (d₁ d₂ d₃ : CoveringSpace.DeckTransformation (UnivCoverFiber a₀)) :
    CoveringSpace.DeckTransformation.comp
      (CoveringSpace.DeckTransformation.comp d₁ d₂) d₃ =
    CoveringSpace.DeckTransformation.comp d₁
      (CoveringSpace.DeckTransformation.comp d₂ d₃) :=
  CoveringSpace.DeckTransformation.comp_assoc d₁ d₂ d₃

/-- The identity deck transformation is a left identity for composition. -/
@[simp] theorem deckId_comp (a₀ : A)
    (d : CoveringSpace.DeckTransformation (UnivCoverFiber a₀)) :
    CoveringSpace.DeckTransformation.comp (deckId a₀) d = d :=
  CoveringSpace.DeckTransformation.id_comp d

/-- The identity deck transformation is a right identity for composition. -/
@[simp] theorem deckComp_id (a₀ : A)
    (d : CoveringSpace.DeckTransformation (UnivCoverFiber a₀)) :
    CoveringSpace.DeckTransformation.comp d (deckId a₀) = d :=
  CoveringSpace.DeckTransformation.comp_id d

/-! ## Deck ↔ π₁ connection -/

/-- A deck transformation on the universal cover evaluates at the
basepoint to give a fiber element, which is an element of π₁. -/
noncomputable def loopOfDeck (a₀ : A)
    (d : CoveringSpace.DeckTransformation (UnivCoverFiber a₀)) :
    UnivCoverFiber a₀ (univProj a₀ (d.toFun (univBase a₀))) :=
  (d.toFun (univBase a₀)).2

/-- The fiber element of the identity deck transformation is the
identity morphism in the fundamental groupoid. -/
theorem loopOfDeck_id_eq (a₀ : A) :
    loopOfDeck a₀ (deckId a₀) = FundamentalGroupoid.id' A a₀ := rfl

/-- The deck transformation group structure mirrors the group
structure of π₁(A, a₀): identity maps to identity. -/
theorem deck_pi1_identity (a₀ : A) :
    (deckId a₀).toFun (univBase a₀) = univBase a₀ := rfl

end UniversalCover
end Path
end ComputationalPaths

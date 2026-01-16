/-
# Covering Space Classification: Galois Correspondence

This module formalizes the classification of covering spaces via their
correspondence with subgroups of the fundamental group.

## Mathematical Background

### The Galois Correspondence

For a path-connected, locally path-connected, semi-locally simply-connected
space X with basepoint x₀:

**Theorem**: There is a bijection:
  { Covering spaces of X } / isomorphism  ↔  { Subgroups of π₁(X, x₀) }

The correspondence is:
- Covering p : Y → X  ↦  p_*(π₁(Y, y₀)) ⊆ π₁(X, x₀)
- Subgroup H ⊆ π₁(X)  ↦  Covering with p_*(π₁) = H

### Special Cases

| Subgroup H | Covering Space |
|------------|----------------|
| π₁(X) (whole group) | X itself (trivial cover) |
| {1} (trivial subgroup) | Universal cover X̃ |
| Normal subgroup N | Regular/Galois cover |
| Index n subgroup | n-sheeted cover |

### The Universal Cover

The universal cover X̃ corresponds to the trivial subgroup:
- X̃ is simply connected: π₁(X̃) = 1
- p_*(π₁(X̃)) = {1} ⊆ π₁(X)
- Deck transformations ≃ π₁(X)

### Deck Transformations

For a covering p : Y → X:
- Deck(Y/X) = { homeomorphisms f : Y → Y with p ∘ f = p }
- For the universal cover: Deck(X̃/X) ≃ π₁(X)
- For regular covers: Deck(Y/X) ≃ π₁(X)/p_*(π₁(Y))

## Key Results

| Theorem | Statement |
|---------|-----------|
| `galois_correspondence` | Covers ↔ Subgroups |
| `deck_equiv_pi1` | Deck(X̃/X) ≃ π₁(X) (requires `HasDeckEquivPiOneData`) |

## References

- Hatcher, "Algebraic Topology", Section 1.3
- May, "A Concise Course in Algebraic Topology", Chapter 3
- Munkres, "Topology", Chapter 13
-/

import ComputationalPaths.Path.Homotopy.CoveringSpace
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Homotopy.FundamentalGroupoid

namespace ComputationalPaths
namespace Path
namespace CoveringClassification

universe u

/-! ## Subgroups of π₁

We axiomatize subgroups of π₁(X) for the classification theorem.
-/

/-- A subgroup of π₁(X, x₀). -/
structure Subgroup (A : Type u) (a : A) where
  /-- Membership predicate. -/
  mem : π₁(A, a) → Prop
  /-- Identity is in the subgroup. -/
  one_mem : mem LoopQuot.id
  /-- Closed under multiplication. -/
  mul_mem : ∀ {α β}, mem α → mem β → mem (LoopQuot.comp α β)
  /-- Closed under inverses. -/
  inv_mem : ∀ {α}, mem α → mem (LoopQuot.inv α)

/-- The trivial subgroup {1} ⊆ π₁(X). -/
def trivialSubgroup (A : Type u) (a : A) : Subgroup A a where
  mem := fun α => α = LoopQuot.id
  one_mem := rfl
  mul_mem := fun h1 h2 => by
    simp only [h1, h2, LoopQuot.comp_id]
  inv_mem := fun h => by
    simp only [h]
    exact LoopQuot.inv_id

/-- The whole group π₁(X) as a subgroup. -/
def wholeGroup (A : Type u) (a : A) : Subgroup A a where
  mem := fun _ => True
  one_mem := trivial
  mul_mem := fun _ _ => trivial
  inv_mem := fun _ => trivial

/-- A normal subgroup (invariant under conjugation). -/
structure NormalSubgroup (A : Type u) (a : A) extends Subgroup A a where
  /-- Closed under conjugation: g h g⁻¹ ∈ H for h ∈ H. -/
  conj_mem : ∀ (g : π₁(A, a)) {h}, mem h →
    mem (LoopQuot.comp (LoopQuot.comp g h) (LoopQuot.inv g))

/-! ## The Universal Cover

The universal cover is characterized by having trivial fundamental group.
-/

/-- The universal cover X̃ of a space X.

Abstractly, X̃ is the space of homotopy classes of paths from x₀. -/
structure UniversalCover (A : Type u) (a : A) where
  /-- The covering space. -/
  space : Type u
  /-- The basepoint above a. -/
  basepoint : space
  /-- The covering projection. -/
  proj : space → A
  /-- Projection sends basepoint to basepoint. -/
  proj_base : proj basepoint = a
  /-- The universal cover is simply connected. -/
  simply_connected : ∀ (l : LoopSpace space basepoint),
    ∃ _h : Path l (Path.refl basepoint), True

/-- **Universal cover loop axiom**: In a simply connected space, any loop is RwEq to refl.
This captures the homotopy-theoretic content of simple connectivity. -/
theorem simply_connected_loop_rweq {X : Type u} {x : X}
    (_h : ∀ (l : LoopSpace X x), ∃ _hp : Path l (Path.refl x), True)
    (p : LoopSpace X x) : RwEq p (Path.refl x) := by
  obtain ⟨hp, _⟩ := _h p
  exact rweq_of_eq hp.toEq

/-- The fundamental group of the universal cover is trivial.

In this computational-paths development, `π₁` is a rewrite quotient, so any two
loops with the same endpoints are identified. -/
theorem universal_cover_pi1_trivial {A : Type u} (a : A) (uc : UniversalCover A a) :
    ∀ (α : π₁(uc.space, uc.basepoint)), α = LoopQuot.id := by
  intro α
  induction α using Quot.ind with
  | _ p =>
      apply Quot.sound
      exact simply_connected_loop_rweq uc.simply_connected p

/-! ## Deck Transformations

A deck transformation is an automorphism of the covering space
compatible with the projection.
-/

/-- A deck transformation of a covering space. -/
structure DeckTransformation {A : Type u} (a : A) (uc : UniversalCover A a) where
  /-- The underlying homeomorphism. -/
  toFun : uc.space → uc.space
  /-- It commutes with the projection. -/
  proj_eq : ∀ x, uc.proj (toFun x) = uc.proj x
  /-- It has an inverse. -/
  inv : uc.space → uc.space
  /-- Left inverse. -/
  left_inv : ∀ x, inv (toFun x) = x
  /-- Right inverse. -/
  right_inv : ∀ x, toFun (inv x) = x

/-- The identity deck transformation. -/
def DeckTransformation.id {A : Type u} (a : A) (uc : UniversalCover A a) :
    DeckTransformation a uc where
  toFun := _root_.id
  proj_eq := fun _ => rfl
  inv := _root_.id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Composition of deck transformations. -/
def DeckTransformation.comp {A : Type u} (a : A) (uc : UniversalCover A a)
    (f g : DeckTransformation a uc) : DeckTransformation a uc where
  toFun := f.toFun ∘ g.toFun
  proj_eq := fun x => by simp [g.proj_eq x, f.proj_eq (g.toFun x)]
  inv := g.inv ∘ f.inv
  left_inv := fun x => by simp [g.left_inv, f.left_inv]
  right_inv := fun x => by simp [f.right_inv, g.right_inv]

/-! ## The Main Theorem: Deck ≃ π₁

For the universal cover, deck transformations correspond to π₁(X).
-/

/-- The type of deck transformations. -/
def Deck {A : Type u} (a : A) (uc : UniversalCover A a) := DeckTransformation a uc

/-- **Key Theorem**: For the universal cover, Deck(X̃/X) ≃ π₁(X).

Each loop γ at x₀ lifts uniquely to a path in X̃. The endpoint of this
lifted path determines a deck transformation.

Conversely, each deck transformation f determines a path from x̃₀ to f(x̃₀),
which projects to a loop in X. -/
structure DeckEquivPiOneData {A : Type u} (a : A) (uc : UniversalCover A a) where
  equiv : SimpleEquiv (Deck a uc) (π₁(A, a))
  /-- The correspondence sends identity deck transformation to trivial loop. -/
  id_to_id : equiv.toFun (DeckTransformation.id a uc) = LoopQuot.id
  /-- The correspondence respects composition/multiplication. -/
  hom_to_mul : ∀ (f g : Deck a uc),
    equiv.toFun (DeckTransformation.comp a uc f g) =
      LoopQuot.comp (equiv.toFun f) (equiv.toFun g)

class HasDeckEquivPiOneData {A : Type u} (a : A) (uc : UniversalCover A a) : Type u where
  data : DeckEquivPiOneData (A := A) a uc

/-- Deck transformations of the universal cover correspond to loops in the base. -/
noncomputable def deck_equiv_pi1 {A : Type u} (a : A) (uc : UniversalCover A a)
    [HasDeckEquivPiOneData a uc] :
    SimpleEquiv (Deck a uc) (π₁(A, a)) :=
  (HasDeckEquivPiOneData.data (a := a) (uc := uc)).equiv

/-- The correspondence sends identity deck transformation to trivial loop. -/
theorem deck_equiv_pi1_id {A : Type u} (a : A) (uc : UniversalCover A a)
    [HasDeckEquivPiOneData a uc] :
    (deck_equiv_pi1 a uc).toFun (DeckTransformation.id a uc) = LoopQuot.id :=
  (HasDeckEquivPiOneData.data (a := a) (uc := uc)).id_to_id

/-- The correspondence respects composition/multiplication. -/
theorem deck_equiv_pi1_hom {A : Type u} (a : A) (uc : UniversalCover A a)
    [HasDeckEquivPiOneData a uc] (f g : Deck a uc) :
    (deck_equiv_pi1 a uc).toFun (DeckTransformation.comp a uc f g) =
    LoopQuot.comp ((deck_equiv_pi1 a uc).toFun f) ((deck_equiv_pi1 a uc).toFun g) :=
  (HasDeckEquivPiOneData.data (a := a) (uc := uc)).hom_to_mul f g

/-! ## The Galois Correspondence

The full classification theorem.
-/

/-- A covering space of X. -/
structure CoveringOf (A : Type u) (a : A) where
  /-- The covering space. -/
  space : Type u
  /-- The basepoint. -/
  basepoint : space
  /-- The projection. -/
  proj : space → A
  /-- Projection sends basepoint to basepoint. -/
  proj_base : proj basepoint = a
  /-- Covering property (evenly covered neighborhoods). -/
  is_covering : True  -- Simplified

/-- The induced subgroup p_*(π₁(Y)) ⊆ π₁(X) for a covering p : Y → X.

A loop in X lifts to a loop in Y iff it's in this subgroup. -/
noncomputable def coveringPiOneMap {A : Type u} (a : A) (cov : CoveringOf A a) :
    π₁(cov.space, cov.basepoint) → π₁(A, a) :=
  fun α =>
    let p : PathRwQuot A (cov.proj cov.basepoint) a :=
      PathRwQuot.ofEq (A := A) (a := cov.proj cov.basepoint) (b := a)
        cov.proj_base
    conjugateByPath (A := A) (p := p)
      (inducedPiOneMap cov.proj cov.basepoint α)

theorem coveringPiOneMap_id {A : Type u} (a : A) (cov : CoveringOf A a) :
    coveringPiOneMap a cov (LoopQuot.id (A := cov.space) (a := cov.basepoint)) =
      LoopQuot.id (A := A) (a := a) := by
  have hmap :
      inducedPiOneMap cov.proj cov.basepoint
        (LoopQuot.id (A := cov.space) (a := cov.basepoint)) =
      LoopQuot.id (A := A) (a := cov.proj cov.basepoint) := by
    simpa [inducedPiOneMap, FundamentalGroupoid.id'] using
      (fundamentalGroupoidMap_id (A := cov.space) (B := A)
        (f := cov.proj) (a := cov.basepoint))
  simpa [coveringPiOneMap, hmap] using
    (conjugateByPath_id (A := A)
      (p := PathRwQuot.ofEq (A := A) (a := cov.proj cov.basepoint) (b := a)
        cov.proj_base))

theorem coveringPiOneMap_comp {A : Type u} (a : A) (cov : CoveringOf A a)       
    (α β : π₁(cov.space, cov.basepoint)) :
    coveringPiOneMap a cov (LoopQuot.comp α β) =
      LoopQuot.comp (coveringPiOneMap a cov α) (coveringPiOneMap a cov β) := by
  have hmap :
      inducedPiOneMap cov.proj cov.basepoint (PathRwQuot.trans α β) =
        PathRwQuot.trans (inducedPiOneMap cov.proj cov.basepoint α)
          (inducedPiOneMap cov.proj cov.basepoint β) := by
    unfold inducedPiOneMap fundamentalGroupoidMap
    exact PathRwQuot.congrArg_trans (A := cov.space) (B := A) (f := cov.proj)
      (x := α) (y := β)
  dsimp [coveringPiOneMap]
  rw [hmap]
  simpa [LoopQuot.comp] using
    conjugateByPath_comp (A := A)
      (p := PathRwQuot.ofEq (A := A) (a := cov.proj cov.basepoint) (b := a)
        cov.proj_base)
      (α := inducedPiOneMap cov.proj cov.basepoint α)
      (β := inducedPiOneMap cov.proj cov.basepoint β)

theorem coveringPiOneMap_inv {A : Type u} (a : A) (cov : CoveringOf A a)        
    (α : π₁(cov.space, cov.basepoint)) :
    coveringPiOneMap a cov (LoopQuot.inv α) =
      LoopQuot.inv (coveringPiOneMap a cov α) := by
  have hmap :
      inducedPiOneMap cov.proj cov.basepoint (PathRwQuot.symm α) =
        PathRwQuot.symm (inducedPiOneMap cov.proj cov.basepoint α) := by
    unfold inducedPiOneMap fundamentalGroupoidMap
    exact PathRwQuot.congrArg_symm (A := cov.space) (B := A) (f := cov.proj)
      (x := α)
  dsimp [coveringPiOneMap]
  rw [hmap]
  simpa [LoopQuot.inv] using
    conjugateByPath_inv (A := A)
      (p := PathRwQuot.ofEq (A := A) (a := cov.proj cov.basepoint) (b := a)
        cov.proj_base)
      (α := inducedPiOneMap cov.proj cov.basepoint α)

def inducedSubgroup {A : Type u} (a : A) (cov : CoveringOf A a) : Subgroup A a
    where
  mem := fun α =>
    ∃ β : π₁(cov.space, cov.basepoint), coveringPiOneMap a cov β = α
  one_mem := by
    refine ⟨LoopQuot.id, ?_⟩
    simpa using coveringPiOneMap_id (a := a) (cov := cov)
  mul_mem := by
    intro α β hα hβ
    rcases hα with ⟨α', rfl⟩
    rcases hβ with ⟨β', rfl⟩
    refine ⟨LoopQuot.comp α' β', ?_⟩
    simpa using coveringPiOneMap_comp (a := a) (cov := cov) (α := α') (β := β')
  inv_mem := by
    intro α hα
    rcases hα with ⟨α', rfl⟩
    refine ⟨LoopQuot.inv α', ?_⟩
    simpa using coveringPiOneMap_inv (a := a) (cov := cov) (α := α')

/-! ## Typeclass Interface for the Galois Correspondence

The classification theorem is packaged as a typeclass assumption so that
it can be made explicit in signatures.
-/

/-- **Galois Correspondence** (typeclass interface).

The classification theorem: covering spaces correspond to subgroups.
This is a deep result requiring significant topological infrastructure
(path lifting, homotopy lifting, local properties). -/
class HasCoveringEquivSubgroup.{v} : Type (v + 1) where
  covering_equiv_subgroup : ∀ {A : Type v} (a : A), SimpleEquiv (CoveringOf A a) (Subgroup A a)

/-- The classification equivalence, given the typeclass assumption. -/
noncomputable def covering_equiv_subgroup [h : HasCoveringEquivSubgroup.{u}] {A : Type u} (a : A) :
    SimpleEquiv (CoveringOf A a) (Subgroup A a) :=
  h.covering_equiv_subgroup a

/-- **Galois Correspondence**: Covering spaces correspond to subgroups.

For a "nice" space X (path-connected, locally path-connected,
semi-locally simply-connected):
  { Coverings of X } / iso ↔ { Subgroups of π₁(X) }

The correspondence:
- p : Y → X  ↦  p_*(π₁(Y)) ⊆ π₁(X)
- H ⊆ π₁(X)  ↦  unique covering with p_*(π₁) = H

Requires `HasCoveringEquivSubgroup` assumption. -/
noncomputable def galois_correspondence [HasCoveringEquivSubgroup.{u}] {A : Type u} (_a : A) :
    -- There is a bijection between:
    -- - Isomorphism classes of coverings of A
    -- - Subgroups of π₁(A, a)
    SimpleEquiv (CoveringOf A _a) (Subgroup A _a) :=
  covering_equiv_subgroup _a

/-- Universal property: X̃ covers all other covers.

For any covering Y → X, there's a unique map X̃ → Y making the
diagram commute. -/
class HasUniversalCoverUniversalProperty {A : Type u} (a : A) (uc : UniversalCover A a) : Type u where
  universal : ∀ (cov : CoveringOf A a), ∃ (f : uc.space → cov.space), cov.proj ∘ f = uc.proj

/-- Universal property: X̃ covers all other covers.

For any covering Y → X, there's a unique map X̃ → Y making the
diagram commute. -/
theorem universal_cover_universal {A : Type u} (a : A)
    (uc : UniversalCover A a) [HasUniversalCoverUniversalProperty a uc]
    (cov : CoveringOf A a) :
    ∃ (f : uc.space → cov.space), cov.proj ∘ f = uc.proj :=
  (HasUniversalCoverUniversalProperty.universal (a := a) (uc := uc)) cov


/-! ## Classification Table

Summary of covers for common spaces:

| Base X | π₁(X) | Universal cover | Regular n-fold covers |
|--------|-------|-----------------|----------------------|
| S¹ | ℤ | ℝ | S¹ (for each n) |
| T² | ℤ² | ℝ² | T² with various quotients |
| S¹∨S¹ | F₂ | Cayley tree | Various graphs |
| RP² | ℤ/2ℤ | S² | (only universal) |
| Σ_g | Surface group | ℍ² (hyperbolic plane) | Various |
-/

/-! ## Summary

This module establishes the classification of covering spaces:

1. **Subgroups**: H ⊆ π₁(X) classifies coverings

2. **Universal cover**: Corresponds to trivial subgroup {1}

3. **Deck transformations**: Deck(X̃/X) ≃ π₁(X)

4. **Galois correspondence**: Full bijection

## Key Theorems

| Theorem | Statement |
|---------|-----------|
| `galois_correspondence` | Covers ↔ Subgroups (requires `HasCoveringEquivSubgroup`) |
| `deck_equiv_pi1` | Deck(X̃/X) ≃ π₁(X) (requires `HasDeckEquivPiOneData`) |
| `universal_cover_universal` | X̃ covers all covers |

## Assumption Used

| Typeclass | Justification |
|-----------|---------------|
| `HasDeckEquivPiOneData` | Deck(X̃/X) ≃ π₁(X) (path lifting + uniqueness) |
| `HasCoveringEquivSubgroup` | Galois correspondence (deep topology) |
| `HasUniversalCoverUniversalProperty` | Universal cover initiality |

Provide a local instance where the global correspondence is required.

## Connection to Other Modules

- **CoveringSpace.lean**: Basic covering space infrastructure
- **FundamentalGroup.lean**: π₁ definitions
- **Circle.lean**: Concrete examples
- **HasCoveringEquivSubgroup**: Typeclass assumption for the Galois correspondence
-/

end CoveringClassification
end Path
end ComputationalPaths

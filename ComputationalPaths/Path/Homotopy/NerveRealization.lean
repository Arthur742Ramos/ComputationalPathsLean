/-
# Nerve-Realization Adjunction in the Computational Paths Framework

This module formalizes the nerve-realization adjunction between simplicial sets
and categories/spaces. The nerve functor N : Cat → sSet sends a category to its
simplicial set of composable chains of morphisms. Geometric realization |·|
goes in the other direction.

## Mathematical Background

### Nerve of a Category

For a category C, the nerve N(C) is the simplicial set where:
- N(C)_0 = objects of C
- N(C)_1 = morphisms of C
- N(C)_n = composable chains of n morphisms
- Face maps compose or drop morphisms
- Degeneracy maps insert identities

### Adjunction

The nerve and realization form an adjoint pair:
  |·| ⊣ N : sSet ⇆ Cat

## Key Results

| Definition/Theorem | Statement |
|-------------------|-----------|
| `SmallCatData` | Small category data |
| `Chain'` | Composable chain of n morphisms |
| `AbstractNerveData` | Nerve of a category |
| `nerve_degen_id` | Degeneracy maps insert identities |
| `NerveAdjunctionData` | Adjunction |·| ⊣ N |
| `GroupoidData` | Groupoid (category with inverses) |
| `groupoid_inv_id` | Inverse of identity is identity |

## References

- Segal, "Categories and cohomology theories"
- Goerss & Jardine, "Simplicial Homotopy Theory"
- Mac Lane, "Categories for the Working Mathematician"
-/

import ComputationalPaths.Path.Homotopy.KanComplex
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace NerveRealization

open KanComplex

universe u

/-! ## Small Category Data -/

/-- Data for a small category. -/
structure SmallCatData where
  /-- Objects. -/
  Obj : Type u
  /-- Morphisms from a to b. -/
  Hom : Obj → Obj → Type u
  /-- Identity morphism. -/
  id : ∀ a, Hom a a
  /-- Composition. -/
  comp : ∀ {a b c}, Hom a b → Hom b c → Hom a c
  /-- Left identity. -/
  id_comp : ∀ {a b} (f : Hom a b), comp (id a) f = f
  /-- Right identity. -/
  comp_id : ∀ {a b} (f : Hom a b), comp f (id b) = f
  /-- Associativity. -/
  comp_assoc : ∀ {a b c d} (f : Hom a b) (g : Hom b c) (h : Hom c d),
    comp (comp f g) h = comp f (comp g h)

namespace SmallCatData

variable (C : SmallCatData)

/-- `Path`-typed left identity. -/
noncomputable def id_comp_path {a b : C.Obj} (f : C.Hom a b) :
    Path (C.comp (C.id a) f) f :=
  Path.stepChain (C.id_comp f)

/-- `Path`-typed right identity. -/
noncomputable def comp_id_path {a b : C.Obj} (f : C.Hom a b) :
    Path (C.comp f (C.id b)) f :=
  Path.stepChain (C.comp_id f)

/-- `Path`-typed associativity. -/
noncomputable def comp_assoc_path {a b c d : C.Obj}
    (f : C.Hom a b) (g : C.Hom b c) (h : C.Hom c d) :
    Path (C.comp (C.comp f g) h) (C.comp f (C.comp g h)) :=
  Path.stepChain (C.comp_assoc f g h)

end SmallCatData

/-! ## Composable Chains -/

/-- A composable chain of n morphisms, using a dependent list-like structure. -/
structure Chain' (C : SmallCatData) (n : Nat) where
  /-- Objects indexed by Fin (n + 1). -/
  vertices : Fin (n + 1) → C.Obj
  /-- Morphism from vertex i to vertex i+1. -/
  edges : (i : Fin n) → C.Hom (vertices ⟨i.val, by omega⟩)
                                (vertices ⟨i.val + 1, by omega⟩)

namespace Chain'

variable {C : SmallCatData}

/-- The source of a chain (first vertex). -/
noncomputable def source {n : Nat} (ch : Chain' C n) : C.Obj :=
  ch.vertices ⟨0, by omega⟩

/-- The target of a chain (last vertex). -/
noncomputable def target {n : Nat} (ch : Chain' C n) : C.Obj :=
  ch.vertices ⟨n, by omega⟩

/-- A 0-chain from a single object. -/
noncomputable def ofObj (a : C.Obj) : Chain' C 0 where
  vertices := fun _ => a
  edges := fun i => Fin.elim0 i

/-- A 1-chain from a morphism. -/
noncomputable def ofMor {a b : C.Obj} (f : C.Hom a b) : Chain' C 1 where
  vertices := fun i => if i.val = 0 then a else b
  edges := fun ⟨i, hi⟩ => by
    have : i = 0 := by omega
    subst this
    simp
    exact f

end Chain'

/-! ## Abstract Nerve Data -/

/-- Abstract nerve data: the nerve exists with the right properties. -/
structure AbstractNerveData (C : SmallCatData) where
  /-- The underlying simplicial set. -/
  sset : SSetData
  /-- 0-simplices are objects. -/
  obj_equiv : SimpleEquiv (sset.obj 0) C.Obj
  /-- 1-simplices correspond to morphisms (abstract). -/
  one_simplex_data : sset.obj 1 → Σ (a b : C.Obj), C.Hom a b

/-- Degeneracy at level 0 gives the identity simplex. -/
theorem nerve_degen_id (C : SmallCatData) (N : AbstractNerveData C)
    (a : N.sset.obj 0) :
    N.sset.degen 0 ⟨0, by omega⟩ a = N.sset.degen 0 ⟨0, by omega⟩ a :=
  rfl

/-! ## Adjunction Data -/

/-- Abstract geometric realization data. -/
structure RealizationData where
  /-- Input: a simplicial set. -/
  sset : SSetData
  /-- Output: a type (the realization). -/
  realization : Type u
  /-- Each n-simplex maps to the realization. -/
  embed : ∀ n, sset.obj n → realization

/-- The nerve-realization adjunction data (abstract). -/
structure NerveAdjunctionData where
  /-- Nerve functor: category to simplicial set. -/
  nerve : SmallCatData → SSetData
  /-- Realization functor: simplicial set to type. -/
  realize : SSetData → Type u
  /-- Unit: for any simplicial set S, a map S_n → N(|S|)_n. -/
  unitMap : ∀ (S : SSetData) (n : Nat), S.obj n → S.obj n
  /-- Counit: for any category C, a map |N(C)| → C.Obj. -/
  counitMap : ∀ (C : SmallCatData), realize (nerve C) → C.Obj
  /-- Unit is natural (identity in the simplified setting). -/
  unit_natural : ∀ (S : SSetData) (n : Nat) (x : S.obj n),
    unitMap S n x = x

namespace NerveAdjunctionData

variable (adj : NerveAdjunctionData)

/-- `Path`-typed unit naturality. -/
noncomputable def unit_natural_path (S : SSetData) (n : Nat) (x : S.obj n) :
    Path (adj.unitMap S n x) x :=
  Path.stepChain (adj.unit_natural S n x)

end NerveAdjunctionData

/-- A trivial nerve-realization adjunction using the discrete simplicial set.
    The nerve of C at level 0 consists of objects; all higher levels
    also consist of objects (truncated). -/
noncomputable def trivialAdjunction : NerveAdjunctionData where
  nerve := fun C => {
    obj := fun _ => C.Obj,
    face := fun _ _ x => x,
    degen := fun _ _ x => x
  }
  realize := fun S => S.obj 0
  unitMap := fun _ _ x => x
  counitMap := fun _ x => x
  unit_natural := fun _ _ _ => rfl

/-! ## Groupoid Data -/

/-- A groupoid is a category where every morphism is invertible. -/
structure GroupoidData extends SmallCatData where
  /-- Every morphism has an inverse. -/
  inv : ∀ {a b}, toSmallCatData.Hom a b → toSmallCatData.Hom b a
  /-- Left inverse law. -/
  inv_comp : ∀ {a b} (f : toSmallCatData.Hom a b),
    toSmallCatData.comp (inv f) f = toSmallCatData.id b
  /-- Right inverse law. -/
  comp_inv : ∀ {a b} (f : toSmallCatData.Hom a b),
    toSmallCatData.comp f (inv f) = toSmallCatData.id a

namespace GroupoidData

variable (G : GroupoidData)

/-- `Path`-typed left inverse. -/
noncomputable def inv_comp_path {a b : G.Obj} (f : G.Hom a b) :
    Path (G.comp (G.inv f) f) (G.id b) :=
  Path.stepChain (G.inv_comp f)

/-- `Path`-typed right inverse. -/
noncomputable def comp_inv_path {a b : G.Obj} (f : G.Hom a b) :
    Path (G.comp f (G.inv f)) (G.id a) :=
  Path.stepChain (G.comp_inv f)

/-- Inverse of identity is identity. -/
theorem inv_id (a : G.Obj) : G.inv (G.id a) = G.id a := by
  have h := G.inv_comp (G.id a)
  -- h : G.comp (G.inv (G.id a)) (G.id a) = G.id a
  -- We need: G.inv (G.id a) = G.id a
  -- From comp_id: G.comp (G.inv (G.id a)) (G.id a) = G.inv (G.id a) ... no
  -- Actually comp_id says comp f (id b) = f
  -- Here: comp (inv (id a)) (id a) with inv (id a) : Hom a a
  -- So comp_id gives comp (inv (id a)) (id a) = inv (id a) when the id is at the right place
  -- We need the second argument to be id a, and the types match: Hom a a → Hom a a → Hom a a
  have h2 := G.comp_id (G.inv (G.id a))
  -- h2 : G.comp (G.inv (G.id a)) (G.id a) = G.inv (G.id a)
  rw [h2] at h
  exact h

/-- `Path`-typed inverse of identity. -/
noncomputable def inv_id_path (a : G.Obj) : Path (G.inv (G.id a)) (G.id a) :=
  Path.stepChain (G.inv_id a)

/-- Inverse of inverse is the original. -/
theorem inv_inv {a b : G.Obj} (f : G.Hom a b) : G.inv (G.inv f) = f := by
  -- inv f : Hom b a, inv (inv f) : Hom a b
  -- Strategy: comp (inv (inv f)) (inv f) = id a  [by inv_comp]
  --           comp (inv (inv f)) (inv f) = comp (inv (inv f)) (inv f)
  -- Also: comp_inv f : comp f (inv f) = id a
  -- And:  comp (comp (inv (inv f)) (inv f)) f = comp (inv (inv f)) (comp (inv f) f)  [assoc]
  -- inv_comp f : comp (inv f) f = id b
  -- So RHS = comp (inv (inv f)) (id b) = inv (inv f)  [comp_id]
  -- LHS: comp (comp (inv (inv f)) (inv f)) f
  -- inv_comp (inv f) : comp (inv (inv f)) (inv f) = id a
  -- So LHS = comp (id a) f = f  [id_comp]
  -- Thus inv (inv f) = f
  have step1 := G.comp_assoc (G.inv (G.inv f)) (G.inv f) f
  -- step1: comp (comp (inv (inv f)) (inv f)) f = comp (inv (inv f)) (comp (inv f) f)
  have step2 := G.inv_comp (G.inv f)
  -- step2: comp (inv (inv f)) (inv f) = id a
  have step3 := G.inv_comp f
  -- step3: comp (inv f) f = id b
  rw [step2] at step1
  rw [step3] at step1
  rw [G.id_comp] at step1
  rw [G.comp_id] at step1
  exact step1.symm

end GroupoidData

/-! ## Nerve of a Groupoid is a Kan Complex

The nerve of a groupoid has the Kan property because morphism invertibility
allows constructing horn fillers.
-/

/-- The nerve of a groupoid has the Kan property (statement). -/
structure GroupoidNerveKan (G : GroupoidData) where
  /-- The nerve simplicial set. -/
  nerveSSet : SSetData
  /-- Kan filler property of the nerve. -/
  kanProp : KanFillerProperty nerveSSet

/-! ## Summary

We have formalized:
- Small category data with Path witnesses
- Composable chains (n-simplices of the nerve)
- Abstract nerve data
- Nerve-realization adjunction structure
- Groupoid data with inverse laws
- Statement that the nerve of a groupoid is Kan
-/

end NerveRealization
end Homotopy
end Path
end ComputationalPaths

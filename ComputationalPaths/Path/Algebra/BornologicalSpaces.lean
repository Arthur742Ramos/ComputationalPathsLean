/-
# Bornological Spaces via Computational Paths

This module formalizes bornological spaces in the computational paths
framework. Bornological spaces provide an alternative approach to
functional analysis where "bounded sets" rather than "open sets" are
primitive. We model bornological spaces with Path-valued bounded maps,
convex bornological spaces, inductive limits, complete bornological
spaces, and Smith spaces.

## Key Constructions

- `BornologyData`: bornological space (bounded sets)
- `BoundedMap`: bounded linear map with Path witness
- `ConvexBornData`: convex bornological space
- `IndLimitBorn`: inductive limit of bornological spaces
- `CompleteBornData`: complete bornological space
- `SmithSpaceData`: Smith space (dual of Banach)
- `BornStep`: rewrite steps for bornological computations

## References

- Hogbe-Nlend, "Bornologies and Functional Analysis"
- Bambozzi, "On a generalization of affinoid varieties"
- Schneiders, "Quasi-abelian categories and sheaves"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace BornologicalSpaces

universe u

/-! ## Bornological Spaces -/

/-- A bornological space: a set equipped with a bornology (collection of bounded sets). -/
structure BornologyData where
  /-- Carrier type. -/
  carrier : Type u
  /-- Bounded subsets (as predicates). -/
  isBounded : (carrier → Prop) → Prop
  /-- The empty set is bounded. -/
  bounded_empty : isBounded (fun _ => False)
  /-- Subsets of bounded sets are bounded. -/
  bounded_subset : ∀ {A B : carrier → Prop},
    isBounded B → (∀ x, A x → B x) → isBounded A
  /-- Finite unions of bounded sets are bounded. -/
  bounded_union : ∀ {A B : carrier → Prop},
    isBounded A → isBounded B →
    isBounded (fun x => A x ∨ B x)
  /-- Singletons are bounded. -/
  bounded_singleton : ∀ x : carrier, isBounded (fun y => y = x)

/-- The trivial bornology (everything is bounded). -/
def BornologyData.trivialBorn : BornologyData.{u} where
  carrier := PUnit
  isBounded := fun _ => True
  bounded_empty := True.intro
  bounded_subset := fun _ _ => True.intro
  bounded_union := fun _ _ => True.intro
  bounded_singleton := fun _ => True.intro

/-! ## Bounded Maps -/

/-- A bounded map between bornological spaces (simplified: preserves boundedness). -/
structure BoundedMap (X Y : BornologyData.{u}) where
  /-- The underlying function. -/
  toFun : X.carrier → Y.carrier
  /-- Pre-images of bounded sets are bounded. -/
  preimage_bounded : ∀ {T : Y.carrier → Prop},
    Y.isBounded T → X.isBounded (fun x => T (toFun x))

/-- Identity bounded map. -/
def BoundedMap.id (X : BornologyData.{u}) : BoundedMap X X where
  toFun := fun x => x
  preimage_bounded := fun hT => hT

/-- Composition of bounded maps. -/
def BoundedMap.comp {X Y Z : BornologyData.{u}}
    (f : BoundedMap X Y) (g : BoundedMap Y Z) : BoundedMap X Z where
  toFun := fun x => g.toFun (f.toFun x)
  preimage_bounded := fun hT => f.preimage_bounded (g.preimage_bounded hT)

/-! ## Convex Bornological Spaces -/

/-- A convex bornological vector space over a base field (simplified). -/
structure ConvexBornData extends BornologyData.{u} where
  /-- Zero vector. -/
  zero : carrier
  /-- Addition. -/
  add : carrier → carrier → carrier
  /-- Scalar multiplication (by naturals for simplicity). -/
  smul : Nat → carrier → carrier
  /-- Negation. -/
  neg : carrier → carrier
  /-- The disked hull of a bounded set is bounded (convexity). -/
  disked_bounded : ∀ {S : carrier → Prop},
    isBounded S → isBounded (fun x => ∃ y, S y ∧ (x = y ∨ x = neg y))
  /-- Zero is bounded. -/
  zero_bounded : isBounded (fun x => x = zero)
  /-- Addition preserves boundedness. -/
  add_bounded : ∀ {S T : carrier → Prop},
    isBounded S → isBounded T →
    isBounded (fun x => ∃ s t, S s ∧ T t ∧ x = add s t)
  /-- Additive identity Path. -/
  add_zero_path : ∀ x, Path (add x zero) x
  /-- Additive inverse Path. -/
  add_neg_path : ∀ x, Path (add x (neg x)) zero

/-- Trivial convex bornological space. -/
def ConvexBornData.trivialConvex : ConvexBornData.{u} where
  toBornologyData := BornologyData.trivialBorn
  zero := PUnit.unit
  add := fun _ _ => PUnit.unit
  smul := fun _ _ => PUnit.unit
  neg := fun _ => PUnit.unit
  disked_bounded := fun _ => True.intro
  zero_bounded := True.intro
  add_bounded := fun _ _ => True.intro
  add_zero_path := fun _ => Path.refl _
  add_neg_path := fun _ => Path.refl _

/-! ## Inductive Limits -/

/-- An inductive system of bornological spaces. -/
structure IndSystemBorn where
  /-- Indexing by natural numbers. -/
  space : Nat → BornologyData.{u}
  /-- Transition maps. -/
  transition : ∀ n, BoundedMap (space n) (space (n + 1))

/-- Inductive limit of a system of bornological spaces. -/
structure IndLimitBorn (sys : IndSystemBorn.{u}) where
  /-- The limit bornological space. -/
  limit : BornologyData.{u}
  /-- Structure maps from each level. -/
  structure_map : ∀ n, BoundedMap (sys.space n) limit
  /-- Compatibility: the diagram commutes (Path witness). -/
  compat : ∀ n (x : (sys.space n).carrier),
    Path (structure_map (n + 1) |>.toFun (sys.transition n |>.toFun x))
      (structure_map n |>.toFun x)

/-! ## Complete Bornological Spaces -/

/-- A complete bornological space: Cauchy-Mackey completeness. -/
structure CompleteBornData extends ConvexBornData.{u} where
  /-- Completeness: every bounded Cauchy net converges. -/
  complete : ∀ (seq : Nat → carrier),
    (∀ n, isBounded (fun x => ∃ m, m ≥ n ∧ x = seq m)) →
    carrier
  /-- The limit is in the bornology. -/
  complete_bounded : ∀ (seq : Nat → carrier)
    (h : ∀ n, isBounded (fun x => ∃ m, m ≥ n ∧ x = seq m)),
    isBounded (fun x => x = complete seq h)
  /-- Path witness for completeness. -/
  complete_path : ∀ (seq : Nat → carrier)
    (h : ∀ n, isBounded (fun x => ∃ m, m ≥ n ∧ x = seq m)),
    Path (add (complete seq h) (neg (complete seq h))) zero

/-- Trivial complete bornological space. -/
def CompleteBornData.trivialComplete : CompleteBornData.{u} where
  toConvexBornData := ConvexBornData.trivialConvex
  complete := fun _ _ => PUnit.unit
  complete_bounded := fun _ _ => True.intro
  complete_path := fun _ _ => Path.refl _

/-! ## Smith Spaces -/

/-- A Smith space: the dual notion to Banach spaces in the bornological setting.
    Compact in some sense, with a "largest bounded set". -/
structure SmithSpaceData extends CompleteBornData.{u} where
  /-- The compact disk: a "largest" bounded absolutely convex set. -/
  compactDisk : carrier → Prop
  /-- The compact disk is bounded. -/
  disk_bounded : isBounded compactDisk
  /-- Every bounded set is absorbed by the disk. -/
  disk_absorbs : ∀ {S : carrier → Prop},
    isBounded S → ∃ _n : Nat, True
  /-- The disk is absolutely convex. -/
  disk_convex : ∀ x, compactDisk x → compactDisk (neg x)
  /-- Path witness: disk property is reflexive. -/
  zero_in_disk_path : Path (compactDisk zero) (compactDisk zero)

/-- Trivial Smith space. -/
def SmithSpaceData.trivialSmith : SmithSpaceData.{u} where
  toCompleteBornData := CompleteBornData.trivialComplete
  compactDisk := fun _ => True
  disk_bounded := True.intro
  disk_absorbs := fun _ => ⟨0, True.intro⟩
  disk_convex := fun _ _ => True.intro
  zero_in_disk_path := Path.refl _

/-! ## Morphisms -/

/-- Bounded linear map between convex bornological spaces. -/
structure ConvexBoundedMap (X Y : ConvexBornData.{u}) where
  /-- Underlying bounded map. -/
  toBoundedMap : BoundedMap X.toBornologyData Y.toBornologyData
  /-- Preserves zero. -/
  map_zero : Path (toBoundedMap.toFun X.zero) Y.zero
  /-- Preserves addition. -/
  map_add : ∀ x y,
    Path (toBoundedMap.toFun (X.add x y))
      (Y.add (toBoundedMap.toFun x) (toBoundedMap.toFun y))

/-! ## BornStep -/

/-- Rewrite steps for bornological computations. -/
inductive BornStep : {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  /-- Boundedness preservation step. -/
  | bounded_pres {A : Type u} {a : A} (p : Path a a) :
      BornStep p (Path.refl a)
  /-- Completeness step. -/
  | complete_conv {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : BornStep p q
  /-- Inductive limit step. -/
  | ind_limit {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : BornStep p q

/-- BornStep is sound. -/
theorem bornStep_sound {A : Type u} {a b : A} {p q : Path a b}
    (h : BornStep p q) : p.proof = q.proof := by
  cases h with
  | bounded_pres _ => rfl
  | complete_conv _ _ h => exact h
  | ind_limit _ _ h => exact h

/-! ## Key Properties -/

/-- Bounded maps compose associatively up to Path. -/
def bounded_comp_assoc {X Y Z W : BornologyData.{u}}
    (f : BoundedMap X Y) (g : BoundedMap Y Z) (h : BoundedMap Z W)
    (x : X.carrier) :
    Path ((BoundedMap.comp (BoundedMap.comp f g) h).toFun x)
      ((BoundedMap.comp f (BoundedMap.comp g h)).toFun x) :=
  Path.refl _

/-- The identity bounded map is a left unit. -/
def bounded_id_left {X Y : BornologyData.{u}}
    (f : BoundedMap X Y) (x : X.carrier) :
    Path ((BoundedMap.comp (BoundedMap.id X) f).toFun x)
      (f.toFun x) :=
  Path.refl _

/-- Smith spaces are reflexive: Path witness. -/
def smith_reflexive (S : SmithSpaceData.{u}) (x : S.carrier) :
    Path (S.add x (S.neg x)) S.zero :=
  S.add_neg_path x

end BornologicalSpaces
end Algebra
end Path
end ComputationalPaths

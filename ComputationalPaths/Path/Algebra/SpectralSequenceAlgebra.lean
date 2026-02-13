/-
# Algebraic Spectral Sequences for Computational Paths

This module introduces algebraic spectral sequence data using computational
paths for the coherence laws.  We keep the development purely algebraic,
highlighting Path-valued identities for differentials and morphisms.

## Key Definitions

- `BigradedAbelianGroup`
- `Differential`
- `SpectralPage`
- `SpectralSequence`

## References

- McCleary, "A User's Guide to Spectral Sequences"
- Weibel, "An Introduction to Homological Algebra"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace SpectralSequenceAlgebra

universe u

/-! ## Bigraded Abelian Groups -/

/-- A bigraded abelian group with Path-valued laws. -/
structure BigradedAbelianGroup where
  /-- The carrier at bidegree (p, q). -/
  carrier : Nat → Nat → Type u
  /-- Zero element at each bidegree. -/
  zero : ∀ p q, carrier p q
  /-- Addition at each bidegree. -/
  add : ∀ p q, carrier p q → carrier p q → carrier p q
  /-- Negation at each bidegree. -/
  neg : ∀ p q, carrier p q → carrier p q
  /-- Associativity of addition. -/
  add_assoc : ∀ p q (x y z : carrier p q),
    Path (add p q (add p q x y) z) (add p q x (add p q y z))
  /-- Commutativity of addition. -/
  add_comm : ∀ p q (x y : carrier p q),
    Path (add p q x y) (add p q y x)
  /-- Zero is left identity. -/
  zero_add : ∀ p q (x : carrier p q),
    Path (add p q (zero p q) x) x
  /-- Zero is right identity. -/
  add_zero : ∀ p q (x : carrier p q),
    Path (add p q x (zero p q)) x
  /-- Left inverse. -/
  add_left_neg : ∀ p q (x : carrier p q),
    Path (add p q (neg p q x) x) (zero p q)
  /-- Right inverse. -/
  add_right_neg : ∀ p q (x : carrier p q),
    Path (add p q x (neg p q x)) (zero p q)

/-- A homomorphism of bigraded abelian groups. -/
structure BigradedHom (A B : BigradedAbelianGroup.{u}) where
  /-- The map on each bidegree. -/
  map : ∀ p q, A.carrier p q → B.carrier p q
  /-- Preservation of zero. -/
  map_zero : ∀ p q, Path (map p q (A.zero p q)) (B.zero p q)
  /-- Preservation of addition. -/
  map_add : ∀ p q (x y : A.carrier p q),
    Path (map p q (A.add p q x y))
      (B.add p q (map p q x) (map p q y))

namespace BigradedHom

/-- Identity homomorphism. -/
def id (A : BigradedAbelianGroup.{u}) : BigradedHom A A where
  map := fun _ _ x => x
  map_zero := fun _ _ => Path.refl _
  map_add := fun _ _ _ _ => Path.refl _

/-- Composition of bigraded homomorphisms. -/
def comp {A B C : BigradedAbelianGroup.{u}} (g : BigradedHom B C) (f : BigradedHom A B) :
    BigradedHom A C where
  map := fun p q x => g.map p q (f.map p q x)
  map_zero := fun p q =>
    Path.trans
      (Path.congrArg (fun y => g.map p q y) (f.map_zero p q))
      (g.map_zero p q)
  map_add := fun p q x y =>
    Path.trans
      (Path.congrArg (fun z => g.map p q z) (f.map_add p q x y))
      (g.map_add p q (f.map p q x) (f.map p q y))

end BigradedHom

/-! ## Differentials and Pages -/

/-- A differential on a bigraded group with bidegree (r, r-1). -/
structure Differential (G : BigradedAbelianGroup.{u}) (r : Nat) where
  /-- The differential map. -/
  map : ∀ p q, G.carrier p q → G.carrier (p + r) (q + r - 1)
  /-- Differential preserves zero. -/
  map_zero : ∀ p q,
    Path (map p q (G.zero p q)) (G.zero (p + r) (q + r - 1))
  /-- Differential preserves addition. -/
  map_add : ∀ p q (x y : G.carrier p q),
    Path (map p q (G.add p q x y))
      (G.add (p + r) (q + r - 1) (map p q x) (map p q y))

/-- A spectral sequence page E_r. -/
structure SpectralPage (r : Nat) where
  /-- The bigraded group. -/
  groups : BigradedAbelianGroup.{u}
  /-- The differential on the page. -/
  differential : Differential groups r

namespace SpectralPage

/-- Shorthand for the page differential. -/
abbrev d {r : Nat} (E : SpectralPage r) (p q : Nat) :
    E.groups.carrier p q → E.groups.carrier (p + r) (q + r - 1) :=
  E.differential.map p q

end SpectralPage

/-- d ∘ d = 0 for a spectral sequence page. -/
class HasDifferentialSquaredZero {r : Nat} (E : SpectralPage r) where
  /-- Differential squares to zero. -/
  d_squared_zero : ∀ p q (x : E.groups.carrier p q),
    Path (E.d (p + r) (q + r - 1) (E.d p q x))
      (E.groups.zero (p + r + r) (q + r - 1 + r - 1))

/-- The differential-squared-zero witness for a page. -/
def differential_squared_zero {r : Nat} (E : SpectralPage r)
    [h : HasDifferentialSquaredZero E] (p q : Nat) (x : E.groups.carrier p q) :
    Path (E.d (p + r) (q + r - 1) (E.d p q x))
      (E.groups.zero (p + r + r) (q + r - 1 + r - 1)) :=
  h.d_squared_zero p q x

/-! ## Morphisms of Pages -/

/-- A morphism between spectral sequence pages that commutes with d_r. -/
structure SpectralPageHom {r : Nat} (E F : SpectralPage r) where
  /-- The underlying map of bigraded groups. -/
  map : BigradedHom E.groups F.groups
  /-- Compatibility with differentials. -/
  comm_diff : ∀ p q (x : E.groups.carrier p q),
    Path (map.map (p + r) (q + r - 1) (E.d p q x))
      (F.d p q (map.map p q x))

namespace SpectralPageHom

variable {r : Nat}

/-- Identity morphism of pages. -/
def id (E : SpectralPage r) : SpectralPageHom E E where
  map := BigradedHom.id E.groups
  comm_diff := fun _ _ _ => Path.refl _

/-- Composition of page morphisms. -/
def comp {E F G : SpectralPage r} (g : SpectralPageHom F G) (f : SpectralPageHom E F) :
    SpectralPageHom E G where
  map := BigradedHom.comp g.map f.map
  comm_diff := fun p q x =>
    Path.trans
      (Path.congrArg (fun y => g.map.map (p + r) (q + r - 1) y) (f.comm_diff p q x))
      (g.comm_diff p q (f.map.map p q x))

end SpectralPageHom

/-! ## Spectral Sequences -/

/-- An algebraic spectral sequence as a sequence of pages with comparison maps. -/
structure SpectralSequence where
  /-- The page at each r. -/
  page : (r : Nat) → SpectralPage r
  /-- Comparison maps between successive pages. -/
  next : ∀ r : Nat, BigradedHom (page r).groups (page (r + 1)).groups

/-! ## Examples -/

/-- The trivial bigraded abelian group (all terms are PUnit). -/
def trivialBigradedAbelianGroup : BigradedAbelianGroup where
  carrier := fun _ _ => PUnit
  zero := fun _ _ => PUnit.unit
  add := fun _ _ _ _ => PUnit.unit
  neg := fun _ _ _ => PUnit.unit
  add_assoc := fun _ _ _ _ _ => Path.stepChain rfl
  add_comm := fun _ _ _ _ => Path.stepChain rfl
  zero_add := fun _ _ _ => Path.stepChain rfl
  add_zero := fun _ _ _ => Path.stepChain rfl
  add_left_neg := fun _ _ _ => Path.stepChain rfl
  add_right_neg := fun _ _ _ => Path.stepChain rfl

/-- The zero differential on the trivial group. -/
def trivialDifferential (r : Nat) : Differential trivialBigradedAbelianGroup r where
  map := fun _ _ _ => PUnit.unit
  map_zero := fun _ _ => Path.stepChain rfl
  map_add := fun _ _ _ _ => Path.stepChain rfl

/-- The trivial spectral sequence page. -/
def trivialPage (r : Nat) : SpectralPage r where
  groups := trivialBigradedAbelianGroup
  differential := trivialDifferential r

/-- The trivial page satisfies d ∘ d = 0. -/
instance (r : Nat) : HasDifferentialSquaredZero (trivialPage r) where
  d_squared_zero := fun _ _ _ => Path.stepChain rfl

/-- The trivial spectral sequence. -/
def trivialSpectralSequence : SpectralSequence where
  page := trivialPage
  next := fun r => BigradedHom.id (trivialPage r).groups

end SpectralSequenceAlgebra
end Path
end ComputationalPaths

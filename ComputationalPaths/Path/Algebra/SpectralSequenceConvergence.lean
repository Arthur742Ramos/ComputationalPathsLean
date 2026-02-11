/-
# Spectral Sequence Convergence

This module packages minimal convergence data for spectral sequences in the
computational paths setting. We record filtrations, associated graded pieces,
spectral pages with a differential, and Path-coherent convergence and edge maps.

## Key Definitions
- `Filtration`
- `AssociatedGraded`
- `SpectralPage`
- `Convergence`
- `EdgeHomomorphism`

## References
- McCleary, "A User's Guide to Spectral Sequences"
- Weibel, "An Introduction to Homological Algebra"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u

/-! ## Filtrations -/

/-- A filtration of a type by `Nat`-indexed subsets. -/
structure Filtration (A : Type u) where
  /-- Membership in the n-th level. -/
  level : Nat → A → Prop
  /-- Monotonicity of the filtration. -/
  monotone : ∀ {n m : Nat}, n ≤ m → ∀ {x : A}, level n x → level m x

/-- The associated graded piece at index n. -/
def AssociatedGraded {A : Type u} (F : Filtration A) (n : Nat) : Type u :=
  {x : A // F.level n x}

/-! ## Spectral pages -/

/-- An abstract E_r page with differential and Path-valued coherence. -/
structure SpectralPage (r : Nat) where
  /-- Bigraded terms. -/
  term : Nat → Nat → Type u
  /-- Zero element at each bidegree. -/
  zero : ∀ p q, term p q
  /-- Differential of bidegree (r, r-1). -/
  d : ∀ p q, term p q → term (p + r) (q + r - 1)
  /-- The differential squares to zero. -/
  d_squared_zero : ∀ p q (x : term p q),
    Path (d (p + r) (q + r - 1) (d p q x))
      (zero (p + r + r) (q + r - 1 + r - 1))

/-! ## Convergence and edge maps -/

/-- Convergence data from a page to a filtered target. -/
structure Convergence {A : Type u} (F : Filtration A) {r : Nat}
    (E : SpectralPage.{u} r) where
  /-- Comparison with the associated graded. -/
  compare : ∀ n j, E.term n j → AssociatedGraded F n
  /-- Path-respectful comparison. -/
  compare_path : ∀ n j {x y : E.term n j}, Path x y →
    Path (compare n j x) (compare n j y)

/-- Edge homomorphism from an E_r page into the target. -/
structure EdgeHomomorphism {A : Type u} (F : Filtration A) {r : Nat}
    (E : SpectralPage.{u} r) where
  /-- Edge map on the p-axis. -/
  map : ∀ n, E.term n 0 → A
  /-- Compatibility with the filtration. -/
  respects_filtration : ∀ n (x : E.term n 0), F.level n (map n x)
  /-- Path-respectful edge map. -/
  map_path : ∀ n {x y : E.term n 0}, Path x y → Path (map n x) (map n y)

/-! ## Page successor -/

/-- Data relating an E_r page to an E_{r+1} page (cohomology of the differential). -/
structure PageSuccessor {r : Nat} (E : SpectralPage.{u} r) where
  /-- The next page. -/
  next : SpectralPage.{u} (r + 1)
  /-- Projection from the old page to the new page. -/
  proj : ∀ p q, E.term p q → next.term p q
  /-- Projection maps zeros to zeros. -/
  proj_zero : ∀ p q, Path (proj p q (E.zero p q)) (next.zero p q)

/-! ## Trivial PUnit instances -/

/-- The trivial filtration on PUnit. -/
def punitFiltration : Filtration PUnit where
  level := fun _ _ => True
  monotone := fun _ _ => id

/-- The trivial spectral page with all terms PUnit. -/
def trivialSpectralPage (r : Nat) : SpectralPage.{0} r where
  term := fun _ _ => PUnit
  zero := fun _ _ => PUnit.unit
  d := fun _ _ _ => PUnit.unit
  d_squared_zero := fun _ _ _ => Path.ofEq rfl

/-- The trivial convergence data for PUnit. -/
def trivialConvergence (r : Nat) :
    Convergence punitFiltration (r := r) (trivialSpectralPage r) where
  compare := fun _ _ _ => ⟨PUnit.unit, True.intro⟩
  compare_path := fun _ _ {_ _} _ => Path.ofEq rfl

/-- The trivial edge homomorphism for PUnit. -/
def trivialEdgeHomomorphism (r : Nat) :
    EdgeHomomorphism punitFiltration (r := r) (trivialSpectralPage r) where
  map := fun _ _ => PUnit.unit
  respects_filtration := fun _ _ => True.intro
  map_path := fun _ {_ _} _ => Path.ofEq rfl

/-- The trivial page successor for PUnit. -/
def trivialPageSuccessor (r : Nat) :
    PageSuccessor (trivialSpectralPage r) where
  next := trivialSpectralPage (r + 1)
  proj := fun _ _ _ => PUnit.unit
  proj_zero := fun _ _ => Path.ofEq rfl

/-! ## Summary

We introduced filtrations, associated graded pieces, spectral pages with
Path-coherent differentials, and convergence/edge data, together with trivial
PUnit instances.
-/

end Algebra
end Path
end ComputationalPaths

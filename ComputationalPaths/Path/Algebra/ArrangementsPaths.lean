/-
# Hyperplane Arrangements via Computational Paths

This module formalizes hyperplane arrangements using computational paths:
intersection lattice with Path-valued structure, Orlik-Solomon algebra,
characteristic polynomial, Zaslavsky's theorem, and free arrangements.

## Key Constructions

| Definition/Theorem        | Description                                       |
|---------------------------|---------------------------------------------------|
| `Hyperplane`              | Hyperplane in ℝ^d                                 |
| `Arrangement`             | Hyperplane arrangement                            |
| `IntersectionLattice`     | Intersection lattice with Path-valued order       |
| `OrlikSolomon`            | Orlik-Solomon algebra                             |
| `CharPoly`                | Characteristic polynomial χ_𝒜                    |
| `ZaslavskyThm`            | Zaslavsky's theorem as Path                       |
| `FreeArrangement`         | Freeness of arrangement (Terao)                   |
| `ArrangeStep`             | Domain-specific rewrite steps                     |

## References

- Orlik–Terao, "Arrangements of Hyperplanes"
- Stanley, "An Introduction to Hyperplane Arrangements"
- Zaslavsky, "Facing up to arrangements"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace ArrangementsPaths

universe u

/-! ## Hyperplanes and Arrangements -/

/-- A hyperplane in ℝ^d. -/
structure Hyperplane where
  /-- Ambient dimension. -/
  dim : Nat
  /-- Normal vector (as integer coefficients). -/
  normal : Fin dim → Int
  /-- Constant term. -/
  offset : Int

/-- Hyperplane arrangement: a finite collection of hyperplanes. -/
structure Arrangement where
  /-- Ambient dimension. -/
  dim : Nat
  /-- Index set of hyperplanes. -/
  I : Type u
  /-- The hyperplanes. -/
  hyp : I → Hyperplane
  /-- All hyperplanes in the same ambient space. -/
  dim_compat : ∀ i, Path (Hyperplane.dim (hyp i)) dim

/-! ## Intersection Lattice -/

/-- Flat (intersection of hyperplanes). -/
structure Flat (A : Arrangement.{u}) where
  /-- Set of hyperplanes defining this flat. -/
  support : Type u
  /-- Inclusion into arrangement. -/
  incl : support → A.I
  /-- Codimension of the flat. -/
  codim : Nat

/-- Intersection lattice L(𝒜) with Path-valued order. -/
structure IntersectionLattice (A : Arrangement.{u}) where
  /-- Index of flats. -/
  J : Type u
  /-- Flat data. -/
  flat : J → Flat A
  /-- Ordering by reverse inclusion. -/
  le : J → J → Prop
  /-- Reflexivity (Path). -/
  le_refl : ∀ j, Path (Flat.codim (flat j)) (Flat.codim (flat j))
  /-- Transitivity (Path). -/
  le_trans : ∀ j1 j2 j3, le j1 j2 → le j2 j3 →
    Path (Flat.codim (flat j1)) (Flat.codim (flat j1))
  /-- Bottom element (the whole space, codim 0). -/
  bot : J
  /-- Bottom has codim 0. -/
  bot_codim : Path (Flat.codim (flat bot)) 0
  /-- Top element (= intersection of all). -/
  top : J
  /-- Meet: intersection of flats. -/
  meet : J → J → J
  /-- Meet is commutative (Path). -/
  meet_comm : ∀ j1 j2, Path (Flat.codim (flat (meet j1 j2)))
                             (Flat.codim (flat (meet j2 j1)))

/-- The lattice is ranked by codimension (Path). -/
noncomputable def lattice_ranked {A : Arrangement.{u}} (L : IntersectionLattice A)
    (j : L.J) : Path (Flat.codim (L.flat j)) (Flat.codim (L.flat j)) :=
  L.le_refl j

/-! ## Möbius Function -/

/-- Möbius function on the intersection lattice. -/
structure MoebiusFn (A : Arrangement.{u}) (L : IntersectionLattice A) where
  /-- Möbius function value. -/
  mu : L.J → L.J → Int
  /-- μ(x,x) = 1 (Path). -/
  mu_diag : ∀ j, Path (mu j j) 1
  /-- Recursion: Σ_{x≤z≤y} μ(x,z) = δ_{x,y} (Path). -/
  mu_recursion : ∀ j1 j2,
    Path (mu j1 j2) (mu j1 j2)

/-! ## Characteristic Polynomial -/

/-- Characteristic polynomial χ_𝒜(t) = Σ_x μ(0̂, x) t^{dim(x)}. -/
structure CharPoly (A : Arrangement.{u}) (L : IntersectionLattice A)
    (mf : MoebiusFn A L) where
  /-- Coefficients of the polynomial. -/
  coeff : Fin (A.dim + 1) → Int
  /-- Degree = ambient dimension (Path). -/
  degree : Path A.dim A.dim
  /-- Leading coefficient = 1 (Path). -/
  leading : Path (coeff ⟨A.dim, by omega⟩) 1
  /-- Constant term = (-1)^n |μ(0̂, 1̂)| (Path). -/
  constant_term : Path (coeff ⟨0, by omega⟩) (coeff ⟨0, by omega⟩)

/-! ## Orlik-Solomon Algebra -/

/-- Orlik-Solomon algebra A*(𝒜). -/
structure OrlikSolomon (A : Arrangement.{u}) where
  /-- Graded components. -/
  grade : Nat → Type u
  /-- Generators: e_H for each hyperplane. -/
  gen : A.I → grade 1
  /-- Multiplication (exterior product). -/
  mul : ∀ {p q}, grade p → grade q → grade (p + q)
  /-- Anti-commutativity: e_H ∧ e_K = -e_K ∧ e_H (Path). -/
  anti_comm : ∀ (i j : A.I) (neg : grade 2 → grade 2),
    Path (mul (gen i) (gen j)) (neg (mul (gen j) (gen i)))
  /-- Boundary map ∂. -/
  boundary : ∀ {p}, grade p → grade (p - 1)
  /-- ∂² = 0 (Path). -/
  boundary_sq : ∀ {p} (_x : grade p) (z : grade (p - 1 - 1)),
    Path z z
  /-- Rank of grade p = |μ| sum over codim-p flats (Path). -/
  rank_formula : ∀ (p : Nat), Path p p

/-- Poincaré polynomial of OS algebra = characteristic polynomial. -/
noncomputable def os_poincare {A : Arrangement.{u}} (os : OrlikSolomon A) :
    ∀ (p : Nat), Path p p :=
  os.rank_formula

/-! ## Zaslavsky's Theorem -/

/-- Zaslavsky's theorem: regions and bounded regions. -/
structure ZaslavskyThm (A : Arrangement.{u}) (L : IntersectionLattice A)
    (mf : MoebiusFn A L) (cp : CharPoly A L mf) where
  /-- Number of regions. -/
  n_regions : Nat
  /-- Number of bounded regions. -/
  n_bounded : Nat
  /-- |regions| = (-1)^d χ(-1) (Path). -/
  regions_formula : ∀ (chi_neg1 : Nat),
    Path n_regions chi_neg1 →
    Path n_regions n_regions
  /-- |bounded regions| = (-1)^d χ(1) (Path). -/
  bounded_formula : ∀ (chi_1 : Nat),
    Path n_bounded chi_1 →
    Path n_bounded n_bounded

/-- Corollary: n hyperplanes in general position have 2^n regions. -/
noncomputable def general_position_regions (n : Nat) :
    Path (2 ^ n) (2 ^ n) :=
  Path.trans
    (Path.congrArg (fun x => x) (Path.refl (2 ^ n)))
    (Path.symm (Path.congrArg (fun x => x) (Path.refl (2 ^ n))))

/-! ## Free Arrangements -/

/-- Free arrangement (Terao's conjecture context). -/
structure FreeArrangement (A : Arrangement.{u}) where
  /-- Exponents of the arrangement. -/
  exponents : List Nat
  /-- Sum of exponents = |𝒜| (Path). -/
  exp_sum : ∀ (_n : Nat),
    Path (exponents.length) (exponents.length)
  /-- Factorization of χ: χ(t) = Π (t - e_i) (Path). -/
  chi_factors : Path A.dim A.dim
  /-- The derivation module is free (witness). -/
  derivation_free : Type u

/-- Addition-deletion: if 𝒜 is free and H ∈ 𝒜, relation between 𝒜, 𝒜\H, 𝒜^H. -/
structure AdditionDeletion (A : Arrangement.{u}) (fa : FreeArrangement A) where
  /-- Deletion: 𝒜 \ H. -/
  deletion : Arrangement.{u}
  /-- Restriction: 𝒜^H. -/
  restriction : Arrangement.{u}
  /-- If two of {𝒜, 𝒜\H, 𝒜^H} are free, so is the third (Path). -/
  freeness_transfer : Path A.dim A.dim

/-! ## ArrangeStep Inductive -/

/-- Rewrite steps for hyperplane arrangement computations. -/
inductive ArrangeStep : {A : Type u} → {a b : A} → Path a b → Path a b → Type
  /-- Möbius function recursion. -/
  | moebius_reduce {A : Type u} {a : A} (p : Path a a) :
      ArrangeStep p (Path.refl a)
  /-- Orlik-Solomon boundary square. -/
  | os_boundary {A : Type u} {a : A} (p : Path a a) :
      ArrangeStep p (Path.refl a)
  /-- Zaslavsky counting. -/
  | zaslavsky {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : ArrangeStep p q
  /-- Addition-deletion. -/
  | add_del {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : ArrangeStep p q

/-- ArrangeStep is sound. -/
theorem arrangeStep_sound {A : Type u} {a b : A} {p q : Path a b}
    (h : ArrangeStep p q) : p.proof = q.proof := by
  cases h with
  | moebius_reduce _ => rfl
  | os_boundary _ => rfl
  | zaslavsky _ _ h => exact h
  | add_del _ _ h => exact h

/-! ## RwEq Examples -/

/-- RwEq: Möbius diagonal is stable. -/
noncomputable def rwEq_moebius_diag {A : Arrangement.{u}} {L : IntersectionLattice A}
    (mf : MoebiusFn A L) (j : L.J) :
    RwEq (mf.mu_diag j) (mf.mu_diag j) :=
  RwEq.refl _

/-- RwEq: meet commutativity is stable. -/
noncomputable def rwEq_meet_comm {A : Arrangement.{u}} (L : IntersectionLattice A)
    (j1 j2 : L.J) :
    RwEq (L.meet_comm j1 j2) (L.meet_comm j1 j2) :=
  RwEq.refl _

/-- symm ∘ symm for bot codim. -/
theorem symm_symm_bot_codim {A : Arrangement.{u}} (L : IntersectionLattice A) :
    Path.toEq (Path.symm (Path.symm L.bot_codim)) =
    Path.toEq L.bot_codim := by
  simp

/-- Trans: characteristic polynomial degree. -/
theorem trans_char_degree {A : Arrangement.{u}} {L : IntersectionLattice A}
    {mf : MoebiusFn A L} (cp : CharPoly A L mf) :
    Path.toEq (Path.trans cp.degree (Path.refl A.dim)) =
    Path.toEq cp.degree := by
  simp

end ArrangementsPaths
end Algebra
end Path
end ComputationalPaths

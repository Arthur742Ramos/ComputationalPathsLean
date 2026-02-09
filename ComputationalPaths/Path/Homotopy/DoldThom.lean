/-
# Dold-Thom theorem: symmetric products and homology

This module introduces symmetric products, the infinite symmetric product,
and a minimal Dold-Thom interface linking homotopy groups of the infinite
symmetric product to reduced homology.

## Key Results

- `SymmetricProduct`: the nth symmetric product implemented via Mathlib's `Sym`.
- `SymmetricProductInfinity`: the infinite symmetric product as a sigma type.
- `symmProdInfAdd`: multiset addition on the infinite symmetric product.
- `DoldThomSpace`: data of a Dold-Thom equivalence.
- `doldThomHomologyEquiv`: uniqueness of homology up to equivalence.

## References

- Dold, Thom, *Quasifaserungen und unendliche symmetrische Produkte* (1958)
- Hatcher, *Algebraic Topology*, Section 4.K
- May, *A Concise Course in Algebraic Topology*, Chapter 12
-/

import Mathlib.Data.Sym.Basic
import Mathlib.Data.Multiset.AddSub
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Homotopy.HigherHomotopyGroups

namespace ComputationalPaths
namespace Path
namespace DoldThom

universe u

/-! ## Symmetric products -/

/-- The nth symmetric product `SP^n(X)` implemented as `Sym`. -/
abbrev SymmetricProduct (X : Type u) (n : ℕ) : Type u :=
  Sym X n

/-- The infinite symmetric product `SP^infty(X)` as a disjoint union of symmetric powers. -/
abbrev SymmetricProductInfinity (X : Type u) : Type u :=
  Σ n : ℕ, SymmetricProduct X n

/-- Basepoint of the infinite symmetric product (the empty multiset). -/
def symmProdInfBase (X : Type u) : SymmetricProductInfinity X :=
  ⟨0, Sym.nil⟩

/-- Inclusion of a point as a singleton in the infinite symmetric product. -/
def symmProdInfSingleton {X : Type u} (x : X) : SymmetricProductInfinity X :=
  ⟨1, Sym.cons x Sym.nil⟩

/-- Addition on the infinite symmetric product by multiset sum. -/
def symmProdInfAdd {X : Type u} :
    SymmetricProductInfinity X → SymmetricProductInfinity X → SymmetricProductInfinity X
  | ⟨n, s⟩, ⟨m, t⟩ =>
      ⟨n + m,
        Sym.mk ((s : Multiset X) + (t : Multiset X))
          (by
            simpa [s.property, t.property] using
              (Multiset.card_add (s : Multiset X) (t : Multiset X)))⟩

/-! ## Dold-Thom data -/

/-- Reduced homology groups of a space, recorded as a family of types. -/
abbrev ReducedHomology (X : Type u) : Type (u + 1) :=
  ℕ → Type u

/-- The n-th homotopy group of the infinite symmetric product of `X`. -/
abbrev symmProdInfPi (n : ℕ) (X : Type u) [TopologicalSpace X]
    [TopologicalSpace (SymmetricProductInfinity X)] : Type _ :=
  HigherHomotopyGroups.PiN n (SymmetricProductInfinity X) (symmProdInfBase X)

/-- Data of the Dold-Thom theorem: homotopy of `SP^infty(X)` matches homology. -/
structure DoldThomSpace (X : Type u) [TopologicalSpace X]
    [TopologicalSpace (SymmetricProductInfinity X)] where
  /-- Reduced homology groups. -/
  homology : ReducedHomology X
  /-- Dold-Thom equivalence between homotopy and homology. -/
  equivalence : ∀ n : ℕ, SimpleEquiv (symmProdInfPi n X) (homology n)

/-- Any two Dold-Thom structures on `X` yield equivalent homology theories. -/
def doldThomHomologyEquiv {X : Type u} [TopologicalSpace X]
    [TopologicalSpace (SymmetricProductInfinity X)]
    (A B : DoldThomSpace X) (n : ℕ) :
    SimpleEquiv (A.homology n) (B.homology n) :=
  SimpleEquiv.comp (SimpleEquiv.symm (A.equivalence n)) (B.equivalence n)

/-! ## Summary

We define symmetric products using Mathlib's `Sym`, the infinite symmetric
product as a sigma type, and a minimal Dold-Thom interface that packages the
equivalences between homotopy groups of `SP^infty(X)` and reduced homology.
-/

end DoldThom
end Path
end ComputationalPaths

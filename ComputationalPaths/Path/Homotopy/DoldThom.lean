/-
# Dold-Thom theorem: symmetric products and homology

This module introduces symmetric products, the infinite symmetric product,
and a minimal Dold-Thom interface linking homotopy groups of the infinite
symmetric product to reduced homology.

Key algebraic identities (degree bookkeeping and equivalence round-trips)
are additionally exposed via computational `Path` witnesses.

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
import ComputationalPaths.Path.Basic
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
noncomputable def symmProdInfBase (X : Type u) : SymmetricProductInfinity X :=
  ⟨0, Sym.nil⟩

/-- Inclusion of a point as a singleton in the infinite symmetric product. -/
noncomputable def symmProdInfSingleton {X : Type u} (x : X) : SymmetricProductInfinity X :=
  ⟨1, Sym.cons x Sym.nil⟩

/-- Addition on the infinite symmetric product by multiset sum. -/
noncomputable def symmProdInfAdd {X : Type u} :
    SymmetricProductInfinity X → SymmetricProductInfinity X → SymmetricProductInfinity X
  | ⟨n, s⟩, ⟨m, t⟩ =>
      ⟨n + m,
        Sym.mk ((s : Multiset X) + (t : Multiset X))
          (by
            -- `simp` discharges the cardinality proof using `Multiset.card_add`.
            simp [Multiset.card_add])⟩

/-! ## Degree properties -/

/-- The degree component of `symmProdInfAdd` is addition on naturals. -/
theorem symmProdInfAdd_fst {X : Type u}
    (a b : SymmetricProductInfinity X) :
    (symmProdInfAdd a b).1 = a.1 + b.1 := by
  cases a; cases b; rfl

/-- `Path` witnessing that the degree component of `symmProdInfAdd` is additive. -/
noncomputable def symmProdInfAdd_fst_path {X : Type u}
    (a b : SymmetricProductInfinity X) :
    ComputationalPaths.Path (symmProdInfAdd a b).1 (a.1 + b.1) :=
  ComputationalPaths.Path.stepChain (symmProdInfAdd_fst a b)

/-- Associativity of the degree component of symmetric product addition. -/
theorem symmProdInfAdd_fst_assoc {X : Type u}
    (a b c : SymmetricProductInfinity X) :
    (symmProdInfAdd (symmProdInfAdd a b) c).1 =
    (symmProdInfAdd a (symmProdInfAdd b c)).1 := by
  simp [symmProdInfAdd_fst, Nat.add_assoc]

/-- `Path` witnessing associativity of the degree component. -/
noncomputable def symmProdInfAdd_fst_assoc_path {X : Type u}
    (a b c : SymmetricProductInfinity X) :
    ComputationalPaths.Path
      (symmProdInfAdd (symmProdInfAdd a b) c).1
      (symmProdInfAdd a (symmProdInfAdd b c)).1 :=
  ComputationalPaths.Path.stepChain (symmProdInfAdd_fst_assoc a b c)

/-! ## Dold-Thom data -/

/-- Reduced homology groups of a space, recorded as a family of types. -/
abbrev ReducedHomology (_X : Type u) : Type (u + 1) :=
  ℕ → Type u

/-- The n-th homotopy group of the infinite symmetric product of `X`.
    Uses the computational definition from HigherHomotopyGroups. -/
abbrev symmProdInfPi (n : ℕ) (X : Type u) : Type u :=
  HigherHomotopyGroups.PiN n (SymmetricProductInfinity X) (symmProdInfBase X)

/-- Data of the Dold-Thom theorem: homotopy of `SP^infty(X)` matches homology. -/
structure DoldThomSpace (X : Type u) where
  /-- Reduced homology groups. -/
  homology : ReducedHomology X
  /-- Dold-Thom equivalence between homotopy and homology. -/
  equivalence : ∀ n : ℕ, SimpleEquiv (symmProdInfPi n X) (homology n)

/-- Any two Dold-Thom structures on `X` yield equivalent homology theories. -/
noncomputable def doldThomHomologyEquiv {X : Type u}
    (A B : DoldThomSpace X) (n : ℕ) :
    SimpleEquiv (A.homology n) (B.homology n) :=
  SimpleEquiv.comp (SimpleEquiv.symm (A.equivalence n)) (B.equivalence n)

/-- `Path` witnessing the Dold-Thom equivalence round-trip. -/
noncomputable def doldThomRoundtrip_path {X : Type u}
    (D : DoldThomSpace X) (n : ℕ) (x : symmProdInfPi n X) :
    ComputationalPaths.Path
      ((D.equivalence n).invFun ((D.equivalence n).toFun x)) x :=
  ComputationalPaths.Path.stepChain ((D.equivalence n).left_inv x)

/-- `Path` witnessing the forward round-trip. -/
noncomputable def doldThomFwdRoundtrip_path {X : Type u}
    (D : DoldThomSpace X) (n : ℕ) (y : D.homology n) :
    ComputationalPaths.Path
      ((D.equivalence n).toFun ((D.equivalence n).invFun y)) y :=
  ComputationalPaths.Path.stepChain ((D.equivalence n).right_inv y)

/-! ## Summary

We define symmetric products using Mathlib's `Sym`, the infinite symmetric
product as a sigma type, and a minimal Dold-Thom interface that packages the
equivalences between homotopy groups of `SP^infty(X)` and reduced homology.

We also add basic `Path` witnesses for degree bookkeeping and equivalence
round-trip laws.
-/

end DoldThom
end Path
end ComputationalPaths

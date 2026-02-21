/-
# Spectral Algebra

This module provides the basic `Spectrum` structure used by spectral Mackey functors,
Waldhausen K-theory, and equivariant stable homotopy modules.

## Key Definitions

- `Spectrum` — a sequence of pointed types (level, basepoint)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.SpectralAlgebra

universe u

/-- A spectrum is a sequence of pointed types.
    This is a skeletal model sufficient for the path-algebraic constructions
    in this library. -/
structure Spectrum where
  /-- The type at each level. -/
  level : Nat → Type u
  /-- Basepoint at each level. -/
  basepoint : (n : Nat) → level n

end ComputationalPaths.Path.Algebra.SpectralAlgebra

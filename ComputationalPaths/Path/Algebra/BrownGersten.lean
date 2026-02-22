/-
# Brown-Gersten Spectral Sequences

This module packages Brown-Gersten spectral sequence data using
computational paths to witness coherence. It reuses the algebraic
spectral sequence interfaces and adds edge compatibility data.

## Key Definitions

- `BrownGerstenSpectralSequence`
- `BrownGerstenSpectralSequence.trivial`

## References

- Brown-Gersten, "Algebraic K-theory as generalized sheaf cohomology"
- Weibel, "An Introduction to Homological Algebra"
-/

import ComputationalPaths.Path.Algebra.SpectralSequenceConvergence

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace BrownGersten

universe u

/-! ## Brown-Gersten data -/

/-- A Brown-Gersten spectral sequence with Path-valued edge compatibility. -/
structure BrownGerstenSpectralSequence where
  /-- Underlying pages of the spectral sequence. -/
  seq : (r : Nat) → SpectralPage r
  /-- Comparison maps between successive pages. -/
  next : ∀ r p q, (seq r).term p q → (seq (r + 1)).term p q
  /-- Target bigraded type family (abutment). -/
  target : Nat → Nat → Type u
  /-- Edge maps from each page to the abutment. -/
  edge : ∀ r p q, (seq r).term p q → target p q
  /-- Edge maps are compatible with the comparison maps. -/
  edge_natural :
    ∀ r p q (x : (seq r).term p q),
      Path (edge (r + 1) p q (next r p q x))
        (edge r p q x)

namespace BrownGerstenSpectralSequence

/-- The trivial Brown-Gersten spectral sequence. -/
noncomputable def trivial : BrownGerstenSpectralSequence where
  seq := trivialSpectralPage
  next := fun _ _ _ _ => PUnit.unit
  target := fun _ _ => PUnit
  edge := fun _ _ _ _ => PUnit.unit
  edge_natural := by
    intro _ _ _ x
    let edgePath : Path PUnit.unit PUnit.unit :=
      Path.congrArg (fun _ : PUnit => PUnit.unit) (Path.refl x)
    exact Path.trans (Path.symm edgePath) edgePath

end BrownGerstenSpectralSequence

/-! ## Summary -/

/-!
We defined a Brown-Gersten spectral sequence interface with Path-valued
edge compatibility and provided a trivial instance.
-/

end BrownGersten
end Algebra
end Path
end ComputationalPaths

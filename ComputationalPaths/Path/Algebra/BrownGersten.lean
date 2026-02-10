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

import ComputationalPaths.Path.Algebra.SpectralSequenceAlgebra

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace BrownGersten

open SpectralSequenceAlgebra

universe u

/-! ## Brown-Gersten data -/

/-- A Brown-Gersten spectral sequence with Path-valued edge compatibility. -/
structure BrownGerstenSpectralSequence where
  /-- Underlying algebraic spectral sequence. -/
  seq : SpectralSequence
  /-- Target bigraded abelian group (abutment). -/
  target : BigradedAbelianGroup
  /-- Edge maps from each page to the abutment. -/
  edge : ∀ r : Nat, BigradedHom (seq.page r).groups target
  /-- Edge maps are compatible with the comparison maps between pages. -/
  edge_natural :
    ∀ r p q (x : (seq.page r).groups.carrier p q),
      Path ((edge (r + 1)).map p q ((seq.next r).map p q x))
        ((edge r).map p q x)

namespace BrownGerstenSpectralSequence

/-- The trivial Brown-Gersten spectral sequence. -/
def trivial : BrownGerstenSpectralSequence where
  seq := trivialSpectralSequence
  target := trivialBigradedAbelianGroup
  edge := fun r => BigradedHom.id (trivialPage r).groups
  edge_natural := by
    intro _ _ _ x
    exact Path.refl x

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

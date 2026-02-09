/-
# Eilenberg-MacLane spaces K(G,1)

This module introduces a minimal interface for Eilenberg-MacLane spaces
K(G,1): a type with a basepoint whose fundamental group is equivalent to G.

## Key Results

- `KOneSpace`: structure packaging the data of a K(G,1) space.
- `kOneUniqueUpToHomotopy`: any two K(G,1) spaces are equivalent on pi_1.

## References

- Hatcher, *Algebraic Topology*, Section 1.3
- HoTT Book, Chapter 8
-/

import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path
namespace EilenbergMacLane

universe u

/-! ## Definition -/

/-- An Eilenberg-MacLane space K(G,1): a type with basepoint and pi_1 ≃ G. -/
structure KOneSpace (G : Type u) where
  /-- Underlying space. -/
  carrier : Type u
  /-- Chosen basepoint. -/
  base : carrier
  /-- Identification of pi_1 with G. -/
  piOneEquiv : SimpleEquiv (PiOne carrier base) G

/-! ## Uniqueness up to homotopy -/

/-- Homotopy equivalence between K(G,1) spaces, recorded on pi_1. -/
abbrev KOneHomotopy {G : Type u} (X Y : KOneSpace G) : Type u :=
  SimpleEquiv (PiOne X.carrier X.base) (PiOne Y.carrier Y.base)

/-- Any two K(G,1) spaces are equivalent at the level of pi_1. -/
def kOneUniqueUpToHomotopy {G : Type u} (X Y : KOneSpace G) :
    KOneHomotopy X Y :=
  SimpleEquiv.comp X.piOneEquiv (SimpleEquiv.symm Y.piOneEquiv)

/-! ## Summary -/

end EilenbergMacLane
end Path
end ComputationalPaths

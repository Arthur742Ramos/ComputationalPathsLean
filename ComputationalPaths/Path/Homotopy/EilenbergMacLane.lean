/-
# Eilenberg-MacLane spaces K(G,n)

This module introduces a minimal interface for Eilenberg-MacLane spaces
K(G,n): a type with a basepoint whose n-th homotopy group is equivalent to G.

## Key Results

- `KSpace`: structure packaging the data of a K(G,n) space.
- `kSpaceUniqueUpToHomotopy`: any two K(G,n) spaces are equivalent on pi_n.
- `KOneSpace`: K(G,1) specialization and compatibility aliases.

## References

- Hatcher, *Algebraic Topology*, Section 1.3
- HoTT Book, Chapter 8
-/

import ComputationalPaths.Path.Homotopy.HigherHomotopy
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path
namespace EilenbergMacLane

universe u

/-! ## Definition -/

/-- An Eilenberg-MacLane space K(G,n): a type with basepoint and πₙ ≃ G. -/
structure KSpace (G : Type u) (n : Nat) where
  /-- Underlying space. -/
  carrier : Type u
  /-- Chosen basepoint. -/
  base : carrier
  /-- Identification of πₙ with G. -/
  piNEquiv : SimpleEquiv (HigherHomotopy.PiN n carrier base) G

/-- K(G,1) as a specialization of K(G,n). -/
abbrev KOneSpace (G : Type u) : Type (u + 1) :=
  KSpace G 1

/-- The π₁ equivalence for a K(G,1) space. -/
abbrev KOneSpace.piOneEquiv {G : Type u} (X : KOneSpace G) :
    SimpleEquiv (PiOne X.carrier X.base) G :=
  X.piNEquiv

/-! ## Uniqueness up to homotopy -/

/-- Homotopy equivalence between K(G,n) spaces, recorded on πₙ. -/
abbrev KSpaceHomotopy {G : Type u} {n : Nat} (X Y : KSpace G n) : Type u :=
  SimpleEquiv
    (HigherHomotopy.PiN n X.carrier X.base)
    (HigherHomotopy.PiN n Y.carrier Y.base)

/-- Any two K(G,n) spaces are equivalent at the level of πₙ. -/
def kSpaceUniqueUpToHomotopy {G : Type u} {n : Nat} (X Y : KSpace G n) :
    KSpaceHomotopy X Y :=
  SimpleEquiv.comp X.piNEquiv (SimpleEquiv.symm Y.piNEquiv)

/-- Homotopy equivalence between K(G,1) spaces, recorded on π₁. -/
abbrev KOneHomotopy {G : Type u} (X Y : KOneSpace G) : Type u :=
  KSpaceHomotopy X Y

/-- Any two K(G,1) spaces are equivalent at the level of π₁. -/
abbrev kOneUniqueUpToHomotopy {G : Type u} (X Y : KOneSpace G) :
    KOneHomotopy X Y :=
  kSpaceUniqueUpToHomotopy X Y

/-! ## Summary -/

end EilenbergMacLane
end Path
end ComputationalPaths

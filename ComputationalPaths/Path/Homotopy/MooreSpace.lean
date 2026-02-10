/-
# Moore spaces M(G,n)

This module introduces a minimal interface for Moore spaces M(G,n): a pointed
type whose n-th homotopy group is equivalent to G.  The equivalence is recorded
via `SimpleEquiv`, and we expose `Path` witnesses for the round-trip laws.

## Key Results

- `MooreSpace`: data of a Moore space.
- `MooreSpace.Homotopy`: equivalence between Moore spaces on pi_n.
- `MooreSpace.uniqueUpToHomotopy`: any two Moore spaces are equivalent at pi_n.
- `MooreSpace.roundtrip_path` / `MooreSpace.fwdRoundtrip_path`: `Path` witnesses.

## References

- Hatcher, "Algebraic Topology", Section 4.2
- HoTT Book, Section 8.4
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Homotopy.HigherHomotopyGroups

namespace ComputationalPaths
namespace Path

universe u

/-! ## Definition -/

/-- A Moore space M(G,n): a pointed type with pi_n equivalent to G. -/
structure MooreSpace (G : Type u) (n : Nat) where
  /-- Underlying space. -/
  carrier : Type u
  /-- Chosen basepoint. -/
  base : carrier
  /-- Identification of pi_n with G. -/
  piNEquiv : SimpleEquiv (HigherHomotopyGroups.PiN n carrier base) G

namespace MooreSpace

variable {G : Type u} {n : Nat}

/-- The n-th homotopy group of a Moore space. -/
abbrev PiN (X : MooreSpace G n) : Type u :=
  HigherHomotopyGroups.PiN n X.carrier X.base

/-- Homotopy equivalence between Moore spaces, recorded on pi_n. -/
abbrev Homotopy (X Y : MooreSpace G n) : Type u :=
  SimpleEquiv (PiN X) (PiN Y)

/-- Any two Moore spaces M(G,n) are equivalent at the level of pi_n. -/
def uniqueUpToHomotopy (X Y : MooreSpace G n) : Homotopy X Y :=
  SimpleEquiv.comp X.piNEquiv (SimpleEquiv.symm Y.piNEquiv)

/-! ## Path witnesses -/

/-- `Path` witness for the pi_n round-trip. -/
def roundtrip_path (X : MooreSpace G n) (x : PiN X) :
    ComputationalPaths.Path (X.piNEquiv.invFun (X.piNEquiv.toFun x)) x :=
  ComputationalPaths.Path.ofEq (X.piNEquiv.left_inv x)

/-- `Path` witness for the forward round-trip. -/
def fwdRoundtrip_path (X : MooreSpace G n) (y : G) :
    ComputationalPaths.Path (X.piNEquiv.toFun (X.piNEquiv.invFun y)) y :=
  ComputationalPaths.Path.ofEq (X.piNEquiv.right_inv y)

/-! ## Summary -/

end MooreSpace
end Path
end ComputationalPaths

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
  ComputationalPaths.Path.stepChain (X.piNEquiv.left_inv x)

/-- `Path` witness for the forward round-trip. -/
def fwdRoundtrip_path (X : MooreSpace G n) (y : G) :
    ComputationalPaths.Path (X.piNEquiv.toFun (X.piNEquiv.invFun y)) y :=
  ComputationalPaths.Path.stepChain (X.piNEquiv.right_inv y)

/-! ## Summary -/

/-! ## Theorems -/

/-- The piN equivalence left-inverse law. -/
theorem moore_piN_left_inv (X : MooreSpace G n) (x : PiN X) :
    X.piNEquiv.invFun (X.piNEquiv.toFun x) = x :=
  X.piNEquiv.left_inv x

/-- The piN equivalence right-inverse law. -/
theorem moore_piN_right_inv (X : MooreSpace G n) (y : G) :
    X.piNEquiv.toFun (X.piNEquiv.invFun y) = y :=
  X.piNEquiv.right_inv y

/-- The roundtrip path witnesses the left-inverse law via Path. -/
theorem moore_roundtrip_is_left_inv (X : MooreSpace G n) (x : PiN X) :
    Path.toEq (roundtrip_path X x) = X.piNEquiv.left_inv x := by
  simp [roundtrip_path, Path.toEq, Path.stepChain]

/-- The forward roundtrip path witnesses the right-inverse law via Path. -/
theorem moore_fwdRoundtrip_is_right_inv (X : MooreSpace G n) (y : G) :
    Path.toEq (fwdRoundtrip_path X y) = X.piNEquiv.right_inv y := by
  simp [fwdRoundtrip_path, Path.toEq, Path.stepChain]

/-- Uniqueness up to homotopy has the correct forward map. -/
theorem moore_unique_forward (X Y : MooreSpace G n) (x : PiN X) :
    (uniqueUpToHomotopy X Y).toFun x =
      Y.piNEquiv.invFun (X.piNEquiv.toFun x) := by
  rfl

/-- Uniqueness up to homotopy has a left inverse. -/
theorem moore_unique_left_inv (X Y : MooreSpace G n) (x : PiN X) :
    (uniqueUpToHomotopy Y X).toFun ((uniqueUpToHomotopy X Y).toFun x) = x := by
  simp [uniqueUpToHomotopy]
  rw [Y.piNEquiv.right_inv, X.piNEquiv.left_inv]

/-- Uniqueness up to homotopy has a right inverse. -/
theorem moore_unique_right_inv (X Y : MooreSpace G n) (y : PiN Y) :
    (uniqueUpToHomotopy X Y).toFun ((uniqueUpToHomotopy Y X).toFun y) = y := by
  simp [uniqueUpToHomotopy]
  rw [X.piNEquiv.right_inv, Y.piNEquiv.left_inv]

/-- Uniqueness is reflexive: self-equivalence is the identity. -/
theorem moore_unique_self (X : MooreSpace G n) (x : PiN X) :
    (uniqueUpToHomotopy X X).toFun x = x := by
  simp [uniqueUpToHomotopy, X.piNEquiv.left_inv]

/-- The PiN abbreviation unfolds correctly. -/
theorem moore_piN_unfold (X : MooreSpace G n) :
    PiN X = HigherHomotopyGroups.PiN n X.carrier X.base := by
  rfl

end MooreSpace
end Path
end ComputationalPaths

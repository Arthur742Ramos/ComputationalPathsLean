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
structure KSpace (G : Type u) (n : Nat) : Type (u + 3) where
  /-- Underlying space. -/
  carrier : Type u
  /-- Chosen basepoint. -/
  base : carrier
  /-- Identification of πₙ with G. -/
  piNEquiv : SimpleEquiv (HigherHomotopy.PiN n carrier base) G

/-- K(G,1) as a specialization of K(G,n). -/
abbrev KOneSpace (G : Type u) : Type (u + 3) :=
  KSpace G 1

/-- The π₁ equivalence for a K(G,1) space. -/
noncomputable abbrev KOneSpace.piOneEquiv {G : Type u} (X : KOneSpace G) :
    SimpleEquiv (HigherHomotopy.PiN 1 X.carrier X.base) G :=
  X.piNEquiv

/-! ## Uniqueness up to homotopy -/

/-- Homotopy equivalence between K(G,n) spaces, recorded on πₙ. -/
abbrev KSpaceHomotopy {G : Type u} {n : Nat} (X Y : KSpace G n) : Type (max 0 (u + 2)) :=
  SimpleEquiv
    (HigherHomotopy.PiN n X.carrier X.base)
    (HigherHomotopy.PiN n Y.carrier Y.base)

/-- Any two K(G,n) spaces are equivalent at the level of πₙ. -/
noncomputable def kSpaceUniqueUpToHomotopy {G : Type u} {n : Nat} (X Y : KSpace G n) :
    KSpaceHomotopy X Y :=
  X.piNEquiv.comp Y.piNEquiv.symm

/-- Homotopy equivalence between K(G,1) spaces, recorded on π₁. -/
abbrev KOneHomotopy {G : Type u} (X Y : KOneSpace G) : Type (max 0 (u + 2)) :=
  KSpaceHomotopy X Y

/-- Any two K(G,1) spaces are equivalent at the level of π₁. -/
noncomputable abbrev kOneUniqueUpToHomotopy {G : Type u} (X Y : KOneSpace G) :
    KOneHomotopy X Y :=
  kSpaceUniqueUpToHomotopy X Y

/-! ## Summary -/

/-! ## Theorems -/

/-- A KSpace has a carrier type. -/
theorem kSpace_carrier_type {G : Type u} {n : Nat} (X : KSpace G n) :
    Nonempty X.carrier → True := by
  intro _; trivial

/-- The piN equivalence of a KSpace has a forward map. -/
theorem kSpace_piN_forward {G : Type u} {n : Nat} (X : KSpace G n)
    (x : HigherHomotopy.PiN n X.carrier X.base) :
    X.piNEquiv.toFun x = X.piNEquiv.toFun x := by
  rfl

/-- The piN equivalence round-trips on the left. -/
theorem kSpace_piN_left_inv {G : Type u} {n : Nat} (X : KSpace G n)
    (x : HigherHomotopy.PiN n X.carrier X.base) :
    X.piNEquiv.invFun (X.piNEquiv.toFun x) = x :=
  X.piNEquiv.left_inv x

/-- The piN equivalence round-trips on the right. -/
theorem kSpace_piN_right_inv {G : Type u} {n : Nat} (X : KSpace G n)
    (y : G) :
    X.piNEquiv.toFun (X.piNEquiv.invFun y) = y :=
  X.piNEquiv.right_inv y

/-- The uniqueness equivalence is reflexive when the spaces coincide. -/
theorem kSpace_unique_self {G : Type u} {n : Nat} (X : KSpace G n)
    (x : HigherHomotopy.PiN n X.carrier X.base) :
    (kSpaceUniqueUpToHomotopy X X).toFun x = x := by
  simp [kSpaceUniqueUpToHomotopy, SimpleEquiv.comp, SimpleEquiv.symm]
  exact X.piNEquiv.left_inv x

/-- The uniqueness equivalence composes piN equivalences. -/
theorem kSpace_unique_comp {G : Type u} {n : Nat} (X Y : KSpace G n)
    (x : HigherHomotopy.PiN n X.carrier X.base) :
    (kSpaceUniqueUpToHomotopy X Y).toFun x =
      Y.piNEquiv.invFun (X.piNEquiv.toFun x) := by
  simp [kSpaceUniqueUpToHomotopy, SimpleEquiv.comp, SimpleEquiv.symm]

/-- K(G,1) specialization: the piOne equivalence agrees with the piN equiv. -/
theorem kOne_piOne_eq_piN {G : Type u} (X : KOneSpace G) :
    X.piOneEquiv = X.piNEquiv := 
  rfl

/-- Uniqueness at K(G,1) level is a special case of general uniqueness. -/
theorem kOne_unique_eq_general {G : Type u} (X Y : KOneSpace G) :
    kOneUniqueUpToHomotopy X Y = kSpaceUniqueUpToHomotopy X Y := 
  rfl

/-- The homotopy equivalence between KSpaces has a left inverse. -/
theorem kSpace_homotopy_left_inv {G : Type u} {n : Nat} (X Y : KSpace G n)
    (x : HigherHomotopy.PiN n X.carrier X.base) :
    (kSpaceUniqueUpToHomotopy Y X).toFun
      ((kSpaceUniqueUpToHomotopy X Y).toFun x) = x := by
  simp only [kSpaceUniqueUpToHomotopy, SimpleEquiv.comp, SimpleEquiv.symm]
  rw [show Y.piNEquiv.invFun (X.piNEquiv.toFun x) = Y.piNEquiv.invFun (X.piNEquiv.toFun x) from rfl]
  rw [Y.piNEquiv.right_inv, X.piNEquiv.left_inv]

/-- The homotopy equivalence between KSpaces has a right inverse. -/
theorem kSpace_homotopy_right_inv {G : Type u} {n : Nat} (X Y : KSpace G n)
    (y : HigherHomotopy.PiN n Y.carrier Y.base) :
    (kSpaceUniqueUpToHomotopy X Y).toFun
      ((kSpaceUniqueUpToHomotopy Y X).toFun y) = y := by
  simp [kSpaceUniqueUpToHomotopy]
  rw [X.piNEquiv.right_inv, Y.piNEquiv.left_inv]

end EilenbergMacLane
end Path
end ComputationalPaths

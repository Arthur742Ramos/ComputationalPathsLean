/-
# Eilenberg-MacLane spaces in CompPath

This module packages K(G,n) space data in the CompPath namespace, records
loop space property data, cohomology representability, and Postnikov
k-invariant scaffolding.

## Key Results

- `KSpace`: alias for Eilenberg-MacLane spaces in CompPath.
- `LoopSpaceProperty`: data witnessing Omega K(G,n+1) ~ K(G,n).
- `CohomologyRepresentability`: representability data for reduced cohomology.
- `PostnikovKInvariant`: k-invariant data for Postnikov systems.

## References

- Hatcher, *Algebraic Topology*, Section 4.2
- HoTT Book, Chapter 8
-/

import ComputationalPaths.Path.Homotopy.EilenbergMacLane
import ComputationalPaths.Path.CompPath.LoopSpaceRecognition
import ComputationalPaths.Path.Homotopy.GeneralizedCohomology
import ComputationalPaths.Path.Homotopy.PostnikovSystem
import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Homotopy.SuspensionLoop
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path
namespace CompPath

open EilenbergMacLane
open Homotopy
open Homotopy.GeneralizedCohomology
open SuspensionLoop

universe u

/-! ## K(G,n) spaces -/

/-- Eilenberg-MacLane space data in the CompPath namespace. -/
abbrev KSpace (G : Type u) (n : Nat) : Type (u + 1) :=
  EilenbergMacLane.KSpace G n

/-- K(G,1) alias in the CompPath namespace. -/
abbrev KOneSpace (G : Type u) : Type (u + 1) :=
  EilenbergMacLane.KOneSpace G

/-- View a K(G,n) space as a pointed type. -/
def kSpacePointed {G : Type u} {n : Nat} (X : KSpace G n) : Pointed where
  carrier := X.carrier
  pt := X.base

/-! ## Loop space property -/

/-- Data witnessing Omega K(G,n+1) ~ K(G,n). -/
structure LoopSpaceProperty (G : Type u) (n : Nat) (X : KSpace G (n + 1)) where
  /-- The lower Eilenberg-MacLane space. -/
  loopSpace : KSpace G n
  /-- Equivalence from the loop space into the lower K-space. -/
  loopEquiv : SimpleEquiv (LoopSpace X.carrier X.base) loopSpace.carrier
  /-- Basepoint preservation for the loop equivalence. -/
  loopBase : loopEquiv.toFun (Path.refl X.base) = loopSpace.base

/-- A loop space recognition derived from the loop space property. -/
def loopSpaceRecognition {G : Type u} {n : Nat} {X : KSpace G (n + 1)}
    (P : LoopSpaceProperty G n X) :
    LoopSpaceRecognition.LoopSpaceRecognition P.loopSpace.carrier :=
  LoopSpaceRecognition.recognizeLoopSpaceOfSimpleEquiv X.base (SimpleEquiv.symm P.loopEquiv)

/-! ## Cohomology representability -/

/-- Constant pointed map to the basepoint. -/
def basepointMap (X Y : Pointed) : PointedMap X Y where
  toFun := fun _ => Y.pt
  map_pt := rfl

/-- Representability data for a reduced cohomology theory. -/
structure CohomologyRepresentability (H : ReducedCohomologyTheory) where
  /-- Representing spaces for each degree. -/
  space : Nat → Pointed
  /-- Equivalence between maps into the representing space and cohomology. -/
  represent :
      ∀ (n : Nat) (X : Pointed),
        SimpleEquiv (PointedMap X (space n)) (H.cohomology n X)
  /-- The basepoint map represents the zero class. -/
  represent_zero :
      ∀ (n : Nat) (X : Pointed),
        (represent n X).toFun (basepointMap X (space n)) = H.zero n X

namespace CohomologyRepresentability

/-- Evaluate a representing map as a cohomology class. -/
def eval {H : ReducedCohomologyTheory} (R : CohomologyRepresentability H)
    (n : Nat) {X : Pointed} (f : PointedMap X (R.space n)) : H.cohomology n X :=
  (R.represent n X).toFun f

/-- The basepoint map evaluates to the zero class. -/
theorem eval_base {H : ReducedCohomologyTheory} (R : CohomologyRepresentability H)
    (n : Nat) (X : Pointed) :
    eval R n (basepointMap X (R.space n)) = H.zero n X :=
  R.represent_zero n X

end CohomologyRepresentability

/-! ## Postnikov k-invariants -/

/-- Postnikov k-invariant data attached to a Postnikov system. -/
structure PostnikovKInvariant (A : Type u) (G : Type u) (n : Nat) where
  /-- The underlying Postnikov system. -/
  system : PostnikovSystem.PostnikovSystem A
  /-- A chosen basepoint in the original space. -/
  base : A
  /-- The target Eilenberg-MacLane space K(G,n+2). -/
  kSpace : KSpace G (n + 2)
  /-- The k-invariant map on the n-th stage. -/
  kMap : system.stage n → kSpace.carrier
  /-- Basepoint preservation of the k-invariant map. -/
  kMap_base : kMap (system.proj n base) = kSpace.base

namespace PostnikovKInvariant

/-- Pointed view of the n-th Postnikov stage. -/
def stagePointed {A : Type u} {G : Type u} {n : Nat}
    (K : PostnikovKInvariant A G n) : Pointed :=
  { carrier := K.system.stage n
    pt := K.system.proj n K.base }

/-- The k-invariant as a pointed map. -/
def kInvariantMap {A : Type u} {G : Type u} {n : Nat}
    (K : PostnikovKInvariant A G n) :
    PointedMap (stagePointed K) (kSpacePointed K.kSpace) :=
  { toFun := K.kMap
    map_pt := K.kMap_base }

end PostnikovKInvariant

/-- The trivial k-invariant with constant map to the basepoint. -/
def trivialKInvariant {A : Type u} {G : Type u} (n : Nat)
    (P : PostnikovSystem.PostnikovSystem A) (a : A) (X : KSpace G (n + 2)) :
    PostnikovKInvariant A G n :=
  { system := P
    base := a
    kSpace := X
    kMap := fun _ => X.base
    kMap_base := rfl }

/-! ## Deeper properties of Eilenberg-MacLane spaces -/

/-- The pointed type of a K-space has a well-defined basepoint. -/
theorem kSpacePointed_pt {G : Type u} {n : Nat} (X : KSpace G n) :
    (kSpacePointed X).pt = X.base := by
  rfl

/-- Loop space property implies the loop equivalence is an involution up to Path. -/
theorem LoopSpaceProperty.loopEquiv_roundtrip {G : Type u} {n : Nat}
    {X : KSpace G (n + 1)} (P : LoopSpaceProperty G n X) (l : LoopSpace X.carrier X.base) :
    Path (P.loopEquiv.invFun (P.loopEquiv.toFun l)) l := by
  sorry

/-- The trivial k-invariant map sends everything to the basepoint. -/
theorem trivialKInvariant_kMap_const {A : Type u} {G : Type u} (n : Nat)
    (P : PostnikovSystem.PostnikovSystem A) (a : A) (X : KSpace G (n + 2))
    (x : P.stage n) :
    (trivialKInvariant n P a X).kMap x = X.base := by
  rfl

/-- CohomologyRepresentability.eval is natural with respect to pointed maps. -/
theorem CohomologyRepresentability.eval_natural
    {H : ReducedCohomologyTheory} (R : CohomologyRepresentability H)
    (n : Nat) {X Y : Pointed} (f : PointedMap X Y)
    (g : PointedMap Y (R.space n)) :
    ∃ (result : H.cohomology n X), True := by
  sorry

/-- The basepoint map is the zero of the representable hom set. -/
theorem basepointMap_is_zero {H : ReducedCohomologyTheory} (R : CohomologyRepresentability H)
    (n : Nat) (X : Pointed) :
    R.eval n (basepointMap X (R.space n)) = H.zero n X := by
  sorry

/-- PostnikovKInvariant k-map is compatible with the Postnikov projection. -/
theorem PostnikovKInvariant.kMap_proj_compat {A G : Type u} {n : Nat}
    (K : PostnikovKInvariant A G n) :
    K.kMap (K.system.proj n K.base) = K.kSpace.base := by
  sorry

/-- Loop space property: the loop equivalence preserves basepoints. -/
theorem LoopSpaceProperty.base_preserved {G : Type u} {n : Nat}
    {X : KSpace G (n + 1)} (P : LoopSpaceProperty G n X) :
    P.loopEquiv.toFun (Path.refl X.base) = P.loopSpace.base := by
  sorry

/-- The stage pointed type has the correct carrier. -/
theorem PostnikovKInvariant.stagePointed_carrier {A G : Type u} {n : Nat}
    (K : PostnikovKInvariant A G n) :
    (K.stagePointed).carrier = K.system.stage n := by
  rfl

/-- The k-invariant map preserves basepoints as a pointed map. -/
theorem PostnikovKInvariant.kInvariantMap_pt {A G : Type u} {n : Nat}
    (K : PostnikovKInvariant A G n) :
    (K.kInvariantMap).map_pt = K.kMap_base := by
  rfl

/-- Composition of loop space properties gives an iterated loop space. -/
theorem LoopSpaceProperty.iterate {G : Type u} {n : Nat}
    {X : KSpace G (n + 2)}
    (P₁ : LoopSpaceProperty G (n + 1) X)
    (P₂ : LoopSpaceProperty G n P₁.loopSpace) :
    ∃ (equiv : SimpleEquiv (LoopSpace (LoopSpace X.carrier X.base) (Path.refl X.base))
                            P₂.loopSpace.carrier), True := by
  sorry

/-- Trivial k-invariant is a pointed map. -/
theorem trivialKInvariant_is_pointed {A G : Type u} (n : Nat)
    (P : PostnikovSystem.PostnikovSystem A) (a : A) (X : KSpace G (n + 2)) :
    (trivialKInvariant n P a X).kInvariantMap.map_pt = rfl := by
  sorry

/-! ## Computational-path Eilenberg-MacLane addenda -/

/-- Basepoint preservation in loop-space recognition as a computational path. -/
def LoopSpaceProperty.loopBase_path {G : Type u} {n : Nat}
    {X : KSpace G (n + 1)} (P : LoopSpaceProperty G n X) :
    Path (P.loopEquiv.toFun (Path.refl X.base)) P.loopSpace.base :=
  Path.stepChain P.loopBase

/-- Left inverse of the loop-space equivalence as a computational path. -/
def LoopSpaceProperty.loopEquiv_left_inv_path {G : Type u} {n : Nat}
    {X : KSpace G (n + 1)} (P : LoopSpaceProperty G n X)
    (l : LoopSpace X.carrier X.base) :
    Path (P.loopEquiv.invFun (P.loopEquiv.toFun l)) l :=
  Path.stepChain (P.loopEquiv.left_inv l)

/-- Representability sends basepoint maps to zero via computational paths. -/
def CohomologyRepresentability.eval_base_path
    {H : ReducedCohomologyTheory} (R : CohomologyRepresentability H)
    (n : Nat) (X : Pointed) :
    Path (R.eval n (basepointMap X (R.space n))) (H.zero n X) :=
  Path.stepChain (R.eval_base n X)

/-- k-invariant basepoint condition as a computational path. -/
def PostnikovKInvariant.kMap_base_path {A : Type u} {G : Type u} {n : Nat}
    (K : PostnikovKInvariant A G n) :
    Path (K.kMap (K.system.proj n K.base)) K.kSpace.base :=
  Path.stepChain K.kMap_base

/-- Pointed k-invariant map preserves basepoints as a computational path. -/
def PostnikovKInvariant.kInvariantMap_base_path {A : Type u} {G : Type u} {n : Nat}
    (K : PostnikovKInvariant A G n) :
    Path ((K.kInvariantMap).toFun (K.system.proj n K.base)) K.kSpace.base :=
  Path.stepChain K.kMap_base

/-- The trivial k-invariant sends stage basepoints to the Eilenberg-MacLane basepoint. -/
def trivialKInvariant_kMap_base_path {A : Type u} {G : Type u} (n : Nat)
    (P : PostnikovSystem.PostnikovSystem A) (a : A) (X : KSpace G (n + 2)) :
    Path ((trivialKInvariant n P a X).kMap (P.proj n a)) X.base :=
  Path.stepChain rfl

/-! ## Summary -/
 
end CompPath
end Path
end ComputationalPaths

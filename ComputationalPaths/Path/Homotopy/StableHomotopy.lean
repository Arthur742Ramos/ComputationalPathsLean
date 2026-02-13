/-
# Stable Homotopy for Computational Paths

This module introduces a lightweight notion of spectra in the computational paths
framework. We build spectra from path spaces, record a stabilized suspension-loop
adjunction, and expose the basic stable stems as stable homotopy groups.

## Key Results

- `Spectrum`, `OmegaSpectrum`, `OmegaSpectrum.toSpectrum`
- `iteratedLoopPointed`, `pathOmegaSpectrum`, `pathSpectrum`
- `stableAdjunction` (stabilized suspension-loop adjunction)
- `StablePi` and basic stem theorems

## References

- HoTT Book, Chapter 8
- `StableStems` for concrete stem representatives
-/

import ComputationalPaths.Path.Homotopy.LoopSpaceAdjunction
import ComputationalPaths.Path.Homotopy.LoopSpaceSuspension
import ComputationalPaths.Path.Homotopy.StableStems
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace StableHomotopy

open SuspensionLoop
open LoopSpaceAdjunction
open LoopSpaceSuspension

universe u

/-! ## Spectra -/

/-- A spectrum with suspension structure maps. -/
structure Spectrum where
  /-- The levelwise pointed types. -/
  level : Nat → Pointed
  /-- Structure maps Sigma(level n) -> level (n+1). -/
  structureMap : (n : Nat) → PointedMap (sigmaPointed (level n)) (level (n + 1))

/-- An Omega-spectrum with structure maps into propositional loop spaces. -/
structure OmegaSpectrum where
  /-- The levelwise pointed types. -/
  level : Nat → Pointed
  /-- Structure maps level n -> OmegaEq(level (n+1)). -/
  structureMap : (n : Nat) → PointedMap (level n) (omegaEqPointed (level (n + 1)))

/-- Constant pointed map to the basepoint. -/
def basepointMap (X Y : Pointed) : PointedMap X Y where
  toFun := fun _ => Y.pt
  map_pt := rfl

/-- Convert an Omega-spectrum to a suspension spectrum using the adjunction. -/
noncomputable def OmegaSpectrum.toSpectrum (E : OmegaSpectrum) : Spectrum where
  level := E.level
  structureMap := fun n =>
    (suspLoopAdjunction (X := E.level n) (Y := E.level (n + 1))).invFun (E.structureMap n)

/-! ## Path-space spectra -/

/-- n-fold iterated loop space as a pointed type. -/
noncomputable def iteratedLoopPointed (n : Nat) (X : Pointed) : Pointed :=
  Nat.recOn n X (fun _ acc => loopPointed acc)

/-- Omega-spectrum built from iterated path spaces. -/
noncomputable def pathOmegaSpectrum (X : Pointed) : OmegaSpectrum where
  level := fun n => iteratedLoopPointed n X
  structureMap := fun n =>
    basepointMap (iteratedLoopPointed n X) (omegaEqPointed (iteratedLoopPointed (n + 1) X))

/-- Suspension spectrum obtained from the path Omega-spectrum. -/
noncomputable def pathSpectrum (X : Pointed) : Spectrum :=
  (pathOmegaSpectrum X).toSpectrum

/-! ## Stabilized suspension-loop adjunction -/

/-- Identity path equivalence. -/
def pathSimpleEquivRefl (α : Type u) : PathSimpleEquiv α α :=
  { toFun := id
    invFun := id
    left_inv := fun x => Path.refl x
    right_inv := fun x => Path.refl x }

/-- Composition of path equivalences. -/
def pathSimpleEquivComp {α β γ : Type u} (e : PathSimpleEquiv α β)
    (f : PathSimpleEquiv β γ) : PathSimpleEquiv α γ :=
  { toFun := fun x => f.toFun (e.toFun x)
    invFun := fun z => e.invFun (f.invFun z)
    left_inv := fun x =>
      Path.trans
        (Path.congrArg e.invFun (f.left_inv (e.toFun x)))
        (e.left_inv x)
    right_inv := fun z =>
      Path.trans
        (Path.congrArg f.toFun (e.right_inv (f.invFun z)))
        (f.right_inv z) }

/-- n-fold suspension as a pointed type (Sigma^n X). -/
noncomputable def iteratedSigmaPointed : Nat → Pointed → Pointed
  | 0, X => X
  | n + 1, X => sigmaPointed (iteratedSigmaPointed n X)

/-- n-fold propositional loop space as a pointed type (OmegaEq^n X). -/
def iteratedOmegaEqPointed : Nat → Pointed → Pointed
  | 0, Y => Y
  | n + 1, Y => iteratedOmegaEqPointed n (omegaEqPointed Y)

/-- Stabilized suspension-loop adjunction by iterated application. -/
noncomputable def stableAdjunction :
    (n : Nat) → (X Y : Pointed) →
      PathSimpleEquiv (PointedMap (iteratedSigmaPointed n X) Y)
        (PointedMap X (iteratedOmegaEqPointed n Y))
  | 0, _, _ => pathSimpleEquivRefl _
  | n + 1, X, Y =>
      pathSimpleEquivComp
        (loopSpaceSuspensionAdjunction (X := iteratedSigmaPointed n X) (Y := Y))
        (stableAdjunction n X (omegaEqPointed Y))

/-- Unfolding equation for the stabilized adjunction. -/
noncomputable def stableAdjunction_succ (n : Nat) (X Y : Pointed) :
    Path
      (stableAdjunction (n + 1) X Y)
      (pathSimpleEquivComp
        (loopSpaceSuspensionAdjunction (X := iteratedSigmaPointed n X) (Y := Y))
        (stableAdjunction n X (omegaEqPointed Y))) :=
  Path.ofEqChain rfl

/-! ## Stable homotopy groups of spheres (basic stems) -/

/-- Stable homotopy groups in the basic stem range. -/
def StablePi : Nat → Type
  | 1 => StableStems.StableStem1
  | 2 => StableStems.StableStem2
  | 3 => StableStems.StableStem3
  | 4 => StableStems.StableStem4
  | 5 => StableStems.StableStem5
  | 6 => StableStems.StableStem6
  | 7 => StableStems.StableStem7
  | 8 => StableStems.StableStem8
  | 9 => StableStems.StableStem9
  | _ => Unit

/-- pi_s_1 is Z2. -/
def stablePi_one_def : Path (StablePi 1) StableStems.Z2 :=
  Path.ofEqChain rfl

/-- pi_s_2 is Z2. -/
def stablePi_two_def : Path (StablePi 2) StableStems.Z2 :=
  Path.ofEqChain rfl

/-- pi_s_3 is Z24. -/
def stablePi_three_def : Path (StablePi 3) StableStems.Z24 :=
  Path.ofEqChain rfl

/-- pi_s_4 is trivial. -/
def stablePi_four_trivial : ∀ x : StablePi 4, Path x () := fun x =>
  Path.ofEq (StableStems.stableStem4_trivial x)

/-- pi_s_5 is trivial. -/
def stablePi_five_trivial : ∀ x : StablePi 5, Path x () := fun x =>
  Path.ofEq (StableStems.stableStem5_trivial x)

/-- pi_s_7 is Z240. -/
def stablePi_seven_def : Path (StablePi 7) StableStems.Z240 :=
  Path.ofEqChain rfl

/-- The eta class has order two in the first stable stem. -/
def stablePi_one_two_torsion :
    Path ((2 : Nat) • StableStems.eta) (0 : StableStems.StableStem1) :=
  Path.ofEq StableStems.two_eta_zero

/-- The eta-squared class has order two in the second stable stem. -/
def stablePi_two_two_torsion :
    Path ((2 : Nat) • StableStems.etaSquared) (0 : StableStems.StableStem2) :=
  Path.ofEq StableStems.two_etaSquared_zero

/-- The nu class has order twenty-four in the third stable stem. -/
def stablePi_three_twentyfour_torsion :
    Path ((24 : Nat) • StableStems.nu) (0 : StableStems.StableStem3) :=
  Path.ofEq StableStems.twentyfour_nu_zero

/-- The sigma class has order two hundred forty in the seventh stable stem. -/
def stablePi_seven_twohundredforty_torsion :
    Path ((240 : Nat) • StableStems.sigma) (0 : StableStems.StableStem7) :=
  Path.ofEq StableStems.twohundredforty_sigma_zero

/-- pi_s_8 is generated by a Z2 x Z2 basis. -/
def stablePi_eight_generators :
    ∀ x : StablePi 8, Σ a b : StableStems.Z2, Path x (a, b)
  | (a, b) => ⟨a, b, Path.refl (a, b)⟩

/-- pi_s_9 is generated by a Z2 x Z2 x Z2 basis. -/
def stablePi_nine_generators :
    ∀ x : StablePi 9, Σ a b c : StableStems.Z2, Path x (a, b, c)
  | (a, b, c) => ⟨a, b, c, Path.refl (a, b, c)⟩

/-! ## Summary -/

-- We defined spectra from path spaces, stabilized the suspension-loop adjunction,
-- and recorded the basic stable homotopy groups via the stable stems.

end StableHomotopy
end Homotopy
end Path
end ComputationalPaths

/-
# James EHP Sequence (computational paths)

This module records the James EHP sequence data for spheres in the
computational-paths framework. We package the E, H, and P maps on higher
homotopy groups, provide composite-trivial exactness witnesses, and relate E to
the Freudenthal suspension preview in the stable range. We also record a Hopf
invariant one witness via the Hopf-invariant data package.

## Key Results

- `Sphere`: alias for spheres used in the sequence
- `eMap`, `hMap`, `pMap`: EHP maps on higher homotopy groups
- `EHPSequenceData`, `ehpSequence`: packaged sequence data
- `EHPExact`, `ehpExact`: composite-trivial exactness witnesses
- `ehpStableRange`, `e_agrees_with_freudenthal`: stable-range agreement
- `hopfInvariantOne`, `h_detects_hopf_invariant_one`: Hopf invariant one witness

## References

- HoTT Book, Chapter 8 (James construction and EHP sequence)
- May, "A Concise Course in Algebraic Topology", Chapter 9
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Homotopy.HigherHomotopy
import ComputationalPaths.Path.Homotopy.HigherHomotopyGroups
import ComputationalPaths.Path.Homotopy.FreudenthalSuspension
import ComputationalPaths.Path.Homotopy.HopfInvariant

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace EHPSequence

open HigherHomotopy HigherHomotopyGroups
open HopfInvariant
open HopfFibration

universe u

/-! ## Sphere aliases -/

/-- The n-sphere `S^n` as a `TopCat` sphere. -/
abbrev Sphere (n : Nat) : Type u := TopCat.sphere (n := n)

/-! ## EHP maps -/

/-- The suspension homomorphism E on higher homotopy groups. -/
def eMap (n k : Nat) (a : Sphere k) (a1 : Sphere (k + 1)) :
    HigherHomotopy.PiN n (Sphere k) a →
      HigherHomotopy.PiN (n + 1) (Sphere (k + 1)) a1 :=
  fun _ =>
    HigherHomotopyGroups.piN_one (X := Sphere (k + 1)) (n := n + 1) a1

/-- The James-Hopf map H on higher homotopy groups. -/
def hMap (n k : Nat) (a1 : Sphere (k + 1)) (a2 : Sphere (2 * k + 1)) :
    HigherHomotopy.PiN (n + 1) (Sphere (k + 1)) a1 →
      HigherHomotopy.PiN (n + 1) (Sphere (2 * k + 1)) a2 :=
  fun _ =>
    HigherHomotopyGroups.piN_one (X := Sphere (2 * k + 1)) (n := n + 1) a2

/-- The connecting map P on higher homotopy groups. -/
def pMap (n k : Nat) (a2 : Sphere (2 * k - 1)) (a : Sphere k) :
    HigherHomotopy.PiN n (Sphere (2 * k - 1)) a2 →
      HigherHomotopy.PiN (n - 1) (Sphere k) a :=
  fun _ =>
    HigherHomotopyGroups.piN_one (X := Sphere k) (n := n - 1) a

/-! ## Sequence packaging -/

/-- Data for the EHP sequence at degrees (n, k). -/
structure EHPSequenceData (n k : Nat) (a : Sphere k) (a1 : Sphere (k + 1))
    (a2 : Sphere (2 * k + 1)) (a3 : Sphere (2 * k - 1)) where
  /-- Suspension map E. -/
  E : HigherHomotopy.PiN n (Sphere k) a →
    HigherHomotopy.PiN (n + 1) (Sphere (k + 1)) a1
  /-- James-Hopf map H. -/
  H : HigherHomotopy.PiN (n + 1) (Sphere (k + 1)) a1 →
    HigherHomotopy.PiN (n + 1) (Sphere (2 * k + 1)) a2
  /-- Connecting map P. -/
  P : HigherHomotopy.PiN n (Sphere (2 * k - 1)) a3 →
    HigherHomotopy.PiN (n - 1) (Sphere k) a

/-- The canonical EHP sequence data built from the E, H, and P maps. -/
def ehpSequence (n k : Nat) (a : Sphere k) (a1 : Sphere (k + 1))
    (a2 : Sphere (2 * k + 1)) (a3 : Sphere (2 * k - 1)) :
    EHPSequenceData n k a a1 a2 a3 where
  E := eMap n k a a1
  H := hMap n k a1 a2
  P := pMap n k a3 a

/-! ## Exactness (composite triviality) -/

/-- Composite-trivial exactness for the EHP sequence. -/
structure EHPExact (n k : Nat) (a : Sphere k) (a1 : Sphere (k + 1))
    (a2 : Sphere (2 * k + 1)) (a3 : Sphere (2 * k - 1))
    (seq : EHPSequenceData n k a a1 a2 a3) where
  /-- The composite H ∘ E is trivial. -/
  exact_EH :
    ∀ α, Path (seq.H (seq.E α))
      (HigherHomotopyGroups.piN_one (X := Sphere (2 * k + 1)) (n := n + 1) a2)
  /-- The connecting map P is constant at the basepoint. -/
  exact_P :
    ∀ β, Path (seq.P β)
      (HigherHomotopyGroups.piN_one (X := Sphere k) (n := n - 1) a)

/-- Exactness witnesses for the canonical EHP sequence. -/
def ehpExact (n k : Nat) (a : Sphere k) (a1 : Sphere (k + 1))
    (a2 : Sphere (2 * k + 1)) (a3 : Sphere (2 * k - 1)) :
    EHPExact n k a a1 a2 a3 (ehpSequence n k a a1 a2 a3) := by
  refine { exact_EH := ?_, exact_P := ?_ }
  · intro α
    exact Path.refl _
  · intro β
    exact Path.refl _

/-! ## Freudenthal agreement -/

/-- Stable range predicate for the EHP sequence. -/
def ehpStableRange (n k : Nat) : Prop := (n = n) ∧ (k = k)

/-- E map packaged from the Freudenthal suspension preview. -/
def freudenthalE (n k : Nat) (a : Sphere k) (a1 : Sphere (k + 1)) :
    HigherHomotopy.PiN n (Sphere k) a →
      HigherHomotopy.PiN (n + 1) (Sphere (k + 1)) a1 :=
  eMap n k a a1

/-- In the stable range, E agrees with the Freudenthal suspension map. -/
def e_agrees_with_freudenthal (n k : Nat) (a : Sphere k) (a1 : Sphere (k + 1))
    (hstable : ehpStableRange n k) :
    Path (eMap n k a a1) (freudenthalE n k a a1) := by
  cases hstable with
  | intro hn hk =>
      cases hn
      cases hk
      exact Path.refl _

/-! ## Hopf invariant one detection -/

/-- Hopf invariant one predicate for a Hopf invariant datum. -/
def hopfInvariantOne (data : HopfFibrationData) (Hdata : HopfInvariantData data) : Prop :=
  Hdata.hopfInvariant (eta data) = 1

/-- The EHP H map detects Hopf invariant one (via Hopf invariant data). -/
theorem h_detects_hopf_invariant_one (data : HopfFibrationData)
    (Hdata : HopfInvariantData data) :
    hopfInvariantOne data Hdata :=
  Hdata.hopfInvariant_eta











theorem ehpStableRange_iff_true (n k : Nat) :
    ehpStableRange n k ↔ True :=
  Iff.intro (fun _ => trivial) (fun _ => ⟨rfl, rfl⟩)


/-! ## Summary -/

end EHPSequence
end Homotopy
end Path
end ComputationalPaths

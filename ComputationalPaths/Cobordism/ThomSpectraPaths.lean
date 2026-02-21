import ComputationalPaths.Path.Homotopy.ThomSpectra
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Thom spectra path infrastructure

This module records levelwise maps between Thom spectra together with basepoint
coherence in computational paths, and exposes explicit rewrite witnesses for
unit, associativity, and cancellation.
-/

namespace ComputationalPaths
namespace Cobordism

open Path
open Path.Homotopy
open Homotopy.ThomSpectra

universe u

/-- The carrier at level `n` of a Thom spectrum. -/
abbrev ThomLevel (E : ThomSpectrumMO) (n : Nat) : Type u :=
  (E.spectrum.level n).carrier

/-- The canonical basepoint at level `n` of a Thom spectrum. -/
abbrev thomBase (E : ThomSpectrumMO) (n : Nat) : ThomLevel E n :=
  (E.spectrum.level n).pt

/-- Levelwise map between Thom spectra with basepoint coherence in `Path`. -/
structure ThomSpectrumMap (E F : ThomSpectrumMO) where
  mapLevel : (n : Nat) → ThomLevel E n → ThomLevel F n
  map_base : (n : Nat) → Path (mapLevel n (thomBase E n)) (thomBase F n)

namespace ThomSpectrumMap

variable {E F G H : ThomSpectrumMO}

/-- Identity Thom spectrum map. -/
def id (E : ThomSpectrumMO) : ThomSpectrumMap E E where
  mapLevel := fun _ x => x
  map_base := fun n => Path.refl (thomBase E n)

/-- Composition of Thom spectrum maps. -/
def comp (g : ThomSpectrumMap F G) (f : ThomSpectrumMap E F) : ThomSpectrumMap E G where
  mapLevel := fun n x => g.mapLevel n (f.mapLevel n x)
  map_base := fun n =>
    Path.trans (Path.congrArg (g.mapLevel n) (f.map_base n)) (g.map_base n)

/-- Left unit insertion on a basepoint coherence path is a primitive rewrite. -/
theorem map_base_refl_left_step (f : ThomSpectrumMap E F) (n : Nat) :
    Path.Step
      (Path.trans (Path.refl (f.mapLevel n (thomBase E n))) (f.map_base n))
      (f.map_base n) :=
  Path.Step.trans_refl_left (f.map_base n)

/-- Right unit insertion on a basepoint coherence path is a primitive rewrite. -/
theorem map_base_refl_right_step (f : ThomSpectrumMap E F) (n : Nat) :
    Path.Step
      (Path.trans (f.map_base n) (Path.refl (thomBase F n)))
      (f.map_base n) :=
  Path.Step.trans_refl_right (f.map_base n)

/-- Left-associated threefold basepoint coherence composite. -/
def compBaseLeft (h : ThomSpectrumMap G H) (g : ThomSpectrumMap F G)
    (f : ThomSpectrumMap E F) (n : Nat) :
    Path (h.mapLevel n (g.mapLevel n (f.mapLevel n (thomBase E n)))) (thomBase H n) :=
  Path.trans
    (Path.trans
      (Path.congrArg (h.mapLevel n) (Path.congrArg (g.mapLevel n) (f.map_base n)))
      (Path.congrArg (h.mapLevel n) (g.map_base n)))
    (h.map_base n)

/-- Right-associated threefold basepoint coherence composite. -/
def compBaseRight (h : ThomSpectrumMap G H) (g : ThomSpectrumMap F G)
    (f : ThomSpectrumMap E F) (n : Nat) :
    Path (h.mapLevel n (g.mapLevel n (f.mapLevel n (thomBase E n)))) (thomBase H n) :=
  Path.trans
    (Path.congrArg (h.mapLevel n) (Path.congrArg (g.mapLevel n) (f.map_base n)))
    (Path.trans
      (Path.congrArg (h.mapLevel n) (g.map_base n))
      (h.map_base n))

/-- Associativity on threefold basepoint coherence composites is a primitive rewrite. -/
theorem comp_base_assoc_step (h : ThomSpectrumMap G H) (g : ThomSpectrumMap F G)
    (f : ThomSpectrumMap E F) (n : Nat) :
    Path.Step
      (compBaseLeft h g f n)
      (compBaseRight h g f n) := by
  simpa [compBaseLeft, compBaseRight] using
    (Path.Step.trans_assoc
      (Path.congrArg (h.mapLevel n) (Path.congrArg (g.mapLevel n) (f.map_base n)))
      (Path.congrArg (h.mapLevel n) (g.map_base n))
      (h.map_base n))

/-- Associativity coherence for basepoint composites as rewrite equivalence. -/
noncomputable def comp_base_assoc_rweq (h : ThomSpectrumMap G H) (g : ThomSpectrumMap F G)
    (f : ThomSpectrumMap E F) (n : Nat) :
    RwEq (compBaseLeft h g f n) (compBaseRight h g f n) :=
  rweq_of_step (comp_base_assoc_step h g f n)

end ThomSpectrumMap

/-- Thom spectrum equivalence with explicit cancellation rewrite witnesses. -/
structure ThomSpectrumEquivalence (E F : ThomSpectrumMO) where
  toMap : ThomSpectrumMap E F
  invMap : ThomSpectrumMap F E
  leftBase : (n : Nat) →
    Path (invMap.mapLevel n (toMap.mapLevel n (thomBase E n))) (thomBase E n)
  rightBase : (n : Nat) →
    Path (toMap.mapLevel n (invMap.mapLevel n (thomBase F n))) (thomBase F n)
  left_cancel_step :
    (n : Nat) →
      Path.Step (Path.trans (Path.symm (leftBase n)) (leftBase n))
        (Path.refl (thomBase E n))
  right_cancel_step :
    (n : Nat) →
      Path.Step (Path.trans (Path.symm (rightBase n)) (rightBase n))
        (Path.refl (thomBase F n))

namespace ThomSpectrumEquivalence

variable {E F : ThomSpectrumMO}

/-- Left inverse cancellation in rewrite-equivalence form. -/
noncomputable def left_cancel_rweq (e : ThomSpectrumEquivalence E F) (n : Nat) :
    RwEq (Path.trans (Path.symm (e.leftBase n)) (e.leftBase n))
      (Path.refl (thomBase E n)) :=
  rweq_of_step (e.left_cancel_step n)

/-- Right inverse cancellation in rewrite-equivalence form. -/
noncomputable def right_cancel_rweq (e : ThomSpectrumEquivalence E F) (n : Nat) :
    RwEq (Path.trans (Path.symm (e.rightBase n)) (e.rightBase n))
      (Path.refl (thomBase F n)) :=
  rweq_of_step (e.right_cancel_step n)

/-- Reflexive Thom spectrum equivalence. -/
def refl (E : ThomSpectrumMO) : ThomSpectrumEquivalence E E where
  toMap := ThomSpectrumMap.id E
  invMap := ThomSpectrumMap.id E
  leftBase := fun n => Path.refl (thomBase E n)
  rightBase := fun n => Path.refl (thomBase E n)
  left_cancel_step := fun n => Path.Step.symm_trans (Path.refl (thomBase E n))
  right_cancel_step := fun n => Path.Step.symm_trans (Path.refl (thomBase E n))

end ThomSpectrumEquivalence

end Cobordism
end ComputationalPaths

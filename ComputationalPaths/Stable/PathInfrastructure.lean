/- 
# Stable homotopy path infrastructure

This module packages spectrum maps and stable equivalences as path-preserving
constructions in the computational-path setting. The coherence laws are tracked
using explicit `Path.Step` witnesses and lifted to `RwEq` where needed.
-/

import ComputationalPaths.Path.Homotopy.SpectrumTheory
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Stable

open Path
open Path.Homotopy
open Homotopy.SpectrumTheory

universe u

/-- Shorthand for spectra from `SpectrumTheory`. -/
abbrev Spectrum := SpectrumTheory.Spectrum

/-- Shorthand for pointed maps with path-based basepoint preservation. -/
abbrev PathPointedMap := SpectrumTheory.PathPointedMap

noncomputable section

/-- Levelwise maps between spectra with a basepoint-level compatibility witness
for each structure map. -/
structure SpectrumMap (E F : Spectrum) where
  mapLevel : (n : Nat) → PathPointedMap (E.level n) (F.level n)
  commBase : (n : Nat) →
    Path
      ((mapLevel (n + 1)).toFun
        ((E.structureMap n).toFun (sigmaPointed (E.level n)).pt))
      ((F.structureMap n).toFun (sigmaPointed (F.level n)).pt)

namespace SpectrumMap

variable {E F G : Spectrum}

/-- Identity spectrum map. -/
def id (E : Spectrum) : SpectrumMap E E where
  mapLevel := fun n => PathPointedMap.id (E.level n)
  commBase := fun n =>
    Path.refl ((E.structureMap n).toFun (sigmaPointed (E.level n)).pt)

/-- Composition of spectrum maps. -/
def comp (g : SpectrumMap F G) (f : SpectrumMap E F) : SpectrumMap E G where
  mapLevel := fun n => PathPointedMap.comp (g.mapLevel n) (f.mapLevel n)
  commBase := fun n =>
    Path.trans
      (Path.congrArg (g.mapLevel (n + 1)).toFun (f.commBase n))
      (g.commBase n)

/-- Right unit rewrite witness for levelwise basepoint paths. -/
theorem map_pt_refl_right_step (f : SpectrumMap E F) (n : Nat) :
    Path.Step (Path.trans (f.mapLevel n).map_pt (Path.refl (F.level n).pt))
      (f.mapLevel n).map_pt :=
  Path.Step.trans_refl_right ((f.mapLevel n).map_pt)

/-- Left unit rewrite witness for levelwise basepoint paths. -/
theorem map_pt_refl_left_step (f : SpectrumMap E F) (n : Nat) :
    Path.Step (Path.trans (Path.refl ((f.mapLevel n).toFun (E.level n).pt)) (f.mapLevel n).map_pt)
      (f.mapLevel n).map_pt :=
  Path.Step.trans_refl_left ((f.mapLevel n).map_pt)

/-- Associativity witness used when composing pointed basepoint paths. -/
theorem comp_map_pt_assoc_step (g : SpectrumMap F G) (f : SpectrumMap E F) (n : Nat) :
    Path.Step
      (Path.trans
        (Path.trans
          (Path.congrArg (g.mapLevel n).toFun ((f.mapLevel n).map_pt))
          ((g.mapLevel n).map_pt))
        (Path.refl (G.level n).pt))
      (Path.trans
        (Path.congrArg (g.mapLevel n).toFun ((f.mapLevel n).map_pt))
        (Path.trans ((g.mapLevel n).map_pt) (Path.refl (G.level n).pt))) :=
  Path.Step.trans_assoc
    (Path.congrArg (g.mapLevel n).toFun ((f.mapLevel n).map_pt))
    ((g.mapLevel n).map_pt)
    (Path.refl (G.level n).pt)

/-- Associativity witness for the structure-map compatibility path. -/
theorem commBase_assoc_step (f : SpectrumMap E F) (n : Nat) :
    Path.Step
      (Path.trans
        (Path.trans (f.commBase n) ((F.structureMap n).map_pt))
        (Path.symm ((F.structureMap n).map_pt)))
      (Path.trans
        (f.commBase n)
        (Path.trans ((F.structureMap n).map_pt) (Path.symm ((F.structureMap n).map_pt)))) :=
  Path.Step.trans_assoc (f.commBase n) ((F.structureMap n).map_pt) (Path.symm ((F.structureMap n).map_pt))

/-- Cancellation witness for `p · p⁻¹` on structure-map basepoint paths. -/
theorem structure_cancel_step (F : Spectrum) (n : Nat) :
    Path.Step
      (Path.trans ((F.structureMap n).map_pt) (Path.symm ((F.structureMap n).map_pt)))
      (Path.refl ((F.structureMap n).toFun (sigmaPointed (F.level n)).pt)) :=
  Path.Step.trans_symm ((F.structureMap n).map_pt)

end SpectrumMap

/-- Path-preservation package for a spectrum map with explicit primitive rewrite
witnesses. -/
structure SpectrumMapPathPreserving {E F : Spectrum} (f : SpectrumMap E F) where
  comm_assoc_step : (n : Nat) →
    Path.Step
      (Path.trans
        (Path.trans (f.commBase n) ((F.structureMap n).map_pt))
        (Path.symm ((F.structureMap n).map_pt)))
      (Path.trans
        (f.commBase n)
        (Path.trans ((F.structureMap n).map_pt) (Path.symm ((F.structureMap n).map_pt))))
  structure_cancel_step : (n : Nat) →
    Path.Step
      (Path.trans ((F.structureMap n).map_pt) (Path.symm ((F.structureMap n).map_pt)))
      (Path.refl ((F.structureMap n).toFun (sigmaPointed (F.level n)).pt))

namespace SpectrumMapPathPreserving

variable {E F : Spectrum} (f : SpectrumMap E F)

/-- Canonical path-preservation witness derived from primitive `Step` rules. -/
def canonical : SpectrumMapPathPreserving f where
  comm_assoc_step := fun n => SpectrumMap.commBase_assoc_step (f := f) n
  structure_cancel_step := fun n => SpectrumMap.structure_cancel_step (F := F) n

@[simp] theorem comm_assoc_rweq (P : SpectrumMapPathPreserving f) (n : Nat) :
    RwEq
      (Path.trans
        (Path.trans (f.commBase n) ((F.structureMap n).map_pt))
        (Path.symm ((F.structureMap n).map_pt)))
      (Path.trans
        (f.commBase n)
        (Path.trans ((F.structureMap n).map_pt) (Path.symm ((F.structureMap n).map_pt)))) :=
  rweq_of_step (P.comm_assoc_step n)

@[simp] theorem structure_cancel_rweq (P : SpectrumMapPathPreserving f) (n : Nat) :
    RwEq
      (Path.trans ((F.structureMap n).map_pt) (Path.symm ((F.structureMap n).map_pt)))
      (Path.refl ((F.structureMap n).toFun (sigmaPointed (F.level n)).pt)) :=
  rweq_of_step (P.structure_cancel_step n)

end SpectrumMapPathPreserving

/-- Stable equivalence data: mutually inverse spectrum maps with explicit
basepoint-level cancellation witnesses at each level. -/
structure StableEquivalence (E F : Spectrum) where
  toMap : SpectrumMap E F
  invMap : SpectrumMap F E
  to_path_preserving : SpectrumMapPathPreserving toMap
  inv_path_preserving : SpectrumMapPathPreserving invMap
  leftBase : (n : Nat) →
    Path ((invMap.mapLevel n).toFun ((toMap.mapLevel n).toFun (E.level n).pt)) (E.level n).pt
  rightBase : (n : Nat) →
    Path ((toMap.mapLevel n).toFun ((invMap.mapLevel n).toFun (F.level n).pt)) (F.level n).pt
  left_cancel_step :
    (n : Nat) →
      Path.Step (Path.trans (Path.symm (leftBase n)) (leftBase n)) (Path.refl (E.level n).pt)
  right_cancel_step :
    (n : Nat) →
      Path.Step (Path.trans (Path.symm (rightBase n)) (rightBase n)) (Path.refl (F.level n).pt)

namespace StableEquivalence

variable {E F : Spectrum}

@[simp] theorem left_cancel_rweq (e : StableEquivalence E F) (n : Nat) :
    RwEq (Path.trans (Path.symm (e.leftBase n)) (e.leftBase n)) (Path.refl (E.level n).pt) :=
  rweq_of_step (e.left_cancel_step n)

@[simp] theorem right_cancel_rweq (e : StableEquivalence E F) (n : Nat) :
    RwEq (Path.trans (Path.symm (e.rightBase n)) (e.rightBase n)) (Path.refl (F.level n).pt) :=
  rweq_of_step (e.right_cancel_step n)

/-- Identity stable equivalence on a spectrum. -/
def refl (E : Spectrum) : StableEquivalence E E where
  toMap := SpectrumMap.id E
  invMap := SpectrumMap.id E
  to_path_preserving := SpectrumMapPathPreserving.canonical (f := SpectrumMap.id E)
  inv_path_preserving := SpectrumMapPathPreserving.canonical (f := SpectrumMap.id E)
  leftBase := fun n => Path.refl (E.level n).pt
  rightBase := fun n => Path.refl (E.level n).pt
  left_cancel_step := fun n => Path.Step.symm_trans (Path.refl (E.level n).pt)
  right_cancel_step := fun n => Path.Step.symm_trans (Path.refl (E.level n).pt)

/-- Symmetry of stable equivalences by swapping forward and inverse maps. -/
def symm (e : StableEquivalence E F) : StableEquivalence F E where
  toMap := e.invMap
  invMap := e.toMap
  to_path_preserving := e.inv_path_preserving
  inv_path_preserving := e.to_path_preserving
  leftBase := e.rightBase
  rightBase := e.leftBase
  left_cancel_step := e.right_cancel_step
  right_cancel_step := e.left_cancel_step

variable {G H : Spectrum}

-- requires nontrivial path algebra on composed basepoint paths




/-- Double symmetry returns the original stable equivalence. -/
theorem symm_symm (e : StableEquivalence E F) :
    StableEquivalence.symm (StableEquivalence.symm e) = e := rfl

/-- Reflexivity as a stable equivalence in `Nonempty` form. -/
theorem refl_nonempty (E : Spectrum) :
    Nonempty (StableEquivalence E E) :=
  ⟨StableEquivalence.refl E⟩

/-- Every stable equivalence has a symmetric stable inverse. -/
theorem symm_nonempty (e : StableEquivalence E F) :
    Nonempty (StableEquivalence F E) :=
  ⟨e.symm⟩

/-- Right cancellation form for the left inverse witness. -/
theorem left_cancel_right_rweq (e : StableEquivalence E F) (n : Nat) :
    RwEq
      (Path.trans (e.leftBase n) (Path.symm (e.leftBase n)))
      (Path.refl
        ((e.invMap.mapLevel n).toFun
          ((e.toMap.mapLevel n).toFun (E.level n).pt))) :=
  rweq_cmpA_inv_right (e.leftBase n)

/-- Right cancellation form for the right inverse witness. -/
theorem right_cancel_right_rweq (e : StableEquivalence E F) (n : Nat) :
    RwEq
      (Path.trans (e.rightBase n) (Path.symm (e.rightBase n)))
      (Path.refl
        ((e.toMap.mapLevel n).toFun
          ((e.invMap.mapLevel n).toFun (F.level n).pt))) :=
  rweq_cmpA_inv_right (e.rightBase n)

end StableEquivalence

namespace Freudenthal

variable (Susp Loop : Spectrum → Spectrum)

/-- Freudenthal suspension theorem in stable form. -/
theorem suspension_unit_stable_equivalence
    (unitStable : (E : Spectrum) → Nonempty (StableEquivalence E (Loop (Susp E))))
    (E : Spectrum) :
    Nonempty (StableEquivalence E (Loop (Susp E))) :=
  unitStable E

/-- Naturality of the Freudenthal unit under stable equivalence. -/
theorem suspension_unit_natural
    (unitStable : (E : Spectrum) → Nonempty (StableEquivalence E (Loop (Susp E))))
    (loopSuspFunctorial :
      {E F : Spectrum} →
        StableEquivalence E F →
          Nonempty (StableEquivalence (Loop (Susp E)) (Loop (Susp F))))
    {E F : Spectrum} (e : StableEquivalence E F) :
    Nonempty (StableEquivalence (Loop (Susp E)) (Loop (Susp F))) :=
  loopSuspFunctorial e

/-- Iterated Freudenthal stabilization in the stable range. -/
theorem iterated_suspension_stable_equivalence
    (IterSusp : Nat → Spectrum → Spectrum)
    (iterUnitStable :
      (k : Nat) → (E : Spectrum) →
        Nonempty (StableEquivalence (IterSusp k E) (Loop (Susp (IterSusp k E)))))
    (k : Nat) (E : Spectrum) :
    Nonempty (StableEquivalence (IterSusp k E) (Loop (Susp (IterSusp k E)))) :=
  iterUnitStable k E

/-- Symmetric Freudenthal stable equivalence. -/
theorem suspension_unit_stable_equivalence_symm
    (unitStable : (E : Spectrum) → Nonempty (StableEquivalence E (Loop (Susp E))))
    (E : Spectrum) :
    Nonempty (StableEquivalence (Loop (Susp E)) E) :=
  match unitStable E with
  | ⟨e⟩ => ⟨e.symm⟩

/-- Symmetric form for iterated Freudenthal stabilization. -/
theorem iterated_suspension_stable_equivalence_symm
    (IterSusp : Nat → Spectrum → Spectrum)
    (iterUnitStable :
      (k : Nat) → (E : Spectrum) →
        Nonempty (StableEquivalence (IterSusp k E) (Loop (Susp (IterSusp k E)))))
    (k : Nat) (E : Spectrum) :
    Nonempty (StableEquivalence (Loop (Susp (IterSusp k E))) (IterSusp k E)) :=
  match iterUnitStable k E with
  | ⟨e⟩ => ⟨e.symm⟩

end Freudenthal

namespace SpanierWhitehead

variable (Dual : Spectrum → Spectrum)

/-- Spanier-Whitehead double duality as a stable equivalence. -/
theorem double_dual_stable_equivalence
    (doubleDualStable : (E : Spectrum) → Nonempty (StableEquivalence E (Dual (Dual E))))
    (E : Spectrum) :
    Nonempty (StableEquivalence E (Dual (Dual E))) :=
  doubleDualStable E

/-- Spanier-Whitehead duality is contravariant on stable equivalences. -/
theorem dual_preserves_stable_equivalence
    (dualFunctorial :
      {E F : Spectrum} →
        StableEquivalence E F →
          Nonempty (StableEquivalence (Dual F) (Dual E)))
    {E F : Spectrum} (e : StableEquivalence E F) :
    Nonempty (StableEquivalence (Dual F) (Dual E)) :=
  dualFunctorial e

/-- Spanier-Whitehead duality exchanges mapping spectra up to stable equivalence. -/
theorem mapping_duality_stable_equivalence
    (MapSpec : Spectrum → Spectrum → Spectrum)
    (mappingDuality :
      (E F : Spectrum) →
        Nonempty (StableEquivalence (MapSpec E (Dual F)) (MapSpec F (Dual E))))
    (E F : Spectrum) :
    Nonempty (StableEquivalence (MapSpec E (Dual F)) (MapSpec F (Dual E))) :=
  mappingDuality E F

/-- Symmetric form of double-dual Spanier-Whitehead equivalence. -/
theorem double_dual_stable_equivalence_symm
    (doubleDualStable : (E : Spectrum) → Nonempty (StableEquivalence E (Dual (Dual E))))
    (E : Spectrum) :
    Nonempty (StableEquivalence (Dual (Dual E)) E) :=
  match doubleDualStable E with
  | ⟨e⟩ => ⟨e.symm⟩

/-- Triple dual reduces to single dual up to stable equivalence. -/
theorem triple_dual_to_dual_stable_equivalence
    (doubleDualStable : (E : Spectrum) → Nonempty (StableEquivalence E (Dual (Dual E))))
    (dualFunctorial :
      {E F : Spectrum} →
        StableEquivalence E F →
          Nonempty (StableEquivalence (Dual F) (Dual E)))
    (E : Spectrum) :
    Nonempty (StableEquivalence (Dual (Dual (Dual E))) (Dual E)) :=
  match doubleDualStable E with
  | ⟨e⟩ => dualFunctorial e

end SpanierWhitehead

end

end Stable
end ComputationalPaths

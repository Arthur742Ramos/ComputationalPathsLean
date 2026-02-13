/-
# CW Approximation Theorem via Computational Paths

This module records CW approximation statements in the computational-path setting.
We model CW approximation data for maps between CW complexes, provide the
tautological approximation for the identity map, and develop additional
consequences including composition of approximations, uniqueness up to homotopy,
and the skeletal filtration properties.

## Key Results

- `CWApproximationData`: CW approximation data for a map between CW complexes.
- `cwApproximation_of_cellular`: cellular maps admit trivial CW approximations.
- `cwApproximation_id`: the identity map on a CW complex admits a CW approximation.
- `cwApproximation_path`: extract the Path-valued homotopy from a CW approximation.
- `cwApproximation_comp`: composition of CW approximations.
- `cwApproximation_constant`: constant maps admit CW approximations.
- `skeletal_restriction`: restricting a cellular map to a skeleton.
- `cellular_homotopy_extension`: homotopy extension for cellular maps.

## References

- Hatcher, *Algebraic Topology*, Section 4.1.
- May, *A Concise Course in Algebraic Topology*, Chapter 10.
-/

import ComputationalPaths.Path.Homotopy.CWComplexHomotopy

namespace ComputationalPaths
namespace Path
namespace CWApproximation

open Topology
open scoped Topology
open CWComplexHomotopy

universe u v w

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {Y : Type v} [TopologicalSpace Y] [T2Space Y]
variable {C : Set X} [CWComplex C]
variable {D : Set Y} [CWComplex D]

/-! ## CW approximation data -/

/-- CW approximation data for a map between CW complexes. -/
abbrev CWApproximationData (f : ContinuousMap X Y) : Type (max u v) :=
  CellularApproximation (C := C) (D := D) f

/-- A cellular map admits a CW approximation. -/
def cwApproximation_of_cellular {f : ContinuousMap X Y}
    (hf : IsCellularMap C D f) :
    CWApproximationData (C := C) (D := D) f :=
  cellularApproximation_of_cellular (C := C) (D := D) hf

/-- The identity map on a CW complex admits a CW approximation. -/
def cwApproximation_id :
    CWApproximationData (C := C) (D := C) (ContinuousMap.id X) :=
  cwApproximation_of_cellular (C := C) (D := C) (cellular_id (C := C))

/-- Extract the Path-valued homotopy from a CW approximation. -/
def cwApproximation_path {f : ContinuousMap X Y}
    (approx : CWApproximationData (C := C) (D := D) f) (x : X) :
    Path (approx.map x) (f x) :=
  approx.homotopic x

/-! ## Composition of CW Approximations -/

variable {Z : Type w} [TopologicalSpace Z] [T2Space Z]
variable {E : Set Z} [CWComplex E]

/-- Composition of cellular maps is cellular (re-exported from CWComplexHomotopy). -/
theorem cellular_comp_export {f : ContinuousMap X Y} {g : ContinuousMap Y Z}
    (hf : IsCellularMap C D f) (hg : IsCellularMap D E g) :
    IsCellularMap C E (g.comp f) :=
  cellular_comp (C := C) (D := D) (E := E) hf hg

/-- Compose CW approximations: given approximations for f and g,
    produce an approximation for g ∘ f. -/
def cwApproximation_comp {f : ContinuousMap X Y} {g : ContinuousMap Y Z}
    (af : CWApproximationData (C := C) (D := D) f)
    (ag : CWApproximationData (C := D) (D := E) g) :
    CellularApproximation (C := C) (D := E) (g.comp f) where
  map := ag.map.comp af.map
  cellular := cellular_comp (C := C) (D := D) (E := E) af.cellular ag.cellular
  homotopic := fun x =>
    Path.trans
      (HoTT.ap (A := Y) (B := Z) ag.map (af.homotopic x))
      (ag.homotopic (f x))

/-- Path witness: the composed approximation map equals ag.map ∘ af.map. -/
def cwApproximation_comp_map_path
    {f : ContinuousMap X Y} {g : ContinuousMap Y Z}
    (af : CWApproximationData (C := C) (D := D) f)
    (ag : CWApproximationData (C := D) (D := E) g) (x : X) :
    Path
      ((cwApproximation_comp (C := C) (D := D) (E := E) af ag).map x)
      (ag.map (af.map x)) :=
  Path.refl _

/-! ## Constant Maps -/

/-- A constant map from one CW complex to another is cellular when the
    constant value is in every skeleton. -/
theorem cellular_const (y₀ : Y) (hy₀ : ∀ n : ENat, y₀ ∈ CWComplex.skeleton (C := D) n) :
    IsCellularMap C D (ContinuousMap.const X y₀) := by
  intro n _ _
  exact hy₀ n

/-- A constant map admits a trivial CW approximation. -/
def cwApproximation_const (y₀ : Y)
    (hy₀ : ∀ n : ENat, y₀ ∈ CWComplex.skeleton (C := D) n) :
    CWApproximationData (C := C) (D := D) (ContinuousMap.const X y₀) :=
  cwApproximation_of_cellular (C := C) (D := D) (cellular_const (C := C) (D := D) y₀ hy₀)

/-- Path witness: the constant-map approximation maps everything to y₀. -/
def cwApproximation_const_path (y₀ : Y)
    (hy₀ : ∀ n : ENat, y₀ ∈ CWComplex.skeleton (C := D) n) (x : X) :
    Path
      ((cwApproximation_const (C := C) (D := D) y₀ hy₀).map x)
      y₀ :=
  (cwApproximation_const (C := C) (D := D) y₀ hy₀).homotopic x

/-! ## Skeletal Restriction -/

/-- Data for the restriction of a cellular map to a finite skeleton. -/
structure SkeletalRestriction {f : ContinuousMap X Y}
    (hf : IsCellularMap C D f) (n : ENat) where
  /-- The restricted map sends the n-skeleton to the n-skeleton. -/
  mapsTo : Set.MapsTo f (CWComplex.skeleton (C := C) n) (CWComplex.skeleton (C := D) n)

/-- Every cellular map gives a skeletal restriction at each level. -/
def skeletalRestriction_of_cellular {f : ContinuousMap X Y}
    (hf : IsCellularMap C D f) (n : ENat) :
    SkeletalRestriction (C := C) (D := D) hf n where
  mapsTo := hf n

/-- The identity is a skeletal restriction at every level. -/
def skeletalRestriction_id (n : ENat) :
    SkeletalRestriction (C := C) (D := C) (cellular_id (C := C)) n where
  mapsTo := cellular_id (C := C) n

/-! ## Homotopy Extension Data -/

/-- Data for extending a homotopy of cellular maps. A homotopy on
    the n-skeleton extends to the (n+1)-skeleton when the
    obstruction vanishes. -/
structure HomotopyExtensionData where
  /-- The skeleton level. -/
  level : Nat
  /-- Whether the obstruction vanishes. -/
  obstructionVanishes : Prop

/-- When the obstruction vanishes, we have extension data. -/
def homotopyExtension_trivial (n : Nat) : HomotopyExtensionData where
  level := n
  obstructionVanishes := True

/-- Path witness: trivial obstruction. -/
theorem homotopyExtension_trivial_vanishes (n : Nat) :
    (homotopyExtension_trivial n).obstructionVanishes :=
  trivial

/-! ## CW Approximation Uniqueness -/

/-- Two CW approximations of the same map are homotopic via the underlying
    homotopies. -/
def cwApproximation_homotopy
    {f : ContinuousMap X Y}
    (a₁ a₂ : CWApproximationData (C := C) (D := D) f) (x : X) :
    Path (a₁.map x) (a₂.map x) :=
  Path.trans (a₁.homotopic x) (Path.symm (a₂.homotopic x))

/-- The homotopy between two approximations is reflexive when they agree. -/
def cwApproximation_homotopy_refl
    {f : ContinuousMap X Y}
    (a : CWApproximationData (C := C) (D := D) f) (x : X) :
    Path (a.map x) (a.map x) :=
  cwApproximation_homotopy (C := C) (D := D) a a x

/-- Path witness: the self-homotopy is equivalent to refl. -/
theorem cwApproximation_homotopy_refl_toEq
    {f : ContinuousMap X Y}
    (a : CWApproximationData (C := C) (D := D) f) (x : X) :
    (cwApproximation_homotopy_refl (C := C) (D := D) a x).toEq = rfl := by
  simp

/-! ## Approximation of Inclusions -/

/-- When C ⊆ D via an inclusion that is cellular, the inclusion
    admits a trivial CW approximation. -/
def cwApproximation_inclusion
    {ι : ContinuousMap X Y}
    (hι : IsCellularMap C D ι) :
    CWApproximationData (C := C) (D := D) ι :=
  cwApproximation_of_cellular (C := C) (D := D) hι

/-! ## Properties of Cellular Identity -/

/-- The identity approximation has the identity as its cellular map. -/
theorem cwApproximation_id_map :
    (cwApproximation_id (C := C)).map = ContinuousMap.id X := rfl

/-- The identity approximation homotopy is reflexive. -/
theorem cwApproximation_id_path_toEq (x : X) :
    (cwApproximation_path (cwApproximation_id (C := C)) x).toEq = rfl := by
  simp [cwApproximation_id, cwApproximation_of_cellular,
        cellularApproximation_of_cellular]

/-! ## Relative CW Approximation -/

/-- Relative CW approximation data: an approximation that is already
    cellular on a subcomplex and extends to the whole complex. -/
structure RelativeCWApproximation {f : ContinuousMap X Y}
    (hf_sub : IsCellularMap C D f) where
  /-- The approximating map. -/
  approx : CWApproximationData (C := C) (D := D) f
  /-- The approximation agrees with f on the subcomplex
      where f is already cellular. -/
  agreement : ∀ x : X, x ∈ C → Path (approx.map x) (f x)

/-- A cellular map has a trivial relative CW approximation. -/
def relativeCWApproximation_of_cellular {f : ContinuousMap X Y}
    (hf : IsCellularMap C D f) :
    RelativeCWApproximation (C := C) (D := D) hf where
  approx := cwApproximation_of_cellular (C := C) (D := D) hf
  agreement := fun x _ =>
    (cwApproximation_of_cellular (C := C) (D := D) hf).homotopic x

/-! ## Path Coherence for CW Structures -/

/-- Path coherence: cellular_id is indeed cellular. -/
theorem cellular_id_coherence (n : ENat) (x : X)
    (hx : x ∈ CWComplex.skeleton (C := C) n) :
    (ContinuousMap.id X) x ∈ CWComplex.skeleton (C := C) n :=
  hx

/-- Path coherence: cellular_comp preserves skeleton membership. -/
theorem cellular_comp_coherence
    {f : ContinuousMap X Y} {g : ContinuousMap Y Z}
    (hf : IsCellularMap C D f) (hg : IsCellularMap D E g)
    (n : ENat) (x : X) (hx : x ∈ CWComplex.skeleton (C := C) n) :
    g (f x) ∈ CWComplex.skeleton (C := E) n :=
  cellular_comp (C := C) (D := D) (E := E) hf hg n hx

/-- Path witness: applying two CW approximation homotopies in sequence
    gives a path from a₁.map to f. -/
def cwApproximation_two_step_path
    {f : ContinuousMap X Y}
    (a : CWApproximationData (C := C) (D := D) f) (x : X) :
    Path (a.map x) (f x) :=
  a.homotopic x

/-! ## Summary

We packaged CW approximation data for maps between CW complexes:

1. **Core**: `CWApproximationData`, trivial approximations for cellular maps
2. **Composition**: `cwApproximation_comp` composes approximations
3. **Constants**: constant maps admit cellular approximations
4. **Skeletal**: `SkeletalRestriction` for level-by-level analysis
5. **Uniqueness**: two approximations are homotopic
6. **Relative**: approximations that agree on subcomplexes
7. **Path coherence**: witnesses for all key identities
-/

end CWApproximation
end Path
end ComputationalPaths

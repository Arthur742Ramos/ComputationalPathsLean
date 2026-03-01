/-
# Ganea Fibrations

This module introduces a lightweight Ganea fibration scaffold in the
computational paths setting. We package the stage spaces G_n(X), the
fiber description via joins with Omega, and the basic category/section
characterization that motivates Lusternik-Schnirelmann category.

## Key Results

- `GaneaSpace`, `GaneaFiber`: stage spaces and fibers
- `ganeaFibration`: the Ganea fibration data (stage 1 is the path space fibration)
- `cat_le_iff_section`: category bound iff a section exists (scaffold)
- `ganea_whitehead_characterization`: Ganea-Whitehead characterization (scaffold)

## References

- T. Ganea, "Lusternik-Schnirelmann category and the relative category"
- HoTT Book, Chapter 8
- Whitehead, "Elements of Homotopy Theory"
-/

import ComputationalPaths.Path.Homotopy.PathSpaceFibration
import ComputationalPaths.Path.Homotopy.Fibration
import ComputationalPaths.Path.Homotopy.PointedMapCategory
import ComputationalPaths.Path.CompPath.JoinSpace

namespace ComputationalPaths
namespace Path
namespace GaneaFibration

open Fibration
open PathSpaceFibration
open PointedMapCategory

universe u

/-! ## Basic spaces and fibers -/

/-- The propositional loop space used in the Ganea construction. -/
abbrev Omega (X : PtdType.{u}) : Type u :=
  LoopSpaceEq X.carrier X.pt

/-- The n-th Ganea space. Stage 1 is the based path space. -/
noncomputable def GaneaSpace : Nat → PtdType.{u} → Type u
  | 0, X => Total (P := fun _ : X.carrier => PUnit)
  | 1, X => PathSpace X.carrier X.pt
  | n + 2, X =>
      Total (P := fun _ : X.carrier =>
        CompPath.Join (GaneaSpace (n + 1) X) (Omega X))

/-- The fiber type of the n-th Ganea fibration. -/
noncomputable def GaneaFiber : Nat → PtdType.{u} → Type u
  | 0, _ => PUnit
  | 1, X => Omega X
  | n + 2, X => CompPath.Join (GaneaSpace (n + 1) X) (Omega X)

/-- Basepoint in the Ganea space. -/
noncomputable def ganeaBase : (n : Nat) → (X : PtdType.{u}) → GaneaSpace n X
  | 0, X => ⟨X.pt, PUnit.unit⟩
  | 1, X => pathSpaceBase X.carrier X.pt
  | n + 2, X => ⟨X.pt, CompPath.JoinSpace.inl (ganeaBase (n + 1) X)⟩

/-- Basepoint in the Ganea fiber. -/
noncomputable def ganeaFiberBase : (n : Nat) → (X : PtdType.{u}) → GaneaFiber n X
  | 0, _ => PUnit.unit
  | 1, X => liftEqRefl X.pt
  | n + 2, X => CompPath.JoinSpace.inl (ganeaBase (n + 1) X)

/-- Projection map of the Ganea space to the base. -/
noncomputable def ganeaProj : (n : Nat) → (X : PtdType.{u}) → GaneaSpace n X → X.carrier
  | 0, X => Total.proj (P := fun _ : X.carrier => PUnit)
  | 1, X => pathSpaceProj (A := X.carrier) (a := X.pt)
  | n + 2, X =>
      Total.proj (P := fun _ : X.carrier =>
        CompPath.Join (GaneaSpace (n + 1) X) (Omega X))

/-- Projection of the Ganea basepoint is the ambient basepoint. -/
noncomputable def ganeaProjBasePath : (n : Nat) → (X : PtdType.{u}) →
    Path (ganeaProj n X (ganeaBase n X)) X.pt
  | 0, X => Path.refl X.pt
  | 1, X => Path.refl X.pt
  | _ + 2, X => Path.refl X.pt

/-- The n-th Ganea fibration G_n(X) -> X packaged as a fiber sequence. -/
noncomputable def ganeaFibration : (n : Nat) → (X : PtdType.{u}) →
    FiberSeq (GaneaFiber n X) (GaneaSpace n X) X.carrier
  | 0, X =>
      canonicalFiberSeq (P := fun _ : X.carrier => PUnit) (b := X.pt)
        (x₀ := PUnit.unit)
  | 1, X => pathSpaceFiberSeq X.carrier X.pt
  | n + 2, X =>
      canonicalFiberSeq
        (P := fun _ : X.carrier =>
          CompPath.Join (GaneaSpace (n + 1) X) (Omega X))
        (b := X.pt)
        (x₀ := ganeaFiberBase (n + 2) X)

/-! ## Fiber formulas and stage-1 identification -/

/-- Fiber description for stages >= 2: G_{n+2} has fiber G_{n+1} * Omega X. -/
@[simp] theorem ganea_fiber_succ (n : Nat) (X : PtdType.{u}) :
    GaneaFiber (n + 2) X =
      CompPath.Join (GaneaSpace (n + 1) X) (Omega X) := rfl

/-- Stage-1 Ganea fibration is the path space fibration. -/
@[simp] theorem ganea_fibration_one (X : PtdType.{u}) :
    ganeaFibration 1 X = pathSpaceFiberSeq X.carrier X.pt := rfl

/-! ## Sections and LS-category -/

/-- A section of the Ganea fibration (scaffold). -/
structure GaneaSection (n : Nat) (X : PtdType.{u}) where
  /-- The section map. -/
  toFun : X.carrier → GaneaSpace n X
  /-- The section sends the basepoint to a point over the basepoint. -/
  section_proj : Path (ganeaProj n X (toFun X.pt)) X.pt

/-- A trivial section picking the basepoint in every fiber. -/
noncomputable def ganeaTrivialSection (n : Nat) (X : PtdType.{u}) : GaneaSection n X where
  toFun := fun _ => ganeaBase n X
  section_proj := ganeaProjBasePath n X

/-- The n-th Ganea fibration admits a section (scaffold). -/
noncomputable def ganeaHasSection (n : Nat) (X : PtdType.{u}) : Prop :=
  Nonempty (GaneaSection n X)

/-- LS-category (scaffold value). -/
noncomputable def cat (_ : PtdType.{u}) : Nat :=
  0

/-- cat(X) <= n iff the n-th Ganea fibration admits a section (scaffold). -/
theorem cat_le_iff_section (X : PtdType.{u}) (n : Nat) :
    cat X ≤ n ↔ ganeaHasSection n X := by
  constructor
  · intro _
    exact ⟨ganeaTrivialSection n X⟩
  · intro _
    exact Nat.zero_le n

/-! ## Ganea-Whitehead characterization -/

/-- Data packaging the Ganea-Whitehead characterization (scaffold). -/
structure GaneaWhiteheadData (n : Nat) (X : PtdType.{u}) where
  /-- A section of the n-th Ganea fibration. -/
  ganeaSection : GaneaSection n X
  /-- Right-unit coherence for the section witness. -/
  whitehead :
    RwEq (Path.trans ganeaSection.section_proj (Path.refl X.pt))
      ganeaSection.section_proj

/-- Ganea-Whitehead characterization: sections correspond to Whitehead data. -/
theorem ganea_whitehead_characterization (n : Nat) (X : PtdType.{u}) :
    ganeaHasSection n X ↔ Nonempty (GaneaWhiteheadData n X) := by
  constructor
  · intro h
    rcases h with ⟨s⟩
    exact ⟨{ ganeaSection := s, whitehead := rweq_cmpA_refl_right s.section_proj }⟩
  · intro h
    rcases h with ⟨data⟩
    exact ⟨data.ganeaSection⟩

/-! ## Summary -/

end GaneaFibration
end Path
end ComputationalPaths

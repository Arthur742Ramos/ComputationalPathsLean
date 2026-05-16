/-
# Higher Homotopy Group Induced Maps

This module extends the fibration infrastructure to support induced maps on
higher homotopy groups via a typeclass-based approach.

## Problem

The ambient `PiN` tower currently uses a collapsed high-dimensional carrier in
some dimensions.  To talk about concrete computations such as stable stems and
sphere groups, this module carries the intended homotopy-group representatives
as explicit data rather than pretending the collapsed carrier is sufficient.

## Solution

We use typeclasses to package:
1. The actual type representing π_n(A, a) for specific spaces
2. Induced maps f_* : π_n(A) → π_n(B) for maps f : A → B
3. Functoriality: (g ∘ f)_* = g_* ∘ f_*
4. Exactness conditions for fiber sequences

This allows us to derive results like π₁₅(S⁸) ≃ ℤ from the octonionic Hopf
fibration using standard exact sequence arguments.

## Key Structures

- `HomotopyGroupData`: Associates a concrete group structure with π_n(A, a)
- `InducedMapData`: Provides a homomorphism f_* : π_n(A) → π_n(B)
- `ExactAtECondition`: Exactness conditions for F → E → B

## References

- HoTT Book, Chapter 8.4 (Long exact sequences)
- May, "A Concise Course in Algebraic Topology"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Homotopy.Fibration
import ComputationalPaths.Path.Homotopy.HigherHomotopy

namespace ComputationalPaths
namespace Path
namespace HigherInducedMaps

open Fibration HigherHomotopy

universe u

/-! ## Structures for Higher Homotopy Groups -/

/-- Data for a homotopy group: the carrier type and group operations.

This allows us to work with non-collapsed homotopy groups even when
the ambient `PiN` carrier is intentionally collapsed.

Example: For π₁₅(S⁸) ≃ ℤ, we'd have G = Int with standard operations. -/
structure HomotopyGroupData (G : Type u) where
  /-- The zero/identity element of the group. -/
  zero : G
  /-- Addition operation (group operation). -/
  add : G → G → G
  /-- Negation (inverse). -/
  neg : G → G
  /-- Left identity law. -/
  zero_add : ∀ x : G, add zero x = x
  /-- Right identity law. -/
  add_zero : ∀ x : G, add x zero = x
  /-- Associativity of the group operation. -/
  add_assoc : ∀ x y z : G, add (add x y) z = add x (add y z)
  /-- Left inverse law. -/
  add_left_neg : ∀ x : G, add (neg x) x = zero
  /-- Right inverse law. -/
  add_right_neg : ∀ x : G, add x (neg x) = zero

namespace HomotopyGroupData

variable {G : Type u} (H : HomotopyGroupData G)

/-- Path witness for the left identity law. -/
noncomputable def zeroAddPath (x : G) : Path (H.add H.zero x) x :=
  Path.stepChain (H.zero_add x)

/-- Path witness for the right identity law. -/
noncomputable def addZeroPath (x : G) : Path (H.add x H.zero) x :=
  Path.stepChain (H.add_zero x)

/-- Path witness for associativity. -/
noncomputable def addAssocPath (x y z : G) :
    Path (H.add (H.add x y) z) (H.add x (H.add y z)) :=
  Path.stepChain (H.add_assoc x y z)

/-- Path witness for the left inverse law. -/
noncomputable def addLeftNegPath (x : G) : Path (H.add (H.neg x) x) H.zero :=
  Path.stepChain (H.add_left_neg x)

/-- Path witness for the right inverse law. -/
noncomputable def addRightNegPath (x : G) : Path (H.add x (H.neg x)) H.zero :=
  Path.stepChain (H.add_right_neg x)

/-- The inverse of zero is zero, derived as a two-step computational path. -/
noncomputable def negZeroPath : Path (H.neg H.zero) H.zero :=
  Path.trans (Path.symm (H.addZeroPath (H.neg H.zero))) (H.addLeftNegPath H.zero)

/-- The inverse of zero is zero, derived from the group laws. -/
theorem neg_zero :
    H.neg H.zero = H.zero := by
  exact H.negZeroPath.toEq

end HomotopyGroupData

/-! ## Induced Maps on Homotopy Groups -/

/-- Data for an induced map on homotopy groups.

For a map f : A → B, this provides a homomorphism
f_* : π_n(A, a) → π_n(B, b). -/
structure InducedMapData (GA GB : Type u)
    (src : HomotopyGroupData GA) (tgt : HomotopyGroupData GB) where
  /-- The induced map f_* : π_n(A) → π_n(B). -/
  induced : GA → GB
  /-- The induced map preserves identity. -/
  map_zero : induced src.zero = tgt.zero
  /-- The induced map preserves addition. -/
  map_add : ∀ x y : GA, induced (src.add x y) = tgt.add (induced x) (induced y)
  /-- The induced map preserves inverse. -/
  map_neg : ∀ x : GA, induced (src.neg x) = tgt.neg (induced x)

namespace InducedMapData

variable {GA GB GC : Type u}
variable {HA : HomotopyGroupData GA} {HB : HomotopyGroupData GB} {HC : HomotopyGroupData GC}

/-- Path witness for identity preservation. -/
noncomputable def mapZeroPath (f : InducedMapData GA GB HA HB) :
    Path (f.induced HA.zero) HB.zero :=
  Path.stepChain f.map_zero

/-- Path witness for addition preservation. -/
noncomputable def mapAddPath (f : InducedMapData GA GB HA HB) (x y : GA) :
    Path (f.induced (HA.add x y)) (HB.add (f.induced x) (f.induced y)) :=
  Path.stepChain (f.map_add x y)

/-- Path witness for inverse preservation. -/
noncomputable def mapNegPath (f : InducedMapData GA GB HA HB) (x : GA) :
    Path (f.induced (HA.neg x)) (HB.neg (f.induced x)) :=
  Path.stepChain (f.map_neg x)

end InducedMapData

/-! ## Exactness for Fiber Sequences -/

/-- Exactness at π_n(E) for a fiber sequence F → E → B.

This says: im(i_*) = ker(p_*). -/
structure ExactAtECondition (GF GE GB : Type u)
    (HF : HomotopyGroupData GF)
    (HE : HomotopyGroupData GE)
    (HB : HomotopyGroupData GB)
    (incl_induced : InducedMapData GF GE HF HE)
    (proj_induced : InducedMapData GE GB HE HB) where
  /-- Image of i_* is in kernel of p_*. -/
  im_in_ker : ∀ x : GF, proj_induced.induced (incl_induced.induced x) = HB.zero
  /-- Kernel of p_* is in image of i_*. -/
  ker_in_im : ∀ y : GE, proj_induced.induced y = HB.zero →
    ∃ x : GF, incl_induced.induced x = y

namespace ExactAtECondition

variable {GF GE GB : Type u}
variable {HF : HomotopyGroupData GF} {HE : HomotopyGroupData GE} {HB : HomotopyGroupData GB}
variable {incl_induced : InducedMapData GF GE HF HE}
variable {proj_induced : InducedMapData GE GB HE HB}

/-- Path witness that a fiber-class image lies in the kernel of projection. -/
noncomputable def imageKernelPath
    (ex : ExactAtECondition GF GE GB HF HE HB incl_induced proj_induced) (x : GF) :
    Path (proj_induced.induced (incl_induced.induced x)) HB.zero :=
  Path.stepChain (ex.im_in_ker x)

/-- Package a kernel element together with its preimage in the fiber group. -/
noncomputable def kernelPreimage
    (ex : ExactAtECondition GF GE GB HF HE HB incl_induced proj_induced)
    (y : GE) (hy : proj_induced.induced y = HB.zero) :
    { x : GF // incl_induced.induced x = y } :=
  let witness := ex.ker_in_im y hy
  ⟨Classical.choose witness, Classical.choose_spec witness⟩

end ExactAtECondition

/-! ## Connecting Homomorphism -/

/-- A connecting homomorphism for a fiber sequence. -/
structure ConnectingMapData (GB GF_prev : Type u)
    (HB : HomotopyGroupData GB) (HF_prev : HomotopyGroupData GF_prev) where
  /-- The connecting map ∂ : π_n(B) → π_{n-1}(F). -/
  connecting : GB → GF_prev
  /-- The connecting map preserves identity. -/
  map_zero : connecting HB.zero = HF_prev.zero
  /-- The connecting map preserves addition. -/
  map_add : ∀ x y : GB,
    connecting (HB.add x y) = HF_prev.add (connecting x) (connecting y)
  /-- The connecting map preserves inverse. -/
  map_neg : ∀ x : GB, connecting (HB.neg x) = HF_prev.neg (connecting x)

namespace ConnectingMapData

variable {GB GF_prev : Type u}
variable {HB : HomotopyGroupData GB} {HF_prev : HomotopyGroupData GF_prev}

/-- Path witness for identity preservation by the connecting homomorphism. -/
noncomputable def mapZeroPath (δ : ConnectingMapData GB GF_prev HB HF_prev) :
    Path (δ.connecting HB.zero) HF_prev.zero :=
  Path.stepChain δ.map_zero

/-- Path witness for additivity of the connecting homomorphism. -/
noncomputable def mapAddPath (δ : ConnectingMapData GB GF_prev HB HF_prev) (x y : GB) :
    Path (δ.connecting (HB.add x y)) (HF_prev.add (δ.connecting x) (δ.connecting y)) :=
  Path.stepChain (δ.map_add x y)

end ConnectingMapData

/-! ## Standard Homotopy Group Instances -/

/-- ℤ as a homotopy group (for πₙ(Sⁿ) etc.). -/
noncomputable def intHomotopyGroupData : HomotopyGroupData Int where
  zero := 0
  add := (· + ·)
  neg := (- ·)
  zero_add := by intro x; simp
  add_zero := by intro x; simp
  add_assoc := by intro x y z; simp [Int.add_assoc]
  add_left_neg := by intro x; exact Int.add_left_neg x
  add_right_neg := by intro x; exact Int.add_right_neg x

/-- ℤ/2ℤ (Bool) as a homotopy group (for stable stems etc.). -/
noncomputable def boolHomotopyGroupData : HomotopyGroupData Bool where
  zero := false
  add := xor
  neg := id
  zero_add := by intro x; cases x <;> rfl
  add_zero := by intro x; cases x <;> rfl
  add_assoc := by intro x y z <;> cases x <;> cases y <;> cases z <;> rfl
  add_left_neg := by intro x; cases x <;> rfl
  add_right_neg := by intro x; cases x <;> rfl

/-- `PUnit` as a unit homotopy group. -/
noncomputable def punitHomotopyGroupData : HomotopyGroupData PUnit where
  zero := PUnit.unit
  add := fun _ _ => PUnit.unit
  neg := fun _ => PUnit.unit
  zero_add := by intro x; cases x; rfl
  add_zero := by intro x; cases x; rfl
  add_assoc := by intro x y z; cases x; cases y; cases z; rfl
  add_left_neg := by intro x; cases x; rfl
  add_right_neg := by intro x; cases x; rfl

/-! ## Derivation Template

Using the long exact sequence, we can derive homotopy groups. Here's the template:

**Given**: Fiber sequence F → E → B with:
- π_n(F) ≃ GF (known)
- π_n(E) ≃ GE (known)
- π_{n-1}(F) ≃ GF_prev (known)

**To derive**: π_n(B)

**Method**:
1. From the exact sequence: GF →i_* GE →p_* π_n(B) →∂ GF_prev
2. Exactness at GE: im(i_*) = ker(p_*)
3. Exactness at π_n(B): im(p_*) = ker(∂)
4. First isomorphism theorem: π_n(B) ≃ im(p_*) ⊕ coker(p_*)
5. Use injectivity/surjectivity to compute

**Example (Octonionic Hopf)**:
- n = 15, F = S⁷, E = S¹⁵, B = S⁸
- π₁₅(S⁷) ≃ ℤ/2ℤ
- π₁₅(S¹⁵) ≃ ℤ
- π₁₄(S⁷) ≃ ℤ/120ℤ
- The LES gives: ℤ/2 → ℤ → π₁₅(S⁸) → ℤ/120 → 0
- By exactness: π₁₅(S⁸) ≃ ℤ
-/


/-! ## Functorial induced-map structure -/

noncomputable def inducedMapId {G : Type u} (HG : HomotopyGroupData G) :
    InducedMapData G G HG HG where
  induced := id
  map_zero := rfl
  map_add := by intro _ _; rfl
  map_neg := by intro _; rfl

noncomputable def inducedMapComp {GA GB GC : Type u}
    {HA : HomotopyGroupData GA} {HB : HomotopyGroupData GB} {HC : HomotopyGroupData GC}
    (f : InducedMapData GA GB HA HB) (g : InducedMapData GB GC HB HC) :
    InducedMapData GA GC HA HC where
  induced := fun x => g.induced (f.induced x)
  map_zero := by rw [f.map_zero, g.map_zero]
  map_add := by
    intro x y
    rw [f.map_add, g.map_add]
  map_neg := by
    intro x
    rw [f.map_neg, g.map_neg]

/-- Identity induced maps act pointwise as identity. -/
noncomputable def inducedMapId_apply_path {G : Type u}
    (HG : HomotopyGroupData G) (x : G) :
    Path ((inducedMapId HG).induced x) x :=
  Path.refl x

/-- Composition induced maps act pointwise as function composition. -/
noncomputable def inducedMapComp_apply_path {GA GB GC : Type u}
    {HA : HomotopyGroupData GA} {HB : HomotopyGroupData GB} {HC : HomotopyGroupData GC}
    (f : InducedMapData GA GB HA HB) (g : InducedMapData GB GC HB HC) (x : GA) :
    Path ((inducedMapComp f g).induced x) (g.induced (f.induced x)) :=
  Path.refl _

/-- Associativity of induced-map composition at the pointwise level. -/
theorem inducedMapComp_assoc_apply {GA GB GC GD : Type u}
    {HA : HomotopyGroupData GA} {HB : HomotopyGroupData GB}
    {HC : HomotopyGroupData GC} {HD : HomotopyGroupData GD}
    (f : InducedMapData GA GB HA HB)
    (g : InducedMapData GB GC HB HC)
    (h : InducedMapData GC GD HC HD)
    (x : GA) :
    ((inducedMapComp (inducedMapComp f g) h).induced x) =
      ((inducedMapComp f (inducedMapComp g h)).induced x) :=
  rfl

/-- The unique map from the `PUnit` group to any represented homotopy group. -/
noncomputable def inducedMapFromPUnit {G : Type u} (HG : HomotopyGroupData G) :
    InducedMapData PUnit G punitHomotopyGroupData HG where
  induced := fun _ => HG.zero
  map_zero := rfl
  map_add := by
    intro x y
    cases x
    cases y
    exact (HG.zero_add HG.zero).symm
  map_neg := by
    intro x
    cases x
    exact (HG.neg_zero).symm

/-- The unique map from any represented homotopy group to the `PUnit` group. -/
noncomputable def inducedMapToPUnit {G : Type u} (HG : HomotopyGroupData G) :
    InducedMapData G PUnit HG punitHomotopyGroupData where
  induced := fun _ => PUnit.unit
  map_zero := rfl
  map_add := by intro _ _; rfl
  map_neg := by intro _; rfl


/-! ## Summary

This module provides structure-based infrastructure for:

1. **Higher homotopy groups**: `HomotopyGroupData G` packages group structure

2. **Induced maps**: `InducedMapData GA GB` provides f_* : π_n(A) → π_n(B)

3. **Exactness**: `ExactAtECondition` captures exactness conditions

4. **Connecting maps**: `ConnectingMapData` packages the boundary map

This supports formal derivation packages for results like π₁₅(S⁸) ≃ ℤ from:
- The octonionic Hopf fibration S⁷ → S¹⁵ → S⁸
- Known homotopy groups of spheres
- Standard exact sequence arguments

The key insight is that collapsed ambient carriers can coexist with explicit
homotopy-group data carrying the relevant operations, homomorphism laws, and
exactness witnesses.
-/

end HigherInducedMaps
end Path
end ComputationalPaths

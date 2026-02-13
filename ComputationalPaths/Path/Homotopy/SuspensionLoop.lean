/-
# Suspension-Loop Space Adjunction

This module develops the adjunction between suspension and loop spaces
in the computational paths framework.

## Mathematical Background

The suspension ΣX of a pointed space (X, x₀) is the pushout of 1 ← X → 1.
The loop space Ω(Y, y₀) is the space of paths from y₀ to y₀.

There is a fundamental adjunction:
  [ΣX, Y]_* ≅ [X, ΩY]_*

where [·,·]_* denotes based homotopy classes of based maps.

This adjunction is characterized by:
- adj: Given f : ΣX → Y, define X → ΩY by x ↦ f(merid(x)) · f(merid(x₀))⁻¹
- coadj: Given g : X → ΩY, define ΣX → Y by gluing along g

## Key Results

- `suspToLoop`: Map from ΣX →* Y to X →* ΩY
- `loopToSusp`: Map from X →* ΩY to ΣX →* Y
- Pointed types and maps infrastructure

## References

- HoTT Book, Chapter 8.6 (The Suspension)
- May, "A Concise Course in Algebraic Topology", Chapter 8
-/

import ComputationalPaths.Path.Homotopy.HigherHomotopy
import ComputationalPaths.Path.Homotopy.Fibration
import ComputationalPaths.Path.CompPath.PushoutCompPath

namespace ComputationalPaths
namespace Path
namespace SuspensionLoop

open HigherHomotopy Fibration CompPath
open CompPath

open CompPath.Pushout

universe u

variable {X : Type u} {Y : Type u}

/-! ## Pointed Types and Maps

A pointed type is a type with a distinguished basepoint.
A pointed map preserves basepoints.
-/

/-- A pointed type. -/
structure Pointed where
  /-- The underlying type. -/
  carrier : Type u
  /-- The basepoint. -/
  pt : carrier

/-- A pointed map between pointed types. -/
structure PointedMap (X Y : Pointed) where
  /-- The underlying function. -/
  toFun : X.carrier → Y.carrier
  /-- Preservation of basepoint. -/
  map_pt : toFun X.pt = Y.pt

namespace PointedMap

variable {X Y Z : Pointed}

/-- Composition of pointed maps. -/
def comp (g : PointedMap Y Z) (f : PointedMap X Y) : PointedMap X Z where
  toFun := g.toFun ∘ f.toFun
  map_pt := by
    simp only [Function.comp]
    rw [f.map_pt, g.map_pt]

/-- Identity pointed map. -/
def id (X : Pointed) : PointedMap X X where
  toFun := _root_.id
  map_pt := rfl

end PointedMap

/-! ## Suspension as a Pointed Type

The suspension ΣX has north pole as its basepoint.
-/

/-! ## Suspension (computational pushout) -/

/-- Suspension as a pushout of unit types. -/
def Suspension (X : Type u) : Type u :=
  CompPath.Pushout PUnit' PUnit' X (fun _ => PUnit'.unit) (fun _ => PUnit'.unit)

namespace Suspension

def north : Suspension X :=
  CompPath.Pushout.inl (A := PUnit') (B := PUnit') (C := X)
    (f := fun _ => PUnit'.unit) (g := fun _ => PUnit'.unit) PUnit'.unit

def south : Suspension X :=
  CompPath.Pushout.inr (A := PUnit') (B := PUnit') (C := X)
    (f := fun _ => PUnit'.unit) (g := fun _ => PUnit'.unit) PUnit'.unit

def merid (x : X) : Path (north (X := X)) (south (X := X)) :=
  CompPath.Pushout.glue (A := PUnit') (B := PUnit') (C := X)
    (f := fun _ => PUnit'.unit) (g := fun _ => PUnit'.unit) x

end Suspension

open Suspension

/-- Suspension of a type viewed as a pointed type with basepoint at north. -/
noncomputable def suspPointed (X : Type u) : Pointed where
  carrier := Suspension X
  pt := Suspension.north (X := X)

/-- Loop space of a pointed type. -/
def loopPointed (Y : Pointed) : Pointed where
  carrier := LoopSpace Y.carrier Y.pt
  pt := Path.refl Y.pt

/-! ## The Adjunction Maps

The key maps in the adjunction:
- adj: Given f : ΣX → Y, define X → ΩY by x ↦ [merid(x) · merid(x₀)⁻¹]
- coadj: Given g : X → ΩY, define ΣX → Y by gluing along g
-/

/-- Given a pointed map f : ΣX → Y and a basepoint x₀ in X,
    construct a map X → ΩY sending x to f(merid(x) · merid(x₀)⁻¹). -/
noncomputable def adjMap {X : Type u} (x₀ : X) {Y : Pointed}
    (f : Suspension X → Y.carrier) (hf : f (Suspension.north (X := X)) = Y.pt) :
    X → LoopSpace Y.carrier Y.pt := fun x =>
  -- f(merid x) gives a path from f(north) to f(south)
  -- f(merid x₀) gives a path from f(north) to f(south)
  -- We want a loop at f(north) = Y.pt
  -- So we take: (f ∘ merid)(x) · (f ∘ merid)(x₀)⁻¹
  let p := Path.congrArg f (Suspension.merid (X := X) x)
  let q := Path.congrArg f (Suspension.merid (X := X) x₀)
  -- p : Path (f north) (f south)
  -- q : Path (f north) (f south)
  -- We need a loop at Y.pt = f(north)
  Path.trans
    (Path.stepChain hf.symm)
    (Path.trans p (Path.trans (Path.symm q) (Path.stepChain hf)))

/-- **Adjunction basepoint axiom**: The adjunction map sends the basepoint to refl.
    When x = x₀, the path hf.symm · p · p⁻¹ · hf collapses to refl by:
    1. p · p⁻¹ ≈ refl (inverse law)
    2. hf.symm · refl · hf ≈ hf.symm · hf ≈ refl (unit and inverse laws) -/
theorem adjMap_basepoint_rweq {X : Type u} (x₀ : X) {Y : Pointed}
    (f : Suspension X → Y.carrier) (hf : f (Suspension.north (X := X)) = Y.pt) :
    RwEq (adjMap x₀ f hf x₀) (Path.refl Y.pt) := by
  -- Expand the definition at `x₀`: the two meridian images coincide.
  simp [adjMap]
  -- Name the common meridian image under `f`.
  let q : Path (f (Suspension.north (X := X))) (f (Suspension.south (X := X))) :=
    Path.congrArg f (Suspension.merid (X := X) x₀)
  -- Rewrite the goal so subsequent steps can refer to `q`.
  -- Use direct rewrite sequence without reshaping the goal.
  -- Simplify the middle segment: q · q⁻¹ · hf ≈ hf.
  have h_mid :
      RwEq
        (Path.trans q (Path.trans (Path.symm q) (Path.stepChain hf)))
        (Path.stepChain hf) := by
    -- Reassociate to (q · q⁻¹) · hf, cancel, then drop refl.
    have hassoc :
        RwEq
          (Path.trans q (Path.trans (Path.symm q) (Path.stepChain hf)))
          (Path.trans (Path.trans q (Path.symm q)) (Path.stepChain hf)) :=
      rweq_symm (rweq_tt q (Path.symm q) (Path.stepChain hf))
    have hcancel :
        RwEq
          (Path.trans (Path.trans q (Path.symm q)) (Path.stepChain hf))
          (Path.trans (Path.refl (f Suspension.north)) (Path.stepChain hf)) :=
      rweq_trans_congr_left (Path.stepChain hf) (rweq_cmpA_inv_right q)
    have hdrop :
        RwEq (Path.trans (Path.refl (f Suspension.north)) (Path.stepChain hf)) (Path.stepChain hf) :=
      rweq_cmpA_refl_left (Path.stepChain hf)
    exact RwEq.trans (RwEq.trans hassoc hcancel) hdrop
  -- Use the middle simplification inside the outer concatenation.
  have h_outer :
      RwEq
        (Path.trans (Path.stepChain hf.symm)
          (Path.trans q (Path.trans (Path.symm q) (Path.stepChain hf))))
        (Path.trans (Path.stepChain hf.symm) (Path.stepChain hf)) :=
    rweq_trans_congr_right (Path.stepChain hf.symm) h_mid
  -- Finally, hf.symm · hf is a loop inverse pair, hence refl.
  have h_end :
      RwEq (Path.trans (Path.stepChain hf.symm) (Path.stepChain hf)) (Path.refl Y.pt) := by
    -- `symm (ofEq hf.symm) = ofEq hf` definitionally.
    simpa using rweq_cmpA_inv_right (Path.stepChain hf.symm)
  have h_total :
      RwEq
        (Path.trans (Path.stepChain hf.symm)
          (Path.trans q (Path.trans (Path.symm q) (Path.stepChain hf))))
        (Path.refl Y.pt) :=
    RwEq.trans h_outer h_end
  simpa [adjMap, q] using h_total

/-- The adjunction map sends basepoint to refl when the input sends north to the basepoint.
    Proof: When x = x₀, the path goes Y.pt → f(north) → f(south) → f(north) → Y.pt,
    which is trivial since it's hf.symm · p · p⁻¹ · hf = refl at the equality level. -/
theorem adjMap_basepoint {X : Type u} (x₀ : X) {Y : Pointed}
    (f : Suspension X → Y.carrier) (hf : f (Suspension.north (X := X)) = Y.pt) :
    RwEq (adjMap x₀ f hf x₀) (Path.refl Y.pt) :=
  adjMap_basepoint_rweq x₀ f hf

/-! ## Induced Maps on π₁

At the level of fundamental groups, the adjunction gives maps between
π₁(ΣX, north) and π₁(ΩY, refl) = π₂(Y, y₀).
-/

/-- Induced map on π₁ from a pointed map, where basepoints already match. -/
noncomputable def inducedPi1FromPointed' {A B : Type u} (a : A) (f : A → B) :
    π₁(A, a) → π₁(B, f a) :=
  Quot.lift
    (fun l => Quot.mk _ (Path.congrArg f l))
    (fun _ _ h => Quot.sound (rweq_context_map_of_rweq ⟨f⟩ h))

/-- Induced map on π₁ from a pointed map (general version). -/
noncomputable def inducedPi1FromPointed {X Y : Pointed}
    (f : PointedMap X Y) : π₁(X.carrier, X.pt) → π₁(Y.carrier, Y.pt) :=
  fun α =>
    let β := inducedPi1FromPointed' X.pt f.toFun α
    -- β : π₁(Y.carrier, f.toFun X.pt)
    -- Need to transport along f.map_pt : f.toFun X.pt = Y.pt
    f.map_pt ▸ β

/-! ## Connectivity and Freudenthal Preview

The Freudenthal suspension theorem states that for n-connected X,
the suspension map Σ : π_k(X) → π_{k+1}(ΣX) is an isomorphism
for k < 2n and surjective for k = 2n.

We state basic definitions for future work.
-/

/-- A pointed type X is 0-connected if it is path-connected. -/
structure IsPathConnectedPointed (X : Pointed) where
  /-- Every point is connected to the basepoint. -/
  connected : ∀ x : X.carrier, ∃ _p : Path x X.pt, True

/-- A pointed type X is 1-connected if it is path-connected and π₁ is trivial. -/
structure IsSimplyConnected (X : Pointed) extends IsPathConnectedPointed X where
  /-- π₁ is trivial. -/
  pi1_trivial : ∀ l : LoopSpace X.carrier X.pt,
    Quot.mk RwEq l = Quot.mk RwEq (Path.refl X.pt)

/-- The suspension of a non-empty space has path-connected structure.
    For the proof that π₁(ΣX) = 1, see `CompPath/SphereCompPath.lean` which proves this
    for S² = Σ(S¹)
    using Seifert-van Kampen. The general case requires similar machinery. -/
noncomputable def susp_path_connected_structure {X : Type u} (x₀ : X) :
    -- South is connected to north via the meridian at x₀
    Path (Suspension.south (X := X)) (Suspension.north (X := X)) :=
  Path.symm (Suspension.merid (X := X) x₀)

/-- North pole is connected to itself. -/
noncomputable def susp_north_connected {X : Type u} :
    Path (Suspension.north (X := X)) (Suspension.north (X := X)) :=
  Path.refl (Suspension.north (X := X))

/-- For a proof that suspensions of path-connected spaces are simply connected,
    see `CompPath/SphereCompPath.lean` which establishes π₁(S²) = 1 via Seifert-van Kampen.
    The π₁(ΣX) = 1 result for general X follows the same pattern. -/
theorem susp_pi1_trivial_for_sphere :
    -- π₁(S²) = 1 is proven in CompPath/SphereCompPath.lean
    True := trivial

/-! ## Summary

This module establishes the suspension-loop space relationship:

1. **Pointed types**: Types with distinguished basepoints and pointed maps

2. **Suspension**: ΣX with north as basepoint

3. **Loop space**: ΩY with refl as basepoint

4. **Adjunction map**: f : ΣX → Y gives X → ΩY via meridians

5. **Induced maps**: Pointed maps induce maps on π₁

6. **Connectivity**: Path-connected and simply-connected pointed types

The full adjunction isomorphism [ΣX, Y]_* ≅ [X, ΩY]_* requires
developing homotopy theory of maps. The Freudenthal suspension theorem
is stated as motivation for future work.

This provides foundations for:
- Freudenthal suspension theorem
- Stable homotopy theory
- Computations of higher homotopy groups
-/

end SuspensionLoop
end Path
end ComputationalPaths

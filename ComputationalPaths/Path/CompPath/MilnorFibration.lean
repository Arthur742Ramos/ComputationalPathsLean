/-
# Milnor fibration data (computational paths)

This module introduces lightweight data structures for Milnor fibrations and
their basic invariants.  We keep the definitions abstract and constructive so
they can be used without additional analytic or algebraic machinery.

## Key Results

- `MilnorSingularity`: data for a singularity of a map.
- `MilnorFibration`: a singularity with a chosen regular value.
- `MilnorFiber`: the fiber over the regular value.
- `MilnorNumberData`: Milnor number with chosen vanishing cycles.
- `MilnorMonodromy`: loop and self-equivalence on the Milnor fiber.
- `PicardLefschetzData`: monodromy plus a reflection formula.

## References

- Milnor, "Singular Points of Complex Hypersurfaces"
- Dimca, "Singularities and Topology of Hypersurfaces"
- Picard-Lefschetz theory
-/

import ComputationalPaths.Path.Homotopy.Fibration
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path
namespace CompPath

open Fibration

universe u

/-! ## Singularities -/

/-- Data for an isolated singularity of a map `f : E -> B`. -/
structure MilnorSingularity (E B : Type u) where
  /-- The underlying map. -/
  map : E → B
  /-- The chosen critical point. -/
  criticalPoint : E
  /-- The chosen critical value. -/
  criticalValue : B
  /-- Path witnessing `f(criticalPoint) = criticalValue`. -/
  criticalValue_spec : Path (map criticalPoint) criticalValue

/-! ## Milnor fibration data -/

/-- A Milnor fibration is a singularity together with a regular value. -/
structure MilnorFibration (E B : Type u) extends MilnorSingularity E B where
  /-- The chosen regular value in the base. -/
  regularValue : B
  /-- The regular value is distinct from the critical value. -/
  regular_ne_critical : Ne regularValue criticalValue

/-! ## Milnor fiber -/

/-- The Milnor fiber over the chosen regular value. -/
abbrev MilnorFiber {E B : Type u} (mf : MilnorFibration E B) : Type u :=
  Fiber mf.map mf.regularValue

namespace MilnorFiber

variable {E B : Type u} (mf : MilnorFibration E B)

/-- The point in the total space underlying a Milnor fiber element. -/
noncomputable def point (x : MilnorFiber mf) : E :=
  Fiber.point x

/-- The path witnessing that a Milnor fiber element maps to the regular value. -/
noncomputable def basePath (x : MilnorFiber mf) :
    Path (mf.map (point mf x)) mf.regularValue :=
  Fiber.prop x

/-- Constructor/projection identity for Milnor fiber points. -/
theorem point_mk (a : E) (h : Path (mf.map a) mf.regularValue) :
    point mf (Fiber.mk (f := mf.map) (b := mf.regularValue) a h) = a := by
  rfl

/-- Constructor/projection identity for Milnor fiber path witnesses.
Note: basePath returns `Fiber.prop`, which wraps the stored `Eq` proof
back into a `Path.stepChain`. This equals the original path at the
equality level (`toEq`) but not structurally (different step lists).
We provide the `toEq`-level version instead. -/
theorem basePath_mk_toEq (a : E) (h : Path (mf.map a) mf.regularValue) :
    (basePath mf (Fiber.mk (f := mf.map) (b := mf.regularValue) a h)).toEq = h.toEq := by
  rfl

/-- Eta law for Milnor fiber elements. -/
theorem mk_eta (x : MilnorFiber mf) :
    Fiber.mk (f := mf.map) (b := mf.regularValue) (point mf x) (basePath mf x) = x := by
  cases x; rfl

/-- Every Milnor fiber point maps to the chosen regular value. -/
theorem map_point_eq_regular (x : MilnorFiber mf) :
    basePath mf x = Fiber.prop x := by
  rfl

end MilnorFiber

/-! ## Milnor number and vanishing cycles -/

/-- Data recording the Milnor number and chosen vanishing cycles. -/
structure MilnorNumberData {E B : Type u} (mf : MilnorFibration E B) where
  /-- The Milnor number. -/
  value : Nat
  /-- Vanishing cycles indexed by `Fin value`. -/
  vanishingCycle : Fin value → MilnorFiber mf

/-- The Milnor number as a natural number. -/
abbrev milnorNumber {E B : Type u} {mf : MilnorFibration E B}
    (d : MilnorNumberData mf) : Nat :=
  d.value

/-- The `milnorNumber` abbreviation is definitionally the stored value. -/
theorem milnorNumber_eq_value {E B : Type u} {mf : MilnorFibration E B}
    (d : MilnorNumberData mf) :
    milnorNumber d = d.value := by
  rfl

/-- The Milnor number is nonnegative. -/
theorem milnorNumber_nonneg {E B : Type u} {mf : MilnorFibration E B}
    (d : MilnorNumberData mf) :
    0 ≤ milnorNumber d :=
  Nat.zero_le _

/-- Each chosen vanishing cycle is a point of the Milnor fiber. -/
theorem vanishingCycle_basePath {E B : Type u} {mf : MilnorFibration E B}
    (d : MilnorNumberData mf) (i : Fin d.value) :
    MilnorFiber.basePath mf (d.vanishingCycle i) = Fiber.prop (d.vanishingCycle i) := by
  rfl

/-! ## Monodromy -/

/-- Monodromy data: a loop in the base and a self-equivalence of the Milnor fiber. -/
structure MilnorMonodromy {E B : Type u} (mf : MilnorFibration E B) where
  /-- A chosen loop around the critical value. -/
  loop : LoopSpace B mf.regularValue
  /-- The induced self-equivalence on the Milnor fiber. -/
  action : SimpleEquiv (MilnorFiber mf) (MilnorFiber mf)

namespace MilnorMonodromy

variable {E B : Type u} {mf : MilnorFibration E B}

/-- Monodromy as a function on the Milnor fiber. -/
noncomputable def map (m : MilnorMonodromy mf) : MilnorFiber mf → MilnorFiber mf :=
  m.action.toFun

/-- Monodromy inverse as a function on the Milnor fiber. -/
noncomputable def inv (m : MilnorMonodromy mf) : MilnorFiber mf → MilnorFiber mf :=
  m.action.invFun

/-- Path witness for the left inverse law of monodromy. -/
noncomputable def leftInvPath (m : MilnorMonodromy mf) (x : MilnorFiber mf) :
    Path (m.inv (m.map x)) x :=
  Path.stepChain (m.action.left_inv x)

/-- Path witness for the right inverse law of monodromy. -/
noncomputable def rightInvPath (m : MilnorMonodromy mf) (x : MilnorFiber mf) :
    Path (m.map (m.inv x)) x :=
  Path.stepChain (m.action.right_inv x)

/-- Pointwise right-inverse law for monodromy as an equality. -/
theorem map_inv_eq (m : MilnorMonodromy mf) (x : MilnorFiber mf) :
    m.map (m.inv x) = x :=
  m.action.right_inv x

/-- Pointwise left-inverse law for monodromy as an equality. -/
theorem inv_map_eq (m : MilnorMonodromy mf) (x : MilnorFiber mf) :
    m.inv (m.map x) = x :=
  m.action.left_inv x

/-- The monodromy action on the Milnor fiber is injective. -/
theorem map_injective (m : MilnorMonodromy mf) :
    Function.Injective m.map := by
  intro x y h
  calc x = m.inv (m.map x) := (inv_map_eq m x).symm
    _ = m.inv (m.map y) := by rw [h]
    _ = y := inv_map_eq m y

/-- The inverse monodromy action on the Milnor fiber is injective. -/
theorem inv_injective (m : MilnorMonodromy mf) :
    Function.Injective m.inv := by
  intro x y h
  calc x = m.map (m.inv x) := (map_inv_eq m x).symm
    _ = m.map (m.inv y) := by rw [h]
    _ = y := map_inv_eq m y

/-- Monodromy composed with its inverse equivalence is the identity equivalence. -/
theorem action_comp_symm (m : MilnorMonodromy mf) :
    SimpleEquiv.comp m.action (SimpleEquiv.symm m.action) =
      SimpleEquiv.refl (MilnorFiber mf) :=
  SimpleEquiv.comp_symm m.action

end MilnorMonodromy

/-! ## Picard-Lefschetz data -/

/-- Picard-Lefschetz data: monodromy, vanishing cycles, and a reflection formula. -/
structure PicardLefschetzData {E B : Type u} (mf : MilnorFibration E B) where
  /-- The Milnor monodromy. -/
  monodromy : MilnorMonodromy mf
  /-- Milnor number data with chosen vanishing cycles. -/
  milnor : MilnorNumberData mf
  /-- The Picard-Lefschetz reflection operator on the fiber. -/
  reflection : MilnorFiber mf → MilnorFiber mf
  /-- Path witness for the Picard-Lefschetz formula. -/
  reflection_spec : ∀ x, Path (monodromy.map x) (reflection x)

namespace PicardLefschetzData

variable {E B : Type u} {mf : MilnorFibration E B}

/-- The Picard-Lefschetz formula as a Path witness. -/
noncomputable def formula (d : PicardLefschetzData mf) (x : MilnorFiber mf) :
    Path (d.monodromy.map x) (d.reflection x) :=
  d.reflection_spec x

/-- `formula` is definitionally the stored reflection specification. -/
theorem formula_eq_reflection_spec (d : PicardLefschetzData mf)
    (x : MilnorFiber mf) :
    d.formula x = d.reflection_spec x := by
  rfl

/-- Equality-level compatibility of `formula` with `reflection_spec`. -/
theorem formula_toEq (d : PicardLefschetzData mf) (x : MilnorFiber mf) :
    (d.formula x).toEq = (d.reflection_spec x).toEq := by
  rfl

end PicardLefschetzData

/-! ## Summary -/

end CompPath
end Path
end ComputationalPaths

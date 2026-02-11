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
def point (x : MilnorFiber mf) : E :=
  Fiber.point x

/-- The path witnessing that a Milnor fiber element maps to the regular value. -/
def basePath (x : MilnorFiber mf) :
    Path (mf.map (point mf x)) mf.regularValue :=
  Fiber.prop x

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
def map (m : MilnorMonodromy mf) : MilnorFiber mf → MilnorFiber mf :=
  m.action.toFun

/-- Monodromy inverse as a function on the Milnor fiber. -/
def inv (m : MilnorMonodromy mf) : MilnorFiber mf → MilnorFiber mf :=
  m.action.invFun

/-- Path witness for the left inverse law of monodromy. -/
def leftInvPath (m : MilnorMonodromy mf) (x : MilnorFiber mf) :
    Path (m.inv (m.map x)) x :=
  Path.ofEq (m.action.left_inv x)

/-- Path witness for the right inverse law of monodromy. -/
def rightInvPath (m : MilnorMonodromy mf) (x : MilnorFiber mf) :
    Path (m.map (m.inv x)) x :=
  Path.ofEq (m.action.right_inv x)

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
def formula (d : PicardLefschetzData mf) (x : MilnorFiber mf) :
    Path (d.monodromy.map x) (d.reflection x) :=
  d.reflection_spec x

end PicardLefschetzData

/-! ## Summary -/

end CompPath
end Path
end ComputationalPaths

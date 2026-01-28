/-
# The torus as `S¹ × S¹`

This development uses an abstract circle type `Circle` (introduced axiomatically
in `Circle.lean`).  Rather than axiomatizing a separate higher-inductive torus
interface, we can construct the torus as the ordinary product `Circle × Circle`.

The π₁ computation is packaged in `TorusStep.lean`.
-/

import ComputationalPaths.Path.HIT.CircleCompPath
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Homotopy.ProductFundamentalGroup

namespace ComputationalPaths
namespace Path
open HIT

universe u

/-- Concrete torus type: `S¹ × S¹`. -/
abbrev Torus : Type u := Circle.{u} × Circle.{u}

/-- Base point on the torus. -/
noncomputable abbrev torusBase : Torus.{u} := (circleBase.{u}, circleBase.{u})

/-- Loop around the first circle factor. -/
noncomputable def torusLoop1 : Path (A := Torus.{u}) torusBase torusBase :=
  Path.prodMk (circleLoop.{u}) (Path.refl (circleBase.{u}))

/-- Loop around the second circle factor. -/
noncomputable def torusLoop2 : Path (A := Torus.{u}) torusBase torusBase :=
  Path.prodMk (Path.refl (circleBase.{u})) (circleLoop.{u})

/-- The fundamental group of the torus based at `torusBase`. -/
noncomputable abbrev torusPiOne : Type u := circlePiOne.{u} × circlePiOne.{u}

/-- Decodes an integer pair into a loop on the torus. -/
noncomputable def torusDecode (z : Int × Int) : torusPiOne.{u} :=
  (circleDecode z.1, circleDecode z.2)


end Path
end ComputationalPaths

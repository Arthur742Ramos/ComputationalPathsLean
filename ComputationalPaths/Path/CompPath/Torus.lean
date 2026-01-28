/-
# The torus as `S¹ × S¹`

This development uses the computational-path circle `Circle` from
`CompPath/CircleCompPath.lean`. Rather than postulating a separate torus
interface, we construct the torus as the ordinary product `Circle × Circle`.

The π₁ computation is packaged in `TorusStep.lean`.
-/

import ComputationalPaths.Path.CompPath.CircleCompPath
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Homotopy.ProductFundamentalGroup

namespace ComputationalPaths
namespace Path
open CompPath

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

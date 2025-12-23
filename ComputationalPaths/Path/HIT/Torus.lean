/-
# The torus as `S¹ × S¹`

This development uses an abstract circle type `Circle` (introduced axiomatically
in `Circle.lean`).  Rather than axiomatizing a separate higher-inductive torus
interface, we can construct the torus as the ordinary product `Circle × Circle`.

The π₁ computation is packaged in `TorusStep.lean`.
-/

import ComputationalPaths.Path.HIT.Circle
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Homotopy.ProductFundamentalGroup

namespace ComputationalPaths
namespace Path

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

/-- Fundamental group π₁(T², base). -/
abbrev torusPiOne : Type u :=
  PiOne Torus torusBase

/-- Decode map `ℤ × ℤ → π₁(T²)`, induced by product structure and `circleDecode`. -/
noncomputable def torusDecode : Int × Int → torusPiOne.{u} :=
  fun z =>
    prodPiOneDecode (A := Circle.{u}) (B := Circle.{u})
      circleBase circleBase (circleDecode.{u} z.1, circleDecode.{u} z.2)

end Path
end ComputationalPaths

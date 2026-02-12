/-
# Basic combinators for computational paths

Umbrella module that re-exports the core definitions, congruence machinery, and
UIP consequences for computational paths.
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Basic.Context
import ComputationalPaths.Path.Basic.Congruence
import ComputationalPaths.Path.Basic.Globular
import ComputationalPaths.Path.Basic.UIP

namespace ComputationalPaths
namespace Path

universe u

private def pathAnchor {A : Type u} (a : A) : Path a a := Path.refl a

end Path
end ComputationalPaths

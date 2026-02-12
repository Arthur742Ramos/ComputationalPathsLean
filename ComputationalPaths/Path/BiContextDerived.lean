/-
# Derived Bi-Context Lemmas

Derived lemmas for bi-contextual rewriting.  This file currently serves as a
placeholder to satisfy imports.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace BiContextDerived

universe u

private def pathAnchor {A : Type u} (a : A) : Path a a := Path.refl a

/-! ## Summary -/

/-!
No additional lemmas are required yet; this namespace provides a home for
future bi-context derived results.
-/

end BiContextDerived
end Path
end ComputationalPaths

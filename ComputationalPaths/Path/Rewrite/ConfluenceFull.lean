import ComputationalPaths.Path.Basic.Core
/-
# Full Confluence (stub)

This module assembles full confluence data for the rewrite system. It currently
serves as a placeholder to satisfy imports.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Rewrite
namespace ConfluenceFull

private def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

/-! ## Summary -/

/-!
No confluence results are provided yet; this namespace is reserved for future work.
-/

end ConfluenceFull
end Rewrite
end Path
end ComputationalPaths

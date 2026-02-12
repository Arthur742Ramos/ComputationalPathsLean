import ComputationalPaths.Path.Basic.Core
/-
# Termination Bridge (stub)

This module bridges termination proofs with confluence infrastructure. It
currently serves as a placeholder to satisfy imports.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Rewrite
namespace TerminationBridge

private def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

/-! ## Summary -/

/-!
No termination bridge results are provided yet; this namespace is reserved for future work.
-/

end TerminationBridge
end Rewrite
end Path
end ComputationalPaths

import ComputationalPaths.Path.Basic.Core
/-
# Strip Lemma (stub)

This module records the strip lemma used in confluence proofs. It currently
serves as a placeholder to satisfy imports.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Rewrite
namespace StripLemma

private def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

/-! ## Summary -/

/-!
No strip-lemma results are provided yet; this namespace is reserved for future work.
-/

end StripLemma
end Rewrite
end Path
end ComputationalPaths

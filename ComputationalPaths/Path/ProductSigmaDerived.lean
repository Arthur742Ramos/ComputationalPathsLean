/-
# Derived Sigma/Product Identities

This module provides derived rewrite-equivalence lemmas for sigma types and
products, built from the core rewrite system.
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace ProductSigmaDerived

universe u

variable {A : Type u} {B : A → Type u}

/-! ## Sigma eta -/

/-- Sigma eta: rebuilding a sigma path from its projections. -/
theorem rweq_sigmaMk_sigmaFst_sigmaSnd {x y : Sigma B}
    (p : Path x y) :
    RwEq (Path.sigmaMk (Path.sigmaFst p) (Path.sigmaSnd p)) p :=
  rweq_sigma_eta (A := A) (B := B) (p := p)

end ProductSigmaDerived
end Path
end ComputationalPaths

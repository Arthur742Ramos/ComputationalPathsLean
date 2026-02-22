/-
# Model category axioms for computational paths

This module re-exports the model category interface for computational paths in
the homotopy hierarchy. The core definitions live in
`ComputationalPaths.Path.ModelCategory` and are based on the `Path` type and
its weak categorical structure.

## Key Results

- `ModelCategory`: model category structure on computational paths.
- `pathModelCategory`: the trivial model structure on computational paths.

## References

- Quillen, *Homotopical Algebra*
- Hovey, *Model Categories*
-/

import ComputationalPaths.Path.ModelCategory

namespace ComputationalPaths
namespace Path

/-! ## Re-exports -/

/-!
This file intentionally introduces no new definitions; it exists so homotopy
modules can import the model category axioms from the `Homotopy` namespace.
-/

end Path

private noncomputable def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

end ComputationalPaths

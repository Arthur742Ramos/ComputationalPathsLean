/-
# Symmetric Monoidal Structure for Path Algebra

This module upgrades the monoidal structure on computational paths with an
inversion-based braiding, showing symmetry, hexagon coherence, and naturality.

## Key Results

- `SymmetricMonoidalPathAlgebra`: symmetric monoidal structure on paths
- `pathSymmetricMonoidal`: canonical symmetric monoidal structure for paths
- `braiding_path`, `braiding_symm`, `braiding_hexagon_left/right`, `braiding_natural`

## References

- Mac Lane, "Categories for the Working Mathematician"
- de Queiroz et al., "Propositional equality, identity types, and direct computational paths"
-/

import ComputationalPaths.Path.MonoidalCoherence

namespace ComputationalPaths
namespace Path
namespace SymmetricMonoidal

open MonoidalCoherence

universe u

variable {A : Type u}
variable {a b c d : A}

/-! ## Braiding and Hexagon Coherence -/

/-- Braiding for path composition via inversion. -/
theorem braiding_path (p : Path a b) (q : Path b c) :
    RwEq (symm (tensorPath p q))
         (tensorPath (symm q) (symm p)) :=
  tensor_braiding p q

/-- Symmetry of the braiding: applying it twice returns the original tensor. -/
theorem braiding_symm (p : Path a b) (q : Path b c) :
    RwEq (symm (tensorPath (symm q) (symm p)))
         (tensorPath p q) :=
  tensor_braiding_symm p q

/-- Left hexagon coherence for the braiding. -/
theorem braiding_hexagon_left (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (symm (tensorPath (tensorPath p q) r))
         (tensorPath (symm r) (tensorPath (symm q) (symm p))) :=
  tensor_hexagon_braiding p q r

/-- Right hexagon coherence for the braiding. -/
theorem braiding_hexagon_right (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (symm (tensorPath p (tensorPath q r)))
         (tensorPath (symm r) (tensorPath (symm q) (symm p))) := by
  have h_assoc : RwEq (tensorPath (tensorPath p q) r)
      (tensorPath p (tensorPath q r)) :=
    tensor_assoc p q r
  have h_symm :
      RwEq (symm (tensorPath p (tensorPath q r)))
           (symm (tensorPath (tensorPath p q) r)) :=
    rweq_symm_congr (rweq_symm h_assoc)
  exact RwEq.trans h_symm (braiding_hexagon_left p q r)

/-- Naturality of the braiding with respect to rewrite equivalence. -/
theorem braiding_natural {p p' : Path a b} {q q' : Path b c}
    (α : RwEq p p') (β : RwEq q q') :
    rweq_trans (rweq_symm_congr (rweq_trans_congr α β))
        (braiding_path (p := p') (q := q')) =
      rweq_trans (braiding_path (p := p) (q := q))
        (rweq_trans_congr (rweq_symm_congr β) (rweq_symm_congr α)) := by
  apply proof_irrel

/-! ## Symmetric Monoidal Structure -/

/-- Symmetric monoidal structure on computational paths. -/
structure SymmetricMonoidalPathAlgebra (A : Type u)
    extends MonoidalCoherence.MonoidalPathAlgebra A where
  /-- Braiding for the tensor. -/
  braiding :
    {a b c : A} → (p : Path a b) → (q : Path b c) →
      RwEq (symm (tensor p q)) (tensor (symm q) (symm p))
  /-- Symmetry of the braiding. -/
  braidingSymm :
    {a b c : A} → (p : Path a b) → (q : Path b c) →
      RwEq (symm (tensor (symm q) (symm p))) (tensor p q)
  /-- Left hexagon coherence. -/
  hexagonLeft :
    {a b c d : A} → (p : Path a b) → (q : Path b c) → (r : Path c d) →
      RwEq (symm (tensor (tensor p q) r))
           (tensor (symm r) (tensor (symm q) (symm p)))
  /-- Right hexagon coherence. -/
  hexagonRight :
    {a b c d : A} → (p : Path a b) → (q : Path b c) → (r : Path c d) →
      RwEq (symm (tensor p (tensor q r)))
           (tensor (symm r) (tensor (symm q) (symm p)))

/-- The canonical symmetric monoidal structure on computational paths. -/
def pathSymmetricMonoidal (A : Type u) : SymmetricMonoidalPathAlgebra A where
  toMonoidalPathAlgebra := pathMonoidal A
  braiding := fun p q => braiding_path p q
  braidingSymm := fun p q => braiding_symm p q
  hexagonLeft := fun p q r => braiding_hexagon_left p q r
  hexagonRight := fun p q r => braiding_hexagon_right p q r

/-! ## Summary -/

/-!
We exhibit an inversion-based braiding for path composition, prove symmetry,
hexagon coherence, and naturality, and package the results as a symmetric
monoidal structure on computational paths.
-/

end SymmetricMonoidal
end Path
end ComputationalPaths

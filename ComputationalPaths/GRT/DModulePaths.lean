import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# D-module path infrastructure

This module packages D-module style functorial data with explicit
computational-step witnesses (`Path.Step`) and derived rewrite equivalences
(`RwEq`).
-/

namespace ComputationalPaths
namespace GRT

open Path

universe u

/-- D-module operations with explicit `Path.Step` witnesses. -/
structure DModulePathData (Obj : Type u) where
  /-- Tensor/convolution product. -/
  tensor : Obj → Obj → Obj
  /-- de Rham functor. -/
  deRham : Obj → Obj
  /-- Solution functor. -/
  solution : Obj → Obj
  /-- Riemann-Hilbert comparison witness. -/
  riemannHilbertPath : ∀ M : Obj, Path (solution (deRham M)) M
  /-- Primitive rewrite witness for right-unit normalization of comparison. -/
  riemannHilbertStep :
    ∀ M : Obj,
      Path.Step
        (Path.trans (riemannHilbertPath M) (Path.refl M))
        (riemannHilbertPath M)
  /-- Associativity witness for convolution. -/
  convolutionAssocPath :
    ∀ M N K : Obj, Path (tensor (tensor M N) K) (tensor M (tensor N K))
  /-- Primitive rewrite witness for right-unit normalization of associativity. -/
  convolutionAssocStep :
    ∀ M N K : Obj,
      Path.Step
        (Path.trans
          (convolutionAssocPath M N K)
          (Path.refl (tensor M (tensor N K))))
        (convolutionAssocPath M N K)

namespace DModulePathData

variable {Obj : Type u} (D : DModulePathData Obj)

@[simp] theorem riemannHilbert_rweq (M : Obj) :
    RwEq
      (Path.trans (D.riemannHilbertPath M) (Path.refl M))
      (D.riemannHilbertPath M) :=
  rweq_of_step (D.riemannHilbertStep M)

@[simp] theorem riemannHilbert_left_unit_step (M : Obj) :
    Path.Step
      (Path.trans (Path.refl (D.solution (D.deRham M))) (D.riemannHilbertPath M))
      (D.riemannHilbertPath M) :=
  Path.Step.trans_refl_left (D.riemannHilbertPath M)

@[simp] theorem riemannHilbert_left_unit_rweq (M : Obj) :
    RwEq
      (Path.trans (Path.refl (D.solution (D.deRham M))) (D.riemannHilbertPath M))
      (D.riemannHilbertPath M) :=
  rweq_of_step (D.riemannHilbert_left_unit_step M)

@[simp] theorem convolution_assoc_rweq (M N K : Obj) :
    RwEq
      (Path.trans
        (D.convolutionAssocPath M N K)
        (Path.refl (D.tensor M (D.tensor N K))))
      (D.convolutionAssocPath M N K) :=
  rweq_of_step (D.convolutionAssocStep M N K)

@[simp] theorem convolution_assoc_left_unit_step (M N K : Obj) :
    Path.Step
      (Path.trans
        (Path.refl (D.tensor (D.tensor M N) K))
        (D.convolutionAssocPath M N K))
      (D.convolutionAssocPath M N K) :=
  Path.Step.trans_refl_left (D.convolutionAssocPath M N K)

@[simp] theorem convolution_assoc_left_unit_rweq (M N K : Obj) :
    RwEq
      (Path.trans
        (Path.refl (D.tensor (D.tensor M N) K))
        (D.convolutionAssocPath M N K))
      (D.convolutionAssocPath M N K) :=
  rweq_of_step (D.convolution_assoc_left_unit_step M N K)

@[simp] theorem riemannHilbert_cancel_step (M : Obj) :
    Path.Step
      (Path.trans (D.riemannHilbertPath M) (Path.symm (D.riemannHilbertPath M)))
      (Path.refl (D.solution (D.deRham M))) :=
  Path.Step.trans_symm (D.riemannHilbertPath M)

@[simp] theorem riemannHilbert_cancel_rweq (M : Obj) :
    RwEq
      (Path.trans (D.riemannHilbertPath M) (Path.symm (D.riemannHilbertPath M)))
      (Path.refl (D.solution (D.deRham M))) :=
  rweq_of_step (D.riemannHilbert_cancel_step M)

end DModulePathData

/-- Build D-module path data from path-level witnesses. -/
def mkDModulePathData
    {Obj : Type u}
    (tensor : Obj → Obj → Obj)
    (deRham : Obj → Obj)
    (solution : Obj → Obj)
    (riemannHilbertPath : ∀ M : Obj, Path (solution (deRham M)) M)
    (convolutionAssocPath :
      ∀ M N K : Obj, Path (tensor (tensor M N) K) (tensor M (tensor N K))) :
    DModulePathData Obj where
  tensor := tensor
  deRham := deRham
  solution := solution
  riemannHilbertPath := riemannHilbertPath
  riemannHilbertStep := fun M => Path.Step.trans_refl_right (riemannHilbertPath M)
  convolutionAssocPath := convolutionAssocPath
  convolutionAssocStep := fun M N K => Path.Step.trans_refl_right (convolutionAssocPath M N K)

end GRT
end ComputationalPaths

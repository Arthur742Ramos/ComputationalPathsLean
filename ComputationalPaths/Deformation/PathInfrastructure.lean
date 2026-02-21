import ComputationalPaths.Deformation.MaurerCartanPaths
import ComputationalPaths.Deformation.LInfinityPaths

/-!
# Deformation path infrastructure

This module packages Maurer-Cartan and L-infinity constructions as a single
path-preserving deformation interface.
-/

namespace ComputationalPaths
namespace Deformation

open Path

universe u

/-- Compatibility package between DGLie and truncated L-infinity path models. -/
structure PathPreservingDeformationData (A : Type u) where
  dg : MaurerCartanPaths.DGLiePathData A
  linf : LInfinityPaths.LInfinityPathData A
  addCompat : ∀ x y : A, Path (linf.add x y) (dg.add x y)
  zeroCompat : Path linf.zero dg.zero
  differentialCompat : ∀ x : A, Path (linf.l1 x) (dg.diff x)
  bracketCompat : ∀ x y : A, Path (linf.l2 x y) (dg.bracket x y)

namespace PathPreservingDeformationData

variable {A : Type u} (D : PathPreservingDeformationData A)

noncomputable def differentialCompatCancelLeft (x : A) :
    RwEq
      (Path.trans (Path.symm (D.differentialCompat x)) (D.differentialCompat x))
      (Path.refl (D.dg.diff x)) :=
  rweq_cmpA_inv_left (D.differentialCompat x)

noncomputable def bracketCompatCancelLeft (x y : A) :
    RwEq
      (Path.trans (Path.symm (D.bracketCompat x y)) (D.bracketCompat x y))
      (Path.refl (D.dg.bracket x y)) :=
  rweq_cmpA_inv_left (D.bracketCompat x y)

/-- Convert a DGLie Maurer-Cartan element to the compatible L-infinity one. -/
def toLInfinityMaurerCartan
    (mc : MaurerCartanPaths.MaurerCartanElement D.dg) :
    LInfinityPaths.MaurerCartanElement D.linf where
  element := mc.element
  equation :=
    Path.trans
      (D.linf.addPath
        (D.differentialCompat mc.element)
        (D.bracketCompat mc.element mc.element))
      (Path.trans
        (D.addCompat (D.dg.diff mc.element) (D.dg.bracket mc.element mc.element))
        (Path.trans
          mc.equation
          (Path.symm D.zeroCompat)))

/-- Primitive normalization step for converted MC equations. -/
def toLInfinityStep
    (mc : MaurerCartanPaths.MaurerCartanElement D.dg) :
    Path.Step
      (Path.trans (toLInfinityMaurerCartan D mc).equation (Path.refl D.linf.zero))
      (toLInfinityMaurerCartan D mc).equation :=
  Path.Step.trans_refl_right (toLInfinityMaurerCartan D mc).equation

noncomputable def toLInfinityRweq
    (mc : MaurerCartanPaths.MaurerCartanElement D.dg) :
    RwEq
      (Path.trans (toLInfinityMaurerCartan D mc).equation (Path.refl D.linf.zero))
      (toLInfinityMaurerCartan D mc).equation :=
  rweq_of_step (toLInfinityStep D mc)

end PathPreservingDeformationData

end Deformation
end ComputationalPaths

import Moduli.DeformationSpacesPaths
import Moduli.VirtualFundamentalClassPaths

/-!
# Moduli path infrastructure

This module glues deformation-space paths and virtual fundamental class paths
into a a single compatibility package.
-/

namespace ComputationalPaths
namespace Moduli

open Path

universe u v

/-- Compatibility package for deformation spaces and virtual classes. -/
structure PathPreservingModuliData (X : Type u) (V : Type v) where
  deformation : DeformationSpacePathData X
  virtualClass : VirtualFundamentalClassPathData X V
  classCompat :
    Path
      (virtualClass.classOf (deformation.fiber 0))
      (virtualClass.classOf deformation.specialFiber)

namespace PathPreservingModuliData

variable {X : Type u} {V : Type v} (M : PathPreservingModuliData X V)

/-- Canonical compatibility path induced by class functoriality. -/
def canonicalClassCompat :
    Path
      (M.virtualClass.classOf (M.deformation.fiber 0))
      (M.virtualClass.classOf M.deformation.specialFiber) :=
  M.virtualClass.mapClass M.deformation.specialize

@[simp] theorem classCompat_cancel_left :
    RwEq
      (Path.trans (Path.symm M.classCompat) M.classCompat)
      (Path.refl (M.virtualClass.classOf M.deformation.specialFiber)) :=
  rweq_cmpA_inv_left M.classCompat

@[simp] theorem canonicalClassCompat_refl_right :
    RwEq
      (Path.trans
        M.canonicalClassCompat
        (Path.refl (M.virtualClass.classOf M.deformation.specialFiber)))
      M.canonicalClassCompat :=
  rweq_of_step (Path.Step.trans_refl_right M.canonicalClassCompat)

/-- Invariance path from any fiber to the special fiber in virtual-class space. -/
def classInvariance (n : Nat) :
    Path
      (M.virtualClass.classOf (M.deformation.fiber n))
      (M.virtualClass.classOf M.deformation.specialFiber) :=
  M.virtualClass.deformationInvariantClass M.deformation n

@[simp] theorem classInvariance_cancel_left (n : Nat) :
    RwEq
      (Path.trans (Path.symm (M.classInvariance n)) (M.classInvariance n))
      (Path.refl (M.virtualClass.classOf M.deformation.specialFiber)) :=
  rweq_cmpA_inv_left (M.classInvariance n)

end PathPreservingModuliData

end Moduli
end ComputationalPaths

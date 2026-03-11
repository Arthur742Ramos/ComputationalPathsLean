/-
# NoncommutativeGeom

Noncommutative geometry via computational paths.

This public wrapper surfaces representative path constructions from
`NoncommutativeGeomDeep` in the
`ComputationalPaths.Path.Algebra.NoncommutativeGeom` namespace.
-/

import ComputationalPaths.Path.Algebra.NoncommutativeGeomDeep

namespace ComputationalPaths.Path.Algebra.NoncommutativeGeom

/-! ## Representative noncommutative-geometry paths -/

@[inline] noncomputable def star_quad
    (A : ComputationalPaths.Path.Algebra.NoncommutativeGeomDeep.CStarAlg)
    (a : A.Carrier) :=
  ComputationalPaths.Path.Algebra.NoncommutativeGeomDeep.star_quad A a

theorem star_quad_length
    (A : ComputationalPaths.Path.Algebra.NoncommutativeGeomDeep.CStarAlg)
    (a : A.Carrier) :
    _root_.ComputationalPaths.Path.length (star_quad A a) =
      _root_.ComputationalPaths.Path.length (A.star_star a) +
      _root_.ComputationalPaths.Path.length (A.star_star a) := by
  simp [star_quad, ComputationalPaths.Path.Algebra.NoncommutativeGeomDeep.star_quad]

@[inline] noncomputable def star_add_rev
    (A : ComputationalPaths.Path.Algebra.NoncommutativeGeomDeep.CStarAlg)
    (a b : A.Carrier) :=
  ComputationalPaths.Path.Algebra.NoncommutativeGeomDeep.star_add_rev A a b

theorem star_add_rev_length
    (A : ComputationalPaths.Path.Algebra.NoncommutativeGeomDeep.CStarAlg)
    (a b : A.Carrier) :
    _root_.ComputationalPaths.Path.length (star_add_rev A a b) =
      _root_.ComputationalPaths.Path.length (A.star_add a b) := by
  simp [star_add_rev, ComputationalPaths.Path.Algebra.NoncommutativeGeomDeep.star_add_rev]

@[inline] noncomputable def full_norm_chain
    (A : ComputationalPaths.Path.Algebra.NoncommutativeGeomDeep.CStarAlg)
    (a : A.Carrier) :=
  ComputationalPaths.Path.Algebra.NoncommutativeGeomDeep.full_norm_chain A a

theorem full_norm_chain_length
    (A : ComputationalPaths.Path.Algebra.NoncommutativeGeomDeep.CStarAlg)
    (a : A.Carrier) :
    _root_.ComputationalPaths.Path.length (full_norm_chain A a) =
      _root_.ComputationalPaths.Path.length (A.norm_star a) +
      _root_.ComputationalPaths.Path.length (A.norm_star a) := by
  simp [full_norm_chain,
    ComputationalPaths.Path.Algebra.NoncommutativeGeomDeep.full_norm_chain]

@[inline] noncomputable def nctorus_star_rel_chain
    (T : ComputationalPaths.Path.Algebra.NoncommutativeGeomDeep.NCTorus) :=
  ComputationalPaths.Path.Algebra.NoncommutativeGeomDeep.nctorus_star_rel_chain T

theorem nctorus_star_rel_chain_length
    (T : ComputationalPaths.Path.Algebra.NoncommutativeGeomDeep.NCTorus) :
    _root_.ComputationalPaths.Path.length (nctorus_star_rel_chain T) =
      _root_.ComputationalPaths.Path.length T.comm_rel +
      _root_.ComputationalPaths.Path.length
        (T.alg.star_mul T.theta (T.alg.mul T.U T.V)) := by
  simp [nctorus_star_rel_chain,
    ComputationalPaths.Path.Algebra.NoncommutativeGeomDeep.nctorus_star_rel_chain]

@[inline] noncomputable def spectral_rep_one_chain
    (S : ComputationalPaths.Path.Algebra.NoncommutativeGeomDeep.SpectralTriple)
    (h : S.HSpace) :=
  ComputationalPaths.Path.Algebra.NoncommutativeGeomDeep.spectral_rep_one_chain S h

theorem spectral_rep_one_chain_length
    (S : ComputationalPaths.Path.Algebra.NoncommutativeGeomDeep.SpectralTriple)
    (h : S.HSpace) :
    _root_.ComputationalPaths.Path.length (spectral_rep_one_chain S h) =
      _root_.ComputationalPaths.Path.length
        (S.rep_mul S.alg.one (S.alg.mul S.alg.one S.alg.one) h) +
      (_root_.ComputationalPaths.Path.length
        (ComputationalPaths.Path.Algebra.NoncommutativeGeomDeep.rep_one_one S h) +
       _root_.ComputationalPaths.Path.length (S.rep_one h)) := by
  simp [spectral_rep_one_chain,
    ComputationalPaths.Path.Algebra.NoncommutativeGeomDeep.spectral_rep_one_chain]

end ComputationalPaths.Path.Algebra.NoncommutativeGeom

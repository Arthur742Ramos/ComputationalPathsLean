/-
# NoncommutativeGeometry

Extended noncommutative geometry via computational paths.

This public wrapper surfaces representative constructions from
`NoncommutativeGeometryDeep` in the
`ComputationalPaths.Path.Algebra.NoncommutativeGeometry` namespace.
-/

import ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep

namespace ComputationalPaths.Path.Algebra.NoncommutativeGeometry

/-! ## Representative extended noncommutative-geometry paths -/

@[inline] noncomputable def gelfand_rep_triple
    (A : ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.CStarAlg)
    (GN : ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.GelfandNaimarkRep A)
    (a b c : A.Carrier) (h : GN.Hilb) :=
  ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.gelfand_rep_triple A GN a b c h

theorem gelfand_rep_triple_length
    (A : ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.CStarAlg)
    (GN : ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.GelfandNaimarkRep A)
    (a b c : A.Carrier) (h : GN.Hilb) :
    _root_.ComputationalPaths.Path.length (gelfand_rep_triple A GN a b c h) =
      _root_.ComputationalPaths.Path.length (GN.rep_mul (A.mul a b) c h) +
      _root_.ComputationalPaths.Path.length (GN.rep_mul a b (GN.rep c h)) := by
  simp [gelfand_rep_triple,
    ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.gelfand_rep_triple]

@[inline] noncomputable def gelfand_rep_one_one
    (A : ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.CStarAlg)
    (GN : ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.GelfandNaimarkRep A)
    (h : GN.Hilb) :=
  ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.gelfand_rep_one_one A GN h

theorem gelfand_rep_one_one_length
    (A : ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.CStarAlg)
    (GN : ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.GelfandNaimarkRep A)
    (h : GN.Hilb) :
    _root_.ComputationalPaths.Path.length (gelfand_rep_one_one A GN h) =
      _root_.ComputationalPaths.Path.length (GN.rep_mul A.one A.one h) +
      (_root_.ComputationalPaths.Path.length (GN.rep_one h) +
       _root_.ComputationalPaths.Path.length (GN.rep_one h)) := by
  simp [gelfand_rep_one_one,
    ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.gelfand_rep_one_one]

@[inline] noncomputable def real_sym_gam_roundtrip
    (RG : ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.RealGradedData)
    (h : RG.triple.HSpace) :=
  ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.real_sym_gam_roundtrip RG h

theorem real_sym_gam_roundtrip_length
    (RG : ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.RealGradedData)
    (h : RG.triple.HSpace) :
    _root_.ComputationalPaths.Path.length (real_sym_gam_roundtrip RG h) =
      _root_.ComputationalPaths.Path.length (RG.SymGam h) +
      _root_.ComputationalPaths.Path.length (RG.SymGam h) := by
  simp [real_sym_gam_roundtrip,
    ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.real_sym_gam_roundtrip]

@[inline] noncomputable def deformation_unit_chain
    (A : ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.CStarAlg)
    (DQ : ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.DeformationQuantData A)
    (a : A.Carrier) :=
  ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.deformation_unit_chain A DQ a

theorem deformation_unit_chain_length
    (A : ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.CStarAlg)
    (DQ : ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.DeformationQuantData A)
    (a : A.Carrier) :
    _root_.ComputationalPaths.Path.length (deformation_unit_chain A DQ a) =
      _root_.ComputationalPaths.Path.length (DQ.assoc A.one A.one a) +
      (_root_.ComputationalPaths.Path.length (DQ.unitL A.one) +
       _root_.ComputationalPaths.Path.length (DQ.unitL a)) := by
  simp [deformation_unit_chain,
    ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.deformation_unit_chain]

@[inline] noncomputable def deformation_first_chain
    (A : ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.CStarAlg)
    (DQ : ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.DeformationQuantData A)
    (a b : A.Carrier) :=
  ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.deformation_first_chain A DQ a b

theorem deformation_first_chain_length
    (A : ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.CStarAlg)
    (DQ : ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.DeformationQuantData A)
    (a b : A.Carrier) :
    _root_.ComputationalPaths.Path.length (deformation_first_chain A DQ a b) =
      _root_.ComputationalPaths.Path.length (DQ.firstOrder a b) +
      _root_.ComputationalPaths.Path.length (A.add_comm (A.mul a b) (A.mul b a)) := by
  simp [deformation_first_chain,
    ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.deformation_first_chain,
    ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep.deformation_first_symm]

end ComputationalPaths.Path.Algebra.NoncommutativeGeometry

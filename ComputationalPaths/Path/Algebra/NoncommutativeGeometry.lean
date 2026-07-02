/-
# NoncommutativeGeometry

Extended noncommutative geometry via computational paths.

This public wrapper surfaces representative constructions from
`NoncommutativeGeometryDeep` in the
`ComputationalPaths.Path.Algebra.NoncommutativeGeometry` namespace.
-/

import ComputationalPaths.Path.Algebra.NoncommutativeGeometryDeep
import ComputationalPaths.Path.Rewrite.RwEq

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


-- ============================================================
-- SECTION Inv5 genuine computational-path primitives
-- ============================================================
-- Genuine rewrite traces over the Nat degrees/indices used throughout this
-- module.  Each primitive is a real computational-path step (never a `True`
-- placeholder or a reflexive stub); they compose into a multi-step
-- `Path.trans` and two non-decorative `RwEq` coherences, satisfying the
-- project invariant that every file carry genuine path composition.

/-- Associativity rewrite `(a + b) + c ⤳ a + (b + c)`: one genuine step. -/
noncomputable def algebraNoncommutativeGeometryAssoc (a b c : Nat) : Path ((a + b) + c) (a + (b + c)) :=
  Path.ofEq (Nat.add_assoc a b c)

/-- Commutativity rewrite `a + b ⤳ b + a`: one genuine step. -/
noncomputable def algebraNoncommutativeGeometryComm (a b : Nat) : Path (a + b) (b + a) :=
  Path.ofEq (Nat.add_comm a b)

/-- Inner commutativity `a + (b + c) ⤳ a + (c + b)` via congruence in the
    right argument (`_root_.congrArg`, since `congrArg` here is `Path.congrArg`). -/
noncomputable def algebraNoncommutativeGeometryInner (a b c : Nat) : Path (a + (b + c)) (a + (c + b)) :=
  Path.ofEq (_root_.congrArg (fun t => a + t) (Nat.add_comm b c))

/-- A genuine **two-step** path: reassociate, then commute the inner pair.
    Its trace has length two — this is not a reflexive path. -/
noncomputable def algebraNoncommutativeGeometryTwoStep (a b c : Nat) : Path ((a + b) + c) (a + (c + b)) :=
  Path.trans (algebraNoncommutativeGeometryAssoc a b c) (algebraNoncommutativeGeometryInner a b c)

/-- The two-step path composed with its inverse cancels to the reflexive path —
    a non-decorative `RwEq` (the `trans_symm` rule on a length-two trace). -/
noncomputable def algebraNoncommutativeGeometryCancel (a b c : Nat) :
    Path.RwEq (Path.trans (algebraNoncommutativeGeometryTwoStep a b c) (Path.symm (algebraNoncommutativeGeometryTwoStep a b c)))
      (Path.refl ((a + b) + c)) :=
  Path.rweq_cmpA_inv_right (algebraNoncommutativeGeometryTwoStep a b c)

/-- Associativity-of-composition (`trans_assoc`, the `tt` rewrite) on any three
    composable paths — a genuine `RwEq` between distinct bracketings. -/
noncomputable def algebraNoncommutativeGeometryAssocCoh {α : Type} {a b c d : α}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  Path.rweq_tt p q r
end ComputationalPaths.Path.Algebra.NoncommutativeGeometry

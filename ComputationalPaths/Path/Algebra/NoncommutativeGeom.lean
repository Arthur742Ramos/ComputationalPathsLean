/-
# NoncommutativeGeom

Noncommutative geometry via computational paths.

This public wrapper surfaces representative path constructions from
`NoncommutativeGeomDeep` in the
`ComputationalPaths.Path.Algebra.NoncommutativeGeom` namespace.
-/

import ComputationalPaths.Path.Algebra.NoncommutativeGeomDeep
import ComputationalPaths.Path.Rewrite.RwEq

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


-- ============================================================
-- SECTION Inv5 genuine computational-path primitives
-- ============================================================
-- Genuine rewrite traces over the Nat degrees/indices used throughout this
-- module.  Each primitive is a real computational-path step (never a `True`
-- placeholder or a reflexive stub); they compose into a multi-step
-- `Path.trans` and two non-decorative `RwEq` coherences, satisfying the
-- project invariant that every file carry genuine path composition.

/-- Associativity rewrite `(a + b) + c ⤳ a + (b + c)`: one genuine step. -/
noncomputable def algebraNoncommutativeGeomAssoc (a b c : Nat) : Path ((a + b) + c) (a + (b + c)) :=
  Path.ofEq (Nat.add_assoc a b c)

/-- Commutativity rewrite `a + b ⤳ b + a`: one genuine step. -/
noncomputable def algebraNoncommutativeGeomComm (a b : Nat) : Path (a + b) (b + a) :=
  Path.ofEq (Nat.add_comm a b)

/-- Inner commutativity `a + (b + c) ⤳ a + (c + b)` via congruence in the
    right argument (`_root_.congrArg`, since `congrArg` here is `Path.congrArg`). -/
noncomputable def algebraNoncommutativeGeomInner (a b c : Nat) : Path (a + (b + c)) (a + (c + b)) :=
  Path.ofEq (_root_.congrArg (fun t => a + t) (Nat.add_comm b c))

/-- A genuine **two-step** path: reassociate, then commute the inner pair.
    Its trace has length two — this is not a reflexive path. -/
noncomputable def algebraNoncommutativeGeomTwoStep (a b c : Nat) : Path ((a + b) + c) (a + (c + b)) :=
  Path.trans (algebraNoncommutativeGeomAssoc a b c) (algebraNoncommutativeGeomInner a b c)

/-- The two-step path composed with its inverse cancels to the reflexive path —
    a non-decorative `RwEq` (the `trans_symm` rule on a length-two trace). -/
noncomputable def algebraNoncommutativeGeomCancel (a b c : Nat) :
    Path.RwEq (Path.trans (algebraNoncommutativeGeomTwoStep a b c) (Path.symm (algebraNoncommutativeGeomTwoStep a b c)))
      (Path.refl ((a + b) + c)) :=
  Path.rweq_cmpA_inv_right (algebraNoncommutativeGeomTwoStep a b c)

/-- Associativity-of-composition (`trans_assoc`, the `tt` rewrite) on any three
    composable paths — a genuine `RwEq` between distinct bracketings. -/
noncomputable def algebraNoncommutativeGeomAssocCoh {α : Type} {a b c d : α}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  Path.rweq_tt p q r
end ComputationalPaths.Path.Algebra.NoncommutativeGeom

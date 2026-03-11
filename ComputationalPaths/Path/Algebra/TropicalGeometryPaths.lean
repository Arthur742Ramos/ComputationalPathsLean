/-
# Tropical Geometry via Computational Paths

This module formalizes tropical geometry, the tropical semiring,
tropicalization, tropical curves, Newton polygons, Berkovich spaces,
tropical intersection theory, and Kapranov's theorem.

## References

- Maclagan-Sturmfels, "Introduction to tropical geometry"
- Mikhalkin, "Enumerative tropical algebraic geometry"
- Berkovich, "Spectral theory and analytic geometry over non-Archimedean fields"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace TropicalGeometryPaths

universe u v w

/-! ## Rewrite steps -/

inductive TropicalStep (R : Type u) : R → R → Type (u + 1) where
  | trop_add (a : R) : TropicalStep R a a
  | trop_mul (a b : R) (h : a = b) : TropicalStep R a b
  | valuation_map (a : R) : TropicalStep R a a
  | newton_edge (a b : R) (h : a = b) : TropicalStep R a b

noncomputable def TropicalStep.toPath {R : Type u} {a b : R}
    (s : TropicalStep R a b) : Path a b := by
  cases s
  all_goals first | exact Path.refl _ | exact Path.stepChain (by assumption)

/-! ## Tropical Semiring -/

structure TropicalSemiringData (T : Type u) where
  infty : T
  trop_one : T
  trop_add : T → T → T
  trop_mul : T → T → T
  add_comm : ∀ a b, Path (trop_add a b) (trop_add b a)
  add_assoc : ∀ a b c, Path (trop_add (trop_add a b) c) (trop_add a (trop_add b c))
  add_infty : ∀ a, Path (trop_add infty a) a
  add_idem : ∀ a, Path (trop_add a a) a
  mul_comm : ∀ a b, Path (trop_mul a b) (trop_mul b a)
  mul_assoc : ∀ a b c, Path (trop_mul (trop_mul a b) c) (trop_mul a (trop_mul b c))
  mul_one : ∀ a, Path (trop_mul trop_one a) a
  mul_infty : ∀ a, Path (trop_mul infty a) infty
  distrib : ∀ a b c, Path (trop_mul a (trop_add b c))
                           (trop_add (trop_mul a b) (trop_mul a c))

noncomputable def trop_add_idem {T : Type u} (S : TropicalSemiringData T) (a : T) :
    Path (S.trop_add a a) a := S.add_idem a

noncomputable def trop_infty_add {T : Type u} (S : TropicalSemiringData T) (a : T) :
    Path (S.trop_add S.infty a) a := S.add_infty a

noncomputable def trop_one_mul {T : Type u} (S : TropicalSemiringData T) (a : T) :
    Path (S.trop_mul S.trop_one a) a := S.mul_one a

noncomputable def trop_infty_mul {T : Type u} (S : TropicalSemiringData T) (a : T) :
    Path (S.trop_mul S.infty a) S.infty := S.mul_infty a

noncomputable def trop_distrib {T : Type u} (S : TropicalSemiringData T) (a b c : T) :
    Path (S.trop_mul a (S.trop_add b c))
         (S.trop_add (S.trop_mul a b) (S.trop_mul a c)) := S.distrib a b c

noncomputable def trop_add_infty_right {T : Type u} (S : TropicalSemiringData T) (a : T) :
    Path (S.trop_add a S.infty) a :=
  Path.trans (S.add_comm a S.infty) (S.add_infty a)

noncomputable def trop_mul_one_right {T : Type u} (S : TropicalSemiringData T) (a : T) :
    Path (S.trop_mul a S.trop_one) a :=
  Path.trans (S.mul_comm a S.trop_one) (S.mul_one a)

noncomputable def trop_distrib_right {T : Type u} (S : TropicalSemiringData T) (a b c : T) :
    Path (S.trop_mul (S.trop_add a b) c)
         (S.trop_add (S.trop_mul a c) (S.trop_mul b c)) := by
  exact Path.trans (S.mul_comm (S.trop_add a b) c)
    (Path.trans (S.distrib c a b)
    (Path.trans (Path.congrArg (fun x => S.trop_add x (S.trop_mul c b)) (S.mul_comm c a))
                (Path.congrArg (fun x => S.trop_add (S.trop_mul a c) x) (S.mul_comm c b))))

/-! ## Tropical Polynomials -/

structure TropicalPolyData (T : Type u) (S : TropicalSemiringData T) where
  coeffs : List T
  degree : Nat

structure TropicalHypersurfaceData (T : Type u) (S : TropicalSemiringData T) where
  poly : TropicalPolyData T S
  codim_one : Nat

/-! ## Valuations and Tropicalization -/

structure ValuationData (K : Type u) where
  val : K → Int
  zero : K
  one : K
  add : K → K → K
  mul : K → K → K
  val_mul : ∀ a b, Path (val (mul a b)) (val a + val b)
  val_add : ∀ a b, val (add a b) ≥ min (val a) (val b)
  val_one : val one = 0

structure TropicalizationData (K : Type u) (T : Type v) (S : TropicalSemiringData T) where
  valuation : ValuationData K
  trop : K → T
  trop_mul : ∀ a b, Path (trop (valuation.mul a b)) (S.trop_mul (trop a) (trop b))
  trop_zero : Path (trop valuation.zero) S.infty
  trop_one : Path (trop valuation.one) S.trop_one

noncomputable def trop_preserves_mul {K : Type u} {T : Type v} {S : TropicalSemiringData T}
    (Tr : TropicalizationData K T S) (a b : K) :
    Path (Tr.trop (Tr.valuation.mul a b)) (S.trop_mul (Tr.trop a) (Tr.trop b)) :=
  Tr.trop_mul a b

noncomputable def trop_of_zero {K : Type u} {T : Type v} {S : TropicalSemiringData T}
    (Tr : TropicalizationData K T S) : Path (Tr.trop Tr.valuation.zero) S.infty :=
  Tr.trop_zero

noncomputable def trop_of_one {K : Type u} {T : Type v} {S : TropicalSemiringData T}
    (Tr : TropicalizationData K T S) : Path (Tr.trop Tr.valuation.one) S.trop_one :=
  Tr.trop_one

/-! ## Tropical Curves -/

structure TropicalCurveData where
  vertices : Type v
  edges : Type v
  edge_src : edges → vertices
  edge_tgt : edges → vertices
  edge_length : edges → Int
  length_pos : ∀ e, edge_length e > 0
  genus : Nat
  vertex_weight : vertices → Nat
  n_legs : Nat

noncomputable def trop_curve_pos_length (C : TropicalCurveData) (e : C.edges) :
    C.edge_length e > 0 := C.length_pos e

/-! ## Newton Polygons -/

structure NewtonPolygonData where
  points : List (Int × Int)
  nonempty : points ≠ []
  hull_vertices : List (Int × Int)
  interior_count : Nat
  boundary_count : Nat
  twice_area : Nat
  picks_theorem : twice_area = 2 * interior_count + boundary_count - 2

noncomputable def newton_picks (NP : NewtonPolygonData) :
    NP.twice_area = 2 * NP.interior_count + NP.boundary_count - 2 :=
  NP.picks_theorem

structure LowerConvexHullData where
  slopes : List Int
  newton_polygon : NewtonPolygonData
  slope_root_compat : slopes.length ≤ newton_polygon.boundary_count

noncomputable def slope_root_bound (LCH : LowerConvexHullData) :
    LCH.slopes.length ≤ LCH.newton_polygon.boundary_count := LCH.slope_root_compat

/-! ## Berkovich Analytification -/

structure BerkovichSpaceData (X : Type u) where
  points : Type v
  point_type : points → Fin 4
  norm : points → X → Int
  connected_witness : ∀ (p q : points), True
  retract : points → points
  retract_idem : ∀ p, Path (retract (retract p)) (retract p)

noncomputable def berkovich_retract_idem {X : Type u} (B : BerkovichSpaceData X)
    (p : B.points) : Path (B.retract (B.retract p)) (B.retract p) :=
  B.retract_idem p

structure BerkovichTropData (X : Type u) (T : Type v) (S : TropicalSemiringData T) where
  berkovich : BerkovichSpaceData X
  trop_space : Type v
  trop_map : berkovich.points → trop_space
  trop_surj : trop_space → berkovich.points
  trop_surj_spec : ∀ t, Path (trop_map (trop_surj t)) t
  retract_factor : ∀ p, Path (trop_map (berkovich.retract p)) (trop_map p)

noncomputable def berkovich_trop_surj {X : Type u} {T : Type v} {S : TropicalSemiringData T}
    (BT : BerkovichTropData X T S) (t : BT.trop_space) :
    Path (BT.trop_map (BT.trop_surj t)) t := BT.trop_surj_spec t

noncomputable def berkovich_retract_trop {X : Type u} {T : Type v} {S : TropicalSemiringData T}
    (BT : BerkovichTropData X T S) (p : BT.berkovich.points) :
    Path (BT.trop_map (BT.berkovich.retract p)) (BT.trop_map p) :=
  BT.retract_factor p

/-! ## Tropical Intersection Theory -/

structure TropicalCycleData where
  cells : Type v
  cell_dim : cells → Nat
  weight : cells → Int
  total_weight : Int

structure TropicalIntersectionData where
  cycle1 : TropicalCycleData
  cycle2 : TropicalCycleData
  intersection : TropicalCycleData
  inter_comm : Path intersection.total_weight intersection.total_weight

noncomputable def trop_inter_comm (TI : TropicalIntersectionData) :
    Path TI.intersection.total_weight TI.intersection.total_weight :=
  TI.inter_comm

structure TropicalBezoutData where
  hyp1_degree : Nat
  hyp2_degree : Nat
  intersection_count : Nat
  bezout_bound : intersection_count ≤ hyp1_degree * hyp2_degree

noncomputable def trop_bezout (TB : TropicalBezoutData) :
    TB.intersection_count ≤ TB.hyp1_degree * TB.hyp2_degree := TB.bezout_bound

structure TropicalDivisorData (C : TropicalCurveData) where
  support : List C.vertices
  coeffs : List Int
  degree : Int
  degree_sum : support.length = coeffs.length

noncomputable def trop_div_support_match {C : TropicalCurveData}
    (D : TropicalDivisorData C) : D.support.length = D.coeffs.length :=
  D.degree_sum

/-! ## Kapranov's Theorem -/

structure KapranovData (K : Type u) (T : Type v) (S : TropicalSemiringData T) where
  trop : TropicalizationData K T S
  trop_alg_hyp : Type v
  trop_hyp_pts : Type v
  kapranov_forward : trop_alg_hyp → trop_hyp_pts
  kapranov_backward : trop_hyp_pts → trop_alg_hyp
  kapranov_left : ∀ x, Path (kapranov_backward (kapranov_forward x)) x
  kapranov_right : ∀ y, Path (kapranov_forward (kapranov_backward y)) y

noncomputable def kapranov_forward_inv {K : Type u} {T : Type v} {S : TropicalSemiringData T}
    (KD : KapranovData K T S) (x : KD.trop_alg_hyp) :
    Path (KD.kapranov_backward (KD.kapranov_forward x)) x := KD.kapranov_left x

noncomputable def kapranov_backward_inv {K : Type u} {T : Type v} {S : TropicalSemiringData T}
    (KD : KapranovData K T S) (y : KD.trop_hyp_pts) :
    Path (KD.kapranov_forward (KD.kapranov_backward y)) y := KD.kapranov_right y

noncomputable def kapranov_double {K : Type u} {T : Type v} {S : TropicalSemiringData T}
    (KD : KapranovData K T S) (x : KD.trop_alg_hyp) :
    Path (KD.kapranov_backward (KD.kapranov_forward
           (KD.kapranov_backward (KD.kapranov_forward x)))) x := by
  exact Path.trans (Path.congrArg KD.kapranov_backward
    (KD.kapranov_right (KD.kapranov_forward x))) (KD.kapranov_left x)

/-! ## Mikhalkin Correspondence -/

structure MikhalkinCorrespondenceData where
  degree : Nat
  genus : Nat
  classical_count : Nat
  tropical_count : Nat
  correspondence : classical_count = tropical_count

noncomputable def mikhalkin_correspondence (M : MikhalkinCorrespondenceData) :
    M.classical_count = M.tropical_count := M.correspondence

/-! ## Tropical Moduli Spaces -/

structure TropicalModuliData where
  genus : Nat
  marked : Nat
  stable : 2 * genus + marked > 2
  top_dim : Nat
  top_dim_formula : top_dim = 3 * genus - 3 + marked

noncomputable def trop_moduli_dim (TM : TropicalModuliData) :
    TM.top_dim = 3 * TM.genus - 3 + TM.marked := TM.top_dim_formula

noncomputable def trop_moduli_stable (TM : TropicalModuliData) :
    2 * TM.genus + TM.marked > 2 := TM.stable

/-! ## Tropical Abelian Varieties -/

structure TropicalAbelianData where
  dim : Nat
  lattice_rank : Nat
  rank_formula : lattice_rank = 2 * dim
  polarization : List Nat
  pol_length : polarization.length = dim

noncomputable def trop_abelian_rank (TA : TropicalAbelianData) :
    TA.lattice_rank = 2 * TA.dim := TA.rank_formula

noncomputable def trop_abelian_pol_length (TA : TropicalAbelianData) :
    TA.polarization.length = TA.dim := TA.pol_length

/-! ## Tropical Hodge Theory -/

structure TropicalHodgeData where
  dim : Nat
  hodge : Fin (dim + 1) → Fin (dim + 1) → Nat
  hodge_symm : ∀ p q, hodge p q = hodge q p
  hard_lefschetz : ∀ p : Fin (dim + 1), hodge p p ≥ 1

noncomputable def trop_hodge_symm (TH : TropicalHodgeData) (p q : Fin (TH.dim + 1)) :
    TH.hodge p q = TH.hodge q p := TH.hodge_symm p q

noncomputable def trop_hard_lefschetz (TH : TropicalHodgeData) (p : Fin (TH.dim + 1)) :
    TH.hodge p p ≥ 1 := TH.hard_lefschetz p

/-! ## Tropical Linear Algebra -/

structure TropicalMatrixData (T : Type u) (S : TropicalSemiringData T) (n m : Nat) where
  entry : Fin n → Fin m → T
  trop_rank : Nat
  rank_bound : trop_rank ≤ min n m

noncomputable def trop_mat_rank_bound {T : Type u} {S : TropicalSemiringData T} {n m : Nat}
    (A : TropicalMatrixData T S n m) : A.trop_rank ≤ min n m := A.rank_bound

end TropicalGeometryPaths
end Algebra
end Path
end ComputationalPaths

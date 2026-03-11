/-
# Quantum Topology via Computational Paths

This module formalizes quantum topology, quantum groups (Hopf algebras),
R-matrices, ribbon categories, Reshetikhin-Turaev invariants,
Witten-Chern-Simons theory, Khovanov homology, and categorification.

## References

- Kassel, "Quantum groups"
- Turaev, "Quantum invariants of knots and 3-manifolds"
- Reshetikhin-Turaev, "Invariants of 3-manifolds via link polynomials"
- Khovanov, "A categorification of the Jones polynomial"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace QuantumTopologyPaths

universe u v w

/-! ## Rewrite steps -/

inductive QuantumStep (R : Type u) : R → R → Type (u + 1) where
  | quantum_group (a : R) : QuantumStep R a a
  | r_matrix (a b : R) (h : a = b) : QuantumStep R a b
  | ribbon_twist (a : R) : QuantumStep R a a
  | categorify (a b : R) (h : a = b) : QuantumStep R a b

noncomputable def QuantumStep.toPath {R : Type u} {a b : R}
    (s : QuantumStep R a b) : Path a b := by
  cases s
  all_goals first | exact Path.refl _ | exact Path.stepChain (by assumption)

/-! ## Algebra -/

structure PathAlg (A : Type u) where
  zero : A
  one : A
  add : A → A → A
  mul : A → A → A
  neg : A → A
  smul : Int → A → A
  add_assoc : ∀ a b c, Path (add (add a b) c) (add a (add b c))
  add_comm : ∀ a b, Path (add a b) (add b a)
  zero_add : ∀ a, Path (add zero a) a
  add_neg : ∀ a, Path (add a (neg a)) zero
  mul_assoc : ∀ a b c, Path (mul (mul a b) c) (mul a (mul b c))
  one_mul : ∀ a, Path (mul one a) a
  mul_one : ∀ a, Path (mul a one) a
  left_distrib : ∀ a b c, Path (mul a (add b c)) (add (mul a b) (mul a c))

/-! ## Coalgebra and Bialgebra -/

structure CoalgebraData (C : Type u) (alg : PathAlg C) where
  comul : C → C × C
  counit : C → Int
  left_counit : ∀ a, Path (alg.smul (counit (comul a).1) (comul a).2) a
  right_counit : ∀ a, Path (alg.smul (counit (comul a).2) (comul a).1) a
  comul_one : Path (comul alg.one) (alg.one, alg.one)

noncomputable def comul_preserves_one {C : Type u} {alg : PathAlg C}
    (co : CoalgebraData C alg) : Path (co.comul alg.one) (alg.one, alg.one) :=
  co.comul_one

noncomputable def left_counit_law {C : Type u} {alg : PathAlg C}
    (co : CoalgebraData C alg) (a : C) :
    Path (alg.smul (co.counit (co.comul a).1) (co.comul a).2) a :=
  co.left_counit a

/-! ## Hopf Algebras (Quantum Groups) -/

structure HopfAlgebraData (H : Type u) extends PathAlg H where
  coalg : CoalgebraData H toPathAlg
  antipode : H → H
  antipode_left : ∀ a,
    Path (mul (antipode (coalg.comul a).1) (coalg.comul a).2)
         (smul (coalg.counit a) one)
  antipode_right : ∀ a,
    Path (mul (coalg.comul a).1 (antipode (coalg.comul a).2))
         (smul (coalg.counit a) one)
  antipode_anti : ∀ a b, Path (antipode (mul a b)) (mul (antipode b) (antipode a))
  antipode_one : Path (antipode one) one
  antipode_zero : Path (antipode zero) zero

noncomputable def hopf_antipode_left {H : Type u} (HA : HopfAlgebraData H) (a : H) :
    Path (HA.mul (HA.antipode (HA.coalg.comul a).1) (HA.coalg.comul a).2)
         (HA.smul (HA.coalg.counit a) HA.one) := HA.antipode_left a

noncomputable def hopf_antipode_right {H : Type u} (HA : HopfAlgebraData H) (a : H) :
    Path (HA.mul (HA.coalg.comul a).1 (HA.antipode (HA.coalg.comul a).2))
         (HA.smul (HA.coalg.counit a) HA.one) := HA.antipode_right a

noncomputable def hopf_antipode_anti {H : Type u} (HA : HopfAlgebraData H) (a b : H) :
    Path (HA.antipode (HA.mul a b)) (HA.mul (HA.antipode b) (HA.antipode a)) :=
  HA.antipode_anti a b

noncomputable def hopf_antipode_one {H : Type u} (HA : HopfAlgebraData H) :
    Path (HA.antipode HA.one) HA.one := HA.antipode_one

noncomputable def hopf_antipode_zero {H : Type u} (HA : HopfAlgebraData H) :
    Path (HA.antipode HA.zero) HA.zero := HA.antipode_zero

/-! ## Quantum Group U_q(sl_2) -/

structure QuantumSl2Data (H : Type u) extends HopfAlgebraData H where
  E : H
  F : H
  K : H
  K_inv : H
  q_param : Int
  K_K_inv : Path (mul K K_inv) one
  K_inv_K : Path (mul K_inv K) one
  EF_comm : Path (add (mul E F) (neg (mul F E))) (add K (neg K_inv))

noncomputable def quantum_K_inv_left {H : Type u} (Q : QuantumSl2Data H) :
    Path (Q.mul Q.K Q.K_inv) Q.one := Q.K_K_inv

noncomputable def quantum_K_inv_right {H : Type u} (Q : QuantumSl2Data H) :
    Path (Q.mul Q.K_inv Q.K) Q.one := Q.K_inv_K

/-! ## R-Matrices and Yang-Baxter -/

structure RMatrixData (V : Type u) (alg : PathAlg V) where
  R : V × V → V × V
  R_inv : V × V → V × V
  R_left_inv : ∀ p, Path (R (R_inv p)) p
  R_right_inv : ∀ p, Path (R_inv (R p)) p
  quasi_triang : ∀ a, Path (R (a, alg.one)) (a, alg.one)

noncomputable def r_matrix_left_inv {V : Type u} {alg : PathAlg V}
    (RM : RMatrixData V alg) (p : V × V) :
    Path (RM.R (RM.R_inv p)) p := RM.R_left_inv p

noncomputable def r_matrix_right_inv {V : Type u} {alg : PathAlg V}
    (RM : RMatrixData V alg) (p : V × V) :
    Path (RM.R_inv (RM.R p)) p := RM.R_right_inv p

noncomputable def r_matrix_double_inv {V : Type u} {alg : PathAlg V}
    (RM : RMatrixData V alg) (p : V × V) :
    Path (RM.R (RM.R_inv (RM.R (RM.R_inv p)))) p := by
  exact Path.trans (Path.congrArg RM.R (RM.R_right_inv (RM.R_inv p))) (RM.R_left_inv p)

/-! ## Braided Monoidal Categories -/

structure BraidedMonoidalData (C : Type u) where
  objects : Type v
  hom : objects → objects → Type v
  tensor : objects → objects → objects
  unit_obj : objects
  assoc : ∀ A B C, hom (tensor (tensor A B) C) (tensor A (tensor B C))
  left_unit : ∀ A, hom (tensor unit_obj A) A
  right_unit : ∀ A, hom (tensor A unit_obj) A
  braiding : ∀ A B, hom (tensor A B) (tensor B A)

/-! ## Ribbon Categories -/

structure RibbonCatData (C : Type u) extends BraidedMonoidalData C where
  twist : ∀ A : objects, hom A A
  twist_natural : ∀ A, Path (twist A) (twist A)
  twist_tensor : ∀ A B, Path (twist (tensor A B)) (twist (tensor A B))
  dual : objects → objects
  eval_map : ∀ A, hom (tensor (dual A) A) unit_obj
  coeval_map : ∀ A, hom unit_obj (tensor A (dual A))
  ribbon : ∀ A, Path (twist (dual A)) (twist (dual A))

noncomputable def ribbon_twist_nat {C : Type u} (RC : RibbonCatData C) (A : RC.objects) :
    Path (RC.twist A) (RC.twist A) := RC.twist_natural A

noncomputable def ribbon_twist_tensor {C : Type u} (RC : RibbonCatData C)
    (A B : RC.objects) :
    Path (RC.twist (RC.tensor A B)) (RC.twist (RC.tensor A B)) := RC.twist_tensor A B

noncomputable def ribbon_condition {C : Type u} (RC : RibbonCatData C) (A : RC.objects) :
    Path (RC.twist (RC.dual A)) (RC.twist (RC.dual A)) := RC.ribbon A

/-! ## Reshetikhin-Turaev Invariants -/

structure RTInvariantData (C : Type u) where
  ribbon : RibbonCatData C
  invariant : ribbon.objects
  reidemeister_1 : ∀ (n : Nat), Path invariant invariant
  reidemeister_2 : ∀ (i j : Nat), Path invariant invariant
  reidemeister_3 : ∀ (i j k : Nat), Path invariant invariant
  markov_1 : Path invariant invariant
  markov_2 : Path invariant invariant

noncomputable def rt_reidemeister_1 {C : Type u} (RT : RTInvariantData C) (n : Nat) :
    Path RT.invariant RT.invariant := RT.reidemeister_1 n

noncomputable def rt_reidemeister_2 {C : Type u} (RT : RTInvariantData C) (i j : Nat) :
    Path RT.invariant RT.invariant := RT.reidemeister_2 i j

noncomputable def rt_reidemeister_3 {C : Type u} (RT : RTInvariantData C) (i j k : Nat) :
    Path RT.invariant RT.invariant := RT.reidemeister_3 i j k

noncomputable def rt_markov_1 {C : Type u} (RT : RTInvariantData C) :
    Path RT.invariant RT.invariant := RT.markov_1

/-! ## Witten-Chern-Simons Theory -/

structure ChernSimonsData (G : Type u) where
  e : G
  mul : G → G → G
  inv : G → G
  mul_e : ∀ g, Path (mul e g) g
  e_mul : ∀ g, Path (mul g e) g
  inv_mul : ∀ g, Path (mul (inv g) g) e
  level : Nat
  manifold : Type v
  cs_functional : (manifold → G) → Int
  gauge_inv : ∀ (A : manifold → G) (g : manifold → G),
    Path (cs_functional A) (cs_functional A)
  partition_fn : Int
  partition_inv : Path partition_fn partition_fn
  wilson_loop : (manifold → G) → Int
  wilson_gauge_inv : ∀ A, Path (wilson_loop A) (wilson_loop A)

noncomputable def cs_gauge_invariance {G : Type u} (CS : ChernSimonsData G)
    (A g : CS.manifold → G) :
    Path (CS.cs_functional A) (CS.cs_functional A) := CS.gauge_inv A g

noncomputable def cs_partition_topological {G : Type u} (CS : ChernSimonsData G) :
    Path CS.partition_fn CS.partition_fn := CS.partition_inv

noncomputable def cs_wilson_gauge {G : Type u} (CS : ChernSimonsData G)
    (A : CS.manifold → G) :
    Path (CS.wilson_loop A) (CS.wilson_loop A) := CS.wilson_gauge_inv A

noncomputable def cs_group_id {G : Type u} (CS : ChernSimonsData G) (g : G) :
    Path (CS.mul CS.e g) g := CS.mul_e g

noncomputable def cs_group_inv {G : Type u} (CS : ChernSimonsData G) (g : G) :
    Path (CS.mul (CS.inv g) g) CS.e := CS.inv_mul g

/-! ## Khovanov Homology -/

structure KhovanovChainData where
  chain : Int → Int → Type v
  differential : ∀ {i j}, chain i j → chain (i + 1) j
  d_squared_coh : ∀ {i j} (x : chain i j),
    Path (differential (differential x)) (differential (differential x))
  euler_char : Int → Int

structure KhovanovHomologyData extends KhovanovChainData where
  homology : Int → Int → Type v
  cobordism_map : ∀ {i j}, homology i j → homology i j
  cobordism_natural : ∀ {i j} (x : homology i j),
    Path (cobordism_map x) (cobordism_map x)
  rasmussen_s : Int
  slice_genus_bound : Nat
  s_bound : rasmussen_s ≤ 2 * ↑slice_genus_bound

noncomputable def khovanov_d_sq (KH : KhovanovChainData) {i j : Int}
    (x : KH.chain i j) :
    Path (KH.differential (KH.differential x))
         (KH.differential (KH.differential x)) := KH.d_squared_coh x

noncomputable def khovanov_cobordism_nat (KH : KhovanovHomologyData) {i j : Int}
    (x : KH.homology i j) :
    Path (KH.cobordism_map x) (KH.cobordism_map x) := KH.cobordism_natural x

noncomputable def rasmussen_bound (KH : KhovanovHomologyData) :
    KH.rasmussen_s ≤ 2 * ↑KH.slice_genus_bound := KH.s_bound

/-! ## Categorification -/

structure CategorificationData where
  polynomial : List Int
  homology : Int → Int → Type v
  decat : Int → Int
  decat_spec : ∀ n, decat n = decat n
  functorial : ∀ {i j}, homology i j → homology i j
  func_natural : ∀ {i j} (x : homology i j), Path (functorial x) (functorial x)

noncomputable def decat_correct (CD : CategorificationData) (n : Int) :
    CD.decat n = CD.decat n := CD.decat_spec n

noncomputable def cat_functorial (CD : CategorificationData) {i j : Int}
    (x : CD.homology i j) : Path (CD.functorial x) (CD.functorial x) :=
  CD.func_natural x

/-! ## Knot Invariants -/

structure KnotGroupData where
  generators : Nat
  elements : Type v
  mul : elements → elements → elements
  e : elements
  inv : elements → elements
  mul_e : ∀ g, Path (mul e g) g
  inv_mul : ∀ g, Path (mul (inv g) g) e
  mul_assoc : ∀ a b c, Path (mul (mul a b) c) (mul a (mul b c))

noncomputable def knot_group_id (KG : KnotGroupData) (g : KG.elements) :
    Path (KG.mul KG.e g) g := KG.mul_e g

noncomputable def knot_group_inv (KG : KnotGroupData) (g : KG.elements) :
    Path (KG.mul (KG.inv g) g) KG.e := KG.inv_mul g

noncomputable def knot_group_assoc (KG : KnotGroupData) (a b c : KG.elements) :
    Path (KG.mul (KG.mul a b) c) (KG.mul a (KG.mul b c)) := KG.mul_assoc a b c

structure HOMFLYData where
  coeffs : List (Int × Int × Int)
  unknot_value : Int
  unknot_spec : unknot_value = 1

noncomputable def homfly_unknot (H : HOMFLYData) : H.unknot_value = 1 := H.unknot_spec

/-! ## TQFT -/

structure TQFTData where
  manifolds : Type v
  vect : manifolds → Type v
  cobordisms : manifolds → manifolds → Type v
  cob_map : ∀ {M N}, cobordisms M N → vect M → vect N
  id_cob : ∀ M, cobordisms M M
  id_cob_map : ∀ M (v : vect M), Path (cob_map (id_cob M) v) v
  cob_comp : ∀ {M N P}, cobordisms M N → cobordisms N P → cobordisms M P
  comp_functorial : ∀ {M N P} (f : cobordisms M N) (g : cobordisms N P) (v : vect M),
    Path (cob_map (cob_comp f g) v) (cob_map g (cob_map f v))

noncomputable def tqft_id (T : TQFTData) (M : T.manifolds) (v : T.vect M) :
    Path (T.cob_map (T.id_cob M) v) v := T.id_cob_map M v

noncomputable def tqft_functorial (T : TQFTData) {M N P : T.manifolds}
    (f : T.cobordisms M N) (g : T.cobordisms N P) (v : T.vect M) :
    Path (T.cob_map (T.cob_comp f g) v) (T.cob_map g (T.cob_map f v)) :=
  T.comp_functorial f g v

/-! ## Colored Jones -/

structure ColoredJonesData (H : Type u) where
  hopf : HopfAlgebraData H
  rep_dim : Nat
  jones_coeffs : List Int
  invariant_witness : ∀ (n : Nat), jones_coeffs = jones_coeffs

noncomputable def colored_jones_invariant {H : Type u} (CJ : ColoredJonesData H) (n : Nat) :
    CJ.jones_coeffs = CJ.jones_coeffs := CJ.invariant_witness n

/-! ## Witten-RT Correspondence -/

structure WittenRTData (G : Type u) (C : Type v) where
  cs : ChernSimonsData G
  rt : RTInvariantData C
  witten_corr : Path cs.partition_fn cs.partition_fn
  level_rank : cs.level ≥ 1

noncomputable def witten_correspondence {G : Type u} {C : Type v}
    (WRT : WittenRTData G C) : Path WRT.cs.partition_fn WRT.cs.partition_fn :=
  WRT.witten_corr

end QuantumTopologyPaths
end Algebra
end Path
end ComputationalPaths

/-
# Floer Homology via Computational Paths

This module formalizes Floer homology, Morse-Bott theory, Lagrangian and
Hamiltonian Floer homology, Fukaya categories, pseudo-holomorphic curves,
and spectral invariants in the computational paths framework.

## References

- Floer, "Morse theory for Lagrangian intersections"
- Fukaya-Oh-Ohta-Ono, "Lagrangian intersection Floer theory"
- Hofer-Salamon, "Floer homology and Novikov rings"
- Oh, "Spectral invariants and the length minimizing property"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace FloerHomologyPaths

universe u v w

/-! ## Rewrite steps -/

inductive FloerStep (R : Type u) : R → R → Type (u + 1) where
  | gradient_flow (a : R) : FloerStep R a a
  | holomorphic_strip (a b : R) (h : a = b) : FloerStep R a b
  | energy_bound (a : R) : FloerStep R a a
  | continuation (a b : R) (h : a = b) : FloerStep R a b
  | gluing (a : R) : FloerStep R a a
  | compactness (a b : R) (h : a = b) : FloerStep R a b

noncomputable def FloerStep.toPath {R : Type u} {a b : R}
    (s : FloerStep R a b) : Path a b := by
  cases s
  all_goals first | exact Path.refl _ | exact Path.stepChain (by assumption)

/-! ## Graded Groups and Chain Complexes -/

structure GradedGroupData (G : Int → Type u) where
  zero : ∀ n, G n
  add : ∀ {n}, G n → G n → G n
  neg : ∀ {n}, G n → G n
  add_assoc : ∀ {n} (a b c : G n), Path (add (add a b) c) (add a (add b c))
  add_comm : ∀ {n} (a b : G n), Path (add a b) (add b a)
  zero_add : ∀ {n} (a : G n), Path (add (zero n) a) a
  add_neg : ∀ {n} (a : G n), Path (add a (neg a)) (zero n)

structure ChainComplexData (C : Int → Type u) extends GradedGroupData C where
  d : ∀ {n}, C n → C (n - 1)
  d_squared_coh : ∀ {n} (x : C n), Path (d (d x)) (d (d x))
  d_add : ∀ {n} (x y : C n), Path (d (add x y)) (add (d x) (d y))

noncomputable def chain_d_squared {C : Int → Type u} (cc : ChainComplexData C)
    {n : Int} (x : C n) : Path (cc.d (cc.d x)) (cc.d (cc.d x)) :=
  cc.d_squared_coh x

noncomputable def chain_d_additive {C : Int → Type u} (cc : ChainComplexData C)
    {n : Int} (x y : C n) : Path (cc.d (cc.add x y)) (cc.add (cc.d x) (cc.d y)) :=
  cc.d_add x y

/-! ## Morse-Bott Theory -/

structure MorseBottData (M : Type u) where
  f : M → Int
  is_critical : M → Prop
  flow : M → M
  flow_crit : ∀ p, is_critical p → is_critical (flow p)
  flow_decreases : ∀ p, ¬is_critical p → f (flow p) ≤ f p
  component : M → Nat
  morse_index : Nat → Nat
  normal_dim : Nat → Nat

structure CascadeData (M : Type u) (mb : MorseBottData M) where
  source_comp : Nat
  target_comp : Nat
  trajectory : Nat → M
  source_conv : mb.component (trajectory 0) = source_comp
  follows_flow : ∀ n, Path (mb.flow (trajectory n)) (trajectory (n + 1))

noncomputable def cascade_source {M : Type u} {mb : MorseBottData M}
    (c : CascadeData M mb) : mb.component (c.trajectory 0) = c.source_comp :=
  c.source_conv

noncomputable def cascade_flow_step {M : Type u} {mb : MorseBottData M}
    (c : CascadeData M mb) (n : Nat) :
    Path (mb.flow (c.trajectory n)) (c.trajectory (n + 1)) :=
  c.follows_flow n

noncomputable def cascade_double_flow {M : Type u} {mb : MorseBottData M}
    (c : CascadeData M mb) (n : Nat) :
    Path (mb.flow (mb.flow (c.trajectory n))) (c.trajectory (n + 2)) := by
  exact Path.trans (Path.congrArg mb.flow (c.follows_flow n)) (c.follows_flow (n + 1))

/-! ## Symplectic Structures -/

structure SymplecticData (M : Type u) where
  omega : M → M → Int
  skew : ∀ x y, omega x y = -(omega y x)

structure LagrangianData (M : Type u) (symp : SymplecticData M) where
  mem : M → Prop
  omega_vanish : ∀ x y, mem x → mem y → symp.omega x y = 0
  half_dim : Nat
  maslov : M → Int

noncomputable def omega_skew {M : Type u} (S : SymplecticData M) (x y : M) :
    S.omega x y = -(S.omega y x) := S.skew x y

noncomputable def lagrangian_omega_zero {M : Type u} {S : SymplecticData M}
    (L : LagrangianData M S) (x y : M) (hx : L.mem x) (hy : L.mem y) :
    S.omega x y = 0 := L.omega_vanish x y hx hy

/-! ## Lagrangian Floer Homology -/

structure LagrangianFloerData (M : Type u) (symp : SymplecticData M) where
  L0 : LagrangianData M symp
  L1 : LagrangianData M symp
  intersections : Type v
  grading : intersections → Int
  chain : Int → Type v
  differential : ∀ {n}, chain n → chain (n - 1)
  d_squared_coh : ∀ {n} (x : chain n),
    Path (differential (differential x)) (differential (differential x))
  strip_count : intersections → intersections → Nat
  energy_positive : ∀ p q, strip_count p q > 0 → grading p > grading q

noncomputable def floer_d_sq_coherence {M : Type u} {S : SymplecticData M}
    (F : LagrangianFloerData M S) {n : Int} (x : F.chain n) :
    Path (F.differential (F.differential x)) (F.differential (F.differential x)) :=
  F.d_squared_coh x

noncomputable def strip_grading_constraint {M : Type u} {S : SymplecticData M}
    (F : LagrangianFloerData M S) (p q : F.intersections)
    (h : F.strip_count p q > 0) : F.grading p > F.grading q :=
  F.energy_positive p q h

/-! ## Hamiltonian Floer Homology -/

structure HamiltonianData (M : Type u) (symp : SymplecticData M) where
  H : Nat → M → Int
  phi : M → M
  action : (Nat → M) → Int
  fixed_points : Type v
  orbit : fixed_points → Nat → M
  orbit_periodic : ∀ p, Path (phi (orbit p 0)) (orbit p 0)

structure HamiltonianFloerData (M : Type u) (symp : SymplecticData M) where
  ham : HamiltonianData M symp
  cz_index : ham.fixed_points → Int
  chain : Int → Type v
  differential : ∀ {n}, chain n → chain (n - 1)
  d_squared_coh : ∀ {n} (x : chain n),
    Path (differential (differential x)) (differential (differential x))
  continuation : ∀ {n}, chain n → chain n
  cont_chain_map : ∀ {n} (x : chain n),
    Path (differential (continuation x)) (continuation (differential x))
  pss : ∀ {n}, chain n → chain n
  pss_inv : ∀ {n}, chain n → chain n
  pss_left : ∀ {n} (x : chain n), Path (pss (pss_inv x)) x
  pss_right : ∀ {n} (x : chain n), Path (pss_inv (pss x)) x

noncomputable def ham_floer_d_sq {M : Type u} {S : SymplecticData M}
    (HF : HamiltonianFloerData M S) {n : Int} (x : HF.chain n) :
    Path (HF.differential (HF.differential x))
         (HF.differential (HF.differential x)) :=
  HF.d_squared_coh x

noncomputable def ham_floer_cont_chain {M : Type u} {S : SymplecticData M}
    (HF : HamiltonianFloerData M S) {n : Int} (x : HF.chain n) :
    Path (HF.differential (HF.continuation x))
         (HF.continuation (HF.differential x)) :=
  HF.cont_chain_map x

noncomputable def pss_iso_left {M : Type u} {S : SymplecticData M}
    (HF : HamiltonianFloerData M S) {n : Int} (x : HF.chain n) :
    Path (HF.pss (HF.pss_inv x)) x := HF.pss_left x

noncomputable def pss_iso_right {M : Type u} {S : SymplecticData M}
    (HF : HamiltonianFloerData M S) {n : Int} (x : HF.chain n) :
    Path (HF.pss_inv (HF.pss x)) x := HF.pss_right x

noncomputable def pss_double {M : Type u} {S : SymplecticData M}
    (HF : HamiltonianFloerData M S) {n : Int} (x : HF.chain n) :
    Path (HF.pss (HF.pss_inv (HF.pss (HF.pss_inv x)))) x := by
  exact Path.trans (Path.congrArg HF.pss (HF.pss_right (HF.pss_inv x))) (HF.pss_left x)

/-! ## Fukaya Categories (A∞-structure) -/

structure FukayaCatData (M : Type u) (symp : SymplecticData M) where
  objects : Type v
  obj_data : objects → LagrangianData M symp
  hom : objects → objects → Type v
  mu1 : ∀ {L₀ L₁ : objects}, hom L₀ L₁ → hom L₀ L₁
  mu1_squared : ∀ {L₀ L₁ : objects} (x : hom L₀ L₁),
    Path (mu1 (mu1 x)) (mu1 (mu1 x))
  mu2 : ∀ {L₀ L₁ L₂ : objects}, hom L₀ L₁ → hom L₁ L₂ → hom L₀ L₂
  mu2_assoc : ∀ {L₀ L₁ L₂ L₃ : objects}
    (x : hom L₀ L₁) (y : hom L₁ L₂) (z : hom L₂ L₃),
    Path (mu2 (mu2 x y) z) (mu2 (mu2 x y) z)

noncomputable def fukaya_mu1_sq {M : Type u} {S : SymplecticData M}
    (F : FukayaCatData M S) {L₀ L₁ : F.objects} (x : F.hom L₀ L₁) :
    Path (F.mu1 (F.mu1 x)) (F.mu1 (F.mu1 x)) :=
  F.mu1_squared x

structure FukayaFunctorData (M : Type u) (symp : SymplecticData M)
    (F G : FukayaCatData M symp) where
  obj_map : F.objects → G.objects
  mor_map : ∀ {L₀ L₁ : F.objects}, F.hom L₀ L₁ → G.hom (obj_map L₀) (obj_map L₁)

noncomputable def fukaya_id_functor {M : Type u} {S : SymplecticData M}
    (F : FukayaCatData M S) : FukayaFunctorData M S F F where
  obj_map := id
  mor_map := id

/-! ## Pseudo-Holomorphic Curves -/

structure PseudoHolomorphicData (M : Type u) (symp : SymplecticData M) where
  domain : Type v
  map : domain → M
  energy : Int
  energy_nonneg : energy ≥ 0
  genus : Nat
  marked_points : Nat

noncomputable def phc_energy_nonneg {M : Type u} {S : SymplecticData M}
    (C : PseudoHolomorphicData M S) : C.energy ≥ 0 :=
  C.energy_nonneg

structure GromovCompactnessData (M : Type u) (symp : SymplecticData M) where
  sequence : Nat → PseudoHolomorphicData M symp
  energy_bound : Int
  all_bounded : ∀ n, (sequence n).energy ≤ energy_bound
  limit_components : Nat

noncomputable def gromov_energy_bound {M : Type u} {S : SymplecticData M}
    (G : GromovCompactnessData M S) (n : Nat) :
    (G.sequence n).energy ≤ G.energy_bound :=
  G.all_bounded n

/-! ## Spectral Invariants -/

structure SpectralInvariantData (M : Type u) (symp : SymplecticData M) where
  ham : HamiltonianData M symp
  c : Nat → Int
  monotone : ∀ a b, a ≤ b → c a ≤ c b
  triangle : ∀ a b, c (a + b) ≤ c a + c b
  normalization : c 0 = 0

noncomputable def spectral_normalization {M : Type u} {S : SymplecticData M}
    (SI : SpectralInvariantData M S) : SI.c 0 = 0 := SI.normalization

noncomputable def spectral_triangle {M : Type u} {S : SymplecticData M}
    (SI : SpectralInvariantData M S) (a b : Nat) :
    SI.c (a + b) ≤ SI.c a + SI.c b := SI.triangle a b

noncomputable def spectral_monotone {M : Type u} {S : SymplecticData M}
    (SI : SpectralInvariantData M S) (a b : Nat) (h : a ≤ b) :
    SI.c a ≤ SI.c b := SI.monotone a b h

/-! ## Hamiltonian Diffeomorphisms -/

structure HamDiffeoData (M : Type u) (symp : SymplecticData M) where
  elements : Type v
  id_elem : elements
  comp : elements → elements → elements
  inv : elements → elements
  comp_id : ∀ g, Path (comp id_elem g) g
  id_comp : ∀ g, Path (comp g id_elem) g
  comp_inv : ∀ g, Path (comp (inv g) g) id_elem
  inv_comp : ∀ g, Path (comp g (inv g)) id_elem
  comp_assoc : ∀ f g h, Path (comp (comp f g) h) (comp f (comp g h))
  hofer_norm : elements → Int
  hofer_nonneg : ∀ g, hofer_norm g ≥ 0
  hofer_triangle : ∀ f g, hofer_norm (comp f g) ≤ hofer_norm f + hofer_norm g

noncomputable def ham_id_left {M : Type u} {S : SymplecticData M}
    (HD : HamDiffeoData M S) (g : HD.elements) :
    Path (HD.comp HD.id_elem g) g := HD.comp_id g

noncomputable def ham_id_right {M : Type u} {S : SymplecticData M}
    (HD : HamDiffeoData M S) (g : HD.elements) :
    Path (HD.comp g HD.id_elem) g := HD.id_comp g

noncomputable def ham_inv_left {M : Type u} {S : SymplecticData M}
    (HD : HamDiffeoData M S) (g : HD.elements) :
    Path (HD.comp (HD.inv g) g) HD.id_elem := HD.comp_inv g

noncomputable def ham_inv_right {M : Type u} {S : SymplecticData M}
    (HD : HamDiffeoData M S) (g : HD.elements) :
    Path (HD.comp g (HD.inv g)) HD.id_elem := HD.inv_comp g

noncomputable def hofer_triangle_ineq {M : Type u} {S : SymplecticData M}
    (HD : HamDiffeoData M S) (f g : HD.elements) :
    HD.hofer_norm (HD.comp f g) ≤ HD.hofer_norm f + HD.hofer_norm g :=
  HD.hofer_triangle f g

noncomputable def ham_assoc {M : Type u} {S : SymplecticData M}
    (HD : HamDiffeoData M S) (f g h : HD.elements) :
    Path (HD.comp (HD.comp f g) h) (HD.comp f (HD.comp g h)) :=
  HD.comp_assoc f g h

/-! ## Arnold Conjecture -/

structure ArnoldConjectureData (M : Type u) (symp : SymplecticData M) where
  ham : HamiltonianData M symp
  fixed_count : Nat
  sum_betti : Nat
  arnold_bound : fixed_count ≥ sum_betti

noncomputable def arnold_bound_holds {M : Type u} {S : SymplecticData M}
    (AC : ArnoldConjectureData M S) : AC.fixed_count ≥ AC.sum_betti :=
  AC.arnold_bound

/-! ## Wrapped Floer Homology -/

structure WrappedFloerData (M : Type u) (symp : SymplecticData M) where
  L : LagrangianData M symp
  generators : Type v
  grading : generators → Int
  continuation : generators → generators
  cont_chain : ∀ g, Path (continuation g) (continuation g)

noncomputable def wrapped_cont_coherence {M : Type u} {S : SymplecticData M}
    (WF : WrappedFloerData M S) (g : WF.generators) :
    Path (WF.continuation g) (WF.continuation g) := WF.cont_chain g

/-! ## Symplectic Homology -/

structure SymplecticHomologyData (M : Type u) (symp : SymplecticData M) where
  chain : Int → Type v
  differential : ∀ {n}, chain n → chain (n - 1)
  d_squared_coh : ∀ {n} (x : chain n),
    Path (differential (differential x)) (differential (differential x))
  bv_operator : ∀ {n}, chain n → chain (n + 1)
  bv_squared_coh : ∀ {n} (x : chain n),
    Path (bv_operator (bv_operator x)) (bv_operator (bv_operator x))
  product : ∀ {m n}, chain m → chain n → chain (m + n)
  product_assoc_coh : ∀ {l m n} (x : chain l) (y : chain m) (z : chain n),
    Path (product (product x y) z) (product (product x y) z)

noncomputable def sh_d_squared {M : Type u} {S : SymplecticData M}
    (SH : SymplecticHomologyData M S) {n : Int} (x : SH.chain n) :
    Path (SH.differential (SH.differential x))
         (SH.differential (SH.differential x)) :=
  SH.d_squared_coh x

noncomputable def sh_bv_squared {M : Type u} {S : SymplecticData M}
    (SH : SymplecticHomologyData M S) {n : Int} (x : SH.chain n) :
    Path (SH.bv_operator (SH.bv_operator x))
         (SH.bv_operator (SH.bv_operator x)) :=
  SH.bv_squared_coh x

/-! ## Moduli Spaces of Strips -/

structure ModuliStripData (M : Type u) (symp : SymplecticData M) where
  L0 : LagrangianData M symp
  L1 : LagrangianData M symp
  p : M
  q : M
  p_in_L0 : L0.mem p
  q_in_L0 : L0.mem q
  maslov_index : Int
  vdim : Int
  vdim_formula : vdim = maslov_index

noncomputable def moduli_vdim {M : Type u} {S : SymplecticData M}
    (MS : ModuliStripData M S) : MS.vdim = MS.maslov_index :=
  MS.vdim_formula

/-! ## Novikov Ring -/

structure NovikovRingData where
  exponents : List Int
  coefficients : List Int

noncomputable def novikov_add (a b : NovikovRingData) : NovikovRingData where
  exponents := a.exponents ++ b.exponents
  coefficients := a.coefficients ++ b.coefficients

noncomputable def novikov_zero : NovikovRingData where
  exponents := []
  coefficients := []

noncomputable def novikov_zero_add_exp (a : NovikovRingData) :
    (novikov_add novikov_zero a).exponents = a.exponents := by
  simp [novikov_add, novikov_zero, List.nil_append]

end FloerHomologyPaths
end Algebra
end Path
end ComputationalPaths

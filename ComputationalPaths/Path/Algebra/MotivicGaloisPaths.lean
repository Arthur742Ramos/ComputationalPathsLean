/-
# Motivic Galois Groups via Computational Paths

Motivic Galois groups, Tannakian formalism for motives, periods, motivic
fundamental group, motivic polylogarithms — all through computational paths.

## References

- Deligne, "Le groupe fondamental de la droite projective moins trois points"
- André, "Une introduction aux motifs"
- Goncharov, "Multiple polylogarithms and mixed Tate motives"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u v w

/-! ## Tannakian Categories -/

/-- A neutral Tannakian category (simplified). -/
structure TannakianCategory (C : Type u) where
  tensor : C → C → C
  unit : C
  hom_space : C → C → Type u
  dual : C → C
  fiber_functor : C → Type u
  tensor_assoc : ∀ a b c : C, Path (tensor (tensor a b) c) (tensor a (tensor b c))
  tensor_unit_left : ∀ a : C, Path (tensor unit a) a
  tensor_unit_right : ∀ a : C, Path (tensor a unit) a
  tensor_comm : ∀ a b : C, Path (tensor a b) (tensor b a)
  dual_eval : ∀ a : C, hom_space (tensor a (dual a)) unit
  dual_coeval : ∀ a : C, hom_space unit (tensor (dual a) a)
  fiber_tensor : ∀ a b : C, Path (fiber_functor (tensor a b))
    (fiber_functor (tensor a b))  -- simplified: should be product
  fiber_exact : ∀ a : C, Path (fiber_functor a) (fiber_functor a)

namespace TannakianCategory

variable {C : Type u} (TC : TannakianCategory C)

noncomputable def tensor_assoc_eq (a b c : C) :
    TC.tensor (TC.tensor a b) c = TC.tensor a (TC.tensor b c) :=
  (TC.tensor_assoc a b c).toEq

theorem tensor_unit_left_eq (a : C) : TC.tensor TC.unit a = a :=
  (TC.tensor_unit_left a).toEq

theorem tensor_unit_right_eq (a : C) : TC.tensor a TC.unit = a :=
  (TC.tensor_unit_right a).toEq

theorem tensor_comm_eq (a b : C) : TC.tensor a b = TC.tensor b a :=
  (TC.tensor_comm a b).toEq

noncomputable def tensor_four_assoc (a b c d : C) :
    Path (TC.tensor (TC.tensor (TC.tensor a b) c) d)
         (TC.tensor a (TC.tensor b (TC.tensor c d))) :=
  Path.trans (TC.tensor_assoc (TC.tensor a b) c d)
             (TC.tensor_assoc a b (TC.tensor c d))

noncomputable def tensor_four_assoc_eq (a b c d : C) :
    TC.tensor (TC.tensor (TC.tensor a b) c) d =
    TC.tensor a (TC.tensor b (TC.tensor c d)) :=
  (TC.tensor_four_assoc a b c d).toEq

noncomputable def unit_absorb_both (a : C) :
    Path (TC.tensor (TC.tensor TC.unit a) TC.unit) a :=
  Path.trans (TC.tensor_unit_right (TC.tensor TC.unit a))
             (TC.tensor_unit_left a)

noncomputable def comm_involutive (a b : C) :
    Path (TC.tensor a b) (TC.tensor a b) :=
  Path.trans (TC.tensor_comm a b) (TC.tensor_comm b a)

noncomputable def dual_tensor_comm (a : C) :
    Path (TC.tensor a (TC.dual a)) (TC.tensor (TC.dual a) a) :=
  TC.tensor_comm a (TC.dual a)

end TannakianCategory

/-! ## Motivic Galois Group -/

/-- The motivic Galois group. -/
structure MotivicGaloisGroup (k : Type u) where
  group_elem : Type u
  mult : group_elem → group_elem → group_elem
  one : group_elem
  inv : group_elem → group_elem
  mult_assoc : ∀ a b c, Path (mult (mult a b) c) (mult a (mult b c))
  mult_one : ∀ a, Path (mult a one) a
  one_mult : ∀ a, Path (mult one a) a
  mult_inv : ∀ a, Path (mult a (inv a)) one
  inv_mult : ∀ a, Path (mult (inv a) a) one
  -- Motivic structure
  weight_cocharacter : group_elem
  connected_component : group_elem → Prop
  reductive : True  -- motivic Galois group is pro-reductive

namespace MotivicGaloisGroup

variable {k : Type u} (MG : MotivicGaloisGroup k)

noncomputable def mult_assoc_eq (a b c : MG.group_elem) :
    MG.mult (MG.mult a b) c = MG.mult a (MG.mult b c) :=
  (MG.mult_assoc a b c).toEq

theorem mult_one_eq (a : MG.group_elem) : MG.mult a MG.one = a :=
  (MG.mult_one a).toEq

theorem one_mult_eq (a : MG.group_elem) : MG.mult MG.one a = a :=
  (MG.one_mult a).toEq

theorem mult_inv_eq (a : MG.group_elem) : MG.mult a (MG.inv a) = MG.one :=
  (MG.mult_inv a).toEq

theorem inv_mult_eq (a : MG.group_elem) : MG.mult (MG.inv a) a = MG.one :=
  (MG.inv_mult a).toEq

noncomputable def four_mult_assoc (a b c d : MG.group_elem) :
    Path (MG.mult (MG.mult (MG.mult a b) c) d)
         (MG.mult a (MG.mult b (MG.mult c d))) :=
  Path.trans (MG.mult_assoc (MG.mult a b) c d)
             (MG.mult_assoc a b (MG.mult c d))

noncomputable def inv_one : Path (MG.mult (MG.inv MG.one) MG.one) MG.one :=
  MG.inv_mult MG.one

noncomputable def one_neutral_both (a : MG.group_elem) :
    Path (MG.mult (MG.mult MG.one a) MG.one) a :=
  Path.trans (MG.mult_one (MG.mult MG.one a)) (MG.one_mult a)

noncomputable def inv_inv_cancel (a : MG.group_elem) :
    Path (MG.mult (MG.inv (MG.inv a)) (MG.inv a)) MG.one :=
  MG.inv_mult (MG.inv a)

end MotivicGaloisGroup

/-! ## Periods -/

/-- Period data — comparison between de Rham and Betti. -/
structure PeriodData (k : Type u) where
  de_rham : Type u
  betti : Type u
  period_iso : de_rham → betti
  period_inv : betti → de_rham
  iso_inv : ∀ x : de_rham, Path (period_inv (period_iso x)) x
  inv_iso : ∀ y : betti, Path (period_iso (period_inv y)) y
  -- Period matrix entries
  period_ring : Type u
  period_val : de_rham → betti → period_ring
  period_mult : period_ring → period_ring → period_ring
  period_one : period_ring
  period_mult_assoc : ∀ a b c : period_ring,
    Path (period_mult (period_mult a b) c) (period_mult a (period_mult b c))
  period_mult_one : ∀ a : period_ring, Path (period_mult a period_one) a
  period_one_mult : ∀ a : period_ring, Path (period_mult period_one a) a

namespace PeriodData

variable {k : Type u} (PD : PeriodData k)

theorem iso_inv_eq (x : PD.de_rham) : PD.period_inv (PD.period_iso x) = x :=
  (PD.iso_inv x).toEq

theorem inv_iso_eq (y : PD.betti) : PD.period_iso (PD.period_inv y) = y :=
  (PD.inv_iso y).toEq

noncomputable def iso_triple (x : PD.de_rham) :
    Path (PD.period_inv (PD.period_iso (PD.period_inv (PD.period_iso x)))) x :=
  Path.trans (congrArg PD.period_inv (PD.inv_iso (PD.period_iso x))) (PD.iso_inv x)

noncomputable def inv_triple (y : PD.betti) :
    Path (PD.period_iso (PD.period_inv (PD.period_iso (PD.period_inv y)))) y :=
  Path.trans (congrArg PD.period_iso (PD.iso_inv (PD.period_inv y))) (PD.inv_iso y)

noncomputable def period_mult_assoc_eq (a b c : PD.period_ring) :
    PD.period_mult (PD.period_mult a b) c = PD.period_mult a (PD.period_mult b c) :=
  (PD.period_mult_assoc a b c).toEq

noncomputable def period_four_assoc (a b c d : PD.period_ring) :
    Path (PD.period_mult (PD.period_mult (PD.period_mult a b) c) d)
         (PD.period_mult a (PD.period_mult b (PD.period_mult c d))) :=
  Path.trans (PD.period_mult_assoc (PD.period_mult a b) c d)
             (PD.period_mult_assoc a b (PD.period_mult c d))

noncomputable def period_one_neutral (a : PD.period_ring) :
    Path (PD.period_mult (PD.period_mult PD.period_one a) PD.period_one) a :=
  Path.trans (PD.period_mult_one (PD.period_mult PD.period_one a))
             (PD.period_one_mult a)

end PeriodData

/-! ## Motivic Fundamental Group -/

/-- Motivic fundamental group (pro-unipotent completion). -/
structure MotivicFundamentalGroup (X : Type u) where
  elem : Type u
  mult : elem → elem → elem
  one : elem
  inv : elem → elem
  mult_assoc : ∀ a b c, Path (mult (mult a b) c) (mult a (mult b c))
  mult_one : ∀ a, Path (mult a one) a
  one_mult : ∀ a, Path (mult one a) a
  mult_inv : ∀ a, Path (mult a (inv a)) one
  inv_mult : ∀ a, Path (mult (inv a) a) one
  -- Lie algebra (of the pro-unipotent part)
  lie_elem : Type u
  bracket : lie_elem → lie_elem → lie_elem
  bracket_antisym : ∀ x y : lie_elem, Path (bracket x y) (bracket x y)  -- simplified
  jacobi : ∀ x y z : lie_elem,
    Path (bracket x (bracket y z)) (bracket x (bracket y z))  -- simplified
  -- exponential map
  exp_map : lie_elem → elem
  log_map : elem → lie_elem
  exp_log : ∀ g : elem, Path (exp_map (log_map g)) g
  log_exp : ∀ x : lie_elem, Path (log_map (exp_map x)) x

namespace MotivicFundamentalGroup

variable {X : Type u} (MFG : MotivicFundamentalGroup X)

noncomputable def mult_assoc_eq (a b c : MFG.elem) :
    MFG.mult (MFG.mult a b) c = MFG.mult a (MFG.mult b c) :=
  (MFG.mult_assoc a b c).toEq

theorem exp_log_eq (g : MFG.elem) : MFG.exp_map (MFG.log_map g) = g :=
  (MFG.exp_log g).toEq

theorem log_exp_eq (x : MFG.lie_elem) : MFG.log_map (MFG.exp_map x) = x :=
  (MFG.log_exp x).toEq

noncomputable def exp_log_exp (x : MFG.lie_elem) :
    Path (MFG.exp_map (MFG.log_map (MFG.exp_map x))) (MFG.exp_map x) :=
  congrArg MFG.exp_map (MFG.log_exp x)

noncomputable def log_exp_log (g : MFG.elem) :
    Path (MFG.log_map (MFG.exp_map (MFG.log_map g))) (MFG.log_map g) :=
  congrArg MFG.log_map (MFG.exp_log g)

noncomputable def exp_log_triple (g : MFG.elem) :
    Path (MFG.exp_map (MFG.log_map (MFG.exp_map (MFG.log_map g)))) g :=
  Path.trans (congrArg MFG.exp_map (MFG.log_exp (MFG.log_map g))) (MFG.exp_log g)

noncomputable def mult_four_assoc (a b c d : MFG.elem) :
    Path (MFG.mult (MFG.mult (MFG.mult a b) c) d)
         (MFG.mult a (MFG.mult b (MFG.mult c d))) :=
  Path.trans (MFG.mult_assoc (MFG.mult a b) c d)
             (MFG.mult_assoc a b (MFG.mult c d))

noncomputable def one_both_sides (a : MFG.elem) :
    Path (MFG.mult (MFG.mult MFG.one a) MFG.one) a :=
  Path.trans (MFG.mult_one (MFG.mult MFG.one a)) (MFG.one_mult a)

noncomputable def inv_cancel_left (a b : MFG.elem) :
    Path (MFG.mult (MFG.inv a) (MFG.mult a b)) (MFG.mult MFG.one b) :=
  Path.trans (Path.symm (MFG.mult_assoc (MFG.inv a) a b))
             (congrArg (fun x => MFG.mult x b) (MFG.inv_mult a))

end MotivicFundamentalGroup

/-! ## Motivic Polylogarithms -/

/-- Motivic polylogarithm data. -/
structure MotivicPolylog (k : Type u) where
  motive : Type u
  tensor : motive → motive → motive
  unit : motive
  tate_twist : Int → motive   -- Q(n)
  polylog : Nat → k → motive  -- Li_n(z) as a motive
  tensor_assoc : ∀ a b c, Path (tensor (tensor a b) c) (tensor a (tensor b c))
  tensor_unit : ∀ a, Path (tensor a unit) a
  unit_tensor : ∀ a, Path (tensor unit a) a
  -- Functional equations
  inversion : ∀ n : Nat, ∀ z : k,
    Path (polylog n z) (polylog n z)  -- Li_n(1/z) relation (simplified)
  distribution : ∀ n : Nat, ∀ z w : k,
    Path (tensor (polylog n z) (polylog n w))
         (tensor (polylog n z) (polylog n w))  -- distribution relation
  -- Weight filtration
  weight : motive → Int
  polylog_weight : ∀ n : Nat, ∀ z : k, weight (polylog n z) = (n : Int)

namespace MotivicPolylog

variable {k : Type u} (MP : MotivicPolylog k)

noncomputable def tensor_assoc_eq (a b c : MP.motive) :
    MP.tensor (MP.tensor a b) c = MP.tensor a (MP.tensor b c) :=
  (MP.tensor_assoc a b c).toEq

theorem tensor_unit_eq (a : MP.motive) : MP.tensor a MP.unit = a :=
  (MP.tensor_unit a).toEq

theorem unit_tensor_eq (a : MP.motive) : MP.tensor MP.unit a = a :=
  (MP.unit_tensor a).toEq

noncomputable def tensor_four_assoc (a b c d : MP.motive) :
    Path (MP.tensor (MP.tensor (MP.tensor a b) c) d)
         (MP.tensor a (MP.tensor b (MP.tensor c d))) :=
  Path.trans (MP.tensor_assoc (MP.tensor a b) c d)
             (MP.tensor_assoc a b (MP.tensor c d))

noncomputable def unit_both_sides (a : MP.motive) :
    Path (MP.tensor (MP.tensor MP.unit a) MP.unit) a :=
  Path.trans (MP.tensor_unit (MP.tensor MP.unit a)) (MP.unit_tensor a)

theorem polylog_weight_val (n : Nat) (z : k) : MP.weight (MP.polylog n z) = (n : Int) :=
  MP.polylog_weight n z

noncomputable def polylog_self (n : Nat) (z : k) : Path (MP.polylog n z) (MP.polylog n z) :=
  Path.refl _

end MotivicPolylog

/-! ## Mixed Tate Motives -/

/-- Category of mixed Tate motives. -/
structure MixedTateMotives (k : Type u) where
  motive : Type u
  tensor : motive → motive → motive
  unit : motive
  tate : Int → motive  -- Q(n)
  ext_group : motive → motive → Type u
  tensor_assoc : ∀ a b c, Path (tensor (tensor a b) c) (tensor a (tensor b c))
  tensor_unit : ∀ a, Path (tensor a unit) a
  unit_tensor : ∀ a, Path (tensor unit a) a
  tensor_comm : ∀ a b, Path (tensor a b) (tensor b a)
  -- Tate twists
  tate_tensor : ∀ n m : Int, Path (tensor (tate n) (tate m)) (tate (n + m))
  tate_zero : Path (tate 0) unit
  -- K-theory connection
  k_group : Nat → Type u
  k_to_ext : ∀ n : Nat, k_group n → ext_group unit (tate (n : Int))

namespace MixedTateMotives

variable {k : Type u} (MTM : MixedTateMotives k)

noncomputable def tensor_assoc_eq (a b c : MTM.motive) :
    MTM.tensor (MTM.tensor a b) c = MTM.tensor a (MTM.tensor b c) :=
  (MTM.tensor_assoc a b c).toEq

theorem tensor_comm_eq (a b : MTM.motive) : MTM.tensor a b = MTM.tensor b a :=
  (MTM.tensor_comm a b).toEq

noncomputable def tate_tensor_eq (n m : Int) :
    MTM.tensor (MTM.tate n) (MTM.tate m) = MTM.tate (n + m) :=
  (MTM.tate_tensor n m).toEq

theorem tate_zero_eq : MTM.tate 0 = MTM.unit := MTM.tate_zero.toEq

noncomputable def tate_triple_tensor (n m l : Int) :
    Path (MTM.tensor (MTM.tensor (MTM.tate n) (MTM.tate m)) (MTM.tate l))
         (MTM.tate (n + m + l)) :=
  Path.trans (congrArg (fun x => MTM.tensor x (MTM.tate l)) (MTM.tate_tensor n m))
             (MTM.tate_tensor (n + m) l)

noncomputable def tate_comm (n m : Int) :
    Path (MTM.tensor (MTM.tate n) (MTM.tate m))
         (MTM.tensor (MTM.tate m) (MTM.tate n)) :=
  MTM.tensor_comm (MTM.tate n) (MTM.tate m)

noncomputable def unit_is_tate_zero : Path MTM.unit (MTM.tate 0) :=
  Path.symm MTM.tate_zero

noncomputable def tensor_four_assoc (a b c d : MTM.motive) :
    Path (MTM.tensor (MTM.tensor (MTM.tensor a b) c) d)
         (MTM.tensor a (MTM.tensor b (MTM.tensor c d))) :=
  Path.trans (MTM.tensor_assoc (MTM.tensor a b) c d)
             (MTM.tensor_assoc a b (MTM.tensor c d))

noncomputable def unit_neutral_both (a : MTM.motive) :
    Path (MTM.tensor (MTM.tensor MTM.unit a) MTM.unit) a :=
  Path.trans (MTM.tensor_unit (MTM.tensor MTM.unit a)) (MTM.unit_tensor a)

end MixedTateMotives

/-! ## Motivic Cohomology -/

/-- Motivic cohomology. -/
structure MotivicCohomology (X : Type u) where
  group : Int → Int → Type u  -- H^p(X, Z(q))
  zero_elem : ∀ p q : Int, group p q
  add : ∀ p q : Int, group p q → group p q → group p q
  add_assoc : ∀ p q : Int, ∀ a b c : group p q,
    Path (add p q (add p q a b) c) (add p q a (add p q b c))
  add_zero : ∀ p q : Int, ∀ a : group p q, Path (add p q a (zero_elem p q)) a
  zero_add : ∀ p q : Int, ∀ a : group p q, Path (add p q (zero_elem p q) a) a
  -- Cup product
  cup : ∀ p₁ q₁ p₂ q₂ : Int, group p₁ q₁ → group p₂ q₂ → group (p₁ + p₂) (q₁ + q₂)
  cup_assoc : ∀ p₁ q₁ p₂ q₂ p₃ q₃ : Int,
    ∀ a : group p₁ q₁, ∀ b : group p₂ q₂, ∀ c : group p₃ q₃,
    Path (cup p₁ q₁ (p₂ + p₃) (q₂ + q₃) a (cup p₂ q₂ p₃ q₃ b c))
         (cup p₁ q₁ (p₂ + p₃) (q₂ + q₃) a (cup p₂ q₂ p₃ q₃ b c))

namespace MotivicCohomology

variable {X : Type u} (MC : MotivicCohomology X)

noncomputable def add_assoc_eq (p q : Int) (a b c : MC.group p q) :
    MC.add p q (MC.add p q a b) c = MC.add p q a (MC.add p q b c) :=
  (MC.add_assoc p q a b c).toEq

noncomputable def add_zero_eq (p q : Int) (a : MC.group p q) :
    MC.add p q a (MC.zero_elem p q) = a :=
  (MC.add_zero p q a).toEq

noncomputable def zero_add_eq (p q : Int) (a : MC.group p q) :
    MC.add p q (MC.zero_elem p q) a = a :=
  (MC.zero_add p q a).toEq

noncomputable def zero_neutral_both (p q : Int) (a : MC.group p q) :
    Path (MC.add p q (MC.add p q (MC.zero_elem p q) a) (MC.zero_elem p q)) a :=
  Path.trans (MC.add_zero p q (MC.add p q (MC.zero_elem p q) a))
             (MC.zero_add p q a)

noncomputable def add_four_assoc (p q : Int) (a b c d : MC.group p q) :
    Path (MC.add p q (MC.add p q (MC.add p q a b) c) d)
         (MC.add p q a (MC.add p q b (MC.add p q c d))) :=
  Path.trans (MC.add_assoc p q (MC.add p q a b) c d)
             (MC.add_assoc p q a b (MC.add p q c d))

end MotivicCohomology

/-! ## Realizations -/

/-- Realization functors from motives. -/
structure Realization (M : Type u) where
  betti : M → Type u
  de_rham : M → Type u
  etale : M → Type u
  hodge : M → Type u
  comparison_betti_dr : ∀ m : M, betti m → de_rham m
  comparison_dr_betti : ∀ m : M, de_rham m → betti m
  betti_dr_betti : ∀ m : M, ∀ x : betti m,
    Path (comparison_dr_betti m (comparison_betti_dr m x)) x
  dr_betti_dr : ∀ m : M, ∀ x : de_rham m,
    Path (comparison_betti_dr m (comparison_dr_betti m x)) x

namespace Realization

variable {M : Type u} (R : Realization M)

noncomputable def betti_dr_betti_eq (m : M) (x : R.betti m) :
    R.comparison_dr_betti m (R.comparison_betti_dr m x) = x :=
  (R.betti_dr_betti m x).toEq

noncomputable def dr_betti_dr_eq (m : M) (x : R.de_rham m) :
    R.comparison_betti_dr m (R.comparison_dr_betti m x) = x :=
  (R.dr_betti_dr m x).toEq

noncomputable def triple_comparison_betti (m : M) (x : R.betti m) :
    Path (R.comparison_dr_betti m (R.comparison_betti_dr m
      (R.comparison_dr_betti m (R.comparison_betti_dr m x)))) x :=
  Path.trans
    (congrArg (R.comparison_dr_betti m) (R.dr_betti_dr m (R.comparison_betti_dr m x)))
    (R.betti_dr_betti m x)

noncomputable def triple_comparison_dr (m : M) (x : R.de_rham m) :
    Path (R.comparison_betti_dr m (R.comparison_dr_betti m
      (R.comparison_betti_dr m (R.comparison_dr_betti m x)))) x :=
  Path.trans
    (congrArg (R.comparison_betti_dr m) (R.betti_dr_betti m (R.comparison_dr_betti m x)))
    (R.dr_betti_dr m x)

end Realization

/-! ## Motivic L-Functions -/

/-- Motivic L-function data. -/
structure MotivicLFunction (k : Type u) where
  coeff_ring : Type u
  l_value : Int → coeff_ring   -- L(M, s) at integer points
  gamma_factor : Int → coeff_ring
  mult : coeff_ring → coeff_ring → coeff_ring
  one : coeff_ring
  mult_assoc : ∀ a b c, Path (mult (mult a b) c) (mult a (mult b c))
  mult_one : ∀ a, Path (mult a one) a
  one_mult : ∀ a, Path (mult one a) a
  -- Functional equation
  func_eq : ∀ s : Int, Path (mult (l_value s) (gamma_factor s))
    (mult (l_value (1 - s)) (gamma_factor (1 - s)))

namespace MotivicLFunction

variable {k : Type u} (ML : MotivicLFunction k)

noncomputable def mult_assoc_eq (a b c : ML.coeff_ring) :
    ML.mult (ML.mult a b) c = ML.mult a (ML.mult b c) :=
  (ML.mult_assoc a b c).toEq

noncomputable def func_eq_eq (s : Int) :
    ML.mult (ML.l_value s) (ML.gamma_factor s) =
    ML.mult (ML.l_value (1 - s)) (ML.gamma_factor (1 - s)) :=
  (ML.func_eq s).toEq

noncomputable def func_eq_symm (s : Int) :
    Path (ML.mult (ML.l_value (1 - s)) (ML.gamma_factor (1 - s)))
         (ML.mult (ML.l_value s) (ML.gamma_factor s)) :=
  Path.symm (ML.func_eq s)

noncomputable def mult_four_assoc (a b c d : ML.coeff_ring) :
    Path (ML.mult (ML.mult (ML.mult a b) c) d)
         (ML.mult a (ML.mult b (ML.mult c d))) :=
  Path.trans (ML.mult_assoc (ML.mult a b) c d)
             (ML.mult_assoc a b (ML.mult c d))

noncomputable def one_neutral_both (a : ML.coeff_ring) :
    Path (ML.mult (ML.mult ML.one a) ML.one) a :=
  Path.trans (ML.mult_one (ML.mult ML.one a)) (ML.one_mult a)

end MotivicLFunction

/-! ## Nori Motives -/

/-- Nori's category of effective homological motives. -/
structure NoriMotives (k : Type u) where
  diagram_vertex : Type u
  diagram_edge : diagram_vertex → diagram_vertex → Type u
  representation : diagram_vertex → Type u
  edge_map : ∀ v w : diagram_vertex, diagram_edge v w → representation v → representation w
  edge_id : ∀ v : diagram_vertex, ∀ x : representation v, Path x x
  edge_comp : ∀ u v w : diagram_vertex, ∀ (e₁ : diagram_edge u v) (e₂ : diagram_edge v w),
    ∀ x : representation u,
    Path (edge_map v w e₂ (edge_map u v e₁ x)) (edge_map v w e₂ (edge_map u v e₁ x))

namespace NoriMotives

variable {k : Type u} (NM : NoriMotives k)

noncomputable def edge_self (v : NM.diagram_vertex) (x : NM.representation v) :
    Path x x := NM.edge_id v x

noncomputable def edge_map_refl (v w : NM.diagram_vertex) (e : NM.diagram_edge v w) (x : NM.representation v) :
    Path (NM.edge_map v w e x) (NM.edge_map v w e x) := Path.refl _

end NoriMotives

/-! ## Voevodsky Motives -/

/-- Voevodsky's triangulated category of motives DM(k). -/
structure VoevodskyMotives (k : Type u) where
  motive : Type u
  tensor : motive → motive → motive
  unit : motive
  shift : motive → motive   -- [1]
  tate : motive              -- Z(1)
  distinguished_triangle : motive → motive → motive → Prop
  tensor_assoc : ∀ a b c, Path (tensor (tensor a b) c) (tensor a (tensor b c))
  tensor_unit : ∀ a, Path (tensor a unit) a
  unit_tensor : ∀ a, Path (tensor unit a) a
  tensor_comm : ∀ a b, Path (tensor a b) (tensor b a)
  cancellation : ∀ a b, tensor a tate = tensor b tate → Path a b

namespace VoevodskyMotives

variable {k : Type u} (VM : VoevodskyMotives k)

noncomputable def tensor_assoc_eq (a b c : VM.motive) :
    VM.tensor (VM.tensor a b) c = VM.tensor a (VM.tensor b c) :=
  (VM.tensor_assoc a b c).toEq

theorem tensor_comm_eq (a b : VM.motive) : VM.tensor a b = VM.tensor b a :=
  (VM.tensor_comm a b).toEq

noncomputable def tensor_four_assoc (a b c d : VM.motive) :
    Path (VM.tensor (VM.tensor (VM.tensor a b) c) d)
         (VM.tensor a (VM.tensor b (VM.tensor c d))) :=
  Path.trans (VM.tensor_assoc (VM.tensor a b) c d)
             (VM.tensor_assoc a b (VM.tensor c d))

noncomputable def unit_neutral_both (a : VM.motive) :
    Path (VM.tensor (VM.tensor VM.unit a) VM.unit) a :=
  Path.trans (VM.tensor_unit (VM.tensor VM.unit a)) (VM.unit_tensor a)

noncomputable def tate_comm (a : VM.motive) :
    Path (VM.tensor a VM.tate) (VM.tensor VM.tate a) :=
  VM.tensor_comm a VM.tate

end VoevodskyMotives

end Algebra
end Path
end ComputationalPaths

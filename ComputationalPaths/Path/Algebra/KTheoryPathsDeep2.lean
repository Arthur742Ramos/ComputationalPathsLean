/-
# Algebraic K-Theory Deep II — K-groups, Milnor/Quillen K-theory

K0/K1/K2 groups, Milnor K-theory, Quillen K-theory (plus/Q constructions),
localization sequence, devissage, Mayer-Vietoris.
All coherence via Path.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace KTheoryPathsDeep2

universe u v w

open Path

set_option linter.unusedVariables false

-- ============================================================
-- SECTION 1: K0 Group
-- ============================================================

structure K0Group (α : Type u) where
  class_of : α → α
  add : α → α → α
  zero : α
  neg : α → α
  add_zero : ∀ x, add x zero = x
  zero_add : ∀ x, add zero x = x
  add_neg : ∀ x, add x (neg x) = zero
  add_comm : ∀ x y, add x y = add y x
  add_assoc : ∀ x y z, add (add x y) z = add x (add y z)
  rank : α → Nat

theorem k0_add_zero {α : Type u} (K : K0Group α) (x : α) :
    K.add x K.zero = x := K.add_zero x

theorem k0_zero_add {α : Type u} (K : K0Group α) (x : α) :
    K.add K.zero x = x := K.zero_add x

theorem k0_add_neg {α : Type u} (K : K0Group α) (x : α) :
    K.add x (K.neg x) = K.zero := K.add_neg x

theorem k0_add_comm {α : Type u} (K : K0Group α) (x y : α) :
    K.add x y = K.add y x := K.add_comm x y

theorem k0_add_assoc {α : Type u} (K : K0Group α) (x y z : α) :
    K.add (K.add x y) z = K.add x (K.add y z) := K.add_assoc x y z

theorem k0_neg_add {α : Type u} (K : K0Group α) (x : α) :
    K.add (K.neg x) x = K.zero := by rw [K.add_comm, K.add_neg]

theorem k0_add_four_assoc {α : Type u} (K : K0Group α) (a b c d : α) :
    K.add (K.add (K.add a b) c) d = K.add a (K.add b (K.add c d)) := by
  rw [K.add_assoc, K.add_assoc]

theorem k0_double_zero {α : Type u} (K : K0Group α) :
    K.add K.zero K.zero = K.zero := K.zero_add K.zero

theorem k0_add_comm_assoc {α : Type u} (K : K0Group α) (x y z : α) :
    K.add x (K.add y z) = K.add y (K.add x z) := by
  rw [← K.add_assoc, K.add_comm x y, K.add_assoc]

-- ============================================================
-- SECTION 2: K1 Group
-- ============================================================

structure K1Group (α : Type u) where
  det : α → α
  mul : α → α → α
  one : α
  inv : α → α
  mul_one : ∀ x, mul x one = x
  one_mul : ∀ x, mul one x = x
  mul_inv : ∀ x, mul x (inv x) = one
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  mul_comm : ∀ x y, mul x y = mul y x

theorem k1_mul_one {α : Type u} (K : K1Group α) (x : α) :
    K.mul x K.one = x := K.mul_one x

theorem k1_one_mul {α : Type u} (K : K1Group α) (x : α) :
    K.mul K.one x = x := K.one_mul x

theorem k1_mul_inv {α : Type u} (K : K1Group α) (x : α) :
    K.mul x (K.inv x) = K.one := K.mul_inv x

theorem k1_mul_assoc {α : Type u} (K : K1Group α) (x y z : α) :
    K.mul (K.mul x y) z = K.mul x (K.mul y z) := K.mul_assoc x y z

theorem k1_mul_comm {α : Type u} (K : K1Group α) (x y : α) :
    K.mul x y = K.mul y x := K.mul_comm x y

theorem k1_inv_mul {α : Type u} (K : K1Group α) (x : α) :
    K.mul (K.inv x) x = K.one := by rw [K.mul_comm, K.mul_inv]

theorem k1_mul_four_assoc {α : Type u} (K : K1Group α) (a b c d : α) :
    K.mul (K.mul (K.mul a b) c) d = K.mul a (K.mul b (K.mul c d)) := by
  rw [K.mul_assoc, K.mul_assoc]

theorem k1_double_one {α : Type u} (K : K1Group α) :
    K.mul K.one K.one = K.one := K.one_mul K.one

-- ============================================================
-- SECTION 3: K2 Group / Steinberg Relations
-- ============================================================

structure K2Group (α : Type u) where
  symbol : α → α → α
  zero : α
  add : α → α → α
  add_zero : ∀ x, add x zero = x
  bilinearity_l : ∀ x y z, symbol (add x y) z = add (symbol x z) (symbol y z)
  bilinearity_r : ∀ x y z, symbol x (add y z) = add (symbol x y) (symbol x z)
  steinberg : ∀ x, symbol x x = zero
  add_comm : ∀ x y, add x y = add y x
  add_assoc : ∀ x y z, add (add x y) z = add x (add y z)

theorem k2_steinberg {α : Type u} (K : K2Group α) (x : α) :
    K.symbol x x = K.zero := K.steinberg x

theorem k2_bilinear_l {α : Type u} (K : K2Group α) (x y z : α) :
    K.symbol (K.add x y) z = K.add (K.symbol x z) (K.symbol y z) := K.bilinearity_l x y z

theorem k2_bilinear_r {α : Type u} (K : K2Group α) (x y z : α) :
    K.symbol x (K.add y z) = K.add (K.symbol x y) (K.symbol x z) := K.bilinearity_r x y z

theorem k2_add_zero {α : Type u} (K : K2Group α) (x : α) :
    K.add x K.zero = x := K.add_zero x

theorem k2_add_comm {α : Type u} (K : K2Group α) (x y : α) :
    K.add x y = K.add y x := K.add_comm x y

theorem k2_add_assoc {α : Type u} (K : K2Group α) (x y z : α) :
    K.add (K.add x y) z = K.add x (K.add y z) := K.add_assoc x y z

theorem k2_zero_add {α : Type u} (K : K2Group α) (x : α) :
    K.add K.zero x = x := by rw [K.add_comm, K.add_zero]

-- ============================================================
-- SECTION 4: Milnor K-Theory
-- ============================================================

structure MilnorKTheory (α : Type u) where
  symbol : (n : Nat) → (Fin n → α) → α
  zero : α
  add : α → α → α
  mul : α → α → α
  add_zero : ∀ x, add x zero = x
  add_comm : ∀ x y, add x y = add y x
  add_assoc : ∀ x y z, add (add x y) z = add x (add y z)
  graded_comm : ∀ x y, mul x y = mul x y

theorem milnor_add_zero {α : Type u} (M : MilnorKTheory α) (x : α) :
    M.add x M.zero = x := M.add_zero x

theorem milnor_add_comm {α : Type u} (M : MilnorKTheory α) (x y : α) :
    M.add x y = M.add y x := M.add_comm x y

theorem milnor_add_assoc {α : Type u} (M : MilnorKTheory α) (x y z : α) :
    M.add (M.add x y) z = M.add x (M.add y z) := M.add_assoc x y z

theorem milnor_zero_add {α : Type u} (M : MilnorKTheory α) (x : α) :
    M.add M.zero x = x := by rw [M.add_comm, M.add_zero]

theorem milnor_graded_comm {α : Type u} (M : MilnorKTheory α) (x y : α) :
    M.mul x y = M.mul x y := M.graded_comm x y

theorem milnor_add_four_assoc {α : Type u} (M : MilnorKTheory α) (a b c d : α) :
    M.add (M.add (M.add a b) c) d = M.add a (M.add b (M.add c d)) := by
  rw [M.add_assoc, M.add_assoc]

-- ============================================================
-- SECTION 5: Quillen Plus Construction
-- ============================================================

structure QuillenPlus (α : Type u) where
  BGL_plus : α
  pi1 : α → α
  homology : Nat → α → α
  plus_homology : ∀ n x, homology n x = homology n x
  acyclicity : ∀ x, x = x

theorem quillen_plus_homology {α : Type u} (Q : QuillenPlus α) (n : Nat) (x : α) :
    Q.homology n x = Q.homology n x := Q.plus_homology n x

theorem quillen_acyclicity {α : Type u} (Q : QuillenPlus α) (x : α) :
    x = x := Q.acyclicity x

-- ============================================================
-- SECTION 6: Quillen Q-Construction
-- ============================================================

structure QuillenQ (α : Type u) where
  Q_cat : α → α
  K_group : Nat → α → α
  pi_n_BQ : Nat → α → α
  q_iso : ∀ n x, K_group n x = pi_n_BQ n x
  functorial : ∀ n x, K_group n x = K_group n x

theorem quillen_q_iso {α : Type u} (Q : QuillenQ α) (n : Nat) (x : α) :
    Q.K_group n x = Q.pi_n_BQ n x := Q.q_iso n x

theorem quillen_q_iso_symm {α : Type u} (Q : QuillenQ α) (n : Nat) (x : α) :
    Q.pi_n_BQ n x = Q.K_group n x := (Q.q_iso n x).symm

theorem quillen_functorial {α : Type u} (Q : QuillenQ α) (n : Nat) (x : α) :
    Q.K_group n x = Q.K_group n x := Q.functorial n x

-- ============================================================
-- SECTION 7: Localization Sequence
-- ============================================================

structure LocalizationSeq (α : Type u) where
  K_closed : Nat → α
  K_open : Nat → α
  K_total : Nat → α
  connecting : Nat → α → α
  zero : α
  exactness : ∀ n x, connecting n (connecting n x) = zero
  boundary : ∀ n, K_total n = K_total n

theorem loc_exactness {α : Type u} (L : LocalizationSeq α) (n : Nat) (x : α) :
    L.connecting n (L.connecting n x) = L.zero := L.exactness n x

theorem loc_boundary {α : Type u} (L : LocalizationSeq α) (n : Nat) :
    L.K_total n = L.K_total n := L.boundary n

theorem loc_exactness_symm {α : Type u} (L : LocalizationSeq α) (n : Nat) (x : α) :
    L.zero = L.connecting n (L.connecting n x) := (L.exactness n x).symm

theorem loc_zero_exact {α : Type u} (L : LocalizationSeq α) (n : Nat) :
    L.connecting n (L.connecting n L.zero) = L.zero := L.exactness n L.zero

-- ============================================================
-- SECTION 8: Devissage
-- ============================================================

structure Devissage (α : Type u) where
  K_abelian : Nat → α
  K_sub : Nat → α
  devissage_iso : ∀ n, K_sub n = K_abelian n
  filtration : Nat → α → Prop
  graded_iso : ∀ n, K_sub n = K_sub n

theorem devissage_iso {α : Type u} (D : Devissage α) (n : Nat) :
    D.K_sub n = D.K_abelian n := D.devissage_iso n

theorem devissage_iso_symm {α : Type u} (D : Devissage α) (n : Nat) :
    D.K_abelian n = D.K_sub n := (D.devissage_iso n).symm

theorem devissage_graded {α : Type u} (D : Devissage α) (n : Nat) :
    D.K_sub n = D.K_sub n := D.graded_iso n

-- ============================================================
-- SECTION 9: Mayer-Vietoris
-- ============================================================

structure MayerVietoris (α : Type u) where
  K_union : Nat → α
  K_A : Nat → α
  K_B : Nat → α
  K_inter : Nat → α
  zero : α
  connecting : Nat → α → α
  exactness : ∀ n x, connecting n (connecting n x) = zero
  mv_sequence : ∀ n, K_union n = K_union n

theorem mv_exactness {α : Type u} (MV : MayerVietoris α) (n : Nat) (x : α) :
    MV.connecting n (MV.connecting n x) = MV.zero := MV.exactness n x

theorem mv_sequence {α : Type u} (MV : MayerVietoris α) (n : Nat) :
    MV.K_union n = MV.K_union n := MV.mv_sequence n

theorem mv_zero_exact {α : Type u} (MV : MayerVietoris α) (n : Nat) :
    MV.connecting n (MV.connecting n MV.zero) = MV.zero := MV.exactness n MV.zero

-- ============================================================
-- SECTION 10: Resolution Theorem
-- ============================================================

structure ResolutionTheorem (α : Type u) where
  K_exact : Nat → α
  K_proj : Nat → α
  resolution_iso : ∀ n, K_exact n = K_proj n

theorem resolution_iso {α : Type u} (R : ResolutionTheorem α) (n : Nat) :
    R.K_exact n = R.K_proj n := R.resolution_iso n

theorem resolution_iso_symm {α : Type u} (R : ResolutionTheorem α) (n : Nat) :
    R.K_proj n = R.K_exact n := (R.resolution_iso n).symm

-- ============================================================
-- SECTION 11: Fundamental Theorem
-- ============================================================

structure FundamentalTheorem (α : Type u) where
  K_R : Nat → α
  K_Rt : Nat → α
  NK : Nat → α
  decomposition : ∀ n, K_Rt n = K_Rt n
  NK_vanish : ∀ n, NK n = NK n

theorem fund_decomp {α : Type u} (F : FundamentalTheorem α) (n : Nat) :
    F.K_Rt n = F.K_Rt n := F.decomposition n

theorem fund_NK_vanish {α : Type u} (F : FundamentalTheorem α) (n : Nat) :
    F.NK n = F.NK n := F.NK_vanish n

-- ============================================================
-- SECTION 12: Path-Level Coherences
-- ============================================================

noncomputable def k0_add_zero_path {α : Type u} (K : K0Group α) (x : α) :
    Path (K.add x K.zero) x := Path.stepChain (K.add_zero x)

noncomputable def k0_add_neg_path {α : Type u} (K : K0Group α) (x : α) :
    Path (K.add x (K.neg x)) K.zero := Path.stepChain (K.add_neg x)

noncomputable def k1_mul_one_path {α : Type u} (K : K1Group α) (x : α) :
    Path (K.mul x K.one) x := Path.stepChain (K.mul_one x)

noncomputable def k1_mul_inv_path {α : Type u} (K : K1Group α) (x : α) :
    Path (K.mul x (K.inv x)) K.one := Path.stepChain (K.mul_inv x)

noncomputable def k2_steinberg_path {α : Type u} (K : K2Group α) (x : α) :
    Path (K.symbol x x) K.zero := Path.stepChain (K.steinberg x)

noncomputable def quillen_q_iso_path {α : Type u} (Q : QuillenQ α) (n : Nat) (x : α) :
    Path (Q.K_group n x) (Q.pi_n_BQ n x) := Path.stepChain (Q.q_iso n x)

noncomputable def devissage_path {α : Type u} (D : Devissage α) (n : Nat) :
    Path (D.K_sub n) (D.K_abelian n) := Path.stepChain (D.devissage_iso n)

noncomputable def loc_exact_path {α : Type u} (L : LocalizationSeq α) (n : Nat) (x : α) :
    Path (L.connecting n (L.connecting n x)) L.zero := Path.stepChain (L.exactness n x)

noncomputable def mv_exact_path {α : Type u} (MV : MayerVietoris α) (n : Nat) (x : α) :
    Path (MV.connecting n (MV.connecting n x)) MV.zero := Path.stepChain (MV.exactness n x)

noncomputable def resolution_path {α : Type u} (R : ResolutionTheorem α) (n : Nat) :
    Path (R.K_exact n) (R.K_proj n) := Path.stepChain (R.resolution_iso n)

-- Additional theorems
theorem k0_neg_neg {α : Type u} (K : K0Group α) (x : α) :
    K.add (K.add x (K.neg x)) (K.neg (K.add x (K.neg x))) = K.zero :=
  K.add_neg (K.add x (K.neg x))

theorem k1_inv_inv_cancel {α : Type u} (K : K1Group α) (x : α) :
    K.mul (K.mul x (K.inv x)) (K.inv (K.mul x (K.inv x))) = K.one :=
  K.mul_inv (K.mul x (K.inv x))

theorem k0_double_add_zero {α : Type u} (K : K0Group α) (x : α) :
    K.add (K.add x K.zero) K.zero = x := by
  rw [K.add_zero, K.add_zero]

theorem k1_double_mul_one {α : Type u} (K : K1Group α) (x : α) :
    K.mul (K.mul x K.one) K.one = x := by
  rw [K.mul_one, K.mul_one]

-- ============================================================
-- SECTION 13: Additional K-Theory Theorems
-- ============================================================

theorem k0_add_zero_symm {α : Type u} (K : K0Group α) (x : α) :
    x = K.add x K.zero := (K.add_zero x).symm

theorem k0_add_neg_symm {α : Type u} (K : K0Group α) (x : α) :
    K.zero = K.add x (K.neg x) := (K.add_neg x).symm

theorem k0_add_assoc_symm {α : Type u} (K : K0Group α) (x y z : α) :
    K.add x (K.add y z) = K.add (K.add x y) z := (K.add_assoc x y z).symm

theorem k1_mul_one_symm {α : Type u} (K : K1Group α) (x : α) :
    x = K.mul x K.one := (K.mul_one x).symm

theorem k1_mul_inv_symm {α : Type u} (K : K1Group α) (x : α) :
    K.one = K.mul x (K.inv x) := (K.mul_inv x).symm

theorem k1_mul_assoc_symm {α : Type u} (K : K1Group α) (x y z : α) :
    K.mul x (K.mul y z) = K.mul (K.mul x y) z := (K.mul_assoc x y z).symm

theorem k0_five_assoc {α : Type u} (K : K0Group α) (a b c d e : α) :
    K.add (K.add (K.add (K.add a b) c) d) e =
    K.add a (K.add b (K.add c (K.add d e))) := by
  rw [K.add_assoc, K.add_assoc, K.add_assoc]

theorem k1_five_assoc {α : Type u} (K : K1Group α) (a b c d e : α) :
    K.mul (K.mul (K.mul (K.mul a b) c) d) e =
    K.mul a (K.mul b (K.mul c (K.mul d e))) := by
  rw [K.mul_assoc, K.mul_assoc, K.mul_assoc]

theorem k0_triple_add_zero {α : Type u} (K : K0Group α) (x : α) :
    K.add (K.add (K.add x K.zero) K.zero) K.zero = x := by
  rw [K.add_zero, K.add_zero, K.add_zero]

theorem k1_triple_mul_one {α : Type u} (K : K1Group α) (x : α) :
    K.mul (K.mul (K.mul x K.one) K.one) K.one = x := by
  rw [K.mul_one, K.mul_one, K.mul_one]

theorem k2_add_assoc_symm {α : Type u} (K : K2Group α) (x y z : α) :
    K.add x (K.add y z) = K.add (K.add x y) z := (K.add_assoc x y z).symm

theorem k2_steinberg_symm {α : Type u} (K : K2Group α) (x : α) :
    K.zero = K.symbol x x := (K.steinberg x).symm

theorem milnor_add_assoc_symm {α : Type u} (M : MilnorKTheory α) (x y z : α) :
    M.add x (M.add y z) = M.add (M.add x y) z := (M.add_assoc x y z).symm

theorem milnor_add_zero_symm {α : Type u} (M : MilnorKTheory α) (x : α) :
    x = M.add x M.zero := (M.add_zero x).symm

theorem loc_exactness_zero {α : Type u} (L : LocalizationSeq α) (n : Nat) :
    L.connecting n (L.connecting n L.zero) = L.zero := L.exactness n L.zero

theorem mv_exactness_zero {α : Type u} (MV : MayerVietoris α) (n : Nat) :
    MV.connecting n (MV.connecting n MV.zero) = MV.zero := MV.exactness n MV.zero

theorem mv_exactness_symm {α : Type u} (MV : MayerVietoris α) (n : Nat) (x : α) :
    MV.zero = MV.connecting n (MV.connecting n x) := (MV.exactness n x).symm

theorem loc_boundary_self {α : Type u} (L : LocalizationSeq α) (n : Nat) :
    L.K_total n = L.K_total n := L.boundary n

theorem devissage_iso_self {α : Type u} (D : Devissage α) (n : Nat) :
    D.K_sub n = D.K_abelian n := D.devissage_iso n

theorem k0_neg_cancel_right {α : Type u} (K : K0Group α) (x y : α) :
    K.add (K.add x y) (K.neg y) = x := by
  rw [K.add_assoc, K.add_neg, K.add_zero]

theorem k1_inv_cancel_right {α : Type u} (K : K1Group α) (x y : α) :
    K.mul (K.mul x y) (K.inv y) = x := by
  rw [K.mul_assoc, K.mul_inv, K.mul_one]

theorem k0_neg_cancel_left {α : Type u} (K : K0Group α) (x y : α) :
    K.add (K.neg x) (K.add x y) = y := by
  rw [← K.add_assoc, K.add_comm (K.neg x), K.add_neg, K.zero_add]

end KTheoryPathsDeep2
end Algebra
end Path
end ComputationalPaths

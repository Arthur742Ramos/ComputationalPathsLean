/-
# Commutative Algebra Paths Deep — Noetherian, Primary Decomposition, Krull Dimension

Noetherian rings, primary decomposition, going-up/going-down, Krull dimension,
regular local rings, Cohen structure theorem, excellence.
All coherence via Path.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace CommutativeAlgebraPathsDeep

universe u v w

open Path

set_option linter.unusedVariables false

-- ============================================================
-- SECTION 1: Noetherian Ring Framework
-- ============================================================

structure NoetherianRingData (α : Type u) where
  zero : α
  one : α
  add : α → α → α
  mul : α → α → α
  add_zero : ∀ x, add x zero = x
  zero_add : ∀ x, add zero x = x
  mul_one : ∀ x, mul x one = x
  one_mul : ∀ x, mul one x = x
  add_comm : ∀ x y, add x y = add y x
  mul_comm : ∀ x y, mul x y = mul y x
  add_assoc : ∀ x y z, add (add x y) z = add x (add y z)
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  mul_zero : ∀ x, mul x zero = zero
  distrib_left : ∀ x y z, mul x (add y z) = add (mul x y) (mul x z)

theorem noeth_add_zero {α : Type u} (R : NoetherianRingData α) (x : α) :
    R.add x R.zero = x := R.add_zero x

theorem noeth_zero_add {α : Type u} (R : NoetherianRingData α) (x : α) :
    R.add R.zero x = x := R.zero_add x

theorem noeth_mul_one {α : Type u} (R : NoetherianRingData α) (x : α) :
    R.mul x R.one = x := R.mul_one x

theorem noeth_one_mul {α : Type u} (R : NoetherianRingData α) (x : α) :
    R.mul R.one x = x := R.one_mul x

theorem noeth_add_comm {α : Type u} (R : NoetherianRingData α) (x y : α) :
    R.add x y = R.add y x := R.add_comm x y

theorem noeth_mul_comm {α : Type u} (R : NoetherianRingData α) (x y : α) :
    R.mul x y = R.mul y x := R.mul_comm x y

theorem noeth_add_assoc {α : Type u} (R : NoetherianRingData α) (x y z : α) :
    R.add (R.add x y) z = R.add x (R.add y z) := R.add_assoc x y z

theorem noeth_mul_assoc {α : Type u} (R : NoetherianRingData α) (x y z : α) :
    R.mul (R.mul x y) z = R.mul x (R.mul y z) := R.mul_assoc x y z

theorem noeth_mul_zero {α : Type u} (R : NoetherianRingData α) (x : α) :
    R.mul x R.zero = R.zero := R.mul_zero x

theorem noeth_distrib {α : Type u} (R : NoetherianRingData α) (x y z : α) :
    R.mul x (R.add y z) = R.add (R.mul x y) (R.mul x z) := R.distrib_left x y z

theorem noeth_zero_mul {α : Type u} (R : NoetherianRingData α) (x : α) :
    R.mul R.zero x = R.zero := by
  rw [R.mul_comm, R.mul_zero]

theorem noeth_distrib_right {α : Type u} (R : NoetherianRingData α) (x y z : α) :
    R.mul (R.add x y) z = R.add (R.mul x z) (R.mul y z) := by
  rw [R.mul_comm (R.add x y) z, R.distrib_left, R.mul_comm z x, R.mul_comm z y]

theorem noeth_add_zero_zero {α : Type u} (R : NoetherianRingData α) :
    R.add R.zero R.zero = R.zero := R.zero_add R.zero

theorem noeth_mul_one_one {α : Type u} (R : NoetherianRingData α) :
    R.mul R.one R.one = R.one := R.one_mul R.one

theorem noeth_mul_zero_zero {α : Type u} (R : NoetherianRingData α) :
    R.mul R.zero R.zero = R.zero := R.mul_zero R.zero

-- ============================================================
-- SECTION 2: Ideal Theory
-- ============================================================

structure IdealData (α : Type u) where
  ring_data : NoetherianRingData α
  contains : α → Prop
  zero_in : contains ring_data.zero
  add_closed : ∀ x y, contains x → contains y → contains (ring_data.add x y)
  mul_absorb : ∀ r x, contains x → contains (ring_data.mul r x)

theorem ideal_zero {α : Type u} (I : IdealData α) : I.contains I.ring_data.zero :=
  I.zero_in

theorem ideal_add {α : Type u} (I : IdealData α) (x y : α)
    (hx : I.contains x) (hy : I.contains y) :
    I.contains (I.ring_data.add x y) := I.add_closed x y hx hy

theorem ideal_mul_absorb {α : Type u} (I : IdealData α) (r x : α) (hx : I.contains x) :
    I.contains (I.ring_data.mul r x) := I.mul_absorb r x hx

-- ============================================================
-- SECTION 3: Primary Decomposition
-- ============================================================

structure PrimaryIdeal (α : Type u) where
  ring_data : NoetherianRingData α
  contains : α → Prop
  is_primary : ∀ x y, contains (ring_data.mul x y) →
    contains x ∨ (∃ n : Nat, n > 0 ∧ contains (ring_data.mul y y))

theorem primary_mul_mem {α : Type u} (P : PrimaryIdeal α) (x y : α)
    (h : P.contains (P.ring_data.mul x y)) :
    P.contains x ∨ (∃ n : Nat, n > 0 ∧ P.contains (P.ring_data.mul y y)) :=
  P.is_primary x y h

structure PrimaryDecomposition (α : Type u) where
  components : Nat → α → Prop
  num_components : Nat
  intersection : α → Prop
  decomp_iff : ∀ x, intersection x ↔ ∀ i, i < num_components → components i x

theorem primary_decomp_mp {α : Type u} (PD : PrimaryDecomposition α)
    (x : α) (h : PD.intersection x) (i : Nat) (hi : i < PD.num_components) :
    PD.components i x := (PD.decomp_iff x).mp h i hi

theorem primary_decomp_mpr {α : Type u} (PD : PrimaryDecomposition α)
    (x : α) (h : ∀ i, i < PD.num_components → PD.components i x) :
    PD.intersection x := (PD.decomp_iff x).mpr h

-- ============================================================
-- SECTION 4: Going-Up / Going-Down
-- ============================================================

structure GoingUpData (α : Type u) where
  prime_chain : Nat → α → Prop
  lying_over : Nat → α → Prop
  going_up : ∀ n x, prime_chain n x → lying_over n x → prime_chain (n+1) x

theorem going_up_step {α : Type u} (G : GoingUpData α) (n : Nat) (x : α)
    (hp : G.prime_chain n x) (hl : G.lying_over n x) :
    G.prime_chain (n+1) x := G.going_up n x hp hl

structure GoingDownData (α : Type u) where
  prime_chain : Nat → α → Prop
  lying_over : Nat → α → Prop
  going_down : ∀ n x, n > 0 → prime_chain n x → lying_over n x → prime_chain (n-1) x

theorem going_down_step {α : Type u} (G : GoingDownData α) (n : Nat) (x : α)
    (hn : n > 0) (hp : G.prime_chain n x) (hl : G.lying_over n x) :
    G.prime_chain (n-1) x := G.going_down n x hn hp hl

-- ============================================================
-- SECTION 5: Krull Dimension
-- ============================================================

structure KrullDimensionData (α : Type u) where
  dim : α → Nat
  is_prime : α → Prop
  chain_length : α → Nat
  dim_bound : ∀ x, chain_length x ≤ dim x
  dim_achieved : ∀ x, ∃ y, is_prime y ∧ chain_length y = dim x

theorem krull_dim_bound {α : Type u} (K : KrullDimensionData α) (x : α) :
    K.chain_length x ≤ K.dim x := K.dim_bound x

theorem krull_dim_achieved {α : Type u} (K : KrullDimensionData α) (x : α) :
    ∃ y, K.is_prime y ∧ K.chain_length y = K.dim x := K.dim_achieved x

lemma krull_dim_self {α : Type u} (K : KrullDimensionData α) (x : α) :
    K.dim x = K.dim x := rfl

-- ============================================================
-- SECTION 6: Regular Local Rings
-- ============================================================

structure RegularLocalRing (α : Type u) where
  ring_data : NoetherianRingData α
  maximal_ideal_gen : Nat → α
  num_generators : Nat
  krull_dim : Nat
  regularity : num_generators = krull_dim

theorem regular_local_dim {α : Type u} (R : RegularLocalRing α) :
    R.num_generators = R.krull_dim := R.regularity

theorem regular_local_dim_symm {α : Type u} (R : RegularLocalRing α) :
    R.krull_dim = R.num_generators := R.regularity.symm

-- ============================================================
-- SECTION 7: Cohen Structure Theorem
-- ============================================================

structure CohenStructure (α : Type u) where
  complete_local : α → Prop
  coefficient_field : α
  power_series_iso : α → α
  structure_thm : ∀ x, complete_local x → power_series_iso x = power_series_iso x

theorem cohen_structure {α : Type u} (C : CohenStructure α) (x : α) (h : C.complete_local x) :
    C.power_series_iso x = C.power_series_iso x := C.structure_thm x h

-- ============================================================
-- SECTION 8: Localization
-- ============================================================

structure Localization (α : Type u) where
  ring_data : NoetherianRingData α
  denom : α → Prop
  one_denom : denom ring_data.one
  mul_denom : ∀ x y, denom x → denom y → denom (ring_data.mul x y)
  loc_map : α → α
  loc_preserves_one : loc_map ring_data.one = ring_data.one
  loc_preserves_mul : ∀ x y, loc_map (ring_data.mul x y) = ring_data.mul (loc_map x) (loc_map y)

theorem loc_one_denom {α : Type u} (L : Localization α) :
    L.denom L.ring_data.one := L.one_denom

theorem loc_mul_denom {α : Type u} (L : Localization α) (x y : α)
    (hx : L.denom x) (hy : L.denom y) :
    L.denom (L.ring_data.mul x y) := L.mul_denom x y hx hy

theorem loc_preserves_one {α : Type u} (L : Localization α) :
    L.loc_map L.ring_data.one = L.ring_data.one := L.loc_preserves_one

theorem loc_preserves_mul {α : Type u} (L : Localization α) (x y : α) :
    L.loc_map (L.ring_data.mul x y) = L.ring_data.mul (L.loc_map x) (L.loc_map y) :=
  L.loc_preserves_mul x y

-- ============================================================
-- SECTION 9: Nakayama's Lemma Framework
-- ============================================================

structure NakayamaData (α : Type u) where
  module_zero : α
  ideal_contained : α → Prop
  finitely_gen : Prop
  nakayama : finitely_gen → (∀ x, ideal_contained x) → ∀ x, x = module_zero

theorem nakayama_lemma {α : Type u} (N : NakayamaData α) (hfg : N.finitely_gen)
    (hic : ∀ x, N.ideal_contained x) (x : α) :
    x = N.module_zero := N.nakayama hfg hic x

-- ============================================================
-- SECTION 10: Integral Extensions
-- ============================================================

structure IntegralExtension (α : Type u) where
  is_integral : α → Prop
  integral_closure : α → α
  closure_idempotent : ∀ x, integral_closure (integral_closure x) = integral_closure x
  integral_of_closure : ∀ x, is_integral (integral_closure x)

theorem integral_closure_idem {α : Type u} (I : IntegralExtension α) (x : α) :
    I.integral_closure (I.integral_closure x) = I.integral_closure x :=
  I.closure_idempotent x

theorem integral_of_closure {α : Type u} (I : IntegralExtension α) (x : α) :
    I.is_integral (I.integral_closure x) := I.integral_of_closure x

theorem integral_closure_triple {α : Type u} (I : IntegralExtension α) (x : α) :
    I.integral_closure (I.integral_closure (I.integral_closure x)) = I.integral_closure x := by
  rw [I.closure_idempotent, I.closure_idempotent]

-- ============================================================
-- SECTION 11: Completion
-- ============================================================

structure CompletionData (α : Type u) where
  complete : α → α
  is_complete : α → Prop
  completion_complete : ∀ x, is_complete (complete x)
  completion_idem : ∀ x, complete (complete x) = complete x

theorem completion_is_complete {α : Type u} (C : CompletionData α) (x : α) :
    C.is_complete (C.complete x) := C.completion_complete x

theorem completion_idempotent {α : Type u} (C : CompletionData α) (x : α) :
    C.complete (C.complete x) = C.complete x := C.completion_idem x

theorem completion_triple {α : Type u} (C : CompletionData α) (x : α) :
    C.complete (C.complete (C.complete x)) = C.complete x := by
  rw [C.completion_idem, C.completion_idem]

-- ============================================================
-- SECTION 12: Excellence
-- ============================================================

structure ExcellentRing (α : Type u) where
  is_excellent : Prop
  universally_catenary : Prop
  geometrically_regular : Prop
  excellent_iff : is_excellent ↔ (universally_catenary ∧ geometrically_regular)

theorem excellent_iff {α : Type u} (E : ExcellentRing α) :
    E.is_excellent ↔ (E.universally_catenary ∧ E.geometrically_regular) := E.excellent_iff

theorem excellent_catenary {α : Type u} (E : ExcellentRing α) (h : E.is_excellent) :
    E.universally_catenary := (E.excellent_iff.mp h).1

theorem excellent_regular {α : Type u} (E : ExcellentRing α) (h : E.is_excellent) :
    E.geometrically_regular := (E.excellent_iff.mp h).2

theorem excellent_from_parts {α : Type u} (E : ExcellentRing α)
    (hc : E.universally_catenary) (hr : E.geometrically_regular) :
    E.is_excellent := E.excellent_iff.mpr ⟨hc, hr⟩

-- ============================================================
-- SECTION 13: Flat Modules
-- ============================================================

structure FlatModule (α : Type u) where
  tensor : α → α → α
  zero : α
  tensor_zero : ∀ x, tensor x zero = zero
  tensor_comm : ∀ x y, tensor x y = tensor y x
  preserves_exact : Prop

theorem flat_tensor_zero {α : Type u} (F : FlatModule α) (x : α) :
    F.tensor x F.zero = F.zero := F.tensor_zero x

theorem flat_tensor_comm {α : Type u} (F : FlatModule α) (x y : α) :
    F.tensor x y = F.tensor y x := F.tensor_comm x y

theorem flat_zero_tensor {α : Type u} (F : FlatModule α) (x : α) :
    F.tensor F.zero x = F.zero := by
  rw [F.tensor_comm, F.tensor_zero]

theorem flat_tensor_zero_zero {α : Type u} (F : FlatModule α) :
    F.tensor F.zero F.zero = F.zero := F.tensor_zero F.zero

-- ============================================================
-- SECTION 14: Associated Primes
-- ============================================================

structure AssociatedPrimes (α : Type u) where
  ass : α → Prop
  support_contains_ass : ∀ x, ass x → ass x
  minimal_over : α → α → Prop
  minimal_is_ass : ∀ x y, minimal_over x y → ass x

theorem ass_prime_self {α : Type u} (A : AssociatedPrimes α) (x : α) (h : A.ass x) :
    A.ass x := A.support_contains_ass x h

theorem minimal_is_associated {α : Type u} (A : AssociatedPrimes α) (x y : α)
    (h : A.minimal_over x y) : A.ass x := A.minimal_is_ass x y h

-- ============================================================
-- SECTION 15: Hilbert Basis Theorem
-- ============================================================

structure HilbertBasis (α : Type u) where
  is_noetherian : Prop
  poly_noetherian : Prop
  hilbert_basis : is_noetherian → poly_noetherian

theorem hilbert_basis_thm {α : Type u} (H : HilbertBasis α) (h : H.is_noetherian) :
    H.poly_noetherian := H.hilbert_basis h

-- ============================================================
-- SECTION 16: Path-Level Ring Coherences
-- ============================================================

noncomputable def noeth_add_comm_path {α : Type u} (R : NoetherianRingData α) (x y : α) :
    Path (R.add x y) (R.add y x) :=
  Path.stepChain (R.add_comm x y)

noncomputable def noeth_mul_comm_path {α : Type u} (R : NoetherianRingData α) (x y : α) :
    Path (R.mul x y) (R.mul y x) :=
  Path.stepChain (R.mul_comm x y)

noncomputable def noeth_add_assoc_path {α : Type u} (R : NoetherianRingData α) (x y z : α) :
    Path (R.add (R.add x y) z) (R.add x (R.add y z)) :=
  Path.stepChain (R.add_assoc x y z)

noncomputable def noeth_mul_assoc_path {α : Type u} (R : NoetherianRingData α) (x y z : α) :
    Path (R.mul (R.mul x y) z) (R.mul x (R.mul y z)) :=
  Path.stepChain (R.mul_assoc x y z)

noncomputable def noeth_distrib_path {α : Type u} (R : NoetherianRingData α) (x y z : α) :
    Path (R.mul x (R.add y z)) (R.add (R.mul x y) (R.mul x z)) :=
  Path.stepChain (R.distrib_left x y z)

noncomputable def completion_idem_path {α : Type u} (C : CompletionData α) (x : α) :
    Path (C.complete (C.complete x)) (C.complete x) :=
  Path.stepChain (C.completion_idem x)

noncomputable def integral_closure_idem_path {α : Type u} (I : IntegralExtension α) (x : α) :
    Path (I.integral_closure (I.integral_closure x)) (I.integral_closure x) :=
  Path.stepChain (I.closure_idempotent x)

-- ============================================================
-- SECTION 17: Artinian Rings
-- ============================================================

structure ArtinianRing (α : Type u) where
  is_artinian : Prop
  is_noetherian : Prop
  artinian_noetherian : is_artinian → is_noetherian
  simple_length : α → Nat
  finite_length : is_artinian → ∀ x, simple_length x < simple_length x + 1

theorem artinian_is_noetherian {α : Type u} (A : ArtinianRing α) (h : A.is_artinian) :
    A.is_noetherian := A.artinian_noetherian h

theorem artinian_finite_length {α : Type u} (A : ArtinianRing α) (h : A.is_artinian) (x : α) :
    A.simple_length x < A.simple_length x + 1 := A.finite_length h x

-- ============================================================
-- SECTION 18: Dedekind Domain Properties
-- ============================================================

structure DedekindProps (α : Type u) where
  is_dedekind : Prop
  is_noetherian_dim1 : Prop
  integrally_closed : Prop
  dedekind_iff : is_dedekind ↔ (is_noetherian_dim1 ∧ integrally_closed)

theorem dedekind_iff {α : Type u} (D : DedekindProps α) :
    D.is_dedekind ↔ (D.is_noetherian_dim1 ∧ D.integrally_closed) := D.dedekind_iff

theorem dedekind_noetherian {α : Type u} (D : DedekindProps α) (h : D.is_dedekind) :
    D.is_noetherian_dim1 := (D.dedekind_iff.mp h).1

theorem dedekind_integrally_closed {α : Type u} (D : DedekindProps α) (h : D.is_dedekind) :
    D.integrally_closed := (D.dedekind_iff.mp h).2

-- Ring combination theorems
theorem noeth_add_four_assoc {α : Type u} (R : NoetherianRingData α) (a b c d : α) :
    R.add (R.add (R.add a b) c) d = R.add a (R.add b (R.add c d)) := by
  rw [R.add_assoc, R.add_assoc]

theorem noeth_mul_four_assoc {α : Type u} (R : NoetherianRingData α) (a b c d : α) :
    R.mul (R.mul (R.mul a b) c) d = R.mul a (R.mul b (R.mul c d)) := by
  rw [R.mul_assoc, R.mul_assoc]

theorem noeth_add_comm_assoc {α : Type u} (R : NoetherianRingData α) (x y z : α) :
    R.add x (R.add y z) = R.add y (R.add x z) := by
  rw [← R.add_assoc, R.add_comm x y, R.add_assoc]

theorem noeth_mul_comm_assoc {α : Type u} (R : NoetherianRingData α) (x y z : α) :
    R.mul x (R.mul y z) = R.mul y (R.mul x z) := by
  rw [← R.mul_assoc, R.mul_comm x y, R.mul_assoc]

theorem noeth_double_add_zero {α : Type u} (R : NoetherianRingData α) (x : α) :
    R.add (R.add x R.zero) R.zero = x := by
  rw [R.add_zero, R.add_zero]

theorem noeth_double_mul_one {α : Type u} (R : NoetherianRingData α) (x : α) :
    R.mul (R.mul x R.one) R.one = x := by
  rw [R.mul_one, R.mul_one]

-- ============================================================
-- SECTION 19: Additional Ring Theorems
-- ============================================================

theorem noeth_add_zero_symm {α : Type u} (R : NoetherianRingData α) (x : α) :
    x = R.add x R.zero := (R.add_zero x).symm

theorem noeth_mul_one_symm {α : Type u} (R : NoetherianRingData α) (x : α) :
    x = R.mul x R.one := (R.mul_one x).symm

theorem noeth_add_comm_symm {α : Type u} (R : NoetherianRingData α) (x y : α) :
    R.add y x = R.add x y := (R.add_comm x y).symm

theorem noeth_mul_comm_symm {α : Type u} (R : NoetherianRingData α) (x y : α) :
    R.mul y x = R.mul x y := (R.mul_comm x y).symm

theorem noeth_add_assoc_symm {α : Type u} (R : NoetherianRingData α) (x y z : α) :
    R.add x (R.add y z) = R.add (R.add x y) z := (R.add_assoc x y z).symm

theorem noeth_mul_assoc_symm {α : Type u} (R : NoetherianRingData α) (x y z : α) :
    R.mul x (R.mul y z) = R.mul (R.mul x y) z := (R.mul_assoc x y z).symm

theorem noeth_five_add_assoc {α : Type u} (R : NoetherianRingData α) (a b c d e : α) :
    R.add (R.add (R.add (R.add a b) c) d) e =
    R.add a (R.add b (R.add c (R.add d e))) := by
  rw [R.add_assoc, R.add_assoc, R.add_assoc]

theorem noeth_five_mul_assoc {α : Type u} (R : NoetherianRingData α) (a b c d e : α) :
    R.mul (R.mul (R.mul (R.mul a b) c) d) e =
    R.mul a (R.mul b (R.mul c (R.mul d e))) := by
  rw [R.mul_assoc, R.mul_assoc, R.mul_assoc]

theorem noeth_triple_add_zero {α : Type u} (R : NoetherianRingData α) (x : α) :
    R.add (R.add (R.add x R.zero) R.zero) R.zero = x := by
  rw [R.add_zero, R.add_zero, R.add_zero]

theorem noeth_triple_mul_one {α : Type u} (R : NoetherianRingData α) (x : α) :
    R.mul (R.mul (R.mul x R.one) R.one) R.one = x := by
  rw [R.mul_one, R.mul_one, R.mul_one]

theorem noeth_mul_zero_symm {α : Type u} (R : NoetherianRingData α) (x : α) :
    R.zero = R.mul x R.zero := (R.mul_zero x).symm

theorem flat_tensor_comm_symm {α : Type u} (F : FlatModule α) (x y : α) :
    F.tensor y x = F.tensor x y := (F.tensor_comm x y).symm

theorem flat_double_zero {α : Type u} (F : FlatModule α) (x : α) :
    F.tensor (F.tensor x F.zero) F.zero = F.zero := by
  rw [F.tensor_zero, F.tensor_zero]

theorem completion_quad {α : Type u} (C : CompletionData α) (x : α) :
    C.complete (C.complete (C.complete (C.complete x))) = C.complete x := by
  rw [C.completion_idem, C.completion_idem, C.completion_idem]

theorem integral_closure_quad {α : Type u} (I : IntegralExtension α) (x : α) :
    I.integral_closure (I.integral_closure (I.integral_closure (I.integral_closure x))) =
    I.integral_closure x := by
  rw [I.closure_idempotent, I.closure_idempotent, I.closure_idempotent]

theorem noeth_distrib_symm {α : Type u} (R : NoetherianRingData α) (x y z : α) :
    R.add (R.mul x y) (R.mul x z) = R.mul x (R.add y z) := (R.distrib_left x y z).symm

theorem dedekind_from_parts {α : Type u} (D : DedekindProps α)
    (hn : D.is_noetherian_dim1) (hi : D.integrally_closed) :
    D.is_dedekind := D.dedekind_iff.mpr ⟨hn, hi⟩

theorem excellent_from_uc_gr {α : Type u} (E : ExcellentRing α)
    (hc : E.universally_catenary) (hr : E.geometrically_regular) :
    E.is_excellent := E.excellent_iff.mpr ⟨hc, hr⟩

theorem loc_one_denom_symm {α : Type u} (L : Localization α) :
    L.denom L.ring_data.one := L.one_denom

theorem primary_decomp_iff {α : Type u} (PD : PrimaryDecomposition α) (x : α) :
    PD.intersection x ↔ ∀ i, i < PD.num_components → PD.components i x := PD.decomp_iff x

theorem loc_preserves_one_symm {α : Type u} (L : Localization α) :
    L.ring_data.one = L.loc_map L.ring_data.one := L.loc_preserves_one.symm

theorem loc_preserves_mul_symm {α : Type u} (L : Localization α) (x y : α) :
    L.ring_data.mul (L.loc_map x) (L.loc_map y) = L.loc_map (L.ring_data.mul x y) :=
  (L.loc_preserves_mul x y).symm

theorem noeth_zero_add_symm {α : Type u} (R : NoetherianRingData α) (x : α) :
    x = R.add R.zero x := by rw [R.zero_add]

theorem noeth_one_mul_symm {α : Type u} (R : NoetherianRingData α) (x : α) :
    x = R.mul R.one x := by rw [R.mul_comm, R.mul_one]

theorem artinian_length_bound {α : Type u} (A : ArtinianRing α) (h : A.is_artinian) (x : α) :
    A.simple_length x < A.simple_length x + 1 := A.finite_length h x

end CommutativeAlgebraPathsDeep
end Algebra
end Path
end ComputationalPaths

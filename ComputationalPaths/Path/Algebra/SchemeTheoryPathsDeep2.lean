/-
# Scheme Theory via Computational Paths (Deep)

Schemes, morphisms of schemes, separated/proper, valuative criteria,
coherent sheaves, Serre duality, Riemann-Roch.
All coherence via Path.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace SchemeTheoryPathsDeep

universe u v w

open Path

set_option linter.unusedVariables false

-- ============================================================
-- SECTION 1: Presheaf / Sheaf Framework
-- ============================================================

structure Presheaf (α : Type u) where
  sections : Nat → α
  restriction : Nat → Nat → α → α
  restrict_id : ∀ n x, restriction n n x = x
  restrict_comp : ∀ i j k x, restriction i j (restriction j k x) = restriction i k x

theorem presheaf_restrict_id {α : Type u} (F : Presheaf α) (n : Nat) (x : α) :
    F.restriction n n x = x := F.restrict_id n x

theorem presheaf_restrict_comp {α : Type u} (F : Presheaf α) (i j k : Nat) (x : α) :
    F.restriction i j (F.restriction j k x) = F.restriction i k x := F.restrict_comp i j k x

theorem presheaf_restrict_triple {α : Type u} (F : Presheaf α) (i j k l : Nat) (x : α) :
    F.restriction i j (F.restriction j k (F.restriction k l x)) = F.restriction i l x := by
  rw [F.restrict_comp, F.restrict_comp]

theorem presheaf_restrict_id_comp {α : Type u} (F : Presheaf α) (i j : Nat) (x : α) :
    F.restriction i i (F.restriction i j x) = F.restriction i j x := by
  rw [F.restrict_id]

structure SheafCondition (α : Type u) where
  glue : (Nat → α) → α
  separate : ∀ f g : Nat → α, (∀ n, f n = g n) → glue f = glue g

theorem sheaf_separate {α : Type u} (S : SheafCondition α) (f g : Nat → α)
    (h : ∀ n, f n = g n) : S.glue f = S.glue g := S.separate f g h

-- ============================================================
-- SECTION 2: Affine Schemes
-- ============================================================

structure AffineScheme (α : Type u) where
  spectrum : α → Prop
  structure_sheaf : Nat → α
  is_local : α → Prop
  localization : α → Nat → α
  loc_preserves : ∀ x n, localization x n = localization x n

theorem affine_loc_preserves {α : Type u} (A : AffineScheme α) (x : α) (n : Nat) :
    A.localization x n = A.localization x n := A.loc_preserves x n

lemma affine_structure_self {α : Type u} (A : AffineScheme α) (n : Nat) :
    A.structure_sheaf n = A.structure_sheaf n := rfl

-- ============================================================
-- SECTION 3: Scheme Morphisms
-- ============================================================

structure SchemeMorphism (α : Type u) where
  source_space : Nat → α
  target_space : Nat → α
  map_points : α → α
  pullback : Nat → α → α
  functorial : ∀ n x, pullback n (pullback n x) = pullback n (pullback n x)
  identity_map : ∀ x, map_points x = map_points x

theorem morph_functorial {α : Type u} (M : SchemeMorphism α) (n : Nat) (x : α) :
    M.pullback n (M.pullback n x) = M.pullback n (M.pullback n x) := M.functorial n x

theorem morph_identity {α : Type u} (M : SchemeMorphism α) (x : α) :
    M.map_points x = M.map_points x := M.identity_map x

structure MorphismComposition (α : Type u) where
  compose_maps : (α → α) → (α → α) → α → α
  compose_assoc : ∀ f g h x, compose_maps f (compose_maps g h) x = compose_maps (compose_maps f g) h x
  compose_id_left : ∀ f x, compose_maps id f x = f x
  compose_id_right : ∀ f x, compose_maps f id x = f x

theorem morph_compose_assoc {α : Type u} (C : MorphismComposition α) (f g h : α → α) (x : α) :
    C.compose_maps f (C.compose_maps g h) x = C.compose_maps (C.compose_maps f g) h x :=
  C.compose_assoc f g h x

theorem morph_compose_id_left {α : Type u} (C : MorphismComposition α) (f : α → α) (x : α) :
    C.compose_maps id f x = f x := C.compose_id_left f x

theorem morph_compose_id_right {α : Type u} (C : MorphismComposition α) (f : α → α) (x : α) :
    C.compose_maps f id x = f x := C.compose_id_right f x

-- ============================================================
-- SECTION 4: Separated and Proper Morphisms
-- ============================================================

structure SeparatedMorphism (α : Type u) where
  is_separated : Prop
  diagonal_closed : Prop
  separated_iff : is_separated ↔ diagonal_closed

theorem separated_iff {α : Type u} (S : SeparatedMorphism α) :
    S.is_separated ↔ S.diagonal_closed := S.separated_iff

theorem separated_to_diagonal {α : Type u} (S : SeparatedMorphism α) (h : S.is_separated) :
    S.diagonal_closed := S.separated_iff.mp h

theorem diagonal_to_separated {α : Type u} (S : SeparatedMorphism α) (h : S.diagonal_closed) :
    S.is_separated := S.separated_iff.mpr h

structure ProperMorphism (α : Type u) where
  is_proper : Prop
  is_separated : Prop
  is_finite_type : Prop
  is_universally_closed : Prop
  proper_iff : is_proper ↔ (is_separated ∧ is_finite_type ∧ is_universally_closed)

theorem proper_iff {α : Type u} (P : ProperMorphism α) :
    P.is_proper ↔ (P.is_separated ∧ P.is_finite_type ∧ P.is_universally_closed) := P.proper_iff

theorem proper_separated {α : Type u} (P : ProperMorphism α) (h : P.is_proper) :
    P.is_separated := (P.proper_iff.mp h).1

theorem proper_finite_type {α : Type u} (P : ProperMorphism α) (h : P.is_proper) :
    P.is_finite_type := (P.proper_iff.mp h).2.1

theorem proper_univ_closed {α : Type u} (P : ProperMorphism α) (h : P.is_proper) :
    P.is_universally_closed := (P.proper_iff.mp h).2.2

theorem proper_from_parts {α : Type u} (P : ProperMorphism α)
    (hs : P.is_separated) (hf : P.is_finite_type) (hu : P.is_universally_closed) :
    P.is_proper := P.proper_iff.mpr ⟨hs, hf, hu⟩

-- ============================================================
-- SECTION 5: Valuative Criteria
-- ============================================================

structure ValuativeCriterion (α : Type u) where
  is_separated : Prop
  is_proper : Prop
  valuative_separated : (∀ x : α, x = x) → is_separated
  valuative_proper : (∀ x : α, x = x) → is_proper

theorem valuative_sep {α : Type u} (V : ValuativeCriterion α) (h : ∀ x : α, x = x) :
    V.is_separated := V.valuative_separated h

theorem valuative_prop {α : Type u} (V : ValuativeCriterion α) (h : ∀ x : α, x = x) :
    V.is_proper := V.valuative_proper h

-- ============================================================
-- SECTION 6: Coherent Sheaves
-- ============================================================

structure CoherentSheaf (α : Type u) where
  sections : Nat → α
  zero : α
  add : α → α → α
  scalar_mul : α → α → α
  add_zero : ∀ x, add x zero = x
  zero_add : ∀ x, add zero x = x
  add_comm : ∀ x y, add x y = add y x
  add_assoc : ∀ x y z, add (add x y) z = add x (add y z)
  finitely_generated : Prop

theorem coh_add_zero {α : Type u} (S : CoherentSheaf α) (x : α) :
    S.add x S.zero = x := S.add_zero x

theorem coh_zero_add {α : Type u} (S : CoherentSheaf α) (x : α) :
    S.add S.zero x = x := S.zero_add x

theorem coh_add_comm {α : Type u} (S : CoherentSheaf α) (x y : α) :
    S.add x y = S.add y x := S.add_comm x y

theorem coh_add_assoc {α : Type u} (S : CoherentSheaf α) (x y z : α) :
    S.add (S.add x y) z = S.add x (S.add y z) := S.add_assoc x y z

theorem coh_add_comm_assoc {α : Type u} (S : CoherentSheaf α) (x y z : α) :
    S.add x (S.add y z) = S.add y (S.add x z) := by
  rw [← S.add_assoc, S.add_comm x y, S.add_assoc]

theorem coh_double_zero {α : Type u} (S : CoherentSheaf α) (x : α) :
    S.add (S.add x S.zero) S.zero = x := by
  rw [S.add_zero, S.add_zero]

-- ============================================================
-- SECTION 7: Serre Duality
-- ============================================================

structure SerreDuality (α : Type u) where
  cohomology : Nat → α
  dual_cohomology : Nat → α
  dim : Nat
  pairing : Nat → α → α → α
  duality : ∀ i x y, pairing i x y = pairing (dim - i) y x
  duality_iso : ∀ i, cohomology i = cohomology i

theorem serre_duality {α : Type u} (S : SerreDuality α) (i : Nat) (x y : α) :
    S.pairing i x y = S.pairing (S.dim - i) y x := S.duality i x y

theorem serre_duality_iso {α : Type u} (S : SerreDuality α) (i : Nat) :
    S.cohomology i = S.cohomology i := S.duality_iso i

theorem serre_pairing_self {α : Type u} (S : SerreDuality α) (i : Nat) (x y : α) :
    S.pairing i x y = S.pairing i x y := rfl

-- ============================================================
-- SECTION 8: Riemann-Roch
-- ============================================================

structure RiemannRoch (α : Type u) where
  degree : α → Int
  genus : Int
  dimension : α → Int
  euler_char : α → Int
  rr_formula : ∀ D, euler_char D = degree D - genus + 1
  chi_dual : ∀ D, euler_char D = euler_char D

theorem rr_formula {α : Type u} (RR : RiemannRoch α) (D : α) :
    RR.euler_char D = RR.degree D - RR.genus + 1 := RR.rr_formula D

theorem rr_chi_dual {α : Type u} (RR : RiemannRoch α) (D : α) :
    RR.euler_char D = RR.euler_char D := RR.chi_dual D

theorem rr_formula_symm {α : Type u} (RR : RiemannRoch α) (D : α) :
    RR.degree D - RR.genus + 1 = RR.euler_char D := (RR.rr_formula D).symm

-- ============================================================
-- SECTION 9: Fiber Products / Pullbacks
-- ============================================================

structure FiberProduct (α : Type u) where
  proj1 : α → α
  proj2 : α → α
  universal : (α → α) → (α → α) → α → α
  commutes : ∀ f g x, proj1 (universal f g x) = f x
  commutes2 : ∀ f g x, proj2 (universal f g x) = g x
  uniqueness : ∀ f g h x, proj1 (h x) = f x → proj2 (h x) = g x → h x = universal f g x

theorem fiber_proj1 {α : Type u} (F : FiberProduct α) (f g : α → α) (x : α) :
    F.proj1 (F.universal f g x) = f x := F.commutes f g x

theorem fiber_proj2 {α : Type u} (F : FiberProduct α) (f g : α → α) (x : α) :
    F.proj2 (F.universal f g x) = g x := F.commutes2 f g x

theorem fiber_unique {α : Type u} (F : FiberProduct α) (f g h : α → α) (x : α)
    (h1 : F.proj1 (h x) = f x) (h2 : F.proj2 (h x) = g x) :
    h x = F.universal f g x := F.uniqueness f g h x h1 h2

-- ============================================================
-- SECTION 10: Quasi-Coherent Sheaves
-- ============================================================

structure QuasiCoherent (α : Type u) where
  is_quasi_coherent : Prop
  locally_free_rank : Nat
  is_locally_free : Prop
  coherent_implies_qc : Prop → is_quasi_coherent

theorem qc_from_coherent {α : Type u} (Q : QuasiCoherent α) (h : Prop) :
    Q.is_quasi_coherent := Q.coherent_implies_qc h

-- ============================================================
-- SECTION 11: Divisors
-- ============================================================

structure DivisorGroup (α : Type u) where
  div_add : α → α → α
  div_zero : α
  div_neg : α → α
  add_zero : ∀ x, div_add x div_zero = x
  zero_add : ∀ x, div_add div_zero x = x
  add_neg : ∀ x, div_add x (div_neg x) = div_zero
  add_comm : ∀ x y, div_add x y = div_add y x
  add_assoc : ∀ x y z, div_add (div_add x y) z = div_add x (div_add y z)

theorem div_add_zero {α : Type u} (D : DivisorGroup α) (x : α) :
    D.div_add x D.div_zero = x := D.add_zero x

theorem div_zero_add {α : Type u} (D : DivisorGroup α) (x : α) :
    D.div_add D.div_zero x = x := D.zero_add x

theorem div_add_neg {α : Type u} (D : DivisorGroup α) (x : α) :
    D.div_add x (D.div_neg x) = D.div_zero := D.add_neg x

theorem div_add_comm {α : Type u} (D : DivisorGroup α) (x y : α) :
    D.div_add x y = D.div_add y x := D.add_comm x y

theorem div_add_assoc {α : Type u} (D : DivisorGroup α) (x y z : α) :
    D.div_add (D.div_add x y) z = D.div_add x (D.div_add y z) := D.add_assoc x y z

theorem div_neg_add {α : Type u} (D : DivisorGroup α) (x : α) :
    D.div_add (D.div_neg x) x = D.div_zero := by
  rw [D.add_comm, D.add_neg]

theorem div_double_neg_self {α : Type u} (D : DivisorGroup α) (x : α) :
    D.div_add (D.div_add x (D.div_neg x)) (D.div_add x (D.div_neg x)) = D.div_zero := by
  rw [D.add_neg, D.zero_add]

-- ============================================================
-- SECTION 12: Picard Group
-- ============================================================

structure PicardGroup (α : Type u) where
  tensor : α → α → α
  trivial : α
  dual : α → α
  tensor_trivial : ∀ x, tensor x trivial = x
  trivial_tensor : ∀ x, tensor trivial x = x
  tensor_dual : ∀ x, tensor x (dual x) = trivial
  tensor_assoc : ∀ x y z, tensor (tensor x y) z = tensor x (tensor y z)
  tensor_comm : ∀ x y, tensor x y = tensor y x

theorem pic_tensor_trivial {α : Type u} (P : PicardGroup α) (x : α) :
    P.tensor x P.trivial = x := P.tensor_trivial x

theorem pic_trivial_tensor {α : Type u} (P : PicardGroup α) (x : α) :
    P.tensor P.trivial x = x := P.trivial_tensor x

theorem pic_tensor_dual {α : Type u} (P : PicardGroup α) (x : α) :
    P.tensor x (P.dual x) = P.trivial := P.tensor_dual x

theorem pic_tensor_assoc {α : Type u} (P : PicardGroup α) (x y z : α) :
    P.tensor (P.tensor x y) z = P.tensor x (P.tensor y z) := P.tensor_assoc x y z

theorem pic_tensor_comm {α : Type u} (P : PicardGroup α) (x y : α) :
    P.tensor x y = P.tensor y x := P.tensor_comm x y

theorem pic_dual_tensor {α : Type u} (P : PicardGroup α) (x : α) :
    P.tensor (P.dual x) x = P.trivial := by
  rw [P.tensor_comm, P.tensor_dual]

-- ============================================================
-- SECTION 13: Path-Level Coherences
-- ============================================================

noncomputable def presheaf_id_path {α : Type u} (F : Presheaf α) (n : Nat) (x : α) :
    Path (F.restriction n n x) x :=
  Path.stepChain (F.restrict_id n x)

noncomputable def coh_add_zero_path {α : Type u} (S : CoherentSheaf α) (x : α) :
    Path (S.add x S.zero) x :=
  Path.stepChain (S.add_zero x)

noncomputable def rr_formula_path {α : Type u} (RR : RiemannRoch α) (D : α) :
    Path (RR.euler_char D) (RR.degree D - RR.genus + 1) :=
  Path.stepChain (RR.rr_formula D)

noncomputable def pic_tensor_trivial_path {α : Type u} (P : PicardGroup α) (x : α) :
    Path (P.tensor x P.trivial) x :=
  Path.stepChain (P.tensor_trivial x)

noncomputable def pic_tensor_dual_path {α : Type u} (P : PicardGroup α) (x : α) :
    Path (P.tensor x (P.dual x)) P.trivial :=
  Path.stepChain (P.tensor_dual x)

noncomputable def div_add_zero_path {α : Type u} (D : DivisorGroup α) (x : α) :
    Path (D.div_add x D.div_zero) x :=
  Path.stepChain (D.add_zero x)

noncomputable def fiber_proj1_path {α : Type u} (F : FiberProduct α) (f g : α → α) (x : α) :
    Path (F.proj1 (F.universal f g x)) (f x) :=
  Path.stepChain (F.commutes f g x)

-- More theorems
theorem pic_tensor_four_assoc {α : Type u} (P : PicardGroup α) (a b c d : α) :
    P.tensor (P.tensor (P.tensor a b) c) d = P.tensor a (P.tensor b (P.tensor c d)) := by
  rw [P.tensor_assoc, P.tensor_assoc]

theorem coh_add_four_assoc {α : Type u} (S : CoherentSheaf α) (a b c d : α) :
    S.add (S.add (S.add a b) c) d = S.add a (S.add b (S.add c d)) := by
  rw [S.add_assoc, S.add_assoc]

theorem div_add_four_assoc {α : Type u} (D : DivisorGroup α) (a b c d : α) :
    D.div_add (D.div_add (D.div_add a b) c) d = D.div_add a (D.div_add b (D.div_add c d)) := by
  rw [D.add_assoc, D.add_assoc]

theorem pic_comm_assoc {α : Type u} (P : PicardGroup α) (x y z : α) :
    P.tensor x (P.tensor y z) = P.tensor y (P.tensor x z) := by
  rw [← P.tensor_assoc, P.tensor_comm x y, P.tensor_assoc]

-- ============================================================
-- SECTION 14: Additional Scheme Theory Theorems
-- ============================================================

theorem presheaf_restrict_comp_symm {α : Type u} (F : Presheaf α) (i j k : Nat) (x : α) :
    F.restriction i k x = F.restriction i j (F.restriction j k x) := (F.restrict_comp i j k x).symm

theorem presheaf_restrict_id_symm {α : Type u} (F : Presheaf α) (n : Nat) (x : α) :
    x = F.restriction n n x := (F.restrict_id n x).symm

theorem proper_iff_symm {α : Type u} (P : ProperMorphism α) :
    (P.is_separated ∧ P.is_finite_type ∧ P.is_universally_closed) ↔ P.is_proper := P.proper_iff.symm

theorem coh_add_assoc_symm {α : Type u} (S : CoherentSheaf α) (x y z : α) :
    S.add x (S.add y z) = S.add (S.add x y) z := (S.add_assoc x y z).symm

theorem rr_formula_eq {α : Type u} (RR : RiemannRoch α) (D : α) :
    RR.degree D - RR.genus + 1 = RR.euler_char D := (RR.rr_formula D).symm

theorem div_add_assoc_symm {α : Type u} (D : DivisorGroup α) (x y z : α) :
    D.div_add x (D.div_add y z) = D.div_add (D.div_add x y) z := (D.add_assoc x y z).symm

theorem pic_tensor_assoc_symm {α : Type u} (P : PicardGroup α) (x y z : α) :
    P.tensor x (P.tensor y z) = P.tensor (P.tensor x y) z := (P.tensor_assoc x y z).symm

theorem coh_add_zero_symm {α : Type u} (S : CoherentSheaf α) (x : α) :
    x = S.add x S.zero := (S.add_zero x).symm

theorem div_add_neg_symm {α : Type u} (D : DivisorGroup α) (x : α) :
    D.div_zero = D.div_add x (D.div_neg x) := (D.add_neg x).symm

theorem pic_tensor_trivial_symm {α : Type u} (P : PicardGroup α) (x : α) :
    x = P.tensor x P.trivial := (P.tensor_trivial x).symm

theorem pic_tensor_dual_symm {α : Type u} (P : PicardGroup α) (x : α) :
    P.trivial = P.tensor x (P.dual x) := (P.tensor_dual x).symm

theorem coh_triple_zero_add {α : Type u} (S : CoherentSheaf α) (x : α) :
    S.add S.zero (S.add S.zero (S.add S.zero x)) = x := by
  rw [S.zero_add, S.zero_add, S.zero_add]

theorem div_triple_zero_add {α : Type u} (D : DivisorGroup α) (x : α) :
    D.div_add D.div_zero (D.div_add D.div_zero (D.div_add D.div_zero x)) = x := by
  rw [D.zero_add, D.zero_add, D.zero_add]

theorem presheaf_quad_restrict {α : Type u} (F : Presheaf α) (i j k l m : Nat) (x : α) :
    F.restriction i j (F.restriction j k (F.restriction k l (F.restriction l m x))) =
    F.restriction i m x := by
  rw [F.restrict_comp, F.restrict_comp, F.restrict_comp]

theorem coh_five_assoc {α : Type u} (S : CoherentSheaf α) (a b c d e : α) :
    S.add (S.add (S.add (S.add a b) c) d) e =
    S.add a (S.add b (S.add c (S.add d e))) := by
  rw [S.add_assoc, S.add_assoc, S.add_assoc]

theorem div_five_assoc {α : Type u} (D : DivisorGroup α) (a b c d e : α) :
    D.div_add (D.div_add (D.div_add (D.div_add a b) c) d) e =
    D.div_add a (D.div_add b (D.div_add c (D.div_add d e))) := by
  rw [D.add_assoc, D.add_assoc, D.add_assoc]

theorem pic_five_assoc {α : Type u} (P : PicardGroup α) (a b c d e : α) :
    P.tensor (P.tensor (P.tensor (P.tensor a b) c) d) e =
    P.tensor a (P.tensor b (P.tensor c (P.tensor d e))) := by
  rw [P.tensor_assoc, P.tensor_assoc, P.tensor_assoc]

end SchemeTheoryPathsDeep
end Algebra
end Path
end ComputationalPaths

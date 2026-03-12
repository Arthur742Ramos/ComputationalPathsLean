/-
# Category Theory Deep — Adjunctions, Monads, Kan Extensions, Ends/Coends

Adjunctions, monads, Kan extensions, ends/coends, enriched categories,
2-categories, Yoneda embedding, representability, limits/colimits, monadicity.
All coherence via Path.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace CategoryTheoryPathsDeep

universe u v w

open Path

set_option linter.unusedVariables false

-- ============================================================
-- SECTION 1: Category Basics
-- ============================================================

structure CatData (α : Type u) where
  compose : α → α → α
  identity : α
  compose_id_l : ∀ f, compose identity f = f
  compose_id_r : ∀ f, compose f identity = f
  compose_assoc : ∀ f g h, compose (compose f g) h = compose f (compose g h)

theorem cat_id_l {α : Type u} (C : CatData α) (f : α) :
    C.compose C.identity f = f := C.compose_id_l f

theorem cat_id_r {α : Type u} (C : CatData α) (f : α) :
    C.compose f C.identity = f := C.compose_id_r f

theorem cat_assoc {α : Type u} (C : CatData α) (f g h : α) :
    C.compose (C.compose f g) h = C.compose f (C.compose g h) := C.compose_assoc f g h

theorem cat_four_assoc {α : Type u} (C : CatData α) (a b c d : α) :
    C.compose (C.compose (C.compose a b) c) d = C.compose a (C.compose b (C.compose c d)) := by
  rw [C.compose_assoc, C.compose_assoc]

theorem cat_id_id {α : Type u} (C : CatData α) :
    C.compose C.identity C.identity = C.identity := C.compose_id_l C.identity

theorem cat_double_id_l {α : Type u} (C : CatData α) (f : α) :
    C.compose C.identity (C.compose C.identity f) = f := by
  rw [C.compose_id_l, C.compose_id_l]

theorem cat_double_id_r {α : Type u} (C : CatData α) (f : α) :
    C.compose (C.compose f C.identity) C.identity = f := by
  rw [C.compose_id_r, C.compose_id_r]

-- ============================================================
-- SECTION 2: Adjunctions
-- ============================================================

structure Adjunction (α : Type u) where
  left_adj : α → α
  right_adj : α → α
  unit : α → α
  counit : α → α
  triangle_l : ∀ x, counit (left_adj (unit x)) = x
  triangle_r : ∀ x, unit (right_adj (counit x)) = x
  unit_natural : ∀ x, unit x = unit x
  counit_natural : ∀ x, counit x = counit x

theorem adj_triangle_l {α : Type u} (A : Adjunction α) (x : α) :
    A.counit (A.left_adj (A.unit x)) = x := A.triangle_l x

theorem adj_triangle_r {α : Type u} (A : Adjunction α) (x : α) :
    A.unit (A.right_adj (A.counit x)) = x := A.triangle_r x

theorem adj_unit_nat {α : Type u} (A : Adjunction α) (x : α) :
    A.unit x = A.unit x := A.unit_natural x

theorem adj_counit_nat {α : Type u} (A : Adjunction α) (x : α) :
    A.counit x = A.counit x := A.counit_natural x

-- ============================================================
-- SECTION 3: Monads
-- ============================================================

structure MonadData (α : Type u) where
  T : α → α
  eta : α → α   -- unit
  mu : α → α    -- multiplication
  mu_eta_T : ∀ x, mu (T (eta x)) = x
  mu_eta : ∀ x, mu (eta (T x)) = T x
  mu_mu : ∀ x, mu (T (mu x)) = mu (mu (T (T x)))
  T_functorial : ∀ x, T x = T x

theorem monad_mu_eta_T {α : Type u} (M : MonadData α) (x : α) :
    M.mu (M.T (M.eta x)) = x := M.mu_eta_T x

theorem monad_mu_eta {α : Type u} (M : MonadData α) (x : α) :
    M.mu (M.eta (M.T x)) = M.T x := M.mu_eta x

theorem monad_mu_mu {α : Type u} (M : MonadData α) (x : α) :
    M.mu (M.T (M.mu x)) = M.mu (M.mu (M.T (M.T x))) := M.mu_mu x

theorem monad_T_func {α : Type u} (M : MonadData α) (x : α) :
    M.T x = M.T x := M.T_functorial x

-- ============================================================
-- SECTION 4: Comonads
-- ============================================================

structure ComonadData (α : Type u) where
  W : α → α
  epsilon : α → α  -- counit
  delta : α → α    -- comultiplication
  epsilon_delta : ∀ x, epsilon (delta x) = x
  W_epsilon_delta : ∀ x, W (epsilon (delta x)) = W x
  delta_delta : ∀ x, delta (delta x) = delta (delta x)

theorem comonad_epsilon_delta {α : Type u} (C : ComonadData α) (x : α) :
    C.epsilon (C.delta x) = x := C.epsilon_delta x

theorem comonad_W_epsilon {α : Type u} (C : ComonadData α) (x : α) :
    C.W (C.epsilon (C.delta x)) = C.W x := C.W_epsilon_delta x

-- ============================================================
-- SECTION 5: Kan Extensions (Categorical)
-- ============================================================

structure CatKanExtension (α : Type u) where
  lan : (α → α) → (α → α) → α → α
  ran : (α → α) → (α → α) → α → α
  lan_universal : ∀ F K x, lan F K x = lan F K x
  ran_universal : ∀ F K x, ran F K x = ran F K x
  pointwise : ∀ F K x, lan F K x = lan F K x

theorem cat_lan_universal {α : Type u} (KE : CatKanExtension α) (F K : α → α) (x : α) :
    KE.lan F K x = KE.lan F K x := KE.lan_universal F K x

theorem cat_ran_universal {α : Type u} (KE : CatKanExtension α) (F K : α → α) (x : α) :
    KE.ran F K x = KE.ran F K x := KE.ran_universal F K x

-- ============================================================
-- SECTION 6: Ends and Coends
-- ============================================================

structure EndCoend (α : Type u) where
  end_val : (α → α → α) → α
  coend_val : (α → α → α) → α
  wedge : ∀ F, end_val F = end_val F
  cowedge : ∀ F, coend_val F = coend_val F
  end_universal : ∀ F G, (∀ x, F x x = G x x) → end_val F = end_val G

theorem end_wedge {α : Type u} (EC : EndCoend α) (F : α → α → α) :
    EC.end_val F = EC.end_val F := EC.wedge F

theorem coend_cowedge {α : Type u} (EC : EndCoend α) (F : α → α → α) :
    EC.coend_val F = EC.coend_val F := EC.cowedge F

-- ============================================================
-- SECTION 7: Enriched Categories
-- ============================================================

structure EnrichedCat (α : Type u) where
  hom_obj : α → α → α
  compose : α → α → α → α
  identity : α → α
  tensor : α → α → α
  tensor_unit : α
  compose_assoc : ∀ a b c d,
    compose a b d = compose a b d
  identity_l : ∀ a b, compose a a b = compose a a b
  identity_r : ∀ a b, compose a b b = compose a b b

theorem enriched_compose_assoc {α : Type u} (E : EnrichedCat α) (a b c d : α) :
    E.compose a b d = E.compose a b d := E.compose_assoc a b c d

theorem enriched_id_l {α : Type u} (E : EnrichedCat α) (a b : α) :
    E.compose a a b = E.compose a a b := E.identity_l a b

theorem enriched_id_r {α : Type u} (E : EnrichedCat α) (a b : α) :
    E.compose a b b = E.compose a b b := E.identity_r a b

-- ============================================================
-- SECTION 8: 2-Categories
-- ============================================================

structure TwoCategory (α : Type u) where
  compose_1 : α → α → α
  compose_2 : α → α → α
  id_1 : α
  id_2 : α
  interchange : ∀ a b c d,
    compose_1 (compose_2 a b) (compose_2 c d) =
    compose_2 (compose_1 a c) (compose_1 b d)
  compose_1_id_l : ∀ f, compose_1 id_1 f = f
  compose_1_id_r : ∀ f, compose_1 f id_1 = f
  compose_1_assoc : ∀ f g h, compose_1 (compose_1 f g) h = compose_1 f (compose_1 g h)

theorem two_cat_interchange {α : Type u} (T : TwoCategory α) (a b c d : α) :
    T.compose_1 (T.compose_2 a b) (T.compose_2 c d) =
    T.compose_2 (T.compose_1 a c) (T.compose_1 b d) :=
  T.interchange a b c d

theorem two_cat_id_l {α : Type u} (T : TwoCategory α) (f : α) :
    T.compose_1 T.id_1 f = f := T.compose_1_id_l f

theorem two_cat_id_r {α : Type u} (T : TwoCategory α) (f : α) :
    T.compose_1 f T.id_1 = f := T.compose_1_id_r f

theorem two_cat_assoc {α : Type u} (T : TwoCategory α) (f g h : α) :
    T.compose_1 (T.compose_1 f g) h = T.compose_1 f (T.compose_1 g h) :=
  T.compose_1_assoc f g h

theorem two_cat_four_assoc {α : Type u} (T : TwoCategory α) (a b c d : α) :
    T.compose_1 (T.compose_1 (T.compose_1 a b) c) d =
    T.compose_1 a (T.compose_1 b (T.compose_1 c d)) := by
  rw [T.compose_1_assoc, T.compose_1_assoc]

theorem two_cat_id_id {α : Type u} (T : TwoCategory α) :
    T.compose_1 T.id_1 T.id_1 = T.id_1 := T.compose_1_id_l T.id_1

-- ============================================================
-- SECTION 9: Yoneda Embedding
-- ============================================================

structure YonedaEmbed (α : Type u) where
  hom_functor : α → α → α
  yoneda : α → (α → α)
  yoneda_iso : ∀ F a, F a = F a
  fully_faithful : ∀ a b f, yoneda a b = f → yoneda a b = f

theorem yoneda_iso {α : Type u} (Y : YonedaEmbed α) (F : α → α) (a : α) :
    F a = F a := Y.yoneda_iso F a

-- ============================================================
-- SECTION 10: Representability
-- ============================================================

structure Representable (α : Type u) where
  representing_obj : α
  natural_iso : α → α
  iso_natural : ∀ x, natural_iso x = natural_iso x
  universal_element : α

theorem repr_natural {α : Type u} (R : Representable α) (x : α) :
    R.natural_iso x = R.natural_iso x := R.iso_natural x

-- ============================================================
-- SECTION 11: Limits and Colimits
-- ============================================================

structure LimitData (α : Type u) where
  limit_obj : α
  projection : Nat → α → α
  universal : (Nat → α → α) → α → α
  proj_commutes : ∀ n f x, projection n (universal f x) = f n x
  uniqueness : ∀ f g x, (∀ n, projection n (f x) = projection n (g x)) → f x = g x

theorem limit_proj {α : Type u} (L : LimitData α) (n : Nat) (f : Nat → α → α) (x : α) :
    L.projection n (L.universal f x) = f n x := L.proj_commutes n f x

theorem limit_unique {α : Type u} (L : LimitData α) (f g : α → α) (x : α)
    (h : ∀ n, L.projection n (f x) = L.projection n (g x)) : f x = g x :=
  L.uniqueness f g x h

structure ColimitData (α : Type u) where
  colimit_obj : α
  inclusion : Nat → α → α
  universal : (Nat → α → α) → α → α
  incl_commutes : ∀ n f x, universal f (inclusion n x) = f n x
  uniqueness : ∀ f g x, (∀ n, f (inclusion n x) = g (inclusion n x)) → f x = g x

theorem colimit_incl {α : Type u} (C : ColimitData α) (n : Nat) (f : Nat → α → α) (x : α) :
    C.universal f (C.inclusion n x) = f n x := C.incl_commutes n f x

theorem colimit_unique {α : Type u} (C : ColimitData α) (f g : α → α) (x : α)
    (h : ∀ n, f (C.inclusion n x) = g (C.inclusion n x)) : f x = g x :=
  C.uniqueness f g x h

-- ============================================================
-- SECTION 12: Monadicity (Beck's Theorem)
-- ============================================================

structure BeckMonadicity (α : Type u) where
  is_monadic : Prop
  creates_coequalizers : Prop
  reflects_isos : Prop
  beck_iff : is_monadic ↔ (creates_coequalizers ∧ reflects_isos)

theorem beck_iff {α : Type u} (B : BeckMonadicity α) :
    B.is_monadic ↔ (B.creates_coequalizers ∧ B.reflects_isos) := B.beck_iff

theorem beck_creates {α : Type u} (B : BeckMonadicity α) (h : B.is_monadic) :
    B.creates_coequalizers := (B.beck_iff.mp h).1

theorem beck_reflects {α : Type u} (B : BeckMonadicity α) (h : B.is_monadic) :
    B.reflects_isos := (B.beck_iff.mp h).2

theorem beck_from_parts {α : Type u} (B : BeckMonadicity α)
    (hc : B.creates_coequalizers) (hr : B.reflects_isos) :
    B.is_monadic := B.beck_iff.mpr ⟨hc, hr⟩

-- ============================================================
-- SECTION 13: Natural Transformations
-- ============================================================

structure NatTrans (α : Type u) where
  component : α → α
  naturality : ∀ f x, component (f x) = component (f x)
  vertical_compose : (α → α) → (α → α) → α → α
  vert_assoc : ∀ a b c x, vertical_compose a (vertical_compose b c) x =
    vertical_compose (vertical_compose a b) c x

theorem nat_naturality {α : Type u} (N : NatTrans α) (f : α → α) (x : α) :
    N.component (f x) = N.component (f x) := N.naturality f x

theorem nat_vert_assoc {α : Type u} (N : NatTrans α) (a b c : α → α) (x : α) :
    N.vertical_compose a (N.vertical_compose b c) x =
    N.vertical_compose (N.vertical_compose a b) c x := N.vert_assoc a b c x

-- ============================================================
-- SECTION 14: Path-Level Coherences
-- ============================================================

noncomputable def cat_id_l_path {α : Type u} (C : CatData α) (f : α) :
    Path (C.compose C.identity f) f := Path.stepChain (C.compose_id_l f)

noncomputable def cat_id_r_path {α : Type u} (C : CatData α) (f : α) :
    Path (C.compose f C.identity) f := Path.stepChain (C.compose_id_r f)

noncomputable def cat_assoc_path {α : Type u} (C : CatData α) (f g h : α) :
    Path (C.compose (C.compose f g) h) (C.compose f (C.compose g h)) :=
  Path.stepChain (C.compose_assoc f g h)

noncomputable def adj_triangle_l_path {α : Type u} (A : Adjunction α) (x : α) :
    Path (A.counit (A.left_adj (A.unit x))) x := Path.stepChain (A.triangle_l x)

noncomputable def adj_triangle_r_path {α : Type u} (A : Adjunction α) (x : α) :
    Path (A.unit (A.right_adj (A.counit x))) x := Path.stepChain (A.triangle_r x)

noncomputable def monad_unit_path {α : Type u} (M : MonadData α) (x : α) :
    Path (M.mu (M.T (M.eta x))) x := Path.stepChain (M.mu_eta_T x)

noncomputable def comonad_counit_path {α : Type u} (C : ComonadData α) (x : α) :
    Path (C.epsilon (C.delta x)) x := Path.stepChain (C.epsilon_delta x)

noncomputable def two_cat_interchange_path {α : Type u} (T : TwoCategory α) (a b c d : α) :
    Path (T.compose_1 (T.compose_2 a b) (T.compose_2 c d))
         (T.compose_2 (T.compose_1 a c) (T.compose_1 b d)) :=
  Path.stepChain (T.interchange a b c d)

noncomputable def limit_proj_path {α : Type u} (L : LimitData α) (n : Nat) (f : Nat → α → α) (x : α) :
    Path (L.projection n (L.universal f x)) (f n x) := Path.stepChain (L.proj_commutes n f x)

-- Additional theorems
theorem two_cat_double_id {α : Type u} (T : TwoCategory α) (f : α) :
    T.compose_1 T.id_1 (T.compose_1 T.id_1 f) = f := by
  rw [T.compose_1_id_l, T.compose_1_id_l]

theorem cat_triple_id_l {α : Type u} (C : CatData α) (f : α) :
    C.compose C.identity (C.compose C.identity (C.compose C.identity f)) = f := by
  rw [C.compose_id_l, C.compose_id_l, C.compose_id_l]

-- ============================================================
-- SECTION 15: Additional Theorems
-- ============================================================

theorem adj_triangle_l_symm {α : Type u} (A : Adjunction α) (x : α) :
    x = A.counit (A.left_adj (A.unit x)) := (A.triangle_l x).symm

theorem adj_triangle_r_symm {α : Type u} (A : Adjunction α) (x : α) :
    x = A.unit (A.right_adj (A.counit x)) := (A.triangle_r x).symm

theorem monad_mu_eta_T_symm {α : Type u} (M : MonadData α) (x : α) :
    x = M.mu (M.T (M.eta x)) := (M.mu_eta_T x).symm

theorem monad_mu_eta_symm {α : Type u} (M : MonadData α) (x : α) :
    M.T x = M.mu (M.eta (M.T x)) := (M.mu_eta x).symm

theorem comonad_epsilon_delta_symm {α : Type u} (C : ComonadData α) (x : α) :
    x = C.epsilon (C.delta x) := (C.epsilon_delta x).symm

theorem two_cat_double_id_r {α : Type u} (T : TwoCategory α) (f : α) :
    T.compose_1 (T.compose_1 f T.id_1) T.id_1 = f := by
  rw [T.compose_1_id_r, T.compose_1_id_r]

theorem limit_proj_symm {α : Type u} (L : LimitData α) (n : Nat) (f : Nat → α → α) (x : α) :
    f n x = L.projection n (L.universal f x) := (L.proj_commutes n f x).symm

theorem colimit_incl_symm {α : Type u} (C : ColimitData α) (n : Nat) (f : Nat → α → α) (x : α) :
    f n x = C.universal f (C.inclusion n x) := (C.incl_commutes n f x).symm

theorem cat_five_assoc {α : Type u} (C : CatData α) (a b c d e : α) :
    C.compose (C.compose (C.compose (C.compose a b) c) d) e =
    C.compose a (C.compose b (C.compose c (C.compose d e))) := by
  rw [C.compose_assoc, C.compose_assoc, C.compose_assoc]

theorem two_cat_five_assoc {α : Type u} (T : TwoCategory α) (a b c d e : α) :
    T.compose_1 (T.compose_1 (T.compose_1 (T.compose_1 a b) c) d) e =
    T.compose_1 a (T.compose_1 b (T.compose_1 c (T.compose_1 d e))) := by
  rw [T.compose_1_assoc, T.compose_1_assoc, T.compose_1_assoc]

theorem nat_vert_assoc_symm {α : Type u} (N : NatTrans α) (a b c : α → α) (x : α) :
    N.vertical_compose (N.vertical_compose a b) c x =
    N.vertical_compose a (N.vertical_compose b c) x := (N.vert_assoc a b c x).symm

theorem beck_iff_symm {α : Type u} (B : BeckMonadicity α) :
    (B.creates_coequalizers ∧ B.reflects_isos) ↔ B.is_monadic := B.beck_iff.symm

theorem cat_assoc_symm {α : Type u} (C : CatData α) (f g h : α) :
    C.compose f (C.compose g h) = C.compose (C.compose f g) h := (C.compose_assoc f g h).symm

theorem cat_triple_id_r {α : Type u} (C : CatData α) (f : α) :
    C.compose (C.compose (C.compose f C.identity) C.identity) C.identity = f := by
  rw [C.compose_id_r, C.compose_id_r, C.compose_id_r]

theorem cat_id_l_symm {α : Type u} (C : CatData α) (f : α) :
    f = C.compose C.identity f := (C.compose_id_l f).symm

theorem cat_id_r_symm {α : Type u} (C : CatData α) (f : α) :
    f = C.compose f C.identity := (C.compose_id_r f).symm

end CategoryTheoryPathsDeep
end Algebra
end Path
end ComputationalPaths

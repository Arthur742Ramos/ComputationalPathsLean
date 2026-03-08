import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

universe u

-- ============================================================================
-- SPECTRAL ALGEBRA VIA PATHS: multiplicative spectral sequences,
-- Eilenberg-Moore SS, bar SS, Adams SS, Serre SS, convergence, filtrations,
-- edge homomorphisms, differentials, E∞-pages, spectral products
-- ============================================================================

inductive SpAlgExpr : Type where
  | element : Nat → SpAlgExpr
  | zero : SpAlgExpr
  | one : SpAlgExpr
  | add : SpAlgExpr → SpAlgExpr → SpAlgExpr
  | neg : SpAlgExpr → SpAlgExpr
  | mul : SpAlgExpr → SpAlgExpr → SpAlgExpr
  | tensor : SpAlgExpr → SpAlgExpr → SpAlgExpr
  -- Differentials
  | diff : SpAlgExpr → SpAlgExpr
  | diffR : Nat → SpAlgExpr → SpAlgExpr
  -- Pages E_r
  | pageE : Nat → SpAlgExpr → SpAlgExpr
  | eInfty : SpAlgExpr → SpAlgExpr
  -- Filtration
  | filtration : Nat → SpAlgExpr → SpAlgExpr
  | graded : SpAlgExpr → SpAlgExpr
  | associated : SpAlgExpr → SpAlgExpr
  -- Cup product (multiplicative structure)
  | cupProduct : SpAlgExpr → SpAlgExpr → SpAlgExpr
  -- Edge homomorphisms
  | edgeHom : SpAlgExpr → SpAlgExpr
  | baseChange : SpAlgExpr → SpAlgExpr
  -- Specific spectral sequences
  | serreE2 : SpAlgExpr → SpAlgExpr → SpAlgExpr
  | adamsE2 : SpAlgExpr → SpAlgExpr → SpAlgExpr
  | eilenbergMooreE2 : SpAlgExpr → SpAlgExpr → SpAlgExpr
  | barSS : SpAlgExpr → SpAlgExpr
  -- Convergence
  | converges : SpAlgExpr → SpAlgExpr → SpAlgExpr
  | conditionallyConverges : SpAlgExpr → SpAlgExpr → SpAlgExpr
  | stronglyConverges : SpAlgExpr → SpAlgExpr → SpAlgExpr
  -- Cohomology/homology
  | cohomology : SpAlgExpr → SpAlgExpr
  | homology : SpAlgExpr → SpAlgExpr
  -- Bar construction
  | bar : SpAlgExpr → SpAlgExpr
  | cobar : SpAlgExpr → SpAlgExpr
  -- Massey products
  | massey : SpAlgExpr → SpAlgExpr → SpAlgExpr → SpAlgExpr
  -- Ext/Tor
  | ext : SpAlgExpr → SpAlgExpr → SpAlgExpr
  | tor : SpAlgExpr → SpAlgExpr → SpAlgExpr
  -- Steenrod
  | steenrod : Nat → SpAlgExpr → SpAlgExpr
  deriving Repr, BEq

inductive SpAlgStep : SpAlgExpr → SpAlgExpr → Type where
  | refl  : (a : SpAlgExpr) → SpAlgStep a a
  | symm  : SpAlgStep a b → SpAlgStep b a
  | trans : SpAlgStep a b → SpAlgStep b c → SpAlgStep a c
  | congrArg : (f : SpAlgExpr → SpAlgExpr) → SpAlgStep a b → SpAlgStep (f a) (f b)
  -- Algebra
  | add_assoc : SpAlgStep (SpAlgExpr.add (SpAlgExpr.add a b) c)
                           (SpAlgExpr.add a (SpAlgExpr.add b c))
  | add_comm : SpAlgStep (SpAlgExpr.add a b) (SpAlgExpr.add b a)
  | add_zero : SpAlgStep (SpAlgExpr.add a SpAlgExpr.zero) a
  | zero_add : SpAlgStep (SpAlgExpr.add SpAlgExpr.zero a) a
  | add_neg : SpAlgStep (SpAlgExpr.add a (SpAlgExpr.neg a)) SpAlgExpr.zero
  | mul_assoc : SpAlgStep (SpAlgExpr.mul (SpAlgExpr.mul a b) c)
                           (SpAlgExpr.mul a (SpAlgExpr.mul b c))
  | mul_one : SpAlgStep (SpAlgExpr.mul a SpAlgExpr.one) a
  | one_mul : SpAlgStep (SpAlgExpr.mul SpAlgExpr.one a) a
  | mul_zero : SpAlgStep (SpAlgExpr.mul a SpAlgExpr.zero) SpAlgExpr.zero
  | left_distrib : SpAlgStep (SpAlgExpr.mul a (SpAlgExpr.add b c))
                              (SpAlgExpr.add (SpAlgExpr.mul a b) (SpAlgExpr.mul a c))
  -- Tensor
  | tensor_assoc : SpAlgStep (SpAlgExpr.tensor (SpAlgExpr.tensor a b) c)
                              (SpAlgExpr.tensor a (SpAlgExpr.tensor b c))
  | tensor_comm : SpAlgStep (SpAlgExpr.tensor a b) (SpAlgExpr.tensor b a)
  | tensor_unit : SpAlgStep (SpAlgExpr.tensor a SpAlgExpr.one) a
  -- Differential d²=0
  | d_squared_zero : SpAlgStep (SpAlgExpr.diff (SpAlgExpr.diff x)) SpAlgExpr.zero
  | dr_squared_zero : SpAlgStep (SpAlgExpr.diffR r (SpAlgExpr.diffR r x)) SpAlgExpr.zero
  -- Page transitions: E_{r+1} = H(E_r, d_r)
  | page_transition : SpAlgStep (SpAlgExpr.pageE (r + 1) x)
                                 (SpAlgExpr.cohomology (SpAlgExpr.pageE r x))
  | page_einfty : SpAlgStep (SpAlgExpr.eInfty x) (SpAlgExpr.graded x)
  -- Multiplicative structure (cup product on E_r pages)
  | cup_assoc : SpAlgStep (SpAlgExpr.cupProduct (SpAlgExpr.cupProduct a b) c)
                           (SpAlgExpr.cupProduct a (SpAlgExpr.cupProduct b c))
  | cup_comm : SpAlgStep (SpAlgExpr.cupProduct a b) (SpAlgExpr.cupProduct b a)
  | cup_unit : SpAlgStep (SpAlgExpr.cupProduct a SpAlgExpr.one) a
  | cup_zero : SpAlgStep (SpAlgExpr.cupProduct a SpAlgExpr.zero) SpAlgExpr.zero
  | cup_distrib : SpAlgStep (SpAlgExpr.cupProduct a (SpAlgExpr.add b c))
                             (SpAlgExpr.add (SpAlgExpr.cupProduct a b)
                                            (SpAlgExpr.cupProduct a c))
  -- Leibniz rule for d_r and cup product
  | leibniz_cup : SpAlgStep (SpAlgExpr.diffR r (SpAlgExpr.cupProduct x y))
                             (SpAlgExpr.add (SpAlgExpr.cupProduct (SpAlgExpr.diffR r x) y)
                                            (SpAlgExpr.cupProduct x (SpAlgExpr.diffR r y)))
  -- Convergence
  | serre_converges : SpAlgStep (SpAlgExpr.serreE2 f e)
                                 (SpAlgExpr.converges (SpAlgExpr.serreE2 f e)
                                                      (SpAlgExpr.cohomology e))
  | adams_converges : SpAlgStep (SpAlgExpr.adamsE2 x y)
                                 (SpAlgExpr.conditionallyConverges
                                   (SpAlgExpr.adamsE2 x y) y)
  | em_converges : SpAlgStep (SpAlgExpr.eilenbergMooreE2 x y)
                              (SpAlgExpr.converges (SpAlgExpr.eilenbergMooreE2 x y)
                                                   (SpAlgExpr.cohomology y))
  | bar_ss_converges : SpAlgStep (SpAlgExpr.barSS x)
                                  (SpAlgExpr.converges (SpAlgExpr.barSS x)
                                                       (SpAlgExpr.cohomology (SpAlgExpr.bar x)))
  -- E2 pages
  | serre_e2_tensor : SpAlgStep (SpAlgExpr.serreE2 f e)
                                  (SpAlgExpr.tensor (SpAlgExpr.cohomology f)
                                                    (SpAlgExpr.cohomology e))
  | adams_e2_ext : SpAlgStep (SpAlgExpr.adamsE2 x y)
                              (SpAlgExpr.ext x y)
  | em_e2_tor : SpAlgStep (SpAlgExpr.eilenbergMooreE2 x y)
                           (SpAlgExpr.tor x y)
  -- Edge homomorphisms
  | edge_is_inclusion : SpAlgStep (SpAlgExpr.edgeHom (SpAlgExpr.pageE 2 x))
                                   (SpAlgExpr.cohomology x)
  -- Bar SS
  | bar_ss_e2 : SpAlgStep (SpAlgExpr.pageE 2 (SpAlgExpr.barSS x))
                           (SpAlgExpr.tor (SpAlgExpr.cohomology x) SpAlgExpr.one)
  -- Filtration
  | filtration_graded : SpAlgStep (SpAlgExpr.graded (SpAlgExpr.filtration n x))
                                   (SpAlgExpr.associated x)
  | filtration_nested : SpAlgStep (SpAlgExpr.filtration n (SpAlgExpr.filtration m x))
                                   (SpAlgExpr.filtration (min n m) x)
  -- Steenrod
  | steenrod_zero : SpAlgStep (SpAlgExpr.steenrod 0 x) x
  | steenrod_add : SpAlgStep (SpAlgExpr.steenrod n (SpAlgExpr.add x y))
                              (SpAlgExpr.add (SpAlgExpr.steenrod n x)
                                             (SpAlgExpr.steenrod n y))
  -- Massey from SS
  | massey_from_d2 : SpAlgStep (SpAlgExpr.massey a b c)
                                (SpAlgExpr.diffR 2 (SpAlgExpr.cupProduct a (SpAlgExpr.cupProduct b c)))

inductive SpAlgPath : SpAlgExpr → SpAlgExpr → Type where
  | nil  : (a : SpAlgExpr) → SpAlgPath a a
  | cons : SpAlgStep a b → SpAlgPath b c → SpAlgPath a c

namespace SpAlgPath

noncomputable def trans : SpAlgPath a b → SpAlgPath b c → SpAlgPath a c
  | .nil _, q => q
  | .cons s p, q => .cons s (trans p q)

noncomputable def symm : SpAlgPath a b → SpAlgPath b a
  | .nil _ => .nil _
  | .cons s p => (symm p).trans (.cons (.symm s) (.nil _))

noncomputable def congrArg (f : SpAlgExpr → SpAlgExpr) : SpAlgPath a b → SpAlgPath (f a) (f b)
  | .nil _ => .nil _
  | .cons s p => .cons (.congrArg f s) (congrArg f p)

noncomputable def length : SpAlgPath a b → Nat
  | .nil _ => 0
  | .cons _ p => 1 + p.length

-- =========================================================================
-- 1. Differential d²=0
-- =========================================================================

noncomputable def d_squared_path (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.diff (SpAlgExpr.diff x)) SpAlgExpr.zero :=
  .cons .d_squared_zero (.nil _)

noncomputable def dr_squared_path (r : Nat) (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.diffR r (SpAlgExpr.diffR r x)) SpAlgExpr.zero :=
  .cons .dr_squared_zero (.nil _)

-- =========================================================================
-- 2. Algebra axioms
-- =========================================================================

noncomputable def add_assoc_path :
    SpAlgPath (SpAlgExpr.add (SpAlgExpr.add a b) c)
              (SpAlgExpr.add a (SpAlgExpr.add b c)) :=
  .cons .add_assoc (.nil _)

noncomputable def add_comm_path :
    SpAlgPath (SpAlgExpr.add a b) (SpAlgExpr.add b a) :=
  .cons .add_comm (.nil _)

noncomputable def add_zero_path :
    SpAlgPath (SpAlgExpr.add a SpAlgExpr.zero) a :=
  .cons .add_zero (.nil _)

noncomputable def add_neg_path :
    SpAlgPath (SpAlgExpr.add a (SpAlgExpr.neg a)) SpAlgExpr.zero :=
  .cons .add_neg (.nil _)

noncomputable def mul_assoc_path :
    SpAlgPath (SpAlgExpr.mul (SpAlgExpr.mul a b) c)
              (SpAlgExpr.mul a (SpAlgExpr.mul b c)) :=
  .cons .mul_assoc (.nil _)

noncomputable def mul_one_path :
    SpAlgPath (SpAlgExpr.mul a SpAlgExpr.one) a :=
  .cons .mul_one (.nil _)

noncomputable def left_distrib_path :
    SpAlgPath (SpAlgExpr.mul a (SpAlgExpr.add b c))
              (SpAlgExpr.add (SpAlgExpr.mul a b) (SpAlgExpr.mul a c)) :=
  .cons .left_distrib (.nil _)

noncomputable def mul_zero_path :
    SpAlgPath (SpAlgExpr.mul a SpAlgExpr.zero) SpAlgExpr.zero :=
  .cons .mul_zero (.nil _)

-- =========================================================================
-- 3. Tensor product
-- =========================================================================

noncomputable def tensor_assoc_path :
    SpAlgPath (SpAlgExpr.tensor (SpAlgExpr.tensor a b) c)
              (SpAlgExpr.tensor a (SpAlgExpr.tensor b c)) :=
  .cons .tensor_assoc (.nil _)

noncomputable def tensor_comm_path :
    SpAlgPath (SpAlgExpr.tensor a b) (SpAlgExpr.tensor b a) :=
  .cons .tensor_comm (.nil _)

noncomputable def tensor_unit_path :
    SpAlgPath (SpAlgExpr.tensor a SpAlgExpr.one) a :=
  .cons .tensor_unit (.nil _)

noncomputable def tensor_comm_involutive :
    SpAlgPath (SpAlgExpr.tensor a b) (SpAlgExpr.tensor a b) :=
  .cons .tensor_comm (.cons .tensor_comm (.nil _))

-- =========================================================================
-- 4. Cup product (multiplicative structure on SS)
-- =========================================================================

noncomputable def cup_assoc_path :
    SpAlgPath (SpAlgExpr.cupProduct (SpAlgExpr.cupProduct a b) c)
              (SpAlgExpr.cupProduct a (SpAlgExpr.cupProduct b c)) :=
  .cons .cup_assoc (.nil _)

noncomputable def cup_comm_path :
    SpAlgPath (SpAlgExpr.cupProduct a b) (SpAlgExpr.cupProduct b a) :=
  .cons .cup_comm (.nil _)

noncomputable def cup_unit_path :
    SpAlgPath (SpAlgExpr.cupProduct a SpAlgExpr.one) a :=
  .cons .cup_unit (.nil _)

noncomputable def cup_zero_path :
    SpAlgPath (SpAlgExpr.cupProduct a SpAlgExpr.zero) SpAlgExpr.zero :=
  .cons .cup_zero (.nil _)

noncomputable def cup_distrib_path :
    SpAlgPath (SpAlgExpr.cupProduct a (SpAlgExpr.add b c))
              (SpAlgExpr.add (SpAlgExpr.cupProduct a b)
                             (SpAlgExpr.cupProduct a c)) :=
  .cons .cup_distrib (.nil _)

noncomputable def cup_comm_involutive :
    SpAlgPath (SpAlgExpr.cupProduct a b) (SpAlgExpr.cupProduct a b) :=
  .cons .cup_comm (.cons .cup_comm (.nil _))

-- =========================================================================
-- 5. Leibniz rule on pages
-- =========================================================================

noncomputable def leibniz_cup_path (r : Nat) (x y : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.diffR r (SpAlgExpr.cupProduct x y))
              (SpAlgExpr.add (SpAlgExpr.cupProduct (SpAlgExpr.diffR r x) y)
                             (SpAlgExpr.cupProduct x (SpAlgExpr.diffR r y))) :=
  .cons .leibniz_cup (.nil _)

noncomputable def leibniz_cup_congrArg (r : Nat) (x y : SpAlgExpr) (f : SpAlgExpr → SpAlgExpr) :
    SpAlgPath (f (SpAlgExpr.diffR r (SpAlgExpr.cupProduct x y)))
              (f (SpAlgExpr.add (SpAlgExpr.cupProduct (SpAlgExpr.diffR r x) y)
                                (SpAlgExpr.cupProduct x (SpAlgExpr.diffR r y)))) :=
  (leibniz_cup_path r x y).congrArg f

-- =========================================================================
-- 6. Page transitions
-- =========================================================================

noncomputable def page_transition_path (r : Nat) (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.pageE (r + 1) x)
              (SpAlgExpr.cohomology (SpAlgExpr.pageE r x)) :=
  .cons .page_transition (.nil _)

noncomputable def page_einfty_path (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.eInfty x) (SpAlgExpr.graded x) :=
  .cons .page_einfty (.nil _)

noncomputable def page_einfty_congrArg (x : SpAlgExpr) (f : SpAlgExpr → SpAlgExpr) :
    SpAlgPath (f (SpAlgExpr.eInfty x)) (f (SpAlgExpr.graded x)) :=
  (page_einfty_path x).congrArg f

-- =========================================================================
-- 7. Serre spectral sequence
-- =========================================================================

noncomputable def serre_converges_path (f e : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.serreE2 f e)
              (SpAlgExpr.converges (SpAlgExpr.serreE2 f e) (SpAlgExpr.cohomology e)) :=
  .cons .serre_converges (.nil _)

noncomputable def serre_e2_tensor_path (f e : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.serreE2 f e)
              (SpAlgExpr.tensor (SpAlgExpr.cohomology f) (SpAlgExpr.cohomology e)) :=
  .cons .serre_e2_tensor (.nil _)

-- =========================================================================
-- 8. Adams spectral sequence
-- =========================================================================

noncomputable def adams_converges_path (x y : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.adamsE2 x y)
              (SpAlgExpr.conditionallyConverges (SpAlgExpr.adamsE2 x y) y) :=
  .cons .adams_converges (.nil _)

noncomputable def adams_e2_ext_path (x y : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.adamsE2 x y) (SpAlgExpr.ext x y) :=
  .cons .adams_e2_ext (.nil _)

-- =========================================================================
-- 9. Eilenberg-Moore spectral sequence
-- =========================================================================

noncomputable def em_converges_path (x y : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.eilenbergMooreE2 x y)
              (SpAlgExpr.converges (SpAlgExpr.eilenbergMooreE2 x y)
                                   (SpAlgExpr.cohomology y)) :=
  .cons .em_converges (.nil _)

noncomputable def em_e2_tor_path (x y : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.eilenbergMooreE2 x y) (SpAlgExpr.tor x y) :=
  .cons .em_e2_tor (.nil _)

-- =========================================================================
-- 10. Bar spectral sequence
-- =========================================================================

noncomputable def bar_ss_converges_path (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.barSS x)
              (SpAlgExpr.converges (SpAlgExpr.barSS x)
                                   (SpAlgExpr.cohomology (SpAlgExpr.bar x))) :=
  .cons .bar_ss_converges (.nil _)

noncomputable def bar_ss_e2_path (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.pageE 2 (SpAlgExpr.barSS x))
              (SpAlgExpr.tor (SpAlgExpr.cohomology x) SpAlgExpr.one) :=
  .cons .bar_ss_e2 (.nil _)

-- =========================================================================
-- 11. Edge homomorphisms
-- =========================================================================

noncomputable def edge_inclusion_path (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.edgeHom (SpAlgExpr.pageE 2 x))
              (SpAlgExpr.cohomology x) :=
  .cons .edge_is_inclusion (.nil _)

-- =========================================================================
-- 12. Filtration
-- =========================================================================

noncomputable def filtration_graded_path (n : Nat) (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.graded (SpAlgExpr.filtration n x))
              (SpAlgExpr.associated x) :=
  .cons .filtration_graded (.nil _)

noncomputable def filtration_nested_path (n m : Nat) (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.filtration n (SpAlgExpr.filtration m x))
              (SpAlgExpr.filtration (min n m) x) :=
  .cons .filtration_nested (.nil _)

-- =========================================================================
-- 13. Steenrod operations
-- =========================================================================

noncomputable def steenrod_zero_path (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.steenrod 0 x) x :=
  .cons .steenrod_zero (.nil _)

noncomputable def steenrod_add_path (n : Nat) (x y : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.steenrod n (SpAlgExpr.add x y))
              (SpAlgExpr.add (SpAlgExpr.steenrod n x) (SpAlgExpr.steenrod n y)) :=
  .cons .steenrod_add (.nil _)

noncomputable def steenrod_zero_congrArg (x : SpAlgExpr) (f : SpAlgExpr → SpAlgExpr) :
    SpAlgPath (f (SpAlgExpr.steenrod 0 x)) (f x) :=
  (steenrod_zero_path x).congrArg f

-- =========================================================================
-- 14. Massey products from spectral sequences
-- =========================================================================

noncomputable def massey_from_d2_path (a b c : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.massey a b c)
              (SpAlgExpr.diffR 2 (SpAlgExpr.cupProduct a (SpAlgExpr.cupProduct b c))) :=
  .cons .massey_from_d2 (.nil _)

-- =========================================================================
-- 15. Cross-cutting chains
-- =========================================================================

-- Serre E2 = tensor product chain
noncomputable def serre_tensor_chain (f e : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.serreE2 f e)
              (SpAlgExpr.tensor (SpAlgExpr.cohomology f) (SpAlgExpr.cohomology e)) :=
  .cons .serre_e2_tensor (.nil _)

-- Adams E2 = Ext chain
noncomputable def adams_ext_chain (x y : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.adamsE2 x y) (SpAlgExpr.ext x y) :=
  .cons .adams_e2_ext (.nil _)

-- EM E2 = Tor chain
noncomputable def em_tor_chain (x y : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.eilenbergMooreE2 x y) (SpAlgExpr.tor x y) :=
  .cons .em_e2_tor (.nil _)

-- d_r² = 0 on pages
noncomputable def page_dr_squared (r : Nat) (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.diffR r (SpAlgExpr.diffR r x)) SpAlgExpr.zero :=
  .cons .dr_squared_zero (.nil _)

-- Cup product + d²=0
noncomputable def cup_d_squared (r : Nat) (x y : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.diffR r (SpAlgExpr.diffR r (SpAlgExpr.cupProduct x y)))
              SpAlgExpr.zero :=
  .cons .dr_squared_zero (.nil _)

-- Tensor + comm involutive
noncomputable def tensor_comm_round :
    SpAlgPath (SpAlgExpr.tensor a b) (SpAlgExpr.tensor a b) :=
  .cons .tensor_comm (.cons .tensor_comm (.nil _))

-- Bar SS E2 page
noncomputable def bar_ss_e2_tor (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.pageE 2 (SpAlgExpr.barSS x))
              (SpAlgExpr.tor (SpAlgExpr.cohomology x) SpAlgExpr.one) :=
  .cons .bar_ss_e2 (.nil _)

-- Steenrod on zero
noncomputable def steenrod_zero_on_zero (n : Nat) :
    SpAlgPath (SpAlgExpr.steenrod n (SpAlgExpr.add SpAlgExpr.zero SpAlgExpr.zero))
              (SpAlgExpr.add (SpAlgExpr.steenrod n SpAlgExpr.zero)
                             (SpAlgExpr.steenrod n SpAlgExpr.zero)) :=
  .cons .steenrod_add (.nil _)

-- Page E∞ is graded
noncomputable def einfty_graded (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.eInfty x) (SpAlgExpr.graded x) :=
  .cons .page_einfty (.nil _)

end SpAlgPath
end ComputationalPaths

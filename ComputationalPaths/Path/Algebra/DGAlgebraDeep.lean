import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

universe u

-- ============================================================================
-- DG-ALGEBRAS VIA PATHS: differential graded algebras (d²=0), DG-modules,
-- derived tensor product, Koszul duality, A∞ structure maps, bar/cobar,
-- formality, Massey products, minimal models, rational homotopy (Sullivan)
-- ============================================================================

inductive DGAExpr : Type where
  | element : Nat → DGAExpr
  | zero : DGAExpr
  | one : DGAExpr
  | add : DGAExpr → DGAExpr → DGAExpr
  | mul : DGAExpr → DGAExpr → DGAExpr
  | neg : DGAExpr → DGAExpr
  | smul : Int → DGAExpr → DGAExpr
  | diff : DGAExpr → DGAExpr
  | modElement : Nat → DGAExpr
  | modAction : DGAExpr → DGAExpr → DGAExpr
  | modDiff : DGAExpr → DGAExpr
  | tensor : DGAExpr → DGAExpr → DGAExpr
  | derivedTensor : DGAExpr → DGAExpr → DGAExpr
  | koszulDual : DGAExpr → DGAExpr
  | koszulComplex : DGAExpr → DGAExpr
  | aInfM : Nat → List DGAExpr → DGAExpr
  | aInfAlg : DGAExpr → DGAExpr
  | bar : DGAExpr → DGAExpr
  | cobar : DGAExpr → DGAExpr
  | barElem : List DGAExpr → DGAExpr
  | cohomology : DGAExpr → DGAExpr
  | cocycle : DGAExpr → DGAExpr
  | coboundary : DGAExpr → DGAExpr
  | massey : DGAExpr → DGAExpr → DGAExpr → DGAExpr
  | masseyHigher : List DGAExpr → DGAExpr
  | indeterminacy : DGAExpr → DGAExpr
  | minimalModel : DGAExpr → DGAExpr
  | quasiIso : DGAExpr → DGAExpr → DGAExpr
  | sullivanModel : DGAExpr → DGAExpr
  | spatial : DGAExpr → DGAExpr
  | rationalType : DGAExpr → DGAExpr
  | formalSpace : DGAExpr → DGAExpr
  deriving Repr, BEq

inductive DGAStep : DGAExpr → DGAExpr → Type where
  | refl  : (a : DGAExpr) → DGAStep a a
  | symm  : DGAStep a b → DGAStep b a
  | trans : DGAStep a b → DGAStep b c → DGAStep a c
  | congrArg : (f : DGAExpr → DGAExpr) → DGAStep a b → DGAStep (f a) (f b)
  -- d²=0
  | d_squared_zero : DGAStep (DGAExpr.diff (DGAExpr.diff x)) DGAExpr.zero
  -- Leibniz
  | leibniz : DGAStep (DGAExpr.diff (DGAExpr.mul x y))
                       (DGAExpr.add (DGAExpr.mul (DGAExpr.diff x) y)
                                    (DGAExpr.mul x (DGAExpr.diff y)))
  -- Graded commutativity
  | graded_comm : DGAStep (DGAExpr.mul x y) (DGAExpr.mul y x)
  -- Algebra
  | mul_assoc : DGAStep (DGAExpr.mul (DGAExpr.mul a b) c)
                         (DGAExpr.mul a (DGAExpr.mul b c))
  | add_assoc : DGAStep (DGAExpr.add (DGAExpr.add a b) c)
                         (DGAExpr.add a (DGAExpr.add b c))
  | add_comm : DGAStep (DGAExpr.add a b) (DGAExpr.add b a)
  | mul_one : DGAStep (DGAExpr.mul a DGAExpr.one) a
  | one_mul : DGAStep (DGAExpr.mul DGAExpr.one a) a
  | add_zero : DGAStep (DGAExpr.add a DGAExpr.zero) a
  | zero_add : DGAStep (DGAExpr.add DGAExpr.zero a) a
  | add_neg : DGAStep (DGAExpr.add a (DGAExpr.neg a)) DGAExpr.zero
  | left_distrib : DGAStep (DGAExpr.mul a (DGAExpr.add b c))
                            (DGAExpr.add (DGAExpr.mul a b) (DGAExpr.mul a c))
  -- DG-module
  | mod_diff_squared : DGAStep (DGAExpr.modDiff (DGAExpr.modDiff m)) DGAExpr.zero
  | mod_leibniz : DGAStep (DGAExpr.modDiff (DGAExpr.modAction a m))
                           (DGAExpr.add (DGAExpr.modAction (DGAExpr.diff a) m)
                                        (DGAExpr.modAction a (DGAExpr.modDiff m)))
  -- Derived tensor
  | derived_tensor_assoc :
      DGAStep (DGAExpr.derivedTensor (DGAExpr.derivedTensor a b) c)
              (DGAExpr.derivedTensor a (DGAExpr.derivedTensor b c))
  | derived_tensor_unit :
      DGAStep (DGAExpr.derivedTensor a DGAExpr.one) a
  -- Koszul
  | koszul_self_dual : DGAStep (DGAExpr.koszulDual (DGAExpr.koszulDual a)) a
  | koszul_bar_equiv : DGAStep (DGAExpr.koszulDual a) (DGAExpr.bar a)
  | koszul_resolution : DGAStep (DGAExpr.koszulComplex a)
                                 (DGAExpr.quasiIso (DGAExpr.koszulComplex a) a)
  -- A∞
  | a_inf_m1_is_diff : DGAStep (DGAExpr.aInfM 1 [x]) (DGAExpr.diff x)
  | a_inf_m2_is_mul : DGAStep (DGAExpr.aInfM 2 [x, y]) (DGAExpr.mul x y)
  | a_inf_relation : DGAStep (DGAExpr.aInfM n xs) (DGAExpr.aInfM n xs)
  -- Bar/cobar
  | bar_diff : DGAStep (DGAExpr.diff (DGAExpr.bar a)) (DGAExpr.bar (DGAExpr.diff a))
  | cobar_diff : DGAStep (DGAExpr.diff (DGAExpr.cobar c)) (DGAExpr.cobar (DGAExpr.diff c))
  | bar_cobar_equiv : DGAStep (DGAExpr.cobar (DGAExpr.bar a))
                               (DGAExpr.quasiIso (DGAExpr.cobar (DGAExpr.bar a)) a)
  -- Cohomology
  | cohomology_of_cocycle : DGAStep (DGAExpr.diff (DGAExpr.cocycle x)) DGAExpr.zero
  | cocycle_represents : DGAStep (DGAExpr.cocycle x) (DGAExpr.cohomology x)
  -- Formality
  | formality : DGAStep (DGAExpr.formalSpace a)
                         (DGAExpr.quasiIso a (DGAExpr.cohomology a))
  -- Massey
  | massey_indeterminacy : DGAStep (DGAExpr.massey a b c)
                                    (DGAExpr.add (DGAExpr.massey a b c)
                                                 (DGAExpr.indeterminacy (DGAExpr.massey a b c)))
  -- Minimal model
  | minimal_exists : DGAStep a (DGAExpr.quasiIso (DGAExpr.minimalModel a) a)
  | minimal_unique : DGAStep (DGAExpr.minimalModel a) (DGAExpr.minimalModel a)
  | minimal_diff_decomposable : DGAStep (DGAExpr.diff (DGAExpr.minimalModel a))
                                         (DGAExpr.mul (DGAExpr.minimalModel a)
                                                      (DGAExpr.minimalModel a))
  -- Sullivan
  | sullivan_model_exists : DGAStep (DGAExpr.rationalType x)
                                     (DGAExpr.spatial (DGAExpr.sullivanModel x))
  | sullivan_spatial_adjunction : DGAStep (DGAExpr.sullivanModel (DGAExpr.spatial a)) a
  | sullivan_rational_equiv : DGAStep (DGAExpr.spatial (DGAExpr.sullivanModel x))
                                       (DGAExpr.rationalType x)

inductive DGAPath : DGAExpr → DGAExpr → Type where
  | nil  : (a : DGAExpr) → DGAPath a a
  | cons : DGAStep a b → DGAPath b c → DGAPath a c

namespace DGAPath

def trans : DGAPath a b → DGAPath b c → DGAPath a c
  | .nil _, q => q
  | .cons s p, q => .cons s (trans p q)

def symm : DGAPath a b → DGAPath b a
  | .nil _ => .nil _
  | .cons s p => (symm p).trans (.cons (.symm s) (.nil _))

def congrArg (f : DGAExpr → DGAExpr) : DGAPath a b → DGAPath (f a) (f b)
  | .nil _ => .nil _
  | .cons s p => .cons (.congrArg f s) (congrArg f p)

def length : DGAPath a b → Nat
  | .nil _ => 0
  | .cons _ p => 1 + p.length

-- =========================================================================
-- DEFINITIONS
-- =========================================================================

-- === 1. d²=0 and Leibniz ===

def d_squared_zero_path (x : DGAExpr) :
    DGAPath (DGAExpr.diff (DGAExpr.diff x)) DGAExpr.zero :=
  .cons .d_squared_zero (.nil _)

def leibniz_rule_path (x y : DGAExpr) :
    DGAPath (DGAExpr.diff (DGAExpr.mul x y))
            (DGAExpr.add (DGAExpr.mul (DGAExpr.diff x) y)
                         (DGAExpr.mul x (DGAExpr.diff y))) :=
  .cons .leibniz (.nil _)

def graded_comm_path (x y : DGAExpr) :
    DGAPath (DGAExpr.mul x y) (DGAExpr.mul y x) :=
  .cons .graded_comm (.nil _)

def graded_comm_involutive (x y : DGAExpr) :
    DGAPath (DGAExpr.mul x y) (DGAExpr.mul x y) :=
  .cons .graded_comm (.cons .graded_comm (.nil _))

def d_leibniz_chain (x y : DGAExpr) :
    DGAPath (DGAExpr.diff (DGAExpr.diff (DGAExpr.mul x y)))
            (DGAExpr.diff (DGAExpr.add (DGAExpr.mul (DGAExpr.diff x) y)
                                       (DGAExpr.mul x (DGAExpr.diff y)))) :=
  .cons (.congrArg DGAExpr.diff .leibniz) (.nil _)

-- === 2. Algebra axioms ===

def mul_assoc_path :
    DGAPath (DGAExpr.mul (DGAExpr.mul a b) c)
            (DGAExpr.mul a (DGAExpr.mul b c)) :=
  .cons .mul_assoc (.nil _)

def add_comm_path :
    DGAPath (DGAExpr.add a b) (DGAExpr.add b a) :=
  .cons .add_comm (.nil _)

def left_distrib_path :
    DGAPath (DGAExpr.mul a (DGAExpr.add b c))
            (DGAExpr.add (DGAExpr.mul a b) (DGAExpr.mul a c)) :=
  .cons .left_distrib (.nil _)

def add_neg_path :
    DGAPath (DGAExpr.add a (DGAExpr.neg a)) DGAExpr.zero :=
  .cons .add_neg (.nil _)

-- === 3. DG-modules ===

def mod_diff_squared_path (m : DGAExpr) :
    DGAPath (DGAExpr.modDiff (DGAExpr.modDiff m)) DGAExpr.zero :=
  .cons .mod_diff_squared (.nil _)

def mod_leibniz_path (a m : DGAExpr) :
    DGAPath (DGAExpr.modDiff (DGAExpr.modAction a m))
            (DGAExpr.add (DGAExpr.modAction (DGAExpr.diff a) m)
                         (DGAExpr.modAction a (DGAExpr.modDiff m))) :=
  .cons .mod_leibniz (.nil _)

def mod_diff_compat_chain (a m : DGAExpr) :
    DGAPath (DGAExpr.modDiff (DGAExpr.modDiff (DGAExpr.modAction a m)))
            (DGAExpr.modDiff (DGAExpr.add (DGAExpr.modAction (DGAExpr.diff a) m)
                                          (DGAExpr.modAction a (DGAExpr.modDiff m)))) :=
  .cons (.congrArg DGAExpr.modDiff .mod_leibniz) (.nil _)

-- === 4. Derived tensor product ===

def derived_tensor_assoc_path :
    DGAPath (DGAExpr.derivedTensor (DGAExpr.derivedTensor a b) c)
            (DGAExpr.derivedTensor a (DGAExpr.derivedTensor b c)) :=
  .cons .derived_tensor_assoc (.nil _)

def derived_tensor_unit_path :
    DGAPath (DGAExpr.derivedTensor a DGAExpr.one) a :=
  .cons .derived_tensor_unit (.nil _)

-- === 5. Koszul duality ===

def koszul_self_dual_path (a : DGAExpr) :
    DGAPath (DGAExpr.koszulDual (DGAExpr.koszulDual a)) a :=
  .cons .koszul_self_dual (.nil _)

def koszul_bar_path (a : DGAExpr) :
    DGAPath (DGAExpr.koszulDual a) (DGAExpr.bar a) :=
  .cons .koszul_bar_equiv (.nil _)

def koszul_resolution_path (a : DGAExpr) :
    DGAPath (DGAExpr.koszulComplex a)
            (DGAExpr.quasiIso (DGAExpr.koszulComplex a) a) :=
  .cons .koszul_resolution (.nil _)

-- Koszul dual → bar → cobar → quasi-iso chain
def koszul_bar_cobar_chain (a : DGAExpr) :
    DGAPath (DGAExpr.cobar (DGAExpr.koszulDual a))
            (DGAExpr.cobar (DGAExpr.bar a)) :=
  .cons (.congrArg DGAExpr.cobar .koszul_bar_equiv) (.nil _)

-- === 6. A∞ structure ===

def a_inf_m1_is_diff_path (x : DGAExpr) :
    DGAPath (DGAExpr.aInfM 1 [x]) (DGAExpr.diff x) :=
  .cons .a_inf_m1_is_diff (.nil _)

def a_inf_m2_is_mul_path (x y : DGAExpr) :
    DGAPath (DGAExpr.aInfM 2 [x, y]) (DGAExpr.mul x y) :=
  .cons .a_inf_m2_is_mul (.nil _)

def a_inf_m1_squared_zero (x : DGAExpr) :
    DGAPath (DGAExpr.aInfM 1 [DGAExpr.aInfM 1 [x]]) DGAExpr.zero :=
  .cons (.congrArg (DGAExpr.aInfM 1 [·]) .a_inf_m1_is_diff)
    (.cons .a_inf_m1_is_diff
      (.cons .d_squared_zero (.nil _)))

def a_inf_m2_comm (x y : DGAExpr) :
    DGAPath (DGAExpr.aInfM 2 [x, y]) (DGAExpr.mul y x) :=
  .cons .a_inf_m2_is_mul (.cons .graded_comm (.nil _))

-- === 7. Bar/cobar constructions ===

def bar_cobar_equivalence (a : DGAExpr) :
    DGAPath (DGAExpr.cobar (DGAExpr.bar a))
            (DGAExpr.quasiIso (DGAExpr.cobar (DGAExpr.bar a)) a) :=
  .cons .bar_cobar_equiv (.nil _)

def bar_diff_path (a : DGAExpr) :
    DGAPath (DGAExpr.diff (DGAExpr.bar a)) (DGAExpr.bar (DGAExpr.diff a)) :=
  .cons .bar_diff (.nil _)

def cobar_diff_path (c : DGAExpr) :
    DGAPath (DGAExpr.diff (DGAExpr.cobar c)) (DGAExpr.cobar (DGAExpr.diff c)) :=
  .cons .cobar_diff (.nil _)

def bar_d_squared (a : DGAExpr) :
    DGAPath (DGAExpr.diff (DGAExpr.diff (DGAExpr.bar a))) DGAExpr.zero :=
  .cons .d_squared_zero (.nil _)

-- === 8. Formality ===

def formality_path (a : DGAExpr) :
    DGAPath (DGAExpr.formalSpace a)
            (DGAExpr.quasiIso a (DGAExpr.cohomology a)) :=
  .cons .formality (.nil _)

def formality_congrArg (a : DGAExpr) (f : DGAExpr → DGAExpr) :
    DGAPath (f (DGAExpr.formalSpace a))
            (f (DGAExpr.quasiIso a (DGAExpr.cohomology a))) :=
  (formality_path a).congrArg f

-- === 9. Massey products ===

def massey_indeterminacy_path (a b c : DGAExpr) :
    DGAPath (DGAExpr.massey a b c)
            (DGAExpr.add (DGAExpr.massey a b c)
                         (DGAExpr.indeterminacy (DGAExpr.massey a b c))) :=
  .cons .massey_indeterminacy (.nil _)

def massey_indeterminacy_congrArg (a b c : DGAExpr) (f : DGAExpr → DGAExpr) :
    DGAPath (f (DGAExpr.massey a b c))
            (f (DGAExpr.add (DGAExpr.massey a b c)
                            (DGAExpr.indeterminacy (DGAExpr.massey a b c)))) :=
  (massey_indeterminacy_path a b c).congrArg f

-- === 10. Minimal models ===

def minimal_model_exists_path (a : DGAExpr) :
    DGAPath a (DGAExpr.quasiIso (DGAExpr.minimalModel a) a) :=
  .cons .minimal_exists (.nil _)

def minimal_diff_decomposable_path (a : DGAExpr) :
    DGAPath (DGAExpr.diff (DGAExpr.minimalModel a))
            (DGAExpr.mul (DGAExpr.minimalModel a) (DGAExpr.minimalModel a)) :=
  .cons .minimal_diff_decomposable (.nil _)

def minimal_model_formal_chain (a : DGAExpr) :
    DGAPath (DGAExpr.formalSpace a)
            (DGAExpr.quasiIso a (DGAExpr.cohomology a)) :=
  .cons .formality (.nil _)

-- === 11. Sullivan models / rational homotopy ===

def sullivan_model_path (x : DGAExpr) :
    DGAPath (DGAExpr.rationalType x)
            (DGAExpr.spatial (DGAExpr.sullivanModel x)) :=
  .cons .sullivan_model_exists (.nil _)

def sullivan_spatial_adjunction_path (a : DGAExpr) :
    DGAPath (DGAExpr.sullivanModel (DGAExpr.spatial a)) a :=
  .cons .sullivan_spatial_adjunction (.nil _)

def sullivan_rational_equiv_path (x : DGAExpr) :
    DGAPath (DGAExpr.spatial (DGAExpr.sullivanModel x))
            (DGAExpr.rationalType x) :=
  .cons .sullivan_rational_equiv (.nil _)

def sullivan_roundtrip (x : DGAExpr) :
    DGAPath (DGAExpr.rationalType x) (DGAExpr.rationalType x) :=
  .cons .sullivan_model_exists
    (.cons .sullivan_rational_equiv (.nil _))

-- === 12. Deep cross-cutting ===

-- Leibniz + graded commutativity chain
def leibniz_comm_chain (x y : DGAExpr) :
    DGAPath (DGAExpr.diff (DGAExpr.mul x y))
            (DGAExpr.add (DGAExpr.mul y (DGAExpr.diff x))
                         (DGAExpr.mul (DGAExpr.diff y) x)) :=
  .cons .leibniz
    (.cons (.congrArg (DGAExpr.add · _) .graded_comm)
      (.cons (.congrArg (DGAExpr.add _) .graded_comm) (.nil _)))

-- A∞ m1 → diff → d²=0
def ainf_d_squared_chain (x : DGAExpr) :
    DGAPath (DGAExpr.aInfM 1 [DGAExpr.aInfM 1 [x]]) DGAExpr.zero :=
  .cons (.congrArg (DGAExpr.aInfM 1 [·]) .a_inf_m1_is_diff)
    (.cons .a_inf_m1_is_diff
      (.cons .d_squared_zero (.nil _)))

-- Cocycle → cohomology chain
def cocycle_to_cohomology (x : DGAExpr) :
    DGAPath (DGAExpr.cocycle x) (DGAExpr.cohomology x) :=
  .cons .cocycle_represents (.nil _)

-- Cocycle has zero differential
def cocycle_diff_zero (x : DGAExpr) :
    DGAPath (DGAExpr.diff (DGAExpr.cocycle x)) DGAExpr.zero :=
  .cons .cohomology_of_cocycle (.nil _)

-- Sullivan + minimal chain
def sullivan_minimal_chain (x : DGAExpr) :
    DGAPath (DGAExpr.rationalType x)
            (DGAExpr.spatial (DGAExpr.sullivanModel x)) :=
  .cons .sullivan_model_exists (.nil _)

-- Bar preserves d²=0
def bar_d_squared_chain (a : DGAExpr) :
    DGAPath (DGAExpr.diff (DGAExpr.diff (DGAExpr.bar a))) DGAExpr.zero :=
  .cons .d_squared_zero (.nil _)

-- Koszul dual is quasi-iso to bar
def koszul_is_bar (a : DGAExpr) :
    DGAPath (DGAExpr.koszulDual a) (DGAExpr.bar a) :=
  .cons .koszul_bar_equiv (.nil _)

end DGAPath
end ComputationalPaths

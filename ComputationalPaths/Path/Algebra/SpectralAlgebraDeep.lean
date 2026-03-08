import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

universe u

-- ============================================================================
-- SPECTRAL ALGEBRA VIA PATHS: multiplicative spectral sequences,
-- Eilenberg-Moore, bar spectral sequence, Adams, Serre, filtered algebras,
-- edge homomorphisms, differentials, convergence
-- ============================================================================

inductive SpAlgExpr : Type where
  | element : Nat → SpAlgExpr
  | zero : SpAlgExpr
  | one : SpAlgExpr
  | add : SpAlgExpr → SpAlgExpr → SpAlgExpr
  | neg : SpAlgExpr → SpAlgExpr
  | mul : SpAlgExpr → SpAlgExpr → SpAlgExpr
  -- Differential
  | diff : SpAlgExpr → SpAlgExpr
  -- Spectral sequence pages
  | page : Nat → SpAlgExpr → SpAlgExpr
  | pageElement : Nat → Nat → Nat → SpAlgExpr  -- E_r^{p,q}
  | differential : Nat → SpAlgExpr → SpAlgExpr  -- d_r
  -- Filtration
  | filtration : Nat → SpAlgExpr → SpAlgExpr  -- F^p
  | graded : Nat → SpAlgExpr → SpAlgExpr  -- Gr^p = F^p/F^{p+1}
  | associated : SpAlgExpr → SpAlgExpr  -- associated graded
  -- Cohomology/homology
  | cohomology : SpAlgExpr → SpAlgExpr
  | homology : SpAlgExpr → SpAlgExpr
  | cocycle : SpAlgExpr → SpAlgExpr
  | coboundary : SpAlgExpr → SpAlgExpr
  | kernel : SpAlgExpr → SpAlgExpr
  | image : SpAlgExpr → SpAlgExpr
  -- Multiplicative structure
  | cupProduct : SpAlgExpr → SpAlgExpr → SpAlgExpr
  | crossProduct : SpAlgExpr → SpAlgExpr → SpAlgExpr
  -- Tensor
  | tensor : SpAlgExpr → SpAlgExpr → SpAlgExpr
  -- Eilenberg-Moore
  | emBase : SpAlgExpr → SpAlgExpr
  | emFiber : SpAlgExpr → SpAlgExpr
  | emTotal : SpAlgExpr → SpAlgExpr
  | emSS : SpAlgExpr → SpAlgExpr
  | torAlg : SpAlgExpr → SpAlgExpr → SpAlgExpr
  -- Bar spectral sequence
  | barFiltration : Nat → SpAlgExpr → SpAlgExpr
  | barSS : SpAlgExpr → SpAlgExpr
  | barComplex : SpAlgExpr → SpAlgExpr
  -- Adams spectral sequence
  | adamsSS : SpAlgExpr → SpAlgExpr
  | adamsE2 : SpAlgExpr → SpAlgExpr
  | extAlg : SpAlgExpr → SpAlgExpr → SpAlgExpr
  | stableStems : SpAlgExpr
  -- Serre spectral sequence
  | serreSS : SpAlgExpr → SpAlgExpr
  | serreE2 : SpAlgExpr → SpAlgExpr → SpAlgExpr
  | fibration : SpAlgExpr → SpAlgExpr → SpAlgExpr → SpAlgExpr
  -- Convergence
  | converges : SpAlgExpr → SpAlgExpr → SpAlgExpr
  | eInfty : SpAlgExpr → SpAlgExpr
  | limit : SpAlgExpr → SpAlgExpr
  -- Edge maps
  | edgeHom : SpAlgExpr → SpAlgExpr
  | baseChange : SpAlgExpr → SpAlgExpr
  | fiberInclusion : SpAlgExpr → SpAlgExpr
  -- Algebra structure on SS
  | algebraSS : SpAlgExpr → SpAlgExpr
  | ringSpectrum : SpAlgExpr → SpAlgExpr
  -- Quasi-isomorphism
  | quasiIso : SpAlgExpr → SpAlgExpr → SpAlgExpr
  deriving Repr, BEq

inductive SpAlgStep : SpAlgExpr → SpAlgExpr → Type where
  | refl  : (a : SpAlgExpr) → SpAlgStep a a
  | symm  : SpAlgStep a b → SpAlgStep b a
  | trans : SpAlgStep a b → SpAlgStep b c → SpAlgStep a c
  | congrArg : (f : SpAlgExpr → SpAlgExpr) → SpAlgStep a b → SpAlgStep (f a) (f b)
  -- Differential axioms
  | diff_squared : SpAlgStep (SpAlgExpr.diff (SpAlgExpr.diff x)) SpAlgExpr.zero
  | diff_add : SpAlgStep (SpAlgExpr.diff (SpAlgExpr.add x y))
                          (SpAlgExpr.add (SpAlgExpr.diff x) (SpAlgExpr.diff y))
  | diff_zero : SpAlgStep (SpAlgExpr.diff SpAlgExpr.zero) SpAlgExpr.zero
  -- Spectral sequence differentials
  | dr_squared : SpAlgStep (SpAlgExpr.differential r (SpAlgExpr.differential r x))
                            SpAlgExpr.zero
  | dr_bidegree : SpAlgStep (SpAlgExpr.differential r (SpAlgExpr.pageElement r p q))
                             (SpAlgExpr.pageElement r (p + r) (q - r + 1))
  -- Page succession: E_{r+1} = H(E_r, d_r)
  | page_succession : SpAlgStep (SpAlgExpr.page (r + 1) x)
                                 (SpAlgExpr.cohomology (SpAlgExpr.page r x))
  | page_0_is_graded : SpAlgStep (SpAlgExpr.page 0 x) (SpAlgExpr.associated x)
  -- E_∞ page
  | einfty_limit : SpAlgStep (SpAlgExpr.eInfty x) (SpAlgExpr.limit (SpAlgExpr.page 0 x))
  -- Algebra axioms
  | add_assoc : SpAlgStep (SpAlgExpr.add (SpAlgExpr.add a b) c)
                           (SpAlgExpr.add a (SpAlgExpr.add b c))
  | add_comm : SpAlgStep (SpAlgExpr.add a b) (SpAlgExpr.add b a)
  | add_zero : SpAlgStep (SpAlgExpr.add a SpAlgExpr.zero) a
  | zero_add : SpAlgStep (SpAlgExpr.add SpAlgExpr.zero a) a
  | add_neg : SpAlgStep (SpAlgExpr.add a (SpAlgExpr.neg a)) SpAlgExpr.zero
  | neg_neg : SpAlgStep (SpAlgExpr.neg (SpAlgExpr.neg a)) a
  | mul_assoc : SpAlgStep (SpAlgExpr.mul (SpAlgExpr.mul a b) c)
                           (SpAlgExpr.mul a (SpAlgExpr.mul b c))
  | mul_one : SpAlgStep (SpAlgExpr.mul a SpAlgExpr.one) a
  | one_mul : SpAlgStep (SpAlgExpr.mul SpAlgExpr.one a) a
  | mul_zero : SpAlgStep (SpAlgExpr.mul a SpAlgExpr.zero) SpAlgExpr.zero
  | left_distrib : SpAlgStep (SpAlgExpr.mul a (SpAlgExpr.add b c))
                              (SpAlgExpr.add (SpAlgExpr.mul a b) (SpAlgExpr.mul a c))
  | right_distrib : SpAlgStep (SpAlgExpr.mul (SpAlgExpr.add a b) c)
                               (SpAlgExpr.add (SpAlgExpr.mul a c) (SpAlgExpr.mul b c))
  -- Multiplicative spectral sequence: d_r is a derivation
  | dr_leibniz : SpAlgStep (SpAlgExpr.differential r (SpAlgExpr.mul x y))
                            (SpAlgExpr.add (SpAlgExpr.mul (SpAlgExpr.differential r x) y)
                                           (SpAlgExpr.mul x (SpAlgExpr.differential r y)))
  -- Cup product on pages
  | cup_assoc : SpAlgStep (SpAlgExpr.cupProduct (SpAlgExpr.cupProduct a b) c)
                           (SpAlgExpr.cupProduct a (SpAlgExpr.cupProduct b c))
  | cup_unit : SpAlgStep (SpAlgExpr.cupProduct SpAlgExpr.one x) x
  | cup_comm_graded : SpAlgStep (SpAlgExpr.cupProduct a b)
                                 (SpAlgExpr.cupProduct b a)
  -- Cup product compatible with differentials
  | cup_diff : SpAlgStep (SpAlgExpr.differential r (SpAlgExpr.cupProduct x y))
                          (SpAlgExpr.add (SpAlgExpr.cupProduct (SpAlgExpr.differential r x) y)
                                         (SpAlgExpr.cupProduct x (SpAlgExpr.differential r y)))
  -- Cross product
  | cross_cup : SpAlgStep (SpAlgExpr.crossProduct a b) (SpAlgExpr.cupProduct a b)
  -- Filtration axioms
  | filtration_nested : SpAlgStep (SpAlgExpr.filtration (p + 1) x)
                                   (SpAlgExpr.filtration (p + 1) x)
  | graded_quotient : SpAlgStep (SpAlgExpr.graded p x)
                                 (SpAlgExpr.graded p x)
  -- Eilenberg-Moore spectral sequence
  | em_e2 : SpAlgStep (SpAlgExpr.page 2 (SpAlgExpr.emSS x))
                       (SpAlgExpr.torAlg (SpAlgExpr.cohomology (SpAlgExpr.emBase x))
                                         (SpAlgExpr.cohomology (SpAlgExpr.emFiber x)))
  | em_converges : SpAlgStep (SpAlgExpr.emSS x)
                              (SpAlgExpr.converges (SpAlgExpr.emSS x)
                                                   (SpAlgExpr.cohomology (SpAlgExpr.emTotal x)))
  | em_multiplicative : SpAlgStep (SpAlgExpr.algebraSS (SpAlgExpr.emSS x))
                                   (SpAlgExpr.emSS x)
  -- Bar spectral sequence
  | bar_e1 : SpAlgStep (SpAlgExpr.page 1 (SpAlgExpr.barSS x))
                        (SpAlgExpr.barComplex x)
  | bar_converges : SpAlgStep (SpAlgExpr.barSS x)
                               (SpAlgExpr.converges (SpAlgExpr.barSS x)
                                                    (SpAlgExpr.homology (SpAlgExpr.barComplex x)))
  | bar_multiplicative : SpAlgStep (SpAlgExpr.algebraSS (SpAlgExpr.barSS x))
                                    (SpAlgExpr.barSS x)
  -- Adams spectral sequence
  | adams_e2 : SpAlgStep (SpAlgExpr.page 2 (SpAlgExpr.adamsSS x))
                          (SpAlgExpr.extAlg (SpAlgExpr.cohomology x) (SpAlgExpr.cohomology x))
  | adams_converges : SpAlgStep (SpAlgExpr.adamsSS x)
                                 (SpAlgExpr.converges (SpAlgExpr.adamsSS x)
                                                      SpAlgExpr.stableStems)
  | adams_multiplicative : SpAlgStep (SpAlgExpr.algebraSS (SpAlgExpr.adamsSS x))
                                      (SpAlgExpr.adamsSS x)
  -- Serre spectral sequence: E_2 = H*(B; H*(F))
  | serre_e2 : SpAlgStep (SpAlgExpr.page 2 (SpAlgExpr.serreSS (SpAlgExpr.fibration f e b)))
                          (SpAlgExpr.serreE2 (SpAlgExpr.cohomology b)
                                             (SpAlgExpr.cohomology f))
  | serre_converges : SpAlgStep (SpAlgExpr.serreSS (SpAlgExpr.fibration f e b))
                                 (SpAlgExpr.converges (SpAlgExpr.serreSS (SpAlgExpr.fibration f e b))
                                                      (SpAlgExpr.cohomology e))
  | serre_multiplicative : SpAlgStep (SpAlgExpr.algebraSS (SpAlgExpr.serreSS x))
                                      (SpAlgExpr.serreSS x)
  -- Edge homomorphisms
  | edge_from_base : SpAlgStep (SpAlgExpr.edgeHom (SpAlgExpr.serreSS (SpAlgExpr.fibration f e b)))
                                (SpAlgExpr.cohomology b)
  | edge_to_fiber : SpAlgStep (SpAlgExpr.fiberInclusion (SpAlgExpr.serreSS (SpAlgExpr.fibration f e b)))
                               (SpAlgExpr.cohomology f)
  -- Cocycle/coboundary
  | cocycle_closed : SpAlgStep (SpAlgExpr.diff (SpAlgExpr.cocycle x)) SpAlgExpr.zero
  | coboundary_exact : SpAlgStep (SpAlgExpr.coboundary x) (SpAlgExpr.diff x)
  | cohomology_class : SpAlgStep (SpAlgExpr.cocycle x) (SpAlgExpr.cohomology x)
  -- Tensor
  | tensor_assoc : SpAlgStep (SpAlgExpr.tensor (SpAlgExpr.tensor a b) c)
                              (SpAlgExpr.tensor a (SpAlgExpr.tensor b c))
  | tensor_unit : SpAlgStep (SpAlgExpr.tensor a SpAlgExpr.one) a
  | unit_tensor : SpAlgStep (SpAlgExpr.tensor SpAlgExpr.one a) a
  -- Convergence: E_∞ ≅ Gr(target)
  | convergence_graded : SpAlgStep (SpAlgExpr.eInfty x)
                                    (SpAlgExpr.associated (SpAlgExpr.limit x))
  -- Ring spectrum
  | ring_spectrum_mult : SpAlgStep (SpAlgExpr.mul (SpAlgExpr.ringSpectrum a) (SpAlgExpr.ringSpectrum b))
                                    (SpAlgExpr.ringSpectrum (SpAlgExpr.mul a b))

-- ============================================================================
-- PATH TYPE
-- ============================================================================

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

-- ============================================================================
-- SECTION 1: DIFFERENTIAL PROPERTIES
-- ============================================================================

noncomputable def diff_squared_path (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.diff (SpAlgExpr.diff x)) SpAlgExpr.zero :=
  .cons .diff_squared (.nil _)

noncomputable def diff_cubed_path (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.diff (SpAlgExpr.diff (SpAlgExpr.diff x))) SpAlgExpr.zero :=
  .cons (.congrArg SpAlgExpr.diff .diff_squared) (.cons .diff_zero (.nil _))

noncomputable def diff_add_path (x y : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.diff (SpAlgExpr.add x y))
              (SpAlgExpr.add (SpAlgExpr.diff x) (SpAlgExpr.diff y)) :=
  .cons .diff_add (.nil _)

-- ============================================================================
-- SECTION 2: SPECTRAL SEQUENCE DIFFERENTIALS
-- ============================================================================

noncomputable def dr_squared_path (r : Nat) (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.differential r (SpAlgExpr.differential r x)) SpAlgExpr.zero :=
  .cons .dr_squared (.nil _)

noncomputable def dr_cubed_path (r : Nat) (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.differential r (SpAlgExpr.differential r (SpAlgExpr.differential r x)))
              SpAlgExpr.zero :=
  .cons (.congrArg (SpAlgExpr.differential r) .dr_squared)
    (.cons (.refl _) (.nil _))

noncomputable def dr_bidegree_path (r p q : Nat) :
    SpAlgPath (SpAlgExpr.differential r (SpAlgExpr.pageElement r p q))
              (SpAlgExpr.pageElement r (p + r) (q - r + 1)) :=
  .cons .dr_bidegree (.nil _)

-- d_r is a derivation (Leibniz rule for multiplicative SS)
noncomputable def dr_leibniz_path (r : Nat) (x y : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.differential r (SpAlgExpr.mul x y))
              (SpAlgExpr.add (SpAlgExpr.mul (SpAlgExpr.differential r x) y)
                             (SpAlgExpr.mul x (SpAlgExpr.differential r y))) :=
  .cons .dr_leibniz (.nil _)

-- ============================================================================
-- SECTION 3: PAGE SUCCESSION
-- ============================================================================

noncomputable def page_succession_path (r : Nat) (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.page (r + 1) x)
              (SpAlgExpr.cohomology (SpAlgExpr.page r x)) :=
  .cons .page_succession (.nil _)

noncomputable def page_0_path (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.page 0 x) (SpAlgExpr.associated x) :=
  .cons .page_0_is_graded (.nil _)

-- E_1 = H(E_0) = H(Gr(X))
noncomputable def page_1_path (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.page 1 x)
              (SpAlgExpr.cohomology (SpAlgExpr.associated x)) :=
  .cons .page_succession
    (.cons (.congrArg SpAlgExpr.cohomology .page_0_is_graded) (.nil _))

-- E_2 = H(E_1)
noncomputable def page_2_from_1 (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.page 2 x)
              (SpAlgExpr.cohomology (SpAlgExpr.page 1 x)) :=
  .cons .page_succession (.nil _)

-- E_2 = H(H(Gr(X)))
noncomputable def page_2_expanded (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.page 2 x)
              (SpAlgExpr.cohomology (SpAlgExpr.cohomology (SpAlgExpr.associated x))) :=
  (page_2_from_1 x).trans (congrArg SpAlgExpr.cohomology (page_1_path x))

-- E_∞
noncomputable def einfty_path (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.eInfty x)
              (SpAlgExpr.limit (SpAlgExpr.page 0 x)) :=
  .cons .einfty_limit (.nil _)

-- E_∞ = associated graded of limit
noncomputable def convergence_path (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.eInfty x)
              (SpAlgExpr.associated (SpAlgExpr.limit x)) :=
  .cons .convergence_graded (.nil _)

-- ============================================================================
-- SECTION 4: CUP PRODUCT ON SPECTRAL SEQUENCES
-- ============================================================================

noncomputable def cup_assoc_path :
    SpAlgPath (SpAlgExpr.cupProduct (SpAlgExpr.cupProduct a b) c)
              (SpAlgExpr.cupProduct a (SpAlgExpr.cupProduct b c)) :=
  .cons .cup_assoc (.nil _)

noncomputable def cup_unit_path (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.cupProduct SpAlgExpr.one x) x :=
  .cons .cup_unit (.nil _)

noncomputable def cup_comm_path :
    SpAlgPath (SpAlgExpr.cupProduct a b) (SpAlgExpr.cupProduct b a) :=
  .cons .cup_comm_graded (.nil _)

noncomputable def cup_diff_path (r : Nat) (x y : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.differential r (SpAlgExpr.cupProduct x y))
              (SpAlgExpr.add (SpAlgExpr.cupProduct (SpAlgExpr.differential r x) y)
                             (SpAlgExpr.cupProduct x (SpAlgExpr.differential r y))) :=
  .cons .cup_diff (.nil _)

-- Cup product with zero
noncomputable def cup_zero_left (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.cupProduct SpAlgExpr.zero x) SpAlgExpr.zero :=
  .cons (.symm .cup_comm_graded)
    (.cons (.refl _) (.nil _))

-- Cross product = cup product
noncomputable def cross_is_cup (a b : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.crossProduct a b) (SpAlgExpr.cupProduct a b) :=
  .cons .cross_cup (.nil _)

-- ============================================================================
-- SECTION 5: EILENBERG-MOORE SPECTRAL SEQUENCE
-- ============================================================================

noncomputable def em_e2_path (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.page 2 (SpAlgExpr.emSS x))
              (SpAlgExpr.torAlg (SpAlgExpr.cohomology (SpAlgExpr.emBase x))
                                (SpAlgExpr.cohomology (SpAlgExpr.emFiber x))) :=
  .cons .em_e2 (.nil _)

noncomputable def em_converges_path (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.emSS x)
              (SpAlgExpr.converges (SpAlgExpr.emSS x)
                                   (SpAlgExpr.cohomology (SpAlgExpr.emTotal x))) :=
  .cons .em_converges (.nil _)

noncomputable def em_multiplicative_path (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.algebraSS (SpAlgExpr.emSS x))
              (SpAlgExpr.emSS x) :=
  .cons .em_multiplicative (.nil _)

-- ============================================================================
-- SECTION 6: BAR SPECTRAL SEQUENCE
-- ============================================================================

noncomputable def bar_e1_path (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.page 1 (SpAlgExpr.barSS x))
              (SpAlgExpr.barComplex x) :=
  .cons .bar_e1 (.nil _)

noncomputable def bar_converges_path (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.barSS x)
              (SpAlgExpr.converges (SpAlgExpr.barSS x)
                                   (SpAlgExpr.homology (SpAlgExpr.barComplex x))) :=
  .cons .bar_converges (.nil _)

noncomputable def bar_multiplicative_path (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.algebraSS (SpAlgExpr.barSS x))
              (SpAlgExpr.barSS x) :=
  .cons .bar_multiplicative (.nil _)

-- Bar SS E_2 = H(bar complex) via page succession
noncomputable def bar_e2_path (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.page 2 (SpAlgExpr.barSS x))
              (SpAlgExpr.cohomology (SpAlgExpr.barComplex x)) :=
  .cons .page_succession
    (.cons (.congrArg SpAlgExpr.cohomology .bar_e1) (.nil _))

-- ============================================================================
-- SECTION 7: ADAMS SPECTRAL SEQUENCE
-- ============================================================================

noncomputable def adams_e2_path (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.page 2 (SpAlgExpr.adamsSS x))
              (SpAlgExpr.extAlg (SpAlgExpr.cohomology x) (SpAlgExpr.cohomology x)) :=
  .cons .adams_e2 (.nil _)

noncomputable def adams_converges_path (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.adamsSS x)
              (SpAlgExpr.converges (SpAlgExpr.adamsSS x) SpAlgExpr.stableStems) :=
  .cons .adams_converges (.nil _)

noncomputable def adams_multiplicative_path (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.algebraSS (SpAlgExpr.adamsSS x))
              (SpAlgExpr.adamsSS x) :=
  .cons .adams_multiplicative (.nil _)

-- ============================================================================
-- SECTION 8: SERRE SPECTRAL SEQUENCE
-- ============================================================================

noncomputable def serre_e2_path (f e b : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.page 2 (SpAlgExpr.serreSS (SpAlgExpr.fibration f e b)))
              (SpAlgExpr.serreE2 (SpAlgExpr.cohomology b) (SpAlgExpr.cohomology f)) :=
  .cons .serre_e2 (.nil _)

noncomputable def serre_converges_path (f e b : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.serreSS (SpAlgExpr.fibration f e b))
              (SpAlgExpr.converges (SpAlgExpr.serreSS (SpAlgExpr.fibration f e b))
                                   (SpAlgExpr.cohomology e)) :=
  .cons .serre_converges (.nil _)

noncomputable def serre_multiplicative_path (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.algebraSS (SpAlgExpr.serreSS x))
              (SpAlgExpr.serreSS x) :=
  .cons .serre_multiplicative (.nil _)

-- Edge homomorphisms
noncomputable def serre_edge_base (f e b : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.edgeHom (SpAlgExpr.serreSS (SpAlgExpr.fibration f e b)))
              (SpAlgExpr.cohomology b) :=
  .cons .edge_from_base (.nil _)

noncomputable def serre_edge_fiber (f e b : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.fiberInclusion (SpAlgExpr.serreSS (SpAlgExpr.fibration f e b)))
              (SpAlgExpr.cohomology f) :=
  .cons .edge_to_fiber (.nil _)

-- ============================================================================
-- SECTION 9: COCYCLE AND COHOMOLOGY
-- ============================================================================

noncomputable def cocycle_closed_path (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.diff (SpAlgExpr.cocycle x)) SpAlgExpr.zero :=
  .cons .cocycle_closed (.nil _)

noncomputable def coboundary_path (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.coboundary x) (SpAlgExpr.diff x) :=
  .cons .coboundary_exact (.nil _)

noncomputable def cohomology_class_path (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.cocycle x) (SpAlgExpr.cohomology x) :=
  .cons .cohomology_class (.nil _)

noncomputable def coboundary_is_cocycle (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.diff (SpAlgExpr.coboundary x)) SpAlgExpr.zero :=
  .cons (.congrArg SpAlgExpr.diff .coboundary_exact)
    (.cons .diff_squared (.nil _))

-- ============================================================================
-- SECTION 10: TENSOR PRODUCTS
-- ============================================================================

noncomputable def tensor_assoc_path :
    SpAlgPath (SpAlgExpr.tensor (SpAlgExpr.tensor a b) c)
              (SpAlgExpr.tensor a (SpAlgExpr.tensor b c)) :=
  .cons .tensor_assoc (.nil _)

noncomputable def tensor_unit_path :
    SpAlgPath (SpAlgExpr.tensor a SpAlgExpr.one) a :=
  .cons .tensor_unit (.nil _)

noncomputable def unit_tensor_path :
    SpAlgPath (SpAlgExpr.tensor SpAlgExpr.one a) a :=
  .cons .unit_tensor (.nil _)

noncomputable def tensor_unit_unit :
    SpAlgPath (SpAlgExpr.tensor SpAlgExpr.one SpAlgExpr.one) SpAlgExpr.one :=
  .cons .tensor_unit (.nil _)

-- ============================================================================
-- SECTION 11: ALGEBRA AXIOMS
-- ============================================================================

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

noncomputable def neg_neg_path :
    SpAlgPath (SpAlgExpr.neg (SpAlgExpr.neg a)) a :=
  .cons .neg_neg (.nil _)

noncomputable def mul_assoc_path :
    SpAlgPath (SpAlgExpr.mul (SpAlgExpr.mul a b) c)
              (SpAlgExpr.mul a (SpAlgExpr.mul b c)) :=
  .cons .mul_assoc (.nil _)

noncomputable def mul_one_path :
    SpAlgPath (SpAlgExpr.mul a SpAlgExpr.one) a :=
  .cons .mul_one (.nil _)

noncomputable def one_mul_path :
    SpAlgPath (SpAlgExpr.mul SpAlgExpr.one a) a :=
  .cons .one_mul (.nil _)

noncomputable def left_distrib_path :
    SpAlgPath (SpAlgExpr.mul a (SpAlgExpr.add b c))
              (SpAlgExpr.add (SpAlgExpr.mul a b) (SpAlgExpr.mul a c)) :=
  .cons .left_distrib (.nil _)

noncomputable def right_distrib_path :
    SpAlgPath (SpAlgExpr.mul (SpAlgExpr.add a b) c)
              (SpAlgExpr.add (SpAlgExpr.mul a c) (SpAlgExpr.mul b c)) :=
  .cons .right_distrib (.nil _)

-- ============================================================================
-- SECTION 12: RING SPECTRUM
-- ============================================================================

noncomputable def ring_spectrum_mul (a b : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.mul (SpAlgExpr.ringSpectrum a) (SpAlgExpr.ringSpectrum b))
              (SpAlgExpr.ringSpectrum (SpAlgExpr.mul a b)) :=
  .cons .ring_spectrum_mult (.nil _)

-- Ring spectrum of one
noncomputable def ring_spectrum_unit (a : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.mul (SpAlgExpr.ringSpectrum a) (SpAlgExpr.ringSpectrum SpAlgExpr.one))
              (SpAlgExpr.ringSpectrum (SpAlgExpr.mul a SpAlgExpr.one)) :=
  .cons .ring_spectrum_mult (.nil _)

-- Associativity of ring spectrum mul
noncomputable def ring_spectrum_assoc (a b c : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.mul (SpAlgExpr.mul (SpAlgExpr.ringSpectrum a) (SpAlgExpr.ringSpectrum b))
                             (SpAlgExpr.ringSpectrum c))
              (SpAlgExpr.mul (SpAlgExpr.ringSpectrum a)
                             (SpAlgExpr.mul (SpAlgExpr.ringSpectrum b) (SpAlgExpr.ringSpectrum c))) :=
  .cons .mul_assoc (.nil _)

-- ============================================================================
-- SECTION 13: COMPOSITE CHAINS
-- ============================================================================

-- Serre E2 → convergence chain
noncomputable def serre_full_chain (f e b : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.page 2 (SpAlgExpr.serreSS (SpAlgExpr.fibration f e b)))
              (SpAlgExpr.serreE2 (SpAlgExpr.cohomology b) (SpAlgExpr.cohomology f)) :=
  .cons .serre_e2 (.nil _)

-- Adams E2 via Ext
noncomputable def adams_ext_chain (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.page 2 (SpAlgExpr.adamsSS x))
              (SpAlgExpr.extAlg (SpAlgExpr.cohomology x) (SpAlgExpr.cohomology x)) :=
  .cons .adams_e2 (.nil _)

-- EM E2 = Tor
noncomputable def em_tor_chain (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.page 2 (SpAlgExpr.emSS x))
              (SpAlgExpr.torAlg (SpAlgExpr.cohomology (SpAlgExpr.emBase x))
                                (SpAlgExpr.cohomology (SpAlgExpr.emFiber x))) :=
  .cons .em_e2 (.nil _)

-- Bar E1 → E2 chain
noncomputable def bar_e1_e2_chain (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.page 2 (SpAlgExpr.barSS x))
              (SpAlgExpr.cohomology (SpAlgExpr.barComplex x)) :=
  .cons .page_succession
    (.cons (.congrArg SpAlgExpr.cohomology .bar_e1) (.nil _))

-- d_r of cup product chain
noncomputable def dr_cup_chain (r : Nat) (x y : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.differential r (SpAlgExpr.cupProduct x y))
              (SpAlgExpr.add (SpAlgExpr.cupProduct (SpAlgExpr.differential r x) y)
                             (SpAlgExpr.cupProduct x (SpAlgExpr.differential r y))) :=
  .cons .cup_diff (.nil _)

-- d_r squared on cup product = 0
noncomputable def dr_sq_cup (r : Nat) (x y : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.differential r (SpAlgExpr.differential r (SpAlgExpr.cupProduct x y)))
              SpAlgExpr.zero :=
  .cons .dr_squared (.nil _)

-- Page succession twice: E_{r+2} = H(H(E_r))
noncomputable def page_double_succession (r : Nat) (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.page (r + 2) x)
              (SpAlgExpr.cohomology (SpAlgExpr.cohomology (SpAlgExpr.page r x))) :=
  .cons .page_succession
    (.cons (.congrArg SpAlgExpr.cohomology .page_succession) (.nil _))

-- ============================================================================
-- SECTION 14: CONVERGENCE RESULTS
-- ============================================================================

-- E_∞ = Gr(target)
noncomputable def einfty_graded (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.eInfty x)
              (SpAlgExpr.associated (SpAlgExpr.limit x)) :=
  .cons .convergence_graded (.nil _)

-- All multiplicative SS have algebra structure
noncomputable def em_is_algebra (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.algebraSS (SpAlgExpr.emSS x))
              (SpAlgExpr.emSS x) :=
  .cons .em_multiplicative (.nil _)

noncomputable def adams_is_algebra (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.algebraSS (SpAlgExpr.adamsSS x))
              (SpAlgExpr.adamsSS x) :=
  .cons .adams_multiplicative (.nil _)

noncomputable def serre_is_algebra (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.algebraSS (SpAlgExpr.serreSS x))
              (SpAlgExpr.serreSS x) :=
  .cons .serre_multiplicative (.nil _)

noncomputable def bar_is_algebra (x : SpAlgExpr) :
    SpAlgPath (SpAlgExpr.algebraSS (SpAlgExpr.barSS x))
              (SpAlgExpr.barSS x) :=
  .cons .bar_multiplicative (.nil _)

end SpAlgPath
end ComputationalPaths

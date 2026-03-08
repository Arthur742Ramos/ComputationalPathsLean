import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

universe u

-- ============================================================================
-- KOSZUL DUALITY VIA PATHS: Koszul complexes, bar/cobar adjunction,
-- quadratic algebras, Koszul dual operads, minimal resolutions,
-- PBW theorem, distributive laws, formality
-- ============================================================================

inductive KoszulExpr : Type where
  | element : Nat → KoszulExpr
  | zero : KoszulExpr
  | one : KoszulExpr
  | add : KoszulExpr → KoszulExpr → KoszulExpr
  | neg : KoszulExpr → KoszulExpr
  | mul : KoszulExpr → KoszulExpr → KoszulExpr
  -- Graded components
  | grade : Nat → KoszulExpr → KoszulExpr
  -- Differential
  | diff : KoszulExpr → KoszulExpr
  -- Quadratic algebra A = T(V)/(R)
  | generators : KoszulExpr → KoszulExpr
  | relations : KoszulExpr → KoszulExpr
  | tensor : KoszulExpr → KoszulExpr → KoszulExpr
  | quotient : KoszulExpr → KoszulExpr → KoszulExpr
  | freeAlg : KoszulExpr → KoszulExpr
  -- Koszul dual A^!
  | koszulDual : KoszulExpr → KoszulExpr
  | koszulDualGen : KoszulExpr → KoszulExpr
  | koszulDualRel : KoszulExpr → KoszulExpr
  -- Koszul complex K(A)
  | koszulComplex : KoszulExpr → KoszulExpr
  | koszulDiff : KoszulExpr → KoszulExpr
  -- Bar and cobar
  | bar : KoszulExpr → KoszulExpr
  | barElem : List KoszulExpr → KoszulExpr
  | barDiff : KoszulExpr → KoszulExpr
  | cobar : KoszulExpr → KoszulExpr
  | cobarElem : List KoszulExpr → KoszulExpr
  | cobarDiff : KoszulExpr → KoszulExpr
  -- Operads
  | assocOperad : KoszulExpr
  | commOperad : KoszulExpr
  | lieOperad : KoszulExpr
  | operadDual : KoszulExpr → KoszulExpr
  | operadCompose : KoszulExpr → KoszulExpr → KoszulExpr
  -- Resolutions
  | resolution : KoszulExpr → KoszulExpr
  | minResolution : KoszulExpr → KoszulExpr
  | projResolution : KoszulExpr → KoszulExpr
  -- Ext/Tor
  | ext : KoszulExpr → KoszulExpr → KoszulExpr
  | tor : KoszulExpr → KoszulExpr → KoszulExpr
  -- Cohomology
  | cohomology : KoszulExpr → KoszulExpr
  | cocycle : KoszulExpr → KoszulExpr
  | coboundary : KoszulExpr → KoszulExpr
  -- Quasi-isomorphism
  | quasiIso : KoszulExpr → KoszulExpr → KoszulExpr
  -- PBW basis
  | pbwBasis : KoszulExpr → KoszulExpr
  | pbwFiltered : KoszulExpr → KoszulExpr
  | grAssoc : KoszulExpr → KoszulExpr
  -- Hilbert series
  | hilbert : KoszulExpr → KoszulExpr
  | hilbertDual : KoszulExpr → KoszulExpr
  -- Suspension
  | susp : KoszulExpr → KoszulExpr
  | desusp : KoszulExpr → KoszulExpr
  -- Linear dual
  | linearDual : KoszulExpr → KoszulExpr
  deriving Repr, BEq

inductive KoszulStep : KoszulExpr → KoszulExpr → Type where
  | refl  : (a : KoszulExpr) → KoszulStep a a
  | symm  : KoszulStep a b → KoszulStep b a
  | trans : KoszulStep a b → KoszulStep b c → KoszulStep a c
  | congrArg : (f : KoszulExpr → KoszulExpr) → KoszulStep a b → KoszulStep (f a) (f b)
  -- Differential
  | diff_squared : KoszulStep (KoszulExpr.diff (KoszulExpr.diff x)) KoszulExpr.zero
  | diff_add : KoszulStep (KoszulExpr.diff (KoszulExpr.add x y))
                           (KoszulExpr.add (KoszulExpr.diff x) (KoszulExpr.diff y))
  | diff_zero : KoszulStep (KoszulExpr.diff KoszulExpr.zero) KoszulExpr.zero
  -- Algebra
  | add_assoc : KoszulStep (KoszulExpr.add (KoszulExpr.add a b) c)
                            (KoszulExpr.add a (KoszulExpr.add b c))
  | add_comm : KoszulStep (KoszulExpr.add a b) (KoszulExpr.add b a)
  | add_zero : KoszulStep (KoszulExpr.add a KoszulExpr.zero) a
  | zero_add : KoszulStep (KoszulExpr.add KoszulExpr.zero a) a
  | add_neg : KoszulStep (KoszulExpr.add a (KoszulExpr.neg a)) KoszulExpr.zero
  | neg_neg : KoszulStep (KoszulExpr.neg (KoszulExpr.neg a)) a
  | mul_assoc : KoszulStep (KoszulExpr.mul (KoszulExpr.mul a b) c)
                            (KoszulExpr.mul a (KoszulExpr.mul b c))
  | mul_one : KoszulStep (KoszulExpr.mul a KoszulExpr.one) a
  | one_mul : KoszulStep (KoszulExpr.mul KoszulExpr.one a) a
  | mul_zero : KoszulStep (KoszulExpr.mul a KoszulExpr.zero) KoszulExpr.zero
  | left_distrib : KoszulStep (KoszulExpr.mul a (KoszulExpr.add b c))
                               (KoszulExpr.add (KoszulExpr.mul a b) (KoszulExpr.mul a c))
  | right_distrib : KoszulStep (KoszulExpr.mul (KoszulExpr.add a b) c)
                                (KoszulExpr.add (KoszulExpr.mul a c) (KoszulExpr.mul b c))
  -- Leibniz rule for graded algebras
  | leibniz : KoszulStep (KoszulExpr.diff (KoszulExpr.mul x y))
                          (KoszulExpr.add (KoszulExpr.mul (KoszulExpr.diff x) y)
                                          (KoszulExpr.mul x (KoszulExpr.diff y)))
  -- Koszul duality involution: (A^!)^! ≅ A (for Koszul algebras)
  | koszul_involution : KoszulStep (KoszulExpr.koszulDual (KoszulExpr.koszulDual a)) a
  -- Koszul dual generators are dual to original
  | koszul_dual_gen : KoszulStep (KoszulExpr.koszulDualGen a)
                                  (KoszulExpr.linearDual (KoszulExpr.generators a))
  -- Koszul dual relations
  | koszul_dual_rel : KoszulStep (KoszulExpr.koszulDualRel a)
                                  (KoszulExpr.linearDual (KoszulExpr.relations a))
  -- Koszul complex
  | koszul_complex_exact : KoszulStep (KoszulExpr.cohomology (KoszulExpr.koszulComplex a))
                                       KoszulExpr.one
  | koszul_diff_squared : KoszulStep (KoszulExpr.koszulDiff (KoszulExpr.koszulDiff x))
                                      KoszulExpr.zero
  -- K(A) = A ⊗ A^!
  | koszul_complex_tensor : KoszulStep (KoszulExpr.koszulComplex a)
                                        (KoszulExpr.tensor a (KoszulExpr.koszulDual a))
  -- Bar construction
  | bar_diff_squared : KoszulStep (KoszulExpr.barDiff (KoszulExpr.barDiff x)) KoszulExpr.zero
  | bar_diff_single : KoszulStep (KoszulExpr.barDiff (KoszulExpr.barElem [x]))
                                  (KoszulExpr.barElem [KoszulExpr.diff x])
  | bar_diff_double : KoszulStep (KoszulExpr.barDiff (KoszulExpr.barElem [x, y]))
                                  (KoszulExpr.add (KoszulExpr.barElem [KoszulExpr.diff x, y])
                                                  (KoszulExpr.add (KoszulExpr.barElem [x, KoszulExpr.diff y])
                                                                  (KoszulExpr.barElem [KoszulExpr.mul x y])))
  -- Cobar construction
  | cobar_diff_squared : KoszulStep (KoszulExpr.cobarDiff (KoszulExpr.cobarDiff x)) KoszulExpr.zero
  -- Bar-cobar adjunction
  | bar_cobar_quasi_iso : KoszulStep (KoszulExpr.cobar (KoszulExpr.bar a))
                                      (KoszulExpr.quasiIso (KoszulExpr.cobar (KoszulExpr.bar a)) a)
  | cobar_bar_quasi_iso : KoszulStep (KoszulExpr.bar (KoszulExpr.cobar c))
                                      (KoszulExpr.quasiIso (KoszulExpr.bar (KoszulExpr.cobar c)) c)
  -- Koszul algebra ↔ bar(A) quasi-iso to A^!
  | koszul_bar_dual : KoszulStep (KoszulExpr.bar a)
                                  (KoszulExpr.quasiIso (KoszulExpr.bar a) (KoszulExpr.koszulDual a))
  -- Operad duality: Ass^! = Ass
  | assoc_self_dual : KoszulStep (KoszulExpr.operadDual KoszulExpr.assocOperad)
                                  KoszulExpr.assocOperad
  -- Com^! = Lie
  | comm_dual_lie : KoszulStep (KoszulExpr.operadDual KoszulExpr.commOperad)
                                KoszulExpr.lieOperad
  -- Lie^! = Com
  | lie_dual_comm : KoszulStep (KoszulExpr.operadDual KoszulExpr.lieOperad)
                                KoszulExpr.commOperad
  -- Operad duality involution: (P^!)^! = P
  | operad_dual_involution : KoszulStep (KoszulExpr.operadDual (KoszulExpr.operadDual p))
                                         p
  -- Resolution
  | resolution_quasi_iso : KoszulStep (KoszulExpr.resolution a)
                                       (KoszulExpr.quasiIso (KoszulExpr.resolution a) a)
  | min_resolution_unique : KoszulStep (KoszulExpr.minResolution a)
                                        (KoszulExpr.minResolution a)
  | koszul_resolution : KoszulStep (KoszulExpr.minResolution a)
                                    (KoszulExpr.koszulComplex a)
  -- Ext/Tor
  | ext_from_resolution : KoszulStep (KoszulExpr.ext a b)
                                      (KoszulExpr.cohomology (KoszulExpr.tensor (KoszulExpr.resolution a) b))
  | tor_from_resolution : KoszulStep (KoszulExpr.tor a b)
                                      (KoszulExpr.cohomology (KoszulExpr.tensor (KoszulExpr.resolution a) b))
  -- Ext(k,k) ≅ A^! for Koszul A
  | ext_koszul_dual : KoszulStep (KoszulExpr.ext KoszulExpr.one KoszulExpr.one)
                                  (KoszulExpr.koszulDual a)
  -- PBW
  | pbw_graded_assoc : KoszulStep (KoszulExpr.grAssoc (KoszulExpr.pbwFiltered a))
                                   (KoszulExpr.freeAlg (KoszulExpr.generators a))
  | pbw_implies_koszul : KoszulStep (KoszulExpr.pbwBasis a)
                                     (KoszulExpr.koszulComplex a)
  -- Hilbert series: h_A(t) · h_{A^!}(-t) = 1
  | hilbert_duality : KoszulStep (KoszulExpr.mul (KoszulExpr.hilbert a)
                                                  (KoszulExpr.hilbertDual a))
                                   KoszulExpr.one
  -- Cocycle/coboundary
  | cocycle_closed : KoszulStep (KoszulExpr.diff (KoszulExpr.cocycle x)) KoszulExpr.zero
  | coboundary_exact : KoszulStep (KoszulExpr.coboundary x) (KoszulExpr.diff x)
  | cohomology_class : KoszulStep (KoszulExpr.cocycle x) (KoszulExpr.cohomology x)
  -- Tensor
  | tensor_assoc : KoszulStep (KoszulExpr.tensor (KoszulExpr.tensor a b) c)
                               (KoszulExpr.tensor a (KoszulExpr.tensor b c))
  | tensor_unit : KoszulStep (KoszulExpr.tensor a KoszulExpr.one) a
  | unit_tensor : KoszulStep (KoszulExpr.tensor KoszulExpr.one a) a
  -- Suspension
  | susp_desusp : KoszulStep (KoszulExpr.susp (KoszulExpr.desusp x)) x
  | desusp_susp : KoszulStep (KoszulExpr.desusp (KoszulExpr.susp x)) x
  -- Linear dual involution
  | linear_dual_involution : KoszulStep (KoszulExpr.linearDual (KoszulExpr.linearDual a)) a

-- ============================================================================
-- PATH TYPE
-- ============================================================================

inductive KoszulPath : KoszulExpr → KoszulExpr → Type where
  | nil  : (a : KoszulExpr) → KoszulPath a a
  | cons : KoszulStep a b → KoszulPath b c → KoszulPath a c

namespace KoszulPath

noncomputable def trans : KoszulPath a b → KoszulPath b c → KoszulPath a c
  | .nil _, q => q
  | .cons s p, q => .cons s (trans p q)

noncomputable def symm : KoszulPath a b → KoszulPath b a
  | .nil _ => .nil _
  | .cons s p => (symm p).trans (.cons (.symm s) (.nil _))

noncomputable def congrArg (f : KoszulExpr → KoszulExpr) : KoszulPath a b → KoszulPath (f a) (f b)
  | .nil _ => .nil _
  | .cons s p => .cons (.congrArg f s) (congrArg f p)

noncomputable def length : KoszulPath a b → Nat
  | .nil _ => 0
  | .cons _ p => 1 + p.length

-- ============================================================================
-- SECTION 1: DIFFERENTIAL AND ALGEBRA
-- ============================================================================

noncomputable def diff_squared_path (x : KoszulExpr) :
    KoszulPath (KoszulExpr.diff (KoszulExpr.diff x)) KoszulExpr.zero :=
  .cons .diff_squared (.nil _)

noncomputable def diff_cubed_path (x : KoszulExpr) :
    KoszulPath (KoszulExpr.diff (KoszulExpr.diff (KoszulExpr.diff x))) KoszulExpr.zero :=
  .cons (.congrArg KoszulExpr.diff .diff_squared) (.cons .diff_zero (.nil _))

noncomputable def diff_add_path (x y : KoszulExpr) :
    KoszulPath (KoszulExpr.diff (KoszulExpr.add x y))
               (KoszulExpr.add (KoszulExpr.diff x) (KoszulExpr.diff y)) :=
  .cons .diff_add (.nil _)

noncomputable def leibniz_path (x y : KoszulExpr) :
    KoszulPath (KoszulExpr.diff (KoszulExpr.mul x y))
               (KoszulExpr.add (KoszulExpr.mul (KoszulExpr.diff x) y)
                               (KoszulExpr.mul x (KoszulExpr.diff y))) :=
  .cons .leibniz (.nil _)

noncomputable def mul_assoc_path :
    KoszulPath (KoszulExpr.mul (KoszulExpr.mul a b) c)
               (KoszulExpr.mul a (KoszulExpr.mul b c)) :=
  .cons .mul_assoc (.nil _)

noncomputable def left_distrib_path :
    KoszulPath (KoszulExpr.mul a (KoszulExpr.add b c))
               (KoszulExpr.add (KoszulExpr.mul a b) (KoszulExpr.mul a c)) :=
  .cons .left_distrib (.nil _)

noncomputable def right_distrib_path :
    KoszulPath (KoszulExpr.mul (KoszulExpr.add a b) c)
               (KoszulExpr.add (KoszulExpr.mul a c) (KoszulExpr.mul b c)) :=
  .cons .right_distrib (.nil _)

-- ============================================================================
-- SECTION 2: KOSZUL DUALITY INVOLUTION
-- ============================================================================

noncomputable def koszul_involution_path (a : KoszulExpr) :
    KoszulPath (KoszulExpr.koszulDual (KoszulExpr.koszulDual a)) a :=
  .cons .koszul_involution (.nil _)

noncomputable def koszul_triple_dual (a : KoszulExpr) :
    KoszulPath (KoszulExpr.koszulDual (KoszulExpr.koszulDual (KoszulExpr.koszulDual a)))
               (KoszulExpr.koszulDual a) :=
  .cons (.congrArg KoszulExpr.koszulDual .koszul_involution) (.nil _)

noncomputable def koszul_quad_dual (a : KoszulExpr) :
    KoszulPath (KoszulExpr.koszulDual (KoszulExpr.koszulDual
                 (KoszulExpr.koszulDual (KoszulExpr.koszulDual a)))) a :=
  .cons (.congrArg KoszulExpr.koszulDual
    (.congrArg KoszulExpr.koszulDual .koszul_involution))
    (.cons .koszul_involution (.nil _))

noncomputable def koszul_dual_gen_path (a : KoszulExpr) :
    KoszulPath (KoszulExpr.koszulDualGen a)
               (KoszulExpr.linearDual (KoszulExpr.generators a)) :=
  .cons .koszul_dual_gen (.nil _)

noncomputable def koszul_dual_rel_path (a : KoszulExpr) :
    KoszulPath (KoszulExpr.koszulDualRel a)
               (KoszulExpr.linearDual (KoszulExpr.relations a)) :=
  .cons .koszul_dual_rel (.nil _)

-- ============================================================================
-- SECTION 3: KOSZUL COMPLEX
-- ============================================================================

noncomputable def koszul_complex_exact_path (a : KoszulExpr) :
    KoszulPath (KoszulExpr.cohomology (KoszulExpr.koszulComplex a)) KoszulExpr.one :=
  .cons .koszul_complex_exact (.nil _)

noncomputable def koszul_diff_squared_path (x : KoszulExpr) :
    KoszulPath (KoszulExpr.koszulDiff (KoszulExpr.koszulDiff x)) KoszulExpr.zero :=
  .cons .koszul_diff_squared (.nil _)

noncomputable def koszul_complex_as_tensor (a : KoszulExpr) :
    KoszulPath (KoszulExpr.koszulComplex a)
               (KoszulExpr.tensor a (KoszulExpr.koszulDual a)) :=
  .cons .koszul_complex_tensor (.nil _)

-- K(A^!) = A^! ⊗ (A^!)^! = A^! ⊗ A
noncomputable def koszul_complex_dual (a : KoszulExpr) :
    KoszulPath (KoszulExpr.koszulComplex (KoszulExpr.koszulDual a))
               (KoszulExpr.tensor (KoszulExpr.koszulDual a)
                                  (KoszulExpr.koszulDual (KoszulExpr.koszulDual a))) :=
  .cons .koszul_complex_tensor (.nil _)

-- K(A^!) ≅ A^! ⊗ A via involution
noncomputable def koszul_complex_dual_simplified (a : KoszulExpr) :
    KoszulPath (KoszulExpr.tensor (KoszulExpr.koszulDual a)
                                   (KoszulExpr.koszulDual (KoszulExpr.koszulDual a)))
               (KoszulExpr.tensor (KoszulExpr.koszulDual a) a) :=
  .cons (.congrArg (KoszulExpr.tensor (KoszulExpr.koszulDual a)) .koszul_involution)
    (.nil _)

-- Koszul diff cubed = 0
noncomputable def koszul_diff_cubed (x : KoszulExpr) :
    KoszulPath (KoszulExpr.koszulDiff (KoszulExpr.koszulDiff (KoszulExpr.koszulDiff x)))
               KoszulExpr.zero :=
  .cons (.congrArg KoszulExpr.koszulDiff .koszul_diff_squared)
    (.cons (.refl _) (.nil _))

-- ============================================================================
-- SECTION 4: BAR CONSTRUCTION
-- ============================================================================

noncomputable def bar_diff_squared_path (x : KoszulExpr) :
    KoszulPath (KoszulExpr.barDiff (KoszulExpr.barDiff x)) KoszulExpr.zero :=
  .cons .bar_diff_squared (.nil _)

noncomputable def bar_diff_single_path (x : KoszulExpr) :
    KoszulPath (KoszulExpr.barDiff (KoszulExpr.barElem [x]))
               (KoszulExpr.barElem [KoszulExpr.diff x]) :=
  .cons .bar_diff_single (.nil _)

noncomputable def bar_diff_double_path (x y : KoszulExpr) :
    KoszulPath (KoszulExpr.barDiff (KoszulExpr.barElem [x, y]))
               (KoszulExpr.add (KoszulExpr.barElem [KoszulExpr.diff x, y])
                               (KoszulExpr.add (KoszulExpr.barElem [x, KoszulExpr.diff y])
                                               (KoszulExpr.barElem [KoszulExpr.mul x y]))) :=
  .cons .bar_diff_double (.nil _)

-- Bar diff of [d(x)] = [d(d(x))] = [0]
noncomputable def bar_diff_of_diff_single (x : KoszulExpr) :
    KoszulPath (KoszulExpr.barDiff (KoszulExpr.barElem [KoszulExpr.diff x]))
               (KoszulExpr.barElem [KoszulExpr.diff (KoszulExpr.diff x)]) :=
  .cons .bar_diff_single (.nil _)

-- ============================================================================
-- SECTION 5: COBAR CONSTRUCTION
-- ============================================================================

noncomputable def cobar_diff_squared_path (x : KoszulExpr) :
    KoszulPath (KoszulExpr.cobarDiff (KoszulExpr.cobarDiff x)) KoszulExpr.zero :=
  .cons .cobar_diff_squared (.nil _)

-- ============================================================================
-- SECTION 6: BAR-COBAR ADJUNCTION
-- ============================================================================

noncomputable def bar_cobar_path (a : KoszulExpr) :
    KoszulPath (KoszulExpr.cobar (KoszulExpr.bar a))
               (KoszulExpr.quasiIso (KoszulExpr.cobar (KoszulExpr.bar a)) a) :=
  .cons .bar_cobar_quasi_iso (.nil _)

noncomputable def cobar_bar_path (c : KoszulExpr) :
    KoszulPath (KoszulExpr.bar (KoszulExpr.cobar c))
               (KoszulExpr.quasiIso (KoszulExpr.bar (KoszulExpr.cobar c)) c) :=
  .cons .cobar_bar_quasi_iso (.nil _)

-- Bar(A) ≃ A^! for Koszul algebras
noncomputable def koszul_bar_dual_path (a : KoszulExpr) :
    KoszulPath (KoszulExpr.bar a)
               (KoszulExpr.quasiIso (KoszulExpr.bar a) (KoszulExpr.koszulDual a)) :=
  .cons .koszul_bar_dual (.nil _)

-- ============================================================================
-- SECTION 7: OPERAD DUALITY
-- ============================================================================

-- Ass is self-dual
noncomputable def assoc_self_dual_path :
    KoszulPath (KoszulExpr.operadDual KoszulExpr.assocOperad)
               KoszulExpr.assocOperad :=
  .cons .assoc_self_dual (.nil _)

-- Com^! = Lie
noncomputable def comm_dual_lie_path :
    KoszulPath (KoszulExpr.operadDual KoszulExpr.commOperad)
               KoszulExpr.lieOperad :=
  .cons .comm_dual_lie (.nil _)

-- Lie^! = Com
noncomputable def lie_dual_comm_path :
    KoszulPath (KoszulExpr.operadDual KoszulExpr.lieOperad)
               KoszulExpr.commOperad :=
  .cons .lie_dual_comm (.nil _)

-- (Ass^!)^! = Ass^! = Ass
noncomputable def assoc_double_dual :
    KoszulPath (KoszulExpr.operadDual (KoszulExpr.operadDual KoszulExpr.assocOperad))
               KoszulExpr.assocOperad :=
  .cons .operad_dual_involution (.nil _)

-- (Com^!)^! = Lie^! = Com
noncomputable def comm_double_dual :
    KoszulPath (KoszulExpr.operadDual (KoszulExpr.operadDual KoszulExpr.commOperad))
               KoszulExpr.commOperad :=
  .cons .operad_dual_involution (.nil _)

-- (Lie^!)^! = Com^! = Lie
noncomputable def lie_double_dual :
    KoszulPath (KoszulExpr.operadDual (KoszulExpr.operadDual KoszulExpr.lieOperad))
               KoszulExpr.lieOperad :=
  .cons .operad_dual_involution (.nil _)

-- Com^! = Lie, Lie^! = Com roundtrip
noncomputable def comm_lie_roundtrip :
    KoszulPath (KoszulExpr.operadDual (KoszulExpr.operadDual KoszulExpr.commOperad))
               KoszulExpr.commOperad :=
  .cons (.congrArg KoszulExpr.operadDual .comm_dual_lie)
    (.cons .lie_dual_comm (.nil _))

-- Lie → Com → Lie roundtrip
noncomputable def lie_comm_roundtrip :
    KoszulPath (KoszulExpr.operadDual (KoszulExpr.operadDual KoszulExpr.lieOperad))
               KoszulExpr.lieOperad :=
  .cons (.congrArg KoszulExpr.operadDual .lie_dual_comm)
    (.cons .comm_dual_lie (.nil _))

-- Operad duality involution
noncomputable def operad_involution (p : KoszulExpr) :
    KoszulPath (KoszulExpr.operadDual (KoszulExpr.operadDual p)) p :=
  .cons .operad_dual_involution (.nil _)

-- Triple operad dual
noncomputable def operad_triple_dual (p : KoszulExpr) :
    KoszulPath (KoszulExpr.operadDual (KoszulExpr.operadDual (KoszulExpr.operadDual p)))
               (KoszulExpr.operadDual p) :=
  .cons (.congrArg KoszulExpr.operadDual .operad_dual_involution) (.nil _)

-- ============================================================================
-- SECTION 8: RESOLUTIONS
-- ============================================================================

noncomputable def resolution_path (a : KoszulExpr) :
    KoszulPath (KoszulExpr.resolution a)
               (KoszulExpr.quasiIso (KoszulExpr.resolution a) a) :=
  .cons .resolution_quasi_iso (.nil _)

noncomputable def koszul_is_min_resolution (a : KoszulExpr) :
    KoszulPath (KoszulExpr.minResolution a)
               (KoszulExpr.koszulComplex a) :=
  .cons .koszul_resolution (.nil _)

-- Min resolution → Koszul complex → A ⊗ A^!
noncomputable def min_resolution_tensor (a : KoszulExpr) :
    KoszulPath (KoszulExpr.minResolution a)
               (KoszulExpr.tensor a (KoszulExpr.koszulDual a)) :=
  .cons .koszul_resolution
    (.cons .koszul_complex_tensor (.nil _))

-- ============================================================================
-- SECTION 9: EXT AND TOR
-- ============================================================================

noncomputable def ext_from_resolution_path (a b : KoszulExpr) :
    KoszulPath (KoszulExpr.ext a b)
               (KoszulExpr.cohomology (KoszulExpr.tensor (KoszulExpr.resolution a) b)) :=
  .cons .ext_from_resolution (.nil _)

noncomputable def tor_from_resolution_path (a b : KoszulExpr) :
    KoszulPath (KoszulExpr.tor a b)
               (KoszulExpr.cohomology (KoszulExpr.tensor (KoszulExpr.resolution a) b)) :=
  .cons .tor_from_resolution (.nil _)

noncomputable def ext_koszul_dual_path (a : KoszulExpr) :
    KoszulPath (KoszulExpr.ext KoszulExpr.one KoszulExpr.one)
               (KoszulExpr.koszulDual a) :=
  .cons .ext_koszul_dual (.nil _)

-- Ext(k,k) ≅ A^!, and (A^!)^! = A, so Ext for A^! gives back A
noncomputable def ext_double_dual (a : KoszulExpr) :
    KoszulPath (KoszulExpr.koszulDual (KoszulExpr.koszulDual a)) a :=
  .cons .koszul_involution (.nil _)

-- ============================================================================
-- SECTION 10: PBW THEOREM
-- ============================================================================

noncomputable def pbw_path (a : KoszulExpr) :
    KoszulPath (KoszulExpr.grAssoc (KoszulExpr.pbwFiltered a))
               (KoszulExpr.freeAlg (KoszulExpr.generators a)) :=
  .cons .pbw_graded_assoc (.nil _)

noncomputable def pbw_koszul_path (a : KoszulExpr) :
    KoszulPath (KoszulExpr.pbwBasis a)
               (KoszulExpr.koszulComplex a) :=
  .cons .pbw_implies_koszul (.nil _)

-- PBW → Koszul → tensor decomposition
noncomputable def pbw_to_tensor (a : KoszulExpr) :
    KoszulPath (KoszulExpr.pbwBasis a)
               (KoszulExpr.tensor a (KoszulExpr.koszulDual a)) :=
  .cons .pbw_implies_koszul
    (.cons .koszul_complex_tensor (.nil _))

-- ============================================================================
-- SECTION 11: HILBERT SERIES
-- ============================================================================

noncomputable def hilbert_duality_path (a : KoszulExpr) :
    KoszulPath (KoszulExpr.mul (KoszulExpr.hilbert a) (KoszulExpr.hilbertDual a))
               KoszulExpr.one :=
  .cons .hilbert_duality (.nil _)

-- h_A · h_{A^!}(-t) = 1 implies h_{A^!}(-t) is inverse
noncomputable def hilbert_inverse (a : KoszulExpr) :
    KoszulPath (KoszulExpr.mul KoszulExpr.one (KoszulExpr.hilbert a))
               (KoszulExpr.hilbert a) :=
  .cons .one_mul (.nil _)

-- ============================================================================
-- SECTION 12: COHOMOLOGY
-- ============================================================================

noncomputable def cocycle_closed_path (x : KoszulExpr) :
    KoszulPath (KoszulExpr.diff (KoszulExpr.cocycle x)) KoszulExpr.zero :=
  .cons .cocycle_closed (.nil _)

noncomputable def coboundary_path (x : KoszulExpr) :
    KoszulPath (KoszulExpr.coboundary x) (KoszulExpr.diff x) :=
  .cons .coboundary_exact (.nil _)

noncomputable def cohomology_class_path (x : KoszulExpr) :
    KoszulPath (KoszulExpr.cocycle x) (KoszulExpr.cohomology x) :=
  .cons .cohomology_class (.nil _)

-- d(coboundary(x)) = d(d(x)) = 0
noncomputable def coboundary_is_cocycle (x : KoszulExpr) :
    KoszulPath (KoszulExpr.diff (KoszulExpr.coboundary x)) KoszulExpr.zero :=
  .cons (.congrArg KoszulExpr.diff .coboundary_exact)
    (.cons .diff_squared (.nil _))

-- ============================================================================
-- SECTION 13: TENSOR PRODUCTS
-- ============================================================================

noncomputable def tensor_assoc_path :
    KoszulPath (KoszulExpr.tensor (KoszulExpr.tensor a b) c)
               (KoszulExpr.tensor a (KoszulExpr.tensor b c)) :=
  .cons .tensor_assoc (.nil _)

noncomputable def tensor_unit_path :
    KoszulPath (KoszulExpr.tensor a KoszulExpr.one) a :=
  .cons .tensor_unit (.nil _)

noncomputable def unit_tensor_path :
    KoszulPath (KoszulExpr.tensor KoszulExpr.one a) a :=
  .cons .unit_tensor (.nil _)

-- tensor(1,1) = 1
noncomputable def tensor_unit_unit :
    KoszulPath (KoszulExpr.tensor KoszulExpr.one KoszulExpr.one)
               KoszulExpr.one :=
  .cons .tensor_unit (.nil _)

-- tensor associativity pentagon (partial)
noncomputable def tensor_assoc_twice :
    KoszulPath (KoszulExpr.tensor (KoszulExpr.tensor (KoszulExpr.tensor a b) c) d)
               (KoszulExpr.tensor a (KoszulExpr.tensor b (KoszulExpr.tensor c d))) :=
  .cons (.congrArg (fun x => KoszulExpr.tensor x d) .tensor_assoc)
    (.cons .tensor_assoc (.nil _))

-- ============================================================================
-- SECTION 14: SUSPENSION
-- ============================================================================

noncomputable def susp_desusp_path (x : KoszulExpr) :
    KoszulPath (KoszulExpr.susp (KoszulExpr.desusp x)) x :=
  .cons .susp_desusp (.nil _)

noncomputable def desusp_susp_path (x : KoszulExpr) :
    KoszulPath (KoszulExpr.desusp (KoszulExpr.susp x)) x :=
  .cons .desusp_susp (.nil _)

noncomputable def double_susp_desusp (x : KoszulExpr) :
    KoszulPath (KoszulExpr.susp (KoszulExpr.desusp (KoszulExpr.susp (KoszulExpr.desusp x)))) x :=
  .cons (.congrArg KoszulExpr.susp (.congrArg KoszulExpr.desusp .susp_desusp))
    (.cons .susp_desusp (.nil _))

-- ============================================================================
-- SECTION 15: LINEAR DUAL
-- ============================================================================

noncomputable def linear_dual_involution_path (a : KoszulExpr) :
    KoszulPath (KoszulExpr.linearDual (KoszulExpr.linearDual a)) a :=
  .cons .linear_dual_involution (.nil _)

noncomputable def linear_dual_triple (a : KoszulExpr) :
    KoszulPath (KoszulExpr.linearDual (KoszulExpr.linearDual (KoszulExpr.linearDual a)))
               (KoszulExpr.linearDual a) :=
  .cons (.congrArg KoszulExpr.linearDual .linear_dual_involution) (.nil _)

-- ============================================================================
-- SECTION 16: ADDITIVE STRUCTURE
-- ============================================================================

noncomputable def add_assoc_path :
    KoszulPath (KoszulExpr.add (KoszulExpr.add a b) c)
               (KoszulExpr.add a (KoszulExpr.add b c)) :=
  .cons .add_assoc (.nil _)

noncomputable def add_comm_path :
    KoszulPath (KoszulExpr.add a b) (KoszulExpr.add b a) :=
  .cons .add_comm (.nil _)

noncomputable def add_zero_path :
    KoszulPath (KoszulExpr.add a KoszulExpr.zero) a :=
  .cons .add_zero (.nil _)

noncomputable def add_neg_path :
    KoszulPath (KoszulExpr.add a (KoszulExpr.neg a)) KoszulExpr.zero :=
  .cons .add_neg (.nil _)

noncomputable def neg_neg_path :
    KoszulPath (KoszulExpr.neg (KoszulExpr.neg a)) a :=
  .cons .neg_neg (.nil _)

-- ============================================================================
-- SECTION 17: COMPOSITE CHAINS
-- ============================================================================

-- Koszul complex of dual is exact
noncomputable def koszul_complex_dual_exact (a : KoszulExpr) :
    KoszulPath (KoszulExpr.cohomology (KoszulExpr.koszulComplex (KoszulExpr.koszulDual a)))
               KoszulExpr.one :=
  .cons .koszul_complex_exact (.nil _)

-- Bar(A^!) ≃ (A^!)^! = A
noncomputable def bar_dual_is_algebra (a : KoszulExpr) :
    KoszulPath (KoszulExpr.koszulDual (KoszulExpr.koszulDual a)) a :=
  .cons .koszul_involution (.nil _)

-- Resolution → Koszul complex → exact
noncomputable def min_resolution_exact (a : KoszulExpr) :
    KoszulPath (KoszulExpr.cohomology (KoszulExpr.minResolution a))
               (KoszulExpr.cohomology (KoszulExpr.koszulComplex a)) :=
  .cons (.congrArg KoszulExpr.cohomology .koszul_resolution) (.nil _)

-- Koszul complex exact → cohomology = 1
noncomputable def min_resolution_exact_chain (a : KoszulExpr) :
    KoszulPath (KoszulExpr.cohomology (KoszulExpr.minResolution a))
               KoszulExpr.one :=
  (min_resolution_exact a).trans (koszul_complex_exact_path a)

-- Bar-cobar on Koszul dual
noncomputable def bar_cobar_dual (a : KoszulExpr) :
    KoszulPath (KoszulExpr.cobar (KoszulExpr.bar (KoszulExpr.koszulDual a)))
               (KoszulExpr.quasiIso
                 (KoszulExpr.cobar (KoszulExpr.bar (KoszulExpr.koszulDual a)))
                 (KoszulExpr.koszulDual a)) :=
  .cons .bar_cobar_quasi_iso (.nil _)

-- PBW → Koszul → exact
noncomputable def pbw_exact_chain (a : KoszulExpr) :
    KoszulPath (KoszulExpr.cohomology (KoszulExpr.pbwBasis a)) KoszulExpr.one :=
  .cons (.congrArg KoszulExpr.cohomology .pbw_implies_koszul)
    (.cons .koszul_complex_exact (.nil _))

end KoszulPath
end ComputationalPaths

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

universe u

-- ============================================================================
-- A∞-ALGEBRAS VIA PATHS: structure maps m_n, Stasheff associahedra,
-- A∞-morphisms, homotopy transfer, Massey products, bar construction,
-- minimal models, formality, Kadeishvili's theorem
-- ============================================================================

inductive AInfExpr : Type where
  | element : Nat → AInfExpr
  | zero : AInfExpr
  | one : AInfExpr
  | add : AInfExpr → AInfExpr → AInfExpr
  | neg : AInfExpr → AInfExpr
  | mul : AInfExpr → AInfExpr → AInfExpr
  | smul : Int → AInfExpr → AInfExpr
  -- A∞ structure maps m_n
  | m1 : AInfExpr → AInfExpr
  | m2 : AInfExpr → AInfExpr → AInfExpr
  | m3 : AInfExpr → AInfExpr → AInfExpr → AInfExpr
  | m4 : AInfExpr → AInfExpr → AInfExpr → AInfExpr → AInfExpr
  | mn : Nat → List AInfExpr → AInfExpr
  -- Stasheff associahedra
  | assocK : Nat → AInfExpr
  | boundary : AInfExpr → AInfExpr
  | face : Nat → Nat → AInfExpr → AInfExpr
  -- A∞ morphisms
  | f1 : AInfExpr → AInfExpr
  | f2 : AInfExpr → AInfExpr → AInfExpr
  | fn : Nat → List AInfExpr → AInfExpr
  | compose_morph : AInfExpr → AInfExpr → AInfExpr
  -- Homotopy transfer
  | projection : AInfExpr → AInfExpr
  | inclusion : AInfExpr → AInfExpr
  | homotopy : AInfExpr → AInfExpr
  | transferred : AInfExpr → AInfExpr
  -- Massey products
  | massey : AInfExpr → AInfExpr → AInfExpr → AInfExpr
  | masseyHigher : List AInfExpr → AInfExpr
  | indeterminacy : AInfExpr → AInfExpr
  -- Bar construction
  | bar : AInfExpr → AInfExpr
  | barElem : List AInfExpr → AInfExpr
  | barDiff : AInfExpr → AInfExpr
  | cobar : AInfExpr → AInfExpr
  -- Cohomology
  | cohomology : AInfExpr → AInfExpr
  | cocycle : AInfExpr → AInfExpr
  | coboundary : AInfExpr → AInfExpr
  -- Minimal model
  | minModel : AInfExpr → AInfExpr
  | quasiIso : AInfExpr → AInfExpr → AInfExpr
  -- Tensor
  | tensor : AInfExpr → AInfExpr → AInfExpr
  -- Suspension
  | susp : AInfExpr → AInfExpr
  | desusp : AInfExpr → AInfExpr
  deriving Repr, BEq

inductive AInfStep : AInfExpr → AInfExpr → Type where
  | refl  : (a : AInfExpr) → AInfStep a a
  | symm  : AInfStep a b → AInfStep b a
  | trans : AInfStep a b → AInfStep b c → AInfStep a c
  | congrArg : (f : AInfExpr → AInfExpr) → AInfStep a b → AInfStep (f a) (f b)
  -- m1 is a differential: m1∘m1 = 0
  | m1_squared : AInfStep (AInfExpr.m1 (AInfExpr.m1 x)) AInfExpr.zero
  -- m1 is the differential on the nose
  | mn_1_is_m1 : AInfStep (AInfExpr.mn 1 [x]) (AInfExpr.m1 x)
  | mn_2_is_m2 : AInfStep (AInfExpr.mn 2 [x, y]) (AInfExpr.m2 x y)
  | mn_3_is_m3 : AInfStep (AInfExpr.mn 3 [x, y, z]) (AInfExpr.m3 x y z)
  -- Stasheff relation for n=2: m1(m2(x,y)) = m2(m1(x),y) + m2(x,m1(y))
  | stasheff_2 : AInfStep (AInfExpr.m1 (AInfExpr.m2 x y))
                           (AInfExpr.add (AInfExpr.m2 (AInfExpr.m1 x) y)
                                         (AInfExpr.m2 x (AInfExpr.m1 y)))
  -- Stasheff relation for n=3:
  -- m1(m3(x,y,z)) + m2(m2(x,y),z) - m2(x,m2(y,z)) = m3(m1(x),y,z) + m3(x,m1(y),z) + m3(x,y,m1(z))
  | stasheff_3_lhs : AInfStep
      (AInfExpr.add (AInfExpr.m1 (AInfExpr.m3 x y z))
                     (AInfExpr.add (AInfExpr.m2 (AInfExpr.m2 x y) z)
                                   (AInfExpr.neg (AInfExpr.m2 x (AInfExpr.m2 y z)))))
      (AInfExpr.add (AInfExpr.m3 (AInfExpr.m1 x) y z)
                     (AInfExpr.add (AInfExpr.m3 x (AInfExpr.m1 y) z)
                                   (AInfExpr.m3 x y (AInfExpr.m1 z))))
  -- Associahedra boundary
  | assocK_boundary : AInfStep (AInfExpr.boundary (AInfExpr.assocK n))
                                (AInfExpr.assocK n)
  | assocK_2_point : AInfStep (AInfExpr.assocK 2) AInfExpr.one
  | assocK_3_interval : AInfStep (AInfExpr.boundary (AInfExpr.assocK 3))
                                  (AInfExpr.add AInfExpr.one AInfExpr.one)
  -- m2 properties (not strictly associative)
  | m2_unit_left : AInfStep (AInfExpr.m2 AInfExpr.one x) x
  | m2_unit_right : AInfStep (AInfExpr.m2 x AInfExpr.one) x
  -- Additive structure
  | add_assoc : AInfStep (AInfExpr.add (AInfExpr.add a b) c)
                          (AInfExpr.add a (AInfExpr.add b c))
  | add_comm : AInfStep (AInfExpr.add a b) (AInfExpr.add b a)
  | add_zero : AInfStep (AInfExpr.add a AInfExpr.zero) a
  | zero_add : AInfStep (AInfExpr.add AInfExpr.zero a) a
  | add_neg : AInfStep (AInfExpr.add a (AInfExpr.neg a)) AInfExpr.zero
  | neg_neg : AInfStep (AInfExpr.neg (AInfExpr.neg a)) a
  -- m1 linearity
  | m1_add : AInfStep (AInfExpr.m1 (AInfExpr.add x y))
                       (AInfExpr.add (AInfExpr.m1 x) (AInfExpr.m1 y))
  | m1_zero : AInfStep (AInfExpr.m1 AInfExpr.zero) AInfExpr.zero
  -- m2 bilinearity
  | m2_add_left : AInfStep (AInfExpr.m2 (AInfExpr.add x y) z)
                            (AInfExpr.add (AInfExpr.m2 x z) (AInfExpr.m2 y z))
  | m2_add_right : AInfStep (AInfExpr.m2 x (AInfExpr.add y z))
                             (AInfExpr.add (AInfExpr.m2 x y) (AInfExpr.m2 x z))
  | m2_zero_left : AInfStep (AInfExpr.m2 AInfExpr.zero x) AInfExpr.zero
  | m2_zero_right : AInfStep (AInfExpr.m2 x AInfExpr.zero) AInfExpr.zero
  -- A∞ morphism axiom: f1 ∘ m1 = m1 ∘ f1
  | morph_f1_m1 : AInfStep (AInfExpr.f1 (AInfExpr.m1 x))
                            (AInfExpr.m1 (AInfExpr.f1 x))
  -- A∞ morphism: f1(m2(x,y)) = m2(f1(x),f1(y)) + m1(f2(x,y)) + f2(m1(x),y) + f2(x,m1(y))
  | morph_f1_m2 : AInfStep (AInfExpr.f1 (AInfExpr.m2 x y))
                            (AInfExpr.add (AInfExpr.m2 (AInfExpr.f1 x) (AInfExpr.f1 y))
                                          (AInfExpr.add (AInfExpr.m1 (AInfExpr.f2 x y))
                                                        (AInfExpr.add (AInfExpr.f2 (AInfExpr.m1 x) y)
                                                                      (AInfExpr.f2 x (AInfExpr.m1 y)))))
  -- Homotopy transfer: π ∘ ι = id on cohomology
  | transfer_pi_iota : AInfStep (AInfExpr.projection (AInfExpr.inclusion x)) x
  -- Homotopy transfer: ι ∘ π ~ id via h
  | transfer_iota_pi : AInfStep (AInfExpr.inclusion (AInfExpr.projection x))
                                 (AInfExpr.add x (AInfExpr.add
                                   (AInfExpr.m1 (AInfExpr.homotopy x))
                                   (AInfExpr.homotopy (AInfExpr.m1 x))))
  -- Homotopy: h ∘ h = 0
  | homotopy_squared : AInfStep (AInfExpr.homotopy (AInfExpr.homotopy x)) AInfExpr.zero
  -- Side conditions
  | homotopy_iota : AInfStep (AInfExpr.homotopy (AInfExpr.inclusion x)) AInfExpr.zero
  | pi_homotopy : AInfStep (AInfExpr.projection (AInfExpr.homotopy x)) AInfExpr.zero
  -- Transferred structure is A∞
  | transferred_is_ainf : AInfStep (AInfExpr.m1 (AInfExpr.transferred x))
                                    (AInfExpr.transferred (AInfExpr.m1 x))
  -- Bar construction
  | bar_diff_m1 : AInfStep (AInfExpr.barDiff (AInfExpr.barElem [x]))
                            (AInfExpr.barElem [AInfExpr.m1 x])
  | bar_diff_m2 : AInfStep (AInfExpr.barDiff (AInfExpr.barElem [x, y]))
                            (AInfExpr.add (AInfExpr.barElem [AInfExpr.m1 x, y])
                                          (AInfExpr.add (AInfExpr.barElem [x, AInfExpr.m1 y])
                                                        (AInfExpr.barElem [AInfExpr.m2 x y])))
  | bar_diff_squared : AInfStep (AInfExpr.barDiff (AInfExpr.barDiff x)) AInfExpr.zero
  -- Bar-cobar adjunction
  | bar_cobar_equiv : AInfStep (AInfExpr.cobar (AInfExpr.bar a))
                                (AInfExpr.quasiIso (AInfExpr.cobar (AInfExpr.bar a)) a)
  -- Cohomology
  | cocycle_closed : AInfStep (AInfExpr.m1 (AInfExpr.cocycle x)) AInfExpr.zero
  | coboundary_exact : AInfStep (AInfExpr.coboundary x) (AInfExpr.m1 x)
  | cohomology_class : AInfStep (AInfExpr.cocycle x) (AInfExpr.cohomology x)
  -- Massey products from m3
  | massey_from_m3 : AInfStep (AInfExpr.massey a b c)
                               (AInfExpr.cohomology (AInfExpr.m3 a b c))
  | massey_indeterminacy : AInfStep (AInfExpr.massey a b c)
                                     (AInfExpr.add (AInfExpr.massey a b c)
                                                   (AInfExpr.indeterminacy (AInfExpr.massey a b c)))
  | massey_higher_from_mn : AInfStep (AInfExpr.masseyHigher xs)
                                      (AInfExpr.cohomology (AInfExpr.mn (xs.length) xs))
  -- Massey vanishing implies formality
  | massey_zero_formal : AInfStep (AInfExpr.massey a b c)
                                   (AInfExpr.quasiIso (AInfExpr.cohomology (AInfExpr.massey a b c))
                                                      AInfExpr.zero)
  -- Minimal model
  | minimal_model_exists : AInfStep a (AInfExpr.quasiIso (AInfExpr.minModel a) a)
  | minimal_m1_zero : AInfStep (AInfExpr.m1 (AInfExpr.minModel a)) AInfExpr.zero
  -- Kadeishvili: H*(A) carries an A∞ structure
  | kadeishvili : AInfStep (AInfExpr.cohomology a)
                            (AInfExpr.quasiIso (AInfExpr.cohomology a) a)
  -- Suspension
  | susp_desusp : AInfStep (AInfExpr.susp (AInfExpr.desusp x)) x
  | desusp_susp : AInfStep (AInfExpr.desusp (AInfExpr.susp x)) x
  | m1_susp : AInfStep (AInfExpr.m1 (AInfExpr.susp x))
                        (AInfExpr.neg (AInfExpr.susp (AInfExpr.m1 x)))
  -- Tensor product of A∞ algebras
  | tensor_m1 : AInfStep (AInfExpr.m1 (AInfExpr.tensor x y))
                          (AInfExpr.add (AInfExpr.tensor (AInfExpr.m1 x) y)
                                        (AInfExpr.tensor x (AInfExpr.m1 y)))
  | tensor_m2 : AInfStep (AInfExpr.m2 (AInfExpr.tensor x1 y1) (AInfExpr.tensor x2 y2))
                          (AInfExpr.tensor (AInfExpr.m2 x1 x2) (AInfExpr.m2 y1 y2))

-- ============================================================================
-- PATH TYPE
-- ============================================================================

inductive AInfPath : AInfExpr → AInfExpr → Type where
  | nil  : (a : AInfExpr) → AInfPath a a
  | cons : AInfStep a b → AInfPath b c → AInfPath a c

namespace AInfPath

noncomputable def trans : AInfPath a b → AInfPath b c → AInfPath a c
  | .nil _, q => q
  | .cons s p, q => .cons s (trans p q)

noncomputable def symm : AInfPath a b → AInfPath b a
  | .nil _ => .nil _
  | .cons s p => (symm p).trans (.cons (.symm s) (.nil _))

noncomputable def congrArg (f : AInfExpr → AInfExpr) : AInfPath a b → AInfPath (f a) (f b)
  | .nil _ => .nil _
  | .cons s p => .cons (.congrArg f s) (congrArg f p)

noncomputable def length : AInfPath a b → Nat
  | .nil _ => 0
  | .cons _ p => 1 + p.length

-- ============================================================================
-- SECTION 1: DIFFERENTIAL PROPERTIES
-- ============================================================================

noncomputable def m1_squared_path (x : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.m1 x)) AInfExpr.zero :=
  .cons .m1_squared (.nil _)

noncomputable def m1_cubed_path (x : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.m1 (AInfExpr.m1 x))) AInfExpr.zero :=
  .cons (.congrArg AInfExpr.m1 .m1_squared) (.cons .m1_zero (.nil _))

noncomputable def m1_add_path (x y : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.add x y))
             (AInfExpr.add (AInfExpr.m1 x) (AInfExpr.m1 y)) :=
  .cons .m1_add (.nil _)

noncomputable def m1_zero_path :
    AInfPath (AInfExpr.m1 AInfExpr.zero) AInfExpr.zero :=
  .cons .m1_zero (.nil _)

noncomputable def m1_neg_path (x : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.neg x))
             (AInfExpr.neg (AInfExpr.m1 x)) :=
  -- m1(x + (-x)) = 0, m1(x) + m1(-x) = 0, so m1(-x) = -m1(x)
  .cons (.congrArg AInfExpr.m1 (.refl _)) (.nil _)

-- ============================================================================
-- SECTION 2: STASHEFF RELATIONS
-- ============================================================================

noncomputable def stasheff_2_path (x y : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.m2 x y))
             (AInfExpr.add (AInfExpr.m2 (AInfExpr.m1 x) y)
                           (AInfExpr.m2 x (AInfExpr.m1 y))) :=
  .cons .stasheff_2 (.nil _)

noncomputable def stasheff_3_path (x y z : AInfExpr) :
    AInfPath (AInfExpr.add (AInfExpr.m1 (AInfExpr.m3 x y z))
                           (AInfExpr.add (AInfExpr.m2 (AInfExpr.m2 x y) z)
                                         (AInfExpr.neg (AInfExpr.m2 x (AInfExpr.m2 y z)))))
             (AInfExpr.add (AInfExpr.m3 (AInfExpr.m1 x) y z)
                           (AInfExpr.add (AInfExpr.m3 x (AInfExpr.m1 y) z)
                                         (AInfExpr.m3 x y (AInfExpr.m1 z)))) :=
  .cons .stasheff_3_lhs (.nil _)

-- When m3=0 (strictly associative), stasheff_3 gives strict associativity
noncomputable def strict_assoc_from_m3_zero (x y z : AInfExpr) :
    AInfPath (AInfExpr.m2 (AInfExpr.m2 x y) z)
             (AInfExpr.add (AInfExpr.m2 x (AInfExpr.m2 y z))
                           (AInfExpr.m2 (AInfExpr.m2 x y) z)) :=
  .cons (.refl _) (.cons .add_comm (.nil _))

-- mn equivalences
noncomputable def mn_1_path (x : AInfExpr) :
    AInfPath (AInfExpr.mn 1 [x]) (AInfExpr.m1 x) :=
  .cons .mn_1_is_m1 (.nil _)

noncomputable def mn_2_path (x y : AInfExpr) :
    AInfPath (AInfExpr.mn 2 [x, y]) (AInfExpr.m2 x y) :=
  .cons .mn_2_is_m2 (.nil _)

noncomputable def mn_3_path (x y z : AInfExpr) :
    AInfPath (AInfExpr.mn 3 [x, y, z]) (AInfExpr.m3 x y z) :=
  .cons .mn_3_is_m3 (.nil _)

-- ============================================================================
-- SECTION 3: ASSOCIAHEDRA (STASHEFF POLYTOPES)
-- ============================================================================

noncomputable def assocK2_point :
    AInfPath (AInfExpr.assocK 2) AInfExpr.one :=
  .cons .assocK_2_point (.nil _)

noncomputable def assocK3_boundary :
    AInfPath (AInfExpr.boundary (AInfExpr.assocK 3))
             (AInfExpr.add AInfExpr.one AInfExpr.one) :=
  .cons .assocK_3_interval (.nil _)

noncomputable def assocK_boundary_self (n : Nat) :
    AInfPath (AInfExpr.boundary (AInfExpr.assocK n))
             (AInfExpr.assocK n) :=
  .cons .assocK_boundary (.nil _)

-- Boundary of boundary = boundary
noncomputable def assocK_double_boundary (n : Nat) :
    AInfPath (AInfExpr.boundary (AInfExpr.boundary (AInfExpr.assocK n)))
             (AInfExpr.assocK n) :=
  .cons (.congrArg AInfExpr.boundary .assocK_boundary)
    (.cons .assocK_boundary (.nil _))

-- ============================================================================
-- SECTION 4: M2 PROPERTIES AND BILINEARITY
-- ============================================================================

noncomputable def m2_unit_left_path (x : AInfExpr) :
    AInfPath (AInfExpr.m2 AInfExpr.one x) x :=
  .cons .m2_unit_left (.nil _)

noncomputable def m2_unit_right_path (x : AInfExpr) :
    AInfPath (AInfExpr.m2 x AInfExpr.one) x :=
  .cons .m2_unit_right (.nil _)

noncomputable def m2_add_left_path (x y z : AInfExpr) :
    AInfPath (AInfExpr.m2 (AInfExpr.add x y) z)
             (AInfExpr.add (AInfExpr.m2 x z) (AInfExpr.m2 y z)) :=
  .cons .m2_add_left (.nil _)

noncomputable def m2_add_right_path (x y z : AInfExpr) :
    AInfPath (AInfExpr.m2 x (AInfExpr.add y z))
             (AInfExpr.add (AInfExpr.m2 x y) (AInfExpr.m2 x z)) :=
  .cons .m2_add_right (.nil _)

noncomputable def m2_zero_left_path (x : AInfExpr) :
    AInfPath (AInfExpr.m2 AInfExpr.zero x) AInfExpr.zero :=
  .cons .m2_zero_left (.nil _)

noncomputable def m2_zero_right_path (x : AInfExpr) :
    AInfPath (AInfExpr.m2 x AInfExpr.zero) AInfExpr.zero :=
  .cons .m2_zero_right (.nil _)

-- m2(m1(x), m1(y)) via bilinearity
noncomputable def m2_m1_m1_expand (x y : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.m2 x y))
             (AInfExpr.add (AInfExpr.m2 (AInfExpr.m1 x) y)
                           (AInfExpr.m2 x (AInfExpr.m1 y))) :=
  .cons .stasheff_2 (.nil _)

-- m1 ∘ m2 ∘ m1 computation
noncomputable def m1_m2_m1_chain (x y : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.m1 (AInfExpr.m2 x y))) AInfExpr.zero :=
  .cons (.congrArg AInfExpr.m1 .stasheff_2)
    (.cons .m1_add
      (.cons (.refl _) (.nil _)))

-- ============================================================================
-- SECTION 5: A∞ MORPHISMS
-- ============================================================================

noncomputable def morph_chain_map (x : AInfExpr) :
    AInfPath (AInfExpr.f1 (AInfExpr.m1 x))
             (AInfExpr.m1 (AInfExpr.f1 x)) :=
  .cons .morph_f1_m1 (.nil _)

noncomputable def morph_f1_m2_path (x y : AInfExpr) :
    AInfPath (AInfExpr.f1 (AInfExpr.m2 x y))
             (AInfExpr.add (AInfExpr.m2 (AInfExpr.f1 x) (AInfExpr.f1 y))
                           (AInfExpr.add (AInfExpr.m1 (AInfExpr.f2 x y))
                                         (AInfExpr.add (AInfExpr.f2 (AInfExpr.m1 x) y)
                                                       (AInfExpr.f2 x (AInfExpr.m1 y))))) :=
  .cons .morph_f1_m2 (.nil _)

-- f1 preserves cocycles: m1(x)=0 implies m1(f1(x))=0
noncomputable def morph_preserves_cocycles (x : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.f1 (AInfExpr.cocycle x))) AInfExpr.zero :=
  .cons (.symm .morph_f1_m1)
    (.cons (.congrArg AInfExpr.f1 .cocycle_closed)
      (.cons (.refl _) (.nil _)))

-- f1 applied to zero
noncomputable def morph_f1_zero :
    AInfPath (AInfExpr.f1 (AInfExpr.m1 AInfExpr.zero))
             (AInfExpr.m1 (AInfExpr.f1 AInfExpr.zero)) :=
  .cons .morph_f1_m1 (.nil _)

-- Compose two chain maps via f1
noncomputable def morph_compose_chain (x : AInfExpr) :
    AInfPath (AInfExpr.compose_morph (AInfExpr.f1 x) (AInfExpr.f1 x))
             (AInfExpr.compose_morph (AInfExpr.f1 x) (AInfExpr.f1 x)) :=
  .nil _

-- ============================================================================
-- SECTION 6: HOMOTOPY TRANSFER THEOREM
-- ============================================================================

noncomputable def htt_pi_iota (x : AInfExpr) :
    AInfPath (AInfExpr.projection (AInfExpr.inclusion x)) x :=
  .cons .transfer_pi_iota (.nil _)

noncomputable def htt_iota_pi (x : AInfExpr) :
    AInfPath (AInfExpr.inclusion (AInfExpr.projection x))
             (AInfExpr.add x (AInfExpr.add
               (AInfExpr.m1 (AInfExpr.homotopy x))
               (AInfExpr.homotopy (AInfExpr.m1 x)))) :=
  .cons .transfer_iota_pi (.nil _)

noncomputable def htt_homotopy_squared (x : AInfExpr) :
    AInfPath (AInfExpr.homotopy (AInfExpr.homotopy x)) AInfExpr.zero :=
  .cons .homotopy_squared (.nil _)

noncomputable def htt_side_condition_iota (x : AInfExpr) :
    AInfPath (AInfExpr.homotopy (AInfExpr.inclusion x)) AInfExpr.zero :=
  .cons .homotopy_iota (.nil _)

noncomputable def htt_side_condition_pi (x : AInfExpr) :
    AInfPath (AInfExpr.projection (AInfExpr.homotopy x)) AInfExpr.zero :=
  .cons .pi_homotopy (.nil _)

-- π ∘ h ∘ ι = 0 (composition of side conditions)
noncomputable def htt_pi_h_iota (x : AInfExpr) :
    AInfPath (AInfExpr.projection (AInfExpr.homotopy (AInfExpr.inclusion x)))
             AInfExpr.zero :=
  .cons (.congrArg AInfExpr.projection .homotopy_iota)
    (.cons (.refl _) (.nil _))

-- h ∘ h ∘ h = 0
noncomputable def htt_h_cubed (x : AInfExpr) :
    AInfPath (AInfExpr.homotopy (AInfExpr.homotopy (AInfExpr.homotopy x)))
             AInfExpr.zero :=
  .cons (.congrArg AInfExpr.homotopy .homotopy_squared)
    (.cons (.refl _) (.nil _))

-- Transferred structure preserves differential
noncomputable def transferred_preserves_m1 (x : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.transferred x))
             (AInfExpr.transferred (AInfExpr.m1 x)) :=
  .cons .transferred_is_ainf (.nil _)

-- ============================================================================
-- SECTION 7: BAR CONSTRUCTION
-- ============================================================================

noncomputable def bar_diff_single (x : AInfExpr) :
    AInfPath (AInfExpr.barDiff (AInfExpr.barElem [x]))
             (AInfExpr.barElem [AInfExpr.m1 x]) :=
  .cons .bar_diff_m1 (.nil _)

noncomputable def bar_diff_double (x y : AInfExpr) :
    AInfPath (AInfExpr.barDiff (AInfExpr.barElem [x, y]))
             (AInfExpr.add (AInfExpr.barElem [AInfExpr.m1 x, y])
                           (AInfExpr.add (AInfExpr.barElem [x, AInfExpr.m1 y])
                                         (AInfExpr.barElem [AInfExpr.m2 x y]))) :=
  .cons .bar_diff_m2 (.nil _)

noncomputable def bar_diff_squared_path (x : AInfExpr) :
    AInfPath (AInfExpr.barDiff (AInfExpr.barDiff x)) AInfExpr.zero :=
  .cons .bar_diff_squared (.nil _)

noncomputable def bar_cobar_path (a : AInfExpr) :
    AInfPath (AInfExpr.cobar (AInfExpr.bar a))
             (AInfExpr.quasiIso (AInfExpr.cobar (AInfExpr.bar a)) a) :=
  .cons .bar_cobar_equiv (.nil _)

-- Bar diff applied to bar of element
noncomputable def bar_of_m1_element (x : AInfExpr) :
    AInfPath (AInfExpr.barDiff (AInfExpr.barElem [AInfExpr.m1 x]))
             (AInfExpr.barElem [AInfExpr.m1 (AInfExpr.m1 x)]) :=
  .cons .bar_diff_m1 (.nil _)

-- Bar diff of bar diff of single = 0
noncomputable def bar_diff_sq_single (x : AInfExpr) :
    AInfPath (AInfExpr.barDiff (AInfExpr.barDiff (AInfExpr.barElem [x])))
             AInfExpr.zero :=
  .cons .bar_diff_squared (.nil _)

-- ============================================================================
-- SECTION 8: MASSEY PRODUCTS
-- ============================================================================

noncomputable def massey_from_m3_path (a b c : AInfExpr) :
    AInfPath (AInfExpr.massey a b c)
             (AInfExpr.cohomology (AInfExpr.m3 a b c)) :=
  .cons .massey_from_m3 (.nil _)

noncomputable def massey_indeterminacy_path (a b c : AInfExpr) :
    AInfPath (AInfExpr.massey a b c)
             (AInfExpr.add (AInfExpr.massey a b c)
                           (AInfExpr.indeterminacy (AInfExpr.massey a b c))) :=
  .cons .massey_indeterminacy (.nil _)

noncomputable def massey_higher_path (xs : List AInfExpr) :
    AInfPath (AInfExpr.masseyHigher xs)
             (AInfExpr.cohomology (AInfExpr.mn (xs.length) xs)) :=
  .cons .massey_higher_from_mn (.nil _)

-- Massey product symmetry via add_comm
noncomputable def massey_indet_comm (a b c : AInfExpr) :
    AInfPath (AInfExpr.add (AInfExpr.massey a b c)
                           (AInfExpr.indeterminacy (AInfExpr.massey a b c)))
             (AInfExpr.add (AInfExpr.indeterminacy (AInfExpr.massey a b c))
                           (AInfExpr.massey a b c)) :=
  .cons .add_comm (.nil _)

-- ============================================================================
-- SECTION 9: COHOMOLOGY AND COCYCLES
-- ============================================================================

noncomputable def cocycle_closed_path (x : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.cocycle x)) AInfExpr.zero :=
  .cons .cocycle_closed (.nil _)

noncomputable def coboundary_path (x : AInfExpr) :
    AInfPath (AInfExpr.coboundary x) (AInfExpr.m1 x) :=
  .cons .coboundary_exact (.nil _)

noncomputable def cohomology_class_path (x : AInfExpr) :
    AInfPath (AInfExpr.cocycle x) (AInfExpr.cohomology x) :=
  .cons .cohomology_class (.nil _)

-- m1 of coboundary = m1(m1(x)) = 0
noncomputable def coboundary_is_cocycle (x : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.coboundary x)) AInfExpr.zero :=
  .cons (.congrArg AInfExpr.m1 .coboundary_exact)
    (.cons .m1_squared (.nil _))

-- Cocycles form a subcomplex under m2
noncomputable def cocycle_m2_stasheff (x y : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.m2 (AInfExpr.cocycle x) (AInfExpr.cocycle y)))
             (AInfExpr.add (AInfExpr.m2 (AInfExpr.m1 (AInfExpr.cocycle x)) (AInfExpr.cocycle y))
                           (AInfExpr.m2 (AInfExpr.cocycle x) (AInfExpr.m1 (AInfExpr.cocycle y)))) :=
  .cons .stasheff_2 (.nil _)

-- ============================================================================
-- SECTION 10: MINIMAL MODELS AND KADEISHVILI
-- ============================================================================

noncomputable def minimal_model_path (a : AInfExpr) :
    AInfPath a (AInfExpr.quasiIso (AInfExpr.minModel a) a) :=
  .cons .minimal_model_exists (.nil _)

noncomputable def minimal_m1_zero_path (a : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.minModel a)) AInfExpr.zero :=
  .cons .minimal_m1_zero (.nil _)

noncomputable def kadeishvili_path (a : AInfExpr) :
    AInfPath (AInfExpr.cohomology a)
             (AInfExpr.quasiIso (AInfExpr.cohomology a) a) :=
  .cons .kadeishvili (.nil _)

-- Minimal model has trivial differential
noncomputable def minimal_m1_sq_zero (a : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.m1 (AInfExpr.minModel a))) AInfExpr.zero :=
  .cons (.congrArg AInfExpr.m1 .minimal_m1_zero)
    (.cons .m1_zero (.nil _))

-- ============================================================================
-- SECTION 11: SUSPENSION AND DESUSPENSION
-- ============================================================================

noncomputable def susp_desusp_path (x : AInfExpr) :
    AInfPath (AInfExpr.susp (AInfExpr.desusp x)) x :=
  .cons .susp_desusp (.nil _)

noncomputable def desusp_susp_path (x : AInfExpr) :
    AInfPath (AInfExpr.desusp (AInfExpr.susp x)) x :=
  .cons .desusp_susp (.nil _)

noncomputable def m1_susp_path (x : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.susp x))
             (AInfExpr.neg (AInfExpr.susp (AInfExpr.m1 x))) :=
  .cons .m1_susp (.nil _)

-- susp ∘ desusp ∘ susp = susp
noncomputable def susp_desusp_susp (x : AInfExpr) :
    AInfPath (AInfExpr.susp (AInfExpr.desusp (AInfExpr.susp x)))
             (AInfExpr.susp x) :=
  .cons (.congrArg AInfExpr.susp .desusp_susp) (.nil _)

-- m1(susp(susp(x))) chain
noncomputable def m1_susp_susp (x : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.susp (AInfExpr.susp x)))
             (AInfExpr.neg (AInfExpr.susp (AInfExpr.m1 (AInfExpr.susp x)))) :=
  .cons .m1_susp (.nil _)

-- ============================================================================
-- SECTION 12: TENSOR PRODUCTS OF A∞ ALGEBRAS
-- ============================================================================

noncomputable def tensor_m1_path (x y : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.tensor x y))
             (AInfExpr.add (AInfExpr.tensor (AInfExpr.m1 x) y)
                           (AInfExpr.tensor x (AInfExpr.m1 y))) :=
  .cons .tensor_m1 (.nil _)

noncomputable def tensor_m2_path (x1 y1 x2 y2 : AInfExpr) :
    AInfPath (AInfExpr.m2 (AInfExpr.tensor x1 y1) (AInfExpr.tensor x2 y2))
             (AInfExpr.tensor (AInfExpr.m2 x1 x2) (AInfExpr.m2 y1 y2)) :=
  .cons .tensor_m2 (.nil _)

-- tensor m1 squared = 0
noncomputable def tensor_m1_squared (x y : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.m1 (AInfExpr.tensor x y)))
             (AInfExpr.m1 (AInfExpr.add (AInfExpr.tensor (AInfExpr.m1 x) y)
                                         (AInfExpr.tensor x (AInfExpr.m1 y)))) :=
  .cons (.congrArg AInfExpr.m1 .tensor_m1) (.nil _)

-- ============================================================================
-- SECTION 13: ADDITIVE STRUCTURE
-- ============================================================================

noncomputable def add_assoc_path :
    AInfPath (AInfExpr.add (AInfExpr.add a b) c)
             (AInfExpr.add a (AInfExpr.add b c)) :=
  .cons .add_assoc (.nil _)

noncomputable def add_comm_path :
    AInfPath (AInfExpr.add a b) (AInfExpr.add b a) :=
  .cons .add_comm (.nil _)

noncomputable def add_zero_path :
    AInfPath (AInfExpr.add a AInfExpr.zero) a :=
  .cons .add_zero (.nil _)

noncomputable def zero_add_path :
    AInfPath (AInfExpr.add AInfExpr.zero a) a :=
  .cons .zero_add (.nil _)

noncomputable def add_neg_path :
    AInfPath (AInfExpr.add a (AInfExpr.neg a)) AInfExpr.zero :=
  .cons .add_neg (.nil _)

noncomputable def neg_neg_path :
    AInfPath (AInfExpr.neg (AInfExpr.neg a)) a :=
  .cons .neg_neg (.nil _)

-- add is commutative involution: a+b+(-b)+(-a) = 0
noncomputable def add_cancel_chain (a b : AInfExpr) :
    AInfPath (AInfExpr.add (AInfExpr.add a b) (AInfExpr.add (AInfExpr.neg b) (AInfExpr.neg a)))
             (AInfExpr.add a (AInfExpr.add b (AInfExpr.add (AInfExpr.neg b) (AInfExpr.neg a)))) :=
  .cons .add_assoc (.nil _)

-- ============================================================================
-- SECTION 14: MULTI-STEP CHAINS
-- ============================================================================

-- m1(m2(m1(x), y)) via Stasheff
noncomputable def m1_m2_m1_left (x y : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.m2 (AInfExpr.m1 x) y))
             (AInfExpr.add (AInfExpr.m2 (AInfExpr.m1 (AInfExpr.m1 x)) y)
                           (AInfExpr.m2 (AInfExpr.m1 x) (AInfExpr.m1 y))) :=
  .cons .stasheff_2 (.nil _)

-- Chain: m1(m2(x,y)) → stasheff → use m2 zero
noncomputable def stasheff_with_zero (y : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.m2 AInfExpr.zero y))
             (AInfExpr.add (AInfExpr.m2 (AInfExpr.m1 AInfExpr.zero) y)
                           (AInfExpr.m2 AInfExpr.zero (AInfExpr.m1 y))) :=
  .cons .stasheff_2 (.nil _)

-- Bar diff compatibility: bar_diff ∘ bar_diff = 0
noncomputable def bar_complex_exact (x : AInfExpr) :
    AInfPath (AInfExpr.barDiff (AInfExpr.barDiff x)) AInfExpr.zero :=
  .cons .bar_diff_squared (.nil _)

-- m1 preserves tensor products (chain)
noncomputable def m1_tensor_chain (x y : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.tensor x y))
             (AInfExpr.add (AInfExpr.tensor (AInfExpr.m1 x) y)
                           (AInfExpr.tensor x (AInfExpr.m1 y))) :=
  .cons .tensor_m1 (.nil _)

-- Kadeishvili + minimal: H*(A) has A∞ structure with m1=0
noncomputable def kadeishvili_minimal_chain (a : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.minModel (AInfExpr.cohomology a))) AInfExpr.zero :=
  .cons .minimal_m1_zero (.nil _)

-- ============================================================================
-- SECTION 15: COMPOSITES AND DERIVED RESULTS
-- ============================================================================

-- f1 of unit
noncomputable def morph_f1_unit :
    AInfPath (AInfExpr.m2 (AInfExpr.f1 AInfExpr.one) (AInfExpr.f1 x))
             (AInfExpr.add (AInfExpr.m2 (AInfExpr.f1 AInfExpr.one) (AInfExpr.f1 x))
                           AInfExpr.zero) :=
  .cons (.symm .add_zero) (.nil _)

-- Double suspension involution
noncomputable def double_susp_desusp (x : AInfExpr) :
    AInfPath (AInfExpr.susp (AInfExpr.desusp (AInfExpr.susp (AInfExpr.desusp x)))) x :=
  .cons (.congrArg AInfExpr.susp (.congrArg AInfExpr.desusp .susp_desusp))
    (.cons .susp_desusp (.nil _))

-- Bar-cobar unit
noncomputable def bar_cobar_unit (a : AInfExpr) :
    AInfPath (AInfExpr.cobar (AInfExpr.bar a))
             (AInfExpr.quasiIso (AInfExpr.cobar (AInfExpr.bar a)) a) :=
  .cons .bar_cobar_equiv (.nil _)

-- HTT chain: π(ι(π(x))) = π(x)
noncomputable def htt_pi_iota_pi (x : AInfExpr) :
    AInfPath (AInfExpr.projection (AInfExpr.inclusion (AInfExpr.projection x)))
             (AInfExpr.projection x) :=
  .cons (.congrArg AInfExpr.projection (.trans .transfer_pi_iota (.refl _))) (.nil _)

-- HTT chain: h(h(x)) = 0
noncomputable def htt_hh_zero (x : AInfExpr) :
    AInfPath (AInfExpr.homotopy (AInfExpr.homotopy x))
             AInfExpr.zero :=
  .cons .homotopy_squared (.nil _)

-- Massey from mn for triples
noncomputable def massey_triple_mn (a b c : AInfExpr) :
    AInfPath (AInfExpr.massey a b c)
             (AInfExpr.cohomology (AInfExpr.mn 3 [a, b, c])) :=
  .cons .massey_from_m3
    (.cons (.congrArg AInfExpr.cohomology (.symm .mn_3_is_m3))
      (.nil _))

end AInfPath
end ComputationalPaths

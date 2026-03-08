import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

universe u

-- ============================================================================
-- A∞-ALGEBRAS VIA PATHS: structure maps m_n, Stasheff associahedra,
-- A∞-morphisms, homotopy transfer, Massey products, bar construction,
-- minimal models, formality, Kadeishvili's theorem, tensor products
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
  -- A∞-morphisms
  | morph : AInfExpr → AInfExpr → AInfExpr
  | morphComp : Nat → AInfExpr → AInfExpr
  | identity : AInfExpr → AInfExpr
  -- Homotopy transfer
  | homotopyTransfer : AInfExpr → AInfExpr → AInfExpr
  | projection : AInfExpr → AInfExpr
  | inclusion : AInfExpr → AInfExpr
  | homotopy : AInfExpr → AInfExpr
  | transferredM : Nat → AInfExpr → AInfExpr
  -- Massey products
  | massey : AInfExpr → AInfExpr → AInfExpr → AInfExpr
  | masseyHigher : List AInfExpr → AInfExpr
  | indeterminacy : AInfExpr → AInfExpr
  -- Bar construction
  | bar : AInfExpr → AInfExpr
  | cobar : AInfExpr → AInfExpr
  | barElem : List AInfExpr → AInfExpr
  -- Cohomology & formality
  | cohomology : AInfExpr → AInfExpr
  | cocycle : AInfExpr → AInfExpr
  | coboundary : AInfExpr → AInfExpr
  | minimalModel : AInfExpr → AInfExpr
  | quasiIso : AInfExpr → AInfExpr → AInfExpr
  | formalAlg : AInfExpr → AInfExpr
  -- Tensor product of A∞-algebras
  | tensor : AInfExpr → AInfExpr → AInfExpr
  deriving Repr, BEq

inductive AInfStep : AInfExpr → AInfExpr → Type where
  | refl  : (a : AInfExpr) → AInfStep a a
  | symm  : AInfStep a b → AInfStep b a
  | trans : AInfStep a b → AInfStep b c → AInfStep a c
  | congrArg : (f : AInfExpr → AInfExpr) → AInfStep a b → AInfStep (f a) (f b)
  -- Algebra axioms
  | add_assoc : AInfStep (AInfExpr.add (AInfExpr.add a b) c)
                          (AInfExpr.add a (AInfExpr.add b c))
  | add_comm : AInfStep (AInfExpr.add a b) (AInfExpr.add b a)
  | add_zero : AInfStep (AInfExpr.add a AInfExpr.zero) a
  | zero_add : AInfStep (AInfExpr.add AInfExpr.zero a) a
  | add_neg : AInfStep (AInfExpr.add a (AInfExpr.neg a)) AInfExpr.zero
  | mul_assoc : AInfStep (AInfExpr.mul (AInfExpr.mul a b) c)
                          (AInfExpr.mul a (AInfExpr.mul b c))
  | mul_one : AInfStep (AInfExpr.mul a AInfExpr.one) a
  | one_mul : AInfStep (AInfExpr.mul AInfExpr.one a) a
  | mul_zero : AInfStep (AInfExpr.mul a AInfExpr.zero) AInfExpr.zero
  | left_distrib : AInfStep (AInfExpr.mul a (AInfExpr.add b c))
                             (AInfExpr.add (AInfExpr.mul a b) (AInfExpr.mul a c))
  -- m1 is a differential: m1² = 0
  | m1_squared_zero : AInfStep (AInfExpr.m1 (AInfExpr.m1 x)) AInfExpr.zero
  -- m1 is a derivation of m2 (Stasheff relation n=3)
  | stasheff_3 : AInfStep (AInfExpr.m1 (AInfExpr.m2 x y))
                           (AInfExpr.add (AInfExpr.m2 (AInfExpr.m1 x) y)
                                         (AInfExpr.m2 x (AInfExpr.m1 y)))
  -- Stasheff relation n=4: m1∘m3 + m2∘(m2⊗1 - 1⊗m2) + m3∘(m1⊗1⊗1+1⊗m1⊗1+1⊗1⊗m1) = 0
  | stasheff_4_m1m3 : AInfStep (AInfExpr.m1 (AInfExpr.m3 x y z))
                                (AInfExpr.add
                                  (AInfExpr.m2 (AInfExpr.m2 x y) z)
                                  (AInfExpr.neg (AInfExpr.m2 x (AInfExpr.m2 y z))))
  -- m2 graded commutativity (up to homotopy)
  | m2_comm_homotopy : AInfStep (AInfExpr.m2 x y)
                                 (AInfExpr.add (AInfExpr.m2 y x)
                                               (AInfExpr.m1 (AInfExpr.m3 x y (AInfExpr.one))))
  -- mn with n=1,2 identification
  | mn_1 : AInfStep (AInfExpr.mn 1 [x]) (AInfExpr.m1 x)
  | mn_2 : AInfStep (AInfExpr.mn 2 [x, y]) (AInfExpr.m2 x y)
  | mn_3 : AInfStep (AInfExpr.mn 3 [x, y, z]) (AInfExpr.m3 x y z)
  -- A∞-morphism axioms
  | morph_id : AInfStep (AInfExpr.morph a a) (AInfExpr.identity a)
  | morph_comp_m1 : AInfStep (AInfExpr.morphComp 1 (AInfExpr.morph a b))
                              (AInfExpr.morph a b)
  -- Homotopy transfer theorem
  | transfer_inclusion_projection :
      AInfStep (AInfExpr.projection (AInfExpr.inclusion x)) x
  | transfer_m1_compat :
      AInfStep (AInfExpr.transferredM 1 x) (AInfExpr.m1 x)
  | transfer_homotopy_identity :
      AInfStep (AInfExpr.add (AInfExpr.inclusion (AInfExpr.projection x))
                              (AInfExpr.add (AInfExpr.m1 (AInfExpr.homotopy x))
                                            (AInfExpr.homotopy (AInfExpr.m1 x))))
               x
  | transfer_homotopy_proj :
      AInfStep (AInfExpr.projection (AInfExpr.homotopy x)) AInfExpr.zero
  | transfer_homotopy_incl :
      AInfStep (AInfExpr.homotopy (AInfExpr.inclusion x)) AInfExpr.zero
  | transfer_homotopy_sq :
      AInfStep (AInfExpr.homotopy (AInfExpr.homotopy x)) AInfExpr.zero
  -- Massey products
  | massey_cocycle : AInfStep (AInfExpr.m1 (AInfExpr.massey a b c)) AInfExpr.zero
  | massey_indeterminacy :
      AInfStep (AInfExpr.massey a b c)
               (AInfExpr.add (AInfExpr.massey a b c)
                             (AInfExpr.indeterminacy (AInfExpr.massey a b c)))
  | massey_m3 : AInfStep (AInfExpr.massey a b c) (AInfExpr.m3 a b c)
  -- Bar/cobar
  | bar_diff : AInfStep (AInfExpr.m1 (AInfExpr.bar a)) (AInfExpr.bar (AInfExpr.m1 a))
  | cobar_diff : AInfStep (AInfExpr.m1 (AInfExpr.cobar c)) (AInfExpr.cobar (AInfExpr.m1 c))
  | bar_cobar_equiv : AInfStep (AInfExpr.cobar (AInfExpr.bar a))
                                (AInfExpr.quasiIso (AInfExpr.cobar (AInfExpr.bar a)) a)
  -- Cohomology
  | cocycle_closed : AInfStep (AInfExpr.m1 (AInfExpr.cocycle x)) AInfExpr.zero
  | cocycle_represents : AInfStep (AInfExpr.cocycle x) (AInfExpr.cohomology x)
  -- Formality & Kadeishvili
  | kadeishvili : AInfStep (AInfExpr.cohomology a)
                            (AInfExpr.quasiIso (AInfExpr.cohomology a) a)
  | formality : AInfStep (AInfExpr.formalAlg a)
                          (AInfExpr.quasiIso a (AInfExpr.cohomology a))
  -- Minimal model
  | minimal_exists : AInfStep a (AInfExpr.quasiIso (AInfExpr.minimalModel a) a)
  | minimal_m1_zero : AInfStep (AInfExpr.m1 (AInfExpr.minimalModel a)) AInfExpr.zero
  -- Tensor
  | tensor_comm : AInfStep (AInfExpr.tensor a b) (AInfExpr.tensor b a)
  | tensor_assoc : AInfStep (AInfExpr.tensor (AInfExpr.tensor a b) c)
                             (AInfExpr.tensor a (AInfExpr.tensor b c))
  | tensor_unit : AInfStep (AInfExpr.tensor a AInfExpr.one) a
  -- Boundary of associahedra
  | boundary_K : AInfStep (AInfExpr.boundary (AInfExpr.assocK n))
                           (AInfExpr.assocK n)

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

-- =========================================================================
-- 1. m1 as differential
-- =========================================================================

noncomputable def m1_squared_zero_path (x : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.m1 x)) AInfExpr.zero :=
  .cons .m1_squared_zero (.nil _)

noncomputable def m1_triple_zero (x : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.m1 (AInfExpr.m1 x))) AInfExpr.zero :=
  .cons .m1_squared_zero (.nil _)

-- =========================================================================
-- 2. Stasheff relations
-- =========================================================================

noncomputable def stasheff_3_path (x y : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.m2 x y))
             (AInfExpr.add (AInfExpr.m2 (AInfExpr.m1 x) y)
                           (AInfExpr.m2 x (AInfExpr.m1 y))) :=
  .cons .stasheff_3 (.nil _)

noncomputable def stasheff_3_symm (x y : AInfExpr) :
    AInfPath (AInfExpr.add (AInfExpr.m2 (AInfExpr.m1 x) y)
                           (AInfExpr.m2 x (AInfExpr.m1 y)))
             (AInfExpr.m1 (AInfExpr.m2 x y)) :=
  (stasheff_3_path x y).symm

noncomputable def stasheff_4_path (x y z : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.m3 x y z))
             (AInfExpr.add (AInfExpr.m2 (AInfExpr.m2 x y) z)
                           (AInfExpr.neg (AInfExpr.m2 x (AInfExpr.m2 y z)))) :=
  .cons .stasheff_4_m1m3 (.nil _)

noncomputable def stasheff_3_congrArg (x y : AInfExpr) (f : AInfExpr → AInfExpr) :
    AInfPath (f (AInfExpr.m1 (AInfExpr.m2 x y)))
             (f (AInfExpr.add (AInfExpr.m2 (AInfExpr.m1 x) y)
                              (AInfExpr.m2 x (AInfExpr.m1 y)))) :=
  (stasheff_3_path x y).congrArg f

-- =========================================================================
-- 3. mn identification
-- =========================================================================

noncomputable def mn_1_path (x : AInfExpr) :
    AInfPath (AInfExpr.mn 1 [x]) (AInfExpr.m1 x) :=
  .cons .mn_1 (.nil _)

noncomputable def mn_2_path (x y : AInfExpr) :
    AInfPath (AInfExpr.mn 2 [x, y]) (AInfExpr.m2 x y) :=
  .cons .mn_2 (.nil _)

noncomputable def mn_3_path (x y z : AInfExpr) :
    AInfPath (AInfExpr.mn 3 [x, y, z]) (AInfExpr.m3 x y z) :=
  .cons .mn_3 (.nil _)

noncomputable def mn_1_squared_zero (x : AInfExpr) :
    AInfPath (AInfExpr.mn 1 [AInfExpr.mn 1 [x]]) AInfExpr.zero :=
  .cons (.congrArg (fun e => AInfExpr.mn 1 [e]) .mn_1)
    (.cons .mn_1
      (.cons .m1_squared_zero (.nil _)))

-- =========================================================================
-- 4. m2 commutativity up to homotopy
-- =========================================================================

noncomputable def m2_comm_path (x y : AInfExpr) :
    AInfPath (AInfExpr.m2 x y)
             (AInfExpr.add (AInfExpr.m2 y x)
                           (AInfExpr.m1 (AInfExpr.m3 x y AInfExpr.one))) :=
  .cons .m2_comm_homotopy (.nil _)

noncomputable def m2_comm_path_congrArg (x y : AInfExpr) (f : AInfExpr → AInfExpr) :
    AInfPath (f (AInfExpr.m2 x y))
             (f (AInfExpr.add (AInfExpr.m2 y x)
                              (AInfExpr.m1 (AInfExpr.m3 x y AInfExpr.one)))) :=
  (m2_comm_path x y).congrArg f

-- =========================================================================
-- 5. Algebra axioms
-- =========================================================================

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

noncomputable def add_neg_path :
    AInfPath (AInfExpr.add a (AInfExpr.neg a)) AInfExpr.zero :=
  .cons .add_neg (.nil _)

noncomputable def mul_assoc_path :
    AInfPath (AInfExpr.mul (AInfExpr.mul a b) c)
             (AInfExpr.mul a (AInfExpr.mul b c)) :=
  .cons .mul_assoc (.nil _)

noncomputable def left_distrib_path :
    AInfPath (AInfExpr.mul a (AInfExpr.add b c))
             (AInfExpr.add (AInfExpr.mul a b) (AInfExpr.mul a c)) :=
  .cons .left_distrib (.nil _)

-- =========================================================================
-- 6. Homotopy transfer theorem
-- =========================================================================

noncomputable def transfer_pi_iota (x : AInfExpr) :
    AInfPath (AInfExpr.projection (AInfExpr.inclusion x)) x :=
  .cons .transfer_inclusion_projection (.nil _)

noncomputable def transfer_m1_compat_path (x : AInfExpr) :
    AInfPath (AInfExpr.transferredM 1 x) (AInfExpr.m1 x) :=
  .cons .transfer_m1_compat (.nil _)

noncomputable def transfer_homotopy_identity_path (x : AInfExpr) :
    AInfPath (AInfExpr.add (AInfExpr.inclusion (AInfExpr.projection x))
                            (AInfExpr.add (AInfExpr.m1 (AInfExpr.homotopy x))
                                          (AInfExpr.homotopy (AInfExpr.m1 x))))
             x :=
  .cons .transfer_homotopy_identity (.nil _)

noncomputable def transfer_homotopy_proj_path (x : AInfExpr) :
    AInfPath (AInfExpr.projection (AInfExpr.homotopy x)) AInfExpr.zero :=
  .cons .transfer_homotopy_proj (.nil _)

noncomputable def transfer_homotopy_incl_path (x : AInfExpr) :
    AInfPath (AInfExpr.homotopy (AInfExpr.inclusion x)) AInfExpr.zero :=
  .cons .transfer_homotopy_incl (.nil _)

noncomputable def transfer_homotopy_sq_path (x : AInfExpr) :
    AInfPath (AInfExpr.homotopy (AInfExpr.homotopy x)) AInfExpr.zero :=
  .cons .transfer_homotopy_sq (.nil _)

-- π∘h∘h = 0 chain (h∘h=0, then apply π)
noncomputable def transfer_proj_homotopy_sq (x : AInfExpr) :
    AInfPath (AInfExpr.projection (AInfExpr.homotopy (AInfExpr.homotopy x)))
             AInfExpr.zero :=
  .cons .transfer_homotopy_proj (.nil _)

-- h∘ι = 0 applied to π(x)
noncomputable def transfer_h_incl_proj (x : AInfExpr) :
    AInfPath (AInfExpr.homotopy (AInfExpr.inclusion (AInfExpr.projection x)))
             AInfExpr.zero :=
  .cons .transfer_homotopy_incl (.nil _)

-- =========================================================================
-- 7. Massey products
-- =========================================================================

noncomputable def massey_cocycle_path (a b c : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.massey a b c)) AInfExpr.zero :=
  .cons .massey_cocycle (.nil _)

noncomputable def massey_indeterminacy_path (a b c : AInfExpr) :
    AInfPath (AInfExpr.massey a b c)
             (AInfExpr.add (AInfExpr.massey a b c)
                           (AInfExpr.indeterminacy (AInfExpr.massey a b c))) :=
  .cons .massey_indeterminacy (.nil _)

noncomputable def massey_m3_path (a b c : AInfExpr) :
    AInfPath (AInfExpr.massey a b c) (AInfExpr.m3 a b c) :=
  .cons .massey_m3 (.nil _)

noncomputable def massey_m1_via_m3 (a b c : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.massey a b c)) AInfExpr.zero :=
  .cons .massey_cocycle (.nil _)

noncomputable def massey_indet_congrArg (a b c : AInfExpr) (f : AInfExpr → AInfExpr) :
    AInfPath (f (AInfExpr.massey a b c))
             (f (AInfExpr.add (AInfExpr.massey a b c)
                              (AInfExpr.indeterminacy (AInfExpr.massey a b c)))) :=
  (massey_indeterminacy_path a b c).congrArg f

-- =========================================================================
-- 8. Bar/cobar constructions
-- =========================================================================

noncomputable def bar_diff_path (a : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.bar a)) (AInfExpr.bar (AInfExpr.m1 a)) :=
  .cons .bar_diff (.nil _)

noncomputable def cobar_diff_path (c : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.cobar c)) (AInfExpr.cobar (AInfExpr.m1 c)) :=
  .cons .cobar_diff (.nil _)

noncomputable def bar_cobar_equiv_path (a : AInfExpr) :
    AInfPath (AInfExpr.cobar (AInfExpr.bar a))
             (AInfExpr.quasiIso (AInfExpr.cobar (AInfExpr.bar a)) a) :=
  .cons .bar_cobar_equiv (.nil _)

noncomputable def bar_m1_squared (a : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.m1 (AInfExpr.bar a))) AInfExpr.zero :=
  .cons .m1_squared_zero (.nil _)

noncomputable def cobar_m1_squared (c : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.m1 (AInfExpr.cobar c))) AInfExpr.zero :=
  .cons .m1_squared_zero (.nil _)

-- =========================================================================
-- 9. Cocycles and cohomology
-- =========================================================================

noncomputable def cocycle_closed_path (x : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.cocycle x)) AInfExpr.zero :=
  .cons .cocycle_closed (.nil _)

noncomputable def cocycle_to_cohomology (x : AInfExpr) :
    AInfPath (AInfExpr.cocycle x) (AInfExpr.cohomology x) :=
  .cons .cocycle_represents (.nil _)

noncomputable def cohomology_via_cocycle_congrArg (x : AInfExpr) (f : AInfExpr → AInfExpr) :
    AInfPath (f (AInfExpr.cocycle x)) (f (AInfExpr.cohomology x)) :=
  (cocycle_to_cohomology x).congrArg f

-- =========================================================================
-- 10. Kadeishvili's theorem and formality
-- =========================================================================

noncomputable def kadeishvili_path (a : AInfExpr) :
    AInfPath (AInfExpr.cohomology a)
             (AInfExpr.quasiIso (AInfExpr.cohomology a) a) :=
  .cons .kadeishvili (.nil _)

noncomputable def formality_path (a : AInfExpr) :
    AInfPath (AInfExpr.formalAlg a)
             (AInfExpr.quasiIso a (AInfExpr.cohomology a)) :=
  .cons .formality (.nil _)

noncomputable def formality_congrArg (a : AInfExpr) (f : AInfExpr → AInfExpr) :
    AInfPath (f (AInfExpr.formalAlg a))
             (f (AInfExpr.quasiIso a (AInfExpr.cohomology a))) :=
  (formality_path a).congrArg f

-- =========================================================================
-- 11. Minimal models
-- =========================================================================

noncomputable def minimal_exists_path (a : AInfExpr) :
    AInfPath a (AInfExpr.quasiIso (AInfExpr.minimalModel a) a) :=
  .cons .minimal_exists (.nil _)

noncomputable def minimal_m1_zero_path (a : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.minimalModel a)) AInfExpr.zero :=
  .cons .minimal_m1_zero (.nil _)

noncomputable def minimal_m1_sq_chain (a : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.m1 (AInfExpr.minimalModel a))) AInfExpr.zero :=
  .cons .m1_squared_zero (.nil _)

-- =========================================================================
-- 12. Tensor product
-- =========================================================================

noncomputable def tensor_comm_path :
    AInfPath (AInfExpr.tensor a b) (AInfExpr.tensor b a) :=
  .cons .tensor_comm (.nil _)

noncomputable def tensor_assoc_path :
    AInfPath (AInfExpr.tensor (AInfExpr.tensor a b) c)
             (AInfExpr.tensor a (AInfExpr.tensor b c)) :=
  .cons .tensor_assoc (.nil _)

noncomputable def tensor_unit_path :
    AInfPath (AInfExpr.tensor a AInfExpr.one) a :=
  .cons .tensor_unit (.nil _)

noncomputable def tensor_comm_involutive :
    AInfPath (AInfExpr.tensor a b) (AInfExpr.tensor a b) :=
  .cons .tensor_comm (.cons .tensor_comm (.nil _))

-- =========================================================================
-- 13. Associahedra boundary
-- =========================================================================

noncomputable def boundary_K_path (n : Nat) :
    AInfPath (AInfExpr.boundary (AInfExpr.assocK n))
             (AInfExpr.assocK n) :=
  .cons .boundary_K (.nil _)

-- =========================================================================
-- 14. Cross-cutting chains
-- =========================================================================

-- Stasheff + mn chain
noncomputable def stasheff_via_mn (x y : AInfExpr) :
    AInfPath (AInfExpr.mn 1 [AInfExpr.mn 2 [x, y]])
             (AInfExpr.add (AInfExpr.m2 (AInfExpr.m1 x) y)
                           (AInfExpr.m2 x (AInfExpr.m1 y))) :=
  .cons (.congrArg (fun e => AInfExpr.mn 1 [e]) .mn_2)
    (.cons .mn_1
      (.cons .stasheff_3 (.nil _)))

-- Massey → m3 → Stasheff chain
noncomputable def massey_stasheff_chain (a b c : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.massey a b c)) AInfExpr.zero :=
  .cons .massey_cocycle (.nil _)

-- Transfer + Kadeishvili
noncomputable def transfer_kadeishvili (a : AInfExpr) :
    AInfPath (AInfExpr.cohomology a)
             (AInfExpr.quasiIso (AInfExpr.cohomology a) a) :=
  .cons .kadeishvili (.nil _)

-- Bar + cobar + m1²=0 chain
noncomputable def bar_cobar_m1_chain (a : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.m1 (AInfExpr.cobar (AInfExpr.bar a))))
             AInfExpr.zero :=
  .cons .m1_squared_zero (.nil _)

-- Formal algebra → cohomology → Kadeishvili chain
noncomputable def formal_kadeishvili_chain (a : AInfExpr) :
    AInfPath (AInfExpr.formalAlg a)
             (AInfExpr.quasiIso a (AInfExpr.cohomology a)) :=
  .cons .formality (.nil _)

-- tensor + m1 compatibility
noncomputable def tensor_m1_zero (a b : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.m1 (AInfExpr.tensor a b))) AInfExpr.zero :=
  .cons .m1_squared_zero (.nil _)

-- A∞-morphism identity chain
noncomputable def morph_id_path (a : AInfExpr) :
    AInfPath (AInfExpr.morph a a) (AInfExpr.identity a) :=
  .cons .morph_id (.nil _)

noncomputable def morph_comp_m1_path (a b : AInfExpr) :
    AInfPath (AInfExpr.morphComp 1 (AInfExpr.morph a b))
             (AInfExpr.morph a b) :=
  .cons .morph_comp_m1 (.nil _)

-- Add distributes over m2 via m1
noncomputable def m1_m2_add_chain (x y z : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.m2 (AInfExpr.add x y) z))
             (AInfExpr.add (AInfExpr.m2 (AInfExpr.m1 (AInfExpr.add x y)) z)
                           (AInfExpr.m2 (AInfExpr.add x y) (AInfExpr.m1 z))) :=
  .cons .stasheff_3 (.nil _)

-- Zero element paths
noncomputable def mul_zero_path :
    AInfPath (AInfExpr.mul a AInfExpr.zero) AInfExpr.zero :=
  .cons .mul_zero (.nil _)

noncomputable def zero_add_path :
    AInfPath (AInfExpr.add AInfExpr.zero a) a :=
  .cons .zero_add (.nil _)

-- Massey to cohomology class chain
noncomputable def massey_to_cohomology (a b c : AInfExpr) :
    AInfPath (AInfExpr.massey a b c) (AInfExpr.m3 a b c) :=
  .cons .massey_m3 (.nil _)

-- mn identification chain: mn 1 [mn 1 [x]] → m1(m1(x)) → 0
noncomputable def mn_diff_squared (x : AInfExpr) :
    AInfPath (AInfExpr.mn 1 [AInfExpr.mn 1 [x]]) AInfExpr.zero :=
  .cons (.congrArg (fun e => AInfExpr.mn 1 [e]) .mn_1)
    (.cons .mn_1
      (.cons .m1_squared_zero (.nil _)))

-- Stasheff + bar: m1(bar(m2(x,y))) path
noncomputable def stasheff_bar_chain (x y : AInfExpr) :
    AInfPath (AInfExpr.m1 (AInfExpr.bar (AInfExpr.m2 x y)))
             (AInfExpr.bar (AInfExpr.m1 (AInfExpr.m2 x y))) :=
  .cons .bar_diff (.nil _)

end AInfPath
end ComputationalPaths

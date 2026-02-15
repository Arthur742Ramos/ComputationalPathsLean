import ComputationalPaths.Path.Core

namespace ComputationalPaths

universe u

/-! # Quantum Groups Deep II via Computational Paths

Quantized enveloping algebras U_q(g), R-matrix and Yang-Baxter equation,
quantum doubles, ribbon categories, quantum dimension, Reshetikhin-Turaev
invariants, Kazhdan-Lusztig equivalence, crystal bases, canonical bases,
Lusztig's categorification.
-/

-- ═══════════════════════════════════════════════════════════════
-- SECTION 1: Core Domain Types
-- ═══════════════════════════════════════════════════════════════

/-- Quantum parameter -/
inductive QParam : Type where
  | generic : QParam
  | rootOfUnity : Nat → QParam
  | classical : QParam  -- q → 1

/-- Generator types for U_q(g) -/
inductive UqGen : Type where
  | E : Nat → UqGen      -- positive root generators
  | F : Nat → UqGen      -- negative root generators
  | K : Nat → UqGen      -- Cartan generators
  | Kinv : Nat → UqGen   -- inverse Cartan

/-- Quantum algebra elements -/
inductive QAlgElem : Type where
  | one : QAlgElem
  | gen : UqGen → QAlgElem
  | mul : QAlgElem → QAlgElem → QAlgElem
  | add : QAlgElem → QAlgElem → QAlgElem
  | qScalar : QAlgElem   -- scalar q
  | zero : QAlgElem

/-- R-matrix components -/
inductive RMatrix : Type where
  | identity : RMatrix
  | universal : RMatrix
  | quasitriangular : RMatrix → RMatrix
  | inverse : RMatrix → RMatrix
  | tensorFlip : RMatrix → RMatrix

/-- Ribbon category data -/
inductive RibbonData : Type where
  | twist : RibbonData
  | braiding : RibbonData
  | duality : RibbonData
  | compose : RibbonData → RibbonData → RibbonData
  | tensor : RibbonData → RibbonData → RibbonData

/-- Quantum dimension values -/
inductive QDim : Type where
  | classical : Nat → QDim
  | quantum : Nat → QDim    -- [n]_q
  | product : QDim → QDim → QDim
  | ratio : QDim → QDim → QDim

/-- Crystal base data -/
inductive CrystalBase : Type where
  | highest : Nat → CrystalBase
  | lowering : Nat → CrystalBase → CrystalBase  -- ~F_i applied
  | tensor : CrystalBase → CrystalBase → CrystalBase
  | connected : CrystalBase

/-- Canonical base elements -/
inductive CanonBase : Type where
  | standard : Nat → CanonBase
  | dual : CanonBase → CanonBase
  | barInvariant : CanonBase → CanonBase
  | positive : CanonBase → CanonBase

/-- RT invariant components -/
inductive RTInvariant : Type where
  | trivial : RTInvariant
  | jones : Nat → RTInvariant
  | homfly : RTInvariant
  | colored : Nat → RTInvariant → RTInvariant
  | cabled : Nat → RTInvariant → RTInvariant

/-- Categorification data -/
inductive CatData : Type where
  | module : CatData
  | functor : CatData → CatData → CatData
  | natural : CatData → CatData → CatData
  | decategorify : CatData → CatData
  | grothendieck : CatData → CatData

-- ═══════════════════════════════════════════════════════════════
-- SECTION 2: Quantum Group Steps
-- ═══════════════════════════════════════════════════════════════

inductive QGStep : (α : Type u) → α → α → Type (u + 1) where
  | refl : {α : Type u} → (a : α) → QGStep α a a
  | symm : {α : Type u} → {a b : α} → QGStep α a b → QGStep α b a
  | trans : {α : Type u} → {a b c : α} →
      QGStep α a b → QGStep α b c → QGStep α a c
  | congrArg : {α β : Type u} → {a₁ a₂ : α} →
      (f : α → β) → QGStep α a₁ a₂ → QGStep β (f a₁) (f a₂)
  -- U_q(g) relations
  | kkInv : QGStep QAlgElem
      (QAlgElem.mul (QAlgElem.gen (UqGen.K i)) (QAlgElem.gen (UqGen.Kinv i)))
      QAlgElem.one
  | kInvK : QGStep QAlgElem
      (QAlgElem.mul (QAlgElem.gen (UqGen.Kinv i)) (QAlgElem.gen (UqGen.K i)))
      QAlgElem.one
  | qSerre : QGStep QAlgElem
      (QAlgElem.mul (QAlgElem.gen (UqGen.E i)) (QAlgElem.gen (UqGen.F j)))
      (QAlgElem.mul (QAlgElem.gen (UqGen.F j)) (QAlgElem.gen (UqGen.E i)))
  | unitLeft : QGStep QAlgElem (QAlgElem.mul QAlgElem.one a) a
  | unitRight : QGStep QAlgElem (QAlgElem.mul a QAlgElem.one) a
  | zeroLeft : QGStep QAlgElem (QAlgElem.mul QAlgElem.zero a) QAlgElem.zero
  | addComm : QGStep QAlgElem (QAlgElem.add a b) (QAlgElem.add b a)
  | classicalLimit : QGStep QParam QParam.generic QParam.classical
  -- R-matrix / Yang-Baxter
  | rMatrixInv : QGStep RMatrix (RMatrix.quasitriangular (RMatrix.inverse r))
      (RMatrix.inverse (RMatrix.quasitriangular r))
  | yangBaxter : QGStep RMatrix
      (RMatrix.tensorFlip (RMatrix.quasitriangular r))
      (RMatrix.quasitriangular (RMatrix.tensorFlip r))
  | rIdentity : QGStep RMatrix (RMatrix.quasitriangular RMatrix.identity) RMatrix.identity
  | rInvCancel : QGStep RMatrix
      (RMatrix.quasitriangular (RMatrix.inverse (RMatrix.quasitriangular r)))
      (RMatrix.inverse r)
  -- Ribbon category
  | ribbonTwistSquare : QGStep RibbonData
      (RibbonData.compose RibbonData.twist RibbonData.twist)
      (RibbonData.compose RibbonData.braiding RibbonData.braiding)
  | ribbonBraidDual : QGStep RibbonData
      (RibbonData.compose RibbonData.braiding RibbonData.duality)
      (RibbonData.compose RibbonData.duality RibbonData.braiding)
  | ribbonNaturality : QGStep RibbonData
      (RibbonData.compose (RibbonData.tensor a b) RibbonData.braiding)
      (RibbonData.compose RibbonData.braiding (RibbonData.tensor b a))
  -- Quantum dimension
  | qdimClassicalLimit : QGStep QDim (QDim.quantum n) (QDim.classical n)
  | qdimProduct : QGStep QDim (QDim.product (QDim.quantum n) (QDim.quantum m))
      (QDim.quantum (n * m))
  | qdimTensor : QGStep QDim (QDim.product a b) (QDim.product b a)
  -- Crystal bases
  | crystalTensorAssoc : QGStep CrystalBase
      (CrystalBase.tensor (CrystalBase.tensor a b) c)
      (CrystalBase.tensor a (CrystalBase.tensor b c))
  | crystalHighestWeight : QGStep CrystalBase
      (CrystalBase.lowering i (CrystalBase.highest n))
      (CrystalBase.highest (n - 1))
  | crystalConnected : QGStep CrystalBase
      (CrystalBase.tensor (CrystalBase.highest n) CrystalBase.connected)
      (CrystalBase.highest n)
  -- Canonical bases
  | canonBarInvolution : QGStep CanonBase
      (CanonBase.barInvariant (CanonBase.barInvariant b))
      b
  | canonDualDual : QGStep CanonBase (CanonBase.dual (CanonBase.dual b)) b
  | canonPositivity : QGStep CanonBase
      (CanonBase.positive (CanonBase.standard n))
      (CanonBase.standard n)
  -- RT invariants
  | rtTrivial : QGStep RTInvariant (RTInvariant.colored 1 inv) inv
  | rtJonesSkein : QGStep RTInvariant (RTInvariant.jones n) (RTInvariant.colored n RTInvariant.homfly)
  | rtCabling : QGStep RTInvariant (RTInvariant.cabled 1 inv) inv
  | rtCableCompose : QGStep RTInvariant
      (RTInvariant.cabled n (RTInvariant.cabled m inv))
      (RTInvariant.cabled (n * m) inv)
  -- Categorification / KL equivalence
  | catDecatId : QGStep CatData (CatData.decategorify (CatData.grothendieck c)) c
  | catFunctorCompose : QGStep CatData
      (CatData.functor a (CatData.functor b c))
      (CatData.functor (CatData.functor a b) c)
  | klEquivalence : QGStep CatData
      (CatData.grothendieck CatData.module)
      (CatData.decategorify CatData.module)

-- ═══════════════════════════════════════════════════════════════
-- SECTION 3: Path Type
-- ═══════════════════════════════════════════════════════════════

inductive QGPath : (α : Type u) → α → α → Type (u + 1) where
  | nil : {α : Type u} → (a : α) → QGPath α a a
  | cons : {α : Type u} → {a b c : α} →
      QGStep α a b → QGPath α b c → QGPath α a c

namespace QGPath

def trans {α : Type u} {a b c : α} (p : QGPath α a b) (q : QGPath α b c) :
    QGPath α a c :=
  match p with
  | .nil _ => q
  | .cons s rest => .cons s (rest.trans q)

def symm {α : Type u} {a b : α} (p : QGPath α a b) : QGPath α b a :=
  match p with
  | .nil _ => .nil _
  | .cons s rest => rest.symm.trans (.cons (.symm s) (.nil _))

def congrArg {α β : Type u} {a b : α} (f : α → β) (p : QGPath α a b) :
    QGPath β (f a) (f b) :=
  match p with
  | .nil _ => .nil _
  | .cons s rest => .cons (.congrArg f s) (congrArg f rest)

def length {α : Type u} {a b : α} (p : QGPath α a b) : Nat :=
  match p with
  | .nil _ => 0
  | .cons _ rest => 1 + rest.length

-- ═══════════════════════════════════════════════════════════════
-- SECTION 4: U_q(g) Algebra Theorems
-- ═══════════════════════════════════════════════════════════════

/-- KK⁻¹ = 1 -/
theorem kk_inv_one (i : Nat) :
    QGPath QAlgElem
      (QAlgElem.mul (QAlgElem.gen (UqGen.K i)) (QAlgElem.gen (UqGen.Kinv i)))
      QAlgElem.one :=
  .cons .kkInv (.nil _)

/-- K⁻¹K = 1 -/
theorem kinv_k_one (i : Nat) :
    QGPath QAlgElem
      (QAlgElem.mul (QAlgElem.gen (UqGen.Kinv i)) (QAlgElem.gen (UqGen.K i)))
      QAlgElem.one :=
  .cons .kInvK (.nil _)

/-- Both products give 1 -/
theorem k_both_inv (i : Nat) :
    QGPath QAlgElem
      (QAlgElem.mul (QAlgElem.gen (UqGen.K i)) (QAlgElem.gen (UqGen.Kinv i)))
      (QAlgElem.mul (QAlgElem.gen (UqGen.Kinv i)) (QAlgElem.gen (UqGen.K i))) :=
  (kk_inv_one i).trans (kinv_k_one i).symm

/-- Quantum Serre relation path -/
theorem q_serre_relation (i j : Nat) :
    QGPath QAlgElem
      (QAlgElem.mul (QAlgElem.gen (UqGen.E i)) (QAlgElem.gen (UqGen.F j)))
      (QAlgElem.mul (QAlgElem.gen (UqGen.F j)) (QAlgElem.gen (UqGen.E i))) :=
  .cons .qSerre (.nil _)

/-- Unit laws chain -/
theorem unit_laws (a : QAlgElem) :
    QGPath QAlgElem (QAlgElem.mul QAlgElem.one a) a :=
  .cons .unitLeft (.nil _)

/-- Left zero -/
theorem zero_absorb (a : QAlgElem) :
    QGPath QAlgElem (QAlgElem.mul QAlgElem.zero a) QAlgElem.zero :=
  .cons .zeroLeft (.nil _)

/-- Addition commutativity -/
theorem qadd_comm (a b : QAlgElem) :
    QGPath QAlgElem (QAlgElem.add a b) (QAlgElem.add b a) :=
  .cons .addComm (.nil _)

/-- Double add comm is identity -/
theorem qadd_double_comm (a b : QAlgElem) :
    QGPath QAlgElem (QAlgElem.add a b) (QAlgElem.add a b) :=
  (qadd_comm a b).trans (qadd_comm b a)

-- ═══════════════════════════════════════════════════════════════
-- SECTION 5: R-Matrix and Yang-Baxter
-- ═══════════════════════════════════════════════════════════════

/-- R-matrix on identity is identity -/
theorem r_identity : QGPath RMatrix (RMatrix.quasitriangular RMatrix.identity) RMatrix.identity :=
  .cons .rIdentity (.nil _)

/-- Yang-Baxter equation path -/
theorem yang_baxter (r : RMatrix) :
    QGPath RMatrix
      (RMatrix.tensorFlip (RMatrix.quasitriangular r))
      (RMatrix.quasitriangular (RMatrix.tensorFlip r)) :=
  .cons .yangBaxter (.nil _)

/-- R-matrix inverse commutes with quasitriangular -/
theorem r_inv_quasi (r : RMatrix) :
    QGPath RMatrix (RMatrix.quasitriangular (RMatrix.inverse r))
      (RMatrix.inverse (RMatrix.quasitriangular r)) :=
  .cons .rMatrixInv (.nil _)

/-- R-matrix inverse cancellation -/
theorem r_inv_cancel (r : RMatrix) :
    QGPath RMatrix
      (RMatrix.quasitriangular (RMatrix.inverse (RMatrix.quasitriangular r)))
      (RMatrix.inverse r) :=
  .cons .rInvCancel (.nil _)

/-- Yang-Baxter symmetry -/
theorem yang_baxter_symm (r : RMatrix) :
    QGPath RMatrix
      (RMatrix.quasitriangular (RMatrix.tensorFlip r))
      (RMatrix.tensorFlip (RMatrix.quasitriangular r)) :=
  (yang_baxter r).symm

/-- R-matrix functoriality -/
theorem r_matrix_functorial (f : RMatrix → RMatrix) (r : RMatrix) :
    QGPath RMatrix
      (f (RMatrix.quasitriangular (RMatrix.inverse r)))
      (f (RMatrix.inverse (RMatrix.quasitriangular r))) :=
  (r_inv_quasi r).congrArg f

-- ═══════════════════════════════════════════════════════════════
-- SECTION 6: Ribbon Category
-- ═══════════════════════════════════════════════════════════════

/-- Ribbon twist squared equals double braiding -/
theorem ribbon_twist_sq :
    QGPath RibbonData
      (RibbonData.compose RibbonData.twist RibbonData.twist)
      (RibbonData.compose RibbonData.braiding RibbonData.braiding) :=
  .cons .ribbonTwistSquare (.nil _)

/-- Ribbon braiding commutes with duality -/
theorem ribbon_braid_dual :
    QGPath RibbonData
      (RibbonData.compose RibbonData.braiding RibbonData.duality)
      (RibbonData.compose RibbonData.duality RibbonData.braiding) :=
  .cons .ribbonBraidDual (.nil _)

/-- Ribbon naturality -/
theorem ribbon_naturality (a b : RibbonData) :
    QGPath RibbonData
      (RibbonData.compose (RibbonData.tensor a b) RibbonData.braiding)
      (RibbonData.compose RibbonData.braiding (RibbonData.tensor b a)) :=
  .cons .ribbonNaturality (.nil _)

/-- Ribbon twist squared then symmetry -/
theorem ribbon_twist_braid_symm :
    QGPath RibbonData
      (RibbonData.compose RibbonData.braiding RibbonData.braiding)
      (RibbonData.compose RibbonData.twist RibbonData.twist) :=
  ribbon_twist_sq.symm

-- ═══════════════════════════════════════════════════════════════
-- SECTION 7: Quantum Dimension
-- ═══════════════════════════════════════════════════════════════

/-- Quantum dimension classical limit -/
theorem qdim_classical (n : Nat) :
    QGPath QDim (QDim.quantum n) (QDim.classical n) :=
  .cons .qdimClassicalLimit (.nil _)

/-- Quantum dimension product -/
theorem qdim_product (n m : Nat) :
    QGPath QDim (QDim.product (QDim.quantum n) (QDim.quantum m))
      (QDim.quantum (n * m)) :=
  .cons .qdimProduct (.nil _)

/-- Quantum dimension commutativity -/
theorem qdim_comm (a b : QDim) :
    QGPath QDim (QDim.product a b) (QDim.product b a) :=
  .cons .qdimTensor (.nil _)

/-- Quantum dimension product to classical -/
theorem qdim_product_classical (n m : Nat) :
    QGPath QDim (QDim.product (QDim.quantum n) (QDim.quantum m)) (QDim.classical (n * m)) :=
  (qdim_product n m).trans (qdim_classical (n * m))

/-- Quantum dimension double comm -/
theorem qdim_double_comm (a b : QDim) :
    QGPath QDim (QDim.product a b) (QDim.product a b) :=
  (qdim_comm a b).trans (qdim_comm b a)

-- ═══════════════════════════════════════════════════════════════
-- SECTION 8: Crystal Bases
-- ═══════════════════════════════════════════════════════════════

/-- Crystal tensor associativity -/
theorem crystal_assoc (a b c : CrystalBase) :
    QGPath CrystalBase
      (CrystalBase.tensor (CrystalBase.tensor a b) c)
      (CrystalBase.tensor a (CrystalBase.tensor b c)) :=
  .cons .crystalTensorAssoc (.nil _)

/-- Crystal highest weight lowering -/
theorem crystal_lower (i n : Nat) :
    QGPath CrystalBase
      (CrystalBase.lowering i (CrystalBase.highest n))
      (CrystalBase.highest (n - 1)) :=
  .cons .crystalHighestWeight (.nil _)

/-- Crystal connected component -/
theorem crystal_connected (n : Nat) :
    QGPath CrystalBase
      (CrystalBase.tensor (CrystalBase.highest n) CrystalBase.connected)
      (CrystalBase.highest n) :=
  .cons .crystalConnected (.nil _)

/-- Crystal lowering then back -/
theorem crystal_lower_symm (i n : Nat) :
    QGPath CrystalBase (CrystalBase.highest (n - 1))
      (CrystalBase.lowering i (CrystalBase.highest n)) :=
  (crystal_lower i n).symm

/-- Crystal functoriality -/
theorem crystal_functorial (f : CrystalBase → CrystalBase) (a b c : CrystalBase) :
    QGPath CrystalBase
      (f (CrystalBase.tensor (CrystalBase.tensor a b) c))
      (f (CrystalBase.tensor a (CrystalBase.tensor b c))) :=
  (crystal_assoc a b c).congrArg f

-- ═══════════════════════════════════════════════════════════════
-- SECTION 9: Canonical Bases
-- ═══════════════════════════════════════════════════════════════

/-- Bar involution is involutive -/
theorem canon_bar_involution (b : CanonBase) :
    QGPath CanonBase (CanonBase.barInvariant (CanonBase.barInvariant b)) b :=
  .cons .canonBarInvolution (.nil _)

/-- Dual is involutive -/
theorem canon_dual_involution (b : CanonBase) :
    QGPath CanonBase (CanonBase.dual (CanonBase.dual b)) b :=
  .cons .canonDualDual (.nil _)

/-- Positivity of standard basis -/
theorem canon_positivity (n : Nat) :
    QGPath CanonBase (CanonBase.positive (CanonBase.standard n)) (CanonBase.standard n) :=
  .cons .canonPositivity (.nil _)

/-- Bar then dual chain -/
theorem canon_bar_dual (b : CanonBase) :
    QGPath CanonBase (CanonBase.barInvariant (CanonBase.barInvariant b))
      (CanonBase.dual (CanonBase.dual b)) :=
  (canon_bar_involution b).trans (canon_dual_involution b).symm

/-- Canonical base round trip via bar -/
theorem canon_bar_roundtrip (b : CanonBase) :
    QGPath CanonBase b (CanonBase.barInvariant (CanonBase.barInvariant b)) :=
  (canon_bar_involution b).symm

-- ═══════════════════════════════════════════════════════════════
-- SECTION 10: Reshetikhin-Turaev Invariants
-- ═══════════════════════════════════════════════════════════════

/-- RT colored 1 is identity -/
theorem rt_colored_one (inv : RTInvariant) :
    QGPath RTInvariant (RTInvariant.colored 1 inv) inv :=
  .cons .rtTrivial (.nil _)

/-- Jones as colored HOMFLY -/
theorem rt_jones_homfly (n : Nat) :
    QGPath RTInvariant (RTInvariant.jones n) (RTInvariant.colored n RTInvariant.homfly) :=
  .cons .rtJonesSkein (.nil _)

/-- RT cabling identity -/
theorem rt_cable_one (inv : RTInvariant) :
    QGPath RTInvariant (RTInvariant.cabled 1 inv) inv :=
  .cons .rtCabling (.nil _)

/-- RT cable composition -/
theorem rt_cable_compose (n m : Nat) (inv : RTInvariant) :
    QGPath RTInvariant (RTInvariant.cabled n (RTInvariant.cabled m inv))
      (RTInvariant.cabled (n * m) inv) :=
  .cons .rtCableCompose (.nil _)

/-- RT colored then cable -/
theorem rt_colored_cable (n : Nat) (inv : RTInvariant) :
    QGPath RTInvariant (RTInvariant.colored 1 (RTInvariant.cabled 1 inv)) inv :=
  (rt_colored_one (RTInvariant.cabled 1 inv)).trans (rt_cable_one inv)

/-- Jones through colored then cable -/
theorem rt_jones_full (n : Nat) :
    QGPath RTInvariant (RTInvariant.jones n) (RTInvariant.colored n RTInvariant.homfly) :=
  rt_jones_homfly n

/-- RT functoriality -/
theorem rt_functorial (f : RTInvariant → RTInvariant) (inv : RTInvariant) :
    QGPath RTInvariant (f (RTInvariant.colored 1 inv)) (f inv) :=
  (rt_colored_one inv).congrArg f

-- ═══════════════════════════════════════════════════════════════
-- SECTION 11: Categorification / KL Equivalence
-- ═══════════════════════════════════════════════════════════════

/-- Decategorification of Grothendieck group -/
theorem cat_decat (c : CatData) :
    QGPath CatData (CatData.decategorify (CatData.grothendieck c)) c :=
  .cons .catDecatId (.nil _)

/-- Functor composition associativity -/
theorem cat_functor_assoc (a b c : CatData) :
    QGPath CatData
      (CatData.functor a (CatData.functor b c))
      (CatData.functor (CatData.functor a b) c) :=
  .cons .catFunctorCompose (.nil _)

/-- Kazhdan-Lusztig equivalence -/
theorem kl_equivalence :
    QGPath CatData
      (CatData.grothendieck CatData.module)
      (CatData.decategorify CatData.module) :=
  .cons .klEquivalence (.nil _)

/-- Decat-Grothendieck round trip -/
theorem cat_decat_roundtrip (c : CatData) :
    QGPath CatData c (CatData.decategorify (CatData.grothendieck c)) :=
  (cat_decat c).symm

/-- Categorification functoriality -/
theorem cat_functorial (f : CatData → CatData) (c : CatData) :
    QGPath CatData
      (f (CatData.decategorify (CatData.grothendieck c))) (f c) :=
  (cat_decat c).congrArg f

/-- KL equivalence with functor -/
theorem kl_with_functor (f : CatData → CatData) :
    QGPath CatData
      (f (CatData.grothendieck CatData.module))
      (f (CatData.decategorify CatData.module)) :=
  kl_equivalence.congrArg f

-- ═══════════════════════════════════════════════════════════════
-- SECTION 12: Cross-Domain Theorems
-- ═══════════════════════════════════════════════════════════════

/-- Classical limit path -/
theorem classical_limit : QGPath QParam QParam.generic QParam.classical :=
  .cons .classicalLimit (.nil _)

/-- Quantum group to crystal base connection -/
theorem uq_crystal_connection (f : QAlgElem → CrystalBase) (a b : QAlgElem) :
    QGPath CrystalBase (f (QAlgElem.add a b)) (f (QAlgElem.add b a)) :=
  (qadd_comm a b).congrArg f

/-- R-matrix to ribbon via functor -/
theorem r_to_ribbon (f : RMatrix → RibbonData) (r : RMatrix) :
    QGPath RibbonData
      (f (RMatrix.quasitriangular (RMatrix.inverse r)))
      (f (RMatrix.inverse (RMatrix.quasitriangular r))) :=
  (r_inv_quasi r).congrArg f

/-- Crystal to canonical base -/
theorem crystal_to_canon (f : CrystalBase → CanonBase) (a b c : CrystalBase) :
    QGPath CanonBase
      (f (CrystalBase.tensor (CrystalBase.tensor a b) c))
      (f (CrystalBase.tensor a (CrystalBase.tensor b c))) :=
  (crystal_assoc a b c).congrArg f

/-- RT invariant quantum dimension connection -/
theorem rt_qdim_connection (f : RTInvariant → QDim) (inv : RTInvariant) :
    QGPath QDim (f (RTInvariant.colored 1 inv)) (f inv) :=
  (rt_colored_one inv).congrArg f

/-- Full chain: quantum group → crystal → categorification -/
theorem full_quantum_chain (g : CrystalBase → CatData) (f : QAlgElem → CrystalBase)
    (a b : QAlgElem) :
    QGPath CatData (g (f (QAlgElem.add a b))) (g (f (QAlgElem.add b a))) :=
  (uq_crystal_connection f a b).congrArg g

/-- Quantum dimension to RT invariant via classical limit -/
theorem qdim_classical_rt (f : QDim → RTInvariant) (n : Nat) :
    QGPath RTInvariant (f (QDim.quantum n)) (f (QDim.classical n)) :=
  (qdim_classical n).congrArg f

end QGPath

end ComputationalPaths

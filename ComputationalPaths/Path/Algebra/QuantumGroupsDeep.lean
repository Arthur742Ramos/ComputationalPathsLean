import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.QuantumGroupsDeep

universe u

/-- Root datum labels using ASCII names requested by the project style. -/
structure RootDatum where
  Sym : Type u
  Gam : Type u
  pairing : Sym → Gam → Int

/-- Symbolic generators for `Uq(g)`. -/
inductive QGen : Type
  | E : Nat → QGen
  | F : Nat → QGen
  | K : Nat → QGen
  | Kinv : Nat → QGen
deriving DecidableEq, Repr

/-- Symbolic expressions in a quantized enveloping algebra. -/
inductive UqExpr : Type
  | one : UqExpr
  | zero : UqExpr
  | gen : QGen → UqExpr
  | add : UqExpr → UqExpr → UqExpr
  | mul : UqExpr → UqExpr → UqExpr
  | tensor : UqExpr → UqExpr → UqExpr
deriving DecidableEq, Repr

/-- Symbolic R-matrix expressions. -/
inductive RMatExpr : Type
  | id : RMatExpr
  | universal : RMatExpr
  | inverse : RMatExpr → RMatExpr
  | comp : RMatExpr → RMatExpr → RMatExpr
  | tensor : RMatExpr → RMatExpr → RMatExpr
  | braid12 : RMatExpr → RMatExpr
  | braid23 : RMatExpr → RMatExpr
deriving DecidableEq, Repr

/-- Symbolic quantum double data. -/
structure QuantumDouble where
  left : UqExpr
  right : UqExpr
deriving DecidableEq, Repr

/-- Symbolic ribbon category expressions. -/
inductive RibbonExpr : Type
  | obj : Nat → RibbonExpr
  | tensor : RibbonExpr → RibbonExpr → RibbonExpr
  | braiding : RibbonExpr → RibbonExpr → RibbonExpr
  | twist : RibbonExpr → RibbonExpr
  | dual : RibbonExpr → RibbonExpr
deriving DecidableEq, Repr

/-- Symbolic Drinfeld center objects. -/
structure CenterObj where
  carrier : RibbonExpr
  halfBraiding : RibbonExpr
deriving DecidableEq, Repr

/-- Symbolic Kazhdan-Lusztig expressions. -/
inductive KLExpr : Type
  | hecke : Nat → KLExpr
  | basis : Nat → KLExpr
  | polynomial : Nat → Nat → KLExpr
  | bar : KLExpr → KLExpr
deriving DecidableEq, Repr

/-- Symbolic crystal basis expressions. -/
inductive CrystalExpr : Type
  | highest : Nat → CrystalExpr
  | raise : Nat → CrystalExpr → CrystalExpr
  | lower : Nat → CrystalExpr → CrystalExpr
  | tensor : CrystalExpr → CrystalExpr → CrystalExpr
deriving DecidableEq, Repr

/-- Symbolic canonical basis expressions. -/
inductive CanonicalExpr : Type
  | basis : Nat → CanonicalExpr
  | bar : CanonicalExpr → CanonicalExpr
  | dual : CanonicalExpr → CanonicalExpr
  | prod : CanonicalExpr → CanonicalExpr → CanonicalExpr
deriving DecidableEq, Repr

/-- Abstract Hopf algebra operations. -/
structure HopfOps (A : Type u) where
  mul : A → A → A
  one : A
  comul1 : A → A
  comul2 : A → A
  counit : A → A
  antipode : A → A

/-- Build a primitive step directly from an equality witness. -/
noncomputable def mkStepFromEq {A : Type u} {a b : A} (h : a = b) : Step A :=
  Step.mk a b h

/-- Build a one-step path directly from an equality witness. -/
noncomputable def mkPathFromEq {A : Type u} {a b : A} (h : a = b) : Path a b :=
  Path.mk [mkStepFromEq h] h

/-- Reflexive path that stores a concrete singleton `Step.mk` trace. -/
noncomputable def mkReflPath {A : Type u} (a : A) : Path a a :=
  Path.mk [Step.mk a a rfl] rfl

noncomputable def kAction (x : UqExpr) : UqExpr :=
  UqExpr.mul (UqExpr.gen (QGen.K 0)) x

noncomputable def ybLeft (r : RMatExpr) : RMatExpr :=
  RMatExpr.comp (RMatExpr.comp (RMatExpr.braid12 r) (RMatExpr.braid23 r)) (RMatExpr.braid12 r)

noncomputable def ybRight (r : RMatExpr) : RMatExpr :=
  RMatExpr.comp (RMatExpr.braid23 r) (RMatExpr.comp (RMatExpr.braid12 r) (RMatExpr.braid23 r))

noncomputable def qDoubleSwap (d : QuantumDouble) : QuantumDouble :=
  { left := d.right, right := d.left }

/-! ## Core path API and rewrite lemmas -/

theorem thm01_step_symm_symm {A : Type u} (s : Step A) :
    Step.symm (Step.symm s) = s := by
  simpa using Step.symm_symm s

theorem thm02_mkPath_toEq {A : Type u} {a b : A} (h : a = b) :
    Path.toEq (mkPathFromEq h) = h := rfl

theorem thm03_mkRefl_toEq {A : Type u} (a : A) :
    Path.toEq (mkReflPath a) = rfl := rfl

theorem thm04_mkRefl_symm {A : Type u} (a : A) :
    Path.symm (mkReflPath a) = mkReflPath a := by
  rfl

theorem thm05_mkRefl_trans_left {A : Type u} (a : A) :
    Path.trans (Path.refl a) (mkReflPath a) = mkReflPath a := by
  simpa using Path.trans_refl_left (mkReflPath a)

theorem thm06_mkRefl_trans_right {A : Type u} (a : A) :
    Path.trans (mkReflPath a) (Path.refl a) = mkReflPath a := by
  simpa using Path.trans_refl_right (mkReflPath a)

theorem thm07_trans_assoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  simpa using Path.trans_assoc p q r

theorem thm08_symm_trans {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) := by
  simpa using Path.symm_trans p q

theorem thm09_symm_symm {A : Type u} {a b : A} (p : Path a b) :
    Path.symm (Path.symm p) = p := by
  simpa using Path.symm_symm p

theorem thm10_congrArg_trans {A B : Type u} (f : A → B)
    {a b c : A} (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
      Path.trans (Path.congrArg f p) (Path.congrArg f q) := by
  simpa using Path.congrArg_trans f p q

theorem thm11_congrArg_symm {A B : Type u} (f : A → B)
    {a b : A} (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) := by
  simpa using Path.congrArg_symm f p

theorem thm12_mkPath_irrel {A : Type u} {a b : A}
    (h1 h2 : a = b) :
    mkPathFromEq h1 = mkPathFromEq h2 := by
  cases h1
  cases h2
  rfl

/-! ## Hopf algebra coherence wrappers -/

noncomputable def thm13_hopf_mul_refl {A : Type u} (H : HopfOps A) (a b : A) :
    Path (H.mul a b) (H.mul a b) :=
  Path.refl (H.mul a b)

noncomputable def thm14_hopf_unit_refl {A : Type u} (H : HopfOps A) :
    Path H.one H.one :=
  mkReflPath H.one

noncomputable def thm15_hopf_comul1_refl {A : Type u} (H : HopfOps A) (a : A) :
    Path (H.comul1 a) (H.comul1 a) :=
  Path.refl (H.comul1 a)

noncomputable def thm16_hopf_comul2_refl {A : Type u} (H : HopfOps A) (a : A) :
    Path (H.comul2 a) (H.comul2 a) :=
  Path.refl (H.comul2 a)

noncomputable def thm17_hopf_antipode_congr {A : Type u} (H : HopfOps A)
    {a b : A} (p : Path a b) :
    Path (H.antipode a) (H.antipode b) :=
  Path.congrArg H.antipode p

noncomputable def thm18_hopf_counit_congr {A : Type u} (H : HopfOps A)
    {a b : A} (p : Path a b) :
    Path (H.counit a) (H.counit b) :=
  Path.congrArg H.counit p

noncomputable def thm19_hopf_mul_congr_left {A : Type u} (H : HopfOps A)
    (a : A) {b c : A} (p : Path b c) :
    Path (H.mul a b) (H.mul a c) :=
  Path.congrArg (fun x => H.mul a x) p

noncomputable def thm20_hopf_mul_congr_right {A : Type u} (H : HopfOps A)
    (a : A) {b c : A} (p : Path b c) :
    Path (H.mul b a) (H.mul c a) :=
  Path.congrArg (fun x => H.mul x a) p

theorem thm21_hopf_trans_assoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  simpa using Path.trans_assoc p q r

theorem thm22_hopf_symm_trans {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) := by
  simpa using Path.symm_trans p q

/-! ## `Uq(g)` path calculations -/

noncomputable def thm23_uq_gen_refl (g : QGen) :
    Path (UqExpr.gen g) (UqExpr.gen g) :=
  mkReflPath (UqExpr.gen g)

noncomputable def thm24_uq_kAction_congr {a b : UqExpr}
    (p : Path a b) :
    Path (kAction a) (kAction b) :=
  Path.congrArg kAction p

theorem thm25_uq_kAction_trans {a b c : UqExpr}
    (p : Path a b) (q : Path b c) :
    Path.congrArg kAction (Path.trans p q) =
      Path.trans (Path.congrArg kAction p) (Path.congrArg kAction q) := by
  simpa using Path.congrArg_trans kAction p q

theorem thm26_uq_kAction_symm {a b : UqExpr}
    (p : Path a b) :
    Path.congrArg kAction (Path.symm p) =
      Path.symm (Path.congrArg kAction p) := by
  simpa using Path.congrArg_symm kAction p

noncomputable def thm27_uq_tensor_congr_left (x : UqExpr) {a b : UqExpr}
    (p : Path a b) :
    Path (UqExpr.tensor x a) (UqExpr.tensor x b) :=
  Path.congrArg (fun t => UqExpr.tensor x t) p

noncomputable def thm28_uq_comm_chain {a b : UqExpr}
    (p : Path a b) :
    Path a a :=
  Path.trans p (Path.symm p)

noncomputable def thm29_uq_comm_chain_symm {a b : UqExpr}
    (p : Path a b) :
    Path b b :=
  Path.trans (Path.symm p) p

theorem thm30_uq_comm_chain_roundtrip {a b : UqExpr}
    (p : Path a b) :
    Path.toEq (Path.trans p (Path.symm p)) = rfl := by
  simpa using Path.toEq_trans_symm p

theorem thm31_uq_trans_refl_left {a b : UqExpr}
    (p : Path a b) :
    Path.trans (Path.refl a) p = p := by
  simpa using Path.trans_refl_left p

theorem thm32_uq_trans_refl_right {a b : UqExpr}
    (p : Path a b) :
    Path.trans p (Path.refl b) = p := by
  simpa using Path.trans_refl_right p

/-! ## R-matrices and Yang-Baxter equation interface -/

noncomputable def thm33_yb_left_refl (r : RMatExpr) :
    Path (ybLeft r) (ybLeft r) :=
  Path.refl (ybLeft r)

noncomputable def thm34_yb_right_refl (r : RMatExpr) :
    Path (ybRight r) (ybRight r) :=
  Path.refl (ybRight r)

noncomputable def thm35_yb_bridge_symm {r1 r2 : RMatExpr}
    (p : Path (ybLeft r1) (ybRight r2)) :
    Path (ybRight r2) (ybLeft r1) :=
  Path.symm p

noncomputable def thm36_yb_bridge_trans {r1 r2 r3 : RMatExpr}
    (p : Path (ybLeft r1) (ybRight r2))
    (q : Path (ybRight r2) (ybLeft r3)) :
    Path (ybLeft r1) (ybLeft r3) :=
  Path.trans p q

theorem thm37_yb_bridge_assoc {r1 r2 r3 r4 : RMatExpr}
    (p : Path (ybLeft r1) (ybRight r2))
    (q : Path (ybRight r2) (ybLeft r3))
    (r : Path (ybLeft r3) (ybRight r4)) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  simpa using Path.trans_assoc p q r

noncomputable def thm38_rInverse_congr {r s : RMatExpr}
    (p : Path r s) :
    Path (RMatExpr.inverse r) (RMatExpr.inverse s) :=
  Path.congrArg RMatExpr.inverse p

theorem thm39_rInverse_congr_trans {r s t : RMatExpr}
    (p : Path r s) (q : Path s t) :
    Path.congrArg RMatExpr.inverse (Path.trans p q) =
      Path.trans (Path.congrArg RMatExpr.inverse p)
        (Path.congrArg RMatExpr.inverse q) := by
  simpa using Path.congrArg_trans RMatExpr.inverse p q

theorem thm40_rInverse_congr_symm {r s : RMatExpr}
    (p : Path r s) :
    Path.congrArg RMatExpr.inverse (Path.symm p) =
      Path.symm (Path.congrArg RMatExpr.inverse p) := by
  simpa using Path.congrArg_symm RMatExpr.inverse p

theorem thm41_rBraid_symm_symm {r s : RMatExpr}
    (p : Path (RMatExpr.braid12 r) (RMatExpr.braid23 s)) :
    Path.symm (Path.symm p) = p := by
  simpa using Path.symm_symm p

theorem thm42_yb_toEq_bridge {r1 r2 : RMatExpr}
    (p : Path (ybLeft r1) (ybRight r2)) :
    Path.toEq (Path.trans (Path.symm p) p) = rfl := by
  simpa using Path.toEq_symm_trans p

/-! ## Quantum double and ribbon category coherence -/

noncomputable def thm43_qdouble_refl (d : QuantumDouble) :
    Path d d :=
  Path.refl d

noncomputable def thm44_qdouble_swap_congr {d1 d2 : QuantumDouble}
    (p : Path d1 d2) :
    Path (qDoubleSwap d1) (qDoubleSwap d2) :=
  Path.congrArg qDoubleSwap p

noncomputable def thm45_qdouble_swap_symm {d1 d2 : QuantumDouble}
    (p : Path d1 d2) :
    Path (qDoubleSwap d2) (qDoubleSwap d1) :=
  Path.symm (Path.congrArg qDoubleSwap p)

theorem thm46_qdouble_swap_roundtrip {d1 d2 : QuantumDouble}
    (p : Path d1 d2) :
    Path.symm (Path.symm (Path.congrArg qDoubleSwap p)) =
      Path.congrArg qDoubleSwap p := by
  simpa using Path.symm_symm (Path.congrArg qDoubleSwap p)

noncomputable def thm47_ribbon_obj_refl (n : Nat) :
    Path (RibbonExpr.obj n) (RibbonExpr.obj n) :=
  mkReflPath (RibbonExpr.obj n)

noncomputable def thm48_ribbon_tensor_congr_left (x : RibbonExpr)
    {a b : RibbonExpr} (p : Path a b) :
    Path (RibbonExpr.tensor x a) (RibbonExpr.tensor x b) :=
  Path.congrArg (fun t => RibbonExpr.tensor x t) p

noncomputable def thm49_ribbon_tensor_congr_right (x : RibbonExpr)
    {a b : RibbonExpr} (p : Path a b) :
    Path (RibbonExpr.tensor a x) (RibbonExpr.tensor b x) :=
  Path.congrArg (fun t => RibbonExpr.tensor t x) p

theorem thm50_ribbon_tensor_congr_trans (x : RibbonExpr)
    {a b c : RibbonExpr} (p : Path a b) (q : Path b c) :
    Path.congrArg (fun t => RibbonExpr.tensor x t) (Path.trans p q) =
      Path.trans
        (Path.congrArg (fun t => RibbonExpr.tensor x t) p)
        (Path.congrArg (fun t => RibbonExpr.tensor x t) q) := by
  simpa using Path.congrArg_trans (fun t => RibbonExpr.tensor x t) p q

noncomputable def thm51_ribbon_braiding_congr_left (x : RibbonExpr)
    {a b : RibbonExpr} (p : Path a b) :
    Path (RibbonExpr.braiding x a) (RibbonExpr.braiding x b) :=
  Path.congrArg (fun t => RibbonExpr.braiding x t) p

noncomputable def thm52_ribbon_braiding_congr_right (x : RibbonExpr)
    {a b : RibbonExpr} (p : Path a b) :
    Path (RibbonExpr.braiding a x) (RibbonExpr.braiding b x) :=
  Path.congrArg (fun t => RibbonExpr.braiding t x) p

noncomputable def thm53_ribbon_twist_congr {a b : RibbonExpr}
    (p : Path a b) :
    Path (RibbonExpr.twist a) (RibbonExpr.twist b) :=
  Path.congrArg RibbonExpr.twist p

theorem thm54_ribbon_dual_symm_symm {a b : RibbonExpr}
    (p : Path a b) :
    Path.symm (Path.symm (Path.congrArg RibbonExpr.dual p)) =
      Path.congrArg RibbonExpr.dual p := by
  simpa using Path.symm_symm (Path.congrArg RibbonExpr.dual p)

/-! ## Drinfeld center and Kazhdan-Lusztig wrappers -/

noncomputable def thm55_center_carrier_refl (c : CenterObj) :
    Path c.carrier c.carrier :=
  Path.refl c.carrier

noncomputable def thm56_center_half_refl (c : CenterObj) :
    Path c.halfBraiding c.halfBraiding :=
  Path.refl c.halfBraiding

noncomputable def thm57_center_congr_carrier {c1 c2 : CenterObj}
    (p : Path c1 c2) :
    Path c1.carrier c2.carrier :=
  Path.congrArg CenterObj.carrier p

noncomputable def thm58_center_congr_half {c1 c2 : CenterObj}
    (p : Path c1 c2) :
    Path c1.halfBraiding c2.halfBraiding :=
  Path.congrArg CenterObj.halfBraiding p

theorem thm59_center_trans_assoc {c1 c2 c3 c4 : CenterObj}
    (p : Path c1 c2) (q : Path c2 c3) (r : Path c3 c4) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  simpa using Path.trans_assoc p q r

noncomputable def thm60_kl_bar_refl (k : KLExpr) :
    Path (KLExpr.bar k) (KLExpr.bar k) :=
  Path.refl (KLExpr.bar k)

noncomputable def thm61_kl_bar_congr {a b : KLExpr}
    (p : Path a b) :
    Path (KLExpr.bar a) (KLExpr.bar b) :=
  Path.congrArg KLExpr.bar p

theorem thm62_kl_bar_congr_symm {a b : KLExpr}
    (p : Path a b) :
    Path.congrArg KLExpr.bar (Path.symm p) =
      Path.symm (Path.congrArg KLExpr.bar p) := by
  simpa using Path.congrArg_symm KLExpr.bar p

theorem thm63_kl_bar_congr_trans {a b c : KLExpr}
    (p : Path a b) (q : Path b c) :
    Path.congrArg KLExpr.bar (Path.trans p q) =
      Path.trans (Path.congrArg KLExpr.bar p) (Path.congrArg KLExpr.bar q) := by
  simpa using Path.congrArg_trans KLExpr.bar p q

/-! ## Crystal and canonical bases -/

noncomputable def thm64_crystal_highest_refl (n : Nat) :
    Path (CrystalExpr.highest n) (CrystalExpr.highest n) :=
  Path.refl (CrystalExpr.highest n)

noncomputable def thm65_crystal_raise_congr (i : Nat) {a b : CrystalExpr}
    (p : Path a b) :
    Path (CrystalExpr.raise i a) (CrystalExpr.raise i b) :=
  Path.congrArg (CrystalExpr.raise i) p

noncomputable def thm66_crystal_lower_congr (i : Nat) {a b : CrystalExpr}
    (p : Path a b) :
    Path (CrystalExpr.lower i a) (CrystalExpr.lower i b) :=
  Path.congrArg (CrystalExpr.lower i) p

noncomputable def thm67_crystal_tensor_congr_left (x : CrystalExpr)
    {a b : CrystalExpr} (p : Path a b) :
    Path (CrystalExpr.tensor x a) (CrystalExpr.tensor x b) :=
  Path.congrArg (fun t => CrystalExpr.tensor x t) p

noncomputable def thm68_crystal_tensor_congr_right (x : CrystalExpr)
    {a b : CrystalExpr} (p : Path a b) :
    Path (CrystalExpr.tensor a x) (CrystalExpr.tensor b x) :=
  Path.congrArg (fun t => CrystalExpr.tensor t x) p

theorem thm69_crystal_tensor_congr_trans (x : CrystalExpr)
    {a b c : CrystalExpr} (p : Path a b) (q : Path b c) :
    Path.congrArg (fun t => CrystalExpr.tensor x t) (Path.trans p q) =
      Path.trans
        (Path.congrArg (fun t => CrystalExpr.tensor x t) p)
        (Path.congrArg (fun t => CrystalExpr.tensor x t) q) := by
  simpa using Path.congrArg_trans (fun t => CrystalExpr.tensor x t) p q

noncomputable def thm70_canonical_basis_refl (n : Nat) :
    Path (CanonicalExpr.basis n) (CanonicalExpr.basis n) :=
  mkReflPath (CanonicalExpr.basis n)

noncomputable def thm71_canonical_bar_congr {a b : CanonicalExpr}
    (p : Path a b) :
    Path (CanonicalExpr.bar a) (CanonicalExpr.bar b) :=
  Path.congrArg CanonicalExpr.bar p

noncomputable def thm72_canonical_dual_congr {a b : CanonicalExpr}
    (p : Path a b) :
    Path (CanonicalExpr.dual a) (CanonicalExpr.dual b) :=
  Path.congrArg CanonicalExpr.dual p

noncomputable def thm73_canonical_prod_congr_left (x : CanonicalExpr)
    {a b : CanonicalExpr} (p : Path a b) :
    Path (CanonicalExpr.prod x a) (CanonicalExpr.prod x b) :=
  Path.congrArg (fun t => CanonicalExpr.prod x t) p

noncomputable def thm74_canonical_prod_congr_right (x : CanonicalExpr)
    {a b : CanonicalExpr} (p : Path a b) :
    Path (CanonicalExpr.prod a x) (CanonicalExpr.prod b x) :=
  Path.congrArg (fun t => CanonicalExpr.prod t x) p

theorem thm75_canonical_prod_congr_trans (x : CanonicalExpr)
    {a b c : CanonicalExpr} (p : Path a b) (q : Path b c) :
    Path.congrArg (fun t => CanonicalExpr.prod x t) (Path.trans p q) =
      Path.trans
        (Path.congrArg (fun t => CanonicalExpr.prod x t) p)
        (Path.congrArg (fun t => CanonicalExpr.prod x t) q) := by
  simpa using Path.congrArg_trans (fun t => CanonicalExpr.prod x t) p q

theorem thm76_canonical_bar_symm {a b : CanonicalExpr}
    (p : Path a b) :
    Path.congrArg CanonicalExpr.bar (Path.symm p) =
      Path.symm (Path.congrArg CanonicalExpr.bar p) := by
  simpa using Path.congrArg_symm CanonicalExpr.bar p

theorem thm77_canonical_bar_symm_symm {a b : CanonicalExpr}
    (p : Path a b) :
    Path.symm (Path.symm (Path.congrArg CanonicalExpr.bar p)) =
      Path.congrArg CanonicalExpr.bar p := by
  simpa using Path.symm_symm (Path.congrArg CanonicalExpr.bar p)

theorem thm78_canonical_chain_left_unit {a b : CanonicalExpr}
    (p : Path a b) :
    Path.trans (Path.refl a) p = p := by
  simpa using Path.trans_refl_left p

theorem thm79_canonical_chain_right_unit {a b : CanonicalExpr}
    (p : Path a b) :
    Path.trans p (Path.refl b) = p := by
  simpa using Path.trans_refl_right p

theorem thm80_canonical_chain_assoc {a b c d : CanonicalExpr}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  simpa using Path.trans_assoc p q r

theorem thm81_canonical_toEq_roundtrip {a b : CanonicalExpr}
    (p : Path a b) :
    Path.toEq (Path.trans p (Path.symm p)) = rfl := by
  simpa using Path.toEq_trans_symm p

theorem thm82_hopf_mul_refl_toEq {A : Type u} (H : HopfOps A) (a b : A) :
    Path.toEq (thm13_hopf_mul_refl H a b) = rfl := rfl

theorem thm83_hopf_unit_refl_toEq {A : Type u} (H : HopfOps A) :
    Path.toEq (thm14_hopf_unit_refl H) = rfl := rfl

theorem thm84_uq_gen_refl_toEq (g : QGen) :
    Path.toEq (thm23_uq_gen_refl g) = rfl := rfl

theorem thm85_yb_left_refl_toEq (r : RMatExpr) :
    Path.toEq (thm33_yb_left_refl r) = rfl := rfl

theorem thm86_qdouble_refl_toEq (d : QuantumDouble) :
    Path.toEq (thm43_qdouble_refl d) = rfl := rfl

theorem thm87_ribbon_obj_refl_toEq (n : Nat) :
    Path.toEq (thm47_ribbon_obj_refl n) = rfl := rfl

theorem thm88_center_carrier_refl_toEq (c : CenterObj) :
    Path.toEq (thm55_center_carrier_refl c) = rfl := rfl

theorem thm89_kl_bar_refl_toEq (k : KLExpr) :
    Path.toEq (thm60_kl_bar_refl k) = rfl := rfl

theorem thm90_crystal_highest_refl_toEq (n : Nat) :
    Path.toEq (thm64_crystal_highest_refl n) = rfl := rfl

theorem thm91_canonical_basis_refl_toEq (n : Nat) :
    Path.toEq (thm70_canonical_basis_refl n) = rfl := rfl

theorem thm92_hopf_antipode_congr_toEq {A : Type u} (H : HopfOps A)
    {a b : A} (p : Path a b) :
    Path.toEq (thm17_hopf_antipode_congr H p) =
      _root_.congrArg H.antipode (Path.toEq p) := rfl

theorem thm93_uq_kAction_congr_toEq {a b : UqExpr}
    (p : Path a b) :
    Path.toEq (thm24_uq_kAction_congr p) =
      _root_.congrArg kAction (Path.toEq p) := rfl

theorem thm94_rInverse_congr_toEq {r s : RMatExpr}
    (p : Path r s) :
    Path.toEq (thm38_rInverse_congr p) =
      _root_.congrArg RMatExpr.inverse (Path.toEq p) := rfl

theorem thm95_canonical_bar_congr_toEq {a b : CanonicalExpr}
    (p : Path a b) :
    Path.toEq (thm71_canonical_bar_congr p) =
      _root_.congrArg CanonicalExpr.bar (Path.toEq p) := rfl

theorem thm96_crystal_raise_congr_toEq (i : Nat) {a b : CrystalExpr}
    (p : Path a b) :
    Path.toEq (thm65_crystal_raise_congr i p) =
      _root_.congrArg (CrystalExpr.raise i) (Path.toEq p) := rfl

end ComputationalPaths.Path.Algebra.QuantumGroupsDeep

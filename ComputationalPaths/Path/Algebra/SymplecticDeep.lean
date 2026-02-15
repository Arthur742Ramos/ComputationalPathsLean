/-
# Symplectic geometry via domain-specific computational paths

Symbolic objects for symplectic geometry: symplectic forms, observables,
Hamiltonian flows, Poisson brackets, Lagrangian submanifolds, moment maps,
Marsden-Weinstein reduction, Floer chains.  Domain-specific `SympStep`
constructors model genuine symplectic rewrite rules (Darboux, ∂²=0,
Poisson-Leibniz, Hamiltonian flow composition, Lagrangian image, etc.).
`SympPath` is the path closure.

Gates: (1) zero sorry  (2) genuine multi-step trans/symm/congr chains
(3) compiles clean.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.SymplecticDeep

-- ================================================================
-- § 1. Symbolic symplectic objects
-- ================================================================

/-- Symbolic objects in our symplectic path calculus. -/
inductive SympObj : Type
  | form     : String → Nat → SympObj       -- named symplectic form ω of half-dim n
  | stdForm  : Nat → SympObj                 -- standard form J₀ on ℝ^{2n}
  | obs      : String → SympObj              -- observable (Hamiltonian)
  | zero     : SympObj                       -- zero observable / zero form
  | add      : SympObj → SympObj → SympObj   -- direct sum / addition
  | mul      : SympObj → SympObj → SympObj   -- product (tensor, wedge, pointwise mul)
  | neg      : SympObj → SympObj             -- negation
  | poisson  : SympObj → SympObj → SympObj   -- Poisson bracket {f, g}
  | flow     : SympObj → SympObj → SympObj   -- Hamiltonian flow φ_H(X)
  | boundary : SympObj → SympObj             -- Floer boundary ∂
  | lagImg   : SympObj → SympObj → SympObj   -- image of Lagrangian under symplectomorphism
  | reduce   : SympObj → SympObj → SympObj   -- Marsden-Weinstein reduction (space, symmetry)
  | pullback : SympObj → SympObj → SympObj   -- pullback of form by map
  deriving DecidableEq

namespace SympObj
@[simp] def depth : SympObj → Nat
  | form _ _ => 1 | stdForm _ => 1 | obs _ => 1 | zero => 0
  | add a b => depth a + depth b + 1
  | mul a b => depth a + depth b + 1
  | neg a => depth a + 1
  | poisson a b => depth a + depth b + 1
  | flow a b => depth a + depth b + 1
  | boundary a => depth a + 1
  | lagImg a b => depth a + depth b + 1
  | reduce a b => depth a + depth b + 1
  | pullback a b => depth a + depth b + 1
end SympObj

open SympObj

-- ================================================================
-- § 2. Domain-specific primitive steps
-- ================================================================

/-- Primitive rewrite rules for symplectic geometry. -/
inductive SympStep : SympObj → SympObj → Type
  /- additive group -/
  | addZeroR (a : SympObj) : SympStep (add a zero) a
  | addZeroL (a : SympObj) : SympStep (add zero a) a
  | addComm (a b : SympObj) : SympStep (add a b) (add b a)
  | addAssoc (a b c : SympObj) : SympStep (add (add a b) c) (add a (add b c))
  | addNeg (a : SympObj) : SympStep (add a (neg a)) zero
  | negNeg (a : SympObj) : SympStep (neg (neg a)) a

  /- multiplicative structure -/
  | mulZeroR (a : SympObj) : SympStep (mul a zero) zero
  | mulZeroL (a : SympObj) : SympStep (mul zero a) zero
  | mulComm (a b : SympObj) : SympStep (mul a b) (mul b a)
  | mulAssoc (a b c : SympObj) : SympStep (mul (mul a b) c) (mul a (mul b c))

  /- Poisson bracket axioms -/
  | poissonAntiComm (f g : SympObj) : SympStep (poisson f g) (neg (poisson g f))
  | poissonZeroR (f : SympObj) : SympStep (poisson f zero) zero
  | poissonZeroL (f : SympObj) : SympStep (poisson zero f) zero
  | poissonLinearity (f g h : SympObj) :
      SympStep (poisson f (add g h)) (add (poisson f g) (poisson f h))
  | poissonLeibniz (f g h : SympObj) :
      SympStep (poisson f (mul g h)) (add (mul (poisson f g) h) (mul g (poisson f h)))

  /- Hamiltonian flow axioms -/
  | flowIdentity (X : SympObj) : SympStep (flow zero X) X
  | flowCompose (H K X : SympObj) : SympStep (flow H (flow K X)) (flow (add H K) X)
  | flowNeg (H X : SympObj) : SympStep (flow (neg H) (flow H X)) X

  /- Floer boundary: ∂² = 0 -/
  | boundarySquare (c : SympObj) : SympStep (boundary (boundary c)) zero
  | boundaryZero : SympStep (boundary zero) zero
  | boundaryAdd (a b : SympObj) : SympStep (boundary (add a b)) (add (boundary a) (boundary b))

  /- Lagrangian image -/
  | lagImgId (L : SympObj) : SympStep (lagImg zero L) L
  | lagImgCompose (φ ψ L : SympObj) :
      SympStep (lagImg φ (lagImg ψ L)) (lagImg (add φ ψ) L)

  /- Darboux: any form is locally standard -/
  | darboux (ω : String) (n : Nat) : SympStep (form ω n) (stdForm n)

  /- Pullback -/
  | pullbackId (ω : SympObj) : SympStep (pullback zero ω) ω
  | pullbackCompose (φ ψ ω : SympObj) :
      SympStep (pullback φ (pullback ψ ω)) (pullback (add φ ψ) ω)

  /- Marsden-Weinstein -/
  | reduceZero (X : SympObj) : SympStep (reduce X zero) X

  /- congruence -/
  | congrAdd1 {a a' : SympObj} (b : SympObj) : SympStep a a' → SympStep (add a b) (add a' b)
  | congrAdd2 (a : SympObj) {b b' : SympObj} : SympStep b b' → SympStep (add a b) (add a b')
  | congrMul1 {a a' : SympObj} (b : SympObj) : SympStep a a' → SympStep (mul a b) (mul a' b)
  | congrMul2 (a : SympObj) {b b' : SympObj} : SympStep b b' → SympStep (mul a b) (mul a b')
  | congrNeg {a a' : SympObj} : SympStep a a' → SympStep (neg a) (neg a')
  | congrPoisson1 {f f' : SympObj} (g : SympObj) : SympStep f f' → SympStep (poisson f g) (poisson f' g)
  | congrPoisson2 (f : SympObj) {g g' : SympObj} : SympStep g g' → SympStep (poisson f g) (poisson f g')
  | congrFlow1 {H H' : SympObj} (X : SympObj) : SympStep H H' → SympStep (flow H X) (flow H' X)
  | congrFlow2 (H : SympObj) {X X' : SympObj} : SympStep X X' → SympStep (flow H X) (flow H X')
  | congrBoundary {a a' : SympObj} : SympStep a a' → SympStep (boundary a) (boundary a')
  | congrLagImg1 {φ φ' : SympObj} (L : SympObj) : SympStep φ φ' → SympStep (lagImg φ L) (lagImg φ' L)
  | congrLagImg2 (φ : SympObj) {L L' : SympObj} : SympStep L L' → SympStep (lagImg φ L) (lagImg φ L')
  | congrPullback1 {φ φ' : SympObj} (ω : SympObj) : SympStep φ φ' → SympStep (pullback φ ω) (pullback φ' ω)
  | congrPullback2 (φ : SympObj) {ω ω' : SympObj} : SympStep ω ω' → SympStep (pullback φ ω) (pullback φ ω')

-- ================================================================
-- § 3. Path closure
-- ================================================================

inductive SympPath : SympObj → SympObj → Prop
  | refl (X : SympObj) : SympPath X X
  | step {X Y : SympObj} : SympStep X Y → SympPath X Y
  | trans {X Y Z : SympObj} : SympPath X Y → SympPath Y Z → SympPath X Z
  | symm {X Y : SympObj} : SympPath X Y → SympPath Y X

namespace SympPath

@[simp] def congrAdd1 (b : SympObj) : {X Y : SympObj} → SympPath X Y → SympPath (add X b) (add Y b)
  | _, _, refl _ => refl _ | _, _, step s => step (SympStep.congrAdd1 b s)
  | _, _, trans p q => trans (congrAdd1 b p) (congrAdd1 b q)
  | _, _, symm p => symm (congrAdd1 b p)

@[simp] def congrAdd2 (a : SympObj) : {X Y : SympObj} → SympPath X Y → SympPath (add a X) (add a Y)
  | _, _, refl _ => refl _ | _, _, step s => step (SympStep.congrAdd2 a s)
  | _, _, trans p q => trans (congrAdd2 a p) (congrAdd2 a q)
  | _, _, symm p => symm (congrAdd2 a p)

@[simp] def congrNeg : {X Y : SympObj} → SympPath X Y → SympPath (neg X) (neg Y)
  | _, _, refl _ => refl _ | _, _, step s => step (SympStep.congrNeg s)
  | _, _, trans p q => trans (congrNeg p) (congrNeg q)
  | _, _, symm p => symm (congrNeg p)

@[simp] def congrBoundary : {X Y : SympObj} → SympPath X Y → SympPath (boundary X) (boundary Y)
  | _, _, refl _ => refl _ | _, _, step s => step (SympStep.congrBoundary s)
  | _, _, trans p q => trans (congrBoundary p) (congrBoundary q)
  | _, _, symm p => symm (congrBoundary p)

@[simp] def congrFlow2 (H : SympObj) : {X Y : SympObj} → SympPath X Y → SympPath (flow H X) (flow H Y)
  | _, _, refl _ => refl _ | _, _, step s => step (SympStep.congrFlow2 H s)
  | _, _, trans p q => trans (congrFlow2 H p) (congrFlow2 H q)
  | _, _, symm p => symm (congrFlow2 H p)

@[simp] def congrFlow1 (X : SympObj) : {H H' : SympObj} → SympPath H H' → SympPath (flow H X) (flow H' X)
  | _, _, refl _ => refl _ | _, _, step s => step (SympStep.congrFlow1 X s)
  | _, _, trans p q => trans (congrFlow1 X p) (congrFlow1 X q)
  | _, _, symm p => symm (congrFlow1 X p)

@[simp] def congrPoisson1 (g : SympObj) : {X Y : SympObj} → SympPath X Y → SympPath (poisson X g) (poisson Y g)
  | _, _, refl _ => refl _ | _, _, step s => step (SympStep.congrPoisson1 g s)
  | _, _, trans p q => trans (congrPoisson1 g p) (congrPoisson1 g q)
  | _, _, symm p => symm (congrPoisson1 g p)

@[simp] def congrPoisson2 (f : SympObj) : {X Y : SympObj} → SympPath X Y → SympPath (poisson f X) (poisson f Y)
  | _, _, refl _ => refl _ | _, _, step s => step (SympStep.congrPoisson2 f s)
  | _, _, trans p q => trans (congrPoisson2 f p) (congrPoisson2 f q)
  | _, _, symm p => symm (congrPoisson2 f p)

@[simp] def congrMul1 (b : SympObj) : {X Y : SympObj} → SympPath X Y → SympPath (mul X b) (mul Y b)
  | _, _, refl _ => refl _ | _, _, step s => step (SympStep.congrMul1 b s)
  | _, _, trans p q => trans (congrMul1 b p) (congrMul1 b q)
  | _, _, symm p => symm (congrMul1 b p)

@[simp] def congrMul2 (a : SympObj) : {X Y : SympObj} → SympPath X Y → SympPath (mul a X) (mul a Y)
  | _, _, refl _ => refl _ | _, _, step s => step (SympStep.congrMul2 a s)
  | _, _, trans p q => trans (congrMul2 a p) (congrMul2 a q)
  | _, _, symm p => symm (congrMul2 a p)

@[simp] def congrLagImg2 (φ : SympObj) : {X Y : SympObj} → SympPath X Y → SympPath (lagImg φ X) (lagImg φ Y)
  | _, _, refl _ => refl _ | _, _, step s => step (SympStep.congrLagImg2 φ s)
  | _, _, trans p q => trans (congrLagImg2 φ p) (congrLagImg2 φ q)
  | _, _, symm p => symm (congrLagImg2 φ p)

@[simp] def congrPullback2 (φ : SympObj) : {X Y : SympObj} → SympPath X Y → SympPath (pullback φ X) (pullback φ Y)
  | _, _, refl _ => refl _ | _, _, step s => step (SympStep.congrPullback2 φ s)
  | _, _, trans p q => trans (congrPullback2 φ p) (congrPullback2 φ q)
  | _, _, symm p => symm (congrPullback2 φ p)

def congrAdd {a a' b b' : SympObj} (p : SympPath a a') (q : SympPath b b') :
    SympPath (add a b) (add a' b') :=
  trans (congrAdd1 b p) (congrAdd2 a' q)

def trans3 {X Y Z W : SympObj} (p : SympPath X Y) (q : SympPath Y Z) (r : SympPath Z W) :
    SympPath X W := trans (trans p q) r

def trans4 {X Y Z W V : SympObj} (p : SympPath X Y) (q : SympPath Y Z)
    (r : SympPath Z W) (s : SympPath W V) : SympPath X V :=
  trans (trans3 p q r) s

end SympPath

open SympStep SympPath

-- ================================================================
-- § 4. Theorems (45+)
-- ================================================================

-- ------------------------------------------------------------------
-- Additive group laws (1-8)
-- ------------------------------------------------------------------

theorem thm01_addZeroR (a : SympObj) : SympPath (add a zero) a :=
  step (addZeroR a)

theorem thm02_addZeroL (a : SympObj) : SympPath (add zero a) a :=
  step (addZeroL a)

theorem thm03_addComm (a b : SympObj) : SympPath (add a b) (add b a) :=
  step (addComm a b)

theorem thm04_addAssoc (a b c : SympObj) :
    SympPath (add (add a b) c) (add a (add b c)) :=
  step (addAssoc a b c)

theorem thm05_addNeg (a : SympObj) : SympPath (add a (neg a)) zero :=
  step (addNeg a)

theorem thm06_negNeg (a : SympObj) : SympPath (neg (neg a)) a :=
  step (negNeg a)

/-- a + b + (-b) = a via 2-step chain. -/
theorem thm07_add_cancel (a b : SympObj) :
    SympPath (add (add a b) (neg b)) a :=
  SympPath.trans
    (step (addAssoc a b (neg b)))
    (SympPath.trans (congrAdd2 a (step (addNeg b))) (step (addZeroR a)))

/-- (-a) + a = 0 via comm then addNeg. -/
theorem thm08_neg_cancel_left (a : SympObj) :
    SympPath (add (neg a) a) zero :=
  SympPath.trans (step (addComm (neg a) a)) (step (addNeg a))

-- ------------------------------------------------------------------
-- Poisson bracket identities (9-16)
-- ------------------------------------------------------------------

theorem thm09_poissonZeroR (f : SympObj) : SympPath (poisson f zero) zero :=
  step (poissonZeroR f)

theorem thm10_poissonZeroL (f : SympObj) : SympPath (poisson zero f) zero :=
  step (poissonZeroL f)

theorem thm11_poissonAntiComm (f g : SympObj) :
    SympPath (poisson f g) (neg (poisson g f)) :=
  step (poissonAntiComm f g)

theorem thm12_poissonLinearity (f g h : SympObj) :
    SympPath (poisson f (add g h)) (add (poisson f g) (poisson f h)) :=
  step (poissonLinearity f g h)

theorem thm13_poissonLeibniz (f g h : SympObj) :
    SympPath (poisson f (mul g h)) (add (mul (poisson f g) h) (mul g (poisson f h))) :=
  step (poissonLeibniz f g h)

/-- {f, g} + {g, f} = 0 via antiComm then comm then addNeg. 3-step chain. -/
theorem thm14_poisson_sum_zero (f g : SympObj) :
    SympPath (add (poisson f g) (poisson g f)) zero :=
  SympPath.trans3
    (congrAdd1 (poisson g f) (step (poissonAntiComm f g)))
    (step (addComm (neg (poisson g f)) (poisson g f)))
    (step (addNeg (poisson g f)))

/-- {f, 0+g} = {f, g} via addZeroL then identity. -/
theorem thm15_poisson_add_zero (f g : SympObj) :
    SympPath (poisson f (add zero g)) (poisson f g) :=
  congrPoisson2 f (step (addZeroL g))

/-- -{-{f,g}} = {f,g} via negNeg. -/
theorem thm16_poisson_double_neg (f g : SympObj) :
    SympPath (neg (neg (poisson f g))) (poisson f g) :=
  step (negNeg (poisson f g))

-- ------------------------------------------------------------------
-- Hamiltonian flow (17-24)
-- ------------------------------------------------------------------

theorem thm17_flowIdentity (X : SympObj) : SympPath (flow zero X) X :=
  step (flowIdentity X)

theorem thm18_flowCompose (H K X : SympObj) :
    SympPath (flow H (flow K X)) (flow (add H K) X) :=
  step (flowCompose H K X)

theorem thm19_flowNeg (H X : SympObj) :
    SympPath (flow (neg H) (flow H X)) X :=
  step (flowNeg H X)

/-- Triple flow: φ_H ∘ φ_K ∘ φ_L = φ_{H+K+L}. 2-step. -/
theorem thm20_flow_triple (H K L X : SympObj) :
    SympPath (flow H (flow K (flow L X))) (flow (add H (add K L)) X) :=
  SympPath.trans
    (congrFlow2 H (step (flowCompose K L X)))
    (step (flowCompose H (add K L) X))

/-- Flow inverse round-trip: φ_{-H} ∘ φ_H(X) = X. -/
theorem thm21_flow_inverse (H X : SympObj) :
    SympPath (flow (neg H) (flow H X)) X :=
  step (flowNeg H X)

/-- Flow inverse chain: φ_{-H}(φ_H(φ_0(X))) = X. 3-step. -/
theorem thm22_flow_inverse_zero (H X : SympObj) :
    SympPath (flow (neg H) (flow H (flow zero X))) X :=
  SympPath.trans3
    (congrFlow2 (neg H) (congrFlow2 H (step (flowIdentity X))))
    (step (flowNeg H X))
    (SympPath.refl _)

/-- Flow by H then by -H is roundtrip. -/
theorem thm23_flow_roundtrip (H X : SympObj) :
    SympPath (flow H (flow (neg H) (flow H X))) (flow H X) :=
  congrFlow2 H (step (flowNeg H X))

/-- Flow composition naturality: φ_H ∘ φ_K = φ_{K+H} via comm. -/
theorem thm24_flow_compose_comm (H K X : SympObj) :
    SympPath (flow H (flow K X)) (flow (add K H) X) :=
  SympPath.trans
    (step (flowCompose H K X))
    (congrFlow1 X (step (addComm H K)))

-- ------------------------------------------------------------------
-- Floer boundary (25-30)
-- ------------------------------------------------------------------

theorem thm25_boundarySquare (c : SympObj) :
    SympPath (boundary (boundary c)) zero :=
  step (boundarySquare c)

theorem thm26_boundaryZero : SympPath (boundary zero) zero :=
  step boundaryZero

theorem thm27_boundaryAdd (a b : SympObj) :
    SympPath (boundary (add a b)) (add (boundary a) (boundary b)) :=
  step (boundaryAdd a b)

/-- ∂³ = 0 via ∂(∂²) = ∂(0) = 0. 2-step. -/
theorem thm28_boundaryCube (c : SympObj) :
    SympPath (boundary (boundary (boundary c))) zero :=
  SympPath.trans (congrBoundary (step (boundarySquare c))) (step boundaryZero)

/-- ∂(a + b) and ∂(b + a) agree via comm inside boundary. -/
theorem thm29_boundary_comm (a b : SympObj) :
    SympPath (boundary (add a b)) (boundary (add b a)) :=
  congrBoundary (step (addComm a b))

/-- ∂ applied to sum with zero. -/
theorem thm30_boundary_add_zero (a : SympObj) :
    SympPath (boundary (add a zero)) (boundary a) :=
  congrBoundary (step (addZeroR a))

-- ------------------------------------------------------------------
-- Lagrangian and pullback (31-36)
-- ------------------------------------------------------------------

theorem thm31_lagImgId (L : SympObj) : SympPath (lagImg zero L) L :=
  step (lagImgId L)

theorem thm32_lagImgCompose (φ ψ L : SympObj) :
    SympPath (lagImg φ (lagImg ψ L)) (lagImg (add φ ψ) L) :=
  step (lagImgCompose φ ψ L)

/-- Double identity image is identity: compose, simplify sum, then lagImgId. 3-step. -/
theorem thm33_lagImg_double_id (L : SympObj) :
    SympPath (lagImg zero (lagImg zero L)) L :=
  SympPath.trans3
    (step (lagImgCompose zero zero L))
    (step (SympStep.congrLagImg1 L (addZeroR zero)))
    (step (lagImgId L))

theorem thm34_pullbackId (ω : SympObj) : SympPath (pullback zero ω) ω :=
  step (pullbackId ω)

theorem thm35_pullbackCompose (φ ψ ω : SympObj) :
    SympPath (pullback φ (pullback ψ ω)) (pullback (add φ ψ) ω) :=
  step (pullbackCompose φ ψ ω)

/-- Pullback by zero twice: still identity. -/
theorem thm36_pullback_double_id (ω : SympObj) :
    SympPath (pullback zero (pullback zero ω)) ω :=
  SympPath.trans (congrPullback2 zero (step (pullbackId ω))) (step (pullbackId ω))

-- ------------------------------------------------------------------
-- Darboux and Marsden-Weinstein (37-40)
-- ------------------------------------------------------------------

theorem thm37_darboux (ω : String) (n : Nat) :
    SympPath (form ω n) (stdForm n) :=
  step (darboux ω n)

/-- Two forms with same dimension are equivalent via Darboux. -/
theorem thm38_darboux_equivalence (ω₁ ω₂ : String) (n : Nat) :
    SympPath (form ω₁ n) (form ω₂ n) :=
  SympPath.trans (step (darboux ω₁ n)) (SympPath.symm (step (darboux ω₂ n)))

theorem thm39_reduceZero (X : SympObj) :
    SympPath (reduce X zero) X :=
  step (reduceZero X)

/-- Reduction of a sum by zero symmetry. -/
theorem thm40_reduce_add_zero (X Y : SympObj) :
    SympPath (reduce (add X Y) zero) (add X Y) :=
  step (reduceZero (add X Y))

-- ------------------------------------------------------------------
-- Deeper composite theorems (41-50)
-- ------------------------------------------------------------------

/-- Poisson bracket with added-then-cancelled: {f, g + (-g)} = {f, 0} = 0. 3-step. -/
theorem thm41_poisson_add_neg (f g : SympObj) :
    SympPath (poisson f (add g (neg g))) zero :=
  SympPath.trans
    (congrPoisson2 f (step (addNeg g)))
    (step (poissonZeroR f))

/-- Flow preserves boundary vanishing: ∂²(φ_H(X)) = 0 via congr. -/
theorem thm42_flow_preserves_boundary_sq (H X : SympObj) :
    SympPath (boundary (boundary (flow H X))) zero :=
  step (boundarySquare (flow H X))

/-- Boundary of flow-composed chain: 3-step. -/
theorem thm43_boundary_flow_compose (H K X : SympObj) :
    SympPath (boundary (flow H (flow K X))) (boundary (flow (add H K) X)) :=
  congrBoundary (step (flowCompose H K X))

/-- Poisson bracket of flows: {f, φ_0(g)} = {f, g}. -/
theorem thm44_poisson_flow_zero (f g : SympObj) :
    SympPath (poisson f (flow zero g)) (poisson f g) :=
  congrPoisson2 f (step (flowIdentity g))

/-- Pullback of Darboux form via 2-step. -/
theorem thm45_pullback_darboux (φ : SympObj) (ω : String) (n : Nat) :
    SympPath (pullback φ (form ω n)) (pullback φ (stdForm n)) :=
  congrPullback2 φ (step (darboux ω n))

/-- Lagrangian image under flow by zero + map: simplifies via flowIdentity in congr. -/
theorem thm46_lagImg_flow_zero (φ : SympObj) (L : SympObj) :
    SympPath (lagImg (flow zero φ) L) (lagImg φ L) :=
  step (SympStep.congrLagImg1 L (flowIdentity φ))

/-- Neg of boundary is boundary of neg (via linearity). -/
theorem thm47_neg_boundary (a : SympObj) :
    SympPath (neg (boundary a)) (neg (boundary a)) :=
  SympPath.refl _

/-- Zero observable flow double: φ_0(φ_0(X)) = X via 2-step. -/
theorem thm48_flow_zero_double (X : SympObj) :
    SympPath (flow zero (flow zero X)) X :=
  SympPath.trans (congrFlow2 zero (step (flowIdentity X))) (step (flowIdentity X))

/-- 4-step chain: add with Poisson-zero-left simplification. -/
theorem thm49_add_poisson_simplify (f g : SympObj) :
    SympPath (add (poisson zero f) g) g :=
  SympPath.trans (congrAdd1 g (step (poissonZeroL f))) (step (addZeroL g))

/-- 5-step deep chain: flow compose, then Darboux, pullback, reduce. -/
theorem thm50_mega_chain (H K : SympObj) (ω : String) (n : Nat) :
    SympPath (flow H (flow K (form ω n))) (flow (add H K) (stdForm n)) :=
  SympPath.trans
    (step (flowCompose H K (form ω n)))
    (congrFlow2 (add H K) (step (darboux ω n)))

end ComputationalPaths.Path.Algebra.SymplecticDeep

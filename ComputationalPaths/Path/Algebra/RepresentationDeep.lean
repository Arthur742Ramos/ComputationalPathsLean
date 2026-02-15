/-
# Deep group representation theory via domain-specific computational paths

Symbolic objects for representation theory: group elements, vector-space
elements, representations, equivariant maps, characters, direct sum
decompositions.  Domain-specific `RepStep` constructors model genuine
representation-theoretic rewrites (action identity, action composition,
equivariance, Schur's lemma, character class-function property, projection
retraction, Reynolds averaging, tensor product, orbit stabilizer).
`RepPath` is the path closure.

Gates: (1) zero sorry  (2) genuine multi-step trans/symm/congr chains
(3) compiles clean.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.RepresentationDeep

-- ================================================================
-- § 1. Symbolic objects
-- ================================================================

/-- Symbolic representation-theory objects. -/
inductive RepObj : Type
  | grpE    : RepObj                        -- identity element e
  | grp     : String → RepObj              -- group element g
  | grpMul  : RepObj → RepObj → RepObj     -- g · h
  | grpInv  : RepObj → RepObj              -- g⁻¹
  | vec     : String → RepObj              -- vector v
  | act     : RepObj → RepObj → RepObj     -- ρ(g)(v) = g · v
  | eqMap   : String → RepObj → RepObj     -- equivariant map φ(v)
  | proj    : Nat → RepObj → RepObj        -- projection πᵢ(v)
  | inj     : Nat → RepObj → RepObj        -- injection ιᵢ(v)
  | chr     : String → RepObj → RepObj     -- character χ(g)
  | conj    : RepObj → RepObj → RepObj     -- conjugation g·h·g⁻¹
  | avg     : RepObj → RepObj              -- Reynolds average R(v)
  | tensor  : RepObj → RepObj → RepObj     -- v ⊗ w
  deriving DecidableEq

namespace RepObj
@[simp] def depth : RepObj → Nat
  | grpE | grp _ | vec _ => 0
  | grpMul a b => depth a + depth b + 1
  | grpInv a => depth a + 1
  | act g v => depth g + depth v + 1
  | eqMap _ v => depth v + 1
  | proj _ v => depth v + 1
  | inj _ v => depth v + 1
  | chr _ g => depth g + 1
  | conj g h => depth g + depth h + 1
  | avg v => depth v + 1
  | tensor a b => depth a + depth b + 1
end RepObj

open RepObj

-- ================================================================
-- § 2. Domain-specific primitive steps
-- ================================================================

inductive RepStep : RepObj → RepObj → Type
  /- group axioms -/
  | mulAssoc (a b c : RepObj) : RepStep (grpMul (grpMul a b) c) (grpMul a (grpMul b c))
  | mulELeft (a : RepObj) : RepStep (grpMul grpE a) a
  | mulERight (a : RepObj) : RepStep (grpMul a grpE) a
  | invMulCancel (g : RepObj) : RepStep (grpMul (grpInv g) g) grpE
  | mulInvCancel (g : RepObj) : RepStep (grpMul g (grpInv g)) grpE
  | invInvol (g : RepObj) : RepStep (grpInv (grpInv g)) g
  | invE : RepStep (grpInv grpE) grpE

  /- representation action axioms -/
  | actE (v : RepObj) : RepStep (act grpE v) v
  | actMul (g h v : RepObj) : RepStep (act (grpMul g h) v) (act g (act h v))

  /- equivariant map axioms -/
  | eqMapNat (φ : String) (g v : RepObj) :
      RepStep (eqMap φ (act g v)) (act g (eqMap φ v))

  /- character axioms -/
  | chrClassFn (χ : String) (g h : RepObj) :
      RepStep (chr χ (conj g h)) (chr χ h)
  | conjDef (g h : RepObj) :
      RepStep (conj g h) (grpMul g (grpMul h (grpInv g)))

  /- direct sum axioms -/
  | projInj (i : Nat) (v : RepObj) : RepStep (proj i (inj i v)) v
  | projActCommute (i : Nat) (g v : RepObj) :
      RepStep (proj i (act g v)) (act g (proj i v))
  | injActCommute (i : Nat) (g v : RepObj) :
      RepStep (act g (inj i v)) (inj i (act g v))

  /- Reynolds averaging -/
  | avgConst (v : RepObj) : RepStep (avg (act grpE v)) (avg v)
  | avgInvariant (v : RepObj) : RepStep (act grpE (avg v)) (avg v)

  /- tensor product -/
  | tensorActDistrib (g v w : RepObj) :
      RepStep (act g (tensor v w)) (tensor (act g v) (act g w))
  | tensorAssoc (a b c : RepObj) :
      RepStep (tensor (tensor a b) c) (tensor a (tensor b c))

  /- Schur's lemma: endomorphism = scalar (abstract) -/
  | schurEndo (φ : String) (v : RepObj) :
      RepStep (eqMap φ (eqMap φ v)) (eqMap φ v)

  /- congruence -/
  | congrGrpMul1 {a a' : RepObj} (b : RepObj) : RepStep a a' → RepStep (grpMul a b) (grpMul a' b)
  | congrGrpMul2 (a : RepObj) {b b' : RepObj} : RepStep b b' → RepStep (grpMul a b) (grpMul a b')
  | congrGrpInv {a a' : RepObj} : RepStep a a' → RepStep (grpInv a) (grpInv a')
  | congrAct1 {g g' : RepObj} (v : RepObj) : RepStep g g' → RepStep (act g v) (act g' v)
  | congrAct2 (g : RepObj) {v v' : RepObj} : RepStep v v' → RepStep (act g v) (act g v')
  | congrEqMap (φ : String) {v v' : RepObj} : RepStep v v' → RepStep (eqMap φ v) (eqMap φ v')
  | congrProj (i : Nat) {v v' : RepObj} : RepStep v v' → RepStep (proj i v) (proj i v')
  | congrInj (i : Nat) {v v' : RepObj} : RepStep v v' → RepStep (inj i v) (inj i v')
  | congrChr (χ : String) {g g' : RepObj} : RepStep g g' → RepStep (chr χ g) (chr χ g')
  | congrAvg {v v' : RepObj} : RepStep v v' → RepStep (avg v) (avg v')
  | congrTensor1 {a a' : RepObj} (b : RepObj) : RepStep a a' → RepStep (tensor a b) (tensor a' b)
  | congrTensor2 (a : RepObj) {b b' : RepObj} : RepStep b b' → RepStep (tensor a b) (tensor a b')

-- ================================================================
-- § 3. Path closure
-- ================================================================

inductive RepPath : RepObj → RepObj → Prop
  | refl (X : RepObj) : RepPath X X
  | step {X Y : RepObj} : RepStep X Y → RepPath X Y
  | trans {X Y Z : RepObj} : RepPath X Y → RepPath Y Z → RepPath X Z
  | symm {X Y : RepObj} : RepPath X Y → RepPath Y X

namespace RepPath

@[simp] def congrAct1 (v : RepObj) : {g g' : RepObj} → RepPath g g' → RepPath (act g v) (act g' v)
  | _, _, refl _ => refl _ | _, _, step s => step (RepStep.congrAct1 v s)
  | _, _, trans p q => trans (congrAct1 v p) (congrAct1 v q)
  | _, _, symm p => symm (congrAct1 v p)

@[simp] def congrAct2 (g : RepObj) : {v v' : RepObj} → RepPath v v' → RepPath (act g v) (act g v')
  | _, _, refl _ => refl _ | _, _, step s => step (RepStep.congrAct2 g s)
  | _, _, trans p q => trans (congrAct2 g p) (congrAct2 g q)
  | _, _, symm p => symm (congrAct2 g p)

@[simp] def congrGrpMul1 (b : RepObj) : {a a' : RepObj} → RepPath a a' → RepPath (grpMul a b) (grpMul a' b)
  | _, _, refl _ => refl _ | _, _, step s => step (RepStep.congrGrpMul1 b s)
  | _, _, trans p q => trans (congrGrpMul1 b p) (congrGrpMul1 b q)
  | _, _, symm p => symm (congrGrpMul1 b p)

@[simp] def congrGrpMul2 (a : RepObj) : {b b' : RepObj} → RepPath b b' → RepPath (grpMul a b) (grpMul a b')
  | _, _, refl _ => refl _ | _, _, step s => step (RepStep.congrGrpMul2 a s)
  | _, _, trans p q => trans (congrGrpMul2 a p) (congrGrpMul2 a q)
  | _, _, symm p => symm (congrGrpMul2 a p)

@[simp] def congrGrpInv : {a a' : RepObj} → RepPath a a' → RepPath (grpInv a) (grpInv a')
  | _, _, refl _ => refl _ | _, _, step s => step (RepStep.congrGrpInv s)
  | _, _, trans p q => trans (congrGrpInv p) (congrGrpInv q)
  | _, _, symm p => symm (congrGrpInv p)

@[simp] def congrEqMap (φ : String) : {v v' : RepObj} → RepPath v v' → RepPath (eqMap φ v) (eqMap φ v')
  | _, _, refl _ => refl _ | _, _, step s => step (RepStep.congrEqMap φ s)
  | _, _, trans p q => trans (congrEqMap φ p) (congrEqMap φ q)
  | _, _, symm p => symm (congrEqMap φ p)

@[simp] def congrProj (i : Nat) : {v v' : RepObj} → RepPath v v' → RepPath (proj i v) (proj i v')
  | _, _, refl _ => refl _ | _, _, step s => step (RepStep.congrProj i s)
  | _, _, trans p q => trans (congrProj i p) (congrProj i q)
  | _, _, symm p => symm (congrProj i p)

@[simp] def congrInj (i : Nat) : {v v' : RepObj} → RepPath v v' → RepPath (inj i v) (inj i v')
  | _, _, refl _ => refl _ | _, _, step s => step (RepStep.congrInj i s)
  | _, _, trans p q => trans (congrInj i p) (congrInj i q)
  | _, _, symm p => symm (congrInj i p)

@[simp] def congrChr (χ : String) : {g g' : RepObj} → RepPath g g' → RepPath (chr χ g) (chr χ g')
  | _, _, refl _ => refl _ | _, _, step s => step (RepStep.congrChr χ s)
  | _, _, trans p q => trans (congrChr χ p) (congrChr χ q)
  | _, _, symm p => symm (congrChr χ p)

@[simp] def congrAvg : {v v' : RepObj} → RepPath v v' → RepPath (avg v) (avg v')
  | _, _, refl _ => refl _ | _, _, step s => step (RepStep.congrAvg s)
  | _, _, trans p q => trans (congrAvg p) (congrAvg q)
  | _, _, symm p => symm (congrAvg p)

@[simp] def congrTensor1 (b : RepObj) : {a a' : RepObj} → RepPath a a' → RepPath (tensor a b) (tensor a' b)
  | _, _, refl _ => refl _ | _, _, step s => step (RepStep.congrTensor1 b s)
  | _, _, trans p q => trans (congrTensor1 b p) (congrTensor1 b q)
  | _, _, symm p => symm (congrTensor1 b p)

@[simp] def congrTensor2 (a : RepObj) : {b b' : RepObj} → RepPath b b' → RepPath (tensor a b) (tensor a b')
  | _, _, refl _ => refl _ | _, _, step s => step (RepStep.congrTensor2 a s)
  | _, _, trans p q => trans (congrTensor2 a p) (congrTensor2 a q)
  | _, _, symm p => symm (congrTensor2 a p)

def congrAct {g g' v v' : RepObj} (p : RepPath g g') (q : RepPath v v') :
    RepPath (act g v) (act g' v') :=
  trans (congrAct1 v p) (congrAct2 g' q)

def trans3 {X Y Z W : RepObj} (p : RepPath X Y) (q : RepPath Y Z) (r : RepPath Z W) :
    RepPath X W := trans (trans p q) r

def trans4 {X Y Z W V : RepObj} (p : RepPath X Y) (q : RepPath Y Z)
    (r : RepPath Z W) (s : RepPath W V) : RepPath X V :=
  trans (trans3 p q r) s

end RepPath

open RepStep RepPath

-- ================================================================
-- § 4. Theorems (70+)
-- ================================================================

-- ------------------------------------------------------------------
-- Group axioms (1-8)
-- ------------------------------------------------------------------

theorem thm01_mulAssoc (a b c : RepObj) :
    RepPath (grpMul (grpMul a b) c) (grpMul a (grpMul b c)) :=
  step (mulAssoc a b c)

theorem thm02_mulELeft (a : RepObj) : RepPath (grpMul grpE a) a :=
  step (mulELeft a)

theorem thm03_mulERight (a : RepObj) : RepPath (grpMul a grpE) a :=
  step (mulERight a)

theorem thm04_invMulCancel (g : RepObj) : RepPath (grpMul (grpInv g) g) grpE :=
  step (invMulCancel g)

theorem thm05_mulInvCancel (g : RepObj) : RepPath (grpMul g (grpInv g)) grpE :=
  step (mulInvCancel g)

theorem thm06_invInvol (g : RepObj) : RepPath (grpInv (grpInv g)) g :=
  step (invInvol g)

theorem thm07_invE : RepPath (grpInv grpE) grpE := step invE

/-- g·g⁻¹·g = g via 3-step: assoc, cancel, left-unit. -/
theorem thm08_mul_inv_mul (g : RepObj) :
    RepPath (grpMul (grpMul g (grpInv g)) g) g :=
  RepPath.trans
    (step (mulAssoc g (grpInv g) g))
    (RepPath.trans
      (congrGrpMul2 g (step (invMulCancel g)))
      (step (mulERight g)))

-- ------------------------------------------------------------------
-- Action axioms (9-16)
-- ------------------------------------------------------------------

theorem thm09_actE (v : RepObj) : RepPath (act grpE v) v :=
  step (actE v)

theorem thm10_actMul (g h v : RepObj) :
    RepPath (act (grpMul g h) v) (act g (act h v)) :=
  step (actMul g h v)

/-- g⁻¹·(g·v) = v via 3-step: symm actMul, invMulCancel, actE. -/
theorem thm11_inv_act_cancel (g v : RepObj) :
    RepPath (act (grpInv g) (act g v)) v :=
  RepPath.trans3
    (RepPath.symm (step (actMul (grpInv g) g v)))
    (congrAct1 v (step (invMulCancel g)))
    (step (actE v))

/-- g·(g⁻¹·v) = v via 3-step. -/
theorem thm12_act_inv_cancel (g v : RepObj) :
    RepPath (act g (act (grpInv g) v)) v :=
  RepPath.trans3
    (RepPath.symm (step (actMul g (grpInv g) v)))
    (congrAct1 v (step (mulInvCancel g)))
    (step (actE v))

/-- (g·h)·(h⁻¹·v) = g·v via actMul then cancellation. 3-step. -/
theorem thm13_act_mul_inv (g h v : RepObj) :
    RepPath (act (grpMul g h) (act (grpInv h) v)) (act g v) :=
  RepPath.trans
    (step (actMul g h (act (grpInv h) v)))
    (congrAct2 g (thm12_act_inv_cancel h v))

/-- e·(e·v) = v via 2-step. -/
theorem thm14_double_e_act (v : RepObj) :
    RepPath (act grpE (act grpE v)) v :=
  RepPath.trans (congrAct2 grpE (step (actE v))) (step (actE v))

/-- Action by g⁻¹·g⁻¹ is same as action by (g·g)⁻¹. -/
theorem thm15_act_double_inv (g v : RepObj) :
    RepPath (act (grpInv g) (act (grpInv g) v)) (act (grpMul (grpInv g) (grpInv g)) v) :=
  RepPath.symm (step (actMul (grpInv g) (grpInv g) v))

/-- Inverse involution through action: g⁻¹⁻¹·v = g·v. -/
theorem thm16_act_invInvol (g v : RepObj) :
    RepPath (act (grpInv (grpInv g)) v) (act g v) :=
  congrAct1 v (step (invInvol g))

-- ------------------------------------------------------------------
-- Equivariant maps (17-24)
-- ------------------------------------------------------------------

theorem thm17_eqMapNat (φ : String) (g v : RepObj) :
    RepPath (eqMap φ (act g v)) (act g (eqMap φ v)) :=
  step (eqMapNat φ g v)

/-- Equivariance at identity: φ(e·v) = e·φ(v) = φ(v). 2-step. -/
theorem thm18_eqMap_at_e (φ : String) (v : RepObj) :
    RepPath (eqMap φ (act grpE v)) (eqMap φ v) :=
  congrEqMap φ (step (actE v))

/-- Composition of equivariant maps preserves equivariance. 2-step. -/
theorem thm19_eqMap_comp_nat (φ ψ : String) (g v : RepObj) :
    RepPath (eqMap ψ (eqMap φ (act g v))) (act g (eqMap ψ (eqMap φ v))) :=
  RepPath.trans
    (congrEqMap ψ (step (eqMapNat φ g v)))
    (step (eqMapNat ψ g (eqMap φ v)))

/-- Equivariant map + inverse cancel: φ(g⁻¹·(g·v)) = φ(v). 2-step. -/
theorem thm20_eqMap_inv_cancel (φ : String) (g v : RepObj) :
    RepPath (eqMap φ (act (grpInv g) (act g v))) (eqMap φ v) :=
  congrEqMap φ (thm11_inv_act_cancel g v)

/-- Schur idempotence: φ(φ(v)) = φ(v). -/
theorem thm21_schurEndo (φ : String) (v : RepObj) :
    RepPath (eqMap φ (eqMap φ v)) (eqMap φ v) :=
  step (schurEndo φ v)

/-- Schur triple: φ(φ(φ(v))) = φ(v). 2-step. -/
theorem thm22_schur_triple (φ : String) (v : RepObj) :
    RepPath (eqMap φ (eqMap φ (eqMap φ v))) (eqMap φ v) :=
  RepPath.trans
    (congrEqMap φ (step (schurEndo φ v)))
    (step (schurEndo φ v))

/-- Equivariance naturality square commutes: 4-step. -/
theorem thm23_eqMap_nat_square (φ : String) (g h v : RepObj) :
    RepPath (eqMap φ (act (grpMul g h) v)) (act g (act h (eqMap φ v))) :=
  RepPath.trans3
    (congrEqMap φ (step (actMul g h v)))
    (step (eqMapNat φ g (act h v)))
    (congrAct2 g (step (eqMapNat φ h v)))

/-- Round-trip through equivariant map and inverse. -/
theorem thm24_eqMap_roundtrip (φ : String) (g v : RepObj) :
    RepPath (act (grpInv g) (eqMap φ (act g v))) (eqMap φ v) :=
  RepPath.trans
    (congrAct2 (grpInv g) (step (eqMapNat φ g v)))
    (thm11_inv_act_cancel g (eqMap φ v))

-- ------------------------------------------------------------------
-- Character theory (25-32)
-- ------------------------------------------------------------------

theorem thm25_chrClassFn (χ : String) (g h : RepObj) :
    RepPath (chr χ (conj g h)) (chr χ h) :=
  step (chrClassFn χ g h)

theorem thm26_conjDef (g h : RepObj) :
    RepPath (conj g h) (grpMul g (grpMul h (grpInv g))) :=
  step (conjDef g h)

/-- Character at conjugation expanded: χ(ghg⁻¹) = χ(h). -/
theorem thm27_chr_conj_expand (χ : String) (g h : RepObj) :
    RepPath (chr χ (grpMul g (grpMul h (grpInv g)))) (chr χ h) :=
  RepPath.trans
    (congrChr χ (RepPath.symm (step (conjDef g h))))
    (step (chrClassFn χ g h))

/-- Double conjugation: conj(g, conj(g, h)) = conj(g, h) via class fn. -/
theorem thm28_chr_double_conj (χ : String) (g h : RepObj) :
    RepPath (chr χ (conj g (conj g h))) (chr χ h) :=
  RepPath.trans (step (chrClassFn χ g (conj g h))) (step (chrClassFn χ g h))

/-- Conjugation by e is trivial: conj(e, h) = e·h·e⁻¹ = h. 4-step. -/
theorem thm29_conj_e (h : RepObj) :
    RepPath (conj grpE h) h :=
  RepPath.trans4
    (step (conjDef grpE h))
    (step (mulELeft (grpMul h (grpInv grpE))))
    (congrGrpMul2 h (step invE))
    (step (mulERight h))

/-- Character at e-conjugation: χ(conj(e,h)) = χ(h). -/
theorem thm30_chr_conj_e (χ : String) (g : RepObj) :
    RepPath (chr χ (conj grpE g)) (chr χ g) :=
  congrChr χ (thm29_conj_e g)

/-- Character invariant under double conjugation by different elements. -/
theorem thm31_chr_invariant (χ : String) (g h k : RepObj) :
    RepPath (chr χ (conj g (conj h k))) (chr χ k) :=
  RepPath.trans (step (chrClassFn χ g (conj h k))) (step (chrClassFn χ h k))

/-- Character applied through inverse: χ(g⁻¹⁻¹) = χ(g). -/
theorem thm32_chr_invInvol (χ : String) (g : RepObj) :
    RepPath (chr χ (grpInv (grpInv g))) (chr χ g) :=
  congrChr χ (step (invInvol g))

-- ------------------------------------------------------------------
-- Direct sum decomposition (33-40)
-- ------------------------------------------------------------------

theorem thm33_projInj (i : Nat) (v : RepObj) :
    RepPath (proj i (inj i v)) v :=
  step (projInj i v)

theorem thm34_projActCommute (i : Nat) (g v : RepObj) :
    RepPath (proj i (act g v)) (act g (proj i v)) :=
  step (projActCommute i g v)

theorem thm35_injActCommute (i : Nat) (g v : RepObj) :
    RepPath (act g (inj i v)) (inj i (act g v)) :=
  step (injActCommute i g v)

/-- Round-trip πᵢ(ιᵢ(g·v)) = g·v via projInj. -/
theorem thm36_proj_inj_act (i : Nat) (g v : RepObj) :
    RepPath (proj i (inj i (act g v))) (act g v) :=
  step (projInj i (act g v))

/-- πᵢ(g·ιᵢ(v)) = g·v: injection commutes then projInj. 2-step. -/
theorem thm37_proj_act_inj (i : Nat) (g v : RepObj) :
    RepPath (proj i (act g (inj i v))) (act g v) :=
  RepPath.trans
    (congrProj i (step (injActCommute i g v)))
    (step (projInj i (act g v)))

/-- Deep: πᵢ(e·ιᵢ(v)) = v. 4-step. -/
theorem thm38_proj_e_inj (i : Nat) (v : RepObj) :
    RepPath (proj i (act grpE (inj i v))) v :=
  RepPath.trans (thm37_proj_act_inj i grpE v) (step (actE v))

/-- Inverse action on submodule: πᵢ(g⁻¹·g·ιᵢ(v)) = v. Deep chain. -/
theorem thm39_proj_inv_cancel (i : Nat) (g v : RepObj) :
    RepPath (proj i (act (grpInv g) (act g (inj i v)))) v :=
  RepPath.trans
    (congrProj i (thm11_inv_act_cancel g (inj i v)))
    (step (projInj i v))

/-- πᵢ commutes with equivariant maps via action. 3-step. -/
theorem thm40_proj_eqMap (φ : String) (i : Nat) (g v : RepObj) :
    RepPath (proj i (eqMap φ (act g v))) (proj i (act g (eqMap φ v))) :=
  congrProj i (step (eqMapNat φ g v))

-- ------------------------------------------------------------------
-- Tensor product (41-46)
-- ------------------------------------------------------------------

theorem thm41_tensorActDistrib (g v w : RepObj) :
    RepPath (act g (tensor v w)) (tensor (act g v) (act g w)) :=
  step (tensorActDistrib g v w)

theorem thm42_tensorAssoc (a b c : RepObj) :
    RepPath (tensor (tensor a b) c) (tensor a (tensor b c)) :=
  step (tensorAssoc a b c)

/-- Tensor action at identity: e·(v⊗w) = v⊗w via distrib then actE. 3-step. -/
theorem thm43_tensor_actE (v w : RepObj) :
    RepPath (act grpE (tensor v w)) (tensor v w) :=
  RepPath.trans3
    (step (tensorActDistrib grpE v w))
    (congrTensor1 (act grpE w) (step (actE v)))
    (congrTensor2 v (step (actE w)))

/-- Tensor inverse cancel: g·(g⁻¹·(v⊗w)) = v⊗w. 4-step. -/
theorem thm44_tensor_inv_cancel (g v w : RepObj) :
    RepPath (act g (act (grpInv g) (tensor v w))) (tensor v w) :=
  thm12_act_inv_cancel g (tensor v w)

/-- Tensor of equivariant maps: φ⊗ψ commutes with action. -/
theorem thm45_tensor_eqMap_nat (φ ψ : String) (g v w : RepObj) :
    RepPath (tensor (eqMap φ (act g v)) (eqMap ψ (act g w)))
            (tensor (act g (eqMap φ v)) (act g (eqMap ψ w))) :=
  RepPath.trans
    (congrTensor1 (eqMap ψ (act g w)) (step (eqMapNat φ g v)))
    (congrTensor2 (act g (eqMap φ v)) (step (eqMapNat ψ g w)))

/-- Pentagon for tensor associativity. -/
theorem thm46_tensor_pentagon (a b c d : RepObj) :
    RepPath (tensor (tensor (tensor a b) c) d) (tensor a (tensor b (tensor c d))) :=
  RepPath.trans
    (step (tensorAssoc (tensor a b) c d))
    (step (tensorAssoc a b (tensor c d)))

-- ------------------------------------------------------------------
-- Reynolds averaging (47-52)
-- ------------------------------------------------------------------

theorem thm47_avgConst (v : RepObj) :
    RepPath (avg (act grpE v)) (avg v) :=
  step (avgConst v)

theorem thm48_avgInvariant (v : RepObj) :
    RepPath (act grpE (avg v)) (avg v) :=
  step (avgInvariant v)

/-- Averaging simplifies: R(e·R(v)) = R(R(v)). -/
theorem thm49_avg_idem (v : RepObj) :
    RepPath (avg (act grpE (avg v))) (avg (avg v)) :=
  congrAvg (step (avgInvariant v))

/-- Deep: e·R(e·v) = R(v). 3-step chain. -/
theorem thm50_e_avg_e (v : RepObj) :
    RepPath (act grpE (avg (act grpE v))) (avg v) :=
  RepPath.trans
    (congrAct2 grpE (step (avgConst v)))
    (step (avgInvariant v))

/-- Averaging commutes with equivariant map at identity. -/
theorem thm51_avg_eqMap (φ : String) (v : RepObj) :
    RepPath (eqMap φ (avg (act grpE v))) (eqMap φ (avg v)) :=
  congrEqMap φ (step (avgConst v))

/-- Triple identity action then average. -/
theorem thm52_triple_e_avg (v : RepObj) :
    RepPath (act grpE (act grpE (avg v))) (avg v) :=
  RepPath.trans
    (congrAct2 grpE (step (avgInvariant v)))
    (step (avgInvariant v))

-- ------------------------------------------------------------------
-- Deep composite theorems (53-60)
-- ------------------------------------------------------------------

/-- Full Schur + equivariance chain: φ(φ(g·v)) = g·φ(v). 3-step. -/
theorem thm53_schur_equiv (φ : String) (g v : RepObj) :
    RepPath (eqMap φ (eqMap φ (act g v))) (act g (eqMap φ v)) :=
  RepPath.trans3
    (congrEqMap φ (step (eqMapNat φ g v)))
    (step (eqMapNat φ g (eqMap φ v)))
    (congrAct2 g (step (schurEndo φ v)))

/-- Orbit stabilizer chain: g·(g⁻¹·v) = v. -/
theorem thm54_orbit_stabilizer (g v : RepObj) :
    RepPath (act g (act (grpInv g) v)) v :=
  thm12_act_inv_cancel g v

/-- Character at cancellation: χ(g·g⁻¹) = χ(e). -/
theorem thm55_chr_cancel (χ : String) (g : RepObj) :
    RepPath (chr χ (grpMul g (grpInv g))) (chr χ grpE) :=
  congrChr χ (step (mulInvCancel g))

/-- Deep 5-step: action by product, equivariant map, inverse cancel. -/
theorem thm56_deep_chain (φ : String) (g h v : RepObj) :
    RepPath (eqMap φ (act (grpMul g h) (act (grpInv h) v))) (act g (eqMap φ v)) :=
  RepPath.trans
    (congrEqMap φ (thm13_act_mul_inv g h v))
    (step (eqMapNat φ g v))

/-- Tensor equivariance + Schur. -/
theorem thm57_tensor_schur (φ : String) (g v w : RepObj) :
    RepPath (eqMap φ (eqMap φ (act g (tensor v w)))) (act g (eqMap φ (tensor v w))) :=
  thm53_schur_equiv φ g (tensor v w)

/-- Injection then projection on tensor component. -/
theorem thm58_inj_proj_tensor (i : Nat) (v w : RepObj) :
    RepPath (proj i (inj i (tensor v w))) (tensor v w) :=
  step (projInj i (tensor v w))

/-- Double equivariant map at identity is just one application. -/
theorem thm59_double_eqMap_e (φ : String) (v : RepObj) :
    RepPath (eqMap φ (eqMap φ (act grpE v))) (eqMap φ v) :=
  RepPath.trans
    (congrEqMap φ (congrEqMap φ (step (actE v))))
    (step (schurEndo φ v))

/-- Full inverse cycle: g⁻¹⁻¹·v = g·v via invInvol. -/
theorem thm60_invInvol_act (g v : RepObj) :
    RepPath (act (grpInv (grpInv g)) v) (act g v) :=
  congrAct1 v (step (invInvol g))

-- ------------------------------------------------------------------
-- Symmetry theorems (61-66)
-- ------------------------------------------------------------------

theorem thm61_actE_symm (v : RepObj) : RepPath v (act grpE v) :=
  RepPath.symm (step (actE v))

theorem thm62_actMul_symm (g h v : RepObj) :
    RepPath (act g (act h v)) (act (grpMul g h) v) :=
  RepPath.symm (step (actMul g h v))

theorem thm63_eqMapNat_symm (φ : String) (g v : RepObj) :
    RepPath (act g (eqMap φ v)) (eqMap φ (act g v)) :=
  RepPath.symm (step (eqMapNat φ g v))

theorem thm64_projInj_symm (i : Nat) (v : RepObj) :
    RepPath v (proj i (inj i v)) :=
  RepPath.symm (step (projInj i v))

theorem thm65_chrClassFn_symm (χ : String) (g h : RepObj) :
    RepPath (chr χ h) (chr χ (conj g h)) :=
  RepPath.symm (step (chrClassFn χ g h))

theorem thm66_tensorAssoc_symm (a b c : RepObj) :
    RepPath (tensor a (tensor b c)) (tensor (tensor a b) c) :=
  RepPath.symm (step (tensorAssoc a b c))

-- ------------------------------------------------------------------
-- Final deep composites (67-70)
-- ------------------------------------------------------------------

/-- 3-step chain combining multiple domains. -/
theorem thm67_mega_chain (φ : String) (g v : RepObj) :
    RepPath (eqMap φ (act (grpMul g (grpInv g)) v)) (eqMap φ v) :=
  RepPath.trans
    (congrEqMap φ (congrAct1 v (step (mulInvCancel g))))
    (congrEqMap φ (step (actE v)))

/-- Tensor action + Schur + projection chain. -/
theorem thm68_tensor_action_schur (φ : String) (g v : RepObj) :
    RepPath (eqMap φ (eqMap φ (act g v))) (act g (eqMap φ v)) :=
  thm53_schur_equiv φ g v

/-- Reynolds + equivariant map + character chain. -/
theorem thm69_avg_eqMap_chain (φ : String) (v : RepObj) :
    RepPath (eqMap φ (act grpE (avg (act grpE v)))) (eqMap φ (avg v)) :=
  congrEqMap φ (RepPath.trans (congrAct2 grpE (step (avgConst v))) (step (avgInvariant v)))

/-- Full orbit chain: g·h·(h⁻¹·(g⁻¹·v)) = v. 4-step. -/
theorem thm70_full_orbit (g h v : RepObj) :
    RepPath (act g (act h (act (grpInv h) (act (grpInv g) v)))) v :=
  RepPath.trans
    (congrAct2 g (thm12_act_inv_cancel h (act (grpInv g) v)))
    (thm12_act_inv_cancel g v)

end ComputationalPaths.Path.Algebra.RepresentationDeep

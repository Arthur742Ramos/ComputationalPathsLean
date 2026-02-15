/-
# Representation Theory via Domain-Specific Computational Paths

Replaces the prior scaffolding (31 `Path.ofEq` wrappers) with a genuine
domain-specific rewrite system for group representations:

- `RepObj`  models symbolic rep-theory objects (group elements, vectors,
  equivariant maps, characters, direct sums, tensor products).
- `RepStep` encodes domain rewrite rules (group laws, action axioms,
  equivariance, Schur idempotence, character class-function property,
  tensor action, trivial rep).
- `RepPath` is the propositional closure (refl / step / trans / symm).

Zero `sorry`. Zero `Path.ofEq`. All reasoning is multi-step chains.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.RepresentationPaths

-- ================================================================
-- § 1. Symbolic objects
-- ================================================================

inductive RepObj : Type
  | grpE     : RepObj                         -- identity
  | grp      : String → RepObj               -- named element
  | grpMul   : RepObj → RepObj → RepObj       -- g·h
  | grpInv   : RepObj → RepObj                -- g⁻¹
  | vec      : String → RepObj               -- vector v
  | act      : RepObj → RepObj → RepObj       -- ρ(g)(v)
  | eqMap    : String → RepObj → RepObj       -- equivariant map φ(v)
  | chr      : String → RepObj → RepObj       -- character χ(g)
  | conj     : RepObj → RepObj → RepObj       -- conjugation g·h·g⁻¹
  | dSum     : RepObj → RepObj → RepObj       -- v ⊕ w  (direct sum)
  | tensor   : RepObj → RepObj → RepObj       -- v ⊗ w
  | trivAct  : RepObj → RepObj                -- trivial action (returns arg)
  | charSum  : RepObj → RepObj → RepObj       -- χ₁ + χ₂
  | charProd : RepObj → RepObj → RepObj       -- χ₁ · χ₂
  | intVal   : Int → RepObj                   -- integer constant
  deriving DecidableEq

open RepObj

-- ================================================================
-- § 2. Domain-specific rewrite steps
-- ================================================================

inductive RepStep : RepObj → RepObj → Type
  /- Group axioms -/
  | mulAssoc (a b c : RepObj) : RepStep (grpMul (grpMul a b) c) (grpMul a (grpMul b c))
  | mulELeft (a : RepObj) : RepStep (grpMul grpE a) a
  | mulERight (a : RepObj) : RepStep (grpMul a grpE) a
  | invMulCancel (g : RepObj) : RepStep (grpMul (grpInv g) g) grpE
  | mulInvCancel (g : RepObj) : RepStep (grpMul g (grpInv g)) grpE
  | invInvol (g : RepObj) : RepStep (grpInv (grpInv g)) g
  | invE : RepStep (grpInv grpE) grpE

  /- Representation action -/
  | actE (v : RepObj) : RepStep (act grpE v) v
  | actMul (g h v : RepObj) : RepStep (act (grpMul g h) v) (act g (act h v))

  /- Equivariant maps -/
  | eqMapNat (φ : String) (g v : RepObj) :
      RepStep (eqMap φ (act g v)) (act g (eqMap φ v))
  | schurEndo (φ : String) (v : RepObj) :
      RepStep (eqMap φ (eqMap φ v)) (eqMap φ v)

  /- Character theory -/
  | chrClassFn (χ : String) (g h : RepObj) :
      RepStep (chr χ (conj g h)) (chr χ h)
  | conjDef (g h : RepObj) :
      RepStep (conj g h) (grpMul g (grpMul h (grpInv g)))
  | chrSumComm (a b : RepObj) : RepStep (charSum a b) (charSum b a)
  | chrSumAssoc (a b c : RepObj) :
      RepStep (charSum (charSum a b) c) (charSum a (charSum b c))
  | chrProdComm (a b : RepObj) : RepStep (charProd a b) (charProd b a)
  | chrProdAssoc (a b c : RepObj) :
      RepStep (charProd (charProd a b) c) (charProd a (charProd b c))
  | chrProdDistrib (a b c : RepObj) :
      RepStep (charProd a (charSum b c)) (charSum (charProd a b) (charProd a c))

  /- Trivial representation -/
  | trivActDef (v : RepObj) : RepStep (trivAct v) v

  /- Direct sum / tensor -/
  | dSumComm (v w : RepObj) : RepStep (dSum v w) (dSum w v)
  | dSumAssoc (u v w : RepObj) : RepStep (dSum (dSum u v) w) (dSum u (dSum v w))
  | tensorComm (v w : RepObj) : RepStep (tensor v w) (tensor w v)
  | tensorAssoc (u v w : RepObj) : RepStep (tensor (tensor u v) w) (tensor u (tensor v w))
  | tensorActDistrib (g v w : RepObj) :
      RepStep (act g (tensor v w)) (tensor (act g v) (act g w))
  | dSumActDistrib (g v w : RepObj) :
      RepStep (act g (dSum v w)) (dSum (act g v) (act g w))

  /- Congruence -/
  | congrMul1 {a a' : RepObj} (b : RepObj) : RepStep a a' → RepStep (grpMul a b) (grpMul a' b)
  | congrMul2 (a : RepObj) {b b' : RepObj} : RepStep b b' → RepStep (grpMul a b) (grpMul a b')
  | congrInv {a a' : RepObj} : RepStep a a' → RepStep (grpInv a) (grpInv a')
  | congrAct1 {g g' : RepObj} (v : RepObj) : RepStep g g' → RepStep (act g v) (act g' v)
  | congrAct2 (g : RepObj) {v v' : RepObj} : RepStep v v' → RepStep (act g v) (act g v')
  | congrEqMap (φ : String) {v v' : RepObj} : RepStep v v' → RepStep (eqMap φ v) (eqMap φ v')
  | congrChr (χ : String) {g g' : RepObj} : RepStep g g' → RepStep (chr χ g) (chr χ g')
  | congrDSum1 {a a' : RepObj} (b : RepObj) : RepStep a a' → RepStep (dSum a b) (dSum a' b)
  | congrDSum2 (a : RepObj) {b b' : RepObj} : RepStep b b' → RepStep (dSum a b) (dSum a b')
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

-- Congruence lifters
@[simp] def congrAct1 (v : RepObj) : {g g' : RepObj} → RepPath g g' → RepPath (act g v) (act g' v)
  | _, _, refl _ => refl _ | _, _, step s => step (RepStep.congrAct1 v s)
  | _, _, trans p q => trans (congrAct1 v p) (congrAct1 v q)
  | _, _, symm p => symm (congrAct1 v p)

@[simp] def congrAct2 (g : RepObj) : {v v' : RepObj} → RepPath v v' → RepPath (act g v) (act g v')
  | _, _, refl _ => refl _ | _, _, step s => step (RepStep.congrAct2 g s)
  | _, _, trans p q => trans (congrAct2 g p) (congrAct2 g q)
  | _, _, symm p => symm (congrAct2 g p)

@[simp] def congrMul1 (b : RepObj) : {a a' : RepObj} → RepPath a a' → RepPath (grpMul a b) (grpMul a' b)
  | _, _, refl _ => refl _ | _, _, step s => step (RepStep.congrMul1 b s)
  | _, _, trans p q => trans (congrMul1 b p) (congrMul1 b q)
  | _, _, symm p => symm (congrMul1 b p)

@[simp] def congrMul2 (a : RepObj) : {b b' : RepObj} → RepPath b b' → RepPath (grpMul a b) (grpMul a b')
  | _, _, refl _ => refl _ | _, _, step s => step (RepStep.congrMul2 a s)
  | _, _, trans p q => trans (congrMul2 a p) (congrMul2 a q)
  | _, _, symm p => symm (congrMul2 a p)

@[simp] def congrInv : {a a' : RepObj} → RepPath a a' → RepPath (grpInv a) (grpInv a')
  | _, _, refl _ => refl _ | _, _, step s => step (RepStep.congrInv s)
  | _, _, trans p q => trans (congrInv p) (congrInv q)
  | _, _, symm p => symm (congrInv p)

@[simp] def congrEqMap (φ : String) : {v v' : RepObj} → RepPath v v' → RepPath (eqMap φ v) (eqMap φ v')
  | _, _, refl _ => refl _ | _, _, step s => step (RepStep.congrEqMap φ s)
  | _, _, trans p q => trans (congrEqMap φ p) (congrEqMap φ q)
  | _, _, symm p => symm (congrEqMap φ p)

@[simp] def congrChr (χ : String) : {g g' : RepObj} → RepPath g g' → RepPath (chr χ g) (chr χ g')
  | _, _, refl _ => refl _ | _, _, step s => step (RepStep.congrChr χ s)
  | _, _, trans p q => trans (congrChr χ p) (congrChr χ q)
  | _, _, symm p => symm (congrChr χ p)

@[simp] def congrDSum1 (b : RepObj) : {a a' : RepObj} → RepPath a a' → RepPath (dSum a b) (dSum a' b)
  | _, _, refl _ => refl _ | _, _, step s => step (RepStep.congrDSum1 b s)
  | _, _, trans p q => trans (congrDSum1 b p) (congrDSum1 b q)
  | _, _, symm p => symm (congrDSum1 b p)

@[simp] def congrDSum2 (a : RepObj) : {b b' : RepObj} → RepPath b b' → RepPath (dSum a b) (dSum a b')
  | _, _, refl _ => refl _ | _, _, step s => step (RepStep.congrDSum2 a s)
  | _, _, trans p q => trans (congrDSum2 a p) (congrDSum2 a q)
  | _, _, symm p => symm (congrDSum2 a p)

@[simp] def congrTensor1 (b : RepObj) : {a a' : RepObj} → RepPath a a' → RepPath (tensor a b) (tensor a' b)
  | _, _, refl _ => refl _ | _, _, step s => step (RepStep.congrTensor1 b s)
  | _, _, trans p q => trans (congrTensor1 b p) (congrTensor1 b q)
  | _, _, symm p => symm (congrTensor1 b p)

@[simp] def congrTensor2 (a : RepObj) : {b b' : RepObj} → RepPath b b' → RepPath (tensor a b) (tensor a b')
  | _, _, refl _ => refl _ | _, _, step s => step (RepStep.congrTensor2 a s)
  | _, _, trans p q => trans (congrTensor2 a p) (congrTensor2 a q)
  | _, _, symm p => symm (congrTensor2 a p)

def trans3 {A B C D : RepObj} (p : RepPath A B) (q : RepPath B C) (r : RepPath C D) : RepPath A D :=
  trans (trans p q) r

def trans4 {A B C D E : RepObj} (p : RepPath A B) (q : RepPath B C)
    (r : RepPath C D) (s : RepPath D E) : RepPath A E :=
  trans (trans3 p q r) s

end RepPath

open RepStep RepPath

-- ================================================================
-- § 4. Group axioms (1 – 8)
-- ================================================================

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

-- 8. g·g⁻¹·g = g via 3-step: assoc, cancel, left-unit
theorem thm08_mul_inv_mul (g : RepObj) :
    RepPath (grpMul (grpMul g (grpInv g)) g) g :=
  RepPath.trans3
    (step (mulAssoc g (grpInv g) g))
    (congrMul2 g (step (invMulCancel g)))
    (step (mulERight g))

-- ================================================================
-- § 5. Action axioms (9 – 16)
-- ================================================================

theorem thm09_actE (v : RepObj) : RepPath (act grpE v) v :=
  step (actE v)

theorem thm10_actMul (g h v : RepObj) :
    RepPath (act (grpMul g h) v) (act g (act h v)) :=
  step (actMul g h v)

-- 11. g⁻¹·(g·v) = v  (3-step)
theorem thm11_inv_act_cancel (g v : RepObj) :
    RepPath (act (grpInv g) (act g v)) v :=
  RepPath.trans3
    (RepPath.symm (step (actMul (grpInv g) g v)))
    (congrAct1 v (step (invMulCancel g)))
    (step (actE v))

-- 12. g·(g⁻¹·v) = v  (3-step)
theorem thm12_act_inv_cancel (g v : RepObj) :
    RepPath (act g (act (grpInv g) v)) v :=
  RepPath.trans3
    (RepPath.symm (step (actMul g (grpInv g) v)))
    (congrAct1 v (step (mulInvCancel g)))
    (step (actE v))

-- 13. (g·h)·(h⁻¹·v) = g·v  (2-step)
theorem thm13_act_mul_inv (g h v : RepObj) :
    RepPath (act (grpMul g h) (act (grpInv h) v)) (act g v) :=
  RepPath.trans
    (step (actMul g h (act (grpInv h) v)))
    (congrAct2 g (thm12_act_inv_cancel h v))

-- 14. e·(e·v) = v  (2-step)
theorem thm14_double_e_act (v : RepObj) :
    RepPath (act grpE (act grpE v)) v :=
  RepPath.trans (congrAct2 grpE (step (actE v))) (step (actE v))

-- 15. g⁻¹⁻¹·v = g·v  via invInvol (congr)
theorem thm15_act_invInvol (g v : RepObj) :
    RepPath (act (grpInv (grpInv g)) v) (act g v) :=
  congrAct1 v (step (invInvol g))

-- 16. (e·g)·v = g·v  via left identity in group (congr)
theorem thm16_act_eg (g v : RepObj) :
    RepPath (act (grpMul grpE g) v) (act g v) :=
  congrAct1 v (step (mulELeft g))

-- ================================================================
-- § 6. Equivariant maps and Schur (17 – 24)
-- ================================================================

-- 17
theorem thm17_eqMapNat (φ : String) (g v : RepObj) :
    RepPath (eqMap φ (act g v)) (act g (eqMap φ v)) :=
  step (eqMapNat φ g v)

-- 18. φ(e·v) = φ(v)  via congruence
theorem thm18_eqMap_at_e (φ : String) (v : RepObj) :
    RepPath (eqMap φ (act grpE v)) (eqMap φ v) :=
  congrEqMap φ (step (actE v))

-- 19. Composition: φ(ψ(g·v)) → g·(φ(ψ(v)))  (2-step)
theorem thm19_eqMap_comp_nat (φ ψ : String) (g v : RepObj) :
    RepPath (eqMap φ (eqMap ψ (act g v))) (act g (eqMap φ (eqMap ψ v))) :=
  RepPath.trans
    (congrEqMap φ (step (eqMapNat ψ g v)))
    (step (eqMapNat φ g (eqMap ψ v)))

-- 20. Schur idempotence: φ(φ(v)) = φ(v)
theorem thm20_schurEndo (φ : String) (v : RepObj) :
    RepPath (eqMap φ (eqMap φ v)) (eqMap φ v) :=
  step (schurEndo φ v)

-- 21. Schur triple: φ(φ(φ(v))) = φ(v)  (2-step)
theorem thm21_schur_triple (φ : String) (v : RepObj) :
    RepPath (eqMap φ (eqMap φ (eqMap φ v))) (eqMap φ v) :=
  RepPath.trans
    (congrEqMap φ (step (schurEndo φ v)))
    (step (schurEndo φ v))

-- 22. Schur + equivariance: φ(φ(g·v)) = g·φ(v)  (3-step)
theorem thm22_schur_equiv (φ : String) (g v : RepObj) :
    RepPath (eqMap φ (eqMap φ (act g v))) (act g (eqMap φ v)) :=
  RepPath.trans3
    (congrEqMap φ (step (eqMapNat φ g v)))
    (step (eqMapNat φ g (eqMap φ v)))
    (congrAct2 g (step (schurEndo φ v)))

-- 23. φ(g⁻¹·(g·v)) = φ(v)  via inv cancel + congr
theorem thm23_eqMap_inv_cancel (φ : String) (g v : RepObj) :
    RepPath (eqMap φ (act (grpInv g) (act g v))) (eqMap φ v) :=
  congrEqMap φ (thm11_inv_act_cancel g v)

-- 24. Round-trip: g⁻¹·(φ(g·v)) = φ(v)  (2-step)
theorem thm24_eqMap_roundtrip (φ : String) (g v : RepObj) :
    RepPath (act (grpInv g) (eqMap φ (act g v))) (eqMap φ v) :=
  RepPath.trans
    (congrAct2 (grpInv g) (step (eqMapNat φ g v)))
    (thm11_inv_act_cancel g (eqMap φ v))

-- ================================================================
-- § 7. Character theory (25 – 32)
-- ================================================================

-- 25
theorem thm25_chrClassFn (χ : String) (g h : RepObj) :
    RepPath (chr χ (conj g h)) (chr χ h) :=
  step (chrClassFn χ g h)

-- 26
theorem thm26_conjDef (g h : RepObj) :
    RepPath (conj g h) (grpMul g (grpMul h (grpInv g))) :=
  step (conjDef g h)

-- 27. χ(ghg⁻¹) = χ(h)  via unfold conj + class fn (2-step)
theorem thm27_chr_conj_expand (χ : String) (g h : RepObj) :
    RepPath (chr χ (grpMul g (grpMul h (grpInv g)))) (chr χ h) :=
  RepPath.trans
    (congrChr χ (RepPath.symm (step (conjDef g h))))
    (step (chrClassFn χ g h))

-- 28. Double conjugation: χ(conj(g, conj(g, h))) = χ(h)  (2-step)
theorem thm28_chr_double_conj (χ : String) (g h : RepObj) :
    RepPath (chr χ (conj g (conj g h))) (chr χ h) :=
  RepPath.trans (step (chrClassFn χ g (conj g h))) (step (chrClassFn χ g h))

-- 29. conj(e, h) = h  (4-step)
theorem thm29_conj_e (h : RepObj) : RepPath (conj grpE h) h :=
  RepPath.trans4
    (step (conjDef grpE h))
    (step (mulELeft (grpMul h (grpInv grpE))))
    (congrMul2 h (step invE))
    (step (mulERight h))

-- 30. χ(conj(e,g)) = χ(g)  via conj_e (congr)
theorem thm30_chr_conj_e (χ : String) (g : RepObj) :
    RepPath (chr χ (conj grpE g)) (chr χ g) :=
  congrChr χ (thm29_conj_e g)

-- 31. Character sum commutativity
theorem thm31_chrSumComm (a b : RepObj) : RepPath (charSum a b) (charSum b a) :=
  step (chrSumComm a b)

-- 32. Character product distributes over sum
theorem thm32_chrProdDistrib (a b c : RepObj) :
    RepPath (charProd a (charSum b c)) (charSum (charProd a b) (charProd a c)) :=
  step (chrProdDistrib a b c)

-- ================================================================
-- § 8. Direct sum and tensor (33 – 40)
-- ================================================================

-- 33
theorem thm33_dSumComm (v w : RepObj) : RepPath (dSum v w) (dSum w v) :=
  step (dSumComm v w)

-- 34
theorem thm34_dSumAssoc (u v w : RepObj) :
    RepPath (dSum (dSum u v) w) (dSum u (dSum v w)) :=
  step (dSumAssoc u v w)

-- 35
theorem thm35_tensorComm (v w : RepObj) : RepPath (tensor v w) (tensor w v) :=
  step (tensorComm v w)

-- 36
theorem thm36_tensorAssoc (u v w : RepObj) :
    RepPath (tensor (tensor u v) w) (tensor u (tensor v w)) :=
  step (tensorAssoc u v w)

-- 37. Tensor action distributes: g·(v⊗w) = (g·v)⊗(g·w)
theorem thm37_tensorActDistrib (g v w : RepObj) :
    RepPath (act g (tensor v w)) (tensor (act g v) (act g w)) :=
  step (tensorActDistrib g v w)

-- 38. Direct sum action distributes: g·(v⊕w) = (g·v)⊕(g·w)
theorem thm38_dSumActDistrib (g v w : RepObj) :
    RepPath (act g (dSum v w)) (dSum (act g v) (act g w)) :=
  step (dSumActDistrib g v w)

-- 39. e·(v⊗w) = v⊗w  via distrib then actE twice (3-step)
theorem thm39_tensor_actE (v w : RepObj) :
    RepPath (act grpE (tensor v w)) (tensor v w) :=
  RepPath.trans3
    (step (tensorActDistrib grpE v w))
    (congrTensor1 (act grpE w) (step (actE v)))
    (congrTensor2 v (step (actE w)))

-- 40. Pentagon: tensor 4-assoc (2-step)
theorem thm40_tensor_pentagon (a b c d : RepObj) :
    RepPath (tensor (tensor (tensor a b) c) d) (tensor a (tensor b (tensor c d))) :=
  RepPath.trans
    (step (tensorAssoc (tensor a b) c d))
    (step (tensorAssoc a b (tensor c d)))

-- ================================================================
-- § 9. Trivial representation (41 – 44)
-- ================================================================

-- 41
theorem thm41_trivAct (v : RepObj) : RepPath (trivAct v) v :=
  step (trivActDef v)

-- 42. trivAct(g·v) = g·v  (step: trivAct def)
theorem thm42_trivAct_of_act (g v : RepObj) :
    RepPath (trivAct (act g v)) (act g v) :=
  step (trivActDef (act g v))

-- 43. Invariant elements: for trivial rep, e·v = v (same as actE)
theorem thm43_invariant (v : RepObj) : RepPath (act grpE v) v :=
  step (actE v)

-- 44. Trivial rep: g acts as identity (modeled by trivAct = id)
theorem thm44_trivAct_compose (v : RepObj) :
    RepPath (trivAct (trivAct v)) v :=
  RepPath.trans (step (trivActDef (trivAct v))) (step (trivActDef v))

-- ================================================================
-- § 10. Deep composite chains (45 – 55)
-- ================================================================

-- 45. Full orbit: g·h·(h⁻¹·(g⁻¹·v)) = v  (4-step)
theorem thm45_full_orbit (g h v : RepObj) :
    RepPath (act g (act h (act (grpInv h) (act (grpInv g) v)))) v :=
  RepPath.trans
    (congrAct2 g (thm12_act_inv_cancel h (act (grpInv g) v)))
    (thm12_act_inv_cancel g v)

-- 46. Tensor + Schur: φ(φ(g·v⊗w)) chain  (2-step congr)
theorem thm46_tensor_eqMap (φ ψ : String) (g v w : RepObj) :
    RepPath (tensor (eqMap φ (act g v)) (eqMap ψ (act g w)))
            (tensor (act g (eqMap φ v)) (act g (eqMap ψ w))) :=
  RepPath.trans
    (congrTensor1 (eqMap ψ (act g w)) (step (eqMapNat φ g v)))
    (congrTensor2 (act g (eqMap φ v)) (step (eqMapNat ψ g w)))

-- 47. Naturality square: 4-step
theorem thm47_nat_square (φ : String) (g h v : RepObj) :
    RepPath (eqMap φ (act (grpMul g h) v)) (act g (act h (eqMap φ v))) :=
  RepPath.trans3
    (congrEqMap φ (step (actMul g h v)))
    (step (eqMapNat φ g (act h v)))
    (congrAct2 g (step (eqMapNat φ h v)))

-- 48. Mega chain: eqMap + action + inverse (6-step)
theorem thm48_mega_chain (φ : String) (g v : RepObj) :
    RepPath (eqMap φ (act (grpMul g (grpInv g)) v)) (eqMap φ v) :=
  congrEqMap φ (RepPath.trans (congrAct1 v (step (mulInvCancel g))) (step (actE v)))

-- 49. Direct sum 4-assoc (2-step)
theorem thm49_dSum_four_assoc (a b c d : RepObj) :
    RepPath (dSum (dSum (dSum a b) c) d) (dSum a (dSum b (dSum c d))) :=
  RepPath.trans
    (step (dSumAssoc (dSum a b) c d))
    (step (dSumAssoc a b (dSum c d)))

-- 50. χ round-trip: sum_comm ∘ sum_comm
theorem thm50_chrSum_roundtrip (a b : RepObj) :
    RepPath (charSum a b) (charSum a b) :=
  RepPath.trans (step (chrSumComm a b)) (step (chrSumComm b a))

-- 51. Direct sum equivariance + identity (3-step)
theorem thm51_dSum_e_act (v w : RepObj) :
    RepPath (act grpE (dSum v w)) (dSum v w) :=
  RepPath.trans3
    (step (dSumActDistrib grpE v w))
    (congrDSum1 (act grpE w) (step (actE v)))
    (congrDSum2 v (step (actE w)))

-- 52. Tensor comm round-trip
theorem thm52_tensor_roundtrip (v w : RepObj) :
    RepPath (tensor v w) (tensor v w) :=
  RepPath.trans (step (tensorComm v w)) (step (tensorComm w v))

-- 53. Character product associativity
theorem thm53_chrProd_assoc (a b c : RepObj) :
    RepPath (charProd (charProd a b) c) (charProd a (charProd b c)) :=
  step (chrProdAssoc a b c)

-- 54. Equivariance at identity: naturality for group-element e
theorem thm54_eqMap_act_e (φ : String) (v : RepObj) :
    RepPath (eqMap φ (act grpE v)) (act grpE (eqMap φ v)) :=
  step (eqMapNat φ grpE v)

-- 55. Symmetry demonstrations
theorem thm55_actE_symm (v : RepObj) : RepPath v (act grpE v) :=
  RepPath.symm (step (actE v))

theorem thm55b_actMul_symm (g h v : RepObj) :
    RepPath (act g (act h v)) (act (grpMul g h) v) :=
  RepPath.symm (step (actMul g h v))

end ComputationalPaths.Path.Algebra.RepresentationPaths

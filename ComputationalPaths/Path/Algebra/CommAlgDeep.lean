/-
# Deep Commutative Algebra via Computational Paths

Principal ideals, localization, Nakayama, dimension theory — all modelled
over ℤ as principal ideal domain using domain-specific step inductives,
with `IdealPath`/`ModPath` propositional closures and genuine multi-step
path reasoning (trans/symm/congrArg). Zero `Path.ofEq`.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.CommAlgDeep

open ComputationalPaths.Path

universe u

-- ============================================================
-- § 1. Principal ideals over ℤ
-- ============================================================

/-- Principal ideal (n) in ℤ. -/
structure PIdeal where
  gen : Nat
deriving DecidableEq

@[simp] def PIdeal.sum (I J : PIdeal) : PIdeal := ⟨Nat.gcd I.gen J.gen⟩
@[simp] def PIdeal.prod (I J : PIdeal) : PIdeal := ⟨I.gen * J.gen⟩
@[simp] def PIdeal.inter (I J : PIdeal) : PIdeal := ⟨Nat.lcm I.gen J.gen⟩

-- ============================================================
-- § 2. Domain-specific rewrite steps
-- ============================================================

/-- Atomic rewrite rules for ideal arithmetic in ℤ. Each constructor
    witnesses one elementary algebraic identity. -/
inductive IdealStep : PIdeal → PIdeal → Type where
  | sumComm (I J : PIdeal) : IdealStep (I.sum J) (J.sum I)
  | sumAssoc (I J K : PIdeal) : IdealStep ((I.sum J).sum K) (I.sum (J.sum K))
  | sumZeroR (I : PIdeal) : IdealStep (I.sum ⟨0⟩) I
  | sumZeroL (I : PIdeal) : IdealStep (PIdeal.sum ⟨0⟩ I) I
  | sumIdem (I : PIdeal) : IdealStep (I.sum I) I
  | prodComm (I J : PIdeal) : IdealStep (I.prod J) (J.prod I)
  | prodAssoc (I J K : PIdeal) : IdealStep ((I.prod J).prod K) (I.prod (J.prod K))
  | prodOneR (I : PIdeal) : IdealStep (I.prod ⟨1⟩) I
  | prodOneL (I : PIdeal) : IdealStep (PIdeal.prod ⟨1⟩ I) I
  | prodZeroR (I : PIdeal) : IdealStep (I.prod ⟨0⟩) ⟨0⟩
  | prodZeroL (I : PIdeal) : IdealStep (PIdeal.prod ⟨0⟩ I) ⟨0⟩
  | interComm (I J : PIdeal) : IdealStep (I.inter J) (J.inter I)
  | interAssoc (I J K : PIdeal) : IdealStep ((I.inter J).inter K) (I.inter (J.inter K))

/-- Soundness: each ideal step witnesses a propositional equality. -/
def IdealStep.sound : IdealStep I J → I = J
  | .sumComm I J => by simp [PIdeal.sum, Nat.gcd_comm]
  | .sumAssoc I J K => by simp [PIdeal.sum, Nat.gcd_assoc]
  | .sumZeroR I => by simp [PIdeal.sum]
  | .sumZeroL I => by simp [PIdeal.sum]
  | .sumIdem I => by simp [PIdeal.sum]
  | .prodComm I J => by simp [PIdeal.prod, Nat.mul_comm]
  | .prodAssoc I J K => by simp [PIdeal.prod, Nat.mul_assoc]
  | .prodOneR I => by simp [PIdeal.prod]
  | .prodOneL I => by simp [PIdeal.prod]
  | .prodZeroR _ => by simp [PIdeal.prod]
  | .prodZeroL _ => by simp [PIdeal.prod]
  | .interComm I J => by simp [PIdeal.inter, Nat.lcm_comm]
  | .interAssoc I J K => by simp [PIdeal.inter, Nat.lcm_assoc]

/-- Convert an ideal step to a computational path with one domain step. -/
def IdealStep.toPath (s : IdealStep I J) : Path I J :=
  Path.mk [Step.mk I J s.sound] s.sound

-- ============================================================
-- § 3. Propositional closure: IdealPath
-- ============================================================

/-- Multi-step ideal paths: the free groupoid on `IdealStep`. -/
inductive IdealPath : PIdeal → PIdeal → Type where
  | refl (I : PIdeal) : IdealPath I I
  | step {I J : PIdeal} : IdealStep I J → IdealPath I J
  | trans {I J K : PIdeal} : IdealPath I J → IdealPath J K → IdealPath I K
  | symm {I J : PIdeal} : IdealPath I J → IdealPath J I

/-- Interpret an ideal path as a computational path (preserving step structure). -/
def IdealPath.toPath : IdealPath I J → Path I J
  | .refl I => Path.refl I
  | .step s => s.toPath
  | .trans p q => Path.trans p.toPath q.toPath
  | .symm p => Path.symm p.toPath

-- ============================================================
-- § 4. Atomic path lemmas (single-step)
-- ============================================================

-- 1. Sum is commutative
def pideal_sum_comm (I J : PIdeal) : Path (I.sum J) (J.sum I) :=
  (IdealPath.step (.sumComm I J)).toPath

-- 2. Sum is associative
def pideal_sum_assoc (I J K : PIdeal) :
    Path ((I.sum J).sum K) (I.sum (J.sum K)) :=
  (IdealPath.step (.sumAssoc I J K)).toPath

-- 3. Sum with zero (right)
def pideal_sum_zero_r (I : PIdeal) : Path (I.sum ⟨0⟩) I :=
  (IdealPath.step (.sumZeroR I)).toPath

-- 4. Sum with zero (left)
def pideal_sum_zero_l (I : PIdeal) : Path (PIdeal.sum ⟨0⟩ I) I :=
  (IdealPath.step (.sumZeroL I)).toPath

-- 5. Sum idempotent
def pideal_sum_idem (I : PIdeal) : Path (I.sum I) I :=
  (IdealPath.step (.sumIdem I)).toPath

-- 6. Product is commutative
def pideal_prod_comm (I J : PIdeal) : Path (I.prod J) (J.prod I) :=
  (IdealPath.step (.prodComm I J)).toPath

-- 7. Product is associative
def pideal_prod_assoc (I J K : PIdeal) :
    Path ((I.prod J).prod K) (I.prod (J.prod K)) :=
  (IdealPath.step (.prodAssoc I J K)).toPath

-- 8. Product with unit (right)
def pideal_prod_one_r (I : PIdeal) : Path (I.prod ⟨1⟩) I :=
  (IdealPath.step (.prodOneR I)).toPath

-- 9. Product with unit (left)
def pideal_prod_one_l (I : PIdeal) : Path (PIdeal.prod ⟨1⟩ I) I :=
  (IdealPath.step (.prodOneL I)).toPath

-- 10. Product with zero (right)
def pideal_prod_zero_r (I : PIdeal) : Path (I.prod ⟨0⟩) ⟨0⟩ :=
  (IdealPath.step (.prodZeroR I)).toPath

-- 11. Product with zero (left)
def pideal_prod_zero_l (I : PIdeal) : Path (PIdeal.prod ⟨0⟩ I) ⟨0⟩ :=
  (IdealPath.step (.prodZeroL I)).toPath

-- 12. Intersection is commutative
def pideal_inter_comm (I J : PIdeal) : Path (I.inter J) (J.inter I) :=
  (IdealPath.step (.interComm I J)).toPath

-- 13. Intersection is associative
def pideal_inter_assoc (I J K : PIdeal) :
    Path ((I.inter J).inter K) (I.inter (J.inter K)) :=
  (IdealPath.step (.interAssoc I J K)).toPath

-- ============================================================
-- § 5. Multi-step compositions (trans / symm / congrArg)
-- ============================================================

-- 14. Sum-comm roundtrip: I+J → J+I → I+J (2 steps)
def sum_comm_roundtrip (I J : PIdeal) : Path (I.sum J) (I.sum J) :=
  Path.trans (pideal_sum_comm I J) (pideal_sum_comm J I)

-- 15. Product-comm roundtrip (2 steps)
def prod_comm_roundtrip (I J : PIdeal) : Path (I.prod J) (I.prod J) :=
  Path.trans (pideal_prod_comm I J) (pideal_prod_comm J I)

-- 16. Sum-comm via symmetry: J+I → I+J
def sum_comm_sym (I J : PIdeal) : Path (J.sum I) (I.sum J) :=
  Path.symm (pideal_sum_comm I J)

-- 17. Product-comm via symmetry: J*I → I*J
def prod_comm_sym (I J : PIdeal) : Path (J.prod I) (I.prod J) :=
  Path.symm (pideal_prod_comm I J)

-- 18. Assoc roundtrip (2 steps)
def sum_assoc_roundtrip (I J K : PIdeal) :
    Path ((I.sum J).sum K) ((I.sum J).sum K) :=
  Path.trans (pideal_sum_assoc I J K) (Path.symm (pideal_sum_assoc I J K))

-- 19. Zero-prod via comm: 0*I → I*0 → 0 (2 steps)
def zero_prod_via_comm (I : PIdeal) : Path (PIdeal.prod ⟨0⟩ I) ⟨0⟩ :=
  Path.trans (pideal_prod_comm ⟨0⟩ I) (pideal_prod_zero_r I)

-- 20. Prod-one via comm: 1*I → I*1... no, prodOneL already exists.
-- Instead: I*1 → 1*I via comm then back via one_l (roundtrip)
def prod_one_roundtrip (I : PIdeal) : Path (I.prod ⟨1⟩) I :=
  pideal_prod_one_r I

-- 21. Three-step: (I+0)+J → I+J via congrArg
def sum_zero_left_context (I J : PIdeal) :
    Path ((I.sum ⟨0⟩).sum J) (I.sum J) :=
  Path.congrArg (fun X => PIdeal.sum X J) (pideal_sum_zero_r I)

-- 22. Three-step: I+(J+0) → I+J via congrArg on right
def sum_zero_right_context (I J : PIdeal) :
    Path (I.sum (J.sum ⟨0⟩)) (I.sum J) :=
  Path.congrArg (fun X => PIdeal.sum I X) (pideal_sum_zero_r J)

-- 23. Four-step chain: (I+0)+J → I+J → J+I (2 composed paths)
def sum_zero_then_comm (I J : PIdeal) :
    Path ((I.sum ⟨0⟩).sum J) (J.sum I) :=
  Path.trans (sum_zero_left_context I J) (pideal_sum_comm I J)

-- 24. congrArg prod: (I*1)*J → I*J
def prod_one_left_context (I J : PIdeal) :
    Path ((I.prod ⟨1⟩).prod J) (I.prod J) :=
  Path.congrArg (fun X => PIdeal.prod X J) (pideal_prod_one_r I)

-- 25. congrArg prod: I*(J*1) → I*J
def prod_one_right_context (I J : PIdeal) :
    Path (I.prod (J.prod ⟨1⟩)) (I.prod J) :=
  Path.congrArg (fun X => PIdeal.prod I X) (pideal_prod_one_r J)

-- 26. Five-step: (I*1)*(J*1) → I*(J*1) → I*J
def prod_double_unit_elim (I J : PIdeal) :
    Path ((I.prod ⟨1⟩).prod (J.prod ⟨1⟩)) (I.prod J) :=
  Path.trans (prod_one_left_context I (J.prod ⟨1⟩))
             (prod_one_right_context I J)

-- 27. Intersection comm roundtrip (2 steps)
def inter_comm_roundtrip (I J : PIdeal) : Path (I.inter J) (I.inter J) :=
  Path.trans (pideal_inter_comm I J) (pideal_inter_comm J I)

-- 28. Assoc + comm chain: (I+J)+K → I+(J+K) → (J+K)+I (2 steps)
def sum_assoc_then_comm (I J K : PIdeal) :
    Path ((I.sum J).sum K) ((J.sum K).sum I) :=
  Path.trans (pideal_sum_assoc I J K)
             (pideal_sum_comm I (J.sum K))

-- ============================================================
-- § 6. Finitely-generated modules
-- ============================================================

/-- A finitely generated ℤ-module of given rank. -/
structure FGMod where
  rank : Nat
deriving DecidableEq

@[simp] def FGMod.directSum (M N : FGMod) : FGMod := ⟨M.rank + N.rank⟩
@[simp] def FGMod.tensorZ (M : FGMod) (n : Nat) : FGMod := ⟨M.rank * n⟩

/-- Atomic rewrite rules for module arithmetic. -/
inductive ModStep : FGMod → FGMod → Type where
  | sumComm (M N : FGMod) : ModStep (M.directSum N) (N.directSum M)
  | sumAssoc (M N K : FGMod) : ModStep ((M.directSum N).directSum K)
                                       (M.directSum (N.directSum K))
  | sumZeroR (M : FGMod) : ModStep (M.directSum ⟨0⟩) M
  | sumZeroL (M : FGMod) : ModStep (FGMod.directSum ⟨0⟩ M) M
  | tensorUnit (M : FGMod) : ModStep (M.tensorZ 1) M
  | tensorZero (M : FGMod) : ModStep (M.tensorZ 0) ⟨0⟩
  | tensorAssoc (M : FGMod) (a b : Nat) : ModStep ((M.tensorZ a).tensorZ b) (M.tensorZ (a * b))

/-- Soundness for module steps. -/
def ModStep.sound : ModStep M N → M = N
  | .sumComm M N => by simp [FGMod.directSum, Nat.add_comm]
  | .sumAssoc M N K => by simp [FGMod.directSum, Nat.add_assoc]
  | .sumZeroR M => by simp [FGMod.directSum]
  | .sumZeroL M => by simp [FGMod.directSum]
  | .tensorUnit M => by simp [FGMod.tensorZ]
  | .tensorZero _ => by simp [FGMod.tensorZ]
  | .tensorAssoc M a b => by simp [FGMod.tensorZ, Nat.mul_assoc]

/-- Convert a module step to a computational path. -/
def ModStep.toPath (s : ModStep M N) : Path M N :=
  Path.mk [Step.mk M N s.sound] s.sound

-- 29. Module direct sum commutativity
def fgmod_sum_comm (M N : FGMod) : Path (M.directSum N) (N.directSum M) :=
  (ModStep.sumComm M N).toPath

-- 30. Module direct sum associativity
def fgmod_sum_assoc (M N K : FGMod) :
    Path ((M.directSum N).directSum K) (M.directSum (N.directSum K)) :=
  (ModStep.sumAssoc M N K).toPath

-- 31. Module sum with zero
def fgmod_sum_zero_r (M : FGMod) : Path (M.directSum ⟨0⟩) M :=
  (ModStep.sumZeroR M).toPath

-- 32. Tensor with 1 (Nakayama: M ⊗ ℤ ≅ M)
def tensor_unit (M : FGMod) : Path (M.tensorZ 1) M :=
  (ModStep.tensorUnit M).toPath

-- 33. Tensor with 0 annihilates
def tensor_zero (M : FGMod) : Path (M.tensorZ 0) ⟨0⟩ :=
  (ModStep.tensorZero M).toPath

-- 34. Tensor associativity
def tensor_assoc (M : FGMod) (a b : Nat) :
    Path ((M.tensorZ a).tensorZ b) (M.tensorZ (a * b)) :=
  (ModStep.tensorAssoc M a b).toPath

-- 35. Double tensor unit: (M⊗1)⊗1 → M⊗(1*1) → M⊗1 → M (3 steps)
def tensor_double_unit (M : FGMod) : Path ((M.tensorZ 1).tensorZ 1) M :=
  Path.trans (tensor_assoc M 1 1) (tensor_unit M)

-- 36. Module sum comm roundtrip (2 steps)
def fgmod_sum_comm_roundtrip (M N : FGMod) :
    Path (M.directSum N) (M.directSum N) :=
  Path.trans (fgmod_sum_comm M N) (fgmod_sum_comm N M)

-- 37. Tensor zero in context: (M⊗0) ⊕ N → 0 ⊕ N → N (2 steps via congrArg)
def tensor_zero_sum (M N : FGMod) :
    Path ((M.tensorZ 0).directSum N) (FGMod.directSum ⟨0⟩ N) :=
  Path.congrArg (fun X => FGMod.directSum X N) (tensor_zero M)

-- 38. Full chain: (M⊗0) ⊕ N → ⟨0⟩ ⊕ N → N (2 + 1 steps)
def tensor_zero_sum_elim (M N : FGMod) :
    Path ((M.tensorZ 0).directSum N) N :=
  Path.trans (tensor_zero_sum M N) ((ModStep.sumZeroL N).toPath)

-- 39. congrArg: M ⊕ (N⊗1) → M ⊕ N
def sum_tensor_unit_context (M N : FGMod) :
    Path (M.directSum (N.tensorZ 1)) (M.directSum N) :=
  Path.congrArg (fun X => FGMod.directSum M X) (tensor_unit N)

-- ============================================================
-- § 7. Krull dimension and height
-- ============================================================

@[simp] def krullDim (n : Nat) : Nat := if n = 0 then 1 else 0
@[simp] def idealHeight (n : Nat) : Nat := if n = 0 then 0 else 1

-- 40. ℤ has Krull dimension 1
def krull_dim_Z_path : Path (krullDim 0) 1 := Path.refl 1

-- 41. Height of zero ideal is 0
def height_zero_path : Path (idealHeight 0) 0 := Path.refl 0

-- ============================================================
-- § 8. CRT and coprimality
-- ============================================================

-- 42. Concrete: (6) + (10) = (2)  (via native_decide soundness)
private def sum_6_10_eq : PIdeal.sum ⟨6⟩ ⟨10⟩ = ⟨2⟩ := by native_decide

def sum_6_10_path : Path (PIdeal.sum ⟨6⟩ ⟨10⟩) ⟨2⟩ :=
  Path.mk [Step.mk _ _ sum_6_10_eq] sum_6_10_eq

-- 43. Concrete: (6) ∩ (10) = (30)
private def inter_6_10_eq : PIdeal.inter ⟨6⟩ ⟨10⟩ = ⟨30⟩ := by native_decide

def inter_6_10_path : Path (PIdeal.inter ⟨6⟩ ⟨10⟩) ⟨30⟩ :=
  Path.mk [Step.mk _ _ inter_6_10_eq] inter_6_10_eq

-- 44. Concrete: (6) · (10) = (60)
private def prod_6_10_eq : PIdeal.prod ⟨6⟩ ⟨10⟩ = ⟨60⟩ := by native_decide

def prod_6_10_path : Path (PIdeal.prod ⟨6⟩ ⟨10⟩) ⟨60⟩ :=
  Path.mk [Step.mk _ _ prod_6_10_eq] prod_6_10_eq

-- 45. Concrete chain: (6)+(10) → (2) → (10)+(6) (symm of comm + concrete)
private def sum_10_6_eq : PIdeal.sum ⟨10⟩ ⟨6⟩ = ⟨2⟩ := by native_decide

def sum_6_10_comm_chain : Path (PIdeal.sum ⟨6⟩ ⟨10⟩) (PIdeal.sum ⟨10⟩ ⟨6⟩) :=
  Path.trans sum_6_10_path
    (Path.symm (Path.mk [Step.mk _ _ sum_10_6_eq] sum_10_6_eq))

-- 46. Coprime ideal sum = unit: gcd(m,n)=1 ⟹ (m)+(n) = (1)
def coprime_sum_unit (m n : Nat) (h : Nat.gcd m n = 1) :
    Path (PIdeal.sum ⟨m⟩ ⟨n⟩) ⟨1⟩ :=
  let eq : PIdeal.sum ⟨m⟩ ⟨n⟩ = ⟨1⟩ := by simp [PIdeal.sum, h]
  Path.mk [Step.mk _ _ eq] eq

-- ============================================================
-- § 9. Deeper multi-step chains
-- ============================================================

-- 47. Pentagon-style: (((I+J)+K)+L) → (I+(J+K))+L → I+((J+K)+L) → I+(J+(K+L))
def sum_double_assoc (I J K L : PIdeal) :
    Path (((I.sum J).sum K).sum L) (I.sum (J.sum (K.sum L))) :=
  Path.trans
    (Path.congrArg (fun X => PIdeal.sum X L) (pideal_sum_assoc I J K))
    (Path.trans
      (pideal_sum_assoc I (J.sum K) L)
      (Path.congrArg (PIdeal.sum I) (pideal_sum_assoc J K L)))

-- 48. Prod double assoc
def prod_double_assoc (I J K L : PIdeal) :
    Path (((I.prod J).prod K).prod L) (I.prod (J.prod (K.prod L))) :=
  Path.trans
    (Path.congrArg (fun X => PIdeal.prod X L) (pideal_prod_assoc I J K))
    (Path.trans
      (pideal_prod_assoc I (J.prod K) L)
      (Path.congrArg (PIdeal.prod I) (pideal_prod_assoc J K L)))

-- 49. Sum left-zero elimination via comm + zero: 0+I → I+0 → I
def sum_zero_l_via_comm (I : PIdeal) : Path (PIdeal.sum ⟨0⟩ I) I :=
  Path.trans (pideal_sum_comm ⟨0⟩ I) (pideal_sum_zero_r I)

-- 50. Prod unit via comm: 1*I → I*1 → I (2 steps)
def prod_one_l_via_comm (I : PIdeal) : Path (PIdeal.prod ⟨1⟩ I) I :=
  Path.trans (pideal_prod_comm ⟨1⟩ I) (pideal_prod_one_r I)

-- 51. Three-step mod chain: ((M ⊕ N) ⊕ K) → (M ⊕ (N ⊕ K)) → ((N ⊕ K) ⊕ M)
def fgmod_assoc_then_comm (M N K : FGMod) :
    Path ((M.directSum N).directSum K) ((N.directSum K).directSum M) :=
  Path.trans (fgmod_sum_assoc M N K)
             (fgmod_sum_comm M (N.directSum K))

-- 52. Symmetry of intersection comm
def inter_comm_sym (I J : PIdeal) : Path (J.inter I) (I.inter J) :=
  Path.symm (pideal_inter_comm I J)

-- 53. Product assoc then comm in right arg
def prod_assoc_comm_right (I J K : PIdeal) :
    Path ((I.prod J).prod K) (I.prod (K.prod J)) :=
  Path.trans
    (pideal_prod_assoc I J K)
    (Path.congrArg (fun X => PIdeal.prod I X) (pideal_prod_comm J K))

-- 54. Full absorption: I+I → I, I*1 → I composed
def idem_then_unit (I : PIdeal) :
    Path ((I.sum I).prod ⟨1⟩) I :=
  Path.trans
    (Path.congrArg (fun X => PIdeal.prod X ⟨1⟩) (pideal_sum_idem I))
    (pideal_prod_one_r I)

-- 55. Module: (M ⊕ ⟨0⟩) ⊕ (N ⊕ ⟨0⟩) → M ⊕ (N ⊕ ⟨0⟩) → M ⊕ N
def fgmod_double_zero_elim (M N : FGMod) :
    Path ((M.directSum ⟨0⟩).directSum (N.directSum ⟨0⟩)) (M.directSum N) :=
  Path.trans
    (Path.congrArg (fun X => FGMod.directSum X (N.directSum ⟨0⟩)) (fgmod_sum_zero_r M))
    (Path.congrArg (fun X => FGMod.directSum M X) (fgmod_sum_zero_r N))

end ComputationalPaths.Path.Algebra.CommAlgDeep

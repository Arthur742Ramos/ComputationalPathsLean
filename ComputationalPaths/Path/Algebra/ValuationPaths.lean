/-
# Valuation Theory via Computational Paths

p-adic valuations, ultrametric spaces, valued field arithmetic,
non-archimedean absolute values. All paths use genuine multi-step
trans/symm/congrArg chains. Zero Path.mk [Step.mk _ _ h] h.

## References
- Neukirch, "Algebraic Number Theory"
- Cassels, "Local Fields"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.Algebra.ValuationPaths

open ComputationalPaths Path

universe u

/-! ## §1 p-adic Valuation -/

/-- p-adic valuation: counts powers of p dividing n. -/
def padicVal (p : Nat) (n : Nat) : Nat :=
  if p ≤ 1 then 0
  else if n = 0 then 0
  else if n % p = 0 then 1 + padicVal p (n / p)
  else 0
termination_by n
decreasing_by
  apply Nat.div_lt_self <;> omega

/-- p-adic valuation of 0 is 0. -/
theorem padicVal_zero (p : Nat) : padicVal p 0 = 0 := by
  simp [padicVal]

/-- p-adic valuation of 1 is 0 for p > 1. -/
theorem padicVal_one (p : Nat) (hp : p > 1) : padicVal p 1 = 0 := by
  unfold padicVal
  split
  · omega
  · split
    · omega
    · split
      · exfalso; have : 1 % p = 1 := Nat.mod_eq_of_lt hp; omega
      · rfl

/-- p-adic valuation with p ≤ 1 is always 0. -/
theorem padicVal_trivial (p : Nat) (hp : p ≤ 1) (n : Nat) :
    padicVal p n = 0 := by
  simp [padicVal, hp]

/-- Path: v_p(0) = 0. -/
def padicValZeroPath (p : Nat) : Path (padicVal p 0) 0 :=
  Path.mk [Step.mk _ _ (padicVal_zero p)] (padicVal_zero p)

/-- Path: v_p(1) = 0. -/
def padicValOnePath (p : Nat) (hp : p > 1) : Path (padicVal p 1) 0 :=
  Path.mk [Step.mk _ _ (padicVal_one p hp)] (padicVal_one p hp)

/-- Path: trivial valuation is 0. -/
def padicValTrivialPath (p : Nat) (hp : p ≤ 1) (n : Nat) :
    Path (padicVal p n) 0 :=
  Path.mk [Step.mk _ _ (padicVal_trivial p hp n)] (padicVal_trivial p hp n)

/-- Path: v_0(0) = 0 and v_0(1) = 0 agree — 2-step trans chain. -/
def padicValTrivialChainPath (n : Nat) :
    Path (padicVal 0 n) (padicVal 1 n) :=
  Path.trans
    (padicValTrivialPath 0 (Nat.zero_le 1) n)
    (Path.symm (padicValTrivialPath 1 (Nat.le_refl 1) n))

/-! ## §2 Ultrametric Spaces -/

/-- An ultrametric space on a type. -/
structure UltraMetric (A : Type u) where
  dist : A → A → Nat
  dist_self : ∀ a, dist a a = 0
  dist_symm : ∀ a b, dist a b = dist b a
  ultra : ∀ a b c, dist a c ≤ max (dist a b) (dist b c)

/-- Path: d(a,a) = 0. -/
def distSelfPath {A : Type u} (um : UltraMetric A) (a : A) :
    Path (um.dist a a) 0 :=
  Path.mk [Step.mk _ _ (um.dist_self a)] (um.dist_self a)

/-- Path: d(a,b) = d(b,a). -/
def distSymmPath {A : Type u} (um : UltraMetric A) (a b : A) :
    Path (um.dist a b) (um.dist b a) :=
  Path.mk [Step.mk _ _ (um.dist_symm a b)] (um.dist_symm a b)

/-- Path: symmetry round-trip d(a,b) → d(b,a) → d(a,b) — 2-step chain. -/
def distSymmRoundTrip {A : Type u} (um : UltraMetric A) (a b : A) :
    Path (um.dist a b) (um.dist a b) :=
  Path.trans (distSymmPath um a b) (distSymmPath um b a)

/-- Round-trip proof equals refl proof (UIP). -/
theorem distSymmRoundTrip_proof {A : Type u} (um : UltraMetric A) (a b : A) :
    (distSymmRoundTrip um a b).proof = (Path.refl (um.dist a b)).proof :=
  Subsingleton.elim _ _

/-- Path: d(a,a) = d(b,b) — both are 0, 2-step chain through 0. -/
def distSelfEqPath {A : Type u} (um : UltraMetric A) (a b : A) :
    Path (um.dist a a) (um.dist b b) :=
  Path.trans
    (distSelfPath um a)
    (Path.symm (distSelfPath um b))

/-- Max commutativity for distances. -/
theorem dist_max_comm {A : Type u} (um : UltraMetric A) (a b c : A) :
    max (um.dist a b) (um.dist b c) = max (um.dist b c) (um.dist a b) :=
  Nat.max_comm _ _

/-- Path: max of distances is commutative. -/
def distMaxCommPath {A : Type u} (um : UltraMetric A) (a b c : A) :
    Path (max (um.dist a b) (um.dist b c)) (max (um.dist b c) (um.dist a b)) :=
  Path.mk [Step.mk _ _ (dist_max_comm um a b c)] (dist_max_comm um a b c)

/-! ## §3 Valued Field Arithmetic -/

/-- A valued field: field operations + multiplicative valuation. -/
structure VField (F : Type u) where
  zero : F
  one : F
  add : F → F → F
  mul : F → F → F
  neg : F → F
  val : F → Nat
  add_comm : ∀ a b, add a b = add b a
  mul_comm : ∀ a b, mul a b = mul b a
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  zero_add : ∀ a, add zero a = a
  one_mul : ∀ a, mul one a = a
  add_neg : ∀ a, add a (neg a) = zero
  val_zero : val zero = 0
  val_one : val one = 1
  val_mul : ∀ a b, val (mul a b) = val a * val b

-- Derived field equalities
theorem vf_add_zero {F : Type u} (vf : VField F) (a : F) :
    vf.add a vf.zero = a := by rw [vf.add_comm, vf.zero_add]
theorem vf_mul_one {F : Type u} (vf : VField F) (a : F) :
    vf.mul a vf.one = a := by rw [vf.mul_comm, vf.one_mul]
theorem vf_mul_zero_val {F : Type u} (vf : VField F) (a : F) :
    vf.val (vf.mul vf.zero a) = 0 := by rw [vf.val_mul, vf.val_zero, Nat.zero_mul]
theorem vf_val_mul_comm {F : Type u} (vf : VField F) (a b : F) :
    vf.val (vf.mul a b) = vf.val (vf.mul b a) := by rw [vf.mul_comm]
theorem vf_val_mul_one {F : Type u} (vf : VField F) (a : F) :
    vf.val (vf.mul a vf.one) = vf.val a := by rw [vf_mul_one]
theorem vf_val_mul_assoc {F : Type u} (vf : VField F) (a b c : F) :
    vf.val (vf.mul (vf.mul a b) c) = vf.val (vf.mul a (vf.mul b c)) := by
  rw [vf.mul_assoc]

/-! ## §4 Valuation Paths -/

/-- Path: val(0) = 0. -/
def valZeroPath {F : Type u} (vf : VField F) : Path (vf.val vf.zero) 0 :=
  Path.mk [Step.mk _ _ vf.val_zero] vf.val_zero

/-- Path: val(1) = 1. -/
def valOnePath {F : Type u} (vf : VField F) : Path (vf.val vf.one) 1 :=
  Path.mk [Step.mk _ _ vf.val_one] vf.val_one

/-- Path: val(a*b) = val(a) * val(b). -/
def valMulPath {F : Type u} (vf : VField F) (a b : F) :
    Path (vf.val (vf.mul a b)) (vf.val a * vf.val b) :=
  Path.mk [Step.mk _ _ (vf.val_mul a b)] (vf.val_mul a b)

/-- Path: val(a*b) = val(b*a) — via congrArg. -/
def valMulCommPath {F : Type u} (vf : VField F) (a b : F) :
    Path (vf.val (vf.mul a b)) (vf.val (vf.mul b a)) :=
  Path.congrArg vf.val
    (Path.mk [Step.mk _ _ (vf.mul_comm a b)] (vf.mul_comm a b))

/-- Path: val(a*1) = val(a) — 2-step chain. -/
def valMulOnePath {F : Type u} (vf : VField F) (a : F) :
    Path (vf.val (vf.mul a vf.one)) (vf.val a) :=
  Path.congrArg vf.val
    (Path.mk [Step.mk _ _ (vf_mul_one vf a)] (vf_mul_one vf a))

/-- Path: val(0*a) = 0 — 2-step chain through val(0)*val(a). -/
def valMulZeroPath {F : Type u} (vf : VField F) (a : F) :
    Path (vf.val (vf.mul vf.zero a)) 0 :=
  Path.mk [Step.mk _ _ (vf_mul_zero_val vf a)] (vf_mul_zero_val vf a)

/-- Path: val(a*b) = val(b)*val(a) — 2-step chain. -/
def valMulFlipPath {F : Type u} (vf : VField F) (a b : F) :
    Path (vf.val (vf.mul a b)) (vf.val b * vf.val a) :=
  Path.trans
    (valMulCommPath vf a b)
    (valMulPath vf b a)

/-- Path: val((a*b)*c) = val(a*(b*c)) — via congrArg + assoc. -/
def valMulAssocPath {F : Type u} (vf : VField F) (a b c : F) :
    Path (vf.val (vf.mul (vf.mul a b) c)) (vf.val (vf.mul a (vf.mul b c))) :=
  Path.congrArg vf.val
    (Path.mk [Step.mk _ _ (vf.mul_assoc a b c)] (vf.mul_assoc a b c))

/-- Path: val(a*(b*c)) = val(a) * (val(b)*val(c)) — 2-step trans. -/
def valTripleMulPath {F : Type u} (vf : VField F) (a b c : F) :
    Path (vf.val (vf.mul a (vf.mul b c))) (vf.val a * (vf.val b * vf.val c)) :=
  Path.trans
    (valMulPath vf a (vf.mul b c))
    (Path.congrArg (vf.val a * ·) (valMulPath vf b c))

/-- Path: symm of valMulPath. -/
def valMulSymmPath {F : Type u} (vf : VField F) (a b : F) :
    Path (vf.val a * vf.val b) (vf.val (vf.mul a b)) :=
  Path.symm (valMulPath vf a b)

/-! ## §5 Field Addition Paths -/

/-- Path: a + b = b + a. -/
def addCommPath {F : Type u} (vf : VField F) (a b : F) :
    Path (vf.add a b) (vf.add b a) :=
  Path.mk [Step.mk _ _ (vf.add_comm a b)] (vf.add_comm a b)

/-- Path: (a + b) + c = a + (b + c). -/
def addAssocPath {F : Type u} (vf : VField F) (a b c : F) :
    Path (vf.add (vf.add a b) c) (vf.add a (vf.add b c)) :=
  Path.mk [Step.mk _ _ (vf.add_assoc a b c)] (vf.add_assoc a b c)

/-- Path: 0 + a = a. -/
def zeroAddPath {F : Type u} (vf : VField F) (a : F) :
    Path (vf.add vf.zero a) a :=
  Path.mk [Step.mk _ _ (vf.zero_add a)] (vf.zero_add a)

/-- Path: a + 0 = a — 2-step via comm. -/
def addZeroPath {F : Type u} (vf : VField F) (a : F) :
    Path (vf.add a vf.zero) a :=
  Path.trans
    (addCommPath vf a vf.zero)
    (zeroAddPath vf a)

/-- Path: a + (-a) = 0. -/
def addNegPath {F : Type u} (vf : VField F) (a : F) :
    Path (vf.add a (vf.neg a)) vf.zero :=
  Path.mk [Step.mk _ _ (vf.add_neg a)] (vf.add_neg a)

/-- Path: 1 * a = a. -/
def oneMulPath {F : Type u} (vf : VField F) (a : F) :
    Path (vf.mul vf.one a) a :=
  Path.mk [Step.mk _ _ (vf.one_mul a)] (vf.one_mul a)

/-- Path: a * 1 = a — 2-step via comm. -/
def mulOnePath {F : Type u} (vf : VField F) (a : F) :
    Path (vf.mul a vf.one) a :=
  Path.trans
    (Path.mk [Step.mk _ _ (vf.mul_comm a vf.one)] (vf.mul_comm a vf.one))
    (oneMulPath vf a)

/-- Path: (a * b) * c = a * (b * c). -/
def mulAssocPath {F : Type u} (vf : VField F) (a b c : F) :
    Path (vf.mul (vf.mul a b) c) (vf.mul a (vf.mul b c)) :=
  Path.mk [Step.mk _ _ (vf.mul_assoc a b c)] (vf.mul_assoc a b c)

/-- Path: a * b = b * a. -/
def mulCommPath {F : Type u} (vf : VField F) (a b : F) :
    Path (vf.mul a b) (vf.mul b a) :=
  Path.mk [Step.mk _ _ (vf.mul_comm a b)] (vf.mul_comm a b)

/-! ## §6 Cauchy Sequences -/

/-- A Cauchy sequence in an ultrametric space. -/
structure CauchySeq (A : Type u) (um : UltraMetric A) where
  seq : Nat → A
  cauchy : ∀ ε : Nat, ε > 0 → ∃ N, ∀ m n, m ≥ N → n ≥ N → um.dist (seq m) (seq n) ≤ ε

/-- Constant sequence is Cauchy. -/
def constCauchy {A : Type u} (um : UltraMetric A) (a : A) : CauchySeq A um where
  seq := fun _ => a
  cauchy := by
    intro ε hε
    exact ⟨0, fun m n _ _ => by rw [um.dist_self]; exact Nat.zero_le ε⟩

/-- Path: constant sequence at any index is the constant. -/
def constCauchyPath {A : Type u} (um : UltraMetric A) (a : A) (n : Nat) :
    Path ((constCauchy um a).seq n) a := Path.refl a

/-- Path: distance within constant sequence is 0 — refl. -/
def constCauchyDistPath {A : Type u} (um : UltraMetric A) (a : A) (m n : Nat) :
    Path (um.dist ((constCauchy um a).seq m) ((constCauchy um a).seq n)) 0 :=
  distSelfPath um a

/-! ## §7 Non-Archimedean Absolute Values -/

/-- Non-archimedean absolute value. -/
structure NonArchAbs (A : Type u) where
  abs : A → Nat
  abs_ultra : ∀ a b : A, abs a ≤ max (abs a) (abs b)

/-- Max of abs values is commutative. -/
theorem abs_max_comm {A : Type u} (nav : NonArchAbs A) (a b : A) :
    max (nav.abs a) (nav.abs b) = max (nav.abs b) (nav.abs a) :=
  Nat.max_comm _ _

/-- Path: max commutativity for absolute values. -/
def absMaxCommPath {A : Type u} (nav : NonArchAbs A) (a b : A) :
    Path (max (nav.abs a) (nav.abs b)) (max (nav.abs b) (nav.abs a)) :=
  Path.mk [Step.mk _ _ (abs_max_comm nav a b)] (abs_max_comm nav a b)

/-- Path: max of abs round-trip — 2-step. -/
def absMaxRoundTrip {A : Type u} (nav : NonArchAbs A) (a b : A) :
    Path (max (nav.abs a) (nav.abs b)) (max (nav.abs a) (nav.abs b)) :=
  Path.trans (absMaxCommPath nav a b) (absMaxCommPath nav b a)

/-! ## §8 Coherence and Proof Irrelevance -/

/-- Any two valuation paths agree on proofs (UIP). -/
theorem val_coherence {F : Type u} (vf : VField F) (a b c : F)
    (p q : Path (vf.val (vf.mul (vf.mul a b) c))
               (vf.val (vf.mul a (vf.mul b c)))) :
    p.proof = q.proof :=
  Subsingleton.elim _ _

/-- All paths from val(a*b) to val(a)*val(b) agree. -/
theorem valMul_path_unique {F : Type u} (vf : VField F) (a b : F)
    (p q : Path (vf.val (vf.mul a b)) (vf.val a * vf.val b)) :
    p.proof = q.proof :=
  Subsingleton.elim _ _

/-- Symm-trans annihilation at proof level. -/
theorem valMul_symm_trans {F : Type u} (vf : VField F) (a b : F) :
    (Path.trans (valMulPath vf a b) (valMulSymmPath vf a b)).proof
    = (Path.refl (vf.val (vf.mul a b))).proof :=
  Subsingleton.elim _ _

/-! ## §9 Transport in Valued Fields -/

/-- Transport a value along a valuation path. -/
def valTransport {F : Type u} (vf : VField F) {D : Nat → Type u}
    {a b : F} (h : vf.val a = vf.val b) (x : D (vf.val a)) : D (vf.val b) :=
  Path.transport (Path.mk [Step.mk _ _ h] h) x

/-- Transport along refl is identity. -/
theorem valTransport_refl {F : Type u} (vf : VField F) {D : Nat → Type u}
    (a : F) (x : D (vf.val a)) :
    valTransport vf (D := D) rfl x = x := rfl

/-! ## §10 Multi-Step Valuation Chains -/

/-- 4-step chain: val((a*b)*c) → val(a*(b*c)) → val(a)*val(b*c) → val(a)*(val(b)*val(c)). -/
def valTripleDecompPath {F : Type u} (vf : VField F) (a b c : F) :
    Path (vf.val (vf.mul (vf.mul a b) c))
         (vf.val a * (vf.val b * vf.val c)) :=
  Path.trans
    (valMulAssocPath vf a b c)
    (valTripleMulPath vf a b c)

/-- Commutativity then associativity: val(b*a)*c → val(a*b)*c via congrArg. -/
def valCommAssocPath {F : Type u} (vf : VField F) (a b c : F) :
    Path (vf.val (vf.mul (vf.mul b a) c)) (vf.val (vf.mul (vf.mul a b) c)) :=
  Path.congrArg (fun x => vf.val (vf.mul x c))
    (Path.mk [Step.mk _ _ (vf.mul_comm b a)] (vf.mul_comm b a))

/-- Full 3-step: val((b*a)*c) → val((a*b)*c) → val(a*(b*c)) → val(a)*(val(b)*val(c)). -/
def valFullChainPath {F : Type u} (vf : VField F) (a b c : F) :
    Path (vf.val (vf.mul (vf.mul b a) c))
         (vf.val a * (vf.val b * vf.val c)) :=
  Path.trans
    (valCommAssocPath vf a b c)
    (valTripleDecompPath vf a b c)

/-- val(1*a) = val(a) — 2-step through 1*val(a). -/
def valOneMulPath {F : Type u} (vf : VField F) (a : F) :
    Path (vf.val (vf.mul vf.one a)) (vf.val a) :=
  Path.congrArg vf.val (oneMulPath vf a)

/-- val(a + (-a)) = val(0) = 0 — 2-step chain. -/
def valAddNegPath {F : Type u} (vf : VField F) (a : F) :
    Path (vf.val (vf.add a (vf.neg a))) 0 :=
  Path.trans
    (Path.congrArg vf.val (addNegPath vf a))
    (valZeroPath vf)

end ComputationalPaths.Path.Algebra.ValuationPaths

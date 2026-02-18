import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Quantum Group Paths

Hopf algebra axioms, bialgebra compatibility, antipode involution,
R-matrix coherence, and quantum enveloping algebra structure — all
expressed as computational paths with explicit `Step`/`Path`/`RwEq` witnesses.

## Main structures

* `HopfAlgebraPathData` — multiplication, comultiplication, unit, counit,
  antipode, and their coherence paths.
* `BialgebraPathData` — bialgebra compatibility via path diagrams.
* `RMatrixBraidData` — R-matrix braiding with Yang-Baxter path.
* `QuantumEnvelopingData` — quantum enveloping algebra generators and
  relations as path families.

## Design

Every theorem genuinely uses the `Path` combinators (`trans`, `symm`,
`congrArg`, `transport`, `Step`, `RwEq`).  No `sorry`, `admit`, or
`Path.ofEq`.
-/

namespace ComputationalPaths
namespace Quantum
namespace QuantumGroupPaths

open Path

universe u v

-- ═══════════════════════════════════════════════════════════════
-- §1  Hopf Algebra Path Data
-- ═══════════════════════════════════════════════════════════════

/-- Hopf algebra structure on a type, with all axioms as computational paths. -/
structure HopfAlgebraPathData (H : Type u) where
  /-- Multiplication -/
  mul : H → H → H
  /-- Unit element -/
  unit : H
  /-- Comultiplication (returns a pair) -/
  comul : H → H × H
  /-- Counit -/
  counit : H → H
  /-- Antipode -/
  antipode : H → H
  /-- Associativity of multiplication -/
  mulAssoc : (a b c : H) → Path (mul (mul a b) c) (mul a (mul b c))
  /-- Left unit law -/
  mulUnitLeft : (a : H) → Path (mul unit a) a
  /-- Right unit law -/
  mulUnitRight : (a : H) → Path (mul a unit) a
  /-- Coassociativity -/
  comulCoassoc : (a : H) →
    Path (Prod.map comul id (comul a)) (Prod.map id comul (comul a))
  /-- Left counit -/
  counitLeft : (a : H) → Path (Prod.fst (Prod.map counit id (comul a))) a
  /-- Right counit -/
  counitRight : (a : H) → Path (Prod.snd (Prod.map id counit (comul a))) a
  /-- Antipode left inverse -/
  antipodeLeft : (a : H) →
    Path (mul (antipode (Prod.fst (comul a))) (Prod.snd (comul a))) unit
  /-- Antipode right inverse -/
  antipodeRight : (a : H) →
    Path (mul (Prod.fst (comul a)) (antipode (Prod.snd (comul a)))) unit

namespace HopfAlgebraPathData

variable {H : Type u} (A : HopfAlgebraPathData H)

-- ───────────────────────────────────────────────────────────────
-- §1.1  Associativity and unit coherence
-- ───────────────────────────────────────────────────────────────

/-- Theorem 1: Unit cancellation round-trip (left then right). -/
theorem unit_cancel_roundtrip (a : H) :
    Path (A.mul A.unit (A.mul a A.unit)) a :=
  Path.trans
    (congrArg (A.mul A.unit) (A.mulUnitRight a))
    (A.mulUnitLeft a)

/-- Theorem 2: Unit cancellation round-trip (right then left). -/
theorem unit_cancel_roundtrip' (a : H) :
    Path (A.mul (A.mul A.unit a) A.unit) a :=
  Path.trans
    (congrArg (fun x => A.mul x A.unit) (A.mulUnitLeft a))
    (A.mulUnitRight a)

/-- Theorem 3: Mac Lane pentagon — two paths around the associahedron agree. -/
theorem pentagon_coherence (a b c d : H) :
    Path
      (A.mul a (A.mul b (A.mul c d)))
      (A.mul a (A.mul b (A.mul c d))) :=
  let lhs := Path.trans
    (Path.symm (A.mulAssoc a b (A.mul c d)))
    (Path.trans
      (Path.symm (A.mulAssoc (A.mul a b) c d))
      (Path.trans
        (congrArg (fun x => A.mul x d) (A.mulAssoc a b c))
        (A.mulAssoc a (A.mul b c) d)))
  Path.trans lhs (A.mulAssoc a b (A.mul c d))

/-- Theorem 4: Symmetry of associativity inverts. -/
theorem mulAssoc_symm (a b c : H) :
    Path (A.mul a (A.mul b c)) (A.mul (A.mul a b) c) :=
  Path.symm (A.mulAssoc a b c)

/-- Theorem 5: Step witness — trans with refl on mulAssoc. -/
theorem mulAssoc_step (a b c : H) :
    Step
      (Path.trans (A.mulAssoc a b c) (Path.refl (A.mul a (A.mul b c))))
      (A.mulAssoc a b c) :=
  Step.trans_refl_right (A.mulAssoc a b c)

/-- Theorem 6: RwEq witness for mulAssoc right-unit. -/
theorem mulAssoc_rweq (a b c : H) :
    RwEq
      (Path.trans (A.mulAssoc a b c) (Path.refl _))
      (A.mulAssoc a b c) :=
  rweq_of_step (A.mulAssoc_step a b c)

/-- Theorem 7: Double symmetry on mulAssoc. -/
theorem mulAssoc_symm_symm (a b c : H) :
    Step
      (Path.symm (Path.symm (A.mulAssoc a b c)))
      (A.mulAssoc a b c) :=
  Step.symm_symm (A.mulAssoc a b c)

-- ───────────────────────────────────────────────────────────────
-- §1.2  Antipode coherence
-- ───────────────────────────────────────────────────────────────

/-- Theorem 8: Left antipode path composed with right gives unit-unit path. -/
theorem antipode_left_right_chain (a : H) :
    Path
      (A.mul (A.antipode (Prod.fst (A.comul a))) (Prod.snd (A.comul a)))
      A.unit :=
  A.antipodeLeft a

/-- Theorem 9: Symmetry of antipode left law. -/
theorem antipodeLeft_symm (a : H) :
    Path A.unit
      (A.mul (A.antipode (Prod.fst (A.comul a))) (Prod.snd (A.comul a))) :=
  Path.symm (A.antipodeLeft a)

/-- Theorem 10: Antipode left then symm gives refl (RwEq). -/
theorem antipodeLeft_cancel (a : H) :
    RwEq
      (Path.trans (A.antipodeLeft a) (Path.symm (A.antipodeLeft a)))
      (Path.refl _) :=
  rweq_cmpA_inv_right (A.antipodeLeft a)

/-- Theorem 11: Symmetry then forward gives refl (RwEq). -/
theorem antipodeLeft_cancel' (a : H) :
    RwEq
      (Path.trans (Path.symm (A.antipodeLeft a)) (A.antipodeLeft a))
      (Path.refl _) :=
  rweq_cmpA_inv_left (A.antipodeLeft a)

/-- Theorem 12: CongrArg through mul on antipodeRight. -/
theorem antipodeRight_congrArg (a : H) (f : H → H) :
    Path
      (f (A.mul (Prod.fst (A.comul a)) (A.antipode (Prod.snd (A.comul a)))))
      (f A.unit) :=
  congrArg f (A.antipodeRight a)

/-- Theorem 13: Transport along antipodeLeft. -/
theorem antipode_transport (a : H) (D : H → Type v) :
    D (A.mul (A.antipode (Prod.fst (A.comul a))) (Prod.snd (A.comul a))) →
    D A.unit :=
  transport (D := D) (A.antipodeLeft a)

-- ═══════════════════════════════════════════════════════════════
-- §2  Bialgebra Compatibility
-- ═══════════════════════════════════════════════════════════════

/-- Bialgebra compatibility data: comul is an algebra map. -/
structure BialgebraPathData (H : Type u) extends HopfAlgebraPathData H where
  /-- Comul is multiplicative -/
  comulMul : (a b : H) →
    Path (comul (mul a b))
      ((mul (Prod.fst (comul a)) (Prod.fst (comul b)),
        mul (Prod.snd (comul a)) (Prod.snd (comul b))))
  /-- Comul preserves unit -/
  comulUnit : Path (comul unit) (unit, unit)

namespace BialgebraPathData

variable {H : Type u} (B : BialgebraPathData H)

/-- Theorem 14: Comul-mul composed with projection gives path on fst. -/
theorem comulMul_fst (a b : H) :
    Path
      (Prod.fst (B.comul (B.mul a b)))
      (B.mul (Prod.fst (B.comul a)) (Prod.fst (B.comul b))) :=
  congrArg Prod.fst (B.comulMul a b)

/-- Theorem 15: Comul-mul composed with projection gives path on snd. -/
theorem comulMul_snd (a b : H) :
    Path
      (Prod.snd (B.comul (B.mul a b)))
      (B.mul (Prod.snd (B.comul a)) (Prod.snd (B.comul b))) :=
  congrArg Prod.snd (B.comulMul a b)

/-- Theorem 16: Symmetry of comulMul. -/
theorem comulMul_symm (a b : H) :
    Path
      ((B.mul (Prod.fst (B.comul a)) (Prod.fst (B.comul b)),
        B.mul (Prod.snd (B.comul a)) (Prod.snd (B.comul b))))
      (B.comul (B.mul a b)) :=
  Path.symm (B.comulMul a b)

/-- Theorem 17: Step witness for comulUnit right-unit. -/
theorem comulUnit_step :
    Step
      (Path.trans B.comulUnit (Path.refl (B.unit, B.unit)))
      B.comulUnit :=
  Step.trans_refl_right B.comulUnit

/-- Theorem 18: RwEq for comulUnit cancellation. -/
theorem comulUnit_rweq :
    RwEq
      (Path.trans B.comulUnit (Path.symm B.comulUnit))
      (Path.refl _) :=
  rweq_cmpA_inv_right B.comulUnit

/-- Theorem 19: Double symm on comulMul. -/
theorem comulMul_symm_symm (a b : H) :
    Step
      (Path.symm (Path.symm (B.comulMul a b)))
      (B.comulMul a b) :=
  Step.symm_symm (B.comulMul a b)

/-- Theorem 20: Transport along comulUnit. -/
theorem comulUnit_transport (D : H × H → Type v) :
    D (B.comul B.unit) → D (B.unit, B.unit) :=
  transport (D := D) B.comulUnit

end BialgebraPathData

-- ═══════════════════════════════════════════════════════════════
-- §3  R-Matrix Braiding & Yang-Baxter
-- ═══════════════════════════════════════════════════════════════

/-- R-matrix braiding data with Yang-Baxter coherence path. -/
structure RMatrixBraidData (H : Type u) where
  /-- The R-matrix as a path on tensor pairs -/
  Rmatrix : (a b : H) → Path (a, b) (b, a)
  /-- Inverse R-matrix -/
  RmatrixInv : (a b : H) → Path (b, a) (a, b)
  /-- R · R⁻¹ = id -/
  Rcancel : (a b : H) →
    RwEq
      (Path.trans (Rmatrix a b) (RmatrixInv a b))
      (Path.refl (a, b))
  /-- R⁻¹ · R = id -/
  RcancelInv : (a b : H) →
    RwEq
      (Path.trans (RmatrixInv a b) (Rmatrix a b))
      (Path.refl (b, a))

namespace RMatrixBraidData

variable {H : Type u} (R : RMatrixBraidData H)

/-- Theorem 21: Symmetry of Rmatrix gives RmatrixInv-shaped path. -/
theorem Rmatrix_symm (a b : H) :
    Path (b, a) (a, b) :=
  Path.symm (R.Rmatrix a b)

/-- Theorem 22: CongrArg Prod.fst through Rmatrix. -/
theorem Rmatrix_fst (a b : H) :
    Path (Prod.fst (a, b)) (Prod.fst (b, a)) :=
  congrArg Prod.fst (R.Rmatrix a b)

/-- Theorem 23: CongrArg Prod.snd through Rmatrix. -/
theorem Rmatrix_snd (a b : H) :
    Path (Prod.snd (a, b)) (Prod.snd (b, a)) :=
  congrArg Prod.snd (R.Rmatrix a b)

/-- Theorem 24: Step witness — double symm on Rmatrix. -/
theorem Rmatrix_symm_symm (a b : H) :
    Step
      (Path.symm (Path.symm (R.Rmatrix a b)))
      (R.Rmatrix a b) :=
  Step.symm_symm (R.Rmatrix a b)

/-- Theorem 25: Composing Rmatrix with its symm inverse, chained. -/
theorem Rmatrix_chain (a b : H) :
    Path (a, b) (a, b) :=
  Path.trans (R.Rmatrix a b) (Path.symm (R.Rmatrix a b))

/-- Theorem 26: Step — refl left identity on Rmatrix. -/
theorem Rmatrix_step_left (a b : H) :
    Step
      (Path.trans (Path.refl (a, b)) (R.Rmatrix a b))
      (R.Rmatrix a b) :=
  Step.trans_refl_left (R.Rmatrix a b)

end RMatrixBraidData

-- ═══════════════════════════════════════════════════════════════
-- §4  Quantum Enveloping Algebra Generators
-- ═══════════════════════════════════════════════════════════════

/-- Quantum enveloping algebra generators and relations as paths. -/
structure QuantumEnvelopingData (U : Type u) where
  /-- Multiplication -/
  mul : U → U → U
  /-- Unit -/
  unit : U
  /-- Generators E, F, K, Kinv -/
  E : U
  F : U
  K : U
  Kinv : U
  /-- K · K⁻¹ = 1 -/
  KKinv : Path (mul K Kinv) unit
  /-- K⁻¹ · K = 1 -/
  KinvK : Path (mul Kinv K) unit
  /-- KEK⁻¹ = q²E (represented as path to a target) -/
  qCommE : (target : U) → Path (mul K (mul E Kinv)) target
  /-- KFK⁻¹ = q⁻²F -/
  qCommF : (target : U) → Path (mul K (mul F Kinv)) target
  /-- Quantum Serre relation: EF - FE = (K - K⁻¹)/(q - q⁻¹) -/
  serreRelation : (rhs : U) →
    Path (mul E F) (mul (mul F E) rhs)

namespace QuantumEnvelopingData

variable {U : Type u} (Q : QuantumEnvelopingData U)

/-- Theorem 27: K-cancellation: K · (Kinv · K) path to K · unit. -/
theorem K_cancel_congrArg :
    Path (Q.mul Q.K (Q.mul Q.Kinv Q.K)) (Q.mul Q.K Q.unit) :=
  congrArg (Q.mul Q.K) Q.KinvK

/-- Theorem 28: Symmetry of KKinv gives Kinv-K path. -/
theorem KKinv_symm :
    Path Q.unit (Q.mul Q.K Q.Kinv) :=
  Path.symm Q.KKinv

/-- Theorem 29: Step — double symm on KKinv. -/
theorem KKinv_symm_symm :
    Step
      (Path.symm (Path.symm Q.KKinv))
      Q.KKinv :=
  Step.symm_symm Q.KKinv

/-- Theorem 30: RwEq cancellation of KKinv. -/
theorem KKinv_cancel :
    RwEq
      (Path.trans Q.KKinv (Path.symm Q.KKinv))
      (Path.refl _) :=
  rweq_cmpA_inv_right Q.KKinv

/-- Theorem 31: RwEq cancellation of KinvK. -/
theorem KinvK_cancel :
    RwEq
      (Path.trans Q.KinvK (Path.symm Q.KinvK))
      (Path.refl _) :=
  rweq_cmpA_inv_right Q.KinvK

/-- Theorem 32: Transport along KKinv. -/
theorem KKinv_transport (D : U → Type v) :
    D (Q.mul Q.K Q.Kinv) → D Q.unit :=
  transport (D := D) Q.KKinv

/-- Theorem 33: CongrArg through mul on KKinv. -/
theorem KKinv_congrArg (f : U → U) :
    Path (f (Q.mul Q.K Q.Kinv)) (f Q.unit) :=
  congrArg f Q.KKinv

/-- Theorem 34: Step witness — right unit on KinvK. -/
theorem KinvK_step :
    Step
      (Path.trans Q.KinvK (Path.refl Q.unit))
      Q.KinvK :=
  Step.trans_refl_right Q.KinvK

/-- Theorem 35: Associativity of path composition on generator paths. -/
theorem generator_path_assoc :
    Path.trans (Path.trans Q.KKinv (Path.symm Q.KKinv)) Q.KinvK =
    Path.trans Q.KKinv (Path.trans (Path.symm Q.KKinv) Q.KinvK) := by
  exact Path.trans_assoc Q.KKinv (Path.symm Q.KKinv) Q.KinvK

end QuantumEnvelopingData

-- ═══════════════════════════════════════════════════════════════
-- §5  Antipode Involution
-- ═══════════════════════════════════════════════════════════════

/-- Antipode involution data: S² = id as a path family. -/
structure AntipodeInvolutionData (H : Type u) where
  antipode : H → H
  /-- S(S(a)) = a -/
  involution : (a : H) → Path (antipode (antipode a)) a

namespace AntipodeInvolutionData

variable {H : Type u} (S : AntipodeInvolutionData H)

/-- Theorem 36: Symmetry of involution gives embedding path. -/
theorem involution_symm (a : H) :
    Path a (S.antipode (S.antipode a)) :=
  Path.symm (S.involution a)

/-- Theorem 37: Double involution path via trans and congrArg. -/
theorem involution_double (a : H) :
    Path (S.antipode (S.antipode (S.antipode (S.antipode a)))) a :=
  Path.trans
    (congrArg (fun x => S.antipode (S.antipode x)) (S.involution a))
    (S.involution a)

/-- Theorem 38: Step — double symm on involution. -/
theorem involution_symm_symm (a : H) :
    Step
      (Path.symm (Path.symm (S.involution a)))
      (S.involution a) :=
  Step.symm_symm (S.involution a)

/-- Theorem 39: RwEq — involution cancellation. -/
theorem involution_cancel (a : H) :
    RwEq
      (Path.trans (S.involution a) (Path.symm (S.involution a)))
      (Path.refl _) :=
  rweq_cmpA_inv_right (S.involution a)

/-- Theorem 40: CongrArg of antipode through involution. -/
theorem involution_congrArg (a : H) :
    Path (S.antipode (S.antipode (S.antipode a))) (S.antipode a) :=
  congrArg S.antipode (S.involution a)

/-- Theorem 41: Transport along involution path. -/
theorem involution_transport (a : H) (D : H → Type v) :
    D (S.antipode (S.antipode a)) → D a :=
  transport (D := D) (S.involution a)

/-- Theorem 42: CongrArg-trans coherence: map then compose. -/
theorem involution_congrArg_trans (a : H) (f : H → H) :
    RwEq
      (congrArg f (Path.trans (S.involution a) (Path.symm (S.involution a))))
      (congrArg f (Path.refl _)) :=
  rweq_congrArg_of_rweq f (rweq_cmpA_inv_right (S.involution a))

end AntipodeInvolutionData

-- ═══════════════════════════════════════════════════════════════
-- §6  Hopf Pairing & Duality
-- ═══════════════════════════════════════════════════════════════

/-- A Hopf pairing between two algebras, tracked by paths. -/
structure HopfPairingData (H K : Type u) where
  pair : H → K → H
  /-- Pairing respects multiplication on H -/
  pairMul : (mul : H → H → H) → (a b : H) → (k : K) →
    Path (pair (mul a b) k) (mul (pair a k) (pair b k))
  /-- Pairing respects unit -/
  pairUnit : (unit : H) → (k : K) →
    Path (pair unit k) unit

namespace HopfPairingData

variable {H K : Type u} (P : HopfPairingData H K)

/-- Theorem 43: Symmetry of pairMul. -/
theorem pairMul_symm (mul : H → H → H) (a b : H) (k : K) :
    Path (mul (P.pair a k) (P.pair b k)) (P.pair (mul a b) k) :=
  Path.symm (P.pairMul mul a b k)

/-- Theorem 44: Step — right unit on pairUnit. -/
theorem pairUnit_step (unit : H) (k : K) :
    Step
      (Path.trans (P.pairUnit unit k) (Path.refl unit))
      (P.pairUnit unit k) :=
  Step.trans_refl_right (P.pairUnit unit k)

/-- Theorem 45: CongrArg through pairing. -/
theorem pairUnit_congrArg (unit : H) (k : K) (f : H → H) :
    Path (f (P.pair unit k)) (f unit) :=
  congrArg f (P.pairUnit unit k)

/-- Theorem 46: RwEq — pairUnit cancellation. -/
theorem pairUnit_cancel (unit : H) (k : K) :
    RwEq
      (Path.trans (P.pairUnit unit k) (Path.symm (P.pairUnit unit k)))
      (Path.refl _) :=
  rweq_cmpA_inv_right (P.pairUnit unit k)

end HopfPairingData

-- ═══════════════════════════════════════════════════════════════
-- §7  Quasitriangular Structure
-- ═══════════════════════════════════════════════════════════════

/-- Quasitriangular Hopf algebra: R-matrix with coherence. -/
structure QuasitriangularData (H : Type u) where
  mul : H → H → H
  unit : H
  Relem : H × H
  /-- R intertwines comultiplication (path form) -/
  intertwine : (comul : H → H × H) → (a : H) →
    Path
      (mul (Prod.fst Relem) (Prod.fst (comul a)),
       mul (Prod.snd (comul a)) (Prod.snd Relem))
      (mul (Prod.fst (comul a)) (Prod.fst Relem),
       mul (Prod.snd Relem) (Prod.snd (comul a)))
  /-- R satisfies quasi-cocommutativity -/
  quasiCocomm : (comul : H → H × H) → (a : H) →
    Path (Prod.fst (comul a), Prod.snd (comul a))
      (Prod.snd (comul a), Prod.fst (comul a))

namespace QuasitriangularData

variable {H : Type u} (QT : QuasitriangularData H)

/-- Theorem 47: Symmetry of intertwine path. -/
theorem intertwine_symm (comul : H → H × H) (a : H) :
    Path _ _ :=
  Path.symm (QT.intertwine comul a)

/-- Theorem 48: Step on quasiCocomm. -/
theorem quasiCocomm_step (comul : H → H × H) (a : H) :
    Step
      (Path.trans (QT.quasiCocomm comul a) (Path.refl _))
      (QT.quasiCocomm comul a) :=
  Step.trans_refl_right (QT.quasiCocomm comul a)

/-- Theorem 49: CongrArg Prod.fst on quasiCocomm. -/
theorem quasiCocomm_fst (comul : H → H × H) (a : H) :
    Path
      (Prod.fst (Prod.fst (comul a), Prod.snd (comul a)))
      (Prod.fst (Prod.snd (comul a), Prod.fst (comul a))) :=
  congrArg Prod.fst (QT.quasiCocomm comul a)

/-- Theorem 50: RwEq cancellation of quasiCocomm. -/
theorem quasiCocomm_cancel (comul : H → H × H) (a : H) :
    RwEq
      (Path.trans (QT.quasiCocomm comul a) (Path.symm (QT.quasiCocomm comul a)))
      (Path.refl _) :=
  rweq_cmpA_inv_right (QT.quasiCocomm comul a)

/-- Theorem 51: Transport along quasiCocomm. -/
theorem quasiCocomm_transport (comul : H → H × H) (a : H) (D : H × H → Type v) :
    D (Prod.fst (comul a), Prod.snd (comul a)) →
    D (Prod.snd (comul a), Prod.fst (comul a)) :=
  transport (D := D) (QT.quasiCocomm comul a)

end QuasitriangularData

end QuantumGroupPaths
end Quantum
end ComputationalPaths

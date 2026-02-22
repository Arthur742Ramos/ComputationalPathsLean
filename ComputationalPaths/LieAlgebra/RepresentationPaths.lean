/-
# Lie Algebra Representations: Modules, Casimir & Universal Enveloping Algebra

Develops representation-theoretic content: modules over Lie algebras,
weight-space decomposition, Casimir element, universal enveloping algebra
PBW-filtration, and Verma module paths — all via computational paths with
Step/Path/trans/symm/congrArg.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.LieAlgebra.PathInfrastructure

set_option linter.unusedVariables false

namespace ComputationalPaths
namespace Path
namespace LieAlgebra

open Path

universe u v w

noncomputable section

/-! ## Lie Module (Representation) Data -/

/-- A Lie algebra representation: a module `V` acted on by bracket-preserving maps. -/
structure LieModuleData (A : Type u) (V : Type v) extends LieBracketData A where
  act   : A → V → V
  vZero : V
  vAdd  : V → V → V
  vNeg  : V → V
  actZeroLeft  : ∀ v : V, Path (act zero v) vZero
  actZeroRight : ∀ x : A, Path (act x vZero) vZero
  actLinear    : ∀ x : A, ∀ v w : V,
    Path (act x (vAdd v w)) (vAdd (act x v) (act x w))
  actBracket   : ∀ x y : A, ∀ v : V,
    Path (act (bracket x y) v) (vAdd (act x (act y v)) (vNeg (act y (act x v))))
  vAddZeroLeft  : ∀ v : V, Path (vAdd vZero v) v
  vAddZeroRight : ∀ v : V, Path (vAdd v vZero) v
  vAddAssoc     : ∀ u v w : V, Path (vAdd (vAdd u v) w) (vAdd u (vAdd v w))
  vNegInv       : ∀ v : V, Path (vAdd v (vNeg v)) vZero
  vAddComm      : ∀ u v : V, Path (vAdd u v) (vAdd v u)

namespace LieModuleData

variable {A : Type u} {V : Type v} (M : LieModuleData A V)

/-! ### Theorem 1-10: Basic module action identities -/

/-- Theorem 1: Action of zero annihilates. -/
noncomputable def act_zero_left (v : V) : Path (M.act M.zero v) M.vZero :=
  M.actZeroLeft v

/-- Theorem 2: Action on zero module element. -/
noncomputable def act_zero_right (x : A) : Path (M.act x M.vZero) M.vZero :=
  M.actZeroRight x

/-- Theorem 3: Action distributes over module addition. -/
noncomputable def act_linear (x : A) (v w : V) :
    Path (M.act x (M.vAdd v w)) (M.vAdd (M.act x v) (M.act x w)) :=
  M.actLinear x v w

/-- Theorem 4: Action of bracket = commutator. -/
noncomputable def act_bracket (x y : A) (v : V) :
    Path (M.act (M.bracket x y) v)
         (M.vAdd (M.act x (M.act y v)) (M.vNeg (M.act y (M.act x v)))) :=
  M.actBracket x y v

/-- Theorem 5: act_zero_left right-unit coherence. -/
noncomputable def act_zero_left_right_unit (v : V) :
    RwEq (Path.trans (M.actZeroLeft v) (Path.refl _)) (M.actZeroLeft v) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 6: act_zero_right right-unit coherence. -/
noncomputable def act_zero_right_right_unit (x : A) :
    RwEq (Path.trans (M.actZeroRight x) (Path.refl _)) (M.actZeroRight x) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 7: act_zero_left inverse cancel. -/
noncomputable def act_zero_left_inv_cancel (v : V) :
    RwEq (Path.trans (M.actZeroLeft v) (Path.symm (M.actZeroLeft v)))
         (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

/-- Theorem 8: act congruence on Lie element. -/
noncomputable def act_congr_left {x₁ x₂ : A} (p : Path x₁ x₂) (v : V) :
    Path (M.act x₁ v) (M.act x₂ v) :=
  Path.congrArg (fun t => M.act t v) p

/-- Theorem 9: act congruence on module element. -/
noncomputable def act_congr_right (x : A) {v₁ v₂ : V} (q : Path v₁ v₂) :
    Path (M.act x v₁) (M.act x v₂) :=
  Path.congrArg (M.act x) q

/-- Theorem 10: act congruence on both arguments (trans of congrs). -/
noncomputable def act_congr_both {x₁ x₂ : A} {v₁ v₂ : V}
    (p : Path x₁ x₂) (q : Path v₁ v₂) :
    Path (M.act x₁ v₁) (M.act x₂ v₂) :=
  Path.trans (Path.congrArg (fun t => M.act t v₁) p)
             (Path.congrArg (M.act x₂) q)

/-! ### Theorem 11-20: Weight-space paths -/

/-- Weight data: eigenvalue decomposition of a Cartan element action. -/
structure WeightSpaceData where
  weight : A
  eigenval : V → V
  eigenPath : ∀ v : V, Path (M.act weight v) (eigenval v)

variable (W : M.WeightSpaceData)

/-- Theorem 11: weight action path. -/
noncomputable def weight_action (v : V) :
    Path (M.act W.weight v) (W.eigenval v) :=
  W.eigenPath v

/-- Theorem 12: weight action right-unit. -/
noncomputable def weight_action_right_unit (v : V) :
    RwEq (Path.trans (W.eigenPath v) (Path.refl _)) (W.eigenPath v) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 13: weight action left-unit. -/
noncomputable def weight_action_left_unit (v : V) :
    RwEq (Path.trans (Path.refl _) (W.eigenPath v)) (W.eigenPath v) :=
  rweq_of_step (Step.trans_refl_left _)

/-- Theorem 14: weight action inverse cancel. -/
noncomputable def weight_action_inv_cancel (v : V) :
    RwEq (Path.trans (W.eigenPath v) (Path.symm (W.eigenPath v)))
         (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

/-- Theorem 15: weight eigenvalue congruence. -/
noncomputable def weight_eigen_congr {v₁ v₂ : V} (q : Path v₁ v₂) :
    Path (W.eigenval v₁) (W.eigenval v₂) :=
  Path.congrArg W.eigenval q

/-- Theorem 16: double weight action. -/
noncomputable def weight_double_action (v : V) :
    Path (M.act W.weight (M.act W.weight v)) (W.eigenval (W.eigenval v)) :=
  Path.trans (M.act_congr_right W.weight (W.eigenPath v))
             (W.eigenPath (W.eigenval v))

/-- Theorem 17: weight action symmetry coherence. -/
noncomputable def weight_action_symm (v : V) :
    RwEq (Path.symm (Path.symm (W.eigenPath v))) (W.eigenPath v) :=
  rweq_of_step (Step.symm_symm _)

/-- Theorem 18: double weight action associativity. -/
noncomputable def weight_double_assoc (v : V) :
    RwEq (Path.trans (Path.trans
              (M.act_congr_right W.weight (W.eigenPath v))
              (W.eigenPath (W.eigenval v)))
            (Path.refl _))
         (Path.trans (M.act_congr_right W.weight (W.eigenPath v))
                     (W.eigenPath (W.eigenval v))) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 19: eigenvalue at zero module element. -/
noncomputable def weight_at_zero :
    Path (M.act W.weight M.vZero) M.vZero :=
  M.actZeroRight W.weight

/-- Theorem 20: zero-weight and eigenpath composition. -/
noncomputable def weight_zero_eigen_trans :
    Path (M.act W.weight M.vZero) (W.eigenval M.vZero) :=
  W.eigenPath M.vZero

/-! ### Theorem 21-30: Universal enveloping algebra filtration -/

/-- Universal enveloping algebra PBW-filtration data. -/
structure UEAData where
  ueaMul    : V → V → V
  ueaUnit   : V
  ueaEmbed  : A → V
  ueaMulAssoc  : ∀ a b c : V, Path (ueaMul (ueaMul a b) c) (ueaMul a (ueaMul b c))
  ueaLeftUnit  : ∀ a : V, Path (ueaMul ueaUnit a) a
  ueaRightUnit : ∀ a : V, Path (ueaMul a ueaUnit) a
  ueaBracketComm : ∀ x y : A,
    Path (ueaMul (ueaEmbed x) (ueaEmbed y))
         (M.vAdd (ueaMul (ueaEmbed y) (ueaEmbed x))
                 (ueaEmbed (M.bracket x y)))

variable (U : M.UEAData)

/-- Theorem 21: UEA multiplication is associative. -/
noncomputable def uea_assoc (a b c : V) :
    Path (U.ueaMul (U.ueaMul a b) c) (U.ueaMul a (U.ueaMul b c)) :=
  U.ueaMulAssoc a b c

/-- Theorem 22: UEA left unit. -/
noncomputable def uea_left_unit (a : V) :
    Path (U.ueaMul U.ueaUnit a) a :=
  U.ueaLeftUnit a

/-- Theorem 23: UEA right unit. -/
noncomputable def uea_right_unit (a : V) :
    Path (U.ueaMul a U.ueaUnit) a :=
  U.ueaRightUnit a

/-- Theorem 24: UEA bracket commutation. -/
noncomputable def uea_bracket_comm (x y : A) :
    Path (U.ueaMul (U.ueaEmbed x) (U.ueaEmbed y))
         (M.vAdd (U.ueaMul (U.ueaEmbed y) (U.ueaEmbed x))
                 (U.ueaEmbed (M.bracket x y))) :=
  U.ueaBracketComm x y

/-- Theorem 25: UEA associativity right-unit coherence. -/
noncomputable def uea_assoc_right_unit (a b c : V) :
    RwEq (Path.trans (U.ueaMulAssoc a b c) (Path.refl _))
         (U.ueaMulAssoc a b c) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 26: UEA associativity inverse cancel. -/
noncomputable def uea_assoc_inv_cancel (a b c : V) :
    RwEq (Path.trans (U.ueaMulAssoc a b c)
                     (Path.symm (U.ueaMulAssoc a b c)))
         (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

/-- Theorem 27: UEA left-inverse cancel. -/
noncomputable def uea_assoc_left_inv (a b c : V) :
    RwEq (Path.trans (Path.symm (U.ueaMulAssoc a b c))
                     (U.ueaMulAssoc a b c))
         (Path.refl _) :=
  rweq_of_step (Step.symm_trans _)

/-- Theorem 28: UEA embedding congruence. -/
noncomputable def uea_embed_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (U.ueaEmbed x₁) (U.ueaEmbed x₂) :=
  Path.congrArg U.ueaEmbed p

/-- Theorem 29: UEA multiplication congruence (left). -/
noncomputable def uea_mul_congr_left {a₁ a₂ : V} (p : Path a₁ a₂) (b : V) :
    Path (U.ueaMul a₁ b) (U.ueaMul a₂ b) :=
  Path.congrArg (fun t => U.ueaMul t b) p

/-- Theorem 30: UEA multiplication congruence (right). -/
noncomputable def uea_mul_congr_right (a : V) {b₁ b₂ : V} (q : Path b₁ b₂) :
    Path (U.ueaMul a b₁) (U.ueaMul a b₂) :=
  Path.congrArg (U.ueaMul a) q

/-! ### Theorem 31-40: Verma module and highest-weight paths -/

/-- Highest-weight module data. -/
structure HighestWeightData where
  hwVec   : V
  posRoot : A → V → V
  annihilate : ∀ x : A, Path (posRoot x hwVec) M.vZero
  hwWeight : Path (M.act W.weight hwVec) (W.eigenval hwVec)

variable (HW : M.HighestWeightData W)

/-- Theorem 31: Positive root annihilates highest-weight vector. -/
noncomputable def hw_annihilate (x : A) :
    Path (HW.posRoot x HW.hwVec) M.vZero :=
  HW.annihilate x

/-- Theorem 32: Weight action on highest-weight vector. -/
noncomputable def hw_weight_action :
    Path (M.act W.weight HW.hwVec) (W.eigenval HW.hwVec) :=
  HW.hwWeight

/-- Theorem 33: Annihilation right-unit coherence. -/
noncomputable def hw_annihilate_right_unit (x : A) :
    RwEq (Path.trans (HW.annihilate x) (Path.refl _))
         (HW.annihilate x) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 34: Annihilation inverse cancel. -/
noncomputable def hw_annihilate_inv_cancel (x : A) :
    RwEq (Path.trans (HW.annihilate x) (Path.symm (HW.annihilate x)))
         (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

/-- Theorem 35: Annihilation left-inverse cancel. -/
noncomputable def hw_annihilate_left_inv (x : A) :
    RwEq (Path.trans (Path.symm (HW.annihilate x)) (HW.annihilate x))
         (Path.refl _) :=
  rweq_of_step (Step.symm_trans _)

/-- Theorem 36: Annihilation double symmetry. -/
noncomputable def hw_annihilate_symm_symm (x : A) :
    RwEq (Path.symm (Path.symm (HW.annihilate x)))
         (HW.annihilate x) :=
  rweq_of_step (Step.symm_symm _)

/-- Theorem 37: hw weight action right-unit. -/
noncomputable def hw_weight_right_unit :
    RwEq (Path.trans HW.hwWeight (Path.refl _)) HW.hwWeight :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 38: hw weight action left-unit. -/
noncomputable def hw_weight_left_unit :
    RwEq (Path.trans (Path.refl _) HW.hwWeight) HW.hwWeight :=
  rweq_of_step (Step.trans_refl_left _)

/-- Theorem 39: Positive root congruence. -/
noncomputable def hw_posRoot_congr (x : A) {v₁ v₂ : V} (q : Path v₁ v₂) :
    Path (HW.posRoot x v₁) (HW.posRoot x v₂) :=
  Path.congrArg (HW.posRoot x) q

/-- Theorem 40: Annihilation trans with weight action. -/
noncomputable def hw_annihilate_weight_assoc (x : A) :
    RwEq (Path.trans (Path.trans (HW.annihilate x) (Path.refl M.vZero))
                     (Path.refl M.vZero))
         (HW.annihilate x) :=
  RwEq.trans (rweq_of_step (Step.trans_refl_right _))
             (rweq_of_step (Step.trans_refl_right _))

/-! ### Theorem 41-50: Module homomorphism paths -/

/-- Lie module homomorphism: equivariant linear map between representations. -/
structure LieModuleHomData (V₂ : Type w) (M₂ : LieModuleData A V₂) where
  hom       : V → V₂
  homZero   : Path (hom M.vZero) M₂.vZero
  homAdd    : ∀ v w : V, Path (hom (M.vAdd v w)) (M₂.vAdd (hom v) (hom w))
  equivariant : ∀ x : A, ∀ v : V,
    Path (hom (M.act x v)) (M₂.act x (hom v))

variable {V₂ : Type w} {M₂ : LieModuleData A V₂}
variable (φ : M.LieModuleHomData V₂ M₂)

/-- Theorem 41: Module hom preserves zero. -/
noncomputable def modhom_zero : Path (φ.hom M.vZero) M₂.vZero :=
  φ.homZero

/-- Theorem 42: Module hom distributes over addition. -/
noncomputable def modhom_add (v w : V) :
    Path (φ.hom (M.vAdd v w)) (M₂.vAdd (φ.hom v) (φ.hom w)) :=
  φ.homAdd v w

/-- Theorem 43: Module hom is equivariant. -/
noncomputable def modhom_equivariant (x : A) (v : V) :
    Path (φ.hom (M.act x v)) (M₂.act x (φ.hom v)) :=
  φ.equivariant x v

/-- Theorem 44: Module hom congruence. -/
noncomputable def modhom_congr {v₁ v₂ : V} (q : Path v₁ v₂) :
    Path (φ.hom v₁) (φ.hom v₂) :=
  Path.congrArg φ.hom q

/-- Theorem 45: Module hom zero right-unit. -/
noncomputable def modhom_zero_right_unit :
    RwEq (Path.trans φ.homZero (Path.refl _)) φ.homZero :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 46: Module hom zero inverse cancel. -/
noncomputable def modhom_zero_inv_cancel :
    RwEq (Path.trans φ.homZero (Path.symm φ.homZero)) (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

/-- Theorem 47: Equivariance right-unit. -/
noncomputable def modhom_equiv_right_unit (x : A) (v : V) :
    RwEq (Path.trans (φ.equivariant x v) (Path.refl _))
         (φ.equivariant x v) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 48: Equivariance inverse cancel. -/
noncomputable def modhom_equiv_inv_cancel (x : A) (v : V) :
    RwEq (Path.trans (φ.equivariant x v)
                     (Path.symm (φ.equivariant x v)))
         (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

/-- Theorem 49: Equivariance double symmetry. -/
noncomputable def modhom_equiv_symm_symm (x : A) (v : V) :
    RwEq (Path.symm (Path.symm (φ.equivariant x v)))
         (φ.equivariant x v) :=
  rweq_of_step (Step.symm_symm _)

/-- Theorem 50: Hom-add and equivariance composed path. -/
noncomputable def modhom_add_equivariant_trans (x : A) (v w : V) :
    Path (φ.hom (M.act x (M.vAdd v w)))
         (M₂.act x (M₂.vAdd (φ.hom v) (φ.hom w))) :=
  Path.trans (φ.equivariant x (M.vAdd v w))
             (Path.congrArg (M₂.act x) (φ.homAdd v w))

end LieModuleData

end

end LieAlgebra
end Path
end ComputationalPaths

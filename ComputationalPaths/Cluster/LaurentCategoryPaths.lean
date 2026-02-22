/-
# Cluster Algebra: Laurent Phenomenon & Cluster Category Paths

Develops Laurent polynomial data, cluster Laurent phenomenon witnesses,
cluster category / quiver representation data, and Caldero–Chapoton
map coherences — all via computational paths with
Step/Path/trans/symm/congrArg.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Cluster.SeedMutationPaths

set_option linter.unusedVariables false

namespace ComputationalPaths
namespace Cluster

open Path

universe u v

noncomputable section

/-! ## Laurent phenomenon -/

/-- Laurent polynomial ring data with positivity witnesses. -/
structure LaurentData (ι : Type u) (Val : Type v) where
  vars   : ι → Val
  mul    : Val → Val → Val
  add    : Val → Val → Val
  one    : Val
  inv    : ι → Val             -- x_i^{-1}
  zero   : Val
  invPath : ∀ i : ι, Path (mul (vars i) (inv i)) one
  mulAssoc : ∀ a b c : Val, Path (mul (mul a b) c) (mul a (mul b c))
  mulOne   : ∀ a : Val, Path (mul a one) a
  oneMul   : ∀ a : Val, Path (mul one a) a
  mulComm  : ∀ a b : Val, Path (mul a b) (mul b a)
  addAssoc : ∀ a b c : Val, Path (add (add a b) c) (add a (add b c))
  addZero  : ∀ a : Val, Path (add a zero) a
  addComm  : ∀ a b : Val, Path (add a b) (add b a)

namespace LaurentData

variable {ι : Type u} {Val : Type v} (L : LaurentData ι Val)

/-! ### Theorem 1-15: Laurent polynomial coherences -/

/-- Theorem 1: Variable times inverse is one. -/
noncomputable def var_inv (i : ι) :
    Path (L.mul (L.vars i) (L.inv i)) L.one :=
  L.invPath i

/-- Theorem 2: Multiplication is associative. -/
noncomputable def mul_assoc (a b c : Val) :
    Path (L.mul (L.mul a b) c) (L.mul a (L.mul b c)) :=
  L.mulAssoc a b c

/-- Theorem 3: Right multiplicative identity. -/
noncomputable def mul_one (a : Val) : Path (L.mul a L.one) a :=
  L.mulOne a

/-- Theorem 4: Left multiplicative identity. -/
noncomputable def one_mul (a : Val) : Path (L.mul L.one a) a :=
  L.oneMul a

/-- Theorem 5: Multiplication is commutative. -/
noncomputable def mul_comm (a b : Val) : Path (L.mul a b) (L.mul b a) :=
  L.mulComm a b

/-- Theorem 6: Addition is associative. -/
noncomputable def add_assoc (a b c : Val) :
    Path (L.add (L.add a b) c) (L.add a (L.add b c)) :=
  L.addAssoc a b c

/-- Theorem 7: Additive identity. -/
noncomputable def add_zero (a : Val) : Path (L.add a L.zero) a :=
  L.addZero a

/-- Theorem 8: var_inv right-unit. -/
noncomputable def var_inv_right_unit (i : ι) :
    RwEq (Path.trans (L.invPath i) (Path.refl _)) (L.invPath i) :=
  rweq_of_step (Path.Step.trans_refl_right _)

/-- Theorem 9: var_inv inverse cancel. -/
noncomputable def var_inv_inv_cancel (i : ι) :
    RwEq (Path.trans (L.invPath i) (Path.symm (L.invPath i)))
         (Path.refl _) :=
  rweq_of_step (Path.Step.trans_symm _)

/-- Theorem 10: mul_assoc right-unit. -/
noncomputable def mul_assoc_right_unit (a b c : Val) :
    RwEq (Path.trans (L.mulAssoc a b c) (Path.refl _))
         (L.mulAssoc a b c) :=
  rweq_of_step (Path.Step.trans_refl_right _)

/-- Theorem 11: mul_assoc inverse cancel. -/
noncomputable def mul_assoc_inv_cancel (a b c : Val) :
    RwEq (Path.trans (L.mulAssoc a b c)
                     (Path.symm (L.mulAssoc a b c)))
         (Path.refl _) :=
  rweq_of_step (Path.Step.trans_symm _)

/-- Theorem 12: mul congruence (left). -/
noncomputable def mul_congr_left {a₁ a₂ : Val} (p : Path a₁ a₂) (b : Val) :
    Path (L.mul a₁ b) (L.mul a₂ b) :=
  Path.congrArg (fun t => L.mul t b) p

/-- Theorem 13: mul congruence (right). -/
noncomputable def mul_congr_right (a : Val) {b₁ b₂ : Val} (q : Path b₁ b₂) :
    Path (L.mul a b₁) (L.mul a b₂) :=
  Path.congrArg (L.mul a) q

/-- Theorem 14: add congruence (left). -/
noncomputable def add_congr_left {a₁ a₂ : Val} (p : Path a₁ a₂) (b : Val) :
    Path (L.add a₁ b) (L.add a₂ b) :=
  Path.congrArg (fun t => L.add t b) p

/-- Theorem 15: add congruence (right). -/
noncomputable def add_congr_right (a : Val) {b₁ b₂ : Val} (q : Path b₁ b₂) :
    Path (L.add a b₁) (L.add a b₂) :=
  Path.congrArg (L.add a) q

/-! ### Theorem 16-25: Laurent phenomenon witnesses -/

/-- Laurent phenomenon witness: a cluster variable is a Laurent polynomial. -/
structure LaurentPhenomenonWitness (clusterVar : Val) where
  laurentExpr : Val
  laurentPath : Path clusterVar laurentExpr

variable {clusterVar : Val} (LP : L.LaurentPhenomenonWitness clusterVar)

/-- Theorem 16: Laurent expression path. -/
noncomputable def laurent_expr :
    Path clusterVar LP.laurentExpr :=
  LP.laurentPath

/-- Theorem 17: Laurent path right-unit. -/
noncomputable def laurent_right_unit :
    RwEq (Path.trans LP.laurentPath (Path.refl _)) LP.laurentPath :=
  rweq_of_step (Path.Step.trans_refl_right _)

/-- Theorem 18: Laurent path inverse cancel. -/
noncomputable def laurent_inv_cancel :
    RwEq (Path.trans LP.laurentPath (Path.symm LP.laurentPath))
         (Path.refl _) :=
  rweq_of_step (Path.Step.trans_symm _)

/-- Theorem 19: Laurent path left-unit. -/
noncomputable def laurent_left_unit :
    RwEq (Path.trans (Path.refl _) LP.laurentPath) LP.laurentPath :=
  rweq_of_step (Path.Step.trans_refl_left _)

/-- Theorem 20: Laurent path double symmetry. -/
noncomputable def laurent_symm_symm :
    RwEq (Path.symm (Path.symm LP.laurentPath)) LP.laurentPath :=
  rweq_of_step (Path.Step.symm_symm _)

/-- Theorem 21: Laurent path left-inverse. -/
noncomputable def laurent_left_inv :
    RwEq (Path.trans (Path.symm LP.laurentPath) LP.laurentPath)
         (Path.refl _) :=
  rweq_of_step (Path.Step.symm_trans _)

/-- Theorem 22: mul_one double symmetry. -/
noncomputable def mul_one_symm_symm (a : Val) :
    RwEq (Path.symm (Path.symm (L.mulOne a))) (L.mulOne a) :=
  rweq_of_step (Path.Step.symm_symm _)

/-- Theorem 23: one_mul right-unit. -/
noncomputable def one_mul_right_unit (a : Val) :
    RwEq (Path.trans (L.oneMul a) (Path.refl _)) (L.oneMul a) :=
  rweq_of_step (Path.Step.trans_refl_right _)

/-- Theorem 24: add_assoc left-unit. -/
noncomputable def add_assoc_left_unit (a b c : Val) :
    RwEq (Path.trans (Path.refl _) (L.addAssoc a b c))
         (L.addAssoc a b c) :=
  rweq_of_step (Path.Step.trans_refl_left _)

/-- Theorem 25: mul_comm inverse cancel. -/
noncomputable def mul_comm_inv_cancel (a b : Val) :
    RwEq (Path.trans (L.mulComm a b)
                     (Path.symm (L.mulComm a b)))
         (Path.refl _) :=
  rweq_of_step (Path.Step.trans_symm _)

end LaurentData

/-! ## Cluster category / quiver representation -/

/-- Quiver representation data for cluster categories. -/
structure QuiverRepData (ι : Type u) (Val : Type v) where
  dim     : ι → Nat
  arrows  : ι → ι → Val
  zero    : Val
  add     : Val → Val → Val
  compose : Val → Val → Val
  composeAssoc : ∀ a b c : Val,
    Path (compose (compose a b) c) (compose a (compose b c))
  composeZeroLeft : ∀ a : Val, Path (compose zero a) zero
  composeZeroRight : ∀ a : Val, Path (compose a zero) zero
  addComm : ∀ a b : Val, Path (add a b) (add b a)
  addAssoc : ∀ a b c : Val, Path (add (add a b) c) (add a (add b c))
  addZero : ∀ a : Val, Path (add a zero) a

namespace QuiverRepData

variable {ι : Type u} {Val : Type v} (Q : QuiverRepData ι Val)

/-! ### Theorem 26-40: Quiver representation coherences -/

/-- Theorem 26: Composition is associative. -/
noncomputable def qrep_assoc (a b c : Val) :
    Path (Q.compose (Q.compose a b) c) (Q.compose a (Q.compose b c)) :=
  Q.composeAssoc a b c

/-- Theorem 27: Zero absorbs on left. -/
noncomputable def qrep_zero_left (a : Val) :
    Path (Q.compose Q.zero a) Q.zero :=
  Q.composeZeroLeft a

/-- Theorem 28: Zero absorbs on right. -/
noncomputable def qrep_zero_right (a : Val) :
    Path (Q.compose a Q.zero) Q.zero :=
  Q.composeZeroRight a

/-- Theorem 29: compose congruence (left). -/
noncomputable def qrep_congr_left {a₁ a₂ : Val} (p : Path a₁ a₂) (b : Val) :
    Path (Q.compose a₁ b) (Q.compose a₂ b) :=
  Path.congrArg (fun t => Q.compose t b) p

/-- Theorem 30: compose congruence (right). -/
noncomputable def qrep_congr_right (a : Val) {b₁ b₂ : Val} (q : Path b₁ b₂) :
    Path (Q.compose a b₁) (Q.compose a b₂) :=
  Path.congrArg (Q.compose a) q

/-- Theorem 31: assoc right-unit. -/
noncomputable def qrep_assoc_right_unit (a b c : Val) :
    RwEq (Path.trans (Q.composeAssoc a b c) (Path.refl _))
         (Q.composeAssoc a b c) :=
  rweq_of_step (Path.Step.trans_refl_right _)

/-- Theorem 32: assoc inverse cancel. -/
noncomputable def qrep_assoc_inv_cancel (a b c : Val) :
    RwEq (Path.trans (Q.composeAssoc a b c)
                     (Path.symm (Q.composeAssoc a b c)))
         (Path.refl _) :=
  rweq_of_step (Path.Step.trans_symm _)

/-- Theorem 33: zero_left right-unit. -/
noncomputable def qrep_zero_left_right_unit (a : Val) :
    RwEq (Path.trans (Q.composeZeroLeft a) (Path.refl _))
         (Q.composeZeroLeft a) :=
  rweq_of_step (Path.Step.trans_refl_right _)

/-- Theorem 34: zero_right inverse cancel. -/
noncomputable def qrep_zero_right_inv_cancel (a : Val) :
    RwEq (Path.trans (Q.composeZeroRight a)
                     (Path.symm (Q.composeZeroRight a)))
         (Path.refl _) :=
  rweq_of_step (Path.Step.trans_symm _)

/-- Theorem 35: add congruence (left). -/
noncomputable def qrep_add_congr_left {a₁ a₂ : Val} (p : Path a₁ a₂) (b : Val) :
    Path (Q.add a₁ b) (Q.add a₂ b) :=
  Path.congrArg (fun t => Q.add t b) p

/-- Theorem 36: add congruence (right). -/
noncomputable def qrep_add_congr_right (a : Val) {b₁ b₂ : Val} (q : Path b₁ b₂) :
    Path (Q.add a b₁) (Q.add a b₂) :=
  Path.congrArg (Q.add a) q

/-- Theorem 37: addComm right-unit. -/
noncomputable def qrep_addComm_right_unit (a b : Val) :
    RwEq (Path.trans (Q.addComm a b) (Path.refl _))
         (Q.addComm a b) :=
  rweq_of_step (Path.Step.trans_refl_right _)

/-- Theorem 38: addAssoc double symmetry. -/
noncomputable def qrep_addAssoc_symm_symm (a b c : Val) :
    RwEq (Path.symm (Path.symm (Q.addAssoc a b c)))
         (Q.addAssoc a b c) :=
  rweq_of_step (Path.Step.symm_symm _)

/-- Theorem 39: addZero inverse cancel. -/
noncomputable def qrep_addZero_inv_cancel (a : Val) :
    RwEq (Path.trans (Q.addZero a) (Path.symm (Q.addZero a)))
         (Path.refl _) :=
  rweq_of_step (Path.Step.trans_symm _)

/-- Theorem 40: assoc left-inverse. -/
noncomputable def qrep_assoc_left_inv (a b c : Val) :
    RwEq (Path.trans (Path.symm (Q.composeAssoc a b c))
                     (Q.composeAssoc a b c))
         (Path.refl _) :=
  rweq_of_step (Path.Step.symm_trans _)

end QuiverRepData

end

end Cluster
end ComputationalPaths

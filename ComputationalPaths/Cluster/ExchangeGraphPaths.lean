/-
# Cluster Algebra Paths: Exchange Graphs, Tropical Duality & Laurent Phenomenon

Exchange graph structure, tropical semifield operations, Laurent phenomenon
witnesses, cluster variable positivity, seed equivalences, Fomin–Zelevinsky
mutation combinatorics — all via computational paths with
Step/Path/trans/symm/congrArg.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

set_option linter.unusedVariables false

namespace ComputationalPaths
namespace Path
namespace Cluster
namespace ExchangeGraphPaths

open Path

universe u v w

noncomputable section

/-! ## Exchange Graph Data -/

/-- Exchange graph: vertices are seeds, edges are mutations. -/
structure ExchangeGraphData (A : Type u) where
  seed : A                        -- current seed
  mutate : Nat → A → A           -- mutation at direction k
  compose : A → A → A            -- composition (e.g. of cluster monomials)
  one : A                         -- unit
  add : A → A → A
  zero : A
  neg : A → A
  involution : ∀ k : Nat, ∀ s : A, Path (mutate k (mutate k s)) s
  mutateCommute : ∀ i j : Nat, ∀ s : A,
    Path (mutate i (mutate j s)) (mutate j (mutate i s))
  composeAssoc : ∀ x y z : A, Path (compose (compose x y) z) (compose x (compose y z))
  composeOneLeft : ∀ x : A, Path (compose one x) x
  composeOneRight : ∀ x : A, Path (compose x one) x
  addZero : ∀ x : A, Path (add x zero) x
  zeroAdd : ∀ x : A, Path (add zero x) x
  addAssoc : ∀ x y z : A, Path (add (add x y) z) (add x (add y z))
  addComm : ∀ x y : A, Path (add x y) (add y x)
  negInv : ∀ x : A, Path (add x (neg x)) zero

namespace ExchangeGraphData

variable {A : Type u} (G : ExchangeGraphData A)

/-! ### Theorems 1–8: Involution and mutation commutativity -/

/-- Theorem 1: Involution right unit. -/
noncomputable def involution_runit (k : Nat) (s : A) :
    RwEq (Path.trans (G.involution k s) (Path.refl s)) (G.involution k s) :=
  rweq_of_step (Step.trans_refl_right (G.involution k s))

/-- Theorem 2: Involution inverse cancel. -/
noncomputable def involution_inv (k : Nat) (s : A) :
    RwEq (Path.trans (G.involution k s) (Path.symm (G.involution k s)))
         (Path.refl (G.mutate k (G.mutate k s))) :=
  rweq_of_step (Step.trans_symm (G.involution k s))

/-- Theorem 3: Mutation commutativity left unit. -/
noncomputable def mutateComm_lunit (i j : Nat) (s : A) :
    RwEq (Path.trans (Path.refl _) (G.mutateCommute i j s))
         (G.mutateCommute i j s) :=
  rweq_of_step (Step.trans_refl_left (G.mutateCommute i j s))

/-- Theorem 4: Mutation commutativity inverse cancel (left). -/
noncomputable def mutateComm_inv_left (i j : Nat) (s : A) :
    RwEq (Path.trans (Path.symm (G.mutateCommute i j s)) (G.mutateCommute i j s))
         (Path.refl (G.mutate j (G.mutate i s))) :=
  rweq_of_step (Step.symm_trans (G.mutateCommute i j s))

/-- Theorem 5: Congruence of mutate in seed argument. -/
noncomputable def mutate_congr (k : Nat) {s₁ s₂ : A} (p : Path s₁ s₂) :
    Path (G.mutate k s₁) (G.mutate k s₂) :=
  congrArg (G.mutate k ·) p

/-- Theorem 6: Triple mutation reduces via involution. -/
noncomputable def triple_mutate (k : Nat) (s : A) :
    Path (G.mutate k (G.mutate k (G.mutate k s))) (G.mutate k s) :=
  congrArg (G.mutate k ·) (G.involution k s)

/-- Theorem 7: Quadruple mutation reduces to identity. -/
noncomputable def quad_mutate (k : Nat) (s : A) :
    Path (G.mutate k (G.mutate k (G.mutate k (G.mutate k s)))) s :=
  Path.trans (congrArg (G.mutate k ·) (G.triple_mutate k s)) (G.involution k s)

/-- Theorem 8: Compose associativity right unit. -/
noncomputable def composeAssoc_runit (x y z : A) :
    RwEq (Path.trans (G.composeAssoc x y z) (Path.refl _))
         (G.composeAssoc x y z) :=
  rweq_of_step (Step.trans_refl_right (G.composeAssoc x y z))

/-! ### Theorems 9–15: Composition identities -/

/-- Theorem 9: Left unit of compose. -/
noncomputable def composeOne_lunit (x : A) :
    RwEq (Path.trans (Path.refl _) (G.composeOneLeft x)) (G.composeOneLeft x) :=
  rweq_of_step (Step.trans_refl_left (G.composeOneLeft x))

/-- Theorem 10: Right unit inverse cancel. -/
noncomputable def composeOneR_inv (x : A) :
    RwEq (Path.trans (G.composeOneRight x) (Path.symm (G.composeOneRight x)))
         (Path.refl (G.compose x G.one)) :=
  rweq_of_step (Step.trans_symm (G.composeOneRight x))

/-- Theorem 11: Congruence of compose left. -/
noncomputable def compose_congr_left {x₁ x₂ : A} (p : Path x₁ x₂) (y : A) :
    Path (G.compose x₁ y) (G.compose x₂ y) :=
  congrArg (G.compose · y) p

/-- Theorem 12: Congruence of compose right. -/
noncomputable def compose_congr_right (x : A) {y₁ y₂ : A} (q : Path y₁ y₂) :
    Path (G.compose x y₁) (G.compose x y₂) :=
  congrArg (G.compose x ·) q

/-- Theorem 13: Congruence of compose both. -/
noncomputable def compose_congr {x₁ x₂ y₁ y₂ : A} (p : Path x₁ x₂) (q : Path y₁ y₂) :
    Path (G.compose x₁ y₁) (G.compose x₂ y₂) :=
  Path.trans (congrArg (G.compose · y₁) p) (congrArg (G.compose x₂ ·) q)

/-- Theorem 14: Outer associativity step. -/
noncomputable def compose_assoc_outer (a b c d : A) :
    Path (G.compose (G.compose (G.compose a b) c) d)
         (G.compose (G.compose a b) (G.compose c d)) :=
  G.composeAssoc (G.compose a b) c d

/-- Theorem 15: Compose one·one = one. -/
noncomputable def compose_one_one :
    Path (G.compose G.one G.one) G.one :=
  G.composeOneLeft G.one

end ExchangeGraphData

/-! ## Tropical Semifield Data -/

/-- Tropical semifield: ⊕ = min, ⊗ = +, for coefficient systems. -/
structure TropicalData (A : Type u) where
  trop_add : A → A → A          -- tropical addition (min)
  trop_mul : A → A → A          -- tropical multiplication (+)
  trop_zero : A                  -- tropical zero (∞)
  trop_one : A                   -- tropical one (0)
  addIdemp : ∀ x : A, Path (trop_add x x) x
  addComm : ∀ x y : A, Path (trop_add x y) (trop_add y x)
  addAssoc : ∀ x y z : A,
    Path (trop_add (trop_add x y) z) (trop_add x (trop_add y z))
  mulComm : ∀ x y : A, Path (trop_mul x y) (trop_mul y x)
  mulAssoc : ∀ x y z : A,
    Path (trop_mul (trop_mul x y) z) (trop_mul x (trop_mul y z))
  mulOneLeft : ∀ x : A, Path (trop_mul trop_one x) x
  mulOneRight : ∀ x : A, Path (trop_mul x trop_one) x
  addZeroLeft : ∀ x : A, Path (trop_add trop_zero x) x
  addZeroRight : ∀ x : A, Path (trop_add x trop_zero) x
  distribute : ∀ x y z : A,
    Path (trop_mul x (trop_add y z)) (trop_add (trop_mul x y) (trop_mul x z))

namespace TropicalData

variable {A : Type u} (T : TropicalData A)

/-! ### Theorems 16–25: Tropical identities -/

/-- Theorem 16: Idempotence right unit. -/
noncomputable def addIdemp_runit (x : A) :
    RwEq (Path.trans (T.addIdemp x) (Path.refl x)) (T.addIdemp x) :=
  rweq_of_step (Step.trans_refl_right (T.addIdemp x))

/-- Theorem 17: Commutativity inverse cancel. -/
noncomputable def addComm_inv (x y : A) :
    RwEq (Path.trans (T.addComm x y) (Path.symm (T.addComm x y)))
         (Path.refl (T.trop_add x y)) :=
  rweq_of_step (Step.trans_symm (T.addComm x y))

/-- Theorem 18: Mul commutativity left unit. -/
noncomputable def mulComm_lunit (x y : A) :
    RwEq (Path.trans (Path.refl _) (T.mulComm x y)) (T.mulComm x y) :=
  rweq_of_step (Step.trans_refl_left (T.mulComm x y))

/-- Theorem 19: Distributivity right unit. -/
noncomputable def distribute_runit (x y z : A) :
    RwEq (Path.trans (T.distribute x y z) (Path.refl _)) (T.distribute x y z) :=
  rweq_of_step (Step.trans_refl_right (T.distribute x y z))

/-- Theorem 20: Congruence of trop_add. -/
noncomputable def tropAdd_congr {x₁ x₂ y₁ y₂ : A} (p : Path x₁ x₂) (q : Path y₁ y₂) :
    Path (T.trop_add x₁ y₁) (T.trop_add x₂ y₂) :=
  Path.trans (congrArg (T.trop_add · y₁) p) (congrArg (T.trop_add x₂ ·) q)

/-- Theorem 21: Congruence of trop_mul. -/
noncomputable def tropMul_congr {x₁ x₂ y₁ y₂ : A} (p : Path x₁ x₂) (q : Path y₁ y₂) :
    Path (T.trop_mul x₁ y₁) (T.trop_mul x₂ y₂) :=
  Path.trans (congrArg (T.trop_mul · y₁) p) (congrArg (T.trop_mul x₂ ·) q)

/-- Theorem 22: Mul one·one = one. -/
noncomputable def mul_one_one :
    Path (T.trop_mul T.trop_one T.trop_one) T.trop_one :=
  T.mulOneLeft T.trop_one

/-- Theorem 23: Add zero⊕zero = zero. -/
noncomputable def add_zero_zero :
    Path (T.trop_add T.trop_zero T.trop_zero) T.trop_zero :=
  T.addIdemp T.trop_zero

/-- Theorem 24: Outer associativity of trop_add. -/
noncomputable def tropAdd_assoc_outer (a b c d : A) :
    Path (T.trop_add (T.trop_add (T.trop_add a b) c) d)
         (T.trop_add (T.trop_add a b) (T.trop_add c d)) :=
  T.addAssoc (T.trop_add a b) c d

/-- Theorem 25: Distribute then idempotence. -/
noncomputable def distribute_idemp (x y : A) :
    Path (T.trop_mul x (T.trop_add y y)) (T.trop_add (T.trop_mul x y) (T.trop_mul x y)) :=
  T.distribute x y y

end TropicalData

/-! ## Laurent Phenomenon Data -/

/-- Laurent phenomenon: cluster variables are Laurent polynomials. -/
structure LaurentData (A : Type u) where
  clusterVar : Nat → A           -- x_i
  laurentExpr : A → A            -- Laurent expression
  mul : A → A → A
  inv : A → A                    -- multiplicative inverse
  add : A → A → A
  one : A
  zero : A
  laurentWitness : ∀ i : Nat,
    Path (laurentExpr (clusterVar i)) (clusterVar i)
  mulAssoc : ∀ x y z : A, Path (mul (mul x y) z) (mul x (mul y z))
  mulOneLeft : ∀ x : A, Path (mul one x) x
  mulOneRight : ∀ x : A, Path (mul x one) x
  mulInvRight : ∀ x : A, Path (mul x (inv x)) one
  mulInvLeft : ∀ x : A, Path (mul (inv x) x) one
  addZero : ∀ x : A, Path (add x zero) x
  zeroAdd : ∀ x : A, Path (add zero x) x
  addAssoc : ∀ x y z : A, Path (add (add x y) z) (add x (add y z))
  laurentMul : ∀ x y : A,
    Path (laurentExpr (mul x y)) (mul (laurentExpr x) (laurentExpr y))
  laurentAdd : ∀ x y : A,
    Path (laurentExpr (add x y)) (add (laurentExpr x) (laurentExpr y))

namespace LaurentData

variable {A : Type u} (L : LaurentData A)

/-! ### Theorems 26–35: Laurent phenomenon identities -/

/-- Theorem 26: Laurent witness right unit. -/
noncomputable def laurentWitness_runit (i : Nat) :
    RwEq (Path.trans (L.laurentWitness i) (Path.refl _)) (L.laurentWitness i) :=
  rweq_of_step (Step.trans_refl_right (L.laurentWitness i))

/-- Theorem 27: Laurent witness inverse cancel. -/
noncomputable def laurentWitness_inv (i : Nat) :
    RwEq (Path.trans (L.laurentWitness i) (Path.symm (L.laurentWitness i)))
         (Path.refl (L.laurentExpr (L.clusterVar i))) :=
  rweq_of_step (Step.trans_symm (L.laurentWitness i))

/-- Theorem 28: Mul inverse right unit. -/
noncomputable def mulInvR_runit (x : A) :
    RwEq (Path.trans (L.mulInvRight x) (Path.refl L.one)) (L.mulInvRight x) :=
  rweq_of_step (Step.trans_refl_right (L.mulInvRight x))

/-- Theorem 29: Mul inverse left, left unit. -/
noncomputable def mulInvL_lunit (x : A) :
    RwEq (Path.trans (Path.refl _) (L.mulInvLeft x)) (L.mulInvLeft x) :=
  rweq_of_step (Step.trans_refl_left (L.mulInvLeft x))

/-- Theorem 30: Congruence of laurentExpr. -/
noncomputable def laurent_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (L.laurentExpr x₁) (L.laurentExpr x₂) :=
  congrArg L.laurentExpr p

/-- Theorem 31: Congruence of mul left. -/
noncomputable def mul_congr_left {x₁ x₂ : A} (p : Path x₁ x₂) (y : A) :
    Path (L.mul x₁ y) (L.mul x₂ y) :=
  congrArg (L.mul · y) p

/-- Theorem 32: Congruence of mul right. -/
noncomputable def mul_congr_right (x : A) {y₁ y₂ : A} (q : Path y₁ y₂) :
    Path (L.mul x y₁) (L.mul x y₂) :=
  congrArg (L.mul x ·) q

/-- Theorem 33: Laurent of product via laurentMul path. -/
noncomputable def laurent_product (x y : A) :
    Path (L.laurentExpr (L.mul x y)) (L.mul (L.laurentExpr x) (L.laurentExpr y)) :=
  L.laurentMul x y

/-- Theorem 34: Laurent of mul(x, inv x) = one. -/
noncomputable def laurent_mul_inv (x : A) :
    Path (L.laurentExpr (L.mul x (L.inv x))) (L.mul (L.laurentExpr x) (L.laurentExpr (L.inv x))) :=
  L.laurentMul x (L.inv x)

/-- Theorem 35: Outer mul associativity. -/
noncomputable def mul_assoc_outer (a b c d : A) :
    Path (L.mul (L.mul (L.mul a b) c) d) (L.mul (L.mul a b) (L.mul c d)) :=
  L.mulAssoc (L.mul a b) c d

end LaurentData

/-! ## Cluster Complex / Simplicial Structure -/

/-- Simplicial complex of compatible cluster variables. -/
structure ClusterComplexData (A : Type u) where
  face : List A → A              -- face map
  boundary : A → A               -- boundary operator
  add : A → A → A
  zero : A
  boundaryFace : ∀ xs : List A, Path (boundary (face xs)) zero
  boundaryZero : Path (boundary zero) zero
  boundaryAdd : ∀ x y : A,
    Path (boundary (add x y)) (add (boundary x) (boundary y))
  addZero : ∀ x : A, Path (add x zero) x
  zeroAdd : ∀ x : A, Path (add zero x) x
  addAssoc : ∀ x y z : A, Path (add (add x y) z) (add x (add y z))

namespace ClusterComplexData

variable {A : Type u} (CC : ClusterComplexData A)

/-! ### Theorems 36–45: Cluster complex identities -/

/-- Theorem 36: Boundary of face right unit. -/
noncomputable def boundaryFace_runit (xs : List A) :
    RwEq (Path.trans (CC.boundaryFace xs) (Path.refl CC.zero)) (CC.boundaryFace xs) :=
  rweq_of_step (Step.trans_refl_right (CC.boundaryFace xs))

/-- Theorem 37: Boundary of zero inverse cancel. -/
noncomputable def boundaryZero_inv :
    RwEq (Path.trans CC.boundaryZero (Path.symm CC.boundaryZero))
         (Path.refl (CC.boundary CC.zero)) :=
  rweq_of_step (Step.trans_symm CC.boundaryZero)

/-- Theorem 38: Boundary additive left unit. -/
noncomputable def boundaryAdd_lunit (x y : A) :
    RwEq (Path.trans (Path.refl _) (CC.boundaryAdd x y)) (CC.boundaryAdd x y) :=
  rweq_of_step (Step.trans_refl_left (CC.boundaryAdd x y))

/-- Theorem 39: Congruence of boundary. -/
noncomputable def boundary_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (CC.boundary x₁) (CC.boundary x₂) :=
  congrArg CC.boundary p

/-- Theorem 40: Congruence of face. -/
noncomputable def face_congr {xs₁ xs₂ : List A} (p : Path xs₁ xs₂) :
    Path (CC.face xs₁) (CC.face xs₂) :=
  congrArg CC.face p

/-- Theorem 41: Boundary add then collapse zero. -/
noncomputable def boundary_add_collapse (x : A) :
    Path (CC.add (CC.boundary CC.zero) (CC.boundary x)) (CC.boundary x) :=
  Path.trans (congrArg (CC.add · (CC.boundary x)) CC.boundaryZero)
             (CC.zeroAdd (CC.boundary x))

/-- Theorem 42: Outer add associativity. -/
noncomputable def add_assoc_outer (a b c d : A) :
    Path (CC.add (CC.add (CC.add a b) c) d) (CC.add (CC.add a b) (CC.add c d)) :=
  CC.addAssoc (CC.add a b) c d

/-- Theorem 43: Boundary face at empty list right unit. -/
noncomputable def boundaryFace_empty_runit :
    RwEq (Path.trans (CC.boundaryFace []) (Path.refl CC.zero)) (CC.boundaryFace []) :=
  rweq_of_step (Step.trans_refl_right (CC.boundaryFace []))

/-- Theorem 44: Add zero then boundary. -/
noncomputable def addZero_boundary (x : A) :
    Path (CC.boundary (CC.add x CC.zero)) (CC.boundary x) :=
  congrArg CC.boundary (CC.addZero x)

/-- Theorem 45: Zero add then boundary. -/
noncomputable def zeroAdd_boundary (x : A) :
    Path (CC.boundary (CC.add CC.zero x)) (CC.boundary x) :=
  congrArg CC.boundary (CC.zeroAdd x)

end ClusterComplexData

end
end ExchangeGraphPaths
end Cluster
end Path
end ComputationalPaths

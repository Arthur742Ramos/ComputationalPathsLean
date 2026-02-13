import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Cluster algebra paths: seeds and mutations

This module packages seed and mutation data for cluster algebras with explicit
computational-path witnesses. Exchange relations and mutation involutivity are
tracked by `Path`, with `Path.Step` witnesses used to normalize the composites
and derive `RwEq` coherence lemmas.
-/

namespace ComputationalPaths
namespace Cluster
namespace SeedMutationPaths

open Path

universe u v

/-- Domain-specific rewrite tags for cluster seed/mutation coherence moves. -/
inductive ClusterSeedStep : Type
  | skew
  | exchange
  | involution

/-- A cluster seed with exchange matrix, variables, and skew-symmetry witness. -/
structure SeedPathData (ι : Type u) (Val : Type v) where
  exchangeMatrix : ι → ι → Int
  vars : ι → Val
  skewPath : ∀ i j : ι, Path (exchangeMatrix i j) (-(exchangeMatrix j i))

namespace SeedPathData

variable {ι : Type u} {Val : Type v} (S : SeedPathData ι Val)

/-- Step witness: right-unit normalization for matrix skew-symmetry paths. -/
def skew_step (i j : ι) :
    Path.Step
      (Path.trans (S.skewPath i j) (Path.refl (-(S.exchangeMatrix j i))))
      (S.skewPath i j) :=
  Path.Step.trans_refl_right (S.skewPath i j)

@[simp] theorem skew_rweq (i j : ι) :
    RwEq
      (Path.trans (S.skewPath i j) (Path.refl (-(S.exchangeMatrix j i))))
      (S.skewPath i j) :=
  rweq_of_step (S.skew_step i j)

end SeedPathData

/-- Mutation data over a fixed seed, including exchange and involution paths. -/
structure MutationPathData {ι : Type u} {Val : Type v}
    (S : SeedPathData ι Val) where
  direction : ι
  mul : Val → Val → Val
  add : Val → Val → Val
  mutatedVar : Val
  posMonomial : Val
  negMonomial : Val
  mutateAt : ι → Val → Val
  exchangePath :
    Path (mul (S.vars direction) mutatedVar) (add posMonomial negMonomial)
  mutationInvolutivePath :
    Path (mutateAt direction (mutateAt direction (S.vars direction))) (S.vars direction)

namespace MutationPathData

variable {ι : Type u} {Val : Type v} {S : SeedPathData ι Val}
variable (M : MutationPathData S)

/-- Step witness: right-unit normalization for the exchange relation path. -/
def exchange_step :
    Path.Step
      (Path.trans (M.exchangePath) (Path.refl (M.add M.posMonomial M.negMonomial)))
      (M.exchangePath) :=
  Path.Step.trans_refl_right (M.exchangePath)

@[simp] theorem exchange_rweq :
    RwEq
      (Path.trans (M.exchangePath) (Path.refl (M.add M.posMonomial M.negMonomial)))
      (M.exchangePath) :=
  rweq_of_step (M.exchange_step)

/-- Step witness: left-unit normalization for mutation involutivity. -/
def mutation_involutive_step :
    Path.Step
      (Path.trans
        (Path.refl (M.mutateAt M.direction (M.mutateAt M.direction (S.vars M.direction))))
        (M.mutationInvolutivePath))
      (M.mutationInvolutivePath) :=
  Path.Step.trans_refl_left (M.mutationInvolutivePath)

@[simp] theorem mutation_involutive_rweq :
    RwEq
      (Path.trans
        (Path.refl (M.mutateAt M.direction (M.mutateAt M.direction (S.vars M.direction))))
        (M.mutationInvolutivePath))
      (M.mutationInvolutivePath) :=
  rweq_of_step (M.mutation_involutive_step)

@[simp] theorem exchange_cancel_rweq :
    RwEq
      (Path.trans (Path.symm (M.exchangePath)) (M.exchangePath))
      (Path.refl (M.add M.posMonomial M.negMonomial)) :=
  rweq_cmpA_inv_left (M.exchangePath)

end MutationPathData

/-- Trivial seed package over `PUnit`. -/
def trivialSeedPathData : SeedPathData PUnit PUnit where
  exchangeMatrix := fun _ _ => 0
  vars := fun _ => PUnit.unit
  skewPath := fun _ _ => Path.ofEq (by simp)

/-- Trivial mutation package over the trivial seed. -/
def trivialMutationPathData : MutationPathData trivialSeedPathData where
  direction := PUnit.unit
  mul := fun _ _ => PUnit.unit
  add := fun _ _ => PUnit.unit
  mutatedVar := PUnit.unit
  posMonomial := PUnit.unit
  negMonomial := PUnit.unit
  mutateAt := fun _ _ => PUnit.unit
  exchangePath := Path.refl PUnit.unit
  mutationInvolutivePath := Path.refl PUnit.unit

end SeedMutationPaths
end Cluster
end ComputationalPaths

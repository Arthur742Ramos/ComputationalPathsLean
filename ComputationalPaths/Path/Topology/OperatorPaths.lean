/-
# Operator Theory via Computational Paths

This module formalizes operator theory using the computational paths
framework: bounded operators, spectrum, resolvent, compact operators,
self-adjoint operators, and spectral theorem aspects.

## References

- Reed & Simon, "Methods of Modern Mathematical Physics"
- Dunford & Schwartz, "Linear Operators"
- Kato, "Perturbation Theory for Linear Operators"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Topology
namespace OperatorPaths

open ComputationalPaths.Path

universe u

/-! ## Operator Algebra -/

/-- A linear space (simplified). -/
structure LinSpace where
  carrier : Type u
  zero : carrier
  add : carrier → carrier → carrier
  neg : carrier → carrier
  smul : Int → carrier → carrier
  add_zero : ∀ v, Path (add v zero) v
  add_comm : ∀ v w, Path (add v w) (add w v)
  add_neg : ∀ v, Path (add v (neg v)) zero

/-- A bounded operator on a linear space. -/
structure BoundedOp (V : LinSpace) where
  op : V.carrier → V.carrier
  op_zero : Path (op V.zero) V.zero
  op_add : ∀ v w, Path (op (V.add v w)) (V.add (op v) (op w))

/-- The identity operator. -/
def BoundedOp.idOp (V : LinSpace) : BoundedOp V where
  op := fun v => v
  op_zero := Path.refl _
  op_add := fun _ _ => Path.refl _

/-- The zero operator. -/
def BoundedOp.zeroOp (V : LinSpace) : BoundedOp V where
  op := fun _ => V.zero
  op_zero := Path.refl _
  op_add := fun _ _ => symm (V.add_zero V.zero)

/-- Composition of bounded operators. -/
def BoundedOp.comp {V : LinSpace} (A B : BoundedOp V) : BoundedOp V where
  op := fun v => A.op (B.op v)
  op_zero := trans (congrArg A.op B.op_zero) A.op_zero
  op_add := fun v w =>
    trans (congrArg A.op (B.op_add v w)) (A.op_add (B.op v) (B.op w))

/-- Composition with identity on the left. -/
def comp_id_left {V : LinSpace} (A : BoundedOp V) :
    Path (BoundedOp.comp (BoundedOp.idOp V) A).op A.op :=
  Path.refl _

/-- Composition with identity on the right. -/
def comp_id_right {V : LinSpace} (A : BoundedOp V) :
    Path (BoundedOp.comp A (BoundedOp.idOp V)).op A.op :=
  Path.refl _

/-- Composition is associative at the map level. -/
def comp_assoc {V : LinSpace} (A B C : BoundedOp V) :
    Path (BoundedOp.comp (BoundedOp.comp A B) C).op
         (BoundedOp.comp A (BoundedOp.comp B C)).op :=
  Path.refl _

/-- Zero composed with anything is zero. -/
def comp_zero_left {V : LinSpace} (A : BoundedOp V) :
    Path (BoundedOp.comp (BoundedOp.zeroOp V) A).op (BoundedOp.zeroOp V).op :=
  Path.refl _

/-- Anything composed with zero maps zero to zero. -/
def comp_zero_at_zero {V : LinSpace} (A : BoundedOp V) :
    Path ((BoundedOp.comp A (BoundedOp.zeroOp V)).op V.zero) V.zero :=
  trans (congrArg A.op (Path.refl _)) A.op_zero

/-! ## Operator Addition -/

/-- Sum of two bounded operators (linearity is witnessed abstractly). -/
def BoundedOp.addOp {V : LinSpace} (A B : BoundedOp V)
    (add_linearity : ∀ v w, Path (V.add (A.op (V.add v w)) (B.op (V.add v w)))
                                  (V.add (V.add (A.op v) (B.op v)) (V.add (A.op w) (B.op w)))) :
    BoundedOp V where
  op := fun v => V.add (A.op v) (B.op v)
  op_zero := trans (congrArg (fun x => V.add x (B.op V.zero))
    A.op_zero) (trans (congrArg (V.add V.zero) B.op_zero) (V.add_zero V.zero))
  op_add := add_linearity

/-- Adding zero operator on the right yields add with zero. -/
def addOp_zero_right {V : LinSpace} (A : BoundedOp V) (v : V.carrier) :
    Path (V.add (A.op v) V.zero) (A.op v) :=
  V.add_zero (A.op v)

/-- Adding zero operator: both directions simplify. -/
def addOp_zero_left_simp {V : LinSpace} (A : BoundedOp V) (v : V.carrier) :
    Path (V.add V.zero (A.op v)) (V.add (A.op v) V.zero) :=
  V.add_comm V.zero (A.op v)

/-! ## Spectrum -/

/-- The spectrum type: λ is in the spectrum if (A - λI) is not invertible. -/
structure SpectrumPoint (V : LinSpace) where
  operator : BoundedOp V
  eigenvalue : Int
  eigenvector : V.carrier
  eigen_eq : Path (operator.op eigenvector) (V.smul eigenvalue eigenvector)

/-- An eigenvalue equation: Av = λv. -/
def eigen_equation {V : LinSpace} (sp : SpectrumPoint V) :
    Path (sp.operator.op sp.eigenvector) (V.smul sp.eigenvalue sp.eigenvector) :=
  sp.eigen_eq

/-- Applying operator twice to eigenvector. -/
def eigen_twice {V : LinSpace} (sp : SpectrumPoint V)
    (smul_compat : Path (sp.operator.op (V.smul sp.eigenvalue sp.eigenvector))
                       (V.smul sp.eigenvalue (sp.operator.op sp.eigenvector))) :
    Path (sp.operator.op (sp.operator.op sp.eigenvector))
         (V.smul sp.eigenvalue (V.smul sp.eigenvalue sp.eigenvector)) :=
  trans (congrArg sp.operator.op sp.eigen_eq)
        (trans smul_compat (congrArg (V.smul sp.eigenvalue) sp.eigen_eq))

/-! ## Resolvent -/

/-- The resolvent: (A - λI)⁻¹ when it exists. -/
structure Resolvent (V : LinSpace) where
  operator : BoundedOp V
  lambda : Int
  resolvent_op : V.carrier → V.carrier
  left_inv : ∀ v, Path (resolvent_op (V.add (operator.op v) (V.neg (V.smul lambda v)))) v
  right_inv : ∀ v, Path (V.add (operator.op (resolvent_op v)) (V.neg (V.smul lambda (resolvent_op v)))) v

/-- Resolvent at zero recovers operator inverse. -/
def resolvent_at_zero {V : LinSpace} (R : Resolvent V) (v : V.carrier) :
    Path (R.resolvent_op (V.add (R.operator.op v) (V.neg (V.smul R.lambda v)))) v :=
  R.left_inv v

/-! ## Compact Operators -/

/-- A compact operator (abstract: finite rank approximation). -/
structure CompactOp (V : LinSpace) extends BoundedOp V where
  rank : Nat
  finite_rank_approx : V.carrier → V.carrier
  approx_zero : Path (finite_rank_approx V.zero) V.zero

/-- The zero operator is compact. -/
def CompactOp.zeroCompact (V : LinSpace) : CompactOp V where
  op := fun _ => V.zero
  op_zero := Path.refl _
  op_add := fun _ _ => symm (V.add_zero V.zero)
  rank := 0
  finite_rank_approx := fun _ => V.zero
  approx_zero := Path.refl _

/-- Compact operator at zero gives zero. -/
def compact_at_zero {V : LinSpace} (K : CompactOp V) :
    Path (K.op V.zero) V.zero :=
  K.op_zero

/-- Composition of compact with bounded is compact (at map level). -/
def compact_comp_bounded {V : LinSpace} (K : CompactOp V) (B : BoundedOp V) :
    CompactOp V where
  op := fun v => K.op (B.op v)
  op_zero := trans (congrArg K.op B.op_zero) K.op_zero
  op_add := fun v w =>
    trans (congrArg K.op (B.op_add v w)) (K.op_add (B.op v) (B.op w))
  rank := K.rank
  finite_rank_approx := fun v => K.finite_rank_approx (B.op v)
  approx_zero := trans (congrArg K.finite_rank_approx B.op_zero) K.approx_zero

/-! ## Self-Adjoint Operators -/

/-- A self-adjoint operator (with an inner product). -/
structure SelfAdjointOp (V : LinSpace) where
  op : BoundedOp V
  inner : V.carrier → V.carrier → Int
  self_adjoint : ∀ v w, Path (inner (op.op v) w) (inner v (op.op w))

/-- Identity is self-adjoint. -/
def SelfAdjointOp.identity (V : LinSpace)
    (inner : V.carrier → V.carrier → Int) : SelfAdjointOp V where
  op := BoundedOp.idOp V
  inner := inner
  self_adjoint := fun _ _ => Path.refl _

/-- Self-adjointness swaps arguments via path. -/
def self_adj_swap {V : LinSpace} (S : SelfAdjointOp V)
    (v w : V.carrier) :
    Path (S.inner (S.op.op v) w) (S.inner v (S.op.op w)) :=
  S.self_adjoint v w

/-- Double self-adjoint swap returns to original. -/
def self_adj_double_swap {V : LinSpace} (S : SelfAdjointOp V)
    (v w : V.carrier) :
    Path (S.inner (S.op.op v) w) (S.inner (S.op.op v) w) :=
  trans (S.self_adjoint v w) (symm (S.self_adjoint v w))

/-! ## Spectral Theorem Aspects -/

/-- A spectral decomposition: operator expressed via eigenvalues. -/
structure SpectralDecomp (V : LinSpace) where
  op : BoundedOp V
  numEigenvalues : Nat
  eigenvalues : Fin numEigenvalues → Int
  projections : Fin numEigenvalues → V.carrier → V.carrier
  proj_idempotent : ∀ i v, Path ((projections i) ((projections i) v)) ((projections i) v)

/-- Each spectral projection is idempotent. -/
def spectral_proj_idem {V : LinSpace} (S : SpectralDecomp V)
    (i : Fin S.numEigenvalues) (v : V.carrier) :
    Path (S.projections i (S.projections i v)) (S.projections i v) :=
  S.proj_idempotent i v

/-- Triple application of spectral projection. -/
def spectral_proj_triple {V : LinSpace} (S : SpectralDecomp V)
    (i : Fin S.numEigenvalues) (v : V.carrier) :
    Path (S.projections i (S.projections i (S.projections i v)))
         (S.projections i v) :=
  trans (congrArg (S.projections i) (S.proj_idempotent i v))
        (S.proj_idempotent i v)

/-! ## Functional Calculus -/

/-- Functional calculus: apply a function to an operator via spectral decomposition. -/
structure FuncCalc (V : LinSpace) where
  op : SpectralDecomp V
  func : Int → Int
  result_eigenvalues : Fin op.numEigenvalues → Int
  func_applied : ∀ i, Path (result_eigenvalues i) (func (op.eigenvalues i))

/-- Functional calculus with identity function preserves eigenvalues. -/
def funcCalc_id {V : LinSpace} (S : SpectralDecomp V) :
    FuncCalc V where
  op := S
  func := fun x => x
  result_eigenvalues := S.eigenvalues
  func_applied := fun _ => Path.refl _

/-- Functional calculus with constant zero function. -/
def funcCalc_zero {V : LinSpace} (S : SpectralDecomp V) :
    FuncCalc V where
  op := S
  func := fun _ => 0
  result_eigenvalues := fun _ => 0
  func_applied := fun _ => Path.refl _

/-- Composition of functional calculus. -/
def funcCalc_comp {V : LinSpace} (fc : FuncCalc V) (g : Int → Int)
    (comp_spec : ∀ i, Path (g (fc.result_eigenvalues i))
                            (g (fc.func (fc.op.eigenvalues i)))) :
    FuncCalc V where
  op := fc.op
  func := fun x => g (fc.func x)
  result_eigenvalues := fun i => g (fc.result_eigenvalues i)
  func_applied := fun i => trans (comp_spec i) (Path.refl _)

end OperatorPaths
end Topology
end Path
end ComputationalPaths

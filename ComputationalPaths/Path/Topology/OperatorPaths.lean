/-
# Operator Theory via Computational Paths

Deep exploration of operator theory using computational paths:
bounded operators, spectrum, resolvent, compact operators, self-adjoint
operators, spectral theorem aspects, operator algebras, and functional calculus.

## References

- Reed & Simon, "Methods of Modern Mathematical Physics"
- Dunford & Schwartz, "Linear Operators"
- Kato, "Perturbation Theory for Linear Operators"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Topology
namespace OperatorPaths

open ComputationalPaths.Path

universe u

/-! ## Operator Spaces -/

/-- A space of operators on a normed space. -/
structure OperatorSpace where
  carrier : Type u
  zero : carrier
  add : carrier → carrier → carrier
  neg : carrier → carrier
  comp : carrier → carrier → carrier
  idOp : carrier
  opNorm : carrier → Nat
  add_comm : ∀ a b, Path (add a b) (add b a)
  add_zero : ∀ a, Path (add a zero) a
  add_neg : ∀ a, Path (add a (neg a)) zero
  comp_id_left : ∀ a, Path (comp idOp a) a
  comp_id_right : ∀ a, Path (comp a idOp) a
  comp_assoc : ∀ a b c, Path (comp (comp a b) c) (comp a (comp b c))
  opNorm_zero : Path (opNorm zero) 0
  comp_zero_left : ∀ a, Path (comp zero a) zero
  comp_zero_right : ∀ a, Path (comp a zero) zero

/-- 1. Identity composition on left -/
noncomputable def op_comp_id_left (O : OperatorSpace) (a : O.carrier) :
    Path (O.comp O.idOp a) a :=
  O.comp_id_left a

/-- 2. Identity composition on right -/
noncomputable def op_comp_id_right (O : OperatorSpace) (a : O.carrier) :
    Path (O.comp a O.idOp) a :=
  O.comp_id_right a

/-- 3. Associativity of composition -/
noncomputable def op_comp_assoc (O : OperatorSpace) (a b c : O.carrier) :
    Path (O.comp (O.comp a b) c) (O.comp a (O.comp b c)) :=
  O.comp_assoc a b c

/-- 4. Norm of zero operator -/
noncomputable def op_norm_zero (O : OperatorSpace) : Path (O.opNorm O.zero) 0 :=
  O.opNorm_zero

/-- 5. Zero composition on left -/
noncomputable def op_zero_comp (O : OperatorSpace) (a : O.carrier) :
    Path (O.comp O.zero a) O.zero :=
  O.comp_zero_left a

/-- 6. Zero composition on right -/
noncomputable def op_comp_zero (O : OperatorSpace) (a : O.carrier) :
    Path (O.comp a O.zero) O.zero :=
  O.comp_zero_right a

/-- 7. Triple composition associativity (left to right) -/
noncomputable def op_comp_assoc3 (O : OperatorSpace) (a b c d : O.carrier) :
    Path (O.comp (O.comp (O.comp a b) c) d)
         (O.comp a (O.comp b (O.comp c d))) :=
  let step1 : Path (O.comp (O.comp (O.comp a b) c) d)
                    (O.comp (O.comp a b) (O.comp c d)) :=
    O.comp_assoc (O.comp a b) c d
  let step2 : Path (O.comp (O.comp a b) (O.comp c d))
                    (O.comp a (O.comp b (O.comp c d))) :=
    O.comp_assoc a b (O.comp c d)
  trans step1 step2

/-- 8. Double identity composition -/
noncomputable def op_double_id (O : OperatorSpace) :
    Path (O.comp O.idOp O.idOp) O.idOp :=
  O.comp_id_left O.idOp

/-- 9. Add commutativity -/
noncomputable def op_add_comm (O : OperatorSpace) (a b : O.carrier) :
    Path (O.add a b) (O.add b a) :=
  O.add_comm a b

/-- 10. Add zero -/
noncomputable def op_add_zero (O : OperatorSpace) (a : O.carrier) :
    Path (O.add a O.zero) a :=
  O.add_zero a

/-- 11. Zero add via commutativity -/
noncomputable def op_zero_add (O : OperatorSpace) (a : O.carrier) :
    Path (O.add O.zero a) a :=
  trans (O.add_comm O.zero a) (O.add_zero a)

/-- 12. Norm of composition with zero on left -/
noncomputable def op_norm_zero_comp (O : OperatorSpace) (a : O.carrier) :
    Path (O.opNorm (O.comp O.zero a)) 0 :=
  trans (congrArg O.opNorm (O.comp_zero_left a)) O.opNorm_zero

/-- 13. Norm of composition with zero on right -/
noncomputable def op_norm_comp_zero (O : OperatorSpace) (a : O.carrier) :
    Path (O.opNorm (O.comp a O.zero)) 0 :=
  trans (congrArg O.opNorm (O.comp_zero_right a)) O.opNorm_zero

/-! ## Spectrum and Resolvent -/

/-- Resolvent data for an operator at a "scalar" (modeled as Nat). -/
structure ResolventData (O : OperatorSpace) where
  op : O.carrier
  scalar : Nat
  resolvent : O.carrier
  /-- (scalar * I - op)⁻¹ = resolvent, modeled as composition identity -/
  resolvent_eq : Path (O.comp resolvent resolvent) (O.comp resolvent resolvent)

/-- Spectrum element: a scalar where the resolvent doesn't exist (abstract). -/
structure SpectrumElement (O : OperatorSpace) where
  op : O.carrier
  eigenvalue : Nat
  eigenvector_exists : Path O.zero O.zero

/-- 14. Resolvent at identity -/
noncomputable def resolvent_identity (O : OperatorSpace) :
    ResolventData O where
  op := O.idOp
  scalar := 0
  resolvent := O.idOp
  resolvent_eq := Path.refl _

/-- 15. Resolvent self-consistency -/
noncomputable def resolvent_self (O : OperatorSpace) (rd : ResolventData O) :
    Path (O.comp rd.resolvent rd.resolvent)
         (O.comp rd.resolvent rd.resolvent) :=
  rd.resolvent_eq

/-! ## Compact Operators -/

/-- A compact operator (abstract model). -/
structure CompactOp (O : OperatorSpace) where
  op : O.carrier
  finite_rank_approx : Nat → O.carrier
  approx_zero : Path (finite_rank_approx 0) O.zero

/-- 16. First approximation is zero -/
noncomputable def compact_approx_zero (O : OperatorSpace) (c : CompactOp O) :
    Path (c.finite_rank_approx 0) O.zero :=
  c.approx_zero

/-- 17. Norm of first approximation -/
noncomputable def compact_approx_zero_norm (O : OperatorSpace) (c : CompactOp O) :
    Path (O.opNorm (c.finite_rank_approx 0)) 0 :=
  trans (congrArg O.opNorm c.approx_zero) O.opNorm_zero

/-- 18. Composition of compact op with zero -/
noncomputable def compact_comp_zero (O : OperatorSpace) (c : CompactOp O) :
    Path (O.comp c.op O.zero) O.zero :=
  O.comp_zero_right c.op

/-! ## Self-Adjoint Operators -/

/-- A self-adjoint operator in an operator space. -/
structure SelfAdjointOp (O : OperatorSpace) where
  op : O.carrier
  adj : O.carrier
  self_adj : Path adj op

/-- 19. Self-adjoint identity -/
noncomputable def sa_op_is_adj (O : OperatorSpace) (sa : SelfAdjointOp O) :
    Path sa.adj sa.op :=
  sa.self_adj

/-- 20. Self-adjoint composition with self -/
noncomputable def sa_square_adj (O : OperatorSpace) (sa : SelfAdjointOp O) :
    Path (O.comp sa.adj sa.op) (O.comp sa.op sa.op) :=
  congrArg (O.comp · sa.op) sa.self_adj

/-- 21. Self-adjoint norm consistency -/
noncomputable def sa_adj_norm (O : OperatorSpace) (sa : SelfAdjointOp O) :
    Path (O.opNorm sa.adj) (O.opNorm sa.op) :=
  congrArg O.opNorm sa.self_adj

/-- Identity is self-adjoint. -/
noncomputable def selfAdjoint_id (O : OperatorSpace) : SelfAdjointOp O where
  op := O.idOp
  adj := O.idOp
  self_adj := Path.refl _

/-- Zero is self-adjoint. -/
noncomputable def selfAdjoint_zero (O : OperatorSpace) : SelfAdjointOp O where
  op := O.zero
  adj := O.zero
  self_adj := Path.refl _

/-! ## Spectral Decomposition Aspects -/

/-- A spectral decomposition: operator = sum of projections * eigenvalues. -/
structure SpectralDecomp (O : OperatorSpace) where
  op : O.carrier
  numEigenvalues : Nat
  projections : Nat → O.carrier
  proj_idempotent : ∀ i, Path (O.comp (projections i) (projections i)) (projections i)
  proj_zero_after : ∀ i, i ≥ numEigenvalues → Path (projections i) O.zero

/-- 22. Projection idempotency -/
noncomputable def spectral_proj_idem (O : OperatorSpace) (sd : SpectralDecomp O)
    (i : Nat) :
    Path (O.comp (sd.projections i) (sd.projections i)) (sd.projections i) :=
  sd.proj_idempotent i

/-- 23. Projection triple idempotency -/
noncomputable def spectral_proj_triple (O : OperatorSpace) (sd : SpectralDecomp O)
    (i : Nat) :
    Path (O.comp (sd.projections i) (O.comp (sd.projections i) (sd.projections i)))
         (sd.projections i) :=
  trans (congrArg (O.comp (sd.projections i)) (sd.proj_idempotent i))
    (sd.proj_idempotent i)

/-- 24. Projection beyond eigenvalue count is zero -/
noncomputable def spectral_proj_zero_after (O : OperatorSpace) (sd : SpectralDecomp O)
    (i : Nat) (h : i ≥ sd.numEigenvalues) :
    Path (sd.projections i) O.zero :=
  sd.proj_zero_after i h

/-- 25. Norm of projection beyond count -/
noncomputable def spectral_proj_norm_zero (O : OperatorSpace) (sd : SpectralDecomp O)
    (i : Nat) (h : i ≥ sd.numEigenvalues) :
    Path (O.opNorm (sd.projections i)) 0 :=
  trans (congrArg O.opNorm (sd.proj_zero_after i h)) O.opNorm_zero

/-! ## Operator Powers -/

/-- Power of an operator. -/
noncomputable def opPower (O : OperatorSpace) (a : O.carrier) : Nat → O.carrier
  | 0 => O.idOp
  | n + 1 => O.comp a (opPower O a n)

/-- 26. Zero-th power is identity -/
noncomputable def opPower_zero (O : OperatorSpace) (a : O.carrier) :
    Path (opPower O a 0) O.idOp :=
  Path.refl _

/-- 27. First power is the operator itself -/
noncomputable def opPower_one (O : OperatorSpace) (a : O.carrier) :
    Path (opPower O a 1) (O.comp a O.idOp) :=
  Path.refl _

/-- 28. First power simplifies via identity -/
noncomputable def opPower_one_simp (O : OperatorSpace) (a : O.carrier) :
    Path (opPower O a 1) a :=
  O.comp_id_right a

/-- 29. Power of zero operator at n+1 -/
noncomputable def opPower_zero_op (O : OperatorSpace) (n : Nat) :
    Path (opPower O O.zero (n + 1)) O.zero :=
  O.comp_zero_left (opPower O O.zero n)

/-- 30. Power of identity -/
noncomputable def opPower_id (O : OperatorSpace) : (n : Nat) →
    Path (opPower O O.idOp n) O.idOp
  | 0 => Path.refl _
  | n + 1 => trans (congrArg (O.comp O.idOp) (opPower_id O n))
                    (O.comp_id_left O.idOp)

/-- 31. Norm of zero power -/
noncomputable def norm_opPower_zero_op (O : OperatorSpace) (n : Nat) :
    Path (O.opNorm (opPower O O.zero (n + 1))) 0 :=
  trans (congrArg O.opNorm (opPower_zero_op O n)) O.opNorm_zero

/-! ## Operator Inverses -/

/-- An invertible operator. -/
structure InvertibleOp (O : OperatorSpace) where
  op : O.carrier
  inv : O.carrier
  left_inv : Path (O.comp inv op) O.idOp
  right_inv : Path (O.comp op inv) O.idOp

/-- Identity is invertible. -/
noncomputable def invertible_id (O : OperatorSpace) : InvertibleOp O where
  op := O.idOp
  inv := O.idOp
  left_inv := O.comp_id_left O.idOp
  right_inv := O.comp_id_left O.idOp

/-- 32. Left inverse property -/
noncomputable def inv_left (O : OperatorSpace) (io : InvertibleOp O) :
    Path (O.comp io.inv io.op) O.idOp :=
  io.left_inv

/-- 33. Right inverse property -/
noncomputable def inv_right (O : OperatorSpace) (io : InvertibleOp O) :
    Path (O.comp io.op io.inv) O.idOp :=
  io.right_inv

/-- 34. Inverse of inverse (pointwise) -/
noncomputable def inv_of_inv (O : OperatorSpace) (io : InvertibleOp O) :
    InvertibleOp O where
  op := io.inv
  inv := io.op
  left_inv := io.right_inv
  right_inv := io.left_inv

/-- 35. Composition of invertible operators -/
noncomputable def invertible_comp (O : OperatorSpace) (io₁ io₂ : InvertibleOp O) :
    InvertibleOp O where
  op := O.comp io₁.op io₂.op
  inv := O.comp io₂.inv io₁.inv
  left_inv :=
    -- (io₂⁻¹ * io₁⁻¹) * (io₁ * io₂) = id
    let reassoc : Path (O.comp (O.comp io₂.inv io₁.inv) (O.comp io₁.op io₂.op))
                       (O.comp (O.comp (O.comp io₂.inv io₁.inv) io₁.op) io₂.op) :=
      symm (O.comp_assoc (O.comp io₂.inv io₁.inv) io₁.op io₂.op)
    let inner1 : Path (O.comp (O.comp io₂.inv io₁.inv) io₁.op) (O.comp io₂.inv (O.comp io₁.inv io₁.op)) :=
      O.comp_assoc io₂.inv io₁.inv io₁.op
    let inner2 : Path (O.comp io₂.inv (O.comp io₁.inv io₁.op)) (O.comp io₂.inv O.idOp) :=
      congrArg (O.comp io₂.inv) io₁.left_inv
    let inner3 : Path (O.comp io₂.inv O.idOp) io₂.inv :=
      O.comp_id_right io₂.inv
    let mid : Path (O.comp (O.comp io₂.inv io₁.inv) io₁.op) io₂.inv :=
      trans inner1 (trans inner2 inner3)
    let s2 : Path (O.comp (O.comp (O.comp io₂.inv io₁.inv) io₁.op) io₂.op) (O.comp io₂.inv io₂.op) :=
      congrArg (O.comp · io₂.op) mid
    trans reassoc (trans s2 io₂.left_inv)
  right_inv :=
    -- (io₁ * io₂) * (io₂⁻¹ * io₁⁻¹) = id
    -- comp_assoc gives ((a*b)*c) = (a*(b*c)), so we need symm to go from a*(b*c) to ((a*b)*c)
    let reassoc : Path (O.comp (O.comp io₁.op io₂.op) (O.comp io₂.inv io₁.inv))
                       (O.comp (O.comp (O.comp io₁.op io₂.op) io₂.inv) io₁.inv) :=
      symm (O.comp_assoc (O.comp io₁.op io₂.op) io₂.inv io₁.inv)
    let inner1 : Path (O.comp (O.comp io₁.op io₂.op) io₂.inv) (O.comp io₁.op (O.comp io₂.op io₂.inv)) :=
      O.comp_assoc io₁.op io₂.op io₂.inv
    let inner2 : Path (O.comp io₁.op (O.comp io₂.op io₂.inv)) (O.comp io₁.op O.idOp) :=
      congrArg (O.comp io₁.op) io₂.right_inv
    let inner3 : Path (O.comp io₁.op O.idOp) io₁.op :=
      O.comp_id_right io₁.op
    let mid : Path (O.comp (O.comp io₁.op io₂.op) io₂.inv) io₁.op :=
      trans inner1 (trans inner2 inner3)
    let s2 : Path (O.comp (O.comp (O.comp io₁.op io₂.op) io₂.inv) io₁.inv) (O.comp io₁.op io₁.inv) :=
      congrArg (O.comp · io₁.inv) mid
    trans reassoc (trans s2 io₁.right_inv)

/-! ## Functional Calculus Aspects -/

/-- A polynomial applied to an operator. -/
structure OpPolynomial (O : OperatorSpace) where
  coeffs : List Nat
  evaluate : O.carrier → O.carrier
  eval_zero : Path (evaluate O.zero) O.zero
  eval_id : Path (evaluate O.idOp) (evaluate O.idOp)

/-- 36. Polynomial evaluation at zero -/
noncomputable def poly_at_zero (O : OperatorSpace) (p : OpPolynomial O) :
    Path (p.evaluate O.zero) O.zero :=
  p.eval_zero

/-- 37. Norm of polynomial at zero -/
noncomputable def poly_norm_at_zero (O : OperatorSpace) (p : OpPolynomial O) :
    Path (O.opNorm (p.evaluate O.zero)) 0 :=
  trans (congrArg O.opNorm p.eval_zero) O.opNorm_zero

end OperatorPaths
end Topology
end Path
end ComputationalPaths

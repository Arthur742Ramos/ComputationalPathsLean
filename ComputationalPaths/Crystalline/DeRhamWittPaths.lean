import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Crystalline cohomology paths: de Rham-Witt complexes

This module packages a lightweight de Rham-Witt interface using computational
paths. Core identities carry explicit `Path.Step` witnesses and are exposed as
`RwEq` normalizations.
-/

namespace ComputationalPaths
namespace Crystalline
namespace DeRhamWittPaths

open Path

universe u

/-- Domain-specific rewrite tags for de Rham-Witt coherence moves. -/
inductive DeRhamWittStep : Type
  | frobeniusNaturality
  | verschiebungNaturality
  | differentialCompatibility
  | projectionCompatibility

/-- Path-aware de Rham-Witt data with explicit rewrite witnesses. -/
structure DeRhamWittPathData (Ring : Type u) where
  level : Nat → Type u
  zero : (n : Nat) → level n
  add : (n : Nat) → level n → level n → level n
  frobenius : (n : Nat) → level (n + 1) → level n
  verschiebung : (n : Nat) → level n → level (n + 1)
  differential : (n : Nat) → level n → level n
  projection : (n : Nat) → level (n + 1) → level n
  addZeroPath :
    ∀ (n : Nat) (x : level n), Path (add n x (zero n)) x
  differentialZeroPath :
    ∀ n : Nat, Path (differential n (zero n)) (zero n)
  frobeniusVerschiebungPath :
    ∀ (n : Nat) (x : level n), Path (frobenius n (verschiebung n x)) x
  projectionFrobeniusPath :
    ∀ (n : Nat) (x : level (n + 1)), Path (projection n x) (frobenius n x)
  addZeroStep :
    ∀ (n : Nat) (x : level n),
      Path.Step
        (Path.trans (addZeroPath n x) (Path.refl x))
        (addZeroPath n x)
  differentialZeroStep :
    ∀ n : Nat,
      Path.Step
        (Path.trans (differentialZeroPath n) (Path.refl (zero n)))
        (differentialZeroPath n)
  frobeniusVerschiebungStep :
    ∀ (n : Nat) (x : level n),
      Path.Step
        (Path.trans (frobeniusVerschiebungPath n x) (Path.refl x))
        (frobeniusVerschiebungPath n x)
  projectionFrobeniusStep :
    ∀ (n : Nat) (x : level (n + 1)),
      Path.Step
        (Path.trans (projectionFrobeniusPath n x) (Path.refl (frobenius n x)))
        (projectionFrobeniusPath n x)

namespace DeRhamWittPathData

variable {Ring : Type u} (W : DeRhamWittPathData Ring)

/-- Functorial transport of paths along Frobenius. -/
noncomputable def frobeniusTransport {n : Nat} {x y : W.level (n + 1)} (p : Path x y) :
    Path (W.frobenius n x) (W.frobenius n y) :=
  Path.congrArg (W.frobenius n) p

/-- Functorial transport of paths along Verschiebung. -/
noncomputable def verschiebungTransport {n : Nat} {x y : W.level n} (p : Path x y) :
    Path (W.verschiebung n x) (W.verschiebung n y) :=
  Path.congrArg (W.verschiebung n) p

noncomputable def addZero_rweq (n : Nat) (x : W.level n) :
    RwEq
      (Path.trans (W.addZeroPath n x) (Path.refl x))
      (W.addZeroPath n x) :=
  rweq_of_step (W.addZeroStep n x)

noncomputable def differentialZero_rweq (n : Nat) :
    RwEq
      (Path.trans (W.differentialZeroPath n) (Path.refl (W.zero n)))
      (W.differentialZeroPath n) :=
  rweq_of_step (W.differentialZeroStep n)

noncomputable def frobeniusVerschiebung_rweq (n : Nat) (x : W.level n) :
    RwEq
      (Path.trans (W.frobeniusVerschiebungPath n x) (Path.refl x))
      (W.frobeniusVerschiebungPath n x) :=
  rweq_of_step (W.frobeniusVerschiebungStep n x)

noncomputable def frobeniusVerschiebung_cancel_rweq (n : Nat) (x : W.level n) :
    RwEq
      (Path.trans (Path.symm (W.frobeniusVerschiebungPath n x))
        (W.frobeniusVerschiebungPath n x))
      (Path.refl x) :=
  rweq_cmpA_inv_left (W.frobeniusVerschiebungPath n x)

noncomputable def projectionFrobenius_rweq (n : Nat) (x : W.level (n + 1)) :
    RwEq
      (Path.trans (W.projectionFrobeniusPath n x) (Path.refl (W.frobenius n x)))
      (W.projectionFrobeniusPath n x) :=
  rweq_of_step (W.projectionFrobeniusStep n x)

/-- Primitive right-unit normalization witness for `frobeniusTransport`. -/
noncomputable def frobeniusTransport_step {n : Nat} {x y : W.level (n + 1)} (p : Path x y) :
    Path.Step
      (Path.trans (W.frobeniusTransport p) (Path.refl (W.frobenius n y)))
      (W.frobeniusTransport p) :=
  Path.Step.trans_refl_right (W.frobeniusTransport p)

noncomputable def frobeniusTransport_rweq {n : Nat} {x y : W.level (n + 1)}
    (p : Path x y) :
    RwEq
      (Path.trans (W.frobeniusTransport p) (Path.refl (W.frobenius n y)))
      (W.frobeniusTransport p) :=
  rweq_of_step (W.frobeniusTransport_step p)

/-- Primitive right-unit normalization witness for `verschiebungTransport`. -/
noncomputable def verschiebungTransport_step {n : Nat} {x y : W.level n} (p : Path x y) :
    Path.Step
      (Path.trans (W.verschiebungTransport p) (Path.refl (W.verschiebung n y)))
      (W.verschiebungTransport p) :=
  Path.Step.trans_refl_right (W.verschiebungTransport p)

noncomputable def verschiebungTransport_rweq {n : Nat} {x y : W.level n}
    (p : Path x y) :
    RwEq
      (Path.trans (W.verschiebungTransport p) (Path.refl (W.verschiebung n y)))
      (W.verschiebungTransport p) :=
  rweq_of_step (W.verschiebungTransport_step p)

end DeRhamWittPathData

/-- Trivial de Rham-Witt path package on `PUnit`. -/
noncomputable def trivialDeRhamWittPathData (Ring : Type u) : DeRhamWittPathData Ring where
  level := fun _ => PUnit
  zero := fun _ => PUnit.unit
  add := fun _ _ _ => PUnit.unit
  frobenius := fun _ _ => PUnit.unit
  verschiebung := fun _ _ => PUnit.unit
  differential := fun _ _ => PUnit.unit
  projection := fun _ _ => PUnit.unit
  addZeroPath := fun _ _ => Path.refl PUnit.unit
  differentialZeroPath := fun _ => Path.refl PUnit.unit
  frobeniusVerschiebungPath := fun _ _ => Path.refl PUnit.unit
  projectionFrobeniusPath := fun _ _ => Path.refl PUnit.unit
  addZeroStep := fun _ _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)
  differentialZeroStep := fun _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)
  frobeniusVerschiebungStep := fun _ _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)
  projectionFrobeniusStep := fun _ _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)

end DeRhamWittPaths
end Crystalline
end ComputationalPaths

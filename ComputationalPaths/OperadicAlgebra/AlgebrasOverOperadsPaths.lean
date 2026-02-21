import ComputationalPaths.Path.Algebra.OperadTheory
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Algebras over operads as computational paths

This module packages algebras over operads with explicit path-preserving
coherence data and domain-specific normalization steps.
-/

namespace ComputationalPaths
namespace OperadicAlgebra

open Path

universe u v w

/-- Domain-specific rewrite steps for operadic algebra coherence paths. -/
inductive OperadAlgebraStep {A : Type u} :
    {a b : A} → Path a b → Path a b → Prop where
  | right_unit {a b : A} (p : Path a b) :
      OperadAlgebraStep (Path.trans p (Path.refl b)) p
  | left_unit {a b : A} (p : Path a b) :
      OperadAlgebraStep (Path.trans (Path.refl a) p) p
  | inverse_cancel {a b : A} (p : Path a b) :
      OperadAlgebraStep (Path.trans p (Path.symm p)) (Path.refl a)

/-- Interpret an operadic-algebra domain step as a primitive `Path.Step`. -/
def OperadAlgebraStep.toStep {A : Type u} {a b : A} {p q : Path a b}
    (s : OperadAlgebraStep p q) : Path.Step p q :=
  match s with
  | .right_unit p => Path.Step.trans_refl_right p
  | .left_unit p => Path.Step.trans_refl_left p
  | .inverse_cancel p => Path.Step.trans_symm p

/-- Lift an operadic-algebra normalization step to rewrite equivalence. -/
noncomputable def rweq_of_operad_algebra_step {A : Type u} {a b : A}
    {p q : Path a b} (s : OperadAlgebraStep p q) : RwEq p q :=
  rweq_of_step (OperadAlgebraStep.toStep s)

/-- Algebra over an operad with path-preserving coherence witnesses. -/
structure AlgebraOverOperadPathData
    (O : Path.Algebra.OperadTheory.CleanOperad) (A : Type v) where
  /-- Operad action on arity-indexed tuples. -/
  act : {n : Nat} → O.ops n → (Fin n → A) → A
  /-- Action of the operadic unit. -/
  unitActionPath : ∀ x : A, Path (act O.unit (fun _ => x)) x
  /-- Equivariance under symmetric-group action. -/
  equivariantPath :
    {n : Nat} → ∀ (σ : Path.Algebra.OperadTheory.Perm n) (θ : O.ops n) (xs : Fin n → A),
      Path (act (O.action σ θ) xs) (act θ (xs ∘ σ.invFun))
  /-- Right-unit normalization for unit action. -/
  unitActionStep :
    ∀ x : A,
      OperadAlgebraStep
        (Path.trans (unitActionPath x) (Path.refl x))
        (unitActionPath x)
  /-- Left-unit normalization for equivariance witness. -/
  equivariantStep :
    {n : Nat} → ∀ (σ : Path.Algebra.OperadTheory.Perm n) (θ : O.ops n) (xs : Fin n → A),
      OperadAlgebraStep
        (Path.trans (Path.refl (act (O.action σ θ) xs)) (equivariantPath σ θ xs))
        (equivariantPath σ θ xs)

namespace AlgebraOverOperadPathData

variable {O : Path.Algebra.OperadTheory.CleanOperad}
variable {A : Type v}
variable (D : AlgebraOverOperadPathData O A)

noncomputable def unit_action_rweq (x : A) :
    RwEq
      (Path.trans (D.unitActionPath x) (Path.refl x))
      (D.unitActionPath x) :=
  rweq_of_operad_algebra_step (D.unitActionStep x)

noncomputable def equivariant_rweq
    {n : Nat} (σ : Path.Algebra.OperadTheory.Perm n) (θ : O.ops n) (xs : Fin n → A) :
    RwEq
      (Path.trans (Path.refl (D.act (O.action σ θ) xs)) (D.equivariantPath σ θ xs))
      (D.equivariantPath σ θ xs) :=
  rweq_of_operad_algebra_step (D.equivariantStep σ θ xs)

/-- Round-trip path for a symmetry action witness. -/
def actionRoundTrip
    {n : Nat} (σ : Path.Algebra.OperadTheory.Perm n) (θ : O.ops n) (xs : Fin n → A) :
    Path (D.act (O.action σ θ) xs) (D.act (O.action σ θ) xs) :=
  Path.trans (D.equivariantPath σ θ xs) (Path.symm (D.equivariantPath σ θ xs))

noncomputable def action_roundtrip_rweq
    {n : Nat} (σ : Path.Algebra.OperadTheory.Perm n) (θ : O.ops n) (xs : Fin n → A) :
    RwEq (D.actionRoundTrip σ θ xs) (Path.refl (D.act (O.action σ θ) xs)) := by
  unfold actionRoundTrip
  exact rweq_cmpA_inv_right (D.equivariantPath σ θ xs)

/-- Transport operad action data along a map of carrier types. -/
def mapPath {B : Type w} (f : A → B) {x y : A} (p : Path x y) : Path (f x) (f y) :=
  Path.congrArg f p

end AlgebraOverOperadPathData

/-- The trivial path-preserving algebra over any operad. -/
def AlgebraOverOperadPathData.trivial (O : Path.Algebra.OperadTheory.CleanOperad) :
    AlgebraOverOperadPathData O Unit where
  act := fun _ _ => ()
  unitActionPath := fun _ => Path.refl ()
  equivariantPath := fun _ _ _ => Path.refl ()
  unitActionStep := fun _ => OperadAlgebraStep.right_unit (Path.refl ())
  equivariantStep := fun _ _ _ => OperadAlgebraStep.left_unit (Path.refl ())

/-- Upgrade an `OperadTheory.OperadAlgebra` to path-preserving coherence data,
using an explicit unit path witness. -/
def AlgebraOverOperadPathData.ofOperadAlgebra
    (O : Path.Algebra.OperadTheory.CleanOperad)
    (alg : Path.Algebra.OperadTheory.OperadAlgebra O)
    (unitPath : ∀ x : alg.carrier, Path (alg.act O.unit (fun _ => x)) x) :
    AlgebraOverOperadPathData O alg.carrier where
  act := alg.act
  unitActionPath := unitPath
  equivariantPath := fun σ θ xs => Path.stepChain (alg.equivariant σ θ xs)
  unitActionStep := fun x => OperadAlgebraStep.right_unit (unitPath x)
  equivariantStep := fun σ θ xs =>
    OperadAlgebraStep.left_unit (Path.stepChain (alg.equivariant σ θ xs))

/-- Path-preserving morphism between operadic algebras. -/
structure OperadAlgebraMorphismPathData
    {O : Path.Algebra.OperadTheory.CleanOperad}
    {A B : Type v}
    (X : AlgebraOverOperadPathData O A)
    (Y : AlgebraOverOperadPathData O B) where
  /-- Underlying map of carriers. -/
  toFun : A → B
  /-- Compatibility with operad action, as a computational path. -/
  mapActionPath :
    {n : Nat} → ∀ (θ : O.ops n) (xs : Fin n → A),
      Path (toFun (X.act θ xs)) (Y.act θ (toFun ∘ xs))
  /-- Right-unit normalization for compatibility paths. -/
  mapActionStep :
    {n : Nat} → ∀ (θ : O.ops n) (xs : Fin n → A),
      OperadAlgebraStep
        (Path.trans (mapActionPath θ xs)
          (Path.refl (Y.act θ (toFun ∘ xs))))
        (mapActionPath θ xs)

namespace OperadAlgebraMorphismPathData

variable {O : Path.Algebra.OperadTheory.CleanOperad}
variable {A B : Type v}
variable {X : AlgebraOverOperadPathData O A}
variable {Y : AlgebraOverOperadPathData O B}
variable (f : OperadAlgebraMorphismPathData X Y)

noncomputable def map_action_rweq
    {n : Nat} (θ : O.ops n) (xs : Fin n → A) :
    RwEq
      (Path.trans (f.mapActionPath θ xs)
        (Path.refl (Y.act θ (f.toFun ∘ xs))))
      (f.mapActionPath θ xs) :=
  rweq_of_operad_algebra_step (f.mapActionStep θ xs)

/-- Identity path-preserving operadic algebra morphism. -/
def id (X : AlgebraOverOperadPathData O A) :
    OperadAlgebraMorphismPathData X X where
  toFun := _root_.id
  mapActionPath := fun _ _ => Path.refl _
  mapActionStep := fun _ _ => OperadAlgebraStep.right_unit (Path.refl _)

end OperadAlgebraMorphismPathData

end OperadicAlgebra
end ComputationalPaths

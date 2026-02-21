/-!
# Deep Loop-Space Package for CompPaths

This module packages loop-space deepening results in the `CompPaths` facade:
`Ω`, `Ω²`, `Ωⁿ`, basepoint-change conjugation, and the James map.
-/

import CompPaths.Core
import ComputationalPaths.Path.Homotopy.LoopSpaceAlgebra
import ComputationalPaths.Path.Homotopy.EckmannHilton
import ComputationalPaths.Path.Homotopy.IteratedLoopSpace
import ComputationalPaths.Path.Homotopy.FundamentalGroupoid
import ComputationalPaths.Path.Homotopy.JamesConstruction

namespace CompPaths
namespace Homotopy
namespace LoopSpaceDeep

open ComputationalPaths
open ComputationalPaths.Path
open ComputationalPaths.Path.Homotopy

universe u

section OmegaOne

variable {A : Type u} {a : A}

/-- Based loop space `Ω(A, a)`. -/
abbrev Omega (A : Type u) (a : A) : Type u :=
  LoopSpace A a

/-- Loop multiplication from path concatenation. -/
@[simp] def omegaMul (p q : Omega A a) : Omega A a :=
  Path.trans p q

/-- Loop identity at the basepoint. -/
@[simp] def omegaOne : Omega A a :=
  Path.refl a

/-- Loop inverse from path symmetry. -/
@[simp] def omegaInv (p : Omega A a) : Omega A a :=
  Path.symm p

/-- Associativity witness for `Ω(A, a)`. -/
noncomputable def omegaMulAssocRwEq (p q r : Omega A a) :
    RwEq (omegaMul (omegaMul p q) r) (omegaMul p (omegaMul q r)) :=
  rweq_of_step (Step.trans_assoc p q r)

/-- Left identity witness for `Ω(A, a)`. -/
noncomputable def omegaOneMulRwEq (p : Omega A a) :
    RwEq (omegaMul omegaOne p) p :=
  rweq_of_step (Step.trans_refl_left p)

/-- Right identity witness for `Ω(A, a)`. -/
noncomputable def omegaMulOneRwEq (p : Omega A a) :
    RwEq (omegaMul p omegaOne) p :=
  rweq_of_step (Step.trans_refl_right p)

/-- Left inverse witness for `Ω(A, a)`. -/
noncomputable def omegaInvMulRwEq (p : Omega A a) :
    RwEq (omegaMul (omegaInv p) p) omegaOne :=
  rweq_of_step (Step.symm_trans p)

/-- Right inverse witness for `Ω(A, a)`. -/
noncomputable def omegaMulInvRwEq (p : Omega A a) :
    RwEq (omegaMul p (omegaInv p)) omegaOne :=
  rweq_of_step (Step.trans_symm p)

/-- Canonical loop-space group object with laws witnessed by `RwEq`. -/
noncomputable def omegaGroupWitness (A : Type u) (a : A) :
    LoopSpaceAlgebra.LoopSpaceGroup A a :=
  LoopSpaceAlgebra.loopSpaceGroup A a

end OmegaOne

section OmegaTwo

variable {A : Type u} {a : A}

/-- Double loop space `Ω²(A, a)` at `refl a`. -/
abbrev OmegaTwo (A : Type u) (a : A) : Type u :=
  EckmannHilton.OmegaTwo A a

/-- Explicit `RwEq` witness on `refl · refl`. -/
noncomputable def omegaTwoReflRwEq (a : A) :
    RwEq (Path.trans (Path.refl a) (Path.refl a)) (Path.refl a) :=
  rweq_of_step (Step.trans_refl_left (Path.refl a))

/-- Explicit interchange witness used in the Eckmann-Hilton argument. -/
def omegaTwoInterchangeStep (α β : OmegaTwo A a) :
    Derivation₃ (EckmannHilton.OmegaTwo.hcomp α β) (EckmannHilton.hcomp' α β) :=
  EckmannHilton.interchange_omegaTwo α β

/-- `Ω²` is abelian (Eckmann-Hilton), as a 3-cell witness. -/
def omegaTwoAbelianDerivation (α β : OmegaTwo A a) :
    Derivation₃ (EckmannHilton.OmegaTwo.vcomp α β) (EckmannHilton.OmegaTwo.vcomp β α) :=
  EckmannHilton.eckmann_hilton α β

/-- `Ω²` abelianity at the induced `RwEq` level. -/
theorem omegaTwoAbelianRwEq (α β : OmegaTwo A a) :
    Derivation₂.toRwEq (EckmannHilton.OmegaTwo.vcomp α β) =
      Derivation₂.toRwEq (EckmannHilton.OmegaTwo.vcomp β α) :=
  EckmannHilton.eckmann_hilton_rweq α β

end OmegaTwo

section IteratedLoops

/-- Pointed-space shorthand for iterated loop constructions. -/
abbrev Pointed := SuspensionLoop.Pointed

/-- Iterated loop spaces `Ωⁿ` as pointed types. -/
noncomputable abbrev OmegaN (n : Nat) (X : Pointed) : Pointed :=
  IteratedLoopSpace.OmegaN n X

theorem omegaN_zero (X : Pointed) : OmegaN 0 X = X :=
  IteratedLoopSpace.omegaN_zero X

theorem omegaN_succ (n : Nat) (X : Pointed) :
    OmegaN (n + 1) X = SuspensionLoop.loopPointed (OmegaN n X) :=
  IteratedLoopSpace.omegaN_succ n X

/-- The delooping existence question for `Ωⁿ`. -/
def DeloopingQuestion (X : Pointed) (n : Nat) : Prop :=
  Nonempty (IteratedLoopSpace.IteratedDelooping X n)

/-- The zero-stage delooping exists canonically. -/
theorem deloopingQuestion_zero (X : Pointed) :
    DeloopingQuestion X 0 :=
  ⟨IteratedLoopSpace.IteratedDelooping.zero X⟩

end IteratedLoops

section ConjugationFunctor

variable {A : Type u} {a b : A}

/-- Conjugation sends loops at `a` to loops at `b` along `p : a ⟶ b`. -/
def omegaConjugate (p : Path a b) (ℓ : Omega A a) : Omega A b :=
  Path.trans (Path.symm p) (Path.trans ℓ p)

/-- Conjugation is natural in `RwEq` on source loops. -/
noncomputable def omegaConjugateNaturality (p : Path a b) {ℓ₁ ℓ₂ : Omega A a}
    (h : RwEq ℓ₁ ℓ₂) :
    RwEq (omegaConjugate p ℓ₁) (omegaConjugate p ℓ₂) :=
  rweq_trans_congr_right (Path.symm p) (rweq_trans_congr_left p h)

/-- On `π₁`, conjugation along `p` is the basepoint-change group isomorphism. -/
noncomputable def omegaConjugatePiOneIso (p : Path a b) :
    SimpleEquiv (π₁(A, a)) (π₁(A, b)) :=
  FundamentalGroupoid.basepointIsomorphism p

/-- Naturality of conjugation with respect to induced maps. -/
theorem omegaConjugatePiOneNaturality {B : Type u} (f : A → B)
    (p : Path a b) (α : π₁(A, a)) :
    FundamentalGroupoid.inducedPiOneMap f b
      (FundamentalGroupoid.conjugateByPath p α) =
      FundamentalGroupoid.conjugateByPath
        (FundamentalGroupoid.fundamentalGroupoidMap f p)
        (FundamentalGroupoid.inducedPiOneMap f a α) := by
  simpa using
    FundamentalGroupoid.inducedPiOneMap_conjugateByPath (f := f) p α

end ConjugationFunctor

section JamesConnection

variable {A : Type u} {a : A}

/-- `Ω(A, a)` as a pointed type. -/
def omegaPointed (A : Type u) (a : A) : SuspensionLoop.Pointed where
  carrier := Omega A a
  pt := Path.refl a

/-- James construction on `Ω(A, a)` (reduced free monoid model). -/
abbrev JamesOnOmega (A : Type u) (a : A) : Type u :=
  JamesConstruction.JamesConstruction (omegaPointed A a)

/-- Canonical map from free-monoid data on `Ω` to loop paths. -/
noncomputable def jamesOnOmegaToPath :
    JamesOnOmega A a →
      LoopSpace (SuspensionLoop.Suspension (Omega A a))
        (SuspensionLoop.Suspension.north (X := Omega A a)) :=
  JamesConstruction.jamesToLoop (omegaPointed A a)

/-- The James basepoint maps to reflexivity. -/
noncomputable def jamesOnOmega_base :
    Path
      (jamesOnOmegaToPath (A := A) (a := a)
        (JamesConstruction.jamesBase (omegaPointed A a)))
      (Path.refl (SuspensionLoop.Suspension.north (X := Omega A a))) :=
  JamesConstruction.jamesToLoop_base (omegaPointed A a)

/-- James multiplication maps to loop concatenation. -/
noncomputable def jamesOnOmega_mul (x y : JamesOnOmega A a) :
    Path
      (jamesOnOmegaToPath (A := A) (a := a)
        (JamesConstruction.jamesMul (omegaPointed A a) x y))
      (LoopSpace.comp
        (jamesOnOmegaToPath (A := A) (a := a) x)
        (jamesOnOmegaToPath (A := A) (a := a) y)) :=
  JamesConstruction.jamesToLoop_mul (omegaPointed A a) x y

end JamesConnection

end LoopSpaceDeep
end Homotopy
end CompPaths

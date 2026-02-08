/-
# Homotopy Invariance of the Fundamental Group

This module defines homotopy equivalence for computational path spaces and
proves that homotopy-equivalent spaces have isomorphic fundamental groups.

## Key Results
- `HomotopyEquiv`: Homotopy equivalence between computational path spaces.
- `inducedPiOneMap_comp`: Composition law for induced π₁ maps.
- `HomotopyEquiv.piOneEquiv`: π₁ invariance under homotopy equivalence.
-/

import ComputationalPaths.Path.Homotopy.HoTT
import ComputationalPaths.Path.Homotopy.FundamentalGroupoid

namespace ComputationalPaths
namespace Path

open HoTT

universe u

/-! ## Homotopy equivalences -/

/-- Convert a function homotopy into propositional equality of functions. -/
theorem funHomotopy_toEq {A : Type u} {B : Type u} {f g : A → B}
    (H : FunHomotopy f g) : f = g := by
  funext x
  exact (H x).toEq

/-- A homotopy equivalence between computational path spaces. -/
structure HomotopyEquiv (A : Type u) (B : Type u) : Type u where
  /-- Forward map. -/
  toFun : A → B
  /-- Inverse map. -/
  invFun : B → A
  /-- Homotopy f ∘ g ~ id. -/
  leftHomotopy : FunHomotopy (fun b => toFun (invFun b)) (fun b => b)
  /-- Homotopy g ∘ f ~ id. -/
  rightHomotopy : FunHomotopy (fun a => invFun (toFun a)) (fun a => a)

namespace HomotopyEquiv

variable {A : Type u} {B : Type u}

/-- The left homotopy as an equality of functions. -/
theorem left_eq (e : HomotopyEquiv A B) : e.toFun ∘ e.invFun = id := by
  exact funHomotopy_toEq e.leftHomotopy

/-- The right homotopy as an equality of functions. -/
theorem right_eq (e : HomotopyEquiv A B) : e.invFun ∘ e.toFun = id := by
  exact funHomotopy_toEq e.rightHomotopy

/-- The right homotopy evaluated at a basepoint. -/
theorem right_point (e : HomotopyEquiv A B) (a : A) : e.invFun (e.toFun a) = a := by
  have h := e.right_eq
  simpa [Function.comp] using _root_.congrArg (fun h => h a) h

/-- The left homotopy evaluated at a basepoint. -/
theorem left_point (e : HomotopyEquiv A B) (b : B) : e.toFun (e.invFun b) = b := by
  have h := e.left_eq
  simpa [Function.comp] using _root_.congrArg (fun h => h b) h

end HomotopyEquiv

/-! ## Induced maps on π₁ -/

/-- Transport π₁ along equality of basepoints. -/
@[simp] def castPiOne {A : Type u} {a b : A} (h : a = b) :
    π₁(A, a) → π₁(A, b) :=
  fun α => Eq.ndrec (motive := fun x => π₁(A, x)) α h

@[simp] theorem castPiOne_rfl {A : Type u} {a : A} (α : π₁(A, a)) :
    castPiOne (A := A) (a := a) (b := a) rfl α = α := rfl

/-- Composition law for induced maps on fundamental groups. -/
theorem inducedPiOneMap_comp {A : Type u} {B : Type u} {C : Type u}
    (f : A → B) (g : B → C) (a : A) (α : π₁(A, a)) :
    inducedPiOneMap g (f a) (inducedPiOneMap f a α) =
      inducedPiOneMap (g ∘ f) a α := by
  simp [inducedPiOneMap, fundamentalGroupoidMap]

/-! ## Homotopy invariance of π₁ -/

/-- Homotopy equivalences induce isomorphisms on fundamental groups. -/
noncomputable def HomotopyEquiv.piOneEquiv {A : Type u} {B : Type u}
    (e : HomotopyEquiv A B) (a : A) :
    SimpleEquiv (π₁(A, a)) (π₁(B, e.toFun a)) := by
  let a' := e.invFun (e.toFun a)
  let b' := e.toFun a'
  have hpointA : a' = a := by
    simpa [a'] using HomotopyEquiv.right_point e a
  have hpointB : b' = e.toFun a := by
    simpa [a', b'] using HomotopyEquiv.left_point e (e.toFun a)
  have hpointInv : e.invFun b' = a' := by
    simpa [b'] using HomotopyEquiv.right_point e a'
  let toFun' : π₁(A, a') → π₁(B, b') :=
    inducedPiOneMap e.toFun a'
  let invFun' : π₁(B, b') → π₁(A, a') :=
    fun β =>
      castPiOne (A := A) (a := e.invFun b') (b := a') hpointInv
        (inducedPiOneMap e.invFun b' β)
  have hright : e.invFun ∘ e.toFun = id := HomotopyEquiv.right_eq e
  have hleft : e.toFun ∘ e.invFun = id := HomotopyEquiv.left_eq e
  have equiv' : SimpleEquiv (π₁(A, a')) (π₁(B, b')) :=
    { toFun := toFun'
      invFun := invFun'
      left_inv := by
        intro α
        have hcalc :
            inducedPiOneMap e.invFun b' (inducedPiOneMap e.toFun a' α) = α := by
          cases hpointInv
          calc
            inducedPiOneMap e.invFun b' (inducedPiOneMap e.toFun a' α)
                = inducedPiOneMap (e.invFun ∘ e.toFun) a' α := by
                    simpa using
                      (inducedPiOneMap_comp (f := e.toFun) (g := e.invFun)
                        (a := a') (α := α))
            _ = inducedPiOneMap id a' α := by
                  simpa [hright, Function.comp]
            _ = α := inducedPiOneMap_idFun (a := a') α
        simpa [invFun', castPiOne, hpointInv] using hcalc
      right_inv := by
        intro β
        have hcalc :
            inducedPiOneMap e.toFun (e.invFun b')
                (inducedPiOneMap e.invFun b' β) = β := by
          cases hpointInv
          calc
            inducedPiOneMap e.toFun (e.invFun b')
                (inducedPiOneMap e.invFun b' β)
                = inducedPiOneMap (e.toFun ∘ e.invFun) b' β := by
                    simpa using
                      (inducedPiOneMap_comp (f := e.invFun) (g := e.toFun)
                        (a := b') (α := β))
            _ = inducedPiOneMap id b' β := by
                  simpa [hleft, Function.comp]
            _ = β := inducedPiOneMap_idFun (a := b') β
        simpa [invFun', castPiOne, hpointInv] using hcalc }
  have htypeA : π₁(A, a') = π₁(A, a) := by
    simpa [hpointA]
  have htypeB : π₁(B, b') = π₁(B, e.toFun a) := by
    simpa [hpointB]
  let equivB : SimpleEquiv (π₁(A, a')) (π₁(B, e.toFun a)) :=
    (SimpleEquiv.cast htypeB equiv'.symm).symm
  exact SimpleEquiv.cast htypeA equivB


end Path
end ComputationalPaths

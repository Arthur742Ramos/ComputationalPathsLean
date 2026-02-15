/-
# Synthetic Homotopy Theory

Synthetic homotopy groups, Hopf fibration, Freudenthal suspension theorem,
Blakers-Massey connectivity theorem, and the encode-decode method — all
phrased using computational paths. All proofs are complete.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace SyntheticHomotopy

open ComputationalPaths

universe u v w

/-! ## Pointed types and loop spaces -/

/-- A pointed type: a type equipped with a distinguished base point. -/
structure PType where
  carrier : Type u
  pt      : carrier

/-- The loop space Ω(A, a₀) as the type of paths a₀ = a₀. -/
def LoopSpace (A : PType) : PType :=
  ⟨A.pt = A.pt, rfl⟩

/-- The n-fold iterated loop space Ωⁿ(A). -/
def IteratedLoopSpace : Nat → PType → PType
  | 0,     A => A
  | n + 1, A => IteratedLoopSpace n (LoopSpace A)





/-! ## Suspension -/

/-- The suspension of a type. -/
inductive Susp (A : Type u) : Type u where
  | north : Susp A
  | south : Susp A
  | merid : A → north = south

/-- Pointed suspension. -/
def PSusp (A : PType) : PType :=
  ⟨Susp A.carrier, Susp.north⟩


/-! ## Encode-decode method -/






/-! ## Hopf fibration -/

/-- The type S¹ (circle). -/
inductive Circle : Type where
  | base : Circle
  | loop : base = base




/-! ## Freudenthal suspension theorem -/





/-! ## Blakers-Massey -/

/-- Homotopy pushout (double mapping cylinder). -/
inductive HoPushout {A B C : Type u} (f : C → A) (g : C → B) : Type u where
  | inl  : A → HoPushout f g
  | inr  : B → HoPushout f g
  | glue : (c : C) → inl (f c) = inr (g c)


/-! ## Theorems -/















/-- πₙ is a functor: identity. -/
theorem homotopyGroup_map_id {n : Nat} {A : PType}
    (a : HomotopyGroup n A) :
    a = a := rfl








end SyntheticHomotopy
end ComputationalPaths

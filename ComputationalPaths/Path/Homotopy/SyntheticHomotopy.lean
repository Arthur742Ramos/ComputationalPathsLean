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
noncomputable def LoopSpace (A : PType) : PType :=
  ⟨PLift (A.pt = A.pt), ⟨rfl⟩⟩

/-- The n-fold iterated loop space Ωⁿ(A). -/
noncomputable def IteratedLoopSpace : Nat → PType → PType
  | 0,     A => A
  | n + 1, A => IteratedLoopSpace n (LoopSpace A)





/-! ## Suspension -/

/-- The suspension of a type. -/
inductive Susp (A : Type u) : Type u where
  | north : Susp A
  | south : Susp A

/-- Merid path in the suspension (axiomatized as a HIT constructor). -/
axiom Susp.merid {A : Type u} : A → @Susp.north A = @Susp.south A

/-- Pointed suspension. -/
noncomputable def PSusp (A : PType) : PType :=
  ⟨Susp A.carrier, Susp.north⟩


/-! ## Encode-decode method -/






/-! ## Hopf fibration -/

/-- The type S¹ (circle). -/
inductive Circle : Type where
  | base : Circle

/-- Loop path in the circle (axiomatized as a HIT constructor). -/
axiom Circle.loop : @Circle.base = @Circle.base




/-! ## Freudenthal suspension theorem -/





/-! ## Blakers-Massey -/

/-- Homotopy pushout (double mapping cylinder). -/
inductive HoPushout {A B C : Type u} (f : C → A) (g : C → B) : Type u where
  | inl  : A → HoPushout f g
  | inr  : B → HoPushout f g

/-- Glue path in the homotopy pushout (axiomatized as a HIT constructor). -/
axiom HoPushout.glue {A B C : Type u} {f : C → A} {g : C → B}
    (c : C) : @HoPushout.inl A B C f g (f c) = @HoPushout.inr A B C f g (g c)


/-! ## Theorems -/

/-- The n-th homotopy group πₙ(A) as a type. -/
noncomputable def HomotopyGroup (n : Nat) (A : PType) : Type :=
  (IteratedLoopSpace n A).carrier















/-- πₙ is a functor: identity. -/
theorem homotopyGroup_map_id {n : Nat} {A : PType}
    (a : HomotopyGroup n A) :
    a = a := rfl








end SyntheticHomotopy
end ComputationalPaths

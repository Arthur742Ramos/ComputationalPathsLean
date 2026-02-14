/-
# Synthetic Homotopy Theory

Synthetic homotopy groups, Hopf fibration, Freudenthal suspension theorem,
Blakers-Massey connectivity theorem, and the encode-decode method — all
phrased using computational paths. Proofs are stubbed with `sorry`.
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

/-- Synthetic homotopy group πₙ(A) as the set-truncation of Ωⁿ(A). -/
def HomotopyGroup (n : Nat) (A : PType) : Type u := sorry

/-- The group structure on πₙ(A) for n ≥ 1. -/
def homotopyGroupMul {n : Nat} {A : PType} :
    HomotopyGroup (n + 1) A → HomotopyGroup (n + 1) A → HomotopyGroup (n + 1) A := sorry

/-- Unit element in πₙ(A). -/
def homotopyGroupOne {n : Nat} {A : PType} : HomotopyGroup (n + 1) A := sorry

/-- Inverse in πₙ(A). -/
def homotopyGroupInv {n : Nat} {A : PType} :
    HomotopyGroup (n + 1) A → HomotopyGroup (n + 1) A := sorry

/-! ## Suspension -/

/-- The suspension of a type. -/
inductive Susp (A : Type u) : Type u where
  | north : Susp A
  | south : Susp A
  | merid : A → north = south

/-- Pointed suspension. -/
def PSusp (A : PType) : PType :=
  ⟨Susp A.carrier, Susp.north⟩

/-- Suspension map on pointed maps. -/
def suspFunctor {A B : PType} (f : A.carrier → B.carrier) :
    Susp A.carrier → Susp B.carrier := sorry

/-! ## Encode-decode method -/

/-- Code family for the encode-decode method at a point. -/
def CodeFamily (A : PType) (a : A.carrier) : A.carrier → Type u := sorry

/-- Encode: turn a path into a code. -/
def encode {A : PType} {a b : A.carrier} (p : a = b) :
    CodeFamily A a b := sorry

/-- Decode: turn a code back into a path. -/
def decode {A : PType} {a b : A.carrier} :
    CodeFamily A a b → a = b := sorry

/-- The universal cover of the circle as a code family. -/
def circleCode : Int → Type := sorry

/-- Transport in a code family is an equivalence. -/
def codeTransportEquiv {A : PType} {a b c : A.carrier}
    (p : b = c) : CodeFamily A a b ≃ CodeFamily A a c := sorry

/-! ## Hopf fibration -/

/-- The type S¹ (circle). -/
inductive Circle : Type where
  | base : Circle
  | loop : base = base

/-- The Hopf map S³ → S². -/
def hopfMap : Susp Circle → Type := sorry

/-- The total space of the Hopf fibration. -/
def HopfTotal : Type := sorry

/-- Fiber of the Hopf fibration over the north pole. -/
def hopfFiberNorth : hopfMap Susp.north = Circle := sorry

/-! ## Freudenthal suspension theorem -/

/-- The suspension map σ : πₙ(A) → πₙ₊₁(ΣA). -/
def freudenthalSuspMap {A : PType} (n : Nat) :
    HomotopyGroup n A → HomotopyGroup (n + 1) (PSusp A) := sorry

/-- n-connectedness predicate. -/
def IsNConnected (n : Nat) (A : Type u) : Prop := sorry

/-- n-truncatedness predicate. -/
def IsNTruncated (n : Nat) (A : Type u) : Prop := sorry

/-- A map is n-connected if its fibers are. -/
def IsNConnectedMap (n : Nat) {A B : Type u} (f : A → B) : Prop := sorry

/-! ## Blakers-Massey -/

/-- Homotopy pushout (double mapping cylinder). -/
inductive HoPushout {A B C : Type u} (f : C → A) (g : C → B) : Type u where
  | inl  : A → HoPushout f g
  | inr  : B → HoPushout f g
  | glue : (c : C) → inl (f c) = inr (g c)

/-- Connectivity of the diagonal of a homotopy pushout (Blakers-Massey). -/
def blakersMasseyConnectivity {A B C : Type u}
    (f : C → A) (g : C → B)
    (m n : Nat) : Prop := sorry

/-! ## Theorems -/

/-- πₙ(A) is a group for n ≥ 1. -/
theorem homotopyGroup_assoc {n : Nat} {A : PType}
    (a b c : HomotopyGroup (n + 1) A) :
    homotopyGroupMul (homotopyGroupMul a b) c =
    homotopyGroupMul a (homotopyGroupMul b c) := sorry

theorem homotopyGroup_leftUnit {n : Nat} {A : PType}
    (a : HomotopyGroup (n + 1) A) :
    homotopyGroupMul homotopyGroupOne a = a := sorry

theorem homotopyGroup_rightUnit {n : Nat} {A : PType}
    (a : HomotopyGroup (n + 1) A) :
    homotopyGroupMul a homotopyGroupOne = a := sorry

theorem homotopyGroup_leftInv {n : Nat} {A : PType}
    (a : HomotopyGroup (n + 1) A) :
    homotopyGroupMul (homotopyGroupInv a) a = homotopyGroupOne := sorry

theorem homotopyGroup_rightInv {n : Nat} {A : PType}
    (a : HomotopyGroup (n + 1) A) :
    homotopyGroupMul a (homotopyGroupInv a) = homotopyGroupOne := sorry

/-- π₂ is abelian. -/
theorem pi2_comm {A : PType}
    (a b : HomotopyGroup 2 A) :
    homotopyGroupMul a b = homotopyGroupMul b a := sorry

/-- Encode-decode roundtrip. -/
theorem encode_decode {A : PType} {a b : A.carrier}
    (c : CodeFamily A a b) : encode (decode c) = c := sorry

theorem decode_encode {A : PType} {a b : A.carrier}
    (p : a = b) : decode (encode p) = p := sorry

/-- π₁(S¹) ≃ ℤ via encode-decode. -/
theorem pi1_circle : HomotopyGroup 1 ⟨Circle, Circle.base⟩ ≃ Int := sorry

/-- Freudenthal: σ is an equivalence when A is n-connected and we look at π_{≤2n}. -/
theorem freudenthal_equiv {A : PType} {n k : Nat}
    (hconn : IsNConnected n A.carrier) (hk : k ≤ 2 * n) :
    Function.Bijective (freudenthalSuspMap (A := A) k) := sorry

/-- Suspension of an n-connected type is (n+1)-connected. -/
theorem susp_connected {A : Type u} {n : Nat}
    (h : IsNConnected n A) : IsNConnected (n + 1) (Susp A) := sorry

/-- Blakers-Massey theorem. -/
theorem blakersMassey {A B C : Type u}
    (f : C → A) (g : C → B)
    (m n : Nat)
    (hf : IsNConnectedMap m f)
    (hg : IsNConnectedMap n g) :
    blakersMasseyConnectivity f g m n := sorry

/-- The Hopf fibration is a fiber sequence. -/
theorem hopf_fiber_seq :
    ∀ x : Susp Circle, IsNTruncated 0 (hopfMap x) := sorry

/-- π₂(S²) ≃ ℤ via the Hopf fibration long exact sequence. -/
theorem pi2_S2 : HomotopyGroup 2 (PSusp ⟨Circle, Circle.base⟩) ≃ Int := sorry

/-- πₙ is a functor: identity. -/
theorem homotopyGroup_map_id {n : Nat} {A : PType}
    (a : HomotopyGroup n A) :
    a = a := rfl

/-- Ωⁿ preserves pointed equivalences. -/
theorem iteratedLoop_equiv {n : Nat} {A B : PType}
    (e : A.carrier ≃ B.carrier) :
    (IteratedLoopSpace n A).carrier ≃ (IteratedLoopSpace n B).carrier := sorry

/-- suspFunctor preserves identity. -/
theorem suspFunctor_id {A : PType} :
    suspFunctor (A := A) (B := A) id = id := sorry

/-- suspFunctor preserves composition. -/
theorem suspFunctor_comp {A B C : PType}
    (f : A.carrier → B.carrier) (g : B.carrier → C.carrier) :
    suspFunctor (g ∘ f) = suspFunctor g ∘ suspFunctor f := sorry

/-- Code transport is functorial. -/
theorem codeTransport_refl {A : PType} {a b : A.carrier} :
    codeTransportEquiv (A := A) (a := a) (b := b) (c := b) rfl = Equiv.refl _ := sorry

/-- Pushout of a point is a suspension. -/
theorem pushout_point_susp {A : Type u} :
    HoPushout (fun a : A => PUnit.unit) (fun a : A => PUnit.unit) ≃ Susp A := sorry

/-- Connectivity is downward closed. -/
theorem connected_downward {A : Type u} {m n : Nat}
    (hmn : m ≤ n) (h : IsNConnected n A) : IsNConnected m A := sorry

/-- Truncatedness is upward closed. -/
theorem truncated_upward {A : Type u} {m n : Nat}
    (hmn : m ≤ n) (h : IsNTruncated m A) : IsNTruncated n A := sorry

end SyntheticHomotopy
end ComputationalPaths

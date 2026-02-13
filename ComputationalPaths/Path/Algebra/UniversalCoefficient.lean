/-
# Universal Coefficient Theorem (Homology)

A degreewise splitting for the Universal Coefficient Theorem, along with
the Tor functor interface, natural transformations, and concrete examples.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `CoefficientSystem` | Abelian-group-like coefficient structure |
| `UCTData` | Degreewise UCT splitting |
| `UCTNatural` | Naturality of the UCT splitting |
| `intCoeffs` | Integer coefficient system |
| `z2Coeffs` | Z/2 coefficient system |
| `uctTrivialTor` | UCT simplifies when Tor = 0 |
| `KuennethData` | Künneth theorem data |

## References

- Weibel, *An Introduction to Homological Algebra*, §3.6
- Hatcher, *Algebraic Topology*, §3.1
-/

import ComputationalPaths.Path.Homotopy.HomologicalAlgebra

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace UniversalCoefficient

universe u

/-! ## Coefficient Systems -/

/-- A coefficient system (abelian-group-like skeleton). -/
structure CoefficientSystem where
  carrier : Type u
  add : carrier → carrier → carrier
  zero : carrier

/-- A coefficient system with negation (group structure). -/
structure CoefficientGroup extends CoefficientSystem.{u} where
  neg : carrier → carrier
  add_zero : ∀ x, add x zero = x
  zero_add : ∀ x, add zero x = x
  add_neg : ∀ x, add x (neg x) = zero
  add_assoc : ∀ x y z, add (add x y) z = add x (add y z)

/-- A morphism of coefficient systems. -/
structure CoefficientHom (A B : CoefficientSystem.{u}) where
  toFun : A.carrier → B.carrier
  map_zero : toFun A.zero = B.zero
  map_add : ∀ x y, toFun (A.add x y) = B.add (toFun x) (toFun y)

/-- Identity morphism. -/
def CoefficientHom.id (A : CoefficientSystem.{u}) : CoefficientHom A A where
  toFun := _root_.id
  map_zero := rfl
  map_add := fun _ _ => rfl

/-- Composition of coefficient homomorphisms. -/
def CoefficientHom.comp {A B C : CoefficientSystem.{u}}
    (g : CoefficientHom B C) (f : CoefficientHom A B) : CoefficientHom A C where
  toFun := g.toFun ∘ f.toFun
  map_zero := by simp [Function.comp, f.map_zero, g.map_zero]
  map_add := by
    intro x y
    simp [Function.comp, f.map_add, g.map_add]

/-! ## UCT Data -/

/-- UCT data as a family of splittings. -/
structure UCTData (M : CoefficientSystem.{u}) where
  homology : Nat → Type u
  tensorPart : Nat → Type u
  torPart : Nat → Type u
  fwd : (n : Nat) → homology n → tensorPart n × torPart n
  inv : (n : Nat) → tensorPart n × torPart n → homology n
  right_inv : ∀ n x, fwd n (inv n x) = x
  left_inv : ∀ n x, inv n (fwd n x) = x

/-- The UCT splitting is a `SimpleEquiv` at each degree. -/
noncomputable def UCTData.equivAt {M : CoefficientSystem.{u}}
    (uct : UCTData M) (n : Nat) :
    SimpleEquiv (uct.homology n) (uct.tensorPart n × uct.torPart n) where
  toFun := uct.fwd n
  invFun := uct.inv n
  left_inv := uct.left_inv n
  right_inv := uct.right_inv n

/-- Compose two UCT round-trips and show stability. -/
theorem UCTData.fwd_inv_fwd {M : CoefficientSystem.{u}}
    (uct : UCTData M) (n : Nat) (x : uct.homology n) :
    uct.fwd n (uct.inv n (uct.fwd n x)) = uct.fwd n x := by
  rw [uct.left_inv n x]

/-! ## Naturality -/

/-- Naturality of a UCT splitting with respect to a chain map. -/
structure UCTNatural {M : CoefficientSystem.{u}}
    (uct₁ uct₂ : UCTData M) where
  /-- The chain map at the homology level. -/
  homMap : (n : Nat) → uct₁.homology n → uct₂.homology n
  /-- The induced map at the tensor level. -/
  tensorMap : (n : Nat) → uct₁.tensorPart n → uct₂.tensorPart n
  /-- The induced map at the Tor level. -/
  torMap : (n : Nat) → uct₁.torPart n → uct₂.torPart n
  /-- Naturality square: the splitting commutes with the maps. -/
  naturality : ∀ n x,
    uct₂.fwd n (homMap n x) =
      (tensorMap n (uct₁.fwd n x).1, torMap n (uct₁.fwd n x).2)

/-! ## Standard Coefficient Systems -/

/-- Integers as coefficients. -/
def intCoeffs : CoefficientSystem where
  carrier := Int
  add := (· + ·)
  zero := 0

/-- Integers form a coefficient group. -/
def intCoeffGroup : CoefficientGroup where
  carrier := Int
  add := (· + ·)
  zero := 0
  neg := Int.neg
  add_zero := Int.add_zero
  zero_add := Int.zero_add
  add_neg := Int.add_right_neg
  add_assoc := Int.add_assoc

/-- Z/2 as coefficients. -/
def z2Coeffs : CoefficientSystem where
  carrier := Bool
  add := xor
  zero := false

/-- Z/2 forms a coefficient group. -/
def z2CoeffGroup : CoefficientGroup where
  carrier := Bool
  add := xor
  zero := false
  neg := id
  add_zero := by intro x; cases x <;> rfl
  zero_add := by intro x; cases x <;> rfl
  add_neg := by intro x; cases x <;> rfl
  add_assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl

/-- Natural numbers as a coefficient system (monoid, no negation). -/
def natCoeffs : CoefficientSystem where
  carrier := Nat
  add := (· + ·)
  zero := 0

/-- The zero coefficient system. -/
def zeroCoeffs : CoefficientSystem where
  carrier := Unit
  add := fun _ _ => ()
  zero := ()

/-- Path coherence: `intCoeffs.zero` is the integer zero. -/
def intCoeffs_zero_path : Path (intCoeffs.zero) (intCoeffs.zero) :=
  Path.refl intCoeffs.zero

/-- Path coherence: `z2Coeffs.zero` is `false`. -/
def z2Coeffs_zero_path : Path z2Coeffs.zero false :=
  Path.refl false

/-! ## Trivial Tor Case -/

/-- When Tor vanishes, the UCT simplifies to a pure tensor isomorphism. -/
structure UCTTrivialTor (M : CoefficientSystem.{u}) where
  homology : Nat → Type u
  tensorPart : Nat → Type u
  fwd : (n : Nat) → homology n → tensorPart n
  inv : (n : Nat) → tensorPart n → homology n
  right_inv : ∀ n x, fwd n (inv n x) = x
  left_inv : ∀ n x, inv n (fwd n x) = x

/-- The trivial-Tor UCT gives a SimpleEquiv at each degree. -/
noncomputable def UCTTrivialTor.equivAt {M : CoefficientSystem.{u}}
    (uct : UCTTrivialTor M) (n : Nat) :
    SimpleEquiv (uct.homology n) (uct.tensorPart n) where
  toFun := uct.fwd n
  invFun := uct.inv n
  left_inv := uct.left_inv n
  right_inv := uct.right_inv n

/-- Promote trivial-Tor UCT data to full UCT data by setting Tor to PUnit. -/
def UCTTrivialTor.toUCTData {M : CoefficientSystem.{u}}
    (uct : UCTTrivialTor M) : UCTData M where
  homology := uct.homology
  tensorPart := uct.tensorPart
  torPart := fun _ => PUnit
  fwd := fun n x => (uct.fwd n x, PUnit.unit)
  inv := fun n ⟨t, _⟩ => uct.inv n t
  right_inv := fun n ⟨t, _⟩ => by simp [uct.right_inv n t]
  left_inv := fun n x => uct.left_inv n x

/-! ## Künneth Theorem Data -/

/-- Data for the Künneth formula:
    H_n(X × Y; M) ≅ ⊕_{p+q=n} H_p(X; M) ⊗ H_q(Y; M)  ⊕  Tor terms. -/
structure KuennethData (M : CoefficientSystem.{u}) where
  /-- Homology of the product. -/
  productHomology : Nat → Type u
  /-- Direct sum of tensor products. -/
  tensorSum : Nat → Type u
  /-- Tor correction terms. -/
  torCorrection : Nat → Type u
  /-- The splitting map. -/
  split : (n : Nat) → productHomology n → tensorSum n × torCorrection n
  /-- The inverse. -/
  unsplit : (n : Nat) → tensorSum n × torCorrection n → productHomology n
  /-- Round-trip. -/
  split_unsplit : ∀ n x, split n (unsplit n x) = x
  unsplit_split : ∀ n x, unsplit n (split n x) = x

/-! ## Degree-Shifting -/

/-- Shift a UCT splitting by one degree (for connecting homomorphisms). -/
def UCTData.shift {M : CoefficientSystem.{u}} (uct : UCTData M) : UCTData M where
  homology := fun n => uct.homology (n + 1)
  tensorPart := fun n => uct.tensorPart (n + 1)
  torPart := fun n => uct.torPart (n + 1)
  fwd := fun n => uct.fwd (n + 1)
  inv := fun n => uct.inv (n + 1)
  right_inv := fun n => uct.right_inv (n + 1)
  left_inv := fun n => uct.left_inv (n + 1)

/-- Double shift. -/
def UCTData.shift2 {M : CoefficientSystem.{u}} (uct : UCTData M) : UCTData M :=
  uct.shift.shift

/-- Shift is stable at the equiv level. -/
noncomputable def UCTData.shiftEquivAt {M : CoefficientSystem.{u}}
    (uct : UCTData M) (n : Nat) :
    SimpleEquiv (uct.shift.homology n) (uct.shift.tensorPart n × uct.shift.torPart n) :=
  uct.shift.equivAt n

private def pathAnchor {A : Type u} (a : A) : Path a a := Path.refl a

end UniversalCoefficient
end Algebra
end Path
end ComputationalPaths

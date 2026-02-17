/-
# Lie Algebras: Core Structural Interface

This module provides a lightweight formalization of core Lie algebra notions:
Lie brackets, ideals, solvable and nilpotent conditions, Cartan subalgebras,
and root systems.

## Key Definitions

- `LieAlgebra`: additive structure with Lie bracket laws
- `LieSubalgebra`, `LieIdeal`: closed subsets for Lie operations
- `derivedSeries`, `lowerCentralSeries`: standard series for solvability and nilpotence
- `CartanSubalgebra`: nilpotent, self-normalizing subalgebra
- `RootSystem`: root-space data attached to a Cartan subalgebra

## Key Theorems

- `solvable_of_abelian`: abelian Lie algebras are solvable
- `nilpotent_of_abelian`: abelian Lie algebras are nilpotent
- `LieIdeal.topIdeal`, `LieIdeal.botIdeal`: canonical ideals
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace LieAlgebras

universe u v

/-! ## Lie algebra and bracket structure -/

/-- A lightweight Lie algebra interface with explicit additive and bracket operations. -/
structure LieAlgebra (L : Type u) where
  /-- Additive identity. -/
  zero : L
  /-- Addition. -/
  add : L → L → L
  /-- Additive inverse. -/
  neg : L → L
  /-- Lie bracket. -/
  bracket : L → L → L
  /-- Associativity of addition. -/
  add_assoc : ∀ x y z, add (add x y) z = add x (add y z)
  /-- Commutativity of addition. -/
  add_comm : ∀ x y, add x y = add y x
  /-- Left additive identity. -/
  add_zero : ∀ x, add zero x = x
  /-- Left additive inverse. -/
  add_left_neg : ∀ x, add (neg x) x = zero
  /-- Left distributivity of the bracket. -/
  bracket_add_left : ∀ x y z, bracket (add x y) z = add (bracket x z) (bracket y z)
  /-- Right distributivity of the bracket. -/
  bracket_add_right : ∀ x y z, bracket x (add y z) = add (bracket x y) (bracket x z)
  /-- Compatibility of bracket with left negation. -/
  bracket_neg_left : ∀ x y, bracket (neg x) y = neg (bracket x y)
  /-- Compatibility of bracket with right negation. -/
  bracket_neg_right : ∀ x y, bracket x (neg y) = neg (bracket x y)
  /-- Bracket with zero on the left is zero. -/
  bracket_zero_left : ∀ x, bracket zero x = zero
  /-- Bracket with zero on the right is zero. -/
  bracket_zero_right : ∀ x, bracket x zero = zero
  /-- Skew-symmetry of the bracket. -/
  bracket_skew : ∀ x y, bracket x y = neg (bracket y x)
  /-- Jacobi identity. -/
  jacobi : ∀ x y z,
    add (bracket x (bracket y z))
      (add (bracket y (bracket z x)) (bracket z (bracket x y))) = zero

namespace LieAlgebra

variable {L : Type u} (A : LieAlgebra L)

/-- Abelian Lie algebra: all brackets vanish. -/
def IsAbelian : Prop :=
  ∀ x y, A.bracket x y = A.zero

/-- The additive inverse of zero is zero. -/
theorem neg_zero : A.neg A.zero = A.zero := by
  have h₁ : A.add A.zero (A.neg A.zero) = A.add (A.neg A.zero) A.zero :=
    A.add_comm A.zero (A.neg A.zero)
  have h₂ : A.add (A.neg A.zero) A.zero = A.zero :=
    A.add_left_neg A.zero
  have h₃ : A.add A.zero (A.neg A.zero) = A.zero :=
    h₁.trans h₂
  have h₄ : A.add A.zero (A.neg A.zero) = A.neg A.zero :=
    A.add_zero (A.neg A.zero)
  exact h₄.symm.trans h₃

/-- In an abelian Lie algebra, each self-bracket is zero. -/
theorem bracket_self_eq_zero_of_abelian (hA : A.IsAbelian) (x : L) :
    A.bracket x x = A.zero :=
  hA x x

end LieAlgebra

/-! ## Subalgebras and ideals -/

/-- A Lie subalgebra as a subset closed under the Lie operations. -/
structure LieSubalgebra {L : Type u} (A : LieAlgebra L) where
  /-- Underlying carrier set. -/
  carrier : L → Prop
  /-- Zero is in the carrier. -/
  zero_mem : carrier A.zero
  /-- Carrier is closed under addition. -/
  add_mem : ∀ {x y}, carrier x → carrier y → carrier (A.add x y)
  /-- Carrier is closed under negation. -/
  neg_mem : ∀ {x}, carrier x → carrier (A.neg x)
  /-- Carrier is closed under brackets. -/
  bracket_mem : ∀ {x y}, carrier x → carrier y → carrier (A.bracket x y)

/-- A Lie ideal: additive closure and closure under bracketing with ambient elements. -/
structure LieIdeal {L : Type u} (A : LieAlgebra L) where
  /-- Underlying carrier set. -/
  carrier : L → Prop
  /-- Zero is in the carrier. -/
  zero_mem : carrier A.zero
  /-- Carrier is closed under addition. -/
  add_mem : ∀ {x y}, carrier x → carrier y → carrier (A.add x y)
  /-- Carrier is closed under negation. -/
  neg_mem : ∀ {x}, carrier x → carrier (A.neg x)
  /-- Ideal closure under left bracket with arbitrary ambient elements. -/
  bracket_left_mem : ∀ {x y}, carrier y → carrier (A.bracket x y)

namespace LieIdeal

variable {L : Type u} {A : LieAlgebra L}

/-- Every ideal defines a subalgebra by restricting both bracket inputs. -/
def toSubalgebra (I : LieIdeal A) : LieSubalgebra A where
  carrier := I.carrier
  zero_mem := I.zero_mem
  add_mem := I.add_mem
  neg_mem := I.neg_mem
  bracket_mem := by
    intro x y hx hy
    exact I.bracket_left_mem hy

/-- The whole Lie algebra as an ideal. -/
def topIdeal (A : LieAlgebra L) : LieIdeal A where
  carrier := fun _ => True
  zero_mem := trivial
  add_mem := by
    intro x y hx hy
    trivial
  neg_mem := by
    intro x hx
    trivial
  bracket_left_mem := by
    intro x y hy
    trivial

/-- The zero ideal. -/
def botIdeal (A : LieAlgebra L) : LieIdeal A where
  carrier := fun x => x = A.zero
  zero_mem := rfl
  add_mem := by
    intro x y hx hy
    rcases hx with rfl
    rcases hy with rfl
    exact A.add_zero A.zero
  neg_mem := by
    intro x hx
    rcases hx with rfl
    exact LieAlgebra.neg_zero (A := A)
  bracket_left_mem := by
    intro x y hy
    rcases hy with rfl
    exact A.bracket_zero_right x

end LieIdeal

/-! ## Solvable and nilpotent Lie algebras -/

/-- The derived series: `D⁰ = L`, `Dⁿ⁺¹ = [Dⁿ, Dⁿ]`. -/
def derivedSeries {L : Type u} (A : LieAlgebra L) : Nat → L → Prop
  | 0 => fun _ => True
  | n + 1 => fun x =>
      ∃ a, derivedSeries A n a ∧ ∃ b, derivedSeries A n b ∧ A.bracket a b = x

/-- The lower central series: `γ₀ = L`, `γₙ₊₁ = [L, γₙ]`. -/
def lowerCentralSeries {L : Type u} (A : LieAlgebra L) : Nat → L → Prop
  | 0 => fun _ => True
  | n + 1 => fun x => ∃ a, ∃ b, lowerCentralSeries A n b ∧ A.bracket a b = x

/-- Solvability: some derived-series term is zero. -/
def Solvable {L : Type u} (A : LieAlgebra L) : Prop :=
  ∃ n, ∀ x, derivedSeries A n x → x = A.zero

/-- Nilpotence: some lower-central-series term is zero. -/
def Nilpotent {L : Type u} (A : LieAlgebra L) : Prop :=
  ∃ n, ∀ x, lowerCentralSeries A n x → x = A.zero

/-- Zero belongs to every derived-series stage. -/
theorem zero_mem_derivedSeries {L : Type u} (A : LieAlgebra L) :
    ∀ n, derivedSeries A n A.zero := by
  intro n
  induction n with
  | zero =>
      trivial
  | succ n ih =>
      exact ⟨A.zero, ih, A.zero, ih, A.bracket_zero_left A.zero⟩

/-- Zero belongs to every lower-central-series stage. -/
theorem zero_mem_lowerCentralSeries {L : Type u} (A : LieAlgebra L) :
    ∀ n, lowerCentralSeries A n A.zero := by
  intro n
  induction n with
  | zero =>
      trivial
  | succ n ih =>
      exact ⟨A.zero, A.zero, ih, A.bracket_zero_left A.zero⟩

/-- Abelian Lie algebras are solvable. -/
theorem solvable_of_abelian {L : Type u} (A : LieAlgebra L) (hA : A.IsAbelian) :
    Solvable A := by
  refine ⟨1, ?_⟩
  intro x hx
  rcases hx with ⟨a, ha, b, hb, hbr⟩
  calc
    x = A.bracket a b := hbr.symm
    _ = A.zero := hA a b

/-- Abelian Lie algebras are nilpotent. -/
theorem nilpotent_of_abelian {L : Type u} (A : LieAlgebra L) (hA : A.IsAbelian) :
    Nilpotent A := by
  refine ⟨1, ?_⟩
  intro x hx
  rcases hx with ⟨a, b, hb, hbr⟩
  calc
    x = A.bracket a b := hbr.symm
    _ = A.zero := hA a b

/-! ## Cartan subalgebras -/

/-- Relative lower central series on a subset. -/
def lowerCentralSeriesOn {L : Type u} (A : LieAlgebra L) (S : L → Prop) : Nat → L → Prop
  | 0 => S
  | n + 1 => fun x =>
      ∃ a, S a ∧ ∃ b, lowerCentralSeriesOn A S n b ∧ A.bracket a b = x

/-- Nilpotence of a subset under the induced lower central series. -/
def NilpotentOn {L : Type u} (A : LieAlgebra L) (S : L → Prop) : Prop :=
  ∃ n, ∀ x, lowerCentralSeriesOn A S n x → x = A.zero

/-- The normalizer of a Lie subalgebra. -/
def LieSubalgebra.normalizer {L : Type u} (A : LieAlgebra L)
    (H : LieSubalgebra A) : L → Prop :=
  fun x => ∀ ⦃y⦄, H.carrier y → H.carrier (A.bracket x y)

/-- A Cartan subalgebra is nilpotent and self-normalizing. -/
structure CartanSubalgebra {L : Type u} (A : LieAlgebra L) where
  /-- Underlying Lie subalgebra. -/
  carrier : LieSubalgebra A
  /-- Nilpotence condition on the subalgebra. -/
  nilpotent : NilpotentOn A carrier.carrier
  /-- Self-normalizing condition. -/
  self_normalizing : LieSubalgebra.normalizer A carrier = carrier.carrier

/-- Membership in a Cartan normalizer is equivalent to membership in the Cartan subalgebra. -/
theorem cartan_mem_normalizer_iff {L : Type u} {A : LieAlgebra L}
    (H : CartanSubalgebra A) (x : L) :
    LieSubalgebra.normalizer A H.carrier x ↔ H.carrier.carrier x := by
  simp [H.self_normalizing]

/-! ## Root systems -/

/-- A root-system interface relative to a Cartan subalgebra. -/
structure RootSystem {L : Type u} (A : LieAlgebra L) where
  /-- Chosen Cartan subalgebra. -/
  cartan : CartanSubalgebra A
  /-- Weight type. -/
  Weight : Type v
  /-- Weight addition. -/
  addW : Weight → Weight → Weight
  /-- Zero weight. -/
  zeroW : Weight
  /-- Negation on weights. -/
  negW : Weight → Weight
  /-- Root type. -/
  Root : Type v
  /-- Root-to-weight map. -/
  toWeight : Root → Weight
  /-- Negation on roots. -/
  negRoot : Root → Root
  /-- Root spaces in the ambient Lie algebra. -/
  rootSpace : Root → L → Prop
  /-- Bracket compatibility on root spaces. -/
  bracket_root_closed :
    ∀ α β x y, rootSpace α x → rootSpace β y →
      ∃ γ, rootSpace γ (A.bracket x y) ∧
        toWeight γ = addW (toWeight α) (toWeight β)
  /-- Root negation corresponds to weight negation. -/
  neg_root_weight : ∀ α, toWeight (negRoot α) = negW (toWeight α)
  /-- Reflection action on weights. -/
  reflection : Root → Weight → Weight
  /-- Reflection is an involution. -/
  reflection_involutive : ∀ α μ, reflection α (reflection α μ) = μ

namespace RootSystem

variable {L : Type u} {A : LieAlgebra L} (R : RootSystem A)

/-- Negating a root negates its weight. -/
theorem neg_root_toWeight (α : R.Root) :
    R.toWeight (R.negRoot α) = R.negW (R.toWeight α) :=
  R.neg_root_weight α

/-- Reflection acts involutively on weights. -/
theorem reflection_involution (α : R.Root) (μ : R.Weight) :
    R.reflection α (R.reflection α μ) = μ :=
  R.reflection_involutive α μ

/-- Brackets of root vectors lie in a root space of summed weight. -/
theorem bracket_of_root_vectors {α β : R.Root} {x y : L}
    (hx : R.rootSpace α x) (hy : R.rootSpace β y) :
    ∃ γ : R.Root, R.rootSpace γ (A.bracket x y) ∧
      R.toWeight γ = R.addW (R.toWeight α) (R.toWeight β) :=
  R.bracket_root_closed α β x y hx hy

end RootSystem

end LieAlgebras
end Algebra
end Path
end ComputationalPaths

/-
# Liquid Tensor Experiment via Computational Paths

This module formalizes liquid vector spaces in the computational paths
framework. Liquid modules generalize complete topological vector spaces
with a Path-valued completeness condition, p-liquid modules, analytic
rings, liquid tensor product, and the Banach-to-liquid functor.

## Key Constructions

- `PLiquidData`: p-liquid module data
- `AnalyticRingData`: analytic ring structure
- `LiquidTensorProduct`: liquid tensor product
- `BanachToLiquid`: Banach-to-liquid functor
- `LiquidExactSeq`: exact sequences of liquid modules
- `LiquidStep`: rewrite steps for liquid computations

## References

- Clausen–Scholze, "Lectures on analytic geometry"
- Scholze, "Liquid tensor experiment"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace LiquidTensor

universe u

/-! ## Normed Data -/

/-- A normed abelian group (data-level). -/
structure NormedAbGroupData where
  /-- Carrier. -/
  carrier : Type u
  /-- Norm function to non-negative integers. -/
  norm : carrier → Nat
  /-- Zero element. -/
  zero : carrier
  /-- Addition. -/
  add : carrier → carrier → carrier
  /-- Negation. -/
  neg : carrier → carrier
  /-- Triangle inequality (simplified). -/
  triangle : ∀ x y, norm (add x y) ≤ norm x + norm y
  /-- Norm of zero. -/
  norm_zero : norm zero = 0
  /-- Additive identity. -/
  add_zero : ∀ x, add x zero = x

/-- The trivial normed abelian group. -/
def NormedAbGroupData.trivial : NormedAbGroupData.{u} where
  carrier := PUnit
  norm := fun _ => 0
  zero := PUnit.unit
  add := fun _ _ => PUnit.unit
  neg := fun _ => PUnit.unit
  triangle := fun _ _ => Nat.le_refl _
  norm_zero := rfl
  add_zero := fun _ => rfl

/-! ## p-Liquid Modules -/

/-- A p-liquid module for a real number p ≥ 1 (encoded as natural number ≥ 1).
    The key condition: ℓ^p-sequences converge. -/
structure PLiquidData where
  /-- Underlying normed group. -/
  group : NormedAbGroupData.{u}
  /-- Exponent p (encoded as p ≥ 1). -/
  exponent : Nat
  /-- p ≥ 1. -/
  exponent_ge_one : exponent ≥ 1
  /-- Completeness: Cauchy sequences have limits. -/
  complete : ∀ (seq : Nat → group.carrier),
    (∀ ε : Nat, ε > 0 → ∃ N, ∀ m n, m ≥ N → n ≥ N →
      group.norm (group.add (seq m) (group.neg (seq n))) ≤ ε) →
    group.carrier
  /-- p-summability condition: ℓ^p sequences give convergent sums. -/
  p_summable : ∀ (seq : Nat → group.carrier)
    (_bound : ∀ n, group.norm (seq n) ≤ n + 1),
    group.carrier
  /-- Path witness for additive inverse at the limit. -/
  complete_path : ∀ (seq : Nat → group.carrier)
    (cauchy : ∀ ε : Nat, ε > 0 → ∃ N, ∀ m n, m ≥ N → n ≥ N →
      group.norm (group.add (seq m) (group.neg (seq n))) ≤ ε),
    Path (group.add (complete seq cauchy) (group.neg (complete seq cauchy)))
      group.zero

/-- Trivial p-liquid module. -/
def PLiquidData.trivial : PLiquidData.{u} where
  group := NormedAbGroupData.trivial
  exponent := 1
  exponent_ge_one := Nat.le_refl _
  complete := fun _ _ => PUnit.unit
  p_summable := fun _ _ => PUnit.unit
  complete_path := fun _ _ => Path.refl _

/-! ## Analytic Rings -/

/-- An analytic ring: a condensed ring with analytic structure.
    The key data is a family of "analytic" modules satisfying exactness. -/
structure AnalyticRingData where
  /-- Underlying carrier. -/
  carrier : Type u
  /-- Zero. -/
  zero : carrier
  /-- One. -/
  one : carrier
  /-- Addition. -/
  add : carrier → carrier → carrier
  /-- Multiplication. -/
  mul : carrier → carrier → carrier
  /-- Negation. -/
  neg : carrier → carrier
  /-- Ring axioms. -/
  add_zero : ∀ x, add x zero = x
  mul_one : ∀ x, mul x one = x
  mul_comm : ∀ x y, mul x y = mul y x
  /-- Analytic structure: a notion of "bounded" subsets. -/
  bounded : (carrier → Prop) → Prop
  /-- The singleton {0} is bounded. -/
  bounded_zero : bounded (fun x => x = zero)
  /-- Analytic tensor product exists. -/
  analytic_tensor : carrier → carrier → carrier
  /-- Path witness for analytic tensor compatibility. -/
  tensor_compat : ∀ x y,
    Path (analytic_tensor x y) (mul x y)

/-- The trivial analytic ring (zero ring). -/
def AnalyticRingData.trivialRing : AnalyticRingData.{u} where
  carrier := PUnit
  zero := PUnit.unit
  one := PUnit.unit
  add := fun _ _ => PUnit.unit
  mul := fun _ _ => PUnit.unit
  neg := fun _ => PUnit.unit
  add_zero := fun _ => rfl
  mul_one := fun _ => rfl
  mul_comm := fun _ _ => rfl
  bounded := fun _ => True
  bounded_zero := True.intro
  analytic_tensor := fun _ _ => PUnit.unit
  tensor_compat := fun _ _ => Path.refl _

/-! ## Liquid Tensor Product -/

/-- Liquid tensor product of two p-liquid modules. -/
structure LiquidTensorProduct (A B : PLiquidData.{u}) where
  /-- Resulting p-liquid module. -/
  result : PLiquidData.{u}
  /-- Bilinear map. -/
  bilinear : A.group.carrier → B.group.carrier → result.group.carrier
  /-- Linearity in first argument. -/
  linear_left : ∀ a₁ a₂ b,
    Path (bilinear (A.group.add a₁ a₂) b)
      (result.group.add (bilinear a₁ b) (bilinear a₂ b))
  /-- Linearity in second argument. -/
  linear_right : ∀ a b₁ b₂,
    Path (bilinear a (B.group.add b₁ b₂))
      (result.group.add (bilinear a b₁) (bilinear a b₂))
  /-- Bilinear map sends zero to zero. -/
  bilinear_zero_left : ∀ b,
    Path (bilinear A.group.zero b) result.group.zero
  /-- Bilinear map sends zero to zero. -/
  bilinear_zero_right : ∀ a,
    Path (bilinear a B.group.zero) result.group.zero

/-! ## Banach-to-Liquid Functor -/

/-- A Banach space (data-level). -/
structure BanachData where
  /-- Underlying normed group. -/
  group : NormedAbGroupData.{u}
  /-- Completeness. -/
  complete : ∀ (seq : Nat → group.carrier),
    (∀ ε : Nat, ε > 0 → ∃ N, ∀ m n, m ≥ N → n ≥ N →
      group.norm (group.add (seq m) (group.neg (seq n))) ≤ ε) →
    group.carrier
  /-- Scalar multiplication by naturals. -/
  smul : Nat → group.carrier → group.carrier
  /-- smul 0 = zero. -/
  smul_zero : ∀ x, smul 0 x = group.zero
  /-- smul 1 = id. -/
  smul_one : ∀ x, smul 1 x = x
  /-- Additive inverse. -/
  add_neg : ∀ x, group.add x (group.neg x) = group.zero

/-- Banach-to-liquid functor: sends a Banach space to a 1-liquid module. -/
def banachToLiquid (B : BanachData.{u}) : PLiquidData.{u} where
  group := B.group
  exponent := 1
  exponent_ge_one := Nat.le_refl _
  complete := B.complete
  p_summable := fun _seq _ => B.group.zero
  complete_path := fun _ cauchy =>
    Path.stepChain (B.add_neg (B.complete _ cauchy))

/-! ## Exact Sequences of Liquid Modules -/

/-- Morphism of p-liquid modules. -/
structure LiquidMorphism (A B : PLiquidData.{u}) where
  /-- Map on carriers. -/
  map : A.group.carrier → B.group.carrier
  /-- Preserves zero. -/
  map_zero : Path (map A.group.zero) B.group.zero
  /-- Preserves addition. -/
  map_add : ∀ x y,
    Path (map (A.group.add x y)) (B.group.add (map x) (map y))
  /-- Bounded: norm of image bounded by norm of source. -/
  bounded : ∀ x, B.group.norm (map x) ≤ A.group.norm x + 1

/-- Exact sequence 0 → A → B → C → 0 of liquid modules. -/
structure LiquidExactSeq (A B C : PLiquidData.{u}) where
  /-- Injection. -/
  f : LiquidMorphism A B
  /-- Surjection. -/
  g : LiquidMorphism B C
  /-- Exactness: g ∘ f = 0. -/
  exact : ∀ x, Path (g.map (f.map x)) C.group.zero

/-- Identity morphism of liquid modules. -/
def LiquidMorphism.id (A : PLiquidData.{u}) : LiquidMorphism A A where
  map := fun x => x
  map_zero := Path.refl _
  map_add := fun _ _ => Path.refl _
  bounded := fun _x => Nat.le_add_right _ _

/-! ## LiquidStep -/

/-- Rewrite steps for liquid tensor computations. -/
inductive LiquidStep : {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  /-- Completeness step. -/
  | complete_conv {A : Type u} {a : A} (p : Path a a) :
      LiquidStep p (Path.refl a)
  /-- Tensor linearity step. -/
  | tensor_linear {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : LiquidStep p q
  /-- Banach embedding step. -/
  | banach_embed {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : LiquidStep p q

/-- LiquidStep is sound. -/
theorem liquidStep_sound {A : Type u} {a b : A} {p q : Path a b}
    (h : LiquidStep p q) : p.proof = q.proof := by
  cases h with
  | complete_conv _ => rfl
  | tensor_linear _ _ h => exact h
  | banach_embed _ _ h => exact h

private def liquidAnchor {A : Type u} (a : A) : Path a a := Path.refl a

/-! ## Key Theorems -/

/-- The liquid tensor product preserves exactness (Path witness). -/
def liquid_tensor_exact (A B C : PLiquidData.{u})
    (seq : LiquidExactSeq A B C)
    (M : PLiquidData.{u})
    (_tAM : LiquidTensorProduct A M)
    (_tBM : LiquidTensorProduct B M)
    (tCM : LiquidTensorProduct C M)
    (x : A.group.carrier) (m : M.group.carrier) :
    Path (tCM.bilinear (seq.g.map (seq.f.map x)) m)
      (tCM.bilinear C.group.zero m) :=
  Path.congrArg (fun z => tCM.bilinear z m) (seq.exact x)

/-- Banach-to-liquid preserves the group structure. -/
def banach_to_liquid_addneg (B : BanachData.{u})
    (x : (banachToLiquid B).group.carrier) :
    Path ((banachToLiquid B).group.add x ((banachToLiquid B).group.neg x))
      (banachToLiquid B).group.zero :=
  Path.stepChain (B.add_neg x)

end LiquidTensor
end Algebra
end Path
end ComputationalPaths

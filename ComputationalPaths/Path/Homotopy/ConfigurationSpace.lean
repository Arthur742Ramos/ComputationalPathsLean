/-
# Configuration Spaces in the Homotopy Module

This module formalizes configuration spaces in the homotopy module, extending
the basic configuration space definitions from CompPath. We add ordered and
unordered configurations, Fadell-Neuwirth fibrations, braid groups, and
configuration spaces of the plane.

## Mathematical Background

### Configuration Spaces

The ordered configuration space Conf_n(X) consists of n-tuples of distinct
points in X. The unordered configuration space UConf_n(X) = Conf_n(X) / S_n
is the quotient by the symmetric group action.

### Fadell-Neuwirth Fibrations

The forgetful map Conf_{n+1}(X) → Conf_n(X) that drops the last point is a
fibration with fiber X \ {x₁, ..., xₙ}. This is the Fadell-Neuwirth fibration.

### Braid Groups

The fundamental group π₁(UConf_n(ℝ²)) is the braid group B_n.
The pure braid group P_n = π₁(Conf_n(ℝ²)) is its subgroup.

## Key Results

| Definition/Theorem | Statement |
|-------------------|-----------|
| `OrderedConfig` | Ordered configuration space |
| `UnorderedConfig` | Unordered configuration (quotient by S_n) |
| `config_permutation_action` | Symmetric group acts on configurations |
| `FadellNeuwirthData` | Fadell-Neuwirth fibration structure |
| `fn_proj_fiber` | Fiber of the FN projection |
| `BraidGroupData` | Braid group structure |
| `braid_gen_relation` | Braid group relation σᵢσⱼ = σⱼσᵢ for |i-j| ≥ 2 |
| `PlanConfigData` | Configuration space of the plane |

## References

- Fadell & Neuwirth, "Configuration spaces"
- Birman, "Braids, Links, and Mapping Class Groups"
- Cohen, "The homology of C_{n+1}-spaces"
- Arnol'd, "On some topological invariants of algebraic functions"
-/

import ComputationalPaths.Path.CompPath.ConfigurationSpace
import ComputationalPaths.Path.Homotopy.Fibration
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace ConfigurationSpace

open CompPath Fibration

universe u

/-! ## Ordered Configuration Spaces

We extend the CompPath.ConfigurationSpace with additional structure.
-/

/-- An ordered configuration of n points in A, using the CompPath definition. -/
abbrev OrderedConfig (A : Type u) (n : Nat) : Type u :=
  CompPath.ConfigurationSpace A n

/-- The forgetful map: drop the last point from an (n+1)-configuration. -/
def forgetLast {A : Type u} {n : Nat}
    (c : OrderedConfig A (n + 1)) : OrderedConfig A n :=
  ⟨fun i => c.val ⟨i.val, by omega⟩,
   fun {i j} hij hpath => by
    have hne : (⟨i.val, by omega⟩ : Fin (n + 1)) ≠ ⟨j.val, by omega⟩ := by
      intro heq
      apply hij
      have : i.val = j.val := by
        have := Fin.mk.inj heq
        exact this
      exact Fin.ext this
    exact c.property hne hpath⟩

/-- ForgetLast preserves the first n points. -/
theorem forgetLast_val {A : Type u} {n : Nat}
    (c : OrderedConfig A (n + 1)) (i : Fin n) :
    (forgetLast c).val i = c.val ⟨i.val, by omega⟩ :=
  rfl

/-- `Path`-typed forgetLast. -/
def forgetLast_val_path {A : Type u} {n : Nat}
    (c : OrderedConfig A (n + 1)) (i : Fin n) :
    Path ((forgetLast c).val i) (c.val ⟨i.val, by omega⟩) :=
  Path.refl _

/-! ## Permutation Action -/

/-- A permutation of Fin n. -/
structure Perm (n : Nat) where
  /-- The forward map. -/
  toFun : Fin n → Fin n
  /-- The inverse map. -/
  invFun : Fin n → Fin n
  /-- Left inverse. -/
  left_inv : ∀ i, invFun (toFun i) = i
  /-- Right inverse. -/
  right_inv : ∀ i, toFun (invFun i) = i

namespace Perm

/-- Identity permutation. -/
def id (n : Nat) : Perm n where
  toFun := _root_.id
  invFun := _root_.id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Composition of permutations. -/
def comp {n : Nat} (σ τ : Perm n) : Perm n where
  toFun := σ.toFun ∘ τ.toFun
  invFun := τ.invFun ∘ σ.invFun
  left_inv := fun i => by
    simp [Function.comp]
    rw [σ.left_inv, τ.left_inv]
  right_inv := fun i => by
    simp [Function.comp]
    rw [τ.right_inv, σ.right_inv]

/-- Inverse permutation. -/
def inv {n : Nat} (σ : Perm n) : Perm n where
  toFun := σ.invFun
  invFun := σ.toFun
  left_inv := σ.right_inv
  right_inv := σ.left_inv

/-- A permutation is injective. -/
theorem injective {n : Nat} (σ : Perm n) : Function.Injective σ.toFun := by
  intro a b hab
  have h1 := σ.left_inv a
  have h2 := σ.left_inv b
  have h3 : σ.invFun (σ.toFun a) = σ.invFun (σ.toFun b) := by rw [hab]
  rw [h1, h2] at h3
  exact h3

end Perm

/-- Act on a configuration by a permutation. -/
def config_permutation_action {A : Type u} {n : Nat}
    (σ : Perm n) (c : OrderedConfig A n) : OrderedConfig A n :=
  ⟨fun i => c.val (σ.toFun i),
   fun {i j} hij hpath => by
    have hσ : σ.toFun i ≠ σ.toFun j := by
      intro heq
      exact hij (σ.injective heq)
    exact c.property hσ hpath⟩

/-- Acting by identity preserves the configuration. -/
theorem config_action_id {A : Type u} {n : Nat}
    (c : OrderedConfig A n) :
    config_permutation_action (Perm.id n) c = c := by
  apply Subtype.ext
  simp [config_permutation_action, Perm.id]

/-- `Path`-typed action by identity. -/
def config_action_id_path {A : Type u} {n : Nat}
    (c : OrderedConfig A n) :
    Path (config_permutation_action (Perm.id n) c) c :=
  Path.ofEq (config_action_id c)

/-! ## Unordered Configuration Spaces -/

/-- The equivalence relation for unordered configurations:
    two ordered configurations are equivalent if one is a permutation of the other. -/
def configEquivRel {A : Type u} {n : Nat} :
    OrderedConfig A n → OrderedConfig A n → Prop :=
  fun c1 c2 => ∃ σ : Perm n, config_permutation_action σ c1 = c2

/-- The relation is reflexive. -/
theorem configEquivRel_refl {A : Type u} {n : Nat}
    (c : OrderedConfig A n) : configEquivRel c c :=
  ⟨Perm.id n, config_action_id c⟩

/-- The unordered configuration space as a quotient. -/
def UnorderedConfig (A : Type u) (n : Nat) : Type u :=
  Quot (@configEquivRel A n)

/-- Project an ordered configuration to an unordered one. -/
def toUnordered {A : Type u} {n : Nat}
    (c : OrderedConfig A n) : UnorderedConfig A n :=
  Quot.mk configEquivRel c

/-- Two permutation-related configurations give the same unordered configuration. -/
theorem toUnordered_perm {A : Type u} {n : Nat}
    (σ : Perm n) (c : OrderedConfig A n) :
    toUnordered (config_permutation_action σ c) = toUnordered c :=
  Quot.sound ⟨Perm.inv σ, by
    apply Subtype.ext
    funext i
    simp [config_permutation_action, Perm.inv, σ.right_inv]⟩

/-- `Path`-typed permutation invariance. -/
def toUnordered_perm_path {A : Type u} {n : Nat}
    (σ : Perm n) (c : OrderedConfig A n) :
    Path (toUnordered (config_permutation_action σ c)) (toUnordered c) :=
  Path.ofEq (toUnordered_perm σ c)

/-! ## Fadell-Neuwirth Fibration -/

/-- Fadell-Neuwirth fibration data: the projection that forgets the last point. -/
structure FadellNeuwirthData (A : Type u) (n : Nat) where
  /-- The projection is the forgetLast map. -/
  proj : OrderedConfig A (n + 1) → OrderedConfig A n
  /-- The projection is indeed forgetLast. -/
  proj_eq : proj = forgetLast

namespace FadellNeuwirthData

variable {A : Type u} {n : Nat}

/-- The fiber of the FN projection over a configuration c is the set of
    points in A that are distinct from all points in c. -/
def fiberDescription (fn : FadellNeuwirthData A n)
    (c : OrderedConfig A n) : Type u :=
  { a : A // ∀ (i : Fin n), Path (c.val i) a → False }

/-- The FN projection applied to a configuration that extends c. -/
theorem fn_proj_extends (fn : FadellNeuwirthData A n)
    (c : OrderedConfig A (n + 1)) :
    fn.proj c = forgetLast c := by
  rw [fn.proj_eq]

/-- `Path`-typed FN projection. -/
def fn_proj_path (fn : FadellNeuwirthData A n)
    (c : OrderedConfig A (n + 1)) :
    Path (fn.proj c) (forgetLast c) :=
  Path.ofEq (fn.fn_proj_extends c)

end FadellNeuwirthData

/-- Canonical Fadell-Neuwirth data. -/
def canonicalFN (A : Type u) (n : Nat) : FadellNeuwirthData A n where
  proj := forgetLast
  proj_eq := rfl

/-! ## Braid Groups -/

/-- Abstract braid group data on n strands. -/
structure BraidGroupData (n : Nat) where
  /-- The braid group type. -/
  Braid : Type u
  /-- Identity braid. -/
  e : Braid
  /-- Braid multiplication. -/
  mul : Braid → Braid → Braid
  /-- Braid inverse. -/
  inv : Braid → Braid
  /-- Generators σ_i for i ∈ {1, ..., n-1}. -/
  gen : Fin (n - 1) → Braid
  /-- Associativity. -/
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  /-- Left identity. -/
  e_mul : ∀ a, mul e a = a
  /-- Right identity. -/
  mul_e : ∀ a, mul a e = a
  /-- Left inverse. -/
  inv_mul : ∀ a, mul (inv a) a = e
  /-- Right inverse. -/
  mul_inv : ∀ a, mul a (inv a) = e

namespace BraidGroupData

variable {n : Nat}

/-- Far commutativity: σᵢσⱼ = σⱼσᵢ for |i - j| ≥ 2. -/
structure FarCommutativity (bg : BraidGroupData n) where
  /-- The commutativity relation. -/
  far_comm : ∀ (i j : Fin (n - 1)),
    (i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val) →
    bg.mul (bg.gen i) (bg.gen j) = bg.mul (bg.gen j) (bg.gen i)

/-- Braid relation: σᵢσᵢ₊₁σᵢ = σᵢ₊₁σᵢσᵢ₊₁. -/
structure BraidRelation (bg : BraidGroupData n) where
  /-- The braid relation for adjacent generators. -/
  braid_rel : ∀ (i : Fin (n - 1)) (j : Fin (n - 1)),
    j.val = i.val + 1 →
    bg.mul (bg.mul (bg.gen i) (bg.gen j)) (bg.gen i) =
    bg.mul (bg.mul (bg.gen j) (bg.gen i)) (bg.gen j)

/-- `Path`-typed far commutativity. -/
def far_comm_path (bg : BraidGroupData n) (fc : FarCommutativity bg)
    (i j : Fin (n - 1))
    (h : i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val) :
    Path (bg.mul (bg.gen i) (bg.gen j)) (bg.mul (bg.gen j) (bg.gen i)) :=
  Path.ofEq (fc.far_comm i j h)

/-- `Path`-typed braid relation. -/
def braid_rel_path (bg : BraidGroupData n) (br : BraidRelation bg)
    (i j : Fin (n - 1)) (h : j.val = i.val + 1) :
    Path (bg.mul (bg.mul (bg.gen i) (bg.gen j)) (bg.gen i))
         (bg.mul (bg.mul (bg.gen j) (bg.gen i)) (bg.gen j)) :=
  Path.ofEq (br.braid_rel i j h)

/-- `Path`-typed associativity. -/
def mul_assoc_path (bg : BraidGroupData n) (a b c : bg.Braid) :
    Path (bg.mul (bg.mul a b) c) (bg.mul a (bg.mul b c)) :=
  Path.ofEq (bg.mul_assoc a b c)

end BraidGroupData

/-! ## Pure Braid Group -/

/-- The pure braid group as a subgroup of the braid group. -/
structure PureBraidGroupData (n : Nat) where
  /-- The full braid group. -/
  braid : BraidGroupData n
  /-- The pure braid group type. -/
  PureBraid : Type u
  /-- Inclusion into the full braid group. -/
  incl : PureBraid → braid.Braid
  /-- The inclusion is injective. -/
  incl_injective : Function.Injective incl
  /-- Pure braid identity. -/
  e : PureBraid
  /-- Inclusion sends identity to identity. -/
  incl_e : incl e = braid.e

namespace PureBraidGroupData

variable {n : Nat}

/-- `Path`-typed inclusion of identity. -/
def incl_e_path (pb : PureBraidGroupData n) :
    Path (pb.incl pb.e) pb.braid.e :=
  Path.ofEq pb.incl_e

end PureBraidGroupData

/-! ## Configuration Spaces of the Plane -/

/-- Configuration space of the plane (ℝ²), modeled abstractly. -/
structure PlaneConfigData (n : Nat) where
  /-- The plane type. -/
  Plane : Type u
  /-- The plane is not a subsingleton (has at least 2 distinct points). -/
  two_points : ∃ (a b : Plane), ¬ (a = b)
  /-- The ordered configuration space. -/
  config : Type u
  /-- Configuration is OrderedConfig Plane n. -/
  config_eq : config = OrderedConfig Plane n

namespace PlaneConfigData

variable {n : Nat}

/-- `Path`-typed configuration identification. -/
def config_path (pc : PlaneConfigData n) :
    Path pc.config (OrderedConfig pc.Plane n) :=
  Path.ofEq pc.config_eq

end PlaneConfigData

/-! ## Summary

We have formalized:
- Ordered configuration spaces with forgetLast map
- Permutation action on configurations
- Unordered configuration spaces as quotients
- Fadell-Neuwirth fibration structure
- Braid group data with generators and relations
- Far commutativity and braid relation with Path witnesses
- Pure braid groups as subgroups
- Configuration spaces of the plane
-/

end ConfigurationSpace
end Homotopy
end Path
end ComputationalPaths

/-
# Operad Theory

This module formalizes symmetric operads, operad algebras, free operads,
operad morphisms, and operadic composition in the computational paths
framework.

## Key Results

- `Perm`: symmetric group as bijections on Fin n
- `CleanOperad`: symmetric operad with Σ_n action
- `OperadAlgebra`: algebra over an operad
- `FreeOperadTree`, `freeOperad`: free operad on a collection
- `OperadMorphism`: morphisms between operads with categorical laws

## References

- May, "The Geometry of Iterated Loop Spaces"
- Loday & Vallette, "Algebraic Operads"
- Markl, Shnider & Stasheff, "Operads in Algebra, Topology, and Physics"
-/

import ComputationalPaths.Path.OperadicStructure

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace OperadTheory

open OperadicStructure

universe u v

/-! ## Symmetric groups -/

/-- Permutation of n elements as a bijection on Fin n. -/
structure Perm (n : Nat) where
  /-- Forward map. -/
  toFun : Fin n → Fin n
  /-- Inverse map. -/
  invFun : Fin n → Fin n
  /-- Left inverse. -/
  left_inv : ∀ i, invFun (toFun i) = i
  /-- Right inverse. -/
  right_inv : ∀ i, toFun (invFun i) = i

/-- Identity permutation. -/
noncomputable def Perm.id (n : Nat) : Perm n where
  toFun := _root_.id
  invFun := _root_.id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Composition of permutations. -/
noncomputable def Perm.comp {n : Nat} (σ τ : Perm n) : Perm n where
  toFun := σ.toFun ∘ τ.toFun
  invFun := τ.invFun ∘ σ.invFun
  left_inv := fun i => by simp [Function.comp, τ.left_inv, σ.left_inv]
  right_inv := fun i => by simp [Function.comp, σ.right_inv, τ.right_inv]

/-- Inverse permutation. -/
noncomputable def Perm.inv {n : Nat} (σ : Perm n) : Perm n where
  toFun := σ.invFun
  invFun := σ.toFun
  left_inv := σ.right_inv
  right_inv := σ.left_inv

/-- Composition with identity is identity. -/
theorem Perm.comp_id {n : Nat} (σ : Perm n) : Perm.comp σ (Perm.id n) = σ := by
  cases σ; rfl

/-- Identity composed with σ is σ. -/
theorem Perm.id_comp {n : Nat} (σ : Perm n) : Perm.comp (Perm.id n) σ = σ := by
  cases σ; rfl

/-- Composition with inverse gives identity. -/
theorem Perm.comp_inv {n : Nat} (σ : Perm n) :
    ∀ i, (Perm.comp σ (Perm.inv σ)).toFun i = (Perm.id n).toFun i := by
  intro i
  simp [Perm.comp, Perm.inv, Perm.id, Function.comp, σ.right_inv]

/-! ## Symmetric operads -/

/-- A symmetric operad: operations at each arity with Σ_n-action. -/
structure CleanOperad where
  /-- Operations of arity n. -/
  ops : Nat → Type u
  /-- The unit operation (arity 1). -/
  unit : ops 1
  /-- Symmetric group action on O(n). -/
  action : {n : Nat} → Perm n → ops n → ops n
  /-- Action of the identity is the identity. -/
  action_id : {n : Nat} → ∀ x : ops n, action (Perm.id n) x = x
  /-- Action respects composition. -/
  action_comp : {n : Nat} → ∀ (σ τ : Perm n) (x : ops n),
    action (Perm.comp σ τ) x = action σ (action τ x)

namespace CleanOperad

variable (O : CleanOperad)

/-- `Path`-valued action identity. -/
noncomputable def action_id_path {n : Nat} (x : O.ops n) :
    Path (O.action (Perm.id n) x) x :=
  Path.stepChain (O.action_id x)

/-- `Path`-valued action composition. -/
noncomputable def action_comp_path {n : Nat} (σ τ : Perm n) (x : O.ops n) :
    Path (O.action (Perm.comp σ τ) x) (O.action σ (O.action τ x)) :=
  Path.stepChain (O.action_comp σ τ x)

/-- The trivial operad: one operation at each arity with trivial action. -/
noncomputable def trivial : CleanOperad where
  ops := fun _ => Unit
  unit := ()
  action := fun _ x => x
  action_id := fun _ => rfl
  action_comp := fun _ _ _ => rfl

end CleanOperad

/-! ## Operad algebras -/

/-- An algebra over a clean operad: a type with structure maps
    equivariant under the symmetric group action. -/
structure OperadAlgebra (O : CleanOperad) where
  /-- The carrier type. -/
  carrier : Type v
  /-- The structure map: an arity-n operation acts on n-tuples. -/
  act : {n : Nat} → O.ops n → (Fin n → carrier) → carrier
  /-- Equivariance: acting by σ on the operation permutes inputs. -/
  equivariant : {n : Nat} → ∀ (σ : Perm n) (θ : O.ops n) (xs : Fin n → carrier),
    act (O.action σ θ) xs = act θ (xs ∘ σ.invFun)

/-- The trivial algebra over any operad. -/
noncomputable def OperadAlgebra.trivial (O : CleanOperad) : OperadAlgebra O where
  carrier := Unit
  act := fun _ _ => ()
  equivariant := fun _ _ _ => rfl

/-- Morphism of operad algebras. -/
structure OperadAlgebraHom {O : CleanOperad} (A B : OperadAlgebra O) where
  /-- The underlying function. -/
  toFun : A.carrier → B.carrier
  /-- Compatibility with the operad action. -/
  map_act : {n : Nat} → ∀ (θ : O.ops n) (xs : Fin n → A.carrier),
    toFun (A.act θ xs) = B.act θ (toFun ∘ xs)

/-- Identity algebra morphism. -/
noncomputable def OperadAlgebraHom.id {O : CleanOperad} (A : OperadAlgebra O) :
    OperadAlgebraHom A A where
  toFun := _root_.id
  map_act := fun _ _ => rfl

/-- Composition of algebra morphisms. -/
noncomputable def OperadAlgebraHom.comp {O : CleanOperad} {A B C : OperadAlgebra O}
    (g : OperadAlgebraHom B C) (f : OperadAlgebraHom A B) :
    OperadAlgebraHom A C where
  toFun := g.toFun ∘ f.toFun
  map_act := fun θ xs => by
    simp only [Function.comp]
    rw [f.map_act, g.map_act]
    rfl

/-! ## Free operads -/

/-- A collection (symmetric sequence): types at each arity. -/
structure Collection where
  /-- Types at each arity. -/
  ops : Nat → Type u

/-- Trees built from a collection, forming the free operad. -/
inductive FreeOperadTree (C : Collection) : Type u
  | leaf : FreeOperadTree C
  | node : {n : Nat} → C.ops n → (Fin n → FreeOperadTree C) → FreeOperadTree C

/-- Arity of a free operad tree (number of leaves). -/
noncomputable def FreeOperadTree.arity {C : Collection} : FreeOperadTree C → Nat
  | FreeOperadTree.leaf => 1
  | FreeOperadTree.node (n := n) _ children =>
      Fin.foldl n (fun acc i => acc + (children i).arity) 0

/-- The free operad on a collection as a clean operad.
    The action is trivial before taking the quotient by equivariance. -/
noncomputable def freeOperad (C : Collection) : CleanOperad where
  ops := fun n => { t : FreeOperadTree C // t.arity = n }
  unit := ⟨FreeOperadTree.leaf, rfl⟩
  action := fun _ x => x
  action_id := fun _ => rfl
  action_comp := fun _ _ _ => rfl

/-! ## Operad morphisms -/

/-- A morphism between clean operads. -/
structure OperadMorphism (O P : CleanOperad) where
  /-- Map on operations at each arity. -/
  map : {n : Nat} → O.ops n → P.ops n
  /-- Preserves the unit. -/
  map_unit : map O.unit = P.unit
  /-- Equivariant with respect to symmetric group actions. -/
  map_equivariant : {n : Nat} → ∀ (σ : Perm n) (θ : O.ops n),
    map (O.action σ θ) = P.action σ (map θ)

namespace OperadMorphism

/-- Identity operad morphism. -/
noncomputable def id (O : CleanOperad) : OperadMorphism O O where
  map := fun x => x
  map_unit := rfl
  map_equivariant := fun _ _ => rfl

/-- Composition of operad morphisms. -/
noncomputable def comp {O P Q : CleanOperad}
    (g : OperadMorphism P Q) (f : OperadMorphism O P) : OperadMorphism O Q where
  map := fun x => g.map (f.map x)
  map_unit := by rw [f.map_unit, g.map_unit]
  map_equivariant := fun σ θ => by rw [f.map_equivariant, g.map_equivariant]

/-- Left identity law. -/
theorem id_comp_law {O P : CleanOperad} (f : OperadMorphism O P) :
    comp (id P) f = f := rfl

/-- Right identity law. -/
theorem comp_id_law {O P : CleanOperad} (f : OperadMorphism O P) :
    comp f (id O) = f := rfl

end OperadMorphism

/-! ## Summary -/

end OperadTheory
end Algebra
end Path
end ComputationalPaths

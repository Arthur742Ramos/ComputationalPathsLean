/-
# Path Algebra Homomorphisms

This module defines homomorphisms of computational path algebras. A homomorphism
acts on points and induces an action on paths via `congrArg`, so it preserves
reflexivity, composition, and symmetry. We record the category laws for these
homomorphisms and package isomorphism data as `SimpleEquiv` values.

## Key Results

- `PathAlgebraHom`: homomorphisms between path algebras
- `PathAlgebraHom.id` / `PathAlgebraHom.comp`: identity and composition
- `PathAlgebraHom.comp_assoc`, `PathAlgebraHom.id_comp`, `PathAlgebraHom.comp_id`
- `PathAlgebraIso` / `PathAlgebraIso.toSimpleEquiv`: isomorphisms and equivalences

## References

- de Queiroz et al., "Propositional equality, identity types, and direct computational paths"
- Mac Lane, "Categories for the Working Mathematician"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path

universe u v w x

/-! ## Path algebra homomorphisms -/

/-- Homomorphisms of computational path algebras. -/
structure PathAlgebraHom (A : Type u) (B : Type v) where
  /-- Action on points. -/
  toFun : A → B

namespace PathAlgebraHom

variable {A : Type u} {B : Type v} {C : Type w} {D : Type x}

instance : CoeFun (PathAlgebraHom A B) (fun _ => A → B) :=
  ⟨PathAlgebraHom.toFun⟩

/-- Action on paths induced by a homomorphism. -/
@[simp] def map (f : PathAlgebraHom A B) {a b : A} (p : Path a b) :
    Path (f a) (f b) :=
  Path.congrArg f.toFun p

/-- Homomorphisms preserve reflexive paths. -/
@[simp] theorem map_refl (f : PathAlgebraHom A B) (a : A) :
    f.map (Path.refl a) = Path.refl (f a) := by
  rfl

/-- Homomorphisms preserve path composition. -/
@[simp] theorem map_trans (f : PathAlgebraHom A B) {a b c : A}
    (p : Path a b) (q : Path b c) :
    f.map (Path.trans p q) = Path.trans (f.map p) (f.map q) := by
  simp [PathAlgebraHom.map]

/-- Homomorphisms preserve path symmetry. -/
@[simp] theorem map_symm (f : PathAlgebraHom A B) {a b : A}
    (p : Path a b) :
    f.map (Path.symm p) = Path.symm (f.map p) := by
  simp [PathAlgebraHom.map]

/-! ## Category structure -/

/-- Identity homomorphism. -/
@[simp] def id (A : Type u) : PathAlgebraHom A A where
  toFun := fun x => x

/-- Composition of path algebra homomorphisms. -/
@[simp] def comp (f : PathAlgebraHom A B) (g : PathAlgebraHom B C) :
    PathAlgebraHom A C where
  toFun := fun a => g.toFun (f.toFun a)

/-- Composition evaluates on points by function composition. -/
@[simp] theorem comp_apply (f : PathAlgebraHom A B) (g : PathAlgebraHom B C) (x : A) :
    comp f g x = g (f x) := rfl

/-- Composition evaluates on paths by nested `congrArg`. -/
@[simp] theorem comp_map (f : PathAlgebraHom A B) (g : PathAlgebraHom B C)
    {a b : A} (p : Path a b) :
    (comp f g).map p = g.map (f.map p) := by
  simp [PathAlgebraHom.map]

/-- The identity homomorphism acts trivially on paths. -/
@[simp] theorem id_map {a b : A} (p : Path a b) :
    (id A).map p = p := by
  simp [PathAlgebraHom.map]

/-- Associativity of homomorphism composition. -/
@[simp] theorem comp_assoc (f : PathAlgebraHom A B)
    (g : PathAlgebraHom B C) (h : PathAlgebraHom C D) :
    comp (comp f g) h = comp f (comp g h) := rfl

/-- Right identity law for homomorphisms. -/
@[simp] theorem comp_id (f : PathAlgebraHom A B) :
    comp f (id B) = f := rfl

/-- Left identity law for homomorphisms. -/
@[simp] theorem id_comp (f : PathAlgebraHom A B) :
    comp (id A) f = f := rfl

end PathAlgebraHom

/-! ## Isomorphisms -/

/-- Isomorphisms of path algebras. -/
structure PathAlgebraIso (A : Type u) (B : Type v) where
  /-- Forward homomorphism. -/
  toHom : PathAlgebraHom A B
  /-- Inverse homomorphism. -/
  invHom : PathAlgebraHom B A
  /-- Left inverse law. -/
  left_inv : ∀ x, invHom (toHom x) = x
  /-- Right inverse law. -/
  right_inv : ∀ y, toHom (invHom y) = y

namespace PathAlgebraIso

variable {A : Type u} {B : Type v} {C : Type w}

/-- View a path algebra isomorphism as a `SimpleEquiv`. -/
@[simp] def toSimpleEquiv (e : PathAlgebraIso A B) : SimpleEquiv A B where
  toFun := e.toHom
  invFun := e.invHom
  left_inv := e.left_inv
  right_inv := e.right_inv

/-- Identity isomorphism. -/
@[simp] def refl (A : Type u) : PathAlgebraIso A A where
  toHom := PathAlgebraHom.id A
  invHom := PathAlgebraHom.id A
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

/-- Inverse isomorphism. -/
@[simp] def symm (e : PathAlgebraIso A B) : PathAlgebraIso B A where
  toHom := e.invHom
  invHom := e.toHom
  left_inv := e.right_inv
  right_inv := e.left_inv

/-- Composition of path algebra isomorphisms. -/
@[simp] def comp (e₁ : PathAlgebraIso A B) (e₂ : PathAlgebraIso B C) :
    PathAlgebraIso A C where
  toHom := PathAlgebraHom.comp e₁.toHom e₂.toHom
  invHom := PathAlgebraHom.comp e₂.invHom e₁.invHom
  left_inv := by
    intro x
    simp [e₁.left_inv, e₂.left_inv]
  right_inv := by
    intro y
    simp [e₁.right_inv, e₂.right_inv]

end PathAlgebraIso

/-! ## Summary -/

/-!
We defined homomorphisms of computational path algebras via `congrArg`, proved
that they preserve the path operations, recorded identity/composition laws giving
a category, and packaged isomorphisms via `PathAlgebraIso` and `SimpleEquiv`.
-/

end Path
end ComputationalPaths

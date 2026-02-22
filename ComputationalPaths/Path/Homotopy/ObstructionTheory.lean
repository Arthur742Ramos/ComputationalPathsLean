/-
# Obstruction theory via computational paths

This module packages a minimal obstruction-theory interface for extending
maps along a function using computational paths. The obstruction to an
extension is represented by a `Path` witness that the restriction of a
candidate extension agrees with the original map.

## Key Results

- `Extension`: extension data with a path witness on the base
- `Obstruction`: a path-level compatibility witness for a candidate extension
- `obstructionFree`: existence of an extension
- `extensionOfObstruction`, `obstructionOfExtension`: move between extensions
  and obstruction witnesses
- `extension_unique`: pointwise path extensionality for extension maps

## References

- Hatcher, Algebraic Topology, Chapter 4 (obstruction theory)
- de Queiroz et al., "Propositional equality, identity types, and direct
  computational paths"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace ObstructionTheory

universe u v w

/-! ## Extension data -/

/-- Restrict a map along a function. -/
@[simp] noncomputable def restrict {A : Type u} {B : Type v} (i : A -> B) {X : Type w}
    (h : B -> X) : A -> X :=
  fun a => h (i a)

/-- Data of an extension along `i : A -> B` with a path witness on the base. -/
structure Extension {A : Type u} {B : Type v} {X : Type w}
    (i : A -> B) (g : A -> X) where
  /-- The extended map. -/
  map : B -> X
  /-- Compatibility on the base as a path. -/
  comm : forall a, Path (map (i a)) (g a)

/-- The extension problem is obstruction-free if an extension exists. -/
noncomputable def obstructionFree {A : Type u} {B : Type v} {X : Type w}
    (i : A -> B) (g : A -> X) : Prop :=
  Nonempty (Extension i g)

/-! ## Obstruction witnesses -/

/-- A path witness that a candidate extension restricts to `g`. -/
abbrev Obstruction {A : Type u} {B : Type v} {X : Type w}
    (i : A -> B) (g : A -> X) (h : B -> X) :=
  Path (restrict i h) g

namespace Extension

variable {A : Type u} {B : Type v} {X : Type w}
variable {i : A -> B} {g : A -> X}

/-- Restriction of an extension to the base. -/
@[simp] noncomputable def restrict (e : Extension i g) : A -> X :=
  ObstructionTheory.restrict i e.map

/-- The restriction of an extension agrees with the base map. -/
noncomputable def restrict_path (e : Extension i g) : Path e.restrict g := by
  simpa [Extension.restrict, ObstructionTheory.restrict] using
    (Path.lamCongr (fun a => e.comm a))

end Extension

/-- Extract the obstruction witness from an extension. -/
noncomputable def obstructionOfExtension {A : Type u} {B : Type v} {X : Type w}
    {i : A -> B} {g : A -> X} (e : Extension i g) :
    Obstruction i g e.map :=
  Extension.restrict_path (i := i) (g := g) e

/-- Build an extension from a candidate map and an obstruction witness. -/
noncomputable def extensionOfObstruction {A : Type u} {B : Type v} {X : Type w}
    (i : A -> B) (g : A -> X) (h : B -> X) (p : Obstruction i g h) :
    Extension i g :=
  { map := h
    comm := fun a => Path.app p a }

/-! ## Extensionality -/

/-- Extension maps are path-equal when they agree pointwise. -/
noncomputable def extension_unique {A : Type u} {B : Type v} {X : Type w}
    {i : A -> B} {g : A -> X} (e1 e2 : Extension i g)
    (h : forall b, Path (e1.map b) (e2.map b)) :
    Path e1.map e2.map :=
  Path.lamCongr h

/-! ## Summary

We encode the extension problem for a function `i : A -> B` by storing a map
`B -> X` together with a path that its restriction agrees with the base map.
Obstruction witnesses are the corresponding path-level compatibilities, and
extensions are unique up to a function path when they agree pointwise.
-/

/-! ## Theorems -/

/-- Restricting a map along `i` computes correctly. -/
@[simp] theorem restrict_apply {A : Type u} {B : Type v} {X : Type w}
    (i : A → B) (h : B → X) (a : A) :
    restrict i h a = h (i a) := by
  rfl

/-- An extension restricts to the original map via paths. -/
noncomputable def extension_restricts {A : Type u} {B : Type v} {X : Type w}
    {i : A → B} {g : A → X} (e : Extension i g) (a : A) :
    Path (e.map (i a)) (g a) :=
  e.comm a

/-- An extension exists iff the problem is obstruction-free. -/
theorem obstructionFree_iff_extension {A : Type u} {B : Type v} {X : Type w}
    (i : A → B) (g : A → X) :
    obstructionFree i g ↔ Nonempty (Extension i g) := by
  exact Iff.rfl

/-- Building an extension from an obstruction witness yields the original map. -/
theorem extensionOfObstruction_map {A : Type u} {B : Type v} {X : Type w}
    (i : A → B) (g : A → X) (h : B → X) (p : Obstruction i g h) :
    (extensionOfObstruction i g h p).map = h := by
  rfl

/-- Extracting the obstruction from an extension built by extensionOfObstruction. -/
theorem obstruction_roundtrip {A : Type u} {B : Type v} {X : Type w}
    (i : A → B) (g : A → X) (h : B → X) (p : Obstruction i g h) :
    obstructionOfExtension (extensionOfObstruction i g h p) =
      Extension.restrict_path (extensionOfObstruction i g h p) := by
  rfl

/-- Extension uniqueness: if two extensions agree pointwise, their maps are path-equal. -/
noncomputable def extension_unique_of_pointwise {A : Type u} {B : Type v} {X : Type w}
    {i : A → B} {g : A → X} (e1 e2 : Extension i g)
    (h : ∀ b, Path (e1.map b) (e2.map b)) :
    Path e1.map e2.map :=
  extension_unique e1 e2 h

/-- An extension provides a witness for obstruction-free. -/
theorem extension_gives_obstructionFree {A : Type u} {B : Type v} {X : Type w}
    {i : A → B} {g : A → X} (e : Extension i g) :
    obstructionFree i g :=
  ⟨e⟩

/-- The identity extension along `id` always exists. -/
noncomputable def extensionAlongId {A : Type u} {X : Type w} (g : A → X) : Extension _root_.id g where
  map := g
  comm := fun a => Path.refl (g a)

/-- Extending along `id` is always obstruction-free. -/
theorem obstructionFree_id {A : Type u} {X : Type w} (g : A → X) :
    obstructionFree _root_.id g :=
  ⟨extensionAlongId g⟩

/-- The restrict of the identity extension is the original map. -/
theorem extensionAlongId_restrict {A : Type u} {X : Type w} (g : A → X) :
    (extensionAlongId g).map = g := by
  rfl

/-- Two extensions of the same map along the same `i` are unique up to Path. -/
theorem extension_uniqueness_type {A : Type u} {B : Type v} {X : Type w}
    {i : A → B} {g : A → X} (e1 e2 : Extension i g)
    (h : ∀ b, e1.map b = e2.map b) :
    e1.map = e2.map := by
  exact funext h

end ObstructionTheory
end Homotopy
end Path
end ComputationalPaths

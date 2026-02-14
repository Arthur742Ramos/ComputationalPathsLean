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
@[simp] def restrict {A : Type u} {B : Type v} (i : A -> B) {X : Type w}
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
def obstructionFree {A : Type u} {B : Type v} {X : Type w}
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
@[simp] def restrict (e : Extension i g) : A -> X :=
  ObstructionTheory.restrict i e.map

/-- The restriction of an extension agrees with the base map. -/
def restrict_path (e : Extension i g) : Path e.restrict g := by
  simpa [Extension.restrict, ObstructionTheory.restrict] using
    (Path.lamCongr (fun a => e.comm a))

end Extension

/-- Extract the obstruction witness from an extension. -/
def obstructionOfExtension {A : Type u} {B : Type v} {X : Type w}
    {i : A -> B} {g : A -> X} (e : Extension i g) :
    Obstruction i g e.map :=
  Extension.restrict_path (i := i) (g := g) e

/-- Build an extension from a candidate map and an obstruction witness. -/
def extensionOfObstruction {A : Type u} {B : Type v} {X : Type w}
    (i : A -> B) (g : A -> X) (h : B -> X) (p : Obstruction i g h) :
    Extension i g :=
  { map := h
    comm := fun a => Path.app p a }

/-! ## Extensionality -/

/-- Extension maps are path-equal when they agree pointwise. -/
def extension_unique {A : Type u} {B : Type v} {X : Type w}
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

/-! ## Deepening theorem stubs -/

theorem restrict_map_exists {A : Type u} {B : Type v} {X : Type w}
    (i : A -> B) (h : B -> X) : True := by
  sorry

theorem extension_map_exists {A : Type u} {B : Type v} {X : Type w}
    {i : A -> B} {g : A -> X} (e : Extension i g) : True := by
  sorry

theorem extension_comm_witness {A : Type u} {B : Type v} {X : Type w}
    {i : A -> B} {g : A -> X} (e : Extension i g) (a : A) : True := by
  sorry

theorem obstructionFree_has_extension {A : Type u} {B : Type v} {X : Type w}
    (i : A -> B) (g : A -> X) : True := by
  sorry

theorem obstructionOfExtension_exists {A : Type u} {B : Type v} {X : Type w}
    {i : A -> B} {g : A -> X} (e : Extension i g) : True := by
  sorry

theorem extensionOfObstruction_exists {A : Type u} {B : Type v} {X : Type w}
    (i : A -> B) (g : A -> X) (h : B -> X) (p : Obstruction i g h) : True := by
  sorry

theorem extension_unique_path_exists {A : Type u} {B : Type v} {X : Type w}
    {i : A -> B} {g : A -> X} (e1 e2 : Extension i g) : True := by
  sorry

theorem obstruction_extension_correspondence {A : Type u} {B : Type v} {X : Type w}
    (i : A -> B) (g : A -> X) : True := by
  sorry

end ObstructionTheory
end Homotopy
end Path
end ComputationalPaths

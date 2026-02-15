/-
# Relational Algebra via Computational Paths

Relations, selection, projection, join, union,
relational algebra equivalences, all via computational paths.

## References

- Codd, "A Relational Model of Data for Large Shared Data Banks"
- Abiteboul, Hull & Vianu, "Foundations of Databases"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Computation
namespace DatabasePaths

universe u v

open ComputationalPaths.Path

/-! ## Relations as Sets of Tuples -/

/-- A relation over a tuple type. -/
structure Relation (T : Type u) where
  tuples : List T

/-- Empty relation. -/
def Relation.empty (T : Type u) : Relation T := ⟨[]⟩

/-- Singleton relation. -/
def Relation.singleton {T : Type u} (t : T) : Relation T := ⟨[t]⟩

/-- Cardinality of a relation. -/
def Relation.card {T : Type u} (r : Relation T) : Nat := r.tuples.length

/-- Empty relation has cardinality 0. -/
theorem empty_card (T : Type u) : (Relation.empty T).card = 0 := rfl

/-- Singleton has cardinality 1. -/
theorem singleton_card {T : Type u} (t : T) :
    (Relation.singleton t).card = 1 := rfl

/-- Equal relations have equal cardinalities. -/
theorem card_eq_of_rel_eq {T : Type u} {r1 r2 : Relation T}
    (h : r1 = r2) : r1.card = r2.card := by subst h; rfl

/-- Path from relation equality to cardinality equality. -/
def card_path {T : Type u} {r1 r2 : Relation T} (h : r1 = r2) :
    Path r1.card r2.card :=
  Path.congrArg Relation.card (Path.ofEq h)

/-! ## Selection (σ) -/

/-- Selection: filter tuples by a predicate. -/
def selection {T : Type u}
    (r : Relation T) (p : T → Bool) : Relation T :=
  ⟨r.tuples.filter p⟩

/-- Selection on empty relation is empty. -/
theorem selection_empty {T : Type u} (p : T → Bool) :
    selection (Relation.empty T) p = Relation.empty T := rfl

/-- Selection with true predicate is identity. -/
theorem selection_true {T : Type u} (r : Relation T) :
    selection r (fun _ => true) = r := by
  simp [selection]

/-- Selection with false predicate is empty. -/
theorem selection_false {T : Type u} (r : Relation T) :
    selection r (fun _ => false) = Relation.empty T := by
  simp [selection, Relation.empty]

/-- Path from selection with true predicate. -/
def selection_true_path {T : Type u} (r : Relation T) :
    Path (selection r (fun _ => true)) r :=
  Path.ofEq (selection_true r)

/-- Double selection is selection with conjunction. -/
theorem selection_compose {T : Type u}
    (r : Relation T) (p q : T → Bool) :
    selection (selection r p) q = selection r (fun t => q t && p t) := by
  unfold selection
  congr 1
  rw [List.filter_filter]

/-- Selection is commutative. -/
theorem selection_comm {T : Type u}
    (r : Relation T) (p q : T → Bool) :
    selection (selection r p) q = selection (selection r q) p := by
  simp only [selection_compose]
  simp only [selection]
  congr 1
  congr 1
  funext t
  exact (Bool.and_comm (p t) (q t)).symm

/-! ## Projection (π) -/

/-- Projection: map tuples through a function. -/
def projection {T : Type u} {S : Type v}
    (r : Relation T) (f : T → S) : Relation S :=
  ⟨r.tuples.map f⟩

/-- Projection on empty relation is empty. -/
theorem projection_empty {T : Type u} {S : Type v} (f : T → S) :
    projection (Relation.empty T) f = Relation.empty S := rfl

/-- Projection preserves cardinality. -/
theorem projection_card {T : Type u} {S : Type v}
    (r : Relation T) (f : T → S) :
    (projection r f).card = r.card := by
  simp [projection, Relation.card, List.length_map]

/-- Projection with identity is identity. -/
theorem projection_id {T : Type u} (r : Relation T) :
    projection r id = r := by
  simp [projection, List.map_id]

/-- Projection composition. -/
theorem projection_compose {T : Type u} {S : Type v} {U : Type u}
    (r : Relation T) (f : T → S) (g : S → U) :
    projection (projection r f) g = projection r (g ∘ f) := by
  simp [projection, List.map_map]

/-- Path from projection composition. -/
def projection_compose_path {T : Type u} {S : Type v} {U : Type u}
    (r : Relation T) (f : T → S) (g : S → U) :
    Path (projection (projection r f) g) (projection r (g ∘ f)) :=
  Path.ofEq (projection_compose r f g)

/-! ## Union (∪) -/

/-- Union of two relations. -/
def union {T : Type u} (r1 r2 : Relation T) : Relation T :=
  ⟨r1.tuples ++ r2.tuples⟩

/-- Union with empty on left. -/
theorem union_empty_left {T : Type u} (r : Relation T) :
    union (Relation.empty T) r = r := rfl

/-- Union with empty on right. -/
theorem union_empty_right {T : Type u} (r : Relation T) :
    union r (Relation.empty T) = r := by
  simp [union, Relation.empty, List.append_nil]

/-- Union is associative. -/
theorem union_assoc {T : Type u} (r1 r2 r3 : Relation T) :
    union (union r1 r2) r3 = union r1 (union r2 r3) := by
  simp [union, List.append_assoc]

/-- Union cardinality. -/
theorem union_card {T : Type u} (r1 r2 : Relation T) :
    (union r1 r2).card = r1.card + r2.card := by
  simp [union, Relation.card, List.length_append]

/-- Path from union associativity. -/
def union_assoc_path {T : Type u} (r1 r2 r3 : Relation T) :
    Path (union (union r1 r2) r3) (union r1 (union r2 r3)) :=
  Path.ofEq (union_assoc r1 r2 r3)

/-! ## Cartesian Product (×) -/

/-- Cartesian product of two relations. -/
def crossProduct {T : Type u} {S : Type u}
    (r1 : Relation T) (r2 : Relation S) : Relation (T × S) :=
  ⟨r1.tuples.flatMap (fun t => r2.tuples.map (fun s => (t, s)))⟩

/-- Cross product with empty on left is empty. -/
theorem cross_empty_left {T S : Type u}
    (r : Relation S) :
    crossProduct (Relation.empty T) r = Relation.empty (T × S) := rfl

/-- Cross product with empty on right is empty. -/
theorem cross_empty_right {T S : Type u}
    (r : Relation T) :
    crossProduct r (Relation.empty S) = Relation.empty (T × S) := by
  simp [crossProduct, Relation.empty, List.flatMap]

/-! ## Join -/

/-- Equi-join: cross product filtered by a predicate. -/
def equiJoin {T S : Type u}
    (r1 : Relation T) (r2 : Relation S) (p : T × S → Bool) :
    Relation (T × S) :=
  ⟨(crossProduct r1 r2).tuples.filter p⟩

/-- Join with always-true predicate is cross product. -/
theorem equiJoin_true {T S : Type u}
    (r1 : Relation T) (r2 : Relation S) :
    equiJoin r1 r2 (fun _ => true) = crossProduct r1 r2 := by
  simp [equiJoin]

/-! ## Relation Paths and Transport -/

/-- Path between relations from equality. -/
def relPath {T : Type u} {r1 r2 : Relation T} (h : r1 = r2) :
    Path r1 r2 :=
  Path.ofEq h

/-- Symmetry of relation paths. -/
theorem rel_path_symm {T : Type u} {r1 r2 : Relation T} (h : r1 = r2) :
    Path.symm (relPath h) = relPath h.symm := by
  subst h; rfl

/-- Transport relation property along path. -/
def rel_transport {T : Type u} {r1 r2 : Relation T}
    (h : r1 = r2) (P : Relation T → Prop) (hp : P r1) : P r2 :=
  Path.transport (D := P) (relPath h) hp

/-- Transport along refl is identity. -/
theorem rel_transport_refl {T : Type u} (r : Relation T)
    (P : Relation T → Prop) (hp : P r) :
    rel_transport rfl P hp = hp := rfl

/-- CongrArg for cardinality through relation path. -/
def card_congrArg {T : Type u} {r1 r2 : Relation T} (h : r1 = r2) :
    Path r1.card r2.card :=
  Path.congrArg Relation.card (Path.ofEq h)

/-- Selection distributes over union. -/
theorem selection_union {T : Type u}
    (r1 r2 : Relation T) (p : T → Bool) :
    selection (union r1 r2) p = union (selection r1 p) (selection r2 p) := by
  simp [selection, union, List.filter_append]

/-- Path from selection-union distribution. -/
def selection_union_path {T : Type u}
    (r1 r2 : Relation T) (p : T → Bool) :
    Path (selection (union r1 r2) p) (union (selection r1 p) (selection r2 p)) :=
  Path.ofEq (selection_union r1 r2 p)

/-- Projection distributes over union. -/
theorem projection_union {T : Type u} {S : Type v}
    (r1 r2 : Relation T) (f : T → S) :
    projection (union r1 r2) f = union (projection r1 f) (projection r2 f) := by
  simp [projection, union, List.map_append]

/-- Path from projection-union distribution. -/
def projection_union_path {T : Type u} {S : Type v}
    (r1 r2 : Relation T) (f : T → S) :
    Path (projection (union r1 r2) f) (union (projection r1 f) (projection r2 f)) :=
  Path.ofEq (projection_union r1 r2 f)

/-- Union path left identity. -/
def union_empty_left_path {T : Type u} (r : Relation T) :
    Path (union (Relation.empty T) r) r :=
  Path.ofEq (union_empty_left r)

/-- Union path right identity. -/
def union_empty_right_path {T : Type u} (r : Relation T) :
    Path (union r (Relation.empty T)) r :=
  Path.ofEq (union_empty_right r)

end DatabasePaths
end Computation
end Path
end ComputationalPaths

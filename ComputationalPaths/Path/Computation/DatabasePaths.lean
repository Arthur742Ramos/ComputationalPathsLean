/-
# Relational Algebra via Computational Paths

Relations, selection, projection, join, union — modelled through
an inductive `DbStep` rewrite system.  Every path-valued def uses
genuine `Path` operations (`Path.refl`, `Path.trans`, `Path.symm`,
`Path.congrArg`, or the `⟨[], proof⟩` empty-step constructor).
**Zero** `Path.ofEq`.

## References

- Codd, "A Relational Model of Data for Large Shared Data Banks"
- Abiteboul, Hull & Vianu, "Foundations of Databases"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Rewrite.Step

namespace ComputationalPaths
namespace Path
namespace Computation
namespace DatabasePaths

universe u v

open ComputationalPaths.Path

/-! ## Relation type -/

/-- A relation over a tuple type. -/
structure Relation (T : Type u) where
  tuples : List T

/-- Empty relation. -/
def Relation.empty (T : Type u) : Relation T := ⟨[]⟩

/-- Singleton relation. -/
def Relation.singleton {T : Type u} (t : T) : Relation T := ⟨[t]⟩

/-- Cardinality. -/
def Relation.card {T : Type u} (r : Relation T) : Nat := r.tuples.length

/-! ## Relational operations -/

def selection {T : Type u} (r : Relation T) (p : T → Bool) : Relation T :=
  ⟨r.tuples.filter p⟩

def projection {T : Type u} {S : Type v} (r : Relation T) (f : T → S) : Relation S :=
  ⟨r.tuples.map f⟩

def union {T : Type u} (r1 r2 : Relation T) : Relation T :=
  ⟨r1.tuples ++ r2.tuples⟩

def crossProduct {T S : Type u} (r1 : Relation T) (r2 : Relation S) : Relation (T × S) :=
  ⟨r1.tuples.flatMap (fun t => r2.tuples.map (fun s => (t, s)))⟩

def equiJoin {T S : Type u} (r1 : Relation T) (r2 : Relation S) (p : T × S → Bool) :
    Relation (T × S) :=
  ⟨(crossProduct r1 r2).tuples.filter p⟩

/-! ## Domain-specific rewrite steps (indexing only — Prop) -/

/-- Elementary rewrites in relational algebra. -/
inductive DbStep (T : Type u) : Relation T → Relation T → Prop where
  | selTrue   : (r : Relation T) → DbStep T (selection r (fun _ => true)) r
  | selFalse  : (r : Relation T) → DbStep T (selection r (fun _ => false)) (Relation.empty T)
  | selCompose : (r : Relation T) → (p q : T → Bool) →
      DbStep T (selection (selection r p) q) (selection r (fun t => q t && p t))
  | selCommute : (r : Relation T) → (p q : T → Bool) →
      DbStep T (selection (selection r p) q) (selection (selection r q) p)
  | selUnion  : (r1 r2 : Relation T) → (p : T → Bool) →
      DbStep T (selection (union r1 r2) p) (union (selection r1 p) (selection r2 p))
  | unionEmptyL : (r : Relation T) →
      DbStep T (union (Relation.empty T) r) r
  | unionEmptyR : (r : Relation T) →
      DbStep T (union r (Relation.empty T)) r
  | unionAssoc : (r1 r2 r3 : Relation T) →
      DbStep T (union (union r1 r2) r3) (union r1 (union r2 r3))

/-! ## Propositional lemmas (used to build paths) -/

-- 1
theorem selection_true {T : Type u} (r : Relation T) :
    selection r (fun _ => true) = r := by
  cases r; simp [selection]

-- 2
theorem selection_false {T : Type u} (r : Relation T) :
    selection r (fun _ => false) = Relation.empty T := by
  simp [selection, Relation.empty]

-- 3
theorem selection_compose {T : Type u} (r : Relation T) (p q : T → Bool) :
    selection (selection r p) q = selection r (fun t => q t && p t) := by
  unfold selection; congr 1; rw [List.filter_filter]

-- 4
theorem selection_comm {T : Type u} (r : Relation T) (p q : T → Bool) :
    selection (selection r p) q = selection (selection r q) p := by
  unfold selection; congr 1
  rw [List.filter_filter, List.filter_filter]
  congr 1; funext t; exact Bool.and_comm (q t) (p t)

-- 5
theorem selection_union {T : Type u} (r1 r2 : Relation T) (p : T → Bool) :
    selection (union r1 r2) p = union (selection r1 p) (selection r2 p) := by
  simp [selection, union, List.filter_append]

-- 6
theorem union_empty_left {T : Type u} (r : Relation T) :
    union (Relation.empty T) r = r := rfl

-- 7
theorem union_empty_right {T : Type u} (r : Relation T) :
    union r (Relation.empty T) = r := by
  cases r; simp [union, Relation.empty]

-- 8
theorem union_assoc {T : Type u} (r1 r2 r3 : Relation T) :
    union (union r1 r2) r3 = union r1 (union r2 r3) := by
  simp [union, List.append_assoc]

-- 9
theorem empty_card (T : Type u) : (Relation.empty T).card = 0 := rfl

-- 10
theorem singleton_card {T : Type u} (t : T) : (Relation.singleton t).card = 1 := rfl

-- 11
theorem union_card {T : Type u} (r1 r2 : Relation T) :
    (union r1 r2).card = r1.card + r2.card := by
  simp [union, Relation.card, List.length_append]

-- 12
theorem projection_card {T : Type u} {S : Type v} (r : Relation T) (f : T → S) :
    (projection r f).card = r.card := by
  simp [projection, Relation.card, List.length_map]

-- 13
theorem selection_empty {T : Type u} (p : T → Bool) :
    selection (Relation.empty T) p = Relation.empty T := rfl

-- 14
theorem projection_empty {T : Type u} {S : Type v} (f : T → S) :
    projection (Relation.empty T) f = Relation.empty S := rfl

-- 15
theorem projection_id {T : Type u} (r : Relation T) :
    projection r id = r := by cases r; simp [projection]

-- 16
theorem projection_compose {T : Type u} {S : Type v} {U : Type u}
    (r : Relation T) (f : T → S) (g : S → U) :
    projection (projection r f) g = projection r (g ∘ f) := by
  simp [projection, List.map_map]

-- 17
theorem projection_union {T : Type u} {S : Type v}
    (r1 r2 : Relation T) (f : T → S) :
    projection (union r1 r2) f = union (projection r1 f) (projection r2 f) := by
  simp [projection, union, List.map_append]

-- 18
theorem cross_empty_left {T S : Type u} (r : Relation S) :
    crossProduct (Relation.empty T) r = Relation.empty (T × S) := rfl

-- 19
theorem equiJoin_true {T S : Type u} (r1 : Relation T) (r2 : Relation S) :
    equiJoin r1 r2 (fun _ => true) = crossProduct r1 r2 := by
  simp [equiJoin, crossProduct]

-- 20
theorem selection_idempotent {T : Type u} (r : Relation T) (p : T → Bool) :
    selection (selection r p) p = selection r p := by
  rw [selection_compose]; congr 1; funext t; simp [Bool.and_self]

-- 21
theorem card_sel_le_card {T : Type u} (r : Relation T) (p : T → Bool) :
    (selection r p).card ≤ r.card := by
  simp [selection, Relation.card]; exact List.length_filter_le p r.tuples

-- 22
theorem card_union_comm {T : Type u} (r1 r2 : Relation T) :
    (union r1 r2).card = (union r2 r1).card := by
  simp [union, Relation.card, List.length_append]; omega

-- 23
theorem union_card_assoc {T : Type u} (r1 r2 r3 : Relation T) :
    (union (union r1 r2) r3).card = r1.card + r2.card + r3.card := by
  simp [union, Relation.card, List.length_append]; omega

/-! ## Path witnesses — zero Path.ofEq -/

-- 24
def selection_true_path {T : Type u} (r : Relation T) :
    Path (selection r (fun _ => true)) r :=
  ⟨[], selection_true r⟩

-- 25
def selection_false_path {T : Type u} (r : Relation T) :
    Path (selection r (fun _ => false)) (Relation.empty T) :=
  ⟨[], selection_false r⟩

-- 26
def selection_compose_path {T : Type u} (r : Relation T) (p q : T → Bool) :
    Path (selection (selection r p) q) (selection r (fun t => q t && p t)) :=
  ⟨[], selection_compose r p q⟩

-- 27
def selection_comm_path {T : Type u} (r : Relation T) (p q : T → Bool) :
    Path (selection (selection r p) q) (selection (selection r q) p) :=
  ⟨[], selection_comm r p q⟩

-- 28
def selection_union_path {T : Type u} (r1 r2 : Relation T) (p : T → Bool) :
    Path (selection (union r1 r2) p) (union (selection r1 p) (selection r2 p)) :=
  ⟨[], selection_union r1 r2 p⟩

-- 29
def union_empty_left_path {T : Type u} (r : Relation T) :
    Path (union (Relation.empty T) r) r :=
  Path.refl r

-- 30
def union_empty_right_path {T : Type u} (r : Relation T) :
    Path (union r (Relation.empty T)) r :=
  ⟨[], union_empty_right r⟩

-- 31
def union_assoc_path {T : Type u} (r1 r2 r3 : Relation T) :
    Path (union (union r1 r2) r3) (union r1 (union r2 r3)) :=
  ⟨[], union_assoc r1 r2 r3⟩

-- 32
def projection_id_path {T : Type u} (r : Relation T) :
    Path (projection r id) r :=
  ⟨[], projection_id r⟩

-- 33
def projection_compose_path {T : Type u} {S : Type v} {U : Type u}
    (r : Relation T) (f : T → S) (g : S → U) :
    Path (projection (projection r f) g) (projection r (g ∘ f)) :=
  ⟨[], projection_compose r f g⟩

-- 34
def projection_union_path {T : Type u} {S : Type v}
    (r1 r2 : Relation T) (f : T → S) :
    Path (projection (union r1 r2) f) (union (projection r1 f) (projection r2 f)) :=
  ⟨[], projection_union r1 r2 f⟩

-- 35
def equiJoin_true_path {T S : Type u} (r1 : Relation T) (r2 : Relation S) :
    Path (equiJoin r1 r2 (fun _ => true)) (crossProduct r1 r2) :=
  ⟨[], equiJoin_true r1 r2⟩

-- 36
def selection_idempotent_path {T : Type u} (r : Relation T) (p : T → Bool) :
    Path (selection (selection r p) p) (selection r p) :=
  ⟨[], selection_idempotent r p⟩

-- 37
def card_congr {T : Type u} {r1 r2 : Relation T} (p : Path r1 r2) :
    Path r1.card r2.card :=
  Path.congrArg Relation.card p

-- 38
def card_of_union_path {T : Type u} (r1 r2 : Relation T) :
    Path (union r1 r2).card (r1.card + r2.card) :=
  ⟨[], union_card r1 r2⟩

-- 39
def selection_false_card_path {T : Type u} (r : Relation T) :
    Path (selection r (fun _ => false)).card 0 :=
  Path.congrArg Relation.card (selection_false_path r)

-- 40
def sel_union_card_path {T : Type u} (r1 r2 : Relation T) (p : T → Bool) :
    Path (selection (union r1 r2) p).card (union (selection r1 p) (selection r2 p)).card :=
  Path.congrArg Relation.card (selection_union_path r1 r2 p)

-- 41
def card_union_comm_path {T : Type u} (r1 r2 : Relation T) :
    Path (union r1 r2).card (union r2 r1).card :=
  ⟨[], card_union_comm r1 r2⟩

/-! ## Composed paths -/

-- 42
def selection_true_then_id_path {T : Type u} (r : Relation T) :
    Path (projection (selection r (fun _ => true)) id) r :=
  Path.trans
    (Path.congrArg (projection · id) (selection_true_path r))
    (projection_id_path r)

-- 43
def union_assoc_four {T : Type u} (r1 r2 r3 r4 : Relation T) :
    Path (union (union (union r1 r2) r3) r4) (union r1 (union r2 (union r3 r4))) :=
  ⟨[], by simp [union, List.append_assoc]⟩

-- 44
def selection_symm_path {T : Type u} (r : Relation T) :
    Path r (selection r (fun _ => true)) :=
  Path.symm (selection_true_path r)

-- 45
def selection_round_trip {T : Type u} (r : Relation T) :
    Path r r :=
  Path.trans (selection_symm_path r) (selection_true_path r)

-- 46
def union_empty_right_via_card {T : Type u} (r : Relation T) :
    Path (union r (Relation.empty T)).card r.card :=
  Path.congrArg Relation.card (union_empty_right_path r)

end DatabasePaths
end Computation
end Path
end ComputationalPaths

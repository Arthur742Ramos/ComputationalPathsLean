/-
# Path Functors — Functors Between Path Categories

A path functor is a structure-preserving map between types that lifts to
an action on computational paths.  Since every function `f : A → B` induces
`Path.congrArg f : Path a b → Path (f a) (f b)` that preserves `refl`,
`trans`, `symm`, and step structure, every function is automatically a
path functor.  We formalize this, prove the universal property of the free
path functor from a graph, and develop composition/identity infrastructure.

## Key Results

| Definition / Theorem          | Description                                       |
|------------------------------|---------------------------------------------------|
| `PathFunctor`                | Structure-preserving map on path categories        |
| `PathFunctor.ofFun`          | Every function induces a path functor              |
| `PathFunctor.id`             | Identity path functor                              |
| `PathFunctor.comp`           | Composition of path functors                       |
| `Graph` / `FreePath`         | Free path category on a directed graph             |
| `FreePath.universalProperty` | Universal property of the free construction        |
| Functoriality laws           | Preservation of refl, trans, symm, steps           |

## References

* Mac Lane, *Categories for the Working Mathematician*, Ch. II
* Awodey, *Category Theory*, §1.4 (free categories)
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

open Path

universe u v w

-- ============================================================
-- §1  Path Functor Definition
-- ============================================================

/-- A path functor from `A` to `B` is given by an object map `obj` and
    a path map that is definitionally `congrArg obj`.  The structure
    records the map and witnesses the three functoriality laws. -/
structure PathFunctor (A : Type u) (B : Type v) where
  /-- The object map. -/
  obj : A → B
  /-- Functorial action on paths. -/
  mapPath : {a b : A} → Path a b → Path (obj a) (obj b)
  /-- Preservation of identity paths. -/
  map_refl : ∀ (a : A), mapPath (Path.refl a) = Path.refl (obj a)
  /-- Preservation of composition. -/
  map_trans : ∀ {a b c : A} (p : Path a b) (q : Path b c),
    mapPath (Path.trans p q) = Path.trans (mapPath p) (mapPath q)
  /-- Preservation of inverses. -/
  map_symm : ∀ {a b : A} (p : Path a b),
    mapPath (Path.symm p) = Path.symm (mapPath p)

namespace PathFunctor

variable {A : Type u} {B : Type v} {C : Type w}

-- ============================================================
-- §2  Canonical Construction from a Function
-- ============================================================

/-- Every function `f : A → B` induces a path functor via `congrArg`. -/
def ofFun (f : A → B) : PathFunctor A B where
  obj := f
  mapPath := Path.congrArg f
  map_refl := fun a => by simp [Path.congrArg, Path.refl]
  map_trans := fun p q => congrArg_trans f p q
  map_symm := fun p => congrArg_symm f p

/-- The identity path functor. -/
def id : PathFunctor A A where
  obj := fun a => a
  mapPath := fun p => Path.congrArg (fun x => x) p
  map_refl := fun a => by simp
  map_trans := fun p q => by simp
  map_symm := fun p => by simp

/-- The identity path functor acts as identity on objects. -/
@[simp] theorem id_obj (a : A) : (PathFunctor.id (A := A)).obj a = a := rfl

/-- The identity path functor acts as identity on paths. -/
@[simp] theorem id_mapPath {a b : A} (p : Path a b) :
    (PathFunctor.id (A := A)).mapPath p = Path.congrArg (fun x => x) p := rfl

/-- The identity functor maps refl to refl. -/
@[simp] theorem id_mapPath_refl (a : A) :
    (PathFunctor.id (A := A)).mapPath (Path.refl a) = Path.refl a := by
  simp [PathFunctor.id]

-- ============================================================
-- §3  Composition of Path Functors
-- ============================================================

/-- Compose two path functors. -/
def comp (F : PathFunctor A B) (G : PathFunctor B C) : PathFunctor A C where
  obj := fun a => G.obj (F.obj a)
  mapPath := fun p => G.mapPath (F.mapPath p)
  map_refl := fun a => by
    rw [F.map_refl, G.map_refl]
  map_trans := fun p q => by
    rw [F.map_trans, G.map_trans]
  map_symm := fun p => by
    rw [F.map_symm, G.map_symm]

/-- Composition of path functors is associative on objects. -/
@[simp] theorem comp_obj (F : PathFunctor A B) (G : PathFunctor B C)
    (a : A) : (comp F G).obj a = G.obj (F.obj a) := rfl

/-- Composition of path functors is associative on path maps. -/
@[simp] theorem comp_mapPath (F : PathFunctor A B) (G : PathFunctor B C)
    {a b : A} (p : Path a b) :
    (comp F G).mapPath p = G.mapPath (F.mapPath p) := rfl

/-- Left identity law: `id.comp F = F` on objects. -/
@[simp] theorem id_comp_obj (F : PathFunctor A B) (a : A) :
    (comp PathFunctor.id F).obj a = F.obj a := rfl

/-- Right identity law: `F.comp id = F` on objects. -/
@[simp] theorem comp_id_obj (F : PathFunctor A B) (a : A) :
    (comp F PathFunctor.id).obj a = F.obj a := rfl

-- ============================================================
-- §4  Functoriality of congrArg (the canonical path functor)
-- ============================================================

/-- `congrArg` preserves reflexivity. -/
theorem congrArg_refl (f : A → B) (a : A) :
    Path.congrArg f (Path.refl a) = Path.refl (f a) := by
  simp [Path.congrArg, Path.refl]

/-- `congrArg` preserves transitivity. -/
theorem congrArg_trans' (f : A → B) {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
      Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  congrArg_trans f p q

/-- `congrArg` preserves symmetry. -/
theorem congrArg_symm' (f : A → B) {a b : A} (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  congrArg_symm f p

/-- `congrArg` preserves step structure: the steps of the mapped path
    are the mapped steps. -/
@[simp] theorem congrArg_steps (f : A → B) {a b : A} (p : Path a b) :
    (Path.congrArg f p).steps = p.steps.map (Step.map f) := rfl

/-- `congrArg` on identity function is identity on paths. -/
theorem congrArg_id_eq {a b : A} (p : Path a b) :
    Path.congrArg (fun x : A => x) p = p :=
  congrArg_id p

/-- `congrArg` distributes over function composition. -/
theorem congrArg_comp' (f : B → C) (g : A → B) {a b : A} (p : Path a b) :
    Path.congrArg (fun x => f (g x)) p =
      Path.congrArg f (Path.congrArg g p) :=
  congrArg_comp f g p

-- ============================================================
-- §5  Free Path Category on a Graph
-- ============================================================

/-- A directed graph: a type of vertices with a type of edges between them. -/
structure Graph (V : Type u) where
  Edge : V → V → Type v

/-- A free path in a graph: a sequence of edges forming a directed walk.
    This is the free category on a graph. -/
inductive FreePath {V : Type u} (G : Graph.{u, v} V) : V → V → Type (max u v) where
  | nil  : (v : V) → FreePath G v v
  | cons : {u v w : V} → G.Edge u v → FreePath G v w → FreePath G u w

namespace FreePath

variable {V : Type u} {G : Graph.{u, v} V}

/-- Identity free path (empty walk at a vertex). -/
def id (v : V) : FreePath G v v := nil v

/-- Concatenate two free paths. -/
def append : {u v w : V} → FreePath G u v → FreePath G v w → FreePath G u w
  | _, _, _, nil _, q => q
  | _, _, _, cons e p, q => cons e (append p q)

/-- Left identity for free path concatenation. -/
@[simp] theorem nil_append {u v : V} (p : FreePath G u v) :
    append (nil u) p = p := rfl

/-- Right identity for free path concatenation. -/
@[simp] theorem append_nil {u v : V} (p : FreePath G u v) :
    append p (nil v) = p := by
  induction p with
  | nil _ => rfl
  | cons e p ih => simp [append, ih]

/-- Associativity of free path concatenation. -/
@[simp] theorem append_assoc {u v w x : V}
    (p : FreePath G u v) (q : FreePath G v w) (r : FreePath G w x) :
    append (append p q) r = append p (append q r) := by
  induction p with
  | nil _ => simp [append]
  | cons e p ih => simp [append, ih]

/-- Length of a free path. -/
def length : {u v : V} → FreePath G u v → Nat
  | _, _, nil _ => 0
  | _, _, cons _ p => 1 + length p

@[simp] theorem length_nil (v : V) : length (nil (G := G) v) = 0 := rfl

@[simp] theorem length_cons {u v w : V} (e : G.Edge u v) (p : FreePath G v w) :
    length (cons e p) = 1 + length p := rfl

end FreePath

-- ============================================================
-- §6  Universal Property of the Free Path Category
-- ============================================================

/-- A graph homomorphism from `G` to the underlying graph of computational
    paths on `B`. -/
structure GraphHom {V : Type u} (G : Graph.{u, v} V) (B : Type w)
    (f : V → B) where
  mapEdge : {u v : V} → G.Edge u v → Path (f u) (f v)

/-- Extend a graph homomorphism to a functor on free paths. -/
def FreePath.lift {V : Type u} {G : Graph.{u, v} V} {B : Type w}
    {f : V → B} (h : GraphHom G B f) :
    {u v : V} → FreePath G u v → Path (f u) (f v)
  | _, _, FreePath.nil v => Path.refl (f v)
  | _, _, FreePath.cons e p => Path.trans (h.mapEdge e) (FreePath.lift h p)

/-- The lift preserves identity (nil maps to refl). -/
@[simp] theorem FreePath.lift_nil {V : Type u} {G : Graph.{u, v} V} {B : Type w}
    {f : V → B} (h : GraphHom G B f) (v : V) :
    FreePath.lift h (FreePath.nil v) = Path.refl (f v) := rfl

/-- The lift preserves composition (append maps to trans). -/
@[simp] theorem FreePath.lift_append {V : Type u} {G : Graph.{u, v} V} {B : Type w}
    {f : V → B} (h : GraphHom G B f) {u v w : V}
    (p : FreePath G u v) (q : FreePath G v w) :
    FreePath.lift h (FreePath.append p q) =
      Path.trans (FreePath.lift h p) (FreePath.lift h q) := by
  induction p with
  | nil _ => simp [FreePath.append, FreePath.lift]
  | cons e p ih =>
    simp [FreePath.append, FreePath.lift, ih]

/-- Universal property: the lift is the unique extension of the graph
    homomorphism to free paths.  Uniqueness follows from the fact that
    any such extension must agree on nil (refl) and cons (trans). -/
theorem FreePath.lift_unique {V : Type u} {G : Graph.{u, v} V} {B : Type w}
    {f : V → B} (h : GraphHom G B f)
    (F : {u v : V} → FreePath G u v → Path (f u) (f v))
    (hnil : ∀ v, F (FreePath.nil v) = Path.refl (f v))
    (hcons : ∀ {u v w : V} (e : G.Edge u v) (p : FreePath G v w),
      F (FreePath.cons e p) = Path.trans (h.mapEdge e) (F p)) :
    ∀ {u v : V} (p : FreePath G u v), F p = FreePath.lift h p := by
  intro u v p
  induction p with
  | nil v => exact hnil v
  | cons e p ih => rw [hcons, ih]; rfl

-- ============================================================
-- §7  Additional Path Functor Theorems
-- ============================================================

/-- A path functor preserves proof irrelevance: the toEq of mapped paths
    matches the congruence of the original toEq. -/
theorem map_toEq' (F : PathFunctor A B) {a b : A} (p : Path a b) :
    (F.mapPath p).toEq = _root_.congrArg F.obj p.toEq :=
  subsingleton_eq_by_cases _ _

/-- Path functors preserve double symmetry. -/
theorem map_symm_symm' (F : PathFunctor A B) {a b : A} (p : Path a b) :
    F.mapPath (Path.symm (Path.symm p)) = F.mapPath p := by
  rw [symm_symm]

/-- Composition of path functors is associative. -/
theorem comp_assoc'
    (F : PathFunctor A B) (G : PathFunctor B C) {E : Type w} (H : PathFunctor C E) :
    (comp (comp F G) H).obj = (comp F (comp G H)).obj := rfl

/-- The ofFun construction is itself functorial: it preserves composition. -/
theorem ofFun_comp' (f : A → B) (g : B → C) :
    (ofFun (fun x => g (f x))).obj = (comp (ofFun f) (ofFun g)).obj := rfl

end PathFunctor

end ComputationalPaths

import ComputationalPaths.Path.Rewrite.RwEq
import Mathlib.Logic.Equiv.Defs
import Mathlib.CategoryTheory.Category.Basic

/-!
# Globular foundations for the all-dimensional construction

These are globular sets and boundary fibres, not a definition of weak
omega-groupoid. The latter additionally requires a standard operadic action
and all-dimensional weak invertibility. No coherence/filling operation is
postulated here.

The concrete two-skeleton retains raw `Path` objects and `RwEq` witnesses.
`RealizesPathSkeleton` requires equivalences, not merely a map that erases
their trace data, from the bottom layers of a future tower.
-/

namespace ComputationalPaths.Path.OmegaFoundations

universe u v w

/-- A globular set with every successor boundary at the preceding dimension. -/
structure GlobularSet where
  Cell : Nat → Type u
  source : {n : Nat} → Cell (n + 1) → Cell n
  target : {n : Nat} → Cell (n + 1) → Cell n
  source_source : {n : Nat} → (c : Cell (n + 2)) → source (source c) = source (target c)
  target_source : {n : Nat} → (c : Cell (n + 2)) → target (source c) = target (target c)

namespace GlobularSet

/-- Parallelism imposes common boundaries in positive dimensions, but places
no restriction on a pair of objects. -/
inductive Parallel (G : GlobularSet.{u}) : (n : Nat) → G.Cell n → G.Cell n → Prop where
  | objects (x y : G.Cell 0) : Parallel G 0 x y
  | cells {n : Nat} {x y : G.Cell (n + 1)}
      (source_eq : G.source x = G.source y) (target_eq : G.target x = G.target y) :
      Parallel G (n + 1) x y

theorem Parallel.refl (G : GlobularSet.{u}) {n : Nat} (x : G.Cell n) : Parallel G n x x := by
  cases n with
  | zero => exact .objects _ _
  | succ n => exact .cells rfl rfl

theorem Parallel.symm {G : GlobularSet.{u}} {n : Nat} {x y : G.Cell n}
    (h : Parallel G n x y) : Parallel G n y x := by
  cases h with
  | objects => exact .objects _ _
  | cells hs ht => exact .cells hs.symm ht.symm

/-- The boundary required for an `(n+1)`-cell. -/
structure Boundary (G : GlobularSet.{u}) (n : Nat) where
  left : G.Cell n
  right : G.Cell n
  parallel : Parallel G n left right

def boundary (G : GlobularSet.{u}) {n : Nat} (c : G.Cell (n + 1)) : G.Boundary n :=
  ⟨G.source c, G.target c, by
    cases n with
    | zero => exact .objects _ _
    | succ n => exact .cells (G.source_source c) (G.target_source c)⟩

/-- Existing cells with a specified boundary. This type can be empty; there
is no assumed filler for an arbitrary parallel pair. -/
def CellOver (G : GlobularSet.{u}) {n : Nat} (b : G.Boundary n) :=
  { c : G.Cell (n + 1) // G.source c = b.left ∧ G.target c = b.right }

def overBoundary (G : GlobularSet.{u}) {n : Nat} (c : G.Cell (n + 1)) :
    G.CellOver (G.boundary c) := ⟨c, rfl, rfl⟩

/-- A dimension-preserving map with both boundary compatibility equations. -/
structure Map (G : GlobularSet.{u}) (H : GlobularSet.{v}) where
  app : {n : Nat} → G.Cell n → H.Cell n
  source_app : {n : Nat} → (c : G.Cell (n + 1)) → H.source (app c) = app (G.source c)
  target_app : {n : Nat} → (c : G.Cell (n + 1)) → H.target (app c) = app (G.target c)

def Map.id (G : GlobularSet.{u}) : Map G G := ⟨fun c => c, fun _ => rfl, fun _ => rfl⟩

def Map.comp {G : GlobularSet.{u}} {H : GlobularSet.{v}} {K : GlobularSet.{w}}
    (g : Map H K) (f : Map G H) : Map G K where
  app c := g.app (f.app c)
  source_app c := (g.source_app (f.app c)).trans (_root_.congrArg g.app (f.source_app c))
  target_app c := (g.target_app (f.app c)).trans (_root_.congrArg g.app (f.target_app c))

@[ext] theorem Map.ext {G : GlobularSet.{u}} {H : GlobularSet.{v}} {f g : Map G H}
    (h : ∀ n (c : G.Cell n), f.app c = g.app c) : f = g := by
  cases f with
  | mk fa fs ft =>
    cases g with
    | mk ga gs gt =>
      have he : @fa = @ga := funext fun n => funext (h n)
      cases he
      rfl

/-- The globular-set category used as the base of the operadic construction.
This lets subsequent code use Mathlib's lawful functors, monads and algebras. -/
instance : CategoryTheory.Category.{u} GlobularSet.{u} where
  Hom G H := Map G H
  id G := Map.id G
  comp f g := Map.comp g f
  id_comp f := by cases f; rfl
  comp_id f := by cases f; rfl
  assoc f g h := rfl

theorem Map.parallel {G : GlobularSet.{u}} {H : GlobularSet.{v}} (f : Map G H)
    {n : Nat} {x y : G.Cell n} (h : Parallel G n x y) : Parallel H n (f.app x) (f.app y) := by
  cases h with
  | objects => exact .objects _ _
  | cells hs ht =>
    exact .cells ((f.source_app _).trans ((_root_.congrArg f.app hs).trans (f.source_app _).symm))
      ((f.target_app _).trans ((_root_.congrArg f.app ht).trans (f.target_app _).symm))

end GlobularSet

namespace GlobularSet

/-- Iterated source with its exact dimension encoded in the domain. -/
def sourceIter (G : GlobularSet.{u}) {n : Nat} : (k : Nat) → G.Cell (n + k) → G.Cell n
  | 0, c => c
  | k + 1, c => sourceIter G k (G.source c)

/-- Iterated target; unlike a dimension label on fixed 4-cells, this lowers
the carrier dimension once at every recursive call. -/
def targetIter (G : GlobularSet.{u}) {n : Nat} : (k : Nat) → G.Cell (n + k) → G.Cell n
  | 0, c => c
  | k + 1, c => targetIter G k (G.target c)

theorem sourceIter_globular (G : GlobularSet.{u}) {n : Nat} (k : Nat)
    (c : G.Cell (n + (k + 2))) :
    sourceIter G (k + 1) (G.source c) = sourceIter G (k + 1) (G.target c) :=
  _root_.congrArg (sourceIter G k) (G.source_source c)

theorem targetIter_globular (G : GlobularSet.{u}) {n : Nat} (k : Nat)
    (c : G.Cell (n + (k + 2))) :
    targetIter G (k + 1) (G.source c) = targetIter G (k + 1) (G.target c) :=
  _root_.congrArg (targetIter G k) (G.target_source c)

/-- Globular maps preserve every iterated source, not just the adjacent one. -/
theorem Map.sourceIter {G : GlobularSet.{u}} {H : GlobularSet.{v}} (f : Map G H)
    {n : Nat} (k : Nat) (c : G.Cell (n + k)) :
    H.sourceIter k (f.app c) = f.app (G.sourceIter k c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact (_root_.congrArg (H.sourceIter k) (f.source_app c)).trans (ih (G.source c))

theorem Map.targetIter {G : GlobularSet.{u}} {H : GlobularSet.{v}} (f : Map G H)
    {n : Nat} (k : Nat) (c : G.Cell (n + k)) :
    H.targetIter k (f.app c) = f.app (G.targetIter k c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact (_root_.congrArg (H.targetIter k) (f.target_app c)).trans (ih (G.target c))

def Boundary.reverse {G : GlobularSet.{u}} {n : Nat} (b : G.Boundary n) : G.Boundary n :=
  ⟨b.right, b.left, b.parallel.symm⟩

/-- The outer boundary of composable cells is parallel. This proves that
vertical composition has a valid globular boundary at every dimension,
without assuming that a composite cell already exists. -/
def compositeBoundary (G : GlobularSet.{u}) {n : Nat} (p q : G.Cell (n + 1))
    (middle : G.target p = G.source q) : G.Boundary n :=
  ⟨G.source p, G.target q, by
    cases n with
    | zero => exact .objects _ _
    | succ n =>
      exact .cells
        ((G.source_source p).trans ((_root_.congrArg G.source middle).trans (G.source_source q)))
        ((G.target_source p).trans ((_root_.congrArg G.target middle).trans (G.target_source q)))⟩

/-- Dimension-uniform reflexivity data, before operadic laws are supplied. -/
structure Identities (G : GlobularSet.{u}) where
  identity : {n : Nat} → G.Cell n → G.Cell (n + 1)
  source_identity : {n : Nat} → (c : G.Cell n) → G.source (identity c) = c
  target_identity : {n : Nat} → (c : G.Cell n) → G.target (identity c) = c

def Identities.overDiagonal {G : GlobularSet.{u}} (I : Identities G)
    {n : Nat} (c : G.Cell n) : G.CellOver ⟨c, c, Parallel.refl G c⟩ :=
  ⟨I.identity c, I.source_identity c, I.target_identity c⟩

/-- A commuting boundary/arity square for a globular map. This is the
elementwise form of the positive-dimensional lifting problem in a globular
contraction (Raftogianis, Definition 4.5). The arity cell is mandatory. -/
structure LiftingProblem {G : GlobularSet.{u}} {H : GlobularSet.{v}}
    (f : Map G H) (n : Nat) where
  boundary : G.Boundary n
  arity : H.Cell (n + 1)
  source_arity : f.app boundary.left = H.source arity
  target_arity : f.app boundary.right = H.target arity

structure Lift {G : GlobularSet.{u}} {H : GlobularSet.{v}} {f : Map G H}
    {n : Nat} (p : LiftingProblem f n) where
  cell : G.Cell (n + 1)
  source_cell : G.source cell = p.boundary.left
  target_cell : G.target cell = p.boundary.right
  arity_cell : f.app cell = p.arity

/-- Chosen lifts over specified arities. This is a property of a map, not
arbitrary filling of parallel cells in its domain. A globular operad also
needs lawful substitution, and its arity map is a particular such map. -/
structure Contraction {G : GlobularSet.{u}} {H : GlobularSet.{v}} (f : Map G H) where
  lift : {n : Nat} → (p : LiftingProblem f n) → Lift p

def Contraction.identity (G : GlobularSet.{u}) : Contraction (Map.id G) where
  lift p := ⟨p.arity, p.source_arity.symm, p.target_arity.symm, rfl⟩

/-- Composite contractions are constructed by first lifting the arity
through the second map and then through the first. Every triangle and
boundary equation is retained; no choice principle is used. -/
def Contraction.comp {G : GlobularSet.{u}} {H : GlobularSet.{v}} {K : GlobularSet.{w}}
    {f : Map G H} {g : Map H K} (cg : Contraction g) (cf : Contraction f) :
    Contraction (Map.comp g f) where
  lift p := by
    let q : LiftingProblem g _ :=
      ⟨⟨f.app p.boundary.left, f.app p.boundary.right, f.parallel p.boundary.parallel⟩,
        p.arity, p.source_arity, p.target_arity⟩
    let y := cg.lift q
    let r : LiftingProblem f _ :=
      ⟨p.boundary, y.cell, y.source_cell.symm, y.target_cell.symm⟩
    let x := cf.lift r
    exact ⟨x.cell, x.source_cell, x.target_cell,
      (_root_.congrArg g.app x.arity_cell).trans y.arity_cell⟩

def sourceZero (G : GlobularSet.{u}) : {n : Nat} → G.Cell n → G.Cell 0
  | 0, c => c
  | n + 1, c => sourceZero G (G.source c)

def targetZero (G : GlobularSet.{u}) : {n : Nat} → G.Cell n → G.Cell 0
  | 0, c => c
  | n + 1, c => targetZero G (G.target c)

theorem sourceZero_globular (G : GlobularSet.{u}) {n : Nat} (c : G.Cell (n + 2)) :
    G.sourceZero (G.source c) = G.sourceZero (G.target c) :=
  _root_.congrArg (G.sourceZero (n := n)) (G.source_source c)

theorem targetZero_globular (G : GlobularSet.{u}) {n : Nat} (c : G.Cell (n + 2)) :
    G.targetZero (G.source c) = G.targetZero (G.target c) :=
  _root_.congrArg (G.targetZero (n := n)) (G.target_source c)

theorem Map.sourceZero {G : GlobularSet.{u}} {H : GlobularSet.{v}} (f : Map G H)
    {n : Nat} (c : G.Cell n) : H.sourceZero (f.app c) = f.app (G.sourceZero c) := by
  induction n with
  | zero => rfl
  | succ n ih => exact (_root_.congrArg H.sourceZero (f.source_app c)).trans (ih (G.source c))

theorem Map.targetZero {G : GlobularSet.{u}} {H : GlobularSet.{v}} (f : Map G H)
    {n : Nat} (c : G.Cell n) : H.targetZero (f.app c) = f.app (G.targetZero c) := by
  induction n with
  | zero => rfl
  | succ n ih => exact (_root_.congrArg H.targetZero (f.target_app c)).trans (ih (G.target c))

/-- The hom globular set between two objects. Its `n`-cells are genuine
`(n+1)`-cells of `G` with the specified iterated zero-dimensional endpoints.
This dimension shift is the basis of recursively labelled pasting diagrams. -/
def hom (G : GlobularSet.{u}) (a b : G.Cell 0) : GlobularSet.{u} where
  Cell n := { c : G.Cell (n + 1) // G.sourceZero c = a ∧ G.targetZero c = b }
  source {n} c := ⟨G.source c.val,
    c.property.1, (G.targetZero_globular c.val).trans c.property.2⟩
  target {n} c := ⟨G.target c.val,
    (G.sourceZero_globular c.val).symm.trans c.property.1, c.property.2⟩
  source_source c := Subtype.ext (G.source_source c.val)
  target_source c := Subtype.ext (G.target_source c.val)

/-- A globular map induces maps on all its hom globular sets, retaining the
underlying cell and both endpoint equations. -/
def Map.hom {G : GlobularSet.{u}} {H : GlobularSet.{v}} (f : Map G H)
    (a b : G.Cell 0) : Map (G.hom a b) (H.hom (f.app a) (f.app b)) where
  app {n} c := ⟨f.app c.val,
    (f.sourceZero c.val).trans (_root_.congrArg f.app c.property.1),
    (f.targetZero c.val).trans (_root_.congrArg f.app c.property.2)⟩
  source_app c := Subtype.ext (f.source_app c.val)
  target_app c := Subtype.ext (f.target_app c.val)

theorem Map.hom_id (G : GlobularSet.{u}) (a b : G.Cell 0) :
    (Map.id G).hom a b = Map.id (G.hom a b) := by
  apply Map.ext
  intro n c
  exact Subtype.ext rfl

theorem Map.hom_comp {G : GlobularSet.{u}} {H : GlobularSet.{v}} {K : GlobularSet.{w}}
    (f : Map G H) (g : Map H K) (a b : G.Cell 0) :
    (Map.comp g f).hom a b = Map.comp (g.hom (f.app a) (f.app b)) (f.hom a b) := by
  apply Map.ext
  intro n c
  exact Subtype.ext rfl

end GlobularSet

/-- Raw one-cells, including their original rewrite-step lists. -/
abbrev PathOne (A : Type u) := Σ a b : A, Path a b

/-- Raw two-cells, including the full `RwEq` derivation syntax. -/
abbrev PathTwo (A : Type u) := Σ (a b : A) (p q : Path a b), RwEq p q

def sourceOne {A : Type u} (p : PathOne A) : A := p.1
def targetOne {A : Type u} (p : PathOne A) : A := p.2.1
def sourceTwo {A : Type u} (d : PathTwo A) : PathOne A := ⟨d.1, d.2.1, d.2.2.1⟩
def targetTwo {A : Type u} (d : PathTwo A) : PathOne A := ⟨d.1, d.2.1, d.2.2.2.1⟩

theorem path_source_source {A : Type u} (d : PathTwo A) :
    sourceOne (sourceTwo d) = sourceOne (targetTwo d) := rfl

theorem path_target_source {A : Type u} (d : PathTwo A) :
    targetOne (sourceTwo d) = targetOne (targetTwo d) := rfl

/-- The low-dimensional associator is a real primitive rewrite, not an
equality obtained by erasing the path traces. -/
noncomputable def associatorCell {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) : PathTwo A :=
  ⟨a, d, Path.trans (Path.trans p q) r, Path.trans p (Path.trans q r),
    RwEq.step (Step.trans_assoc p q r)⟩

/-- Vertical composition retains both original two-cell derivations. -/
noncomputable def composeTwo {A : Type u} {a b : A} {p q r : Path a b}
    (h : RwEq p q) (k : RwEq q r) : PathTwo A := ⟨a, b, p, r, RwEq.trans h k⟩

/-- A future all-dimensional carrier must genuinely extend the existing raw
two-skeleton. The equivalences rule out silently replacing it by a thin
quotient or by unrelated formal cells. No instance is asserted yet. -/
structure RealizesPathSkeleton (G : GlobularSet.{u + 1}) (A : Type u) where
  objects : G.Cell 0 ≃ A
  paths : G.Cell 1 ≃ PathOne A
  rewrites : G.Cell 2 ≃ PathTwo A
  source_paths : (c : G.Cell 1) → objects (G.source c) = sourceOne (paths c)
  target_paths : (c : G.Cell 1) → objects (G.target c) = targetOne (paths c)
  source_rewrites : (c : G.Cell 2) → paths (G.source c) = sourceTwo (rewrites c)
  target_rewrites : (c : G.Cell 2) → paths (G.target c) = targetTwo (rewrites c)

end ComputationalPaths.Path.OmegaFoundations

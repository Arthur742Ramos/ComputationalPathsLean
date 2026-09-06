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

/-- The pointwise pullback retains both original cells and their matching
equation. It introduces no new cells or identifications. -/
def pullback {G H K : GlobularSet.{u}} (f : Map G K) (g : Map H K) : GlobularSet.{u} where
  Cell n := { p : G.Cell n × H.Cell n // f.app p.1 = g.app p.2 }
  source p := ⟨⟨G.source p.val.1, H.source p.val.2⟩,
    (f.source_app p.val.1).symm.trans
      ((_root_.congrArg K.source p.property).trans (g.source_app p.val.2))⟩
  target p := ⟨⟨G.target p.val.1, H.target p.val.2⟩,
    (f.target_app p.val.1).symm.trans
      ((_root_.congrArg K.target p.property).trans (g.target_app p.val.2))⟩
  source_source p := Subtype.ext (Prod.ext (G.source_source p.val.1) (H.source_source p.val.2))
  target_source p := Subtype.ext (Prod.ext (G.target_source p.val.1) (H.target_source p.val.2))

def pullbackFst {G H K : GlobularSet.{u}} (f : Map G K) (g : Map H K) :
    Map (pullback f g) G where
  app p := p.val.1
  source_app _ := rfl
  target_app _ := rfl

def pullbackSnd {G H K : GlobularSet.{u}} (f : Map G K) (g : Map H K) :
    Map (pullback f g) H where
  app p := p.val.2
  source_app _ := rfl
  target_app _ := rfl

theorem pullback_condition {G H K : GlobularSet.{u}} (f : Map G K) (g : Map H K) :
    Map.comp f (pullbackFst f g) = Map.comp g (pullbackSnd f g) := by
  apply Map.ext
  intro n p
  exact p.property

/-- Lift a commuting globular cone without making any choices. -/
def pullbackLift {G H K X : GlobularSet.{u}} (f : Map G K) (g : Map H K)
    (p : Map X G) (q : Map X H) (h : Map.comp f p = Map.comp g q) :
    Map X (pullback f g) where
  app x := ⟨⟨p.app x, q.app x⟩, _root_.congrArg (fun k : Map X K => k.app x) h⟩
  source_app x := Subtype.ext (Prod.ext (p.source_app x) (q.source_app x))
  target_app x := Subtype.ext (Prod.ext (p.target_app x) (q.target_app x))

theorem pullbackLift_fst {G H K X : GlobularSet.{u}} (f : Map G K) (g : Map H K)
    (p : Map X G) (q : Map X H) (h : Map.comp f p = Map.comp g q) :
    Map.comp (pullbackFst f g) (pullbackLift f g p q h) = p := by
  apply Map.ext
  intro n x
  rfl

theorem pullbackLift_snd {G H K X : GlobularSet.{u}} (f : Map G K) (g : Map H K)
    (p : Map X G) (q : Map X H) (h : Map.comp f p = Map.comp g q) :
    Map.comp (pullbackSnd f g) (pullbackLift f g p q h) = q := by
  apply Map.ext
  intro n x
  rfl

theorem pullback_ext {G H K X : GlobularSet.{u}} (f : Map G K) (g : Map H K)
    (p q : Map X (pullback f g))
    (h₁ : Map.comp (pullbackFst f g) p = Map.comp (pullbackFst f g) q)
    (h₂ : Map.comp (pullbackSnd f g) p = Map.comp (pullbackSnd f g) q) : p = q := by
  apply Map.ext
  intro n x
  apply Subtype.ext
  exact Prod.ext (_root_.congrArg (fun k : Map X G => k.app x) h₁)
    (_root_.congrArg (fun k : Map X H => k.app x) h₂)

theorem pullback_universal {G H K X : GlobularSet.{u}} (f : Map G K) (g : Map H K)
    (p : Map X G) (q : Map X H) (h : Map.comp f p = Map.comp g q) :
    ∃! d : Map X (pullback f g),
      Map.comp (pullbackFst f g) d = p ∧ Map.comp (pullbackSnd f g) d = q := by
  refine ⟨pullbackLift f g p q h, ⟨pullbackLift_fst f g p q h, pullbackLift_snd f g p q h⟩, ?_⟩
  intro d hd
  exact pullback_ext f g d _ (hd.1.trans (pullbackLift_fst f g p q h).symm)
    (hd.2.trans (pullbackLift_snd f g p q h).symm)

theorem Map.parallel {G : GlobularSet.{u}} {H : GlobularSet.{v}} (f : Map G H)
    {n : Nat} {x y : G.Cell n} (h : Parallel G n x y) : Parallel H n (f.app x) (f.app y) := by
  cases h with
  | objects => exact .objects _ _
  | cells hs ht =>
    exact .cells ((f.source_app _).trans ((_root_.congrArg f.app hs).trans (f.source_app _).symm))
      ((f.target_app _).trans ((_root_.congrArg f.app ht).trans (f.target_app _).symm))

/-- Forget the object level, retaining all higher cells and adjacent maps. -/
def shift (G : GlobularSet.{u}) : GlobularSet.{u} where
  Cell n := G.Cell (n + 1)
  source := G.source
  target := G.target
  source_source := G.source_source
  target_source := G.target_source

def Map.shift {G : GlobularSet.{u}} {H : GlobularSet.{v}} (f : Map G H) : Map G.shift H.shift where
  app := f.app
  source_app := f.source_app
  target_app := f.target_app

def constant (X : Type u) : GlobularSet.{u} where
  Cell _ := X
  source := id
  target := id
  source_source _ := rfl
  target_source _ := rfl

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

namespace GlobularSet

/-- The hom set is a boundary-defined sub-globular set of the shifted tower. -/
def homInclusion (G : GlobularSet.{u}) (a b : G.Cell 0) : Map (G.hom a b) G.shift where
  app := Subtype.val
  source_app _ := rfl
  target_app _ := rfl

/-- The hom of a matched-cell pullback maps to the pullback of the two
fixed-endpoint homs over the shifted common target. Using the shifted target
avoids identifying endpoint fibres that are only propositionally equal. -/
def pullbackHomForward {G H K : GlobularSet.{u}} (f : Map G K) (g : Map H K)
    (a b : (pullback f g).Cell 0) :
    Map ((pullback f g).hom a b)
      (pullback (Map.comp f.shift (homInclusion G a.val.1 b.val.1))
        (Map.comp g.shift (homInclusion H a.val.2 b.val.2))) :=
  pullbackLift _ _ ((pullbackFst f g).hom a b) ((pullbackSnd f g).hom a b) (by
    apply Map.ext
    intro n c
    exact c.val.property)

/-- Reassemble matched hom cells, retaining both original cells and all four
endpoint equations. This is the inverse needed for dimension recursion. -/
def pullbackHomBackward {G H K : GlobularSet.{u}} (f : Map G K) (g : Map H K)
    (a b : (pullback f g).Cell 0) :
    Map (pullback (Map.comp f.shift (homInclusion G a.val.1 b.val.1))
        (Map.comp g.shift (homInclusion H a.val.2 b.val.2)))
      ((pullback f g).hom a b) where
  app c := by
    let r : (pullback f g).Cell _ := ⟨⟨c.val.1.val, c.val.2.val⟩, c.property⟩
    refine ⟨r, ?_, ?_⟩
    · apply Subtype.ext
      exact Prod.ext
        (((pullbackFst f g).sourceZero r).symm.trans c.val.1.property.1)
        (((pullbackSnd f g).sourceZero r).symm.trans c.val.2.property.1)
    · apply Subtype.ext
      exact Prod.ext
        (((pullbackFst f g).targetZero r).symm.trans c.val.1.property.2)
        (((pullbackSnd f g).targetZero r).symm.trans c.val.2.property.2)
  source_app c := Subtype.ext (Subtype.ext rfl)
  target_app c := Subtype.ext (Subtype.ext rfl)

theorem pullbackHom_backward_forward {G H K : GlobularSet.{u}}
    (f : Map G K) (g : Map H K) (a b : (pullback f g).Cell 0) :
    Map.comp (pullbackHomBackward f g a b) (pullbackHomForward f g a b) =
      Map.id ((pullback f g).hom a b) := by
  apply Map.ext
  intro n c
  exact Subtype.ext (Subtype.ext rfl)

theorem pullbackHom_forward_backward {G H K : GlobularSet.{u}}
    (f : Map G K) (g : Map H K) (a b : (pullback f g).Cell 0) :
    Map.comp (pullbackHomForward f g a b) (pullbackHomBackward f g a b) =
      Map.id (pullback (Map.comp f.shift (homInclusion G a.val.1 b.val.1))
        (Map.comp g.shift (homInclusion H a.val.2 b.val.2))) := by
  apply Map.ext
  intro n c
  exact Subtype.ext (Prod.ext (Subtype.ext rfl) (Subtype.ext rfl))

theorem pullbackHomBackward_fst {G H K : GlobularSet.{u}}
    (f : Map G K) (g : Map H K) (a b : (pullback f g).Cell 0) :
    Map.comp ((pullbackFst f g).hom a b) (pullbackHomBackward f g a b) =
      pullbackFst (Map.comp f.shift (homInclusion G a.val.1 b.val.1))
        (Map.comp g.shift (homInclusion H a.val.2 b.val.2)) := by
  apply Map.ext
  intro n c
  exact Subtype.ext rfl

theorem pullbackHomBackward_snd {G H K : GlobularSet.{u}}
    (f : Map G K) (g : Map H K) (a b : (pullback f g).Cell 0) :
    Map.comp ((pullbackSnd f g).hom a b) (pullbackHomBackward f g a b) =
      pullbackSnd (Map.comp f.shift (homInclusion G a.val.1 b.val.1))
        (Map.comp g.shift (homInclusion H a.val.2 b.val.2)) := by
  apply Map.ext
  intro n c
  exact Subtype.ext rfl

/-- The fixed zero-dimensional endpoints are globular maps on the shifted
tower, so they can be used to restrict every higher-cut operation to homs. -/
def sourceZeroMap (G : GlobularSet.{u}) : Map G.shift (constant (G.Cell 0)) where
  app := G.sourceZero
  source_app _ := rfl
  target_app c := G.sourceZero_globular c

def targetZeroMap (G : GlobularSet.{u}) : Map G.shift (constant (G.Cell 0)) where
  app := G.targetZero
  source_app c := (G.targetZero_globular c).symm
  target_app _ := rfl

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

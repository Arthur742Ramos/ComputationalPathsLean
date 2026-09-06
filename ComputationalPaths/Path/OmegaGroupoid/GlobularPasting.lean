import ComputationalPaths.Path.OmegaGroupoid.GlobularFoundations
import Mathlib.CategoryTheory.Functor.Basic

/-!
# Recursively labelled globular pasting diagrams

Objects label dimension zero. In dimension `n+1`, a diagram is a composable
chain of `n`-diagrams in hom globular sets. The carrier and adjacent boundary
maps are defined by genuine dimension recursion. This file does not yet
construct monad multiplication or claim the free strict-category property.
-/

namespace ComputationalPaths.Path.OmegaFoundations

universe u v w

/-- A composable, endpoint-indexed finite chain. -/
inductive Chain {O : Type u} (E : O → O → Type v) : O → O → Type (max u v) where
  | nil (x : O) : Chain E x x
  | cons {x y z : O} : E x y → Chain E y z → Chain E x z

namespace Chain

variable {O : Type u} {E : O → O → Type v} {F : O → O → Type w}

def append {x y z : O} (p : Chain E x y) (q : Chain E y z) : Chain E x z :=
  match p with
  | .nil _ => q
  | .cons e p => .cons e (append p q)

def map (f : {x y : O} → E x y → F x y) {x y : O} : Chain E x y → Chain F x y
  | .nil x => .nil x
  | .cons e p => .cons (f e) (map f p)

theorem map_map {D : O → O → Type u}
    (f : {x y : O} → E x y → F x y) (g : {x y : O} → F x y → D x y)
    {x y : O} (p : Chain E x y) : (p.map f).map g = p.map (fun e => g (f e)) := by
  induction p with
  | nil => rfl
  | cons e p ih => exact _root_.congrArg (Chain.cons (g (f e))) ih

theorem map_congr (f g : {x y : O} → E x y → F x y)
    (h : ∀ {x y} (e : E x y), f e = g e) {x y : O} (p : Chain E x y) :
    p.map f = p.map g := by
  induction p with
  | nil => rfl
  | cons e p ih => exact _root_.congrArg₂ Chain.cons (h e) ih

theorem map_id {x y : O} (p : Chain E x y) : p.map (fun e => e) = p := by
  induction p with
  | nil => rfl
  | cons e p ih => exact _root_.congrArg (Chain.cons e) ih

theorem append_assoc {x y z t : O} (p : Chain E x y) (q : Chain E y z) (r : Chain E z t) :
    (p.append q).append r = p.append (q.append r) := by
  induction p with
  | nil => rfl
  | cons e p ih => exact _root_.congrArg (Chain.cons e) (ih q)

theorem map_append (f : {x y : O} → E x y → F x y) {x y z : O}
    (p : Chain E x y) (q : Chain E y z) :
    (p.append q).map f = (p.map f).append (q.map f) := by
  induction p with
  | nil => rfl
  | cons e p ih => exact _root_.congrArg (Chain.cons (f e)) (ih q)

end Chain

namespace Chain

/-- Pair labels only when their images in a common boundary chain agree.
The equality of chains supplies both matching intermediate vertices and
the individual boundary equalities required by the label operation. -/
noncomputable def zipOver {O : Type u} {E F D R : O → O → Type v}
    (s : {x y : O} → E x y → D x y)
    (t : {x y : O} → F x y → D x y)
    (op : {x y : O} → (e : E x y) → (f : F x y) → s e = t f → R x y)
    {x y : O} (p : Chain E x y) (q : Chain F x y)
    (h : p.map s = q.map t) : Chain R x y := by
  induction p with
  | nil x =>
    cases q with
    | nil => exact .nil x
    | cons f q => cases h
  | @cons x z y e p ih =>
    cases q with
    | nil => cases h
    | @cons _ z' _ f q =>
      simp only [map] at h
      have hi : z = z' ∧ HEq (s e) (t f) ∧ HEq (p.map s) (q.map t) := by
        injection h with hx hz hy he hp
        exact ⟨hz, he, hp⟩
      have hz := hi.1
      have he := hi.2.1
      have hp := hi.2.2
      cases hz
      have he' := eq_of_heq he
      have hp' := eq_of_heq hp
      exact .cons (op e f he') (ih q hp')

theorem map_zipOver_left {O : Type u} {E F D R B : O → O → Type v}
    (s : {x y : O} → E x y → D x y)
    (t : {x y : O} → F x y → D x y)
    (op : {x y : O} → (e : E x y) → (f : F x y) → s e = t f → R x y)
    (b : {x y : O} → R x y → B x y) (l : {x y : O} → E x y → B x y)
    (law : ∀ {x y} (e : E x y) (f : F x y) (h : s e = t f), b (op e f h) = l e)
    {x y : O} (p : Chain E x y) (q : Chain F x y) (h : p.map s = q.map t) :
    (zipOver s t op p q h).map b = p.map l := by
  induction p with
  | nil x =>
    cases q with
    | nil => rfl
    | cons f q => cases h
  | @cons x z y e p ih =>
    cases q with
    | nil => cases h
    | @cons _ z' _ f q =>
      have hc := h
      simp only [map] at hc
      injection hc with hx hz hy he hp
      cases hz
      have he' := eq_of_heq he
      have hp' := eq_of_heq hp
      change Chain.cons (b (op e f he')) ((zipOver s t op p q hp').map b) = Chain.cons (l e) (p.map l)
      exact _root_.congrArg₂ Chain.cons (law e f he') (ih q hp')

theorem map_zipOver_right {O : Type u} {E F D R B : O → O → Type v}
    (s : {x y : O} → E x y → D x y)
    (t : {x y : O} → F x y → D x y)
    (op : {x y : O} → (e : E x y) → (f : F x y) → s e = t f → R x y)
    (b : {x y : O} → R x y → B x y) (r : {x y : O} → F x y → B x y)
    (law : ∀ {x y} (e : E x y) (f : F x y) (h : s e = t f), b (op e f h) = r f)
    {x y : O} (p : Chain E x y) (q : Chain F x y) (h : p.map s = q.map t) :
    (zipOver s t op p q h).map b = q.map r := by
  induction p with
  | nil x =>
    cases q with
    | nil => rfl
    | cons f q => cases h
  | @cons x z y e p ih =>
    cases q with
    | nil => cases h
    | @cons _ z' _ f q =>
      have hc := h
      simp only [map] at hc
      injection hc with hx hz hy he hp
      cases hz
      have he' := eq_of_heq he
      have hp' := eq_of_heq hp
      change Chain.cons (b (op e f he')) ((zipOver s t op p q hp').map b) = Chain.cons (r f) (q.map r)
      exact _root_.congrArg₂ Chain.cons (law e f he') (ih q hp')

/-- Alignment distributes over concatenation; this is the chain-level
interchange ingredient for horizontal and adjacent-boundary composition. -/
theorem zipOver_append {O : Type u} {E F D R : O → O → Type v}
    (s : {x y : O} → E x y → D x y)
    (t : {x y : O} → F x y → D x y)
    (op : {x y : O} → (e : E x y) → (f : F x y) → s e = t f → R x y)
    {x y z : O} (p : Chain E x y) (q : Chain F x y) (h : p.map s = q.map t)
    (p' : Chain E y z) (q' : Chain F y z) (h' : p'.map s = q'.map t) :
    zipOver s t op (p.append p') (q.append q')
      ((map_append s p p').trans ((_root_.congrArg₂ Chain.append h h').trans
        (map_append t q q').symm)) =
      (zipOver s t op p q h).append (zipOver s t op p' q' h') := by
  induction p with
  | nil x =>
    cases q with
    | nil => rfl
    | cons f q => cases h
  | @cons x v y e p ih =>
    cases q with
    | nil => cases h
    | @cons _ v' _ f q =>
      have hc := h
      simp only [map] at hc
      injection hc with hx hv hy he hp
      cases hv
      have he' := eq_of_heq he
      have hp' := eq_of_heq hp
      exact _root_.congrArg (Chain.cons (op e f he')) (ih q hp' p' q' h')

variable {O : Type u} {E : O → O → Type v} {F : O → O → Type w}

def single {x y : O} (e : E x y) : Chain E x y := .cons e (.nil y)

theorem append_nil {x y : O} (p : Chain E x y) : p.append (.nil y) = p := by
  induction p with
  | nil => rfl
  | cons e p ih => exact _root_.congrArg (Chain.cons e) ih

/-- Endpoint-preserving substitution of a chain for each edge. -/
def bind (f : {x y : O} → E x y → Chain F x y) {x y : O} :
    Chain E x y → Chain F x y
  | .nil x => .nil x
  | .cons e p => (f e).append (bind f p)

theorem bind_append (f : {x y : O} → E x y → Chain F x y)
    {x y z : O} (p : Chain E x y) (q : Chain E y z) :
    (p.append q).bind f = (p.bind f).append (q.bind f) := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    exact (_root_.congrArg (Chain.append (f e)) (ih q)).trans (Chain.append_assoc _ _ _).symm

theorem bind_single (f : {x y : O} → E x y → Chain F x y)
    {x y : O} (e : E x y) : (single e).bind f = f e := append_nil (f e)

theorem bind_id {x y : O} (p : Chain E x y) : p.bind (fun e => single e) = p := by
  induction p with
  | nil => rfl
  | cons e p ih => exact _root_.congrArg (Chain.cons e) ih

theorem bind_assoc {D : O → O → Type u}
    (f : {x y : O} → E x y → Chain F x y)
    (g : {x y : O} → F x y → Chain D x y) {x y : O} (p : Chain E x y) :
    (p.bind f).bind g = p.bind (fun e => (f e).bind g) := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    exact (bind_append g (f e) (p.bind f)).trans
      (_root_.congrArg (Chain.append ((f e).bind g)) ih)

end Chain

namespace Chain

variable {O : Type u} {P : Type v}

/-- Relabel both vertices and edges of a composable chain. -/
def mapAlong {E : O → O → Type u} {F : P → P → Type v}
    (f : O → P) (e : {x y : O} → E x y → F (f x) (f y))
    {x y : O} : Chain E x y → Chain F (f x) (f y)
  | .nil x => .nil (f x)
  | .cons a p => .cons (e a) (mapAlong f e p)

theorem mapAlong_natural {E D : O → O → Type u} {F K : P → P → Type v}
    (f : O → P) (a : {x y : O} → E x y → D x y)
    (b : {x y : P} → F x y → K x y)
    (e : {x y : O} → E x y → F (f x) (f y))
    (d : {x y : O} → D x y → K (f x) (f y))
    (h : ∀ {x y} (t : E x y), b (e t) = d (a t))
    {x y : O} (p : Chain E x y) :
    (p.mapAlong f e).map b = (p.map a).mapAlong f d := by
  induction p with
  | nil => rfl
  | cons t p ih => exact _root_.congrArg₂ Chain.cons (h t) ih

theorem mapAlong_congr {E : O → O → Type u} {F : P → P → Type v}
    (f : O → P) (e d : {x y : O} → E x y → F (f x) (f y))
    (h : ∀ {x y} (t : E x y), e t = d t) {x y : O} (p : Chain E x y) :
    p.mapAlong f e = p.mapAlong f d := by
  induction p with
  | nil => rfl
  | cons t p ih => exact _root_.congrArg₂ Chain.cons (h t) ih

theorem mapAlong_id {E : O → O → Type u} {x y : O} (p : Chain E x y) :
    p.mapAlong (fun x => x) (fun e => e) = p := by
  induction p with
  | nil => rfl
  | cons t p ih => exact _root_.congrArg (Chain.cons t) ih

theorem mapAlong_append {E : O → O → Type u} {F : P → P → Type v}
    (f : O → P) (e : {x y : O} → E x y → F (f x) (f y))
    {x y z : O} (p : Chain E x y) (q : Chain E y z) :
    (p.append q).mapAlong f e = (p.mapAlong f e).append (q.mapAlong f e) := by
  induction p with
  | nil => rfl
  | cons t p ih => exact _root_.congrArg (Chain.cons (e t)) (ih q)

theorem mapAlong_comp {Q : Type w} {E : O → O → Type u}
    {F : P → P → Type v} {D : Q → Q → Type w}
    (f : O → P) (g : P → Q)
    (e : {x y : O} → E x y → F (f x) (f y))
    (d : {x y : P} → F x y → D (g x) (g y)) {x y : O} (p : Chain E x y) :
    (p.mapAlong f e).mapAlong g d = p.mapAlong (fun x => g (f x)) (fun t => d (e t)) := by
  induction p with
  | nil => rfl
  | cons t p ih => exact _root_.congrArg (Chain.cons (d (e t))) ih

end Chain

/-- The dimension-recursive labelled pasting carrier. -/
def Pasting : Nat → GlobularSet.{u} → Type u
  | 0, G => G.Cell 0
  | n + 1, G => Σ (a b : G.Cell 0), Chain (fun a b => Pasting n (G.hom a b)) a b

namespace Pasting

/-- A single original cell regarded as a labelled pasting diagram. At every
successor dimension the lower label lies in the appropriate hom globular set. -/
def singleton : {n : Nat} → {G : GlobularSet.{u}} → G.Cell n → Pasting n G
  | 0, _, a => a
  | n + 1, G, c =>
      ⟨G.sourceZero c, G.targetZero c,
        Chain.single (singleton (n := n) (G := G.hom (G.sourceZero c) (G.targetZero c))
          ⟨c, rfl, rfl⟩)⟩

/-- Recover an original cell only from a recursively singleton diagram.
Composite and identity diagrams do not pretend to be generating cells. -/
def atom? : {n : Nat} → {G : GlobularSet.{u}} → Pasting n G → Option (G.Cell n)
  | 0, _, a => some a
  | n + 1, G, ⟨a, b, .cons d (.nil _)⟩ =>
      (atom? (n := n) (G := G.hom a b) d).map Subtype.val
  | _ + 1, _, ⟨_, _, .nil _⟩ => none
  | _ + 1, _, ⟨_, _, .cons _ (.cons _ _)⟩ => none

theorem atom_singleton {n : Nat} (G : GlobularSet.{u}) (c : G.Cell n) :
    atom? (singleton c) = some c := by
  induction n generalizing G with
  | zero => rfl
  | succ n ih =>
    change (atom? (singleton (G := G.hom (G.sourceZero c) (G.targetZero c))
      (⟨c, rfl, rfl⟩ : (G.hom (G.sourceZero c) (G.targetZero c)).Cell n))).map Subtype.val = some c
    exact _root_.congrArg (Option.map Subtype.val)
      (ih (G.hom (G.sourceZero c) (G.targetZero c)) ⟨c, rfl, rfl⟩)

/-- The proposed unit retains every original cell, in every dimension. -/
theorem singleton_injective {n : Nat} (G : GlobularSet.{u}) {c d : G.Cell n}
    (h : singleton c = singleton d) : c = d := by
  have he := _root_.congrArg (atom? (G := G)) h
  rw [atom_singleton, atom_singleton] at he
  exact Option.some.inj he

/-- Dimension-recursive relabelling by a globular map. -/
def map : {n : Nat} → {G H : GlobularSet.{u}} → GlobularSet.Map G H → Pasting n G → Pasting n H
  | 0, _, _, f, a => f.app a
  | n + 1, _, _, f, ⟨a, b, p⟩ =>
      ⟨f.app a, f.app b, p.mapAlong f.app (fun {x y} d => map (n := n) (f.hom x y) d)⟩

theorem map_id {n : Nat} (G : GlobularSet.{u}) (c : Pasting n G) :
    map (GlobularSet.Map.id G) c = c := by
  induction n generalizing G with
  | zero => rfl
  | succ n ih =>
    rcases c with ⟨a, b, p⟩
    apply _root_.congrArg (fun q => (⟨a, b, q⟩ : Pasting (n + 1) G))
    refine (Chain.mapAlong_congr (fun x => x) _ (fun d => d) ?_ p).trans (Chain.mapAlong_id p)
    intro x y d
    simp only [GlobularSet.Map.hom_id]
    exact ih (G.hom x y) d

theorem map_comp {n : Nat} {G H K : GlobularSet.{u}}
    (f : GlobularSet.Map G H) (g : GlobularSet.Map H K) (c : Pasting n G) :
    map g (map f c) = map (GlobularSet.Map.comp g f) c := by
  induction n generalizing G H K with
  | zero => rfl
  | succ n ih =>
    rcases c with ⟨a, b, p⟩
    apply _root_.congrArg (fun q => (⟨g.app (f.app a), g.app (f.app b), q⟩ : Pasting (n + 1) K))
    refine (Chain.mapAlong_comp _ _ _ _ p).trans (Chain.mapAlong_congr _ _ _ ?_ p)
    intro x y d
    simp only [GlobularSet.Map.hom_comp]
    exact ih (f.hom x y) (g.hom (f.app x) (f.app y)) d

def source : {n : Nat} → {G : GlobularSet.{u}} → Pasting (n + 1) G → Pasting n G
  | 0, _, ⟨a, _, _⟩ => a
  | n + 1, G, ⟨a, b, p⟩ =>
      ⟨a, b, p.map (fun {x y} d => source (n := n) (G := G.hom x y) d)⟩

def target : {n : Nat} → {G : GlobularSet.{u}} → Pasting (n + 1) G → Pasting n G
  | 0, _, ⟨_, b, _⟩ => b
  | n + 1, G, ⟨a, b, p⟩ =>
      ⟨a, b, p.map (fun {x y} d => target (n := n) (G := G.hom x y) d)⟩

theorem singleton_of_hom {n : Nat} (G : GlobularSet.{u})
    {a b : G.Cell 0} (c : (G.hom a b).Cell n) :
    (⟨a, b, Chain.single (singleton c)⟩ : Pasting (n + 1) G) = singleton c.val := by
  rcases c with ⟨c, ha, hb⟩
  cases ha
  cases hb
  rfl

theorem map_singleton {n : Nat} {G H : GlobularSet.{u}} (f : GlobularSet.Map G H)
    (c : G.Cell n) : map f (singleton c) = singleton (f.app c) := by
  induction n generalizing G H with
  | zero => rfl
  | succ n ih =>
    let d : (G.hom (G.sourceZero c) (G.targetZero c)).Cell n := ⟨c, rfl, rfl⟩
    change (⟨f.app (G.sourceZero c), f.app (G.targetZero c),
      Chain.single (map (f.hom _ _) (singleton d))⟩ : Pasting (n + 1) H) = _
    exact (_root_.congrArg (fun q => (⟨f.app (G.sourceZero c), f.app (G.targetZero c),
      Chain.single q⟩ : Pasting (n + 1) H)) (ih (f.hom _ _) d)).trans
        (singleton_of_hom H ((f.hom _ _).app d))

theorem source_singleton {n : Nat} (G : GlobularSet.{u}) (c : G.Cell (n + 1)) :
    source (singleton c) = singleton (G.source c) := by
  induction n generalizing G with
  | zero => rfl
  | succ n ih =>
    let H := G.hom (G.sourceZero c) (G.targetZero c)
    let d : H.Cell (n + 1) := ⟨c, rfl, rfl⟩
    change (⟨G.sourceZero c, G.targetZero c,
      Chain.single (source (singleton d))⟩ : Pasting (n + 1) G) = _
    exact (_root_.congrArg (fun q => (⟨G.sourceZero c, G.targetZero c,
      Chain.single q⟩ : Pasting (n + 1) G)) (ih H d)).trans
        (singleton_of_hom G (H.source d))

theorem target_singleton {n : Nat} (G : GlobularSet.{u}) (c : G.Cell (n + 1)) :
    target (singleton c) = singleton (G.target c) := by
  induction n generalizing G with
  | zero => rfl
  | succ n ih =>
    let H := G.hom (G.sourceZero c) (G.targetZero c)
    let d : H.Cell (n + 1) := ⟨c, rfl, rfl⟩
    change (⟨G.sourceZero c, G.targetZero c,
      Chain.single (target (singleton d))⟩ : Pasting (n + 1) G) = _
    exact (_root_.congrArg (fun q => (⟨G.sourceZero c, G.targetZero c,
      Chain.single q⟩ : Pasting (n + 1) G)) (ih H d)).trans
        (singleton_of_hom G (H.target d))

theorem source_map {n : Nat} {G H : GlobularSet.{u}} (f : GlobularSet.Map G H)
    (c : Pasting (n + 1) G) : source (map f c) = map f (source c) := by
  induction n generalizing G H with
  | zero => rcases c with ⟨a, b, p⟩; rfl
  | succ n ih =>
    rcases c with ⟨a, b, p⟩
    apply _root_.congrArg (fun q => (⟨f.app a, f.app b, q⟩ : Pasting (n + 1) H))
    exact Chain.mapAlong_natural _ _ _ _ _ (fun {x y} d => ih (f.hom x y) d) p

theorem target_map {n : Nat} {G H : GlobularSet.{u}} (f : GlobularSet.Map G H)
    (c : Pasting (n + 1) G) : target (map f c) = map f (target c) := by
  induction n generalizing G H with
  | zero => rcases c with ⟨a, b, p⟩; rfl
  | succ n ih =>
    rcases c with ⟨a, b, p⟩
    apply _root_.congrArg (fun q => (⟨f.app a, f.app b, q⟩ : Pasting (n + 1) H))
    exact Chain.mapAlong_natural _ _ _ _ _ (fun {x y} d => ih (f.hom x y) d) p

theorem source_source {n : Nat} (G : GlobularSet.{u}) (c : Pasting (n + 2) G) :
    source (source c) = source (target c) := by
  induction n generalizing G with
  | zero => rcases c with ⟨a, b, p⟩; rfl
  | succ n ih =>
    rcases c with ⟨a, b, p⟩
    apply _root_.congrArg (fun q => (⟨a, b, q⟩ : Pasting (n + 1) G))
    simp only [Chain.map_map]
    apply Chain.map_congr
    intro x y d
    exact ih (G.hom x y) d

theorem target_source {n : Nat} (G : GlobularSet.{u}) (c : Pasting (n + 2) G) :
    target (source c) = target (target c) := by
  induction n generalizing G with
  | zero => rcases c with ⟨a, b, p⟩; rfl
  | succ n ih =>
    rcases c with ⟨a, b, p⟩
    apply _root_.congrArg (fun q => (⟨a, b, q⟩ : Pasting (n + 1) G))
    simp only [Chain.map_map]
    apply Chain.map_congr
    intro x y d
    exact ih (G.hom x y) d

/-- All-dimensional pasting diagrams with checked globular boundaries. -/
def globular (G : GlobularSet.{u}) : GlobularSet.{u} where
  Cell n := Pasting n G
  source := source
  target := target
  source_source := source_source G
  target_source := target_source G

def mapGlobular {G H : GlobularSet.{u}} (f : GlobularSet.Map G H) :
    GlobularSet.Map (globular G) (globular H) where
  app := map f
  source_app := source_map f
  target_app := target_map f

/-- The generating-cell inclusion is an injective globular map in all dimensions. -/
def singletonGlobular (G : GlobularSet.{u}) : GlobularSet.Map G (globular G) where
  app := singleton
  source_app := source_singleton G
  target_app := target_singleton G

theorem singleton_natural {G H : GlobularSet.{u}} (f : GlobularSet.Map G H) :
    GlobularSet.Map.comp (mapGlobular f) (singletonGlobular G) =
      GlobularSet.Map.comp (singletonGlobular H) f := by
  apply GlobularSet.Map.ext
  intro n c
  exact map_singleton f c

/-- The lawful endofunctor of recursively labelled pasting diagrams.
Monad unit/multiplication and the universal property are separate obligations. -/
def pastingFunctor : CategoryTheory.Functor GlobularSet.{u} GlobularSet.{u} where
  obj := globular
  map := mapGlobular
  map_id G := by
    apply GlobularSet.Map.ext
    intro n c
    exact map_id G c
  map_comp f g := by
    apply GlobularSet.Map.ext
    intro n c
    exact (map_comp f g c).symm

/-- Identity pastings in every dimension: the empty chain on an object,
and recursively the identity on each label in higher dimensions. -/
def identity : {n : Nat} → {G : GlobularSet.{u}} → Pasting n G → Pasting (n + 1) G
  | 0, _, a => ⟨a, a, .nil a⟩
  | n + 1, G, ⟨a, b, p⟩ =>
      ⟨a, b, p.map (fun {x y} d => identity (n := n) (G := G.hom x y) d)⟩

theorem source_identity {n : Nat} (G : GlobularSet.{u}) (c : Pasting n G) :
    source (identity c) = c := by
  induction n generalizing G with
  | zero => rfl
  | succ n ih =>
    rcases c with ⟨a, b, p⟩
    apply _root_.congrArg (fun q => (⟨a, b, q⟩ : Pasting (n + 1) G))
    exact (Chain.map_map _ _ p).trans
      ((Chain.map_congr _ (fun d => d) (fun {x y} d => ih (G.hom x y) d) p).trans (Chain.map_id p))

theorem target_identity {n : Nat} (G : GlobularSet.{u}) (c : Pasting n G) :
    target (identity c) = c := by
  induction n generalizing G with
  | zero => rfl
  | succ n ih =>
    rcases c with ⟨a, b, p⟩
    apply _root_.congrArg (fun q => (⟨a, b, q⟩ : Pasting (n + 1) G))
    exact (Chain.map_map _ _ p).trans
      ((Chain.map_congr _ (fun d => d) (fun {x y} d => ih (G.hom x y) d) p).trans (Chain.map_id p))

def identities (G : GlobularSet.{u}) : GlobularSet.Identities (globular G) where
  identity := identity
  source_identity := source_identity G
  target_identity := target_identity G

/-- Positive-dimensional diagrams with their zero endpoints exposed in the
type. This is exactly the chain fibre of `Pasting (n+1) G`, not a new carrier. -/
abbrev Horizontal (n : Nat) (G : GlobularSet.{u}) (a b : G.Cell 0) :=
  Chain (fun x y => Pasting n (G.hom x y)) a b

def pack {n : Nat} {G : GlobularSet.{u}} {a b : G.Cell 0}
    (p : Horizontal n G a b) : Pasting (n + 1) G := ⟨a, b, p⟩

theorem sourceZero_pack {n : Nat} {G : GlobularSet.{u}} {a b : G.Cell 0}
    (p : Horizontal n G a b) : (globular G).sourceZero (n := n + 1) (pack p) = a := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (p.map (fun d => source d))

theorem targetZero_pack {n : Nat} {G : GlobularSet.{u}} {a b : G.Cell 0}
    (p : Horizontal n G a b) : (globular G).targetZero (n := n + 1) (pack p) = b := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (p.map (fun d => target d))

/-- Composition along the zero boundary, in every positive dimension. -/
def horizontal {n : Nat} {G : GlobularSet.{u}} {a b c : G.Cell 0}
    (p : Horizontal n G a b) (q : Horizontal n G b c) : Horizontal n G a c :=
  p.append q

theorem horizontal_assoc {n : Nat} {G : GlobularSet.{u}} {a b c d : G.Cell 0}
    (p : Horizontal n G a b) (q : Horizontal n G b c) (r : Horizontal n G c d) :
    horizontal (horizontal p q) r = horizontal p (horizontal q r) :=
  Chain.append_assoc p q r

theorem horizontal_left_unit {n : Nat} {G : GlobularSet.{u}} {a b : G.Cell 0}
    (p : Horizontal n G a b) : horizontal (.nil a) p = p := rfl

theorem horizontal_right_unit {n : Nat} {G : GlobularSet.{u}} {a b : G.Cell 0}
    (p : Horizontal n G a b) : horizontal p (.nil b) = p := Chain.append_nil p

theorem source_horizontal {n : Nat} {G : GlobularSet.{u}} {a b c : G.Cell 0}
    (p : Horizontal (n + 1) G a b) (q : Horizontal (n + 1) G b c) :
    source (pack (horizontal p q)) =
      pack (horizontal (p.map (fun d => source d)) (q.map (fun d => source d))) :=
  _root_.congrArg pack (Chain.map_append (fun d => source d) p q)

theorem target_horizontal {n : Nat} {G : GlobularSet.{u}} {a b c : G.Cell 0}
    (p : Horizontal (n + 1) G a b) (q : Horizontal (n + 1) G b c) :
    target (pack (horizontal p q)) =
      pack (horizontal (p.map (fun d => target d)) (q.map (fun d => target d))) :=
  _root_.congrArg pack (Chain.map_append (fun d => target d) p q)

theorem identity_horizontal {n : Nat} {G : GlobularSet.{u}} {a b c : G.Cell 0}
    (p : Horizontal n G a b) (q : Horizontal n G b c) :
    identity (pack (horizontal p q)) =
      pack (horizontal (p.map (fun d => identity d)) (q.map (fun d => identity d))) :=
  _root_.congrArg pack (Chain.map_append (fun d => identity d) p q)

theorem map_horizontal {n : Nat} {G H : GlobularSet.{u}} (f : GlobularSet.Map G H)
    {a b c : G.Cell 0} (p : Horizontal n G a b) (q : Horizontal n G b c) :
    map f (pack (horizontal p q)) = pack (horizontal
      (p.mapAlong f.app (fun {x y} d => map (f.hom x y) d))
      (q.mapAlong f.app (fun {x y} d => map (f.hom x y) d))) :=
  _root_.congrArg (pack (G := H))
    (Chain.mapAlong_append (F := fun x y => Pasting n (H.hom x y)) f.app
      (fun {x y} d => map (f.hom x y) d) p q)

theorem source_horizontal_one {G : GlobularSet.{u}} {a b c : G.Cell 0}
    (p : Horizontal 0 G a b) (q : Horizontal 0 G b c) :
    source (pack (horizontal p q)) = a := rfl

theorem target_horizontal_one {G : GlobularSet.{u}} {a b c : G.Cell 0}
    (p : Horizontal 0 G a b) (q : Horizontal 0 G b c) :
    target (pack (horizontal p q)) = c := rfl

/-- Composition along the adjacent boundary. At dimension one this is
concatenation; higher dimensions align boundary chains and recursively
compose their labels in the corresponding hom globular set. -/
noncomputable def vertical {n : Nat} {G : GlobularSet.{u}}
    (p q : Pasting (n + 1) G) (h : target p = source q) : Pasting (n + 1) G := by
  induction n generalizing G with
  | zero =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    change b = c at h
    cases h
    exact pack (horizontal p q)
  | succ n ih =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    have ha : a = c := _root_.congrArg Sigma.fst h
    have hb : b = d := _root_.congrArg (fun z => z.2.1) h
    cases ha
    cases hb
    have hp : p.map (fun e => target e) = q.map (fun e => source e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
    exact pack (Chain.zipOver (fun e => target e) (fun e => source e)
      (fun {x y} e f he => ih (G := G.hom x y) e f he) p q hp)

theorem source_vertical {n : Nat} {G : GlobularSet.{u}}
    (p q : Pasting (n + 1) G) (h : target p = source q) :
    source (vertical p q h) = source p := by
  induction n generalizing G with
  | zero =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    change b = c at h
    cases h
    rfl
  | succ n ih =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    have ha : a = c := _root_.congrArg Sigma.fst h
    have hb : b = d := _root_.congrArg (fun z => z.2.1) h
    cases ha
    cases hb
    have hp : p.map (fun e => target e) = q.map (fun e => source e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
    change pack ((Chain.zipOver (fun e => target e) (fun e => source e)
      (fun e f he => vertical e f he) p q hp).map (fun e => source e)) =
        pack (p.map (fun e => source e))
    exact _root_.congrArg pack (Chain.map_zipOver_left _ _ _ _ _
      (fun e f he => ih e f he) p q hp)

theorem target_vertical {n : Nat} {G : GlobularSet.{u}}
    (p q : Pasting (n + 1) G) (h : target p = source q) :
    target (vertical p q h) = target q := by
  induction n generalizing G with
  | zero =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    change b = c at h
    cases h
    rfl
  | succ n ih =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    have ha : a = c := _root_.congrArg Sigma.fst h
    have hb : b = d := _root_.congrArg (fun z => z.2.1) h
    cases ha
    cases hb
    have hp : p.map (fun e => target e) = q.map (fun e => source e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
    change pack ((Chain.zipOver (fun e => target e) (fun e => source e)
      (fun e f he => vertical e f he) p q hp).map (fun e => target e)) =
        pack (q.map (fun e => target e))
    exact _root_.congrArg pack (Chain.map_zipOver_right _ _ _ _ _
      (fun e f he => ih e f he) p q hp)

/-- The recursive operation inhabits the prescribed globular composite
boundary, rather than merely returning an unrelated cell of the same dimension. -/
noncomputable def verticalCell {n : Nat} {G : GlobularSet.{u}}
    (p q : Pasting (n + 1) G) (h : target p = source q) :
    (globular G).CellOver ((globular G).compositeBoundary (n := n) p q h) :=
  ⟨vertical p q h, source_vertical p q h, target_vertical p q h⟩

end Pasting

/-- Interpretation of composable path-labelled chains keeps the endpoints
and composes the actual computational traces. -/
noncomputable def evalPathChain {A : Type u} {a b : A} :
    Chain (fun a b : A => Path a b) a b → Path a b
  | .nil a => Path.refl a
  | .cons p ps => Path.trans p (evalPathChain ps)

theorem evalPathChain_append {A : Type u} {a b c : A}
    (p : Chain (fun a b : A => Path a b) a b)
    (q : Chain (fun a b : A => Path a b) b c) :
    evalPathChain (p.append q) = Path.trans (evalPathChain p) (evalPathChain q) := by
  induction p with
  | nil => exact (Path.trans_refl_left _).symm
  | cons e p ih =>
    exact (_root_.congrArg (Path.trans e) (ih q)).trans
      (Path.trans_assoc e (evalPathChain p) (evalPathChain q)).symm

/-- Substitution of actual computational-path chains agrees with composing
the substituted traces, including their stored rewrite-step lists. -/
theorem evalPathChain_bind {A : Type u}
    (f : {a b : A} → Path a b → Chain (fun a b : A => Path a b) a b)
    {a b : A} (p : Chain (fun a b : A => Path a b) a b) :
    evalPathChain (p.bind f) = evalPathChain (p.map (fun e => evalPathChain (f e))) := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    exact (evalPathChain_append (f e) (p.bind f)).trans
      (_root_.congrArg (Path.trans (evalPathChain (f e))) ih)

noncomputable def pathChainAssoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  RwEq.step (Step.trans_assoc p q r)

end ComputationalPaths.Path.OmegaFoundations

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

end Pasting

/-- Interpretation of composable path-labelled chains keeps the endpoints
and composes the actual computational traces. -/
noncomputable def evalPathChain {A : Type u} {a b : A} :
    Chain (fun a b : A => Path a b) a b → Path a b
  | .nil a => Path.refl a
  | .cons p ps => Path.trans p (evalPathChain ps)

noncomputable def pathChainAssoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  RwEq.step (Step.trans_assoc p q r)

end ComputationalPaths.Path.OmegaFoundations

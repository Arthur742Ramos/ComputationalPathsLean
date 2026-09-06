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

universe u v w u₁

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

theorem map_map {D : O → O → Type u₁}
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

theorem map_heq {D : O → O → Type w} (hFD : F = D)
    (f : {x y : O} → E x y → F x y) (g : {x y : O} → E x y → D x y)
    (h : ∀ {x y} (e : E x y), HEq (f e) (g e)) {x y : O} (p : Chain E x y) :
    HEq (p.map f) (p.map g) := by
  cases hFD
  exact heq_of_eq (map_congr f g (fun e => eq_of_heq (h e)) p)

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

theorem zipOver_map_left {O : Type u} {E D : O → O → Type v}
    (s t : {x y : O} → E x y → D x y)
    (op : {x y : O} → (e f : E x y) → s e = t f → E x y)
    (i : {x y : O} → E x y → E x y)
    (hi : ∀ {x y} (e : E x y), s (i e) = t e)
    (law : ∀ {x y} (e : E x y), op (i e) e (hi e) = e)
    {x y : O} (p : Chain E x y) :
    zipOver s t op (p.map i) p
      ((map_map i s p).trans (map_congr _ t hi p)) = p := by
  induction p with
  | nil => rfl
  | cons e p ih => exact _root_.congrArg₂ Chain.cons (law e) ih

theorem zipOver_map_right {O : Type u} {E D : O → O → Type v}
    (s t : {x y : O} → E x y → D x y)
    (op : {x y : O} → (e f : E x y) → s e = t f → E x y)
    (i : {x y : O} → E x y → E x y)
    (hi : ∀ {x y} (e : E x y), s e = t (i e))
    (law : ∀ {x y} (e : E x y), op e (i e) (hi e) = e)
    {x y : O} (p : Chain E x y) :
    zipOver s t op p (p.map i)
      ((map_congr s _ hi p).trans (map_map i t p).symm) = p := by
  induction p with
  | nil => rfl
  | cons e p ih => exact _root_.congrArg₂ Chain.cons (law e) ih

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

theorem zipOver_assoc {O : Type u} {E D : O → O → Type v}
    (s t : {x y : O} → E x y → D x y)
    (op : {x y : O} → (e f : E x y) → s e = t f → E x y)
    (ls : ∀ {x y} (e f : E x y) (h : s e = t f), s (op e f h) = s f)
    (lt : ∀ {x y} (e f : E x y) (h : s e = t f), t (op e f h) = t e)
    (assoc : ∀ {x y} (e f g : E x y) (h : s e = t f) (k : s f = t g),
      op (op e f h) g ((ls e f h).trans k) = op e (op f g k) (h.trans (lt f g k).symm))
    {x y : O} (p q r : Chain E x y) (h : p.map s = q.map t) (k : q.map s = r.map t) :
    zipOver s t op (zipOver s t op p q h) r
      ((map_zipOver_right s t op s s ls p q h).trans k) =
    zipOver s t op p (zipOver s t op q r k)
      (h.trans (map_zipOver_left s t op t t lt q r k).symm) := by
  induction p with
  | nil x =>
    cases q with
    | nil =>
      cases r with
      | nil => rfl
      | cons g r => cases k
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
      cases r with
      | nil => cases k
      | @cons _ z'' _ g r =>
        have kc := k
        simp only [map] at kc
        injection kc with hx hz hy hf hq
        cases hz
        have hf' := eq_of_heq hf
        have hq' := eq_of_heq hq
        exact _root_.congrArg₂ Chain.cons (assoc e f g he' hf') (ih q r hp' hq')

/-- A label map preserving partial composition lifts to aligned chains.
Both boundary equalities are explicit, so no injectivity of the label map
or reflection of boundary equality is assumed. -/
theorem map_zipOver {O : Type u} {E F D B : O → O → Type v}
    (s t : {x y : O} → E x y → D x y)
    (s' t' : {x y : O} → F x y → B x y)
    (op : {x y : O} → (e f : E x y) → s e = t f → E x y)
    (op' : {x y : O} → (e f : F x y) → s' e = t' f → F x y)
    (f : {x y : O} → E x y → F x y)
    (law : ∀ {x y} (e d : E x y) (h : s e = t d) (h' : s' (f e) = t' (f d)),
      f (op e d h) = op' (f e) (f d) h')
    {x y : O} (p q : Chain E x y) (h : p.map s = q.map t)
    (h' : (p.map f).map s' = (q.map f).map t') :
    (zipOver s t op p q h).map f = zipOver s' t' op' (p.map f) (q.map f) h' := by
  induction p with
  | nil x =>
    cases q with
    | nil => rfl
    | cons d q => cases h
  | @cons x z y e p ih =>
    cases q with
    | nil => cases h
    | @cons _ z' _ d q =>
      have hc := h
      simp only [map] at hc
      injection hc with hx hz hy he hp
      cases hz
      have he' := eq_of_heq he
      have hp' := eq_of_heq hp
      have hd := h'
      simp only [map] at hd
      injection hd with hx hz hy hf hq
      have hf' : s' (f e) = t' (f d) := hf
      have hq' : (p.map f).map s' = (q.map f).map t' := hq
      exact _root_.congrArg₂ Chain.cons (law e d he' hf') (ih q hp' hq')

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

theorem mapAlong_zipOver {E D : O → O → Type u} {F B : P → P → Type v}
    (a : O → P) (f : {x y : O} → E x y → F (a x) (a y))
    (s t : {x y : O} → E x y → D x y)
    (s' t' : {x y : P} → F x y → B x y)
    (op : {x y : O} → (e d : E x y) → s e = t d → E x y)
    (op' : {x y : P} → (e d : F x y) → s' e = t' d → F x y)
    (law : ∀ {x y} (e d : E x y) (h : s e = t d) (h' : s' (f e) = t' (f d)),
      f (op e d h) = op' (f e) (f d) h')
    {x y : O} (p q : Chain E x y) (h : p.map s = q.map t)
    (h' : (p.mapAlong a f).map s' = (q.mapAlong a f).map t') :
    (zipOver s t op p q h).mapAlong a f =
      zipOver s' t' op' (p.mapAlong a f) (q.mapAlong a f) h' := by
  induction p with
  | nil x =>
    cases q with
    | nil => rfl
    | cons d q => cases h
  | @cons x z y e p ih =>
    cases q with
    | nil => cases h
    | @cons _ z' _ d q =>
      have hc := h
      simp only [map] at hc
      injection hc with hx hz hy he hp
      cases hz
      have he' := eq_of_heq he
      have hp' := eq_of_heq hp
      have hd := h'
      simp only [mapAlong, map] at hd
      injection hd with hx hz hy hf hq
      have hf' : s' (f e) = t' (f d) := hf
      have hq' : (p.mapAlong a f).map s' = (q.mapAlong a f).map t' := hq
      exact _root_.congrArg₂ Chain.cons (law e d he' hf') (ih q hp' hq')

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

theorem pack_heq {n m : Nat} {G : GlobularSet.{u}} {a b : G.Cell 0}
    (h : n = m) (p : Horizontal n G a b) (q : Horizontal m G a b) (hp : HEq p q) :
    HEq (pack p) (pack q) := by
  cases h
  cases hp
  rfl

/-- Change only the arithmetic presentation of the dimension. -/
def reindex {n m : Nat} {G : GlobularSet.{u}} (h : n = m) (p : Pasting n G) : Pasting m G :=
  h ▸ p

theorem reindex_trans {n m l : Nat} {G : GlobularSet.{u}} (h : n = m) (j : m = l)
    (p : Pasting n G) : reindex j (reindex h p) = reindex (h.trans j) p := by
  cases h
  cases j
  rfl

theorem reindex_source {n m : Nat} {G : GlobularSet.{u}} (h : n = m)
    (p : Pasting (n + 1) G) :
    source (reindex (_root_.congrArg Nat.succ h) p) = reindex h (source p) := by
  cases h
  rfl

theorem reindex_target {n m : Nat} {G : GlobularSet.{u}} (h : n = m)
    (p : Pasting (n + 1) G) :
    target (reindex (_root_.congrArg Nat.succ h) p) = reindex h (target p) := by
  cases h
  rfl

theorem reindex_heq {n m : Nat} {G : GlobularSet.{u}} (h : n = m) (p : Pasting n G) :
    HEq (reindex h p) p := by
  cases h
  rfl

theorem reindex_pack {n m : Nat} {G : GlobularSet.{u}} {a b : G.Cell 0}
    (h : n = m) (p : Horizontal n G a b) :
    reindex (_root_.congrArg Nat.succ h) (pack p) = pack (p.map (fun e => reindex h e)) := by
  cases h
  exact _root_.congrArg pack (Chain.map_id p).symm

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

theorem vertical_left_unit {n : Nat} {G : GlobularSet.{u}} (p : Pasting (n + 1) G) :
    vertical (identity (source p)) p (target_identity G (source p)) = p := by
  induction n generalizing G with
  | zero => rcases p with ⟨a, b, p⟩; rfl
  | succ n ih =>
    rcases p with ⟨a, b, p⟩
    simp only [identity, source, Chain.map_map]
    exact _root_.congrArg pack (Chain.zipOver_map_left
      (fun e => target e) (fun e => source e) (fun e f h => vertical e f h)
      (fun e => identity (source e)) (fun {x y} e => target_identity (G.hom x y) (source e))
      (fun e => ih e) p)

theorem vertical_right_unit {n : Nat} {G : GlobularSet.{u}} (p : Pasting (n + 1) G) :
    vertical p (identity (target p)) (source_identity G (target p)).symm = p := by
  induction n generalizing G with
  | zero =>
    rcases p with ⟨a, b, p⟩
    exact _root_.congrArg pack (Chain.append_nil p)
  | succ n ih =>
    rcases p with ⟨a, b, p⟩
    simp only [identity, target, Chain.map_map]
    exact _root_.congrArg pack (Chain.zipOver_map_right
      (fun e => target e) (fun e => source e) (fun e f h => vertical e f h)
      (fun e => identity (target e)) (fun {x y} e => (source_identity (G.hom x y) (target e)).symm)
      (fun e => ih e) p)

theorem vertical_assoc {n : Nat} {G : GlobularSet.{u}}
    (p q r : Pasting (n + 1) G) (h : target p = source q) (k : target q = source r) :
    vertical (vertical p q h) r ((target_vertical p q h).trans k) =
      vertical p (vertical q r k) (h.trans (source_vertical q r k).symm) := by
  induction n generalizing G with
  | zero =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    rcases r with ⟨e, f, r⟩
    change b = c at h
    change d = e at k
    cases h
    cases k
    exact _root_.congrArg pack (Chain.append_assoc p q r)
  | succ n ih =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    rcases r with ⟨e, f, r⟩
    have ha : a = c := _root_.congrArg Sigma.fst h
    have hb : b = d := _root_.congrArg (fun z => z.2.1) h
    have hc : c = e := _root_.congrArg Sigma.fst k
    have hd : d = f := _root_.congrArg (fun z => z.2.1) k
    cases ha
    cases hb
    cases hc
    cases hd
    have hp : p.map (fun e => target e) = q.map (fun e => source e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
    have hq : q.map (fun e => target e) = r.map (fun e => source e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj k).2)).2
    exact _root_.congrArg pack (Chain.zipOver_assoc
      (fun e => target e) (fun e => source e) (fun e f h => vertical e f h)
      (fun e f h => target_vertical e f h) (fun e f h => source_vertical e f h)
      (fun e f g h k => ih e f g h k) p q r hp hq)

/-- The adjacent composition with zero endpoints exposed for horizontal
composition. `pack_verticalFibre` identifies it with `vertical`. -/
noncomputable def verticalFibre {n : Nat} {G : GlobularSet.{u}} {a b : G.Cell 0}
    (p q : Horizontal (n + 1) G a b)
    (h : p.map (fun e => target e) = q.map (fun e => source e)) : Horizontal (n + 1) G a b :=
  Chain.zipOver (fun e => target e) (fun e => source e) (fun e f h => vertical e f h) p q h

theorem pack_verticalFibre {n : Nat} {G : GlobularSet.{u}} {a b : G.Cell 0}
    (p q : Horizontal (n + 1) G a b)
    (h : p.map (fun e => target e) = q.map (fun e => source e)) :
    pack (verticalFibre p q h) = vertical (pack p) (pack q) (_root_.congrArg pack h) := rfl

/-- Strict interchange between zero-boundary and adjacent-boundary
composition, in all dimensions at least two. -/
theorem vertical_horizontal_interchange {n : Nat} {G : GlobularSet.{u}} {a b c : G.Cell 0}
    (p q : Horizontal (n + 1) G a b) (r s : Horizontal (n + 1) G b c)
    (h : p.map (fun e => target e) = q.map (fun e => source e))
    (k : r.map (fun e => target e) = s.map (fun e => source e)) :
    verticalFibre (horizontal p r) (horizontal q s)
      ((Chain.map_append _ p r).trans ((_root_.congrArg₂ Chain.append h k).trans
        (Chain.map_append _ q s).symm)) =
      horizontal (verticalFibre p q h) (verticalFibre r s k) :=
  Chain.zipOver_append _ _ _ p q h r s k

/-- Source at dimension `k` of a diagram at dimension `n+k+1`.
The excess dimension `n+1` is arbitrary, not a fixed truncation bound. -/
def sourceAt : (k n : Nat) → {G : GlobularSet.{u}} → Pasting (n + k + 1) G → Pasting k G
  | 0, _, _, ⟨a, _, _⟩ => a
  | k + 1, n, G, ⟨a, b, p⟩ =>
      ⟨a, b, p.map (fun {x y} e => sourceAt k n (G := G.hom x y) e)⟩

def targetAt : (k n : Nat) → {G : GlobularSet.{u}} → Pasting (n + k + 1) G → Pasting k G
  | 0, _, _, ⟨_, b, _⟩ => b
  | k + 1, n, G, ⟨a, b, p⟩ =>
      ⟨a, b, p.map (fun {x y} e => targetAt k n (G := G.hom x y) e)⟩

theorem sourceAt_map (k n : Nat) {G H : GlobularSet.{u}} (f : GlobularSet.Map G H)
    (p : Pasting (n + k + 1) G) : sourceAt k n (map f p) = map f (sourceAt k n p) := by
  induction k generalizing G H with
  | zero => rcases p with ⟨a, b, p⟩; rfl
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    exact _root_.congrArg pack (Chain.mapAlong_natural _ _ _ _ _
      (fun {x y} e => ih (f.hom x y) e) p)

theorem targetAt_map (k n : Nat) {G H : GlobularSet.{u}} (f : GlobularSet.Map G H)
    (p : Pasting (n + k + 1) G) : targetAt k n (map f p) = map f (targetAt k n p) := by
  induction k generalizing G H with
  | zero => rcases p with ⟨a, b, p⟩; rfl
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    exact _root_.congrArg pack (Chain.mapAlong_natural _ _ _ _ _
      (fun {x y} e => ih (f.hom x y) e) p)

theorem sourceAt_adjacent (k : Nat) {G : GlobularSet.{u}} (p : Pasting (0 + k + 1) G) :
    HEq (sourceAt k 0 p) (source p) := by
  induction k generalizing G with
  | zero => rcases p with ⟨a, b, p⟩; rfl
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    exact pack_heq (Nat.zero_add k).symm _ _
      (Chain.map_heq (by rw [Nat.zero_add]) _ _ (fun {x y} e => ih e) p)

theorem targetAt_adjacent (k : Nat) {G : GlobularSet.{u}} (p : Pasting (0 + k + 1) G) :
    HEq (targetAt k 0 p) (target p) := by
  induction k generalizing G with
  | zero => rcases p with ⟨a, b, p⟩; rfl
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    exact pack_heq (Nat.zero_add k).symm _ _
      (Chain.map_heq (by rw [Nat.zero_add]) _ _ (fun {x y} e => ih e) p)

theorem excess_succ_dimension (k n : Nat) : n + k + 2 = (n + 1) + k + 1 := by
  rw [Nat.succ_add]

/-- Increasing the dimension gap is exactly taking one more source in the
original globular tower; reindex changes dimension arithmetic only. -/
theorem sourceAt_step (k n : Nat) {G : GlobularSet.{u}} (p : Pasting (n + k + 2) G) :
    sourceAt k (n + 1) (reindex (excess_succ_dimension k n) p) = sourceAt k n (source p) := by
  induction k generalizing G with
  | zero => rcases p with ⟨a, b, p⟩; rfl
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    change sourceAt (k + 1) (n + 1)
      (reindex (_root_.congrArg Nat.succ (excess_succ_dimension k n)) (pack p)) = _
    rw [reindex_pack]
    change pack ((p.map (fun e => reindex (excess_succ_dimension k n) e)).map
      (fun e => sourceAt k (n + 1) e)) =
      pack ((p.map (fun e => source e)).map (fun e => sourceAt k n e))
    apply _root_.congrArg pack
    simp only [Chain.map_map]
    exact Chain.map_congr _ _ (fun e => ih e) p

theorem targetAt_step (k n : Nat) {G : GlobularSet.{u}} (p : Pasting (n + k + 2) G) :
    targetAt k (n + 1) (reindex (excess_succ_dimension k n) p) = targetAt k n (target p) := by
  induction k generalizing G with
  | zero => rcases p with ⟨a, b, p⟩; rfl
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    change targetAt (k + 1) (n + 1)
      (reindex (_root_.congrArg Nat.succ (excess_succ_dimension k n)) (pack p)) = _
    rw [reindex_pack]
    change pack ((p.map (fun e => reindex (excess_succ_dimension k n) e)).map
      (fun e => targetAt k (n + 1) e)) =
      pack ((p.map (fun e => target e)).map (fun e => targetAt k n e))
    apply _root_.congrArg pack
    simp only [Chain.map_map]
    exact Chain.map_congr _ _ (fun e => ih e) p

theorem sourceAt_globular (k n : Nat) {G : GlobularSet.{u}} (p : Pasting (n + k + 2) G) :
    sourceAt k n (source p) = sourceAt k n (target p) := by
  induction k generalizing G with
  | zero => rcases p with ⟨a, b, p⟩; rfl
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    apply _root_.congrArg pack
    simp only [Chain.map_map]
    exact Chain.map_congr _ _ (fun e => ih e) p

theorem targetAt_globular (k n : Nat) {G : GlobularSet.{u}} (p : Pasting (n + k + 2) G) :
    targetAt k n (source p) = targetAt k n (target p) := by
  induction k generalizing G with
  | zero => rcases p with ⟨a, b, p⟩; rfl
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    apply _root_.congrArg pack
    simp only [Chain.map_map]
    exact Chain.map_congr _ _ (fun e => ih e) p

theorem sourceAt_lower (k n : Nat) {G : GlobularSet.{u}} (p : Pasting (n + k + 2) G) :
    source (sourceAt (k + 1) n p) =
      sourceAt k (n + 1) (reindex (excess_succ_dimension k n) p) := by
  induction k generalizing G with
  | zero => rcases p with ⟨a, b, p⟩; rfl
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    change _ = sourceAt (k + 1) (n + 1)
      (reindex (_root_.congrArg Nat.succ (excess_succ_dimension k n)) (pack p))
    rw [reindex_pack]
    apply _root_.congrArg pack
    simp only [Chain.map_map]
    exact Chain.map_congr _ _ (fun e => ih e) p

theorem targetAt_lower (k n : Nat) {G : GlobularSet.{u}} (p : Pasting (n + k + 2) G) :
    target (targetAt (k + 1) n p) =
      targetAt k (n + 1) (reindex (excess_succ_dimension k n) p) := by
  induction k generalizing G with
  | zero => rcases p with ⟨a, b, p⟩; rfl
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    change _ = targetAt (k + 1) (n + 1)
      (reindex (_root_.congrArg Nat.succ (excess_succ_dimension k n)) (pack p))
    rw [reindex_pack]
    apply _root_.congrArg pack
    simp only [Chain.map_map]
    exact Chain.map_congr _ _ (fun e => ih e) p

/-- Direct identification with the existing tower's iterated source. -/
theorem sourceAt_eq_sourceIter (k n : Nat) {G : GlobularSet.{u}}
    (p : Pasting (n + k + 1) G) :
    sourceAt k n p = (globular G).sourceIter (n := k) (n + 1)
      (reindex (by omega) p) := by
  induction n with
  | zero =>
    change sourceAt k 0 p = source (reindex (_root_.congrArg Nat.succ (Nat.zero_add k)) p)
    rw [reindex_source (Nat.zero_add k)]
    exact eq_of_heq ((sourceAt_adjacent k p).trans (reindex_heq (Nat.zero_add k) (source p)).symm)
  | succ n ih =>
    let q := reindex (excess_succ_dimension k n).symm p
    have hs := sourceAt_step k n q
    have hc : reindex (excess_succ_dimension k n) q = p := by
      dsimp [q]
      rw [reindex_trans]
      rfl
    rw [hc] at hs
    refine hs.trans ((ih (source q)).trans ?_)
    change (globular G).sourceIter (n := k) (n + 1) (reindex _ (source q)) =
      (globular G).sourceIter (n := k) (n + 1) (source (reindex _ p))
    apply _root_.congrArg ((globular G).sourceIter (n := k) (n + 1))
    dsimp [q]
    rw [reindex_source (by omega), reindex_trans, reindex_source (by omega)]

theorem targetAt_eq_targetIter (k n : Nat) {G : GlobularSet.{u}}
    (p : Pasting (n + k + 1) G) :
    targetAt k n p = (globular G).targetIter (n := k) (n + 1)
      (reindex (by omega) p) := by
  induction n with
  | zero =>
    change targetAt k 0 p = target (reindex (_root_.congrArg Nat.succ (Nat.zero_add k)) p)
    rw [reindex_target (Nat.zero_add k)]
    exact eq_of_heq ((targetAt_adjacent k p).trans (reindex_heq (Nat.zero_add k) (target p)).symm)
  | succ n ih =>
    let q := reindex (excess_succ_dimension k n).symm p
    have hs := targetAt_step k n q
    have hc : reindex (excess_succ_dimension k n) q = p := by
      dsimp [q]
      rw [reindex_trans]
      rfl
    rw [hc] at hs
    refine hs.trans ((ih (target q)).trans ?_)
    change (globular G).targetIter (n := k) (n + 1) (reindex _ (target q)) =
      (globular G).targetIter (n := k) (n + 1) (target (reindex _ p))
    apply _root_.congrArg ((globular G).targetIter (n := k) (n + 1))
    dsimp [q]
    rw [reindex_target (by omega), reindex_trans, reindex_target (by omega)]

/-- Composition at an arbitrary lower boundary. Recursion is on the actual
boundary dimension, reducing to horizontal concatenation in each hom tower. -/
noncomputable def composeAt (k n : Nat) {G : GlobularSet.{u}}
    (p q : Pasting (n + k + 1) G) (h : targetAt k n p = sourceAt k n q) :
    Pasting (n + k + 1) G := by
  induction k generalizing G with
  | zero =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    change b = c at h
    cases h
    exact pack (horizontal p q)
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    have ha : a = c := _root_.congrArg Sigma.fst h
    have hb : b = d := _root_.congrArg (fun z => z.2.1) h
    cases ha
    cases hb
    have hp : p.map (fun e => targetAt k n e) = q.map (fun e => sourceAt k n e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
    exact pack (Chain.zipOver (fun e => targetAt k n e) (fun e => sourceAt k n e)
      (fun {x y} e f he => ih (G := G.hom x y) e f he) p q hp)

theorem sourceAt_composeAt (k n : Nat) {G : GlobularSet.{u}}
    (p q : Pasting (n + k + 1) G) (h : targetAt k n p = sourceAt k n q) :
    sourceAt k n (composeAt k n p q h) = sourceAt k n p := by
  induction k generalizing G with
  | zero =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    change b = c at h
    cases h
    rfl
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    have ha : a = c := _root_.congrArg Sigma.fst h
    have hb : b = d := _root_.congrArg (fun z => z.2.1) h
    cases ha
    cases hb
    have hp : p.map (fun e => targetAt k n e) = q.map (fun e => sourceAt k n e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
    exact _root_.congrArg pack (Chain.map_zipOver_left _ _ _ _ _
      (fun e f he => ih e f he) p q hp)

theorem targetAt_composeAt (k n : Nat) {G : GlobularSet.{u}}
    (p q : Pasting (n + k + 1) G) (h : targetAt k n p = sourceAt k n q) :
    targetAt k n (composeAt k n p q h) = targetAt k n q := by
  induction k generalizing G with
  | zero =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    change b = c at h
    cases h
    rfl
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    have ha : a = c := _root_.congrArg Sigma.fst h
    have hb : b = d := _root_.congrArg (fun z => z.2.1) h
    cases ha
    cases hb
    have hp : p.map (fun e => targetAt k n e) = q.map (fun e => sourceAt k n e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
    exact _root_.congrArg pack (Chain.map_zipOver_right _ _ _ _ _
      (fun e f he => ih e f he) p q hp)

/-- The identity diagram over a `k`-cell in dimension `n+k+1`. -/
def identityAt : (k n : Nat) → {G : GlobularSet.{u}} → Pasting k G → Pasting (n + k + 1) G
  | 0, _, _, a => ⟨a, a, .nil a⟩
  | k + 1, n, G, ⟨a, b, p⟩ =>
      ⟨a, b, p.map (fun {x y} e => identityAt k n (G := G.hom x y) e)⟩

theorem map_identityAt (k n : Nat) {G H : GlobularSet.{u}} (f : GlobularSet.Map G H)
    (p : Pasting k G) : map f (identityAt k n p) = identityAt k n (map f p) := by
  induction k generalizing G H with
  | zero => rfl
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    apply _root_.congrArg pack
    exact (Chain.mapAlong_natural _ _ _ _ _ (fun {x y} e => (ih (f.hom x y) e).symm) p).symm

theorem sourceAt_identityAt (k n : Nat) {G : GlobularSet.{u}} (p : Pasting k G) :
    sourceAt k n (identityAt k n p) = p := by
  induction k generalizing G with
  | zero => rfl
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    exact _root_.congrArg pack ((Chain.map_map _ _ p).trans
      ((Chain.map_congr _ (fun e => e) (fun e => ih e) p).trans (Chain.map_id p)))

theorem targetAt_identityAt (k n : Nat) {G : GlobularSet.{u}} (p : Pasting k G) :
    targetAt k n (identityAt k n p) = p := by
  induction k generalizing G with
  | zero => rfl
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    exact _root_.congrArg pack ((Chain.map_map _ _ p).trans
      ((Chain.map_congr _ (fun e => e) (fun e => ih e) p).trans (Chain.map_id p)))

theorem composeAt_left_unit (k n : Nat) {G : GlobularSet.{u}} (p : Pasting (n + k + 1) G) :
    composeAt k n (identityAt k n (sourceAt k n p)) p
      (targetAt_identityAt k n (sourceAt k n p)) = p := by
  induction k generalizing G with
  | zero => rcases p with ⟨a, b, p⟩; rfl
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    simp only [identityAt, sourceAt, Chain.map_map]
    exact _root_.congrArg pack (Chain.zipOver_map_left
      (fun e => targetAt k n e) (fun e => sourceAt k n e) (fun e f h => composeAt k n e f h)
      (fun e => identityAt k n (sourceAt k n e)) (fun e => targetAt_identityAt k n (sourceAt k n e))
      (fun e => ih e) p)

theorem composeAt_right_unit (k n : Nat) {G : GlobularSet.{u}} (p : Pasting (n + k + 1) G) :
    composeAt k n p (identityAt k n (targetAt k n p))
      (sourceAt_identityAt k n (targetAt k n p)).symm = p := by
  induction k generalizing G with
  | zero =>
    rcases p with ⟨a, b, p⟩
    exact _root_.congrArg pack (Chain.append_nil p)
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    simp only [identityAt, targetAt, Chain.map_map]
    exact _root_.congrArg pack (Chain.zipOver_map_right
      (fun e => targetAt k n e) (fun e => sourceAt k n e) (fun e f h => composeAt k n e f h)
      (fun e => identityAt k n (targetAt k n e)) (fun e => (sourceAt_identityAt k n (targetAt k n e)).symm)
      (fun e => ih e) p)

theorem composeAt_assoc (k n : Nat) {G : GlobularSet.{u}}
    (p q r : Pasting (n + k + 1) G)
    (h : targetAt k n p = sourceAt k n q) (j : targetAt k n q = sourceAt k n r) :
    composeAt k n (composeAt k n p q h) r ((targetAt_composeAt k n p q h).trans j) =
      composeAt k n p (composeAt k n q r j) (h.trans (sourceAt_composeAt k n q r j).symm) := by
  induction k generalizing G with
  | zero =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    rcases r with ⟨e, f, r⟩
    change b = c at h
    change d = e at j
    cases h
    cases j
    exact _root_.congrArg pack (Chain.append_assoc p q r)
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    rcases r with ⟨e, f, r⟩
    have ha : a = c := _root_.congrArg Sigma.fst h
    have hb : b = d := _root_.congrArg (fun z => z.2.1) h
    have hc : c = e := _root_.congrArg Sigma.fst j
    have hd : d = f := _root_.congrArg (fun z => z.2.1) j
    cases ha
    cases hb
    cases hc
    cases hd
    have hp : p.map (fun e => targetAt k n e) = q.map (fun e => sourceAt k n e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
    have hq : q.map (fun e => targetAt k n e) = r.map (fun e => sourceAt k n e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj j).2)).2
    exact _root_.congrArg pack (Chain.zipOver_assoc
      (fun e => targetAt k n e) (fun e => sourceAt k n e) (fun e f h => composeAt k n e f h)
      (fun e f h => targetAt_composeAt k n e f h) (fun e f h => sourceAt_composeAt k n e f h)
      (fun e f g h j => ih e f g h j) p q r hp hq)

theorem map_composeAt (k n : Nat) {G H : GlobularSet.{u}} (f : GlobularSet.Map G H)
    (p q : Pasting (n + k + 1) G) (h : targetAt k n p = sourceAt k n q)
    (h' : targetAt k n (map f p) = sourceAt k n (map f q)) :
    map f (composeAt k n p q h) = composeAt k n (map f p) (map f q) h' := by
  induction k generalizing G H with
  | zero =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    change b = c at h
    cases h
    exact map_horizontal f p q
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    have ha : a = c := _root_.congrArg Sigma.fst h
    have hb : b = d := _root_.congrArg (fun z => z.2.1) h
    cases ha
    cases hb
    have hp : p.map (fun e => targetAt k n e) = q.map (fun e => sourceAt k n e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
    have hp' : (p.mapAlong f.app (fun {x y} e => map (f.hom x y) e)).map (fun e => targetAt k n e) =
        (q.mapAlong f.app (fun {x y} e => map (f.hom x y) e)).map (fun e => sourceAt k n e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h').2)).2
    exact _root_.congrArg (pack (G := H)) (Chain.mapAlong_zipOver
      (F := fun x y => Pasting (n + k + 1) (H.hom x y)) f.app
      (fun {x y} e => map (f.hom x y) e)
      (fun e => targetAt k n e) (fun e => sourceAt k n e)
      (fun e => targetAt k n e) (fun e => sourceAt k n e)
      (fun e d h => composeAt k n e d h) (fun e d h => composeAt k n e d h)
      (fun {x y} e d h j => ih (f.hom x y) e d h j) p q hp hp')

/-- Relabelling supplies its own composability proof from the original one. -/
theorem map_composeAt_natural (k n : Nat) {G H : GlobularSet.{u}} (f : GlobularSet.Map G H)
    (p q : Pasting (n + k + 1) G) (h : targetAt k n p = sourceAt k n q) :
    map f (composeAt k n p q h) = composeAt k n (map f p) (map f q)
      ((targetAt_map k n f p).trans ((_root_.congrArg (map f) h).trans (sourceAt_map k n f q).symm)) :=
  map_composeAt k n f p q h _

/-- Adjacent source, indexed so the dimension gap decreases without hiding
arithmetic casts inside a composition. `dropSource_eq` identifies this with
the existing source operation. -/
def dropSource : (k n : Nat) → {G : GlobularSet.{u}} →
    Pasting ((n + 1) + k + 1) G → Pasting (n + k + 1) G
  | 0, _, _, p => source p
  | k + 1, n, G, ⟨a, b, p⟩ =>
      ⟨a, b, p.map (fun {x y} e => dropSource k n (G := G.hom x y) e)⟩

def dropTarget : (k n : Nat) → {G : GlobularSet.{u}} →
    Pasting ((n + 1) + k + 1) G → Pasting (n + k + 1) G
  | 0, _, _, p => target p
  | k + 1, n, G, ⟨a, b, p⟩ =>
      ⟨a, b, p.map (fun {x y} e => dropTarget k n (G := G.hom x y) e)⟩

theorem dropSource_eq (k n : Nat) {G : GlobularSet.{u}} (p : Pasting ((n + 1) + k + 1) G) :
    dropSource k n p = source (reindex (excess_succ_dimension k n).symm p) := by
  induction k generalizing G with
  | zero => rfl
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    change _ = source (reindex (_root_.congrArg Nat.succ (excess_succ_dimension k n).symm) (pack p))
    rw [reindex_pack (excess_succ_dimension k n).symm]
    apply _root_.congrArg pack
    exact (Chain.map_congr _ _ (fun e => ih e) p).trans (Chain.map_map _ _ p).symm

theorem dropTarget_eq (k n : Nat) {G : GlobularSet.{u}} (p : Pasting ((n + 1) + k + 1) G) :
    dropTarget k n p = target (reindex (excess_succ_dimension k n).symm p) := by
  induction k generalizing G with
  | zero => rfl
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    change _ = target (reindex (_root_.congrArg Nat.succ (excess_succ_dimension k n).symm) (pack p))
    rw [reindex_pack (excess_succ_dimension k n).symm]
    apply _root_.congrArg pack
    exact (Chain.map_congr _ _ (fun e => ih e) p).trans (Chain.map_map _ _ p).symm

theorem sourceAt_dropSource (k n : Nat) {G : GlobularSet.{u}} (p : Pasting ((n + 1) + k + 1) G) :
    sourceAt k n (dropSource k n p) = sourceAt k (n + 1) p := by
  induction k generalizing G with
  | zero => rcases p with ⟨a, b, p⟩; rfl
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    exact _root_.congrArg pack ((Chain.map_map _ _ p).trans (Chain.map_congr _ _ (fun e => ih e) p))

theorem targetAt_dropSource (k n : Nat) {G : GlobularSet.{u}} (p : Pasting ((n + 1) + k + 1) G) :
    targetAt k n (dropSource k n p) = targetAt k (n + 1) p := by
  induction k generalizing G with
  | zero => rcases p with ⟨a, b, p⟩; rfl
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    exact _root_.congrArg pack ((Chain.map_map _ _ p).trans (Chain.map_congr _ _ (fun e => ih e) p))

theorem sourceAt_dropTarget (k n : Nat) {G : GlobularSet.{u}} (p : Pasting ((n + 1) + k + 1) G) :
    sourceAt k n (dropTarget k n p) = sourceAt k (n + 1) p := by
  induction k generalizing G with
  | zero => rcases p with ⟨a, b, p⟩; rfl
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    exact _root_.congrArg pack ((Chain.map_map _ _ p).trans (Chain.map_congr _ _ (fun e => ih e) p))

theorem targetAt_dropTarget (k n : Nat) {G : GlobularSet.{u}} (p : Pasting ((n + 1) + k + 1) G) :
    targetAt k n (dropTarget k n p) = targetAt k (n + 1) p := by
  induction k generalizing G with
  | zero => rcases p with ⟨a, b, p⟩; rfl
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    exact _root_.congrArg pack ((Chain.map_map _ _ p).trans (Chain.map_congr _ _ (fun e => ih e) p))

theorem dropSource_composeAt (k n : Nat) {G : GlobularSet.{u}}
    (p q : Pasting ((n + 1) + k + 1) G) (h : targetAt k (n + 1) p = sourceAt k (n + 1) q)
    (h' : targetAt k n (dropSource k n p) = sourceAt k n (dropSource k n q)) :
    dropSource k n (composeAt k (n + 1) p q h) =
      composeAt k n (dropSource k n p) (dropSource k n q) h' := by
  induction k generalizing G with
  | zero =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    change b = c at h
    cases h
    exact source_horizontal p q
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    have ha : a = c := _root_.congrArg Sigma.fst h
    have hb : b = d := _root_.congrArg (fun z => z.2.1) h
    cases ha
    cases hb
    have hp : p.map (fun e => targetAt k (n + 1) e) = q.map (fun e => sourceAt k (n + 1) e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
    have hp' : (p.map (fun e => dropSource k n e)).map (fun e => targetAt k n e) =
        (q.map (fun e => dropSource k n e)).map (fun e => sourceAt k n e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h').2)).2
    exact _root_.congrArg pack (Chain.map_zipOver
      (fun e => targetAt k (n + 1) e) (fun e => sourceAt k (n + 1) e)
      (fun e => targetAt k n e) (fun e => sourceAt k n e)
      (fun e d h => composeAt k (n + 1) e d h) (fun e d h => composeAt k n e d h)
      (fun e => dropSource k n e) (fun e d h j => ih e d h j) p q hp hp')

theorem dropTarget_composeAt (k n : Nat) {G : GlobularSet.{u}}
    (p q : Pasting ((n + 1) + k + 1) G) (h : targetAt k (n + 1) p = sourceAt k (n + 1) q)
    (h' : targetAt k n (dropTarget k n p) = sourceAt k n (dropTarget k n q)) :
    dropTarget k n (composeAt k (n + 1) p q h) =
      composeAt k n (dropTarget k n p) (dropTarget k n q) h' := by
  induction k generalizing G with
  | zero =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    change b = c at h
    cases h
    exact target_horizontal p q
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    have ha : a = c := _root_.congrArg Sigma.fst h
    have hb : b = d := _root_.congrArg (fun z => z.2.1) h
    cases ha
    cases hb
    have hp : p.map (fun e => targetAt k (n + 1) e) = q.map (fun e => sourceAt k (n + 1) e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
    have hp' : (p.map (fun e => dropTarget k n e)).map (fun e => targetAt k n e) =
        (q.map (fun e => dropTarget k n e)).map (fun e => sourceAt k n e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h').2)).2
    exact _root_.congrArg pack (Chain.map_zipOver
      (fun e => targetAt k (n + 1) e) (fun e => sourceAt k (n + 1) e)
      (fun e => targetAt k n e) (fun e => sourceAt k n e)
      (fun e d h => composeAt k (n + 1) e d h) (fun e d h => composeAt k n e d h)
      (fun e => dropTarget k n e) (fun e d h j => ih e d h j) p q hp hp')

/-- Adjacent source preserves composition with a derived, not assumed,
lower-dimensional composability witness. -/
theorem dropSource_composeAt_boundary (k n : Nat) {G : GlobularSet.{u}}
    (p q : Pasting ((n + 1) + k + 1) G) (h : targetAt k (n + 1) p = sourceAt k (n + 1) q) :
    dropSource k n (composeAt k (n + 1) p q h) =
      composeAt k n (dropSource k n p) (dropSource k n q)
        ((targetAt_dropSource k n p).trans (h.trans (sourceAt_dropSource k n q).symm)) :=
  dropSource_composeAt k n p q h _

theorem dropTarget_composeAt_boundary (k n : Nat) {G : GlobularSet.{u}}
    (p q : Pasting ((n + 1) + k + 1) G) (h : targetAt k (n + 1) p = sourceAt k (n + 1) q) :
    dropTarget k n (composeAt k (n + 1) p q h) =
      composeAt k n (dropTarget k n p) (dropTarget k n q)
        ((targetAt_dropTarget k n p).trans (h.trans (sourceAt_dropTarget k n q).symm)) :=
  dropTarget_composeAt k n p q h _

theorem dropSource_identityAt (k n : Nat) {G : GlobularSet.{u}} (p : Pasting k G) :
    dropSource k n (identityAt k (n + 1) p) = identityAt k n p := by
  induction k generalizing G with
  | zero => rfl
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    exact _root_.congrArg pack ((Chain.map_map _ _ p).trans (Chain.map_congr _ _ (fun e => ih e) p))

theorem dropTarget_identityAt (k n : Nat) {G : GlobularSet.{u}} (p : Pasting k G) :
    dropTarget k n (identityAt k (n + 1) p) = identityAt k n p := by
  induction k generalizing G with
  | zero => rfl
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    exact _root_.congrArg pack ((Chain.map_map _ _ p).trans (Chain.map_congr _ _ (fun e => ih e) p))

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

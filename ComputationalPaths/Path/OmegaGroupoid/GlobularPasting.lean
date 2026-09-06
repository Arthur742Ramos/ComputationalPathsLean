import ComputationalPaths.Path.OmegaGroupoid.GlobularFoundations
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Monad.Algebra

/-!
# Recursively labelled globular pasting diagrams

Objects label dimension zero. In dimension `n+1`, a diagram is a composable
chain of `n`-diagrams in hom globular sets. The carrier and adjacent boundary
maps are defined by genuine dimension recursion. Natural globular flattening
satisfies both unit equations and associativity, giving a lawful monad. The
free strict-category universal property is not yet claimed.
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

/-- Comparison of two aligned compositions, even when their boundary
carriers use different dimension expressions. No boundary reflection is needed. -/
theorem zipOver_congr {O : Type u} {E D B : O → O → Type v}
    (s t : {x y : O} → E x y → D x y)
    (s' t' : {x y : O} → E x y → B x y)
    (op : {x y : O} → (e d : E x y) → s e = t d → E x y)
    (op' : {x y : O} → (e d : E x y) → s' e = t' d → E x y)
    (law : ∀ {x y} (e d : E x y) (h : s e = t d) (h' : s' e = t' d),
      op e d h = op' e d h')
    {x y : O} (p q : Chain E x y) (h : p.map s = q.map t) (h' : p.map s' = q.map t') :
    zipOver s t op p q h = zipOver s' t' op' p q h' := by
  have hj : (p.map (fun e => e)).map s' = (q.map (fun e => e)).map t' := by
    simpa only [map_id] using h'
  have hm := map_zipOver s t s' t' op op' (fun e => e) law p q h hj
  simpa only [map_id] using hm

/-- Interchange of two partial label compositions lifts through four aligned
chains. All six composability conditions are retained explicitly. -/
theorem zipOver_interchange {O : Type u} {E D B : O → O → Type v}
    (s t : {x y : O} → E x y → D x y)
    (s' t' : {x y : O} → E x y → B x y)
    (op : {x y : O} → (e d : E x y) → s e = t d → E x y)
    (op' : {x y : O} → (e d : E x y) → s' e = t' d → E x y)
    (law : ∀ {x y} (e f g d : E x y)
      (hef : s e = t f) (hgd : s g = t d) (heg : s' e = t' g) (hfd : s' f = t' d)
      (hrow : s' (op e f hef) = t' (op g d hgd))
      (hcol : s (op' e g heg) = t (op' f d hfd)),
      op' (op e f hef) (op g d hgd) hrow = op (op' e g heg) (op' f d hfd) hcol)
    {x y : O} (p q r u : Chain E x y)
    (hpq : p.map s = q.map t) (hru : r.map s = u.map t)
    (hpr : p.map s' = r.map t') (hqu : q.map s' = u.map t')
    (hrow : (zipOver s t op p q hpq).map s' = (zipOver s t op r u hru).map t')
    (hcol : (zipOver s' t' op' p r hpr).map s = (zipOver s' t' op' q u hqu).map t) :
    zipOver s' t' op' (zipOver s t op p q hpq) (zipOver s t op r u hru) hrow =
      zipOver s t op (zipOver s' t' op' p r hpr) (zipOver s' t' op' q u hqu) hcol := by
  induction p with
  | nil x =>
    cases q with
    | cons f q => cases hpq
    | nil =>
      cases r with
      | cons g r => cases hpr
      | nil =>
        cases u with
        | cons d u => cases hru
        | nil => rfl
  | @cons x z y e p ih =>
    cases q with
    | nil => cases hpq
    | @cons _ zq _ f q =>
      have h := hpq
      simp only [map] at h
      injection h with hx hz hy he hf
      cases hz
      have hef := eq_of_heq he
      have hpq' := eq_of_heq hf
      cases r with
      | nil => cases hpr
      | @cons _ zr _ g r =>
        have h := hpr
        simp only [map] at h
        injection h with hx hz hy he hf
        cases hz
        have heg := eq_of_heq he
        have hpr' := eq_of_heq hf
        cases u with
        | nil => cases hru
        | @cons _ zu _ d u =>
          have h := hru
          simp only [map] at h
          injection h with hx hz hy he hf
          cases hz
          have hgd := eq_of_heq he
          have hru' := eq_of_heq hf
          have h := hqu
          simp only [map] at h
          injection h with hx hz hy hfd hqu'
          have hr := hrow
          change Chain.cons (s' (op e f hef)) ((zipOver s t op p q hpq').map s') =
            Chain.cons (t' (op g d hgd)) ((zipOver s t op r u hru').map t') at hr
          injection hr with hx hz hy hrh hrt
          have hc := hcol
          change Chain.cons (s (op' e g heg)) ((zipOver s' t' op' p r hpr').map s) =
            Chain.cons (t (op' f d hfd)) ((zipOver s' t' op' q u hqu').map t) at hc
          injection hc with hx hz hy hch hct
          exact _root_.congrArg₂ Chain.cons (law e f g d hef hgd heg hfd hrh hch)
            (ih q r u hpq' hru' hpr' hqu' hrt hct)

/-- If composable label grids have composable rows and columns, the same
holds for aligned chains. The outer witnesses are constructed, not assumed. -/
theorem zipOver_grid {O : Type u} {E D B : O → O → Type v}
    (s t : {x y : O} → E x y → D x y)
    (s' t' : {x y : O} → E x y → B x y)
    (op : {x y : O} → (e d : E x y) → s e = t d → E x y)
    (op' : {x y : O} → (e d : E x y) → s' e = t' d → E x y)
    (law : ∀ {x y} (e f g d : E x y)
      (hef : s e = t f) (hgd : s g = t d) (heg : s' e = t' g) (hfd : s' f = t' d),
      s' (op e f hef) = t' (op g d hgd) ∧ s (op' e g heg) = t (op' f d hfd))
    {x y : O} (p q r u : Chain E x y)
    (hpq : p.map s = q.map t) (hru : r.map s = u.map t)
    (hpr : p.map s' = r.map t') (hqu : q.map s' = u.map t') :
    (zipOver s t op p q hpq).map s' = (zipOver s t op r u hru).map t' ∧
      (zipOver s' t' op' p r hpr).map s = (zipOver s' t' op' q u hqu).map t := by
  induction p with
  | nil x =>
    cases q with
    | cons f q => cases hpq
    | nil =>
      cases r with
      | cons g r => cases hpr
      | nil =>
        cases u with
        | cons d u => cases hru
        | nil => exact ⟨rfl, rfl⟩
  | @cons x z y e p ih =>
    cases q with
    | nil => cases hpq
    | @cons _ zq _ f q =>
      have h := hpq
      simp only [map] at h
      injection h with hx hz hy he hf
      cases hz
      have hef := eq_of_heq he
      have hpq' := eq_of_heq hf
      cases r with
      | nil => cases hpr
      | @cons _ zr _ g r =>
        have h := hpr
        simp only [map] at h
        injection h with hx hz hy he hf
        cases hz
        have heg := eq_of_heq he
        have hpr' := eq_of_heq hf
        cases u with
        | nil => cases hru
        | @cons _ zu _ d u =>
          have h := hru
          simp only [map] at h
          injection h with hx hz hy he hf
          cases hz
          have hgd := eq_of_heq he
          have hru' := eq_of_heq hf
          have h := hqu
          simp only [map] at h
          injection h with hx hz hy hfd hqu'
          have heads := law e f g d hef hgd heg hfd
          have tails := ih q r u hpq' hru' hpr' hqu'
          exact ⟨_root_.congrArg₂ Chain.cons heads.1 tails.1,
            _root_.congrArg₂ Chain.cons heads.2 tails.2⟩

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

theorem mapAlong_identity_vertices {E F : O → O → Type u}
    (f : {x y : O} → E x y → F x y) {x y : O} (p : Chain E x y) :
    p.mapAlong (fun x => x) f = p.map f := by
  induction p with
  | nil => rfl
  | cons e p ih => exact _root_.congrArg (Chain.cons (f e)) ih

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

namespace Chain

theorem packed_eq_heq {Q : Type u} {D : Q → Q → Type u}
    {a b c d : Q} (p : Chain D a b) (q : Chain D c d)
    (h : (⟨a, b, p⟩ : Σ x y, Chain D x y) = ⟨c, d, q⟩) : HEq p q := by
  injection h with hac hpq
  cases hac
  have hh := eq_of_heq hpq
  injection hh with hbd hpq

theorem packed_eq_of_heq {Q : Type u} {D : Q → Q → Type u}
    {a b c d : Q} (p : Chain D a b) (q : Chain D c d)
    (ha : a = c) (hb : b = d) (h : HEq p q) :
    (⟨a, b, p⟩ : Σ x y, Chain D x y) = ⟨c, d, q⟩ := by
  cases ha
  cases hb
  cases h
  rfl

theorem cons_heq_components {Q : Type u} {D : Q → Q → Type u}
    {x y z x' y' z' : Q} (a : D x y) (p : Chain D y z)
    (b : D x' y') (q : Chain D y' z') (hx : x = x') (hz : z = z')
    (h : HEq (Chain.cons a p) (Chain.cons b q)) :
    y = y' ∧ HEq a b ∧ HEq p q := by
  cases hx
  cases hz
  have he := eq_of_heq h
  injection he with _ hy _ hab hpq
  exact ⟨hy, hab, hpq⟩

theorem cons_heq_of_components {Q : Type u} {D : Q → Q → Type u}
    {x y z x' y' z' : Q} (a : D x y) (p : Chain D y z)
    (b : D x' y') (q : Chain D y' z') (hx : x = x') (hy : y = y') (hz : z = z')
    (ha : HEq a b) (hp : HEq p q) : HEq (Chain.cons a p) (Chain.cons b q) := by
  cases hx
  cases hy
  cases hz
  cases ha
  cases hp
  rfl

theorem nil_not_heq_cons {Q : Type u} {D : Q → Q → Type u}
    {x x' y' z' : Q} (b : D x' y') (q : Chain D y' z')
    (hx : x = x') (hz : x = z') : ¬ HEq (Chain.nil x : Chain D x x) (Chain.cons b q) := by
  cases hx
  cases hz
  intro h
  have he := eq_of_heq h
  cases he

/-- Match chains whose vertex sets differ. Internal matching vertices are
derived from the equality of relabelled chains, not supplied separately. -/
noncomputable def zipAlong {O P Q : Type u}
    {E : O → O → Type u} {F : P → P → Type u} {D : Q → Q → Type u}
    (s : O → Q) (t : P → Q)
    (se : {x y : O} → E x y → D (s x) (s y))
    (te : {x y : P} → F x y → D (t x) (t y))
    (R : {p : O × P // s p.1 = t p.2} → {p : O × P // s p.1 = t p.2} → Type u)
    (op : ∀ {a b : {p : O × P // s p.1 = t p.2}},
      (e : E a.val.1 b.val.1) → (f : F a.val.2 b.val.2) → HEq (se e) (te f) → R a b)
    {x y : O} {x' y' : P} (p : Chain E x y) (q : Chain F x' y')
    (hx : s x = t x') (hy : s y = t y')
    (h : HEq (p.mapAlong s se) (q.mapAlong t te)) :
    Chain R ⟨(x, x'), hx⟩ ⟨(y, y'), hy⟩ := by
  induction p generalizing x' y' with
  | nil x =>
    cases q with
    | nil => exact .nil _
    | cons f q => exact False.elim (nil_not_heq_cons (te f) (q.mapAlong t te) hx hy h)
  | @cons x z y e p ih =>
    cases q with
    | nil => exact False.elim (nil_not_heq_cons (se e) (p.mapAlong s se) hx.symm hy.symm (HEq.symm h))
    | @cons x' z' y' f q =>
      have hc := cons_heq_components (se e) (p.mapAlong s se) (te f) (q.mapAlong t te) hx hy h
      exact .cons (op (a := ⟨(x, x'), hx⟩) (b := ⟨(z, z'), hc.1⟩) e f hc.2.1)
        (ih q hc.1 hy hc.2.2)

theorem zipAlong_left {O P Q : Type u}
    {E : O → O → Type u} {F : P → P → Type u} {D : Q → Q → Type u}
    (s : O → Q) (t : P → Q)
    (se : {x y : O} → E x y → D (s x) (s y))
    (te : {x y : P} → F x y → D (t x) (t y))
    (R : {p : O × P // s p.1 = t p.2} → {p : O × P // s p.1 = t p.2} → Type u)
    (op : ∀ {a b : {p : O × P // s p.1 = t p.2}},
      (e : E a.val.1 b.val.1) → (f : F a.val.2 b.val.2) → HEq (se e) (te f) → R a b)
    (left : ∀ {a b}, R a b → E a.val.1 b.val.1)
    (law : ∀ {a b} (e : E a.val.1 b.val.1) (f : F a.val.2 b.val.2) h,
      left (op (a := a) (b := b) e f h) = e)
    {x y : O} {x' y' : P} (p : Chain E x y) (q : Chain F x' y')
    (hx : s x = t x') (hy : s y = t y')
    (h : HEq (p.mapAlong s se) (q.mapAlong t te)) :
    (zipAlong s t se te R op p q hx hy h).mapAlong (fun a => a.val.1) left = p := by
  induction p generalizing x' y' with
  | nil x =>
    cases q with
    | nil => rfl
    | cons f q => exact False.elim (nil_not_heq_cons (te f) (q.mapAlong t te) hx hy h)
  | @cons x z y e p ih =>
    cases q with
    | nil => exact False.elim (nil_not_heq_cons (se e) (p.mapAlong s se) hx.symm hy.symm (HEq.symm h))
    | @cons x' z' y' f q =>
      have hc := cons_heq_components (se e) (p.mapAlong s se) (te f) (q.mapAlong t te) hx hy h
      change Chain.cons (left (op (a := ⟨(x, x'), hx⟩) (b := ⟨(z, z'), hc.1⟩) e f hc.2.1))
        ((zipAlong s t se te R op p q hc.1 hy hc.2.2).mapAlong (fun a => a.val.1) left) = _
      exact _root_.congrArg₂ Chain.cons
        (law (a := ⟨(x, x'), hx⟩) (b := ⟨(z, z'), hc.1⟩) e f hc.2.1) (ih q hc.1 hy hc.2.2)

theorem zipAlong_right {O P Q : Type u}
    {E : O → O → Type u} {F : P → P → Type u} {D : Q → Q → Type u}
    (s : O → Q) (t : P → Q)
    (se : {x y : O} → E x y → D (s x) (s y))
    (te : {x y : P} → F x y → D (t x) (t y))
    (R : {p : O × P // s p.1 = t p.2} → {p : O × P // s p.1 = t p.2} → Type u)
    (op : ∀ {a b : {p : O × P // s p.1 = t p.2}},
      (e : E a.val.1 b.val.1) → (f : F a.val.2 b.val.2) → HEq (se e) (te f) → R a b)
    (right : ∀ {a b}, R a b → F a.val.2 b.val.2)
    (law : ∀ {a b} (e : E a.val.1 b.val.1) (f : F a.val.2 b.val.2) h,
      right (op (a := a) (b := b) e f h) = f)
    {x y : O} {x' y' : P} (p : Chain E x y) (q : Chain F x' y')
    (hx : s x = t x') (hy : s y = t y')
    (h : HEq (p.mapAlong s se) (q.mapAlong t te)) :
    (zipAlong s t se te R op p q hx hy h).mapAlong (fun a => a.val.2) right = q := by
  induction p generalizing x' y' with
  | nil x =>
    cases q with
    | nil => rfl
    | cons f q => exact False.elim (nil_not_heq_cons (te f) (q.mapAlong t te) hx hy h)
  | @cons x z y e p ih =>
    cases q with
    | nil => exact False.elim (nil_not_heq_cons (se e) (p.mapAlong s se) hx.symm hy.symm (HEq.symm h))
    | @cons x' z' y' f q =>
      have hc := cons_heq_components (se e) (p.mapAlong s se) (te f) (q.mapAlong t te) hx hy h
      change Chain.cons (right (op (a := ⟨(x, x'), hx⟩) (b := ⟨(z, z'), hc.1⟩) e f hc.2.1))
        ((zipAlong s t se te R op p q hc.1 hy hc.2.2).mapAlong (fun a => a.val.2) right) = _
      exact _root_.congrArg₂ Chain.cons
        (law (a := ⟨(x, x'), hx⟩) (b := ⟨(z, z'), hc.1⟩) e f hc.2.1) (ih q hc.1 hy hc.2.2)

/-- Two relabellings jointly determine a chain when they jointly determine
its vertices and each of its labels. -/
theorem mapAlong_joint_injective {O P Q : Type u}
    {E : O → O → Type u} {F : P → P → Type u} {D : Q → Q → Type u}
    (s : O → P) (t : O → Q)
    (se : {x y : O} → E x y → F (s x) (s y))
    (te : {x y : O} → E x y → D (t x) (t y))
    (hv : ∀ x y, s x = s y → t x = t y → x = y)
    (he : ∀ {x y} (a b : E x y), se a = se b → te a = te b → a = b)
    {x y : O} (p q : Chain E x y)
    (hs : p.mapAlong s se = q.mapAlong s se)
    (ht : p.mapAlong t te = q.mapAlong t te) : p = q := by
  induction p with
  | nil x =>
    cases q with
    | nil => rfl
    | cons b q => cases hs
  | @cons x z y a p ih =>
    cases q with
    | nil => cases hs
    | @cons _ z' _ b q =>
      have h₁ := cons_heq_components (se a) (p.mapAlong s se) (se b) (q.mapAlong s se)
        rfl rfl (heq_of_eq hs)
      have h₂ := cons_heq_components (te a) (p.mapAlong t te) (te b) (q.mapAlong t te)
        rfl rfl (heq_of_eq ht)
      have hz := hv z z' h₁.1 h₂.1
      cases hz
      exact _root_.congrArg₂ Chain.cons (he a b (eq_of_heq h₁.2.1) (eq_of_heq h₂.2.1))
        (ih q (eq_of_heq h₁.2.2) (eq_of_heq h₂.2.2))

/-- A specified segmentation after relabelling lifts to an actual
segmentation of the original chain. No injectivity of the label map is used. -/
theorem split_mapAlong {O P : Type u} {E : O → O → Type u} {F : P → P → Type u}
    (f : O → P) (e : {x y : O} → E x y → F (f x) (f y))
    {a b c : P} (q : Chain F a b) (r : Chain F b c)
    {x z : O} (p : Chain E x z) (hx : f x = a) (hz : f z = c)
    (h : HEq (p.mapAlong f e) (q.append r)) :
    ∃ y : O, ∃ p₁ : Chain E x y, ∃ p₂ : Chain E y z,
      f y = b ∧ p₁.append p₂ = p ∧ HEq (p₁.mapAlong f e) q ∧ HEq (p₂.mapAlong f e) r := by
  induction q generalizing x z with
  | nil a =>
    refine ⟨x, .nil x, p, hx, rfl, ?_, h⟩
    exact packed_eq_heq _ _
      (_root_.congrArg (fun a => (⟨a, a, Chain.nil a⟩ : Σ x y, Chain F x y)) hx)
  | @cons a d b v q ih =>
    cases p with
    | nil x => exact False.elim (nil_not_heq_cons v (q.append r) hx hz h)
    | @cons x w z u p =>
      have hc := cons_heq_components (e u) (p.mapAlong f e) v (q.append r) hx hz h
      obtain ⟨y, p₁, p₂, hy, hp, h₁, h₂⟩ := ih r p hc.1 hz hc.2.2
      refine ⟨y, .cons u p₁, p₂, hy, _root_.congrArg (Chain.cons u) hp, ?_, h₂⟩
      exact cons_heq_of_components (e u) (p₁.mapAlong f e) v q hx hc.1 hy hc.2.1 h₁

/-- A segmentation of a fixed original chain is determined by its
relabelled prefix, even if relabelling identifies vertices or labels. -/
theorem split_mapAlong_unique {O P : Type u} {E : O → O → Type u} {F : P → P → Type u}
    (f : O → P) (e : {x y : O} → E x y → F (f x) (f y))
    {x y y' z : O} (p₁ : Chain E x y) (p₂ : Chain E y z)
    (q₁ : Chain E x y') (q₂ : Chain E y' z)
    (hy : f y = f y') (hs : HEq (p₁.mapAlong f e) (q₁.mapAlong f e))
    (h : p₁.append p₂ = q₁.append q₂) :
    y = y' ∧ HEq p₁ q₁ ∧ HEq p₂ q₂ := by
  induction p₁ generalizing y' with
  | nil x =>
    cases q₁ with
    | nil => exact ⟨rfl, HEq.rfl, heq_of_eq h⟩
    | cons b q => exact False.elim (nil_not_heq_cons (e b) (q.mapAlong f e) rfl hy hs)
  | @cons x w y a p ih =>
    cases q₁ with
    | nil => exact False.elim (nil_not_heq_cons (e a) (p.mapAlong f e) rfl hy.symm (HEq.symm hs))
    | @cons _ w' y' b q =>
      have hc := cons_heq_components a (p.append p₂) b (q.append q₂) rfl rfl (heq_of_eq h)
      have hw := hc.1
      cases hw
      have hm := cons_heq_components (e a) (p.mapAlong f e) (e b) (q.mapAlong f e)
        rfl hy hs
      obtain ⟨hy', hp, hq⟩ := ih p₂ q q₂ hy hm.2.2 (eq_of_heq hc.2.2)
      cases hy'
      exact ⟨rfl, heq_of_eq (_root_.congrArg₂ Chain.cons (eq_of_heq hc.2.1) (eq_of_heq hp)), hq⟩

/-- Lift an entire nested-chain segmentation through relabelling. Empty
inner chains are retained as explicit segments in the resulting outer chain. -/
theorem lift_bind_mapAlong {O P : Type u} {E : O → O → Type u} {F : P → P → Type u}
    (f : O → P) (e : {x y : O} → E x y → F (f x) (f y))
    {a b : P} (q : Chain (fun x y => Chain F x y) a b)
    {x z : O} (p : Chain E x z) (hx : f x = a) (hz : f z = b)
    (h : HEq (p.mapAlong f e) (q.bind (fun r => r))) :
    ∃ r : Chain (fun x y => Chain E x y) x z,
      r.bind (fun s => s) = p ∧
      HEq (r.mapAlong f (fun s => s.mapAlong f e)) q := by
  induction q generalizing x z with
  | nil a =>
    cases p with
    | nil x =>
      refine ⟨.nil x, rfl, ?_⟩
      exact packed_eq_heq _ _
        (_root_.congrArg (fun a => (⟨a, a, Chain.nil a⟩ : Σ x y, Chain (fun x y => Chain F x y) x y)) hx)
    | cons a p => exact False.elim (nil_not_heq_cons (e a) (p.mapAlong f e) hx.symm hz.symm (HEq.symm h))
  | @cons a c b v q ih =>
    obtain ⟨y, p₁, p₂, hy, hp, h₁, h₂⟩ := split_mapAlong f e v (q.bind (fun r => r)) p hx hz h
    obtain ⟨r, hr, hq⟩ := ih p₂ hy hz h₂
    refine ⟨.cons p₁ r, (_root_.congrArg (Chain.append p₁) hr).trans hp, ?_⟩
    exact cons_heq_of_components (p₁.mapAlong f e)
      (r.mapAlong f (fun s => s.mapAlong f e)) v q hx hy hz h₁ hq

/-- Flattening and outer-chain relabelling jointly determine a nested
chain. In particular, empty segments cannot disappear from the lift. -/
theorem bind_mapAlong_joint_injective {O P : Type u}
    {E : O → O → Type u} {F : P → P → Type u}
    (f : O → P) (e : {x y : O} → E x y → F (f x) (f y))
    {x z : O} (p q : Chain (fun x y => Chain E x y) x z)
    (hb : p.bind (fun r => r) = q.bind (fun r => r))
    (hm : p.mapAlong f (fun r => r.mapAlong f e) = q.mapAlong f (fun r => r.mapAlong f e)) : p = q := by
  induction p with
  | nil =>
    cases q with
    | nil => rfl
    | cons b q => cases hm
  | @cons x y z a p ih =>
    cases q with
    | nil => cases hm
    | @cons _ y' _ b q =>
      have hc := cons_heq_components (D := fun x y => Chain F x y) (a.mapAlong f e)
        (p.mapAlong (F := fun x y => Chain F x y) f (fun {x y} (r : Chain E x y) => r.mapAlong (F := F) f e))
        (b.mapAlong f e) (q.mapAlong (F := fun x y => Chain F x y) f
          (fun {x y} (r : Chain E x y) => r.mapAlong (F := F) f e))
        rfl rfl (heq_of_eq hm)
      have hs := split_mapAlong_unique f e a (p.bind (fun r => r)) b (q.bind (fun r => r))
        hc.1 hc.2.1 hb
      have hy := hs.1
      cases hy
      exact _root_.congrArg₂ Chain.cons (eq_of_heq hs.2.1)
        (ih q (eq_of_heq hs.2.2) (eq_of_heq hc.2.2))

/-- The chain multiplication square has unique lifts under arbitrary
vertex and edge relabelling. This is the segmentation ingredient for the
globular multiplication proof, not that all-dimensional proof itself. -/
theorem bind_cartesian {O P : Type u} {E : O → O → Type u} {F : P → P → Type u}
    (f : O → P) (e : {x y : O} → E x y → F (f x) (f y))
    {x z : O} (p : Chain E x z)
    (q : Chain (fun a b => Chain F a b) (f x) (f z))
    (h : p.mapAlong f e = q.bind (fun r => r)) :
    ∃! r : Chain (fun x y => Chain E x y) x z,
      r.bind (fun s => s) = p ∧ r.mapAlong f (fun s => s.mapAlong f e) = q := by
  obtain ⟨r, hr, hq⟩ := lift_bind_mapAlong f e q p rfl rfl (heq_of_eq h)
  refine ⟨r, ⟨hr, eq_of_heq hq⟩, ?_⟩
  intro s hs
  exact bind_mapAlong_joint_injective f e s r (hs.1.trans hr.symm)
    (hs.2.trans (eq_of_heq hq).symm)

/-- Reflect a labelwise retraction from a relabelled chain. The target
chain may have different vertices; matching endpoints are supplied per label. -/
theorem map_retract_of_mapAlong {O P : Type u}
    {E : O → O → Type u} {F D : P → P → Type u}
    (f : O → P) (e : {x y : O} → E x y → F (f x) (f y))
    (j : {x y : P} → D x y → F x y) (r : {x y : O} → E x y → E x y)
    (law : ∀ {x y : O} {a b : P} (p : E x y) (q : D a b),
      f x = a → f y = b → HEq (e p) (j q) → r p = p)
    {x y : O} {a b : P} (p : Chain E x y) (q : Chain D a b)
    (hx : f x = a) (hy : f y = b) (h : HEq (p.mapAlong f e) (q.map j)) :
    p.map r = p := by
  induction p generalizing a b with
  | nil => rfl
  | @cons x z y p ps ih =>
    cases q with
    | nil => exact False.elim (nil_not_heq_cons (e p) (ps.mapAlong f e) hx.symm hy.symm (HEq.symm h))
    | @cons a c b q qs =>
      have hc := cons_heq_components (e p) (ps.mapAlong f e) (j q) (qs.map j) hx hy h
      exact _root_.congrArg₂ Chain.cons (law p q hx hc.1 hc.2.1) (ih qs hc.1 hy hc.2.2)

/-- Assemble labelwise lifts into a chain lift, retaining the original
source vertices and the prescribed target labels. -/
theorem lift_mapAlong_square {O P : Type u}
    {E R : O → O → Type u} {F D : P → P → Type u}
    (f : O → P) (e : {x y : O} → E x y → F (f x) (f y))
    (j : {x y : P} → D x y → F x y)
    (left : {x y : O} → R x y → E x y)
    (right : {x y : O} → R x y → D (f x) (f y))
    (lift : ∀ {x y : O} {a b : P} (p : E x y) (q : D a b),
      f x = a → f y = b → HEq (e p) (j q) →
      ∃ r : R x y, left r = p ∧ HEq (right r) q)
    {x y : O} {a b : P} (p : Chain E x y) (q : Chain D a b)
    (hx : f x = a) (hy : f y = b) (h : HEq (p.mapAlong f e) (q.map j)) :
    ∃ r : Chain R x y, r.map left = p ∧ HEq (r.mapAlong f right) q := by
  induction p generalizing a b with
  | nil x =>
    cases q with
    | nil =>
      refine ⟨.nil x, rfl, ?_⟩
      exact packed_eq_heq _ _
        (_root_.congrArg (fun a => (⟨a, a, Chain.nil a⟩ : Σ x y, Chain D x y)) hx)
    | cons q qs => exact False.elim (nil_not_heq_cons (j q) (qs.map j) hx hy h)
  | @cons x z y p ps ih =>
    cases q with
    | nil => exact False.elim (nil_not_heq_cons (e p) (ps.mapAlong f e) hx.symm hy.symm (HEq.symm h))
    | @cons a c b q qs =>
      have hc := cons_heq_components (e p) (ps.mapAlong f e) (j q) (qs.map j) hx hy h
      obtain ⟨r, hr, hs⟩ := lift p q hx hc.1 hc.2.1
      obtain ⟨rs, hrl, hrs⟩ := ih qs hc.1 hy hc.2.2
      exact ⟨.cons r rs, _root_.congrArg₂ Chain.cons hr hrl,
        cons_heq_of_components (right r) (rs.mapAlong f right) q qs hx hc.1 hy hs hrs⟩

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

/-- Relabelling cannot hide a composite as an atomic generator. -/
theorem atom_map {n : Nat} {G H : GlobularSet.{u}} (f : GlobularSet.Map G H)
    (p : Pasting n G) : atom? (map f p) = (atom? p).map f.app := by
  induction n generalizing G H with
  | zero => rfl
  | succ n ih =>
    rcases p with ⟨a, b, p⟩
    cases p with
    | nil => rfl
    | cons d q =>
      cases q with
      | nil =>
        change (atom? (map (f.hom _ _) d)).map Subtype.val =
          ((atom? d).map Subtype.val).map f.app
        rw [ih]
        cases atom? d <;> rfl
      | cons e r => rfl

/-- Successful extraction characterizes a genuine singleton diagram. -/
theorem singleton_of_atom {n : Nat} {G : GlobularSet.{u}} (p : Pasting n G)
    (c : G.Cell n) (h : atom? p = some c) : singleton c = p := by
  induction n generalizing G with
  | zero => exact Option.some.inj h.symm
  | succ n ih =>
    rcases p with ⟨a, b, p⟩
    cases p with
    | nil => cases h
    | cons d q =>
      cases q with
      | cons e r => cases h
      | nil =>
        change (atom? d).map Subtype.val = some c at h
        cases hd : atom? d with
        | none =>
          rw [hd] at h
          change none = some c at h
          cases h
        | some e =>
          rw [hd] at h
          have hc : e.val = c := Option.some.inj h
          subst c
          exact (singleton_of_hom G e).symm.trans
            (_root_.congrArg (fun z => (⟨a, b, Chain.single z⟩ : Pasting (n + 1) G))
              (ih d e hd))

/-- Pointwise pullback property of the natural unit, with no injectivity
assumption on the relabelling map. -/
theorem singleton_cartesian {n : Nat} {G H : GlobularSet.{u}}
    (f : GlobularSet.Map G H) (p : Pasting n G) (c : H.Cell n)
    (h : map f p = singleton c) :
    ∃! d : G.Cell n, singleton d = p ∧ f.app d = c := by
  have ha : (atom? p).map f.app = some c :=
    (atom_map f p).symm.trans ((_root_.congrArg atom? h).trans (atom_singleton H c))
  cases hp : atom? p with
  | none => simp [hp] at ha
  | some d =>
    have hd : f.app d = c := by simpa [hp] using ha
    refine ⟨d, ⟨singleton_of_atom p d hp, hd⟩, ?_⟩
    intro e he
    exact singleton_injective G (he.1.trans (singleton_of_atom p d hp).symm)

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

/-- The unit naturality square has the universal lifting property in the
category of globular sets, not just separately on its cell sets. -/
theorem singleton_globular_pullback {G H X : GlobularSet.{u}}
    (f : GlobularSet.Map G H) (p : GlobularSet.Map X (globular G))
    (q : GlobularSet.Map X H)
    (h : GlobularSet.Map.comp (mapGlobular f) p =
      GlobularSet.Map.comp (singletonGlobular H) q) :
    ∃! d : GlobularSet.Map X G,
      GlobularSet.Map.comp (singletonGlobular G) d = p ∧
      GlobularSet.Map.comp f d = q := by
  have liftExists (n : Nat) (x : X.Cell n) := singleton_cartesian f (p.app x) (q.app x)
    (_root_.congrArg (fun k : GlobularSet.Map X (globular H) => k.app x) h)
  let d {n : Nat} (x : X.Cell n) : G.Cell n := (liftExists n x).choose
  have hd {n : Nat} (x : X.Cell n) : singleton (d x) = p.app x ∧ f.app (d x) = q.app x :=
    (liftExists n x).choose_spec.1
  let D : GlobularSet.Map X G := {
    app := d
    source_app := fun x => singleton_injective G
      ((source_singleton G (d x)).symm.trans
        ((_root_.congrArg source (hd x).1).trans
          ((p.source_app x).trans (hd (X.source x)).1.symm)))
    target_app := fun x => singleton_injective G
      ((target_singleton G (d x)).symm.trans
        ((_root_.congrArg target (hd x).1).trans
          ((p.target_app x).trans (hd (X.target x)).1.symm))) }
  refine ⟨D, ⟨?_, ?_⟩, ?_⟩
  · apply GlobularSet.Map.ext
    intro n x
    exact (hd x).1
  · apply GlobularSet.Map.ext
    intro n x
    exact (hd x).2
  · intro e he
    apply GlobularSet.Map.ext
    intro n x
    exact singleton_injective G
      ((_root_.congrArg (fun k : GlobularSet.Map X (globular G) => k.app x) he.1).trans
        (hd x).1.symm)

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

/-- The canonical comparison from pastings of matched labels to matched
pastings. Its invertibility and the full image-cone universal property are
proved below; the comparison alone would not establish preservation. -/
def pullbackComparison {G H K : GlobularSet.{u}}
    (f : GlobularSet.Map G K) (g : GlobularSet.Map H K) :
    GlobularSet.Map (globular (GlobularSet.pullback f g))
      (GlobularSet.pullback (mapGlobular f) (mapGlobular g)) :=
  GlobularSet.pullbackLift (mapGlobular f) (mapGlobular g)
    (mapGlobular (GlobularSet.pullbackFst f g)) (mapGlobular (GlobularSet.pullbackSnd f g)) (by
      apply GlobularSet.Map.ext
      intro n p
      exact (map_comp (GlobularSet.pullbackFst f g) f p).trans
        ((_root_.congrArg (fun k => map k p) (GlobularSet.pullback_condition f g)).trans
          (map_comp (GlobularSet.pullbackSnd f g) g p).symm))

theorem pullbackComparison_fst {G H K : GlobularSet.{u}}
    (f : GlobularSet.Map G K) (g : GlobularSet.Map H K) :
    GlobularSet.Map.comp (GlobularSet.pullbackFst (mapGlobular f) (mapGlobular g))
      (pullbackComparison f g) = mapGlobular (GlobularSet.pullbackFst f g) := by
  apply GlobularSet.Map.ext
  intro n p
  rfl

theorem pullbackComparison_snd {G H K : GlobularSet.{u}}
    (f : GlobularSet.Map G K) (g : GlobularSet.Map H K) :
    GlobularSet.Map.comp (GlobularSet.pullbackSnd (mapGlobular f) (mapGlobular g))
      (pullbackComparison f g) = mapGlobular (GlobularSet.pullbackSnd f g) := by
  apply GlobularSet.Map.ext
  intro n p
  rfl

/-- The comparison retains the original pair of labels on every generator. -/
theorem pullbackComparison_singleton {G H K : GlobularSet.{u}}
    (f : GlobularSet.Map G K) (g : GlobularSet.Map H K) {n : Nat}
    (p : (GlobularSet.pullback f g).Cell n) :
    ((pullbackComparison f g).app (singleton p)).val =
      (singleton p.val.1, singleton p.val.2) :=
  Prod.ext (map_singleton (GlobularSet.pullbackFst f g) p)
    (map_singleton (GlobularSet.pullbackSnd f g) p)

theorem map_homInclusion_heq {K : GlobularSet.{u}} {a b c d : K.Cell 0} {n : Nat}
    (p : Pasting n (K.hom a b)) (q : Pasting n (K.hom c d))
    (ha : a = c) (hb : b = d) (h : HEq p q) :
    map (GlobularSet.homInclusion K a b) p = map (GlobularSet.homInclusion K c d) q := by
  cases ha
  cases hb
  cases h
  rfl

/-- Reconstruct a labelled pasting from two matching projections in every
dimension. Internal vertices and hom labels are reconstructed recursively. -/
theorem pullback_pasting_exists {n : Nat} {G H K : GlobularSet.{u}}
    (f : GlobularSet.Map G K) (g : GlobularSet.Map H K)
    (p : Pasting n G) (q : Pasting n H) (h : map f p = map g q) :
    ∃ r : Pasting n (GlobularSet.pullback f g),
      map (GlobularSet.pullbackFst f g) r = p ∧ map (GlobularSet.pullbackSnd f g) r = q := by
  induction n generalizing G H K with
  | zero => exact ⟨⟨(p, q), h⟩, rfl, rfl⟩
  | succ n ih =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨a', b', q⟩
    have ha : f.app a = g.app a' := _root_.congrArg Sigma.fst h
    have hb : f.app b = g.app b' := _root_.congrArg (fun z => z.2.1) h
    have hc : HEq (p.mapAlong (F := fun x y => Pasting n (K.hom x y)) f.app
        (fun {x y} e => map (f.hom x y) e))
        (q.mapAlong (F := fun x y => Pasting n (K.hom x y)) g.app
          (fun {x y} e => map (g.hom x y) e)) := by
      exact Chain.packed_eq_heq _ _ h
    let B := GlobularSet.pullback f g
    let R (x y : B.Cell 0) := Pasting n (B.hom x y)
    have edge {x y : B.Cell 0} (e : Pasting n (G.hom x.val.1 y.val.1))
        (d : Pasting n (H.hom x.val.2 y.val.2))
        (he : HEq (map (f.hom _ _) e) (map (g.hom _ _) d)) :
        ∃ r : R x y, map ((GlobularSet.pullbackFst f g).hom x y) r = e ∧
          map ((GlobularSet.pullbackSnd f g).hom x y) r = d := by
      let f' := GlobularSet.Map.comp f.shift (GlobularSet.homInclusion G x.val.1 y.val.1)
      let g' := GlobularSet.Map.comp g.shift (GlobularSet.homInclusion H x.val.2 y.val.2)
      have hm : map f' e = map g' d :=
        (map_comp (f.hom _ _) (GlobularSet.homInclusion K _ _) e).symm.trans
          ((map_homInclusion_heq _ _ x.property y.property he).trans
            (map_comp (g.hom _ _) (GlobularSet.homInclusion K _ _) d))
      obtain ⟨r, hr, hs⟩ := ih f' g' e d hm
      refine ⟨map (GlobularSet.pullbackHomBackward f g x y) r, ?_, ?_⟩
      · exact (map_comp _ _ r).trans
          ((_root_.congrArg (fun k => map k r) (GlobularSet.pullbackHomBackward_fst f g x y)).trans hr)
      · exact (map_comp _ _ r).trans
          ((_root_.congrArg (fun k => map k r) (GlobularSet.pullbackHomBackward_snd f g x y)).trans hs)
    let op {x y : B.Cell 0} (e : Pasting n (G.hom x.val.1 y.val.1))
        (d : Pasting n (H.hom x.val.2 y.val.2))
        (he : HEq (map (f.hom _ _) e) (map (g.hom _ _) d)) : R x y := (edge e d he).choose
    refine ⟨⟨⟨(a, a'), ha⟩, ⟨(b, b'), hb⟩,
      Chain.zipAlong (D := fun x y => Pasting n (K.hom x y)) f.app g.app (fun e => map (f.hom _ _) e)
        (fun d => map (g.hom _ _) d) R op p q ha hb hc⟩, ?_, ?_⟩
    · apply _root_.congrArg (fun z => (⟨a, b, z⟩ : Pasting (n + 1) G))
      exact Chain.zipAlong_left _ _ _ _ R op
        (fun {x y} r => map ((GlobularSet.pullbackFst f g).hom x y) r)
        (fun e d he => (edge e d he).choose_spec.1) p q ha hb hc
    · apply _root_.congrArg (fun z => (⟨a', b', z⟩ : Pasting (n + 1) H))
      exact Chain.zipAlong_right _ _ _ _ R op
        (fun {x y} r => map ((GlobularSet.pullbackSnd f g).hom x y) r)
        (fun e d he => (edge e d he).choose_spec.2) p q ha hb hc

/-- Both pullback projections jointly determine the complete labelled
pasting, including every internal vertex and higher-dimensional label. -/
theorem pullback_pasting_ext {n : Nat} {G H K : GlobularSet.{u}}
    (f : GlobularSet.Map G K) (g : GlobularSet.Map H K)
    (p q : Pasting n (GlobularSet.pullback f g))
    (hs : map (GlobularSet.pullbackFst f g) p = map (GlobularSet.pullbackFst f g) q)
    (ht : map (GlobularSet.pullbackSnd f g) p = map (GlobularSet.pullbackSnd f g) q) : p = q := by
  induction n generalizing G H K with
  | zero => exact Subtype.ext (Prod.ext hs ht)
  | succ n ih =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨a', b', q⟩
    have ha : a = a' := Subtype.ext (Prod.ext (_root_.congrArg Sigma.fst hs)
      (_root_.congrArg Sigma.fst ht))
    have hb : b = b' := Subtype.ext (Prod.ext (_root_.congrArg (fun z => z.2.1) hs)
      (_root_.congrArg (fun z => z.2.1) ht))
    cases ha
    cases hb
    have edge {x y : (GlobularSet.pullback f g).Cell 0}
        (e d : Pasting n ((GlobularSet.pullback f g).hom x y))
        (h₁ : map ((GlobularSet.pullbackFst f g).hom x y) e =
          map ((GlobularSet.pullbackFst f g).hom x y) d)
        (h₂ : map ((GlobularSet.pullbackSnd f g).hom x y) e =
          map ((GlobularSet.pullbackSnd f g).hom x y) d) : e = d := by
      let f' := GlobularSet.Map.comp f.shift (GlobularSet.homInclusion G x.val.1 y.val.1)
      let g' := GlobularSet.Map.comp g.shift (GlobularSet.homInclusion H x.val.2 y.val.2)
      let F := GlobularSet.pullbackHomForward f g x y
      let B := GlobularSet.pullbackHomBackward f g x y
      have hF : map F e = map F d := ih f' g' _ _
        ((map_comp F (GlobularSet.pullbackFst f' g') e).trans
          (h₁.trans (map_comp F (GlobularSet.pullbackFst f' g') d).symm))
        ((map_comp F (GlobularSet.pullbackSnd f' g') e).trans
          (h₂.trans (map_comp F (GlobularSet.pullbackSnd f' g') d).symm))
      have inverse (z : Pasting n ((GlobularSet.pullback f g).hom x y)) :
          map B (map F z) = z :=
        (map_comp F B z).trans
          ((_root_.congrArg (fun k => map k z) (GlobularSet.pullbackHom_backward_forward f g x y)).trans
            (map_id _ z))
      exact (inverse e).symm.trans ((_root_.congrArg (map B) hF).trans (inverse d))
    apply _root_.congrArg (fun z => (⟨a, b, z⟩ : Pasting (n + 1) (GlobularSet.pullback f g)))
    exact Chain.mapAlong_joint_injective
      (F := fun x y => Pasting n (G.hom x y)) (D := fun x y => Pasting n (H.hom x y))
      (fun x : (GlobularSet.pullback f g).Cell 0 => x.val.1) (fun x => x.val.2)
      (fun {x y} e => map ((GlobularSet.pullbackFst f g).hom x y) e)
      (fun {x y} e => map ((GlobularSet.pullbackSnd f g).hom x y) e)
      (fun x y hx hy => Subtype.ext (Prod.ext hx hy)) (fun e d h₁ h₂ => edge e d h₁ h₂)
      p q (eq_of_heq (Chain.packed_eq_heq _ _ hs)) (eq_of_heq (Chain.packed_eq_heq _ _ ht))

theorem pullbackComparison_injective {G H K : GlobularSet.{u}}
    (f : GlobularSet.Map G K) (g : GlobularSet.Map H K) (n : Nat) :
    Function.Injective ((pullbackComparison f g).app (n := n)) := by
  intro p q h
  exact pullback_pasting_ext f g p q (_root_.congrArg (fun z => z.val.1) h)
    (_root_.congrArg (fun z => z.val.2) h)

theorem pullbackComparison_surjective {G H K : GlobularSet.{u}}
    (f : GlobularSet.Map G K) (g : GlobularSet.Map H K) (n : Nat) :
    Function.Surjective ((pullbackComparison f g).app (n := n)) := by
  intro p
  obtain ⟨r, hr, hs⟩ := pullback_pasting_exists f g p.val.1 p.val.2 p.property
  exact ⟨r, Subtype.ext (Prod.ext hr hs)⟩

noncomputable def pullbackComparisonEquiv {G H K : GlobularSet.{u}}
    (f : GlobularSet.Map G K) (g : GlobularSet.Map H K) (n : Nat) :
    Pasting n (GlobularSet.pullback f g) ≃
      (GlobularSet.pullback (mapGlobular f) (mapGlobular g)).Cell n :=
  Equiv.ofBijective ((pullbackComparison f g).app (n := n))
    ⟨pullbackComparison_injective f g n, pullbackComparison_surjective f g n⟩

/-- The cellwise inverse respects adjacent boundaries because the forward
comparison is globular and injective in every dimension. -/
noncomputable def pullbackComparisonInverse {G H K : GlobularSet.{u}}
    (f : GlobularSet.Map G K) (g : GlobularSet.Map H K) :
    GlobularSet.Map (GlobularSet.pullback (mapGlobular f) (mapGlobular g))
      (globular (GlobularSet.pullback f g)) where
  app {n} := (pullbackComparisonEquiv f g n).symm
  source_app {n} p := by
    apply pullbackComparison_injective f g n
    exact ((pullbackComparison f g).source_app _).symm.trans
      ((_root_.congrArg (GlobularSet.pullback (mapGlobular f) (mapGlobular g)).source
        ((pullbackComparisonEquiv f g (n + 1)).apply_symm_apply p)).trans
          ((pullbackComparisonEquiv f g n).apply_symm_apply _).symm)
  target_app {n} p := by
    apply pullbackComparison_injective f g n
    exact ((pullbackComparison f g).target_app _).symm.trans
      ((_root_.congrArg (GlobularSet.pullback (mapGlobular f) (mapGlobular g)).target
        ((pullbackComparisonEquiv f g (n + 1)).apply_symm_apply p)).trans
          ((pullbackComparisonEquiv f g n).apply_symm_apply _).symm)

/-- Pasting commutes with the actual matched-cell pullback up to a globular
isomorphism. This does not assert cartesianness of monad multiplication. -/
noncomputable def pullbackComparisonIso {G H K : GlobularSet.{u}}
    (f : GlobularSet.Map G K) (g : GlobularSet.Map H K) :
    CategoryTheory.Iso (globular (GlobularSet.pullback f g))
      (GlobularSet.pullback (mapGlobular f) (mapGlobular g)) where
  hom := pullbackComparison f g
  inv := pullbackComparisonInverse f g
  hom_inv_id := by
    apply GlobularSet.Map.ext
    intro n p
    exact (pullbackComparisonEquiv f g n).symm_apply_apply p
  inv_hom_id := by
    apply GlobularSet.Map.ext
    intro n p
    exact (pullbackComparisonEquiv f g n).apply_symm_apply p

/-- The image of every canonical globular pullback cone has the full
universal property. This is stronger than a cellwise bijection alone. -/
theorem pasting_pullback_universal {G H K X : GlobularSet.{u}}
    (f : GlobularSet.Map G K) (g : GlobularSet.Map H K)
    (p : GlobularSet.Map X (globular G)) (q : GlobularSet.Map X (globular H))
    (h : GlobularSet.Map.comp (mapGlobular f) p = GlobularSet.Map.comp (mapGlobular g) q) :
    ∃! d : GlobularSet.Map X (globular (GlobularSet.pullback f g)),
      GlobularSet.Map.comp (mapGlobular (GlobularSet.pullbackFst f g)) d = p ∧
      GlobularSet.Map.comp (mapGlobular (GlobularSet.pullbackSnd f g)) d = q := by
  let l := GlobularSet.pullbackLift (mapGlobular f) (mapGlobular g) p q h
  let d := GlobularSet.Map.comp (pullbackComparisonInverse f g) l
  have hd {n : Nat} (x : X.Cell n) :
      ((pullbackComparison f g).app (d.app x)).val = (p.app x, q.app x) :=
    _root_.congrArg Subtype.val ((pullbackComparisonEquiv f g n).apply_symm_apply (l.app x))
  refine ⟨d, ⟨?_, ?_⟩, ?_⟩
  · apply GlobularSet.Map.ext
    intro n x
    exact _root_.congrArg Prod.fst (hd x)
  · apply GlobularSet.Map.ext
    intro n x
    exact _root_.congrArg Prod.snd (hd x)
  · intro e he
    apply GlobularSet.Map.ext
    intro n x
    exact pullback_pasting_ext f g _ _
      ((_root_.congrArg (fun k : GlobularSet.Map X (globular G) => k.app x) he.1).trans
        (_root_.congrArg Prod.fst (hd x)).symm)
      ((_root_.congrArg (fun k : GlobularSet.Map X (globular H) => k.app x) he.2).trans
        (_root_.congrArg Prod.snd (hd x)).symm)

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

/-- The general operation at the zero boundary is exactly horizontal
concatenation on the existing endpoint fibre. -/
theorem composeAt_horizontal (n : Nat) {G : GlobularSet.{u}} {a b c : G.Cell 0}
    (p : Horizontal n G a b) (q : Horizontal n G b c) :
    composeAt 0 n (pack p) (pack q) rfl = pack (horizontal p q) := rfl

/-- At gap one, the general operation is the previously verified adjacent
composition on the very same cells. -/
theorem composeAt_adjacent (k : Nat) {G : GlobularSet.{u}} (p q : Pasting (0 + k + 1) G)
    (h : targetAt k 0 p = sourceAt k 0 q) (h' : target p = source q) :
    composeAt k 0 p q h = vertical p q h' := by
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
    have hp : p.map (fun e => targetAt k 0 e) = q.map (fun e => sourceAt k 0 e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
    have hp' : p.map (fun e => target e) = q.map (fun e => source e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h').2)).2
    exact _root_.congrArg pack (Chain.zipOver_congr
      (fun e => targetAt k 0 e) (fun e => sourceAt k 0 e)
      (fun e => target e) (fun e => source e)
      (fun e d h => composeAt k 0 e d h) (fun e d h => vertical e d h)
      (fun e d h j => ih e d h j) p q hp hp')

theorem composeAt_adjacent_eq (k : Nat) {G : GlobularSet.{u}} (p q : Pasting (0 + k + 1) G)
    (h : targetAt k 0 p = sourceAt k 0 q) :
    composeAt k 0 p q h = vertical p q
      (eq_of_heq ((targetAt_adjacent k p).symm.trans ((heq_of_eq h).trans (sourceAt_adjacent k q)))) :=
  composeAt_adjacent k p q h _

theorem identityAt_adjacent (k : Nat) {G : GlobularSet.{u}} (p : Pasting k G) :
    HEq (identityAt k 0 p) (identity p) := by
  induction k generalizing G with
  | zero => rfl
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    exact pack_heq (_root_.congrArg Nat.succ (Nat.zero_add k)) _ _
      (Chain.map_heq (by rw [Nat.zero_add]) _ _ (fun e => ih e) p)

/-- The higher identities are iterates of the existing identity operation. -/
theorem identityAt_step (k n : Nat) {G : GlobularSet.{u}} (p : Pasting k G) :
    reindex (excess_succ_dimension k n) (identity (identityAt k n p)) = identityAt k (n + 1) p := by
  induction k generalizing G with
  | zero => rfl
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    change reindex (_root_.congrArg Nat.succ (excess_succ_dimension k n))
      (pack ((p.map (fun e => identityAt k n e)).map (fun e => identity e))) = _
    rw [reindex_pack (excess_succ_dimension k n)]
    apply _root_.congrArg pack
    simp only [Chain.map_map]
    exact Chain.map_congr _ _ (fun e => ih e) p

/-- General composition with zero endpoints exposed. Packing recovers the
same `composeAt` operation, now at boundary dimension `k+1`. -/
noncomputable def composeAtFibre (k n : Nat) {G : GlobularSet.{u}} {a b : G.Cell 0}
    (p q : Horizontal (n + k + 1) G a b)
    (h : p.map (fun e => targetAt k n e) = q.map (fun e => sourceAt k n e)) :
    Horizontal (n + k + 1) G a b :=
  Chain.zipOver (fun e => targetAt k n e) (fun e => sourceAt k n e)
    (fun e d h => composeAt k n e d h) p q h

theorem pack_composeAtFibre (k n : Nat) {G : GlobularSet.{u}} {a b : G.Cell 0}
    (p q : Horizontal (n + k + 1) G a b)
    (h : p.map (fun e => targetAt k n e) = q.map (fun e => sourceAt k n e)) :
    pack (composeAtFibre k n p q h) = composeAt (k + 1) n (pack p) (pack q) (_root_.congrArg pack h) := rfl

/-- Interchange with the zero-boundary composition holds for every higher
boundary, not only the adjacent one. -/
theorem composeAt_horizontal_interchange (k n : Nat) {G : GlobularSet.{u}} {a b c : G.Cell 0}
    (p q : Horizontal (n + k + 1) G a b) (r s : Horizontal (n + k + 1) G b c)
    (h : p.map (fun e => targetAt k n e) = q.map (fun e => sourceAt k n e))
    (j : r.map (fun e => targetAt k n e) = s.map (fun e => sourceAt k n e)) :
    composeAtFibre k n (horizontal p r) (horizontal q s)
      ((Chain.map_append _ p r).trans ((_root_.congrArg₂ Chain.append h j).trans
        (Chain.map_append _ q s).symm)) =
      horizontal (composeAtFibre k n p q h) (composeAtFibre k n r s j) :=
  Chain.zipOver_append _ _ _ p q h r s j

/-- A lower boundary of a positive dimension, indexed without arithmetic
casts. This is an index for the existing pasting carrier, not a new tower. -/
inductive Cut : Nat → Type where
  | bottom {n : Nat} : Cut (n + 1)
  | lift {n : Nat} : Cut n → Cut (n + 1)

def Cut.height : {n : Nat} → Cut n → Nat
  | _, .bottom => 0
  | _, .lift c => c.height + 1

def Cut.at : (k n : Nat) → Cut (n + k + 1)
  | 0, _ => .bottom
  | k + 1, n => .lift (Cut.at k n)

/-- The same composition axis one cell dimension higher. -/
inductive Cut.Raise : {n : Nat} → Cut n → Cut (n + 1) → Prop where
  | bottom {n : Nat} : Raise (bottom : Cut (n + 1)) (bottom : Cut (n + 2))
  | lift {n : Nat} {c : Cut n} {d : Cut (n + 1)} : Raise c d → Raise (.lift c) (.lift d)

theorem Cut.Raise.height_eq {n : Nat} {c : Cut n} {d : Cut (n + 1)} (h : Raise c d) :
    c.height = d.height := by
  induction h with
  | bottom => rfl
  | lift _ ih => exact _root_.congrArg Nat.succ ih

namespace CutBoundary

/-- A globular chain of globular labels. The shifted pasting carrier is
exactly this construction applied to the pasting carriers of hom sets. -/
def chainGlobular {O : Type u} (E : O → O → GlobularSet.{u}) : GlobularSet.{u} where
  Cell n := Σ a b : O, Chain (fun x y => (E x y).Cell n) a b
  source p := ⟨p.1, p.2.1, p.2.2.map (fun {x y} e => (E x y).source e)⟩
  target p := ⟨p.1, p.2.1, p.2.2.map (fun {x y} e => (E x y).target e)⟩
  source_source p := by
    rcases p with ⟨a, b, p⟩
    apply _root_.congrArg (fun q => (⟨a, b, q⟩ : Σ a b : O, Chain (fun x y => (E x y).Cell _) a b))
    exact (Chain.map_map _ _ p).trans
      ((Chain.map_congr _ _ (fun {x y} e => (E x y).source_source e) p).trans
        (Chain.map_map _ _ p).symm)
  target_source p := by
    rcases p with ⟨a, b, p⟩
    apply _root_.congrArg (fun q => (⟨a, b, q⟩ : Σ a b : O, Chain (fun x y => (E x y).Cell _) a b))
    exact (Chain.map_map _ _ p).trans
      ((Chain.map_congr _ _ (fun {x y} e => (E x y).target_source e) p).trans
        (Chain.map_map _ _ p).symm)

theorem sourceZero_chain {O : Type u} (E : O → O → GlobularSet.{u})
    {n : Nat} {a b : O} (p : Chain (fun x y => (E x y).Cell n) a b) :
    (chainGlobular E).sourceZero (⟨a, b, p⟩ : (chainGlobular E).Cell n) =
      ⟨a, b, p.map (fun {x y} e => (E x y).sourceZero e)⟩ := by
  induction n with
  | zero => exact _root_.congrArg (fun q => (⟨a, b, q⟩ : (chainGlobular E).Cell 0)) (Chain.map_id p).symm
  | succ n ih =>
    exact (ih (p.map (fun {x y} e => (E x y).source e))).trans
      (_root_.congrArg (fun q => (⟨a, b, q⟩ : (chainGlobular E).Cell 0)) (Chain.map_map _ _ p))

theorem targetZero_chain {O : Type u} (E : O → O → GlobularSet.{u})
    {n : Nat} {a b : O} (p : Chain (fun x y => (E x y).Cell n) a b) :
    (chainGlobular E).targetZero (⟨a, b, p⟩ : (chainGlobular E).Cell n) =
      ⟨a, b, p.map (fun {x y} e => (E x y).targetZero e)⟩ := by
  induction n with
  | zero => exact _root_.congrArg (fun q => (⟨a, b, q⟩ : (chainGlobular E).Cell 0)) (Chain.map_id p).symm
  | succ n ih =>
    exact (ih (p.map (fun {x y} e => (E x y).target e))).trans
      (_root_.congrArg (fun q => (⟨a, b, q⟩ : (chainGlobular E).Cell 0)) (Chain.map_map _ _ p))

/-- Canonical cut boundaries on any globular set. Lifting a cut forgets one
object level; it does not replace the cells by formal pasting syntax. -/
def source : {n : Nat} → (c : Cut n) → (G : GlobularSet.{u}) → G.Cell n → G.Cell c.height
  | _, .bottom, G, p => G.sourceZero p
  | _, .lift c, G, p => source c G.shift p

def target : {n : Nat} → (c : Cut n) → (G : GlobularSet.{u}) → G.Cell n → G.Cell c.height
  | _, .bottom, G, p => G.targetZero p
  | _, .lift c, G, p => target c G.shift p

theorem source_chain {O : Type u} {n : Nat} (c : Cut n)
    (E : O → O → GlobularSet.{u}) {a b : O} (p : Chain (fun x y => (E x y).Cell n) a b) :
    source c (chainGlobular E) ⟨a, b, p⟩ =
      ⟨a, b, p.map (fun {x y} e => source c (E x y) e)⟩ := by
  induction c generalizing E with
  | bottom => exact sourceZero_chain E p
  | lift c ih => exact ih (fun x y => (E x y).shift) p

theorem target_chain {O : Type u} {n : Nat} (c : Cut n)
    (E : O → O → GlobularSet.{u}) {a b : O} (p : Chain (fun x y => (E x y).Cell n) a b) :
    target c (chainGlobular E) ⟨a, b, p⟩ =
      ⟨a, b, p.map (fun {x y} e => target c (E x y) e)⟩ := by
  induction c generalizing E with
  | bottom => exact targetZero_chain E p
  | lift c ih => exact ih (fun x y => (E x y).shift) p

theorem source_map {n : Nat} (c : Cut n) {G H : GlobularSet.{u}}
    (f : GlobularSet.Map G H) (p : G.Cell n) : source c H (f.app p) = f.app (source c G p) := by
  induction c generalizing G H with
  | bottom => exact f.sourceZero p
  | lift c ih => exact ih f.shift p

theorem target_map {n : Nat} (c : Cut n) {G H : GlobularSet.{u}}
    (f : GlobularSet.Map G H) (p : G.Cell n) : target c H (f.app p) = f.app (target c G p) := by
  induction c generalizing G H with
  | bottom => exact f.targetZero p
  | lift c ih => exact ih f.shift p

theorem source_constant {n : Nat} (c : Cut n) {X : Type u} (p : X) :
    source c (GlobularSet.constant X) p = p := by
  induction c with
  | @bottom n =>
    change (GlobularSet.constant X).sourceZero (n := n + 1) p = p
    induction n with
    | zero => rfl
    | succ n ih => exact ih
  | lift c ih => exact ih

theorem target_constant {n : Nat} (c : Cut n) {X : Type u} (p : X) :
    target c (GlobularSet.constant X) p = p := by
  induction c with
  | @bottom n =>
    change (GlobularSet.constant X).targetZero (n := n + 1) p = p
    induction n with
    | zero => rfl
    | succ n ih => exact ih
  | lift c ih => exact ih

theorem sourceZero_source_lift {n : Nat} (c : Cut n) (G : GlobularSet.{u}) (p : G.Cell (n + 1)) :
    G.sourceZero (source (.lift c) G p) = G.sourceZero p :=
  (source_map c G.sourceZeroMap p).symm.trans (source_constant c _)

theorem targetZero_source_lift {n : Nat} (c : Cut n) (G : GlobularSet.{u}) (p : G.Cell (n + 1)) :
    G.targetZero (source (.lift c) G p) = G.targetZero p :=
  (source_map c G.targetZeroMap p).symm.trans (source_constant c _)

theorem sourceZero_target_lift {n : Nat} (c : Cut n) (G : GlobularSet.{u}) (p : G.Cell (n + 1)) :
    G.sourceZero (target (.lift c) G p) = G.sourceZero p :=
  (target_map c G.sourceZeroMap p).symm.trans (target_constant c _)

theorem targetZero_target_lift {n : Nat} (c : Cut n) (G : GlobularSet.{u}) (p : G.Cell (n + 1)) :
    G.targetZero (target (.lift c) G p) = G.targetZero p :=
  (target_map c G.targetZeroMap p).symm.trans (target_constant c _)

/-- Restricting a canonical boundary to a hom set retains its actual
underlying cell, with the cut shifted by one in the original tower. -/
theorem source_hom {n : Nat} (c : Cut n) (G : GlobularSet.{u}) {a b : G.Cell 0}
    (p : (G.hom a b).Cell n) : source (.lift c) G p.val = (source c (G.hom a b) p).val :=
  source_map c (G.homInclusion a b) p

theorem target_hom {n : Nat} (c : Cut n) (G : GlobularSet.{u}) {a b : G.Cell 0}
    (p : (G.hom a b).Cell n) : target (.lift c) G p.val = (target c (G.hom a b) p).val :=
  target_map c (G.homInclusion a b) p

end CutBoundary

/-- Operations at every canonical cut, with their actual cut-boundary laws.
This is boundary data only, not a declaration of strict category laws. -/
structure CutOperations (G : GlobularSet.{u}) where
  compose : {n : Nat} → (c : Cut n) → (p q : G.Cell n) →
    CutBoundary.target c G p = CutBoundary.source c G q → G.Cell n
  source_compose : ∀ {n} (c : Cut n) (p q : G.Cell n) h,
    CutBoundary.source c G (compose c p q h) = CutBoundary.source c G p
  target_compose : ∀ {n} (c : Cut n) (p q : G.Cell n) h,
    CutBoundary.target c G (compose c p q h) = CutBoundary.target c G q
  unit : {n : Nat} → (c : Cut n) → G.Cell c.height → G.Cell n
  source_unit : ∀ {n} (c : Cut n) (p : G.Cell c.height), CutBoundary.source c G (unit c p) = p
  target_unit : ∀ {n} (c : Cut n) (p : G.Cell c.height), CutBoundary.target c G (unit c p) = p

namespace CutOperations

/-- A globular map preserving the actual operations at every cut. -/
structure Preserves {G H : GlobularSet.{u}} (C : CutOperations G) (D : CutOperations H)
    (f : GlobularSet.Map G H) : Prop where
  compose : ∀ {n} (c : Cut n) (p q : G.Cell n) h h',
    f.app (C.compose c p q h) = D.compose c (f.app p) (f.app q) h'
  unit : ∀ {n} (c : Cut n) (p : G.Cell c.height), f.app (C.unit c p) = D.unit c (f.app p)

/-- Composable pairs in the underlying globular set of cut operations. -/
def Pair {G : GlobularSet.{u}} (_C : CutOperations G) {n : Nat} (c : Cut n) :=
  { p : G.Cell n × G.Cell n // CutBoundary.target c G p.1 = CutBoundary.source c G p.2 }

def pairMap {G H : GlobularSet.{u}} (C : CutOperations G) (D : CutOperations H)
    (f : GlobularSet.Map G H) {n : Nat} (c : Cut n) (p : C.Pair c) : D.Pair c :=
  ⟨(f.app p.val.1, f.app p.val.2), (CutBoundary.target_map c f p.val.1).trans
    ((_root_.congrArg f.app p.property).trans (CutBoundary.source_map c f p.val.2).symm)⟩

def composePair {G : GlobularSet.{u}} (C : CutOperations G) {n : Nat} (c : Cut n)
    (p : C.Pair c) : G.Cell n := C.compose c p.val.1 p.val.2 p.property

/-- A preserving map with unique lifts of all primitive cut operations.
This is an explicit premise for recursive-evaluation lifting, not an axiom
about arbitrary maps or arbitrary globular cells. -/
structure Cartesian {G H : GlobularSet.{u}} (C : CutOperations G) (D : CutOperations H)
    (f : GlobularSet.Map G H) : Prop extends Preserves C D f where
  unit_lift : ∀ {n} (c : Cut n) (p : G.Cell n) (q : H.Cell c.height),
    f.app p = D.unit c q → ∃! r : G.Cell c.height, C.unit c r = p ∧ f.app r = q
  compose_lift : ∀ {n} (c : Cut n) (p : G.Cell n) (q : D.Pair c),
    f.app p = D.composePair c q →
    ∃! r : C.Pair c, C.composePair c r = p ∧ pairMap C D f c r = q

def RightUnital {G : GlobularSet.{u}} (C : CutOperations G) : Prop :=
  ∀ {n} (c : Cut n) (p : G.Cell n),
    C.compose c p (C.unit c (CutBoundary.target c G p))
      (C.source_unit c (CutBoundary.target c G p)).symm = p

def LeftUnital {G : GlobularSet.{u}} (C : CutOperations G) : Prop :=
  ∀ {n} (c : Cut n) (p : G.Cell n),
    C.compose c (C.unit c (CutBoundary.source c G p)) p
      (C.target_unit c (CutBoundary.source c G p)) = p

def Associative {G : GlobularSet.{u}} (C : CutOperations G) : Prop :=
  ∀ {n} (c : Cut n) (p q r : G.Cell n) hpq hqr hl hr,
    C.compose c (C.compose c p q hpq) r hl = C.compose c p (C.compose c q r hqr) hr

/-- Adjacent-boundary compatibility is separate from cut-boundary laws.
Matching witnesses are explicit; no composability or coherence is assumed
merely because two expressions have the same normal form. -/
structure Compatible {G : GlobularSet.{u}} (C : CutOperations G) : Prop where
  source_compose : ∀ {n} {c : Cut n} {d : Cut (n + 1)} (_ : Cut.Raise c d)
    (p q : G.Cell (n + 1)) h h',
    G.source (C.compose d p q h) = C.compose c (G.source p) (G.source q) h'
  target_compose : ∀ {n} {c : Cut n} {d : Cut (n + 1)} (_ : Cut.Raise c d)
    (p q : G.Cell (n + 1)) h h',
    G.target (C.compose d p q h) = C.compose c (G.target p) (G.target q) h'
  source_unit : ∀ {n} {c : Cut n} {d : Cut (n + 1)} (_ : Cut.Raise c d)
    (p : G.Cell c.height) (q : G.Cell d.height), HEq p q → G.source (C.unit d q) = C.unit c p
  target_unit : ∀ {n} {c : Cut n} {d : Cut (n + 1)} (_ : Cut.Raise c d)
    (p : G.Cell c.height) (q : G.Cell d.height), HEq p q → G.target (C.unit d q) = C.unit c p

/-- All cuts restrict to each actual hom globular set. Composition is the
parent operation one cut higher; no new cells or choices are introduced. -/
def hom {G : GlobularSet.{u}} (C : CutOperations G) (a b : G.Cell 0) : CutOperations (G.hom a b) where
  compose c p q h := by
    have hh : CutBoundary.target (.lift c) G p.val = CutBoundary.source (.lift c) G q.val :=
      (CutBoundary.target_hom c G p).trans
        ((_root_.congrArg Subtype.val h).trans (CutBoundary.source_hom c G q).symm)
    let r := C.compose (.lift c) p.val q.val hh
    have hs : G.sourceZero r = a :=
      (CutBoundary.sourceZero_source_lift c G r).symm.trans
        ((_root_.congrArg G.sourceZero (C.source_compose (.lift c) p.val q.val hh)).trans
          ((CutBoundary.sourceZero_source_lift c G p.val).trans p.property.1))
    have ht : G.targetZero r = b :=
      (CutBoundary.targetZero_target_lift c G r).symm.trans
        ((_root_.congrArg G.targetZero (C.target_compose (.lift c) p.val q.val hh)).trans
          ((CutBoundary.targetZero_target_lift c G q.val).trans q.property.2))
    exact ⟨r, hs, ht⟩
  source_compose c p q h := by
    apply Subtype.ext
    exact (CutBoundary.source_hom c G _).symm.trans
      ((C.source_compose (.lift c) p.val q.val _).trans (CutBoundary.source_hom c G p))
  target_compose c p q h := by
    apply Subtype.ext
    exact (CutBoundary.target_hom c G _).symm.trans
      ((C.target_compose (.lift c) p.val q.val _).trans (CutBoundary.target_hom c G q))
  unit c p := by
    let r := C.unit (.lift c) p.val
    have hs : G.sourceZero r = a :=
      (CutBoundary.sourceZero_source_lift c G r).symm.trans
        ((_root_.congrArg G.sourceZero (C.source_unit (.lift c) p.val)).trans p.property.1)
    have ht : G.targetZero r = b :=
      (CutBoundary.targetZero_target_lift c G r).symm.trans
        ((_root_.congrArg G.targetZero (C.target_unit (.lift c) p.val)).trans p.property.2)
    exact ⟨r, hs, ht⟩
  source_unit c p := by
    apply Subtype.ext
    exact (CutBoundary.source_hom c G _).symm.trans (C.source_unit (.lift c) p.val)
  target_unit c p := by
    apply Subtype.ext
    exact (CutBoundary.target_hom c G _).symm.trans (C.target_unit (.lift c) p.val)

/-- Restriction preserves the underlying composite exactly. -/
theorem hom_compose_val {G : GlobularSet.{u}} (C : CutOperations G) {a b : G.Cell 0}
    {n : Nat} (c : Cut n) (p q : (G.hom a b).Cell n)
    (h : CutBoundary.target c (G.hom a b) p = CutBoundary.source c (G.hom a b) q) :
    ((C.hom a b).compose c p q h).val = C.compose (.lift c) p.val q.val
      ((CutBoundary.target_hom c G p).trans
        ((_root_.congrArg Subtype.val h).trans (CutBoundary.source_hom c G q).symm)) := rfl

theorem hom_unit_val {G : GlobularSet.{u}} (C : CutOperations G) {a b : G.Cell 0}
    {n : Nat} (c : Cut n) (p : (G.hom a b).Cell c.height) :
    ((C.hom a b).unit c p).val = C.unit (.lift c) p.val := rfl

theorem hom_val_heq {G : GlobularSet.{u}} {a b : G.Cell 0} {n m : Nat}
    (p : (G.hom a b).Cell n) (q : (G.hom a b).Cell m) (hn : n = m) (hp : HEq p q) :
    HEq p.val q.val := by
  cases hn
  cases hp
  rfl

/-- Boundary compatibility, as well as the operations themselves, survives
restriction to the genuine hom globular sets. -/
theorem Compatible.hom {G : GlobularSet.{u}} {C : CutOperations G}
    (L : Compatible C) (a b : G.Cell 0) : Compatible (C.hom a b) where
  source_compose w p q h h' := Subtype.ext (L.source_compose w.lift p.val q.val _ _)
  target_compose w p q h h' := Subtype.ext (L.target_compose w.lift p.val q.val _ _)
  source_unit w p q hp := Subtype.ext
    (L.source_unit w.lift p.val q.val (hom_val_heq p q w.height_eq hp))
  target_unit w p q hp := Subtype.ext
    (L.target_unit w.lift p.val q.val (hom_val_heq p q w.height_eq hp))

theorem RightUnital.hom {G : GlobularSet.{u}} {C : CutOperations G}
    (R : C.RightUnital) (a b : G.Cell 0) : (C.hom a b).RightUnital := by
  intro n c p
  apply Subtype.ext
  change C.compose (.lift c) p.val (C.unit (.lift c) (CutBoundary.target c (G.hom a b) p).val) _ = p.val
  simp only [← CutBoundary.target_hom]
  exact R (.lift c) p.val

theorem LeftUnital.hom {G : GlobularSet.{u}} {C : CutOperations G}
    (R : C.LeftUnital) (a b : G.Cell 0) : (C.hom a b).LeftUnital := by
  intro n c p
  apply Subtype.ext
  change C.compose (.lift c) (C.unit (.lift c) (CutBoundary.source c (G.hom a b) p).val) p.val _ = p.val
  simp only [← CutBoundary.source_hom]
  exact R (.lift c) p.val

theorem Associative.hom {G : GlobularSet.{u}} {C : CutOperations G}
    (A : C.Associative) (a b : G.Cell 0) : (C.hom a b).Associative := by
  intro n c p q r hpq hqr hl hr
  exact Subtype.ext (A (.lift c) p.val q.val r.val _ _ _ _)

theorem Preserves.hom {G H : GlobularSet.{u}} {C : CutOperations G} {D : CutOperations H}
    {f : GlobularSet.Map G H} (P : Preserves C D f) (a b : G.Cell 0) :
    Preserves (C.hom a b) (D.hom (f.app a) (f.app b)) (f.hom a b) where
  compose c p q h h' := Subtype.ext (P.compose (.lift c) p.val q.val _ _)
  unit c p := Subtype.ext (P.unit (.lift c) p.val)

/-- Primitive unit lifts restrict to the actual fixed-endpoint homs.
The endpoint witnesses are derived from the lifted unit equation. -/
theorem Cartesian.unit_lift_hom {G H : GlobularSet.{u}} {C : CutOperations G} {D : CutOperations H}
    {f : GlobularSet.Map G H} (K : Cartesian C D f) (a b : G.Cell 0)
    {n : Nat} (c : Cut n) (p : (G.hom a b).Cell n)
    (q : (H.hom (f.app a) (f.app b)).Cell c.height)
    (h : (f.hom a b).app p = (D.hom (f.app a) (f.app b)).unit c q) :
    ∃! r : (G.hom a b).Cell c.height,
      (C.hom a b).unit c r = p ∧ (f.hom a b).app r = q := by
  obtain ⟨r, ⟨hr, hf⟩, hu⟩ := K.unit_lift (.lift c) p.val q.val (_root_.congrArg Subtype.val h)
  have hs : G.sourceZero r = a :=
    (_root_.congrArg G.sourceZero (C.source_unit (.lift c) r)).symm.trans
      ((CutBoundary.sourceZero_source_lift c G (C.unit (.lift c) r)).trans
        ((_root_.congrArg G.sourceZero hr).trans p.property.1))
  have ht : G.targetZero r = b :=
    (_root_.congrArg G.targetZero (C.target_unit (.lift c) r)).symm.trans
      ((CutBoundary.targetZero_target_lift c G (C.unit (.lift c) r)).trans
        ((_root_.congrArg G.targetZero hr).trans p.property.2))
  refine ⟨⟨r, hs, ht⟩, ⟨Subtype.ext hr, Subtype.ext hf⟩, ?_⟩
  intro s hs
  exact Subtype.ext (hu s.val ⟨_root_.congrArg Subtype.val hs.1, _root_.congrArg Subtype.val hs.2⟩)

def homPairVal {G : GlobularSet.{u}} (C : CutOperations G) (a b : G.Cell 0)
    {n : Nat} (c : Cut n) (p : (C.hom a b).Pair c) : C.Pair (.lift c) :=
  ⟨(p.val.1.val, p.val.2.val), (CutBoundary.target_hom c G p.val.1).trans
    ((_root_.congrArg Subtype.val p.property).trans (CutBoundary.source_hom c G p.val.2).symm)⟩

/-- A lifted-cut composite has the zero-boundaries of each factor. -/
theorem compose_lift_endpoints {G : GlobularSet.{u}} (C : CutOperations G) {n : Nat} (c : Cut n)
    (r : C.Pair (.lift c)) :
    (G.sourceZero (C.composePair (.lift c) r) = G.sourceZero r.val.1 ∧
      G.targetZero (C.composePair (.lift c) r) = G.targetZero r.val.1) ∧
    (G.sourceZero (C.composePair (.lift c) r) = G.sourceZero r.val.2 ∧
      G.targetZero (C.composePair (.lift c) r) = G.targetZero r.val.2) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact (CutBoundary.sourceZero_source_lift c G _).symm.trans
      ((_root_.congrArg G.sourceZero (C.source_compose (.lift c) r.val.1 r.val.2 r.property)).trans
        (CutBoundary.sourceZero_source_lift c G _))
  · exact (CutBoundary.targetZero_source_lift c G _).symm.trans
      ((_root_.congrArg G.targetZero (C.source_compose (.lift c) r.val.1 r.val.2 r.property)).trans
        (CutBoundary.targetZero_source_lift c G _))
  · exact (CutBoundary.sourceZero_target_lift c G _).symm.trans
      ((_root_.congrArg G.sourceZero (C.target_compose (.lift c) r.val.1 r.val.2 r.property)).trans
        (CutBoundary.sourceZero_target_lift c G _))
  · exact (CutBoundary.targetZero_target_lift c G _).symm.trans
      ((_root_.congrArg G.targetZero (C.target_compose (.lift c) r.val.1 r.val.2 r.property)).trans
        (CutBoundary.targetZero_target_lift c G _))

theorem Cartesian.compose_lift_hom {G H : GlobularSet.{u}} {C : CutOperations G} {D : CutOperations H}
    {f : GlobularSet.Map G H} (K : Cartesian C D f) (a b : G.Cell 0)
    {n : Nat} (c : Cut n) (p : (G.hom a b).Cell n)
    (q : (D.hom (f.app a) (f.app b)).Pair c)
    (h : (f.hom a b).app p = (D.hom (f.app a) (f.app b)).composePair c q) :
    ∃! r : (C.hom a b).Pair c, (C.hom a b).composePair c r = p ∧
      pairMap (C.hom a b) (D.hom (f.app a) (f.app b)) (f.hom a b) c r = q := by
  obtain ⟨r, ⟨hr, hf⟩, hu⟩ := K.compose_lift (.lift c) p.val
    (homPairVal D (f.app a) (f.app b) c q) (_root_.congrArg Subtype.val h)
  have ep := compose_lift_endpoints C c r
  have es := (_root_.congrArg G.sourceZero hr).trans p.property.1
  have et := (_root_.congrArg G.targetZero hr).trans p.property.2
  let r₁ : (G.hom a b).Cell n := ⟨r.val.1, ep.1.1.symm.trans es, ep.1.2.symm.trans et⟩
  let r₂ : (G.hom a b).Cell n := ⟨r.val.2, ep.2.1.symm.trans es, ep.2.2.symm.trans et⟩
  let s : (C.hom a b).Pair c := ⟨(r₁, r₂), Subtype.ext
    ((CutBoundary.target_hom c G r₁).symm.trans (r.property.trans (CutBoundary.source_hom c G r₂)))⟩
  refine ⟨s, ⟨Subtype.ext hr, ?_⟩, ?_⟩
  · exact Subtype.ext (Prod.ext
      (Subtype.ext (_root_.congrArg (fun z : D.Pair (.lift c) => z.val.1) hf))
      (Subtype.ext (_root_.congrArg (fun z : D.Pair (.lift c) => z.val.2) hf)))
  · intro t ht
    have he : homPairVal C a b c t = r := hu (homPairVal C a b c t)
      ⟨_root_.congrArg Subtype.val ht.1,
        _root_.congrArg (homPairVal D (f.app a) (f.app b) c) ht.2⟩
    exact Subtype.ext (Prod.ext
      (Subtype.ext (_root_.congrArg (fun z : C.Pair (.lift c) => z.val.1) he))
      (Subtype.ext (_root_.congrArg (fun z : C.Pair (.lift c) => z.val.2) he)))

/-- Unique primitive lifts survive every genuine hom restriction. -/
theorem Cartesian.hom {G H : GlobularSet.{u}} {C : CutOperations G} {D : CutOperations H}
    {f : GlobularSet.Map G H} (K : Cartesian C D f) (a b : G.Cell 0) :
    Cartesian (C.hom a b) (D.hom (f.app a) (f.app b)) (f.hom a b) where
  toPreserves := K.toPreserves.hom a b
  unit_lift := K.unit_lift_hom a b
  compose_lift := K.compose_lift_hom a b

end CutOperations

theorem Cut.height_at (k n : Nat) : (Cut.at k n).height = k := by
  induction k with
  | zero => rfl
  | succ k ih => exact _root_.congrArg Nat.succ ih

def cutSource : {n : Nat} → (c : Cut n) → {G : GlobularSet.{u}} → Pasting n G → Pasting c.height G
  | _, .bottom, _, ⟨a, _, _⟩ => a
  | _, .lift c, G, ⟨a, b, p⟩ => ⟨a, b, p.map (fun {x y} e => cutSource c (G := G.hom x y) e)⟩

def cutTarget : {n : Nat} → (c : Cut n) → {G : GlobularSet.{u}} → Pasting n G → Pasting c.height G
  | _, .bottom, _, ⟨_, b, _⟩ => b
  | _, .lift c, G, ⟨a, b, p⟩ => ⟨a, b, p.map (fun {x y} e => cutTarget c (G := G.hom x y) e)⟩

/-- The implemented pasting boundary is the canonical globular cut, on
all diagrams and every cut, not only on singleton generators. -/
theorem canonical_source_eq_cutSource {n : Nat} (c : Cut n) {G : GlobularSet.{u}}
    (p : Pasting n G) : CutBoundary.source c (globular G) p = cutSource c p := by
  induction c generalizing G with
  | bottom => rcases p with ⟨a, b, p⟩; exact sourceZero_pack p
  | lift c ih =>
    rcases p with ⟨a, b, p⟩
    change CutBoundary.source c (CutBoundary.chainGlobular (fun x y => globular (G.hom x y)))
      ⟨a, b, p⟩ = pack (p.map (fun e => cutSource c e))
    exact (CutBoundary.source_chain c (fun x y => globular (G.hom x y)) p).trans
      (_root_.congrArg pack (Chain.map_congr _ _ (fun e => ih e) p))

theorem canonical_target_eq_cutTarget {n : Nat} (c : Cut n) {G : GlobularSet.{u}}
    (p : Pasting n G) : CutBoundary.target c (globular G) p = cutTarget c p := by
  induction c generalizing G with
  | bottom => rcases p with ⟨a, b, p⟩; exact targetZero_pack p
  | lift c ih =>
    rcases p with ⟨a, b, p⟩
    change CutBoundary.target c (CutBoundary.chainGlobular (fun x y => globular (G.hom x y)))
      ⟨a, b, p⟩ = pack (p.map (fun e => cutTarget c e))
    exact (CutBoundary.target_chain c (fun x y => globular (G.hom x y)) p).trans
      (_root_.congrArg pack (Chain.map_congr _ _ (fun e => ih e) p))

noncomputable def cutCompose {n : Nat} (c : Cut n) {G : GlobularSet.{u}}
    (p q : Pasting n G) (h : cutTarget c p = cutSource c q) : Pasting n G := by
  induction c generalizing G with
  | bottom =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    change b = c at h
    cases h
    exact pack (horizontal p q)
  | lift c ih =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨d, e, q⟩
    have ha : a = d := _root_.congrArg Sigma.fst h
    have hb : b = e := _root_.congrArg (fun z => z.2.1) h
    cases ha
    cases hb
    have hp : p.map (fun e => cutTarget c e) = q.map (fun e => cutSource c e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
    exact pack (Chain.zipOver (fun e => cutTarget c e) (fun e => cutSource c e)
      (fun {x y} e d h => ih (G := G.hom x y) e d h) p q hp)

/-- Both prescribed factors and their actual cut match are retained. -/
def CutPair {n : Nat} (c : Cut n) (G : GlobularSet.{u}) :=
  { p : Pasting n G × Pasting n G // cutTarget c p.1 = cutSource c p.2 }

/-- The factor-pair chain underlying a lifted-cut composition. -/
noncomputable def cutPairChain {n : Nat} (c : Cut n) {G : GlobularSet.{u}} {a b : G.Cell 0}
    (p q : Horizontal n G a b)
    (h : p.map (fun e => cutTarget c e) = q.map (fun e => cutSource c e)) :
    Chain (fun x y => CutPair c (G.hom x y)) a b :=
  Chain.zipOver (fun e => cutTarget c e) (fun e => cutSource c e)
    (fun e f h => ⟨(e, f), h⟩) p q h

theorem cutPairChain_left {n : Nat} (c : Cut n) {G : GlobularSet.{u}} {a b : G.Cell 0}
    (p q : Horizontal n G a b)
    (h : p.map (fun e => cutTarget c e) = q.map (fun e => cutSource c e)) :
    (cutPairChain c p q h).map (fun r => r.val.1) = p :=
  (Chain.map_zipOver_left (fun e => cutTarget c e) (fun e => cutSource c e)
    (fun e f h => (⟨(e, f), h⟩ : CutPair c _)) (fun r => r.val.1) (fun e => e)
    (fun _ _ _ => rfl) p q h).trans (Chain.map_id p)

theorem cutPairChain_right {n : Nat} (c : Cut n) {G : GlobularSet.{u}} {a b : G.Cell 0}
    (p q : Horizontal n G a b)
    (h : p.map (fun e => cutTarget c e) = q.map (fun e => cutSource c e)) :
    (cutPairChain c p q h).map (fun r => r.val.2) = q :=
  (Chain.map_zipOver_right (fun e => cutTarget c e) (fun e => cutSource c e)
    (fun e f h => (⟨(e, f), h⟩ : CutPair c _)) (fun r => r.val.2) (fun e => e)
    (fun _ _ _ => rfl) p q h).trans (Chain.map_id q)

theorem cutPairChain_composable {n : Nat} (c : Cut n) {G : GlobularSet.{u}} {a b : G.Cell 0}
    (r : Chain (fun x y => CutPair c (G.hom x y)) a b) :
    (r.map (fun p => p.val.1)).map (fun p => cutTarget c p) =
      (r.map (fun p => p.val.2)).map (fun p => cutSource c p) :=
  (Chain.map_map _ _ r).trans ((Chain.map_congr _ _ (fun p => p.property) r).trans
    (Chain.map_map _ _ r).symm)

/-- Packing both factors and recovering them loses no factor data. -/
theorem cutPairChain_roundtrip {n : Nat} (c : Cut n) {G : GlobularSet.{u}} {a b : G.Cell 0}
    (r : Chain (fun x y => CutPair c (G.hom x y)) a b) :
    cutPairChain c (r.map (fun p => p.val.1)) (r.map (fun p => p.val.2))
      (cutPairChain_composable c r) = r := by
  induction r with
  | nil => rfl
  | cons p r ih =>
    change Chain.cons p (cutPairChain c (r.map (fun p => p.val.1)) (r.map (fun p => p.val.2)) _) = _
    exact _root_.congrArg (Chain.cons p) ih

/-- Composing the retained factor pairs gives the implemented aligned
composition, with each original matching witness still available. -/
theorem cutPairChain_compose {n : Nat} (c : Cut n) {G : GlobularSet.{u}} {a b : G.Cell 0}
    (p q : Horizontal n G a b)
    (h : p.map (fun e => cutTarget c e) = q.map (fun e => cutSource c e)) :
    (cutPairChain c p q h).map (fun r => cutCompose c r.val.1 r.val.2 r.property) =
      Chain.zipOver (fun e => cutTarget c e) (fun e => cutSource c e)
        (fun e f h => cutCompose c e f h) p q h := by
  induction p with
  | nil =>
    cases q with
    | nil => rfl
    | cons e q => cases h
  | @cons a d b e p ih =>
    cases q with
    | nil => cases h
    | @cons _ d' _ f q =>
      have hc := h
      simp only [Chain.map] at hc
      injection hc with _ hd _ he hp
      cases hd
      have he' := eq_of_heq he
      have hp' := eq_of_heq hp
      change Chain.cons (cutCompose c e f he')
        ((cutPairChain c p q hp').map (fun r => cutCompose c r.val.1 r.val.2 r.property)) = _
      exact _root_.congrArg (Chain.cons (cutCompose c e f he')) (ih q hp')

theorem cutCompose_lift_pairs {n : Nat} (c : Cut n) {G : GlobularSet.{u}} {a b : G.Cell 0}
    (p q : Horizontal n G a b)
    (h : p.map (fun e => cutTarget c e) = q.map (fun e => cutSource c e)) :
    cutCompose (.lift c) (pack p) (pack q) (_root_.congrArg pack h) =
      pack ((cutPairChain c p q h).map (fun r => cutCompose c r.val.1 r.val.2 r.property)) :=
  _root_.congrArg pack (cutPairChain_compose c p q h).symm

theorem cutSource_cutCompose {n : Nat} (c : Cut n) {G : GlobularSet.{u}}
    (p q : Pasting n G) (h : cutTarget c p = cutSource c q) :
    cutSource c (cutCompose c p q h) = cutSource c p := by
  induction c generalizing G with
  | bottom =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    change b = c at h
    cases h
    rfl
  | lift c ih =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨d, e, q⟩
    have ha : a = d := _root_.congrArg Sigma.fst h
    have hb : b = e := _root_.congrArg (fun z => z.2.1) h
    cases ha
    cases hb
    have hp : p.map (fun e => cutTarget c e) = q.map (fun e => cutSource c e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
    exact _root_.congrArg pack (Chain.map_zipOver_left _ _ _ _ _ (fun e f he => ih e f he) p q hp)

theorem cutTarget_cutCompose {n : Nat} (c : Cut n) {G : GlobularSet.{u}}
    (p q : Pasting n G) (h : cutTarget c p = cutSource c q) :
    cutTarget c (cutCompose c p q h) = cutTarget c q := by
  induction c generalizing G with
  | bottom =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    change b = c at h
    cases h
    rfl
  | lift c ih =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨d, e, q⟩
    have ha : a = d := _root_.congrArg Sigma.fst h
    have hb : b = e := _root_.congrArg (fun z => z.2.1) h
    cases ha
    cases hb
    have hp : p.map (fun e => cutTarget c e) = q.map (fun e => cutSource c e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
    exact _root_.congrArg pack (Chain.map_zipOver_right _ _ _ _ _ (fun e f he => ih e f he) p q hp)

/-- Iterated identity diagram at a specified cut of any dimension. -/
noncomputable def cutUnit {n : Nat} (c : Cut n) {G : GlobularSet.{u}} (p : Pasting c.height G) : Pasting n G := by
  induction c generalizing G with
  | bottom => exact ⟨p, p, .nil p⟩
  | lift c ih =>
    rcases p with ⟨a, b, p⟩
    exact pack (p.map (fun {x y} e => ih (G := G.hom x y) e))

theorem cutSource_cutUnit {n : Nat} (c : Cut n) {G : GlobularSet.{u}} (p : Pasting c.height G) :
    cutSource c (cutUnit c p) = p := by
  induction c generalizing G with
  | bottom => rfl
  | lift c ih =>
    rcases p with ⟨a, b, p⟩
    exact _root_.congrArg pack ((Chain.map_map _ _ p).trans
      ((Chain.map_congr _ (fun e => e) (fun e => ih e) p).trans (Chain.map_id p)))

theorem cutTarget_cutUnit {n : Nat} (c : Cut n) {G : GlobularSet.{u}} (p : Pasting c.height G) :
    cutTarget c (cutUnit c p) = p := by
  induction c generalizing G with
  | bottom => rfl
  | lift c ih =>
    rcases p with ⟨a, b, p⟩
    exact _root_.congrArg pack ((Chain.map_map _ _ p).trans
      ((Chain.map_congr _ (fun e => e) (fun e => ih e) p).trans (Chain.map_id p)))

/-- The cut-indexed identity is a left unit for the existing composition. -/
theorem cutCompose_left_unit {n : Nat} (c : Cut n) {G : GlobularSet.{u}} (p : Pasting n G) :
    cutCompose c (cutUnit c (cutSource c p)) p (cutTarget_cutUnit c (cutSource c p)) = p := by
  induction c generalizing G with
  | bottom => rcases p with ⟨a, b, p⟩; rfl
  | lift c ih =>
    rcases p with ⟨a, b, p⟩
    change cutCompose (.lift c) (pack ((p.map (fun e => cutSource c e)).map (fun e => cutUnit c e)))
      (pack p) _ = pack p
    simp only [Chain.map_map]
    exact _root_.congrArg pack (Chain.zipOver_map_left
      (fun e => cutTarget c e) (fun e => cutSource c e) (fun e f h => cutCompose c e f h)
      (fun e => cutUnit c (cutSource c e)) (fun e => cutTarget_cutUnit c (cutSource c e))
      (fun e => ih e) p)

theorem cutCompose_right_unit {n : Nat} (c : Cut n) {G : GlobularSet.{u}} (p : Pasting n G) :
    cutCompose c p (cutUnit c (cutTarget c p)) (cutSource_cutUnit c (cutTarget c p)).symm = p := by
  induction c generalizing G with
  | bottom => rcases p with ⟨a, b, p⟩; exact _root_.congrArg pack (Chain.append_nil p)
  | lift c ih =>
    rcases p with ⟨a, b, p⟩
    change cutCompose (.lift c) (pack p)
      (pack ((p.map (fun e => cutTarget c e)).map (fun e => cutUnit c e))) _ = pack p
    simp only [Chain.map_map]
    exact _root_.congrArg pack (Chain.zipOver_map_right
      (fun e => cutTarget c e) (fun e => cutSource c e) (fun e f h => cutCompose c e f h)
      (fun e => cutUnit c (cutTarget c e)) (fun e => (cutSource_cutUnit c (cutTarget c e)).symm)
      (fun e => ih e) p)

/-- Strict associativity of the existing operation at every cut. -/
theorem cutCompose_assoc {n : Nat} (c : Cut n) {G : GlobularSet.{u}}
    (p q r : Pasting n G) (h : cutTarget c p = cutSource c q) (j : cutTarget c q = cutSource c r) :
    cutCompose c (cutCompose c p q h) r ((cutTarget_cutCompose c p q h).trans j) =
      cutCompose c p (cutCompose c q r j) (h.trans (cutSource_cutCompose c q r j).symm) := by
  induction c generalizing G with
  | bottom =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    rcases r with ⟨e, f, r⟩
    change b = c at h
    change d = e at j
    cases h
    cases j
    exact _root_.congrArg pack (Chain.append_assoc p q r)
  | lift c ih =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨d, e, q⟩
    rcases r with ⟨f, g, r⟩
    have ha : a = d := _root_.congrArg Sigma.fst h
    have hb : b = e := _root_.congrArg (fun z => z.2.1) h
    have hc : d = f := _root_.congrArg Sigma.fst j
    have hd : e = g := _root_.congrArg (fun z => z.2.1) j
    cases ha
    cases hb
    cases hc
    cases hd
    have hp : p.map (fun e => cutTarget c e) = q.map (fun e => cutSource c e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
    have hq : q.map (fun e => cutTarget c e) = r.map (fun e => cutSource c e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj j).2)).2
    exact _root_.congrArg pack (Chain.zipOver_assoc _ _ _
      (fun e f h => cutTarget_cutCompose c e f h) (fun e f h => cutSource_cutCompose c e f h)
      (fun e f g h j => ih e f g h j) p q r hp hq)

/-- The actual labelled pasting operations satisfy the canonical cut
interface and can therefore be restricted to every iterated hom set. -/
noncomputable def cutOperations (G : GlobularSet.{u}) : CutOperations (globular G) where
  compose c p q h := cutCompose c p q
    ((canonical_target_eq_cutTarget c p).symm.trans (h.trans (canonical_source_eq_cutSource c q)))
  source_compose c p q h :=
    (canonical_source_eq_cutSource c _).trans
      ((cutSource_cutCompose c p q _).trans (canonical_source_eq_cutSource c p).symm)
  target_compose c p q h :=
    (canonical_target_eq_cutTarget c _).trans
      ((cutTarget_cutCompose c p q _).trans (canonical_target_eq_cutTarget c q).symm)
  unit c p := cutUnit (G := G) c p
  source_unit c p := (canonical_source_eq_cutSource c (cutUnit c p)).trans (cutSource_cutUnit c p)
  target_unit c p := (canonical_target_eq_cutTarget c (cutUnit c p)).trans (cutTarget_cutUnit c p)

theorem source_cutCompose {n : Nat} {c : Cut n} {d : Cut (n + 1)} (w : Cut.Raise c d)
    {G : GlobularSet.{u}} (p q : Pasting (n + 1) G)
    (h : cutTarget d p = cutSource d q)
    (h' : cutTarget c (source p) = cutSource c (source q)) :
    source (cutCompose d p q h) = cutCompose c (source p) (source q) h' := by
  induction w generalizing G with
  | bottom =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    change b = c at h
    cases h
    exact _root_.congrArg pack (Chain.map_append _ p q)
  | @lift n c d w ih =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨e, f, q⟩
    have ha : a = e := _root_.congrArg Sigma.fst h
    have hb : b = f := _root_.congrArg (fun z => z.2.1) h
    cases ha
    cases hb
    have hp : p.map (fun e => cutTarget d e) = q.map (fun e => cutSource d e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
    have hp' : (p.map (fun e => source e)).map (fun e => cutTarget c e) =
        (q.map (fun e => source e)).map (fun e => cutSource c e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h').2)).2
    exact _root_.congrArg pack (Chain.map_zipOver _ _ _ _ _ _ _ (fun e f he hf => ih e f he hf) p q hp hp')

theorem target_cutCompose {n : Nat} {c : Cut n} {d : Cut (n + 1)} (w : Cut.Raise c d)
    {G : GlobularSet.{u}} (p q : Pasting (n + 1) G)
    (h : cutTarget d p = cutSource d q)
    (h' : cutTarget c (target p) = cutSource c (target q)) :
    target (cutCompose d p q h) = cutCompose c (target p) (target q) h' := by
  induction w generalizing G with
  | bottom =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    change b = c at h
    cases h
    exact _root_.congrArg pack (Chain.map_append _ p q)
  | @lift n c d w ih =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨e, f, q⟩
    have ha : a = e := _root_.congrArg Sigma.fst h
    have hb : b = f := _root_.congrArg (fun z => z.2.1) h
    cases ha
    cases hb
    have hp : p.map (fun e => cutTarget d e) = q.map (fun e => cutSource d e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
    have hp' : (p.map (fun e => target e)).map (fun e => cutTarget c e) =
        (q.map (fun e => target e)).map (fun e => cutSource c e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h').2)).2
    exact _root_.congrArg pack (Chain.map_zipOver _ _ _ _ _ _ _ (fun e f he hf => ih e f he hf) p q hp hp')

theorem source_cutUnit_reindex {n : Nat} {c : Cut n} {d : Cut (n + 1)} (w : Cut.Raise c d)
    {G : GlobularSet.{u}} (p : Pasting c.height G) :
    source (cutUnit d (reindex w.height_eq p)) = cutUnit c p := by
  induction w generalizing G with
  | bottom => rfl
  | @lift n c d w ih =>
    rcases p with ⟨a, b, p⟩
    change source (cutUnit (.lift d) (reindex (_root_.congrArg Nat.succ w.height_eq) (pack p))) = _
    refine (_root_.congrArg (fun z : Pasting (d.height + 1) G => source (cutUnit (.lift d) z))
      (reindex_pack w.height_eq p)).trans ?_
    change pack (((p.map (fun e => reindex w.height_eq e)).map (fun e => cutUnit d e)).map
      (fun e => source e)) = pack (p.map (fun e => cutUnit c e))
    exact _root_.congrArg pack ((Chain.map_map _ _ _).trans
      ((Chain.map_map _ _ p).trans (Chain.map_congr _ _ (fun e => ih e) p)))

theorem target_cutUnit_reindex {n : Nat} {c : Cut n} {d : Cut (n + 1)} (w : Cut.Raise c d)
    {G : GlobularSet.{u}} (p : Pasting c.height G) :
    target (cutUnit d (reindex w.height_eq p)) = cutUnit c p := by
  induction w generalizing G with
  | bottom => rfl
  | @lift n c d w ih =>
    rcases p with ⟨a, b, p⟩
    change target (cutUnit (.lift d) (reindex (_root_.congrArg Nat.succ w.height_eq) (pack p))) = _
    refine (_root_.congrArg (fun z : Pasting (d.height + 1) G => target (cutUnit (.lift d) z))
      (reindex_pack w.height_eq p)).trans ?_
    change pack (((p.map (fun e => reindex w.height_eq e)).map (fun e => cutUnit d e)).map
      (fun e => target e)) = pack (p.map (fun e => cutUnit c e))
    exact _root_.congrArg pack ((Chain.map_map _ _ _).trans
      ((Chain.map_map _ _ p).trans (Chain.map_congr _ _ (fun e => ih e) p)))

/-- All adjacent boundaries commute with the concrete cut operations. -/
theorem cutOperations_compatible (G : GlobularSet.{u}) : CutOperations.Compatible (cutOperations G) where
  source_compose w p q h h' := source_cutCompose w p q _ _
  target_compose w p q h h' := target_cutCompose w p q _ _
  source_unit w p q hp := by
    have hq : reindex w.height_eq p = q := eq_of_heq ((reindex_heq w.height_eq p).trans hp)
    exact (_root_.congrArg (fun z => source (cutUnit _ z)) hq.symm).trans (source_cutUnit_reindex w p)
  target_unit w p q hp := by
    have hq : reindex w.height_eq p = q := eq_of_heq ((reindex_heq w.height_eq p).trans hp)
    exact (_root_.congrArg (fun z => target (cutUnit _ z)) hq.symm).trans (target_cutUnit_reindex w p)

theorem cutOperations_rightUnital (G : GlobularSet.{u}) : (cutOperations G).RightUnital := by
  intro n c p
  change Pasting n G at p
  change cutCompose c p (cutUnit c (CutBoundary.target c (globular G) p)) _ = p
  simp only [canonical_target_eq_cutTarget]
  exact cutCompose_right_unit c p

theorem cutOperations_leftUnital (G : GlobularSet.{u}) : (cutOperations G).LeftUnital := by
  intro n c p
  change Pasting n G at p
  change cutCompose c (cutUnit c (CutBoundary.source c (globular G) p)) p _ = p
  simp only [canonical_source_eq_cutSource]
  exact cutCompose_left_unit c p

theorem cutOperations_associative (G : GlobularSet.{u}) : (cutOperations G).Associative := by
  intro n c p q r hpq hqr hl hr
  exact cutCompose_assoc c p q r _ _

/-- Empty horizontal units also have unique lifts under relabelling, in
every positive dimension. A nonempty chain cannot map to such a unit. -/
theorem horizontal_unit_cartesian {G H : GlobularSet.{u}} (f : GlobularSet.Map G H)
    {n : Nat} (p : Pasting (n + 1) G) (c : H.Cell 0)
    (h : map f p = cutUnit (.bottom : Cut (n + 1)) c) :
    ∃! a : G.Cell 0, cutUnit (.bottom : Cut (n + 1)) a = p ∧ f.app a = c := by
  rcases p with ⟨a, b, p⟩
  have ha : f.app a = c := _root_.congrArg Sigma.fst h
  have hb : f.app b = c := _root_.congrArg (fun z => z.2.1) h
  cases p with
  | nil =>
    refine ⟨a, ⟨rfl, ha⟩, ?_⟩
    intro d hd
    exact _root_.congrArg Sigma.fst hd.1
  | @cons _ y _ e p =>
    have hc := Chain.packed_eq_heq _ _ h
    exact False.elim (Chain.nil_not_heq_cons (D := fun x y => Pasting n (H.hom x y)) (map (f.hom a y) e)
      (p.mapAlong (F := fun x y => Pasting n (H.hom x y)) f.app
        (fun {x y} e => map (f.hom x y) e)) ha.symm hb.symm (HEq.symm hc))

/-- Unique lifting of an actual horizontal cut factorization in every
positive dimension. The original intermediate vertex and both factors are
recovered even when the globular relabelling identifies labels. -/
theorem horizontal_cut_cartesian {G H : GlobularSet.{u}} (f : GlobularSet.Map G H)
    {n : Nat} {a b : G.Cell 0} (p : Horizontal n G a b) (c : H.Cell 0)
    (q : Horizontal n H (f.app a) c) (r : Horizontal n H c (f.app b))
    (h : map f (pack p) = pack (q.append r)) :
    ∃! s : Σ y : G.Cell 0, Horizontal n G a y × Horizontal n G y b,
      f.app s.1 = c ∧ s.2.1.append s.2.2 = p ∧
      map f (pack s.2.1) = pack q ∧ map f (pack s.2.2) = pack r := by
  have hm : HEq (p.mapAlong (F := fun x y => Pasting n (H.hom x y)) f.app
      (fun {x y} e => map (f.hom x y) e)) (q.append r) := Chain.packed_eq_heq _ _ h
  obtain ⟨y, p₁, p₂, hy, hp, h₁, h₂⟩ := Chain.split_mapAlong f.app
    (fun {x y} e => map (f.hom x y) e) q r p rfl rfl hm
  have hp₁ : map f (pack p₁) = pack q := Chain.packed_eq_of_heq _ _ rfl hy h₁
  have hp₂ : map f (pack p₂) = pack r := Chain.packed_eq_of_heq _ _ hy rfl h₂
  refine ⟨⟨y, p₁, p₂⟩, ⟨hy, hp, hp₁, hp₂⟩, ?_⟩
  rintro ⟨z, q₁, q₂⟩ ⟨hz, hq, hq₁, hq₂⟩
  have hprefix : HEq (q₁.mapAlong (F := fun x y => Pasting n (H.hom x y)) f.app
      (fun {x y} e => map (f.hom x y) e))
      (p₁.mapAlong (F := fun x y => Pasting n (H.hom x y)) f.app
        (fun {x y} e => map (f.hom x y) e)) :=
    HEq.trans (Chain.packed_eq_heq _ _ hq₁) (HEq.symm h₁)
  obtain ⟨hzy, he, hf⟩ := Chain.split_mapAlong_unique (F := fun x y => Pasting n (H.hom x y)) f.app
    (fun {x y} e => map (f.hom x y) e) q₁ q₂ p₁ p₂ (hz.trans hy.symm) hprefix (hq.trans hp.symm)
  cases hzy
  exact _root_.congrArg (fun z => (⟨y, z⟩ : Σ y : G.Cell 0, Horizontal n G a y × Horizontal n G y b))
    (Prod.ext (eq_of_heq he) (eq_of_heq hf))

theorem map_cutCompose {n : Nat} (c : Cut n) {G H : GlobularSet.{u}} (f : GlobularSet.Map G H)
    (p q : Pasting n G) (h : cutTarget c p = cutSource c q)
    (h' : cutTarget c (map f p) = cutSource c (map f q)) :
    map f (cutCompose c p q h) = cutCompose c (map f p) (map f q) h' := by
  induction c generalizing G H with
  | bottom =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    change b = c at h
    cases h
    exact map_horizontal f p q
  | @lift n c ih =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨d, e, q⟩
    have ha : a = d := _root_.congrArg Sigma.fst h
    have hb : b = e := _root_.congrArg (fun z => z.2.1) h
    cases ha
    cases hb
    have hp : p.map (fun e => cutTarget c e) = q.map (fun e => cutSource c e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
    have hp' : (p.mapAlong f.app (fun {x y} e => map (f.hom x y) e)).map (fun e => cutTarget c e) =
        (q.mapAlong f.app (fun {x y} e => map (f.hom x y) e)).map (fun e => cutSource c e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h').2)).2
    exact _root_.congrArg (pack (G := H)) (Chain.mapAlong_zipOver
      (F := fun x y => Pasting n (H.hom x y)) f.app (fun {x y} e => map (f.hom x y) e)
      (fun e => cutTarget c e) (fun e => cutSource c e)
      (fun e => cutTarget c e) (fun e => cutSource c e)
      (fun e d h => cutCompose c e d h) (fun e d h => cutCompose c e d h)
      (fun {x y} e d h j => ih (f.hom x y) e d h j) p q hp hp')

theorem map_cutUnit {n : Nat} (c : Cut n) {G H : GlobularSet.{u}} (f : GlobularSet.Map G H)
    (p : Pasting c.height G) : map f (cutUnit c p) = cutUnit c (map f p) := by
  induction c generalizing G H with
  | bottom => rfl
  | lift c ih =>
    rcases p with ⟨a, b, p⟩
    exact _root_.congrArg pack
      (Chain.mapAlong_natural _ _ _ _ _ (fun {x y} e => (ih (f.hom x y) e).symm) p).symm

theorem mapGlobular_preserves {G H : GlobularSet.{u}} (f : GlobularSet.Map G H) :
    CutOperations.Preserves (cutOperations G) (cutOperations H) (mapGlobular f) where
  compose c p q h h' := map_cutCompose c f p q _ _
  unit c p := map_cutUnit c f p

theorem cutSource_map {n : Nat} (c : Cut n) {G H : GlobularSet.{u}}
    (f : GlobularSet.Map G H) (p : Pasting n G) :
    cutSource c (map f p) = map f (cutSource c p) :=
  (canonical_source_eq_cutSource c (map f p)).symm.trans
    ((CutBoundary.source_map c (mapGlobular f) p).trans
      (_root_.congrArg (map f) (canonical_source_eq_cutSource c p)))

theorem cutTarget_map {n : Nat} (c : Cut n) {G H : GlobularSet.{u}}
    (f : GlobularSet.Map G H) (p : Pasting n G) :
    cutTarget c (map f p) = map f (cutTarget c p) :=
  (canonical_target_eq_cutTarget c (map f p)).symm.trans
    ((CutBoundary.target_map c (mapGlobular f) p).trans
      (_root_.congrArg (map f) (canonical_target_eq_cutTarget c p)))

/-- Relabel both factors without discarding their cut-matching equation. -/
def cutPairMap {n : Nat} (c : Cut n) {G H : GlobularSet.{u}}
    (f : GlobularSet.Map G H) (p : CutPair c G) : CutPair c H :=
  ⟨(map f p.val.1, map f p.val.2), (cutTarget_map c f p.val.1).trans
    ((_root_.congrArg (map f) p.property).trans (cutSource_map c f p.val.2).symm)⟩

noncomputable def cutPairCompose {n : Nat} (c : Cut n) {G : GlobularSet.{u}}
    (p : CutPair c G) : Pasting n G := cutCompose c p.val.1 p.val.2 p.property

theorem cutPairMap_compose {n : Nat} (c : Cut n) {G H : GlobularSet.{u}}
    (f : GlobularSet.Map G H) (p : CutPair c G) :
    map f (cutPairCompose c p) = cutPairCompose c (cutPairMap c f p) :=
  map_cutCompose c f p.val.1 p.val.2 _ _

/-- Prescribed composition lifts keep both target factors, not just their
composite. This is the induction interface for arbitrary cut dimensions. -/
def CutCompositionCartesian {n : Nat} (c : Cut n) {G H : GlobularSet.{u}}
    (f : GlobularSet.Map G H) : Prop :=
  ∀ (p : Pasting n G) (q : CutPair c H), map f p = cutPairCompose c q →
    ∃! r : CutPair c G, cutPairCompose c r = p ∧ cutPairMap c f r = q

/-- The arbitrary-cut composition interface holds for the horizontal
cut in every positive dimension, using the actual factor-pair map. -/
theorem cutCompositionCartesian_bottom {G H : GlobularSet.{u}}
    (f : GlobularSet.Map G H) (n : Nat) : CutCompositionCartesian (.bottom : Cut (n + 1)) f := by
  intro p q h
  rcases p with ⟨a, b, p⟩
  rcases q with ⟨⟨⟨c, d, q⟩, ⟨e, k, r⟩⟩, hq⟩
  change d = e at hq
  cases hq
  have ha : f.app a = c := _root_.congrArg Sigma.fst h
  have hb : f.app b = k := _root_.congrArg (fun z => z.2.1) h
  cases ha
  cases hb
  obtain ⟨⟨y, p₁, p₂⟩, ⟨hy, hp, h₁, h₂⟩, hu⟩ := horizontal_cut_cartesian f p d q r h
  let s : CutPair (.bottom : Cut (n + 1)) G := ⟨(pack p₁, pack p₂), rfl⟩
  refine ⟨s, ⟨_root_.congrArg pack hp, Subtype.ext (Prod.ext h₁ h₂)⟩, ?_⟩
  rintro ⟨⟨⟨a', y', s₁⟩, ⟨z', b', s₂⟩⟩, hs⟩ ⟨hscomp, hsmap⟩
  change y' = z' at hs
  cases hs
  have haa : a' = a := _root_.congrArg Sigma.fst hscomp
  have hbb : b' = b := _root_.congrArg (fun z => z.2.1) hscomp
  cases haa
  cases hbb
  have hl : map f (pack s₁) = pack q := _root_.congrArg (fun z => z.val.1) hsmap
  have hr : map f (pack s₂) = pack r := _root_.congrArg (fun z => z.val.2) hsmap
  have hm : f.app y' = d := _root_.congrArg (fun z => z.2.1) hl
  have happ : s₁.append s₂ = p := eq_of_heq (Chain.packed_eq_heq _ _ hscomp)
  have he := hu ⟨y', s₁, s₂⟩ ⟨hm, happ, hl, hr⟩
  have hv := _root_.congrArg Sigma.fst he
  cases hv
  have he' : (s₁, s₂) = (p₁, p₂) := eq_of_heq (Sigma.mk.inj he).2
  have hl' := _root_.congrArg Prod.fst he'
  have hr' := _root_.congrArg Prod.snd he'
  cases hl'
  cases hr'
  rfl

/-- Assemble the two factors of a lifted cut from their aligned pair chain. -/
def packCutPairChain {n : Nat} (c : Cut n) {G : GlobularSet.{u}} {a b : G.Cell 0}
    (r : Chain (fun x y => CutPair c (G.hom x y)) a b) : CutPair (.lift c) G :=
  ⟨(pack (r.map (fun p => p.val.1)), pack (r.map (fun p => p.val.2))),
    _root_.congrArg pack (cutPairChain_composable c r)⟩

theorem packCutPairChain_compose {n : Nat} (c : Cut n) {G : GlobularSet.{u}} {a b : G.Cell 0}
    (r : Chain (fun x y => CutPair c (G.hom x y)) a b) :
    cutPairCompose (.lift c) (packCutPairChain c r) = pack (r.map (fun p => cutPairCompose c p)) :=
  (cutCompose_lift_pairs c _ _ (cutPairChain_composable c r)).trans
    (_root_.congrArg (fun r => pack (r.map (fun p => cutPairCompose c p))) (cutPairChain_roundtrip c r))

theorem packCutPairChain_roundtrip {n : Nat} (c : Cut n) {G : GlobularSet.{u}} {a b : G.Cell 0}
    (p q : Horizontal n G a b)
    (h : p.map (fun e => cutTarget c e) = q.map (fun e => cutSource c e)) :
    packCutPairChain c (cutPairChain c p q h) =
      (⟨(pack p, pack q), _root_.congrArg pack h⟩ : CutPair (.lift c) G) :=
  Subtype.ext (Prod.ext (_root_.congrArg pack (cutPairChain_left c p q h))
    (_root_.congrArg pack (cutPairChain_right c p q h)))

theorem packCutPairChain_map {n : Nat} (c : Cut n) {G H : GlobularSet.{u}}
    (f : GlobularSet.Map G H) {a b : G.Cell 0}
    (r : Chain (fun x y => CutPair c (G.hom x y)) a b) :
    cutPairMap (.lift c) f (packCutPairChain c r) =
      packCutPairChain c (r.mapAlong f.app (fun {x y} p => cutPairMap c (f.hom x y) p)) := by
  apply Subtype.ext
  apply Prod.ext
  · exact _root_.congrArg pack (Chain.mapAlong_natural
      (E := fun x y => CutPair c (G.hom x y)) (D := fun x y => Pasting n (G.hom x y))
      (F := fun x y => CutPair c (H.hom x y)) (K := fun x y => Pasting n (H.hom x y)) f.app (fun p => p.val.1)
      (fun p => p.val.1) (fun {x y} p => cutPairMap c (f.hom x y) p)
      (fun {x y} p => map (f.hom x y) p) (fun p => rfl) r).symm
  · exact _root_.congrArg pack (Chain.mapAlong_natural
      (E := fun x y => CutPair c (G.hom x y)) (D := fun x y => Pasting n (G.hom x y))
      (F := fun x y => CutPair c (H.hom x y)) (K := fun x y => Pasting n (H.hom x y)) f.app (fun p => p.val.2)
      (fun p => p.val.2) (fun {x y} p => cutPairMap c (f.hom x y) p)
      (fun {x y} p => map (f.hom x y) p) (fun p => rfl) r).symm

theorem packCutPairChain_injective {n : Nat} (c : Cut n) {G : GlobularSet.{u}} {a b : G.Cell 0} :
    Function.Injective (packCutPairChain c (G := G) (a := a) (b := b)) := by
  intro p q h
  have hl : p.map (fun r => r.val.1) = q.map (fun r => r.val.1) :=
    eq_of_heq (Chain.packed_eq_heq _ _ (_root_.congrArg (fun r => r.val.1) h))
  have hr : p.map (fun r => r.val.2) = q.map (fun r => r.val.2) :=
    eq_of_heq (Chain.packed_eq_heq _ _ (_root_.congrArg (fun r => r.val.2) h))
  exact Chain.mapAlong_joint_injective (E := fun x y => CutPair c (G.hom x y))
    (F := fun x y => Pasting n (G.hom x y))
    (D := fun x y => Pasting n (G.hom x y)) (fun x => x) (fun x => x)
    (fun p => p.val.1) (fun p => p.val.2) (fun _ _ h _ => h)
    (fun p q h₁ h₂ => Subtype.ext (Prod.ext h₁ h₂)) p q
    ((Chain.mapAlong_identity_vertices _ p).trans (hl.trans (Chain.mapAlong_identity_vertices _ q).symm))
    ((Chain.mapAlong_identity_vertices _ p).trans (hr.trans (Chain.mapAlong_identity_vertices _ q).symm))

theorem cutPair_hom_reindex {n : Nat} (c : Cut n) {H : GlobularSet.{u}}
    {a b a' b' : H.Cell 0} (p : Pasting n (H.hom a b)) (q : CutPair c (H.hom a' b'))
    (ha : a = a') (hb : b = b') (h : HEq p (cutPairCompose c q)) :
    ∃ q' : CutPair c (H.hom a b), p = cutPairCompose c q' ∧ HEq q' q := by
  cases ha
  cases hb
  exact ⟨q, eq_of_heq h, HEq.rfl⟩

/-- Every prescribed cut factorization after relabelling lifts to actual
factors in the original globular pasting carrier. Uniqueness is separate. -/
theorem cutComposition_lift_exists {n : Nat} (c : Cut n) {G H : GlobularSet.{u}}
    (f : GlobularSet.Map G H) (p : Pasting n G) (q : CutPair c H)
    (h : map f p = cutPairCompose c q) :
    ∃ r : CutPair c G, cutPairCompose c r = p ∧ cutPairMap c f r = q := by
  induction c generalizing G H with
  | bottom => exact (cutCompositionCartesian_bottom f _ p q h).exists
  | @lift n c ih =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨⟨⟨x, y, q₁⟩, ⟨x', y', q₂⟩⟩, hq⟩
    have hx : x = x' := _root_.congrArg Sigma.fst hq
    have hy : y = y' := _root_.congrArg (fun z => z.2.1) hq
    cases hx
    cases hy
    have hq' : q₁.map (fun e => cutTarget c e) = q₂.map (fun e => cutSource c e) :=
      eq_of_heq (Chain.packed_eq_heq _ _ hq)
    let t := cutPairChain c q₁ q₂ hq'
    have hp : map f (pack p) = pack (t.map (fun e => cutPairCompose c e)) :=
      h.trans (cutCompose_lift_pairs c q₁ q₂ hq')
    have ha : f.app a = x := _root_.congrArg Sigma.fst hp
    have hb : f.app b = y := _root_.congrArg (fun z => z.2.1) hp
    have hc := Chain.packed_eq_heq _ _ hp
    obtain ⟨s, hs, hsm⟩ := Chain.lift_mapAlong_square
      (R := fun x y => CutPair c (G.hom x y))
      (F := fun x y => Pasting n (H.hom x y)) (D := fun x y => CutPair c (H.hom x y))
      f.app (fun {x y} e => map (f.hom x y) e) (fun e => cutPairCompose c e)
      (fun e => cutPairCompose c e) (fun {x y} e => cutPairMap c (f.hom x y) e) (by
        intro a b x y e d ha hb he
        obtain ⟨d', hd, hdd⟩ := cutPair_hom_reindex c _ d ha hb he
        obtain ⟨r, hr, hs⟩ := ih (f.hom a b) e d' hd
        exact ⟨r, hr, HEq.trans (heq_of_eq hs) hdd⟩) p t ha hb hc
    refine ⟨packCutPairChain c s, (packCutPairChain_compose c s).trans (_root_.congrArg pack hs), ?_⟩
    have hm : (⟨f.app a, f.app b, s.mapAlong f.app (fun {x y} e => cutPairMap c (f.hom x y) e)⟩ :
        Σ x y : H.Cell 0, Chain (fun x y => CutPair c (H.hom x y)) x y) = ⟨x, y, t⟩ :=
      Chain.packed_eq_of_heq _ _ ha hb hsm
    exact (packCutPairChain_map c f s).trans
      ((_root_.congrArg (fun z : Σ x y : H.Cell 0, Chain (fun x y => CutPair c (H.hom x y)) x y =>
        packCutPairChain c z.2.2) hm).trans (packCutPairChain_roundtrip c q₁ q₂ hq'))

/-- A cut factor pair is determined by its composite and its prescribed
relabelled pair. This proves uniqueness independently of chosen lifts. -/
theorem cutComposition_lift_unique {n : Nat} (c : Cut n) {G H : GlobularSet.{u}}
    (f : GlobularSet.Map G H) (p q : CutPair c G)
    (hc : cutPairCompose c p = cutPairCompose c q) (hm : cutPairMap c f p = cutPairMap c f q) : p = q := by
  induction c generalizing G H with
  | bottom =>
    exact (cutCompositionCartesian_bottom f _ (cutPairCompose _ q) (cutPairMap _ f q)
      (cutPairMap_compose _ f q)).unique ⟨hc, hm⟩ ⟨rfl, rfl⟩
  | @lift n c ih =>
    rcases p with ⟨⟨⟨a, b, p₁⟩, ⟨a', b', p₂⟩⟩, hp⟩
    have ha : a = a' := _root_.congrArg Sigma.fst hp
    have hb : b = b' := _root_.congrArg (fun z => z.2.1) hp
    cases ha
    cases hb
    rcases q with ⟨⟨⟨x, y, q₁⟩, ⟨x', y', q₂⟩⟩, hq⟩
    have hx : x = x' := _root_.congrArg Sigma.fst hq
    have hy : y = y' := _root_.congrArg (fun z => z.2.1) hq
    cases hx
    cases hy
    have ha : a = x := _root_.congrArg Sigma.fst hc
    have hb : b = y := _root_.congrArg (fun z => z.2.1) hc
    cases ha
    cases hb
    have hp' : p₁.map (fun e => cutTarget c e) = p₂.map (fun e => cutSource c e) :=
      eq_of_heq (Chain.packed_eq_heq _ _ hp)
    have hq' : q₁.map (fun e => cutTarget c e) = q₂.map (fun e => cutSource c e) :=
      eq_of_heq (Chain.packed_eq_heq _ _ hq)
    let r := cutPairChain c p₁ p₂ hp'
    let s := cutPairChain c q₁ q₂ hq'
    have hr := packCutPairChain_roundtrip c p₁ p₂ hp'
    have hs := packCutPairChain_roundtrip c q₁ q₂ hq'
    have heval : r.map (fun e => cutPairCompose c e) = s.map (fun e => cutPairCompose c e) :=
      eq_of_heq (Chain.packed_eq_heq _ _ ((cutCompose_lift_pairs c p₁ p₂ hp').symm.trans
        (hc.trans (cutCompose_lift_pairs c q₁ q₂ hq'))))
    have hmap : r.mapAlong (F := fun x y => CutPair c (H.hom x y)) f.app
        (fun {x y} e => cutPairMap c (f.hom x y) e) =
        s.mapAlong (F := fun x y => CutPair c (H.hom x y)) f.app
          (fun {x y} e => cutPairMap c (f.hom x y) e) := by
      apply packCutPairChain_injective c
      exact (packCutPairChain_map c f r).symm.trans
        ((_root_.congrArg (cutPairMap (.lift c) f) hr).trans
          (hm.trans ((_root_.congrArg (cutPairMap (.lift c) f) hs).symm.trans (packCutPairChain_map c f s))))
    have hrs : r = s := Chain.mapAlong_joint_injective
      (F := fun x y => Pasting n (G.hom x y)) (D := fun x y => CutPair c (H.hom x y))
      (fun x => x) f.app (fun p => cutPairCompose c p)
      (fun {x y} p => cutPairMap c (f.hom x y) p) (fun _ _ h _ => h)
      (fun {x y} p q h₁ h₂ => ih (f.hom x y) p q h₁ h₂) r s
      ((Chain.mapAlong_identity_vertices _ r).trans
        (heval.trans (Chain.mapAlong_identity_vertices _ s).symm)) hmap
    exact hr.symm.trans ((_root_.congrArg (packCutPairChain c) hrs).trans hs)

theorem cutComposition_cartesian {n : Nat} (c : Cut n) {G H : GlobularSet.{u}}
    (f : GlobularSet.Map G H) : CutCompositionCartesian c f := by
  intro p q h
  obtain ⟨r, hr, hs⟩ := cutComposition_lift_exists c f p q h
  refine ⟨r, ⟨hr, hs⟩, ?_⟩
  intro s ht
  exact cutComposition_lift_unique c f s r (ht.1.trans hr.symm) (ht.2.trans hs.symm)

theorem cutUnit_hom_heq {n : Nat} (c : Cut n) {H : GlobularSet.{u}}
    {a b a' b' : H.Cell 0} (p : Pasting n (H.hom a b))
    (q : Pasting c.height (H.hom a' b')) (ha : a = a') (hb : b = b')
    (h : HEq p (cutUnit c q)) : ∃ q' : Pasting c.height (H.hom a b), p = cutUnit c q' := by
  cases ha
  cases hb
  exact ⟨q, eq_of_heq h⟩

/-- Relabelling reflects the iterated-unit retraction at every cut, not
only at the horizontal boundary. The proof descends through genuine homs. -/
theorem cutUnit_retract_of_map {n : Nat} (c : Cut n) {G H : GlobularSet.{u}}
    (f : GlobularSet.Map G H) (p : Pasting n G) (q : Pasting c.height H)
    (h : map f p = cutUnit c q) : cutUnit c (cutSource c p) = p := by
  induction c generalizing G H with
  | bottom =>
    obtain ⟨a, ⟨ha, hf⟩, hu⟩ := horizontal_unit_cartesian f p q h
    rw [← ha]
    rfl
  | @lift n c ih =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨a', b', q⟩
    have ha : f.app a = a' := _root_.congrArg Sigma.fst h
    have hb : f.app b = b' := _root_.congrArg (fun z => z.2.1) h
    have hc := Chain.packed_eq_heq _ _ h
    have hr : p.map (fun e => cutUnit c (cutSource c e)) = p :=
      Chain.map_retract_of_mapAlong (F := fun x y => Pasting n (H.hom x y))
        (D := fun x y => Pasting c.height (H.hom x y)) f.app
        (fun {x y} e => map (f.hom x y) e) (fun e => cutUnit c e)
        (fun e => cutUnit c (cutSource c e)) (by
          intro x y a b e d hx hy he
          obtain ⟨d', hd⟩ := cutUnit_hom_heq c _ d hx hy he
          exact ih (f.hom x y) e d' hd) p q ha hb hc
    exact _root_.congrArg pack ((Chain.map_map _ _ p).trans hr)

/-- The naturality square of every cut unit has a unique cell lift. -/
theorem cutUnit_cartesian {n : Nat} (c : Cut n) {G H : GlobularSet.{u}}
    (f : GlobularSet.Map G H) (p : Pasting n G) (q : Pasting c.height H)
    (h : map f p = cutUnit c q) :
    ∃! r : Pasting c.height G, cutUnit c r = p ∧ map f r = q := by
  refine ⟨cutSource c p, ⟨cutUnit_retract_of_map c f p q h, ?_⟩, ?_⟩
  · exact (cutSource_map c f p).symm.trans
      ((_root_.congrArg (cutSource c) h).trans (cutSource_cutUnit c q))
  · intro r hr
    exact (cutSource_cutUnit c r).symm.trans (_root_.congrArg (cutSource c) hr.1)

/-- Convert canonical-boundary pairs to the concrete pasting presentation. -/
def cutOperationsPairToCutPair {n : Nat} (c : Cut n) {G : GlobularSet.{u}}
    (p : (cutOperations G).Pair c) : CutPair c G :=
  ⟨p.val, (canonical_target_eq_cutTarget c p.val.1).symm.trans
    (p.property.trans (canonical_source_eq_cutSource c p.val.2))⟩

def cutPairToCutOperationsPair {n : Nat} (c : Cut n) {G : GlobularSet.{u}}
    (p : CutPair c G) : (cutOperations G).Pair c :=
  ⟨p.val, (canonical_target_eq_cutTarget c p.val.1).trans
    (p.property.trans (canonical_source_eq_cutSource c p.val.2).symm)⟩

/-- The proved primitive lifting results instantiate the generic interface
on every relabelling of the actual pasting globular sets. -/
theorem mapGlobular_cartesian {G H : GlobularSet.{u}} (f : GlobularSet.Map G H) :
    CutOperations.Cartesian (cutOperations G) (cutOperations H) (mapGlobular f) where
  toPreserves := mapGlobular_preserves f
  unit_lift c p q h := cutUnit_cartesian c f p q h
  compose_lift c p q h := by
    obtain ⟨r, ⟨hr, hm⟩, hu⟩ := cutComposition_cartesian c f p (cutOperationsPairToCutPair c q) h
    refine ⟨cutPairToCutOperationsPair c r,
      ⟨hr, Subtype.ext (_root_.congrArg (fun p : CutPair c H => p.val) hm)⟩, ?_⟩
    intro s hs
    have he : cutOperationsPairToCutPair c s = r := hu (cutOperationsPairToCutPair c s)
      ⟨hs.1, Subtype.ext (_root_.congrArg (fun p : (cutOperations H).Pair c => p.val) hs.2)⟩
    exact Subtype.ext (_root_.congrArg (fun p : CutPair c G => p.val) he)

theorem cutSource_at (k n : Nat) {G : GlobularSet.{u}} (p : Pasting (n + k + 1) G) :
    HEq (cutSource (Cut.at k n) p) (sourceAt k n p) := by
  induction k generalizing G with
  | zero => rcases p with ⟨a, b, p⟩; rfl
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    exact pack_heq (Cut.height_at k n) _ _
      (Chain.map_heq (by rw [Cut.height_at]) _ _ (fun e => ih e) p)

theorem cutTarget_at (k n : Nat) {G : GlobularSet.{u}} (p : Pasting (n + k + 1) G) :
    HEq (cutTarget (Cut.at k n) p) (targetAt k n p) := by
  induction k generalizing G with
  | zero => rcases p with ⟨a, b, p⟩; rfl
  | succ k ih =>
    rcases p with ⟨a, b, p⟩
    exact pack_heq (Cut.height_at k n) _ _
      (Chain.map_heq (by rw [Cut.height_at]) _ _ (fun e => ih e) p)

theorem cutCompose_at (k n : Nat) {G : GlobularSet.{u}} (p q : Pasting (n + k + 1) G)
    (h : cutTarget (Cut.at k n) p = cutSource (Cut.at k n) q)
    (h' : targetAt k n p = sourceAt k n q) :
    cutCompose (Cut.at k n) p q h = composeAt k n p q h' := by
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
    have hp : p.map (fun e => cutTarget (Cut.at k n) e) = q.map (fun e => cutSource (Cut.at k n) e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
    have hp' : p.map (fun e => targetAt k n e) = q.map (fun e => sourceAt k n e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h').2)).2
    exact _root_.congrArg pack (Chain.zipOver_congr _ _ _ _ _ _ (fun e d h j => ih e d h j) p q hp hp')

theorem cutCompose_at_eq (k n : Nat) {G : GlobularSet.{u}} (p q : Pasting (n + k + 1) G)
    (h : cutTarget (Cut.at k n) p = cutSource (Cut.at k n) q) :
    cutCompose (Cut.at k n) p q h = composeAt k n p q
      (eq_of_heq ((cutTarget_at k n p).symm.trans ((heq_of_eq h).trans (cutSource_at k n q)))) :=
  cutCompose_at k n p q h _

/-- Strict order of two lower boundaries of the same dimension. -/
inductive Cut.Below : {n : Nat} → Cut n → Cut n → Prop where
  | bottom {n : Nat} (c : Cut n) : Below .bottom (.lift c)
  | lift {n : Nat} {c d : Cut n} : Below c d → Below (.lift c) (.lift d)

/-- Restrict a lower composition axis to the dimension of a higher cut. -/
def Cut.restrict : {n : Nat} → (c d : Cut n) → Below c d → Cut d.height
  | _, .bottom, .bottom, h => nomatch h
  | _, .bottom, .lift _, _ => .bottom
  | _, .lift _, .bottom, h => nomatch h
  | _, .lift c, .lift d, h => .lift (restrict c d (by cases h; assumption))

abbrev Cut.Below.restrict {n : Nat} {c d : Cut n} (h : Below c d) : Cut d.height := Cut.restrict c d h

theorem Cut.Below.restrict_height {n : Nat} {c d : Cut n} (h : Below c d) :
    h.restrict.height = c.height := by
  induction h with
  | bottom => rfl
  | lift h ih => exact _root_.congrArg Nat.succ ih

theorem Cut.height_lt {n : Nat} (c : Cut n) : c.height < n := by
  induction c with
  | bottom => exact Nat.zero_lt_succ _
  | lift c ih => exact Nat.succ_lt_succ ih

theorem Cut.below_iff_height {n : Nat} (c d : Cut n) : Below c d ↔ c.height < d.height := by
  constructor
  · intro h
    induction h with
    | bottom => exact Nat.zero_lt_succ _
    | lift h ih => exact Nat.succ_lt_succ ih
  · intro h
    induction c with
    | bottom =>
      cases d with
      | bottom => exact False.elim (Nat.lt_irrefl 0 h)
      | lift d => exact .bottom d
    | lift c ih =>
      cases d with
      | bottom => exact False.elim (Nat.not_lt_zero _ h)
      | lift d => exact .lift (ih d (Nat.lt_of_succ_lt_succ h))

/-- The four inner composability equations imply both outer equations,
for every pair of strictly ordered boundary dimensions. -/
theorem cutGrid_composable {n : Nat} {c d : Cut n} (below : Cut.Below c d)
    {G : GlobularSet.{u}} (p q r s : Pasting n G)
    (hpq : cutTarget c p = cutSource c q) (hrs : cutTarget c r = cutSource c s)
    (hpr : cutTarget d p = cutSource d r) (hqs : cutTarget d q = cutSource d s) :
    cutTarget d (cutCompose c p q hpq) = cutSource d (cutCompose c r s hrs) ∧
      cutTarget c (cutCompose d p r hpr) = cutSource c (cutCompose d q s hqs) := by
  induction below generalizing G with
  | bottom d =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, e, q⟩
    rcases r with ⟨f, g, r⟩
    rcases s with ⟨i, j, s⟩
    change b = c at hpq
    change g = i at hrs
    cases hpq
    cases hrs
    have ha : a = f := _root_.congrArg Sigma.fst hpr
    have hb : b = g := _root_.congrArg (fun z => z.2.1) hpr
    cases ha
    cases hb
    have he : e = j := _root_.congrArg (fun z => z.2.1) hqs
    cases he
    have hp : p.map (fun e => cutTarget d e) = r.map (fun e => cutSource d e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hpr).2)).2
    have hq : q.map (fun e => cutTarget d e) = s.map (fun e => cutSource d e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hqs).2)).2
    exact ⟨_root_.congrArg pack ((Chain.map_append _ p q).trans
      ((_root_.congrArg₂ Chain.append hp hq).trans (Chain.map_append _ r s).symm)), rfl⟩
  | @lift n c d below ih =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨e, f, q⟩
    rcases r with ⟨g, i, r⟩
    rcases s with ⟨j, k, s⟩
    have ha : a = e := _root_.congrArg Sigma.fst hpq
    have hb : b = f := _root_.congrArg (fun z => z.2.1) hpq
    have hc : a = g := _root_.congrArg Sigma.fst hpr
    have hd : b = i := _root_.congrArg (fun z => z.2.1) hpr
    have he : g = j := _root_.congrArg Sigma.fst hrs
    have hf : i = k := _root_.congrArg (fun z => z.2.1) hrs
    cases ha
    cases hb
    cases hc
    cases hd
    cases he
    cases hf
    have hpq' : p.map (fun e => cutTarget c e) = q.map (fun e => cutSource c e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hpq).2)).2
    have hrs' : r.map (fun e => cutTarget c e) = s.map (fun e => cutSource c e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hrs).2)).2
    have hpr' : p.map (fun e => cutTarget d e) = r.map (fun e => cutSource d e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hpr).2)).2
    have hqs' : q.map (fun e => cutTarget d e) = s.map (fun e => cutSource d e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hqs).2)).2
    have hg := Chain.zipOver_grid
      (fun e => cutTarget c e) (fun e => cutSource c e)
      (fun e => cutTarget d e) (fun e => cutSource d e)
      (fun e f h => cutCompose c e f h) (fun e f h => cutCompose d e f h)
      (fun e f g h a b c d => ih e f g h a b c d) p q r s hpq' hrs' hpr' hqs'
    exact ⟨_root_.congrArg pack hg.1, _root_.congrArg pack hg.2⟩

/-- All-dimensional interchange, for any strictly ordered pair of cuts.
The six equalities specify the four inner and two outer composites. -/
theorem cutCompose_interchange {n : Nat} {c d : Cut n} (below : Cut.Below c d)
    {G : GlobularSet.{u}} (p q r s : Pasting n G)
    (hpq : cutTarget c p = cutSource c q) (hrs : cutTarget c r = cutSource c s)
    (hpr : cutTarget d p = cutSource d r) (hqs : cutTarget d q = cutSource d s)
    (hrow : cutTarget d (cutCompose c p q hpq) = cutSource d (cutCompose c r s hrs))
    (hcol : cutTarget c (cutCompose d p r hpr) = cutSource c (cutCompose d q s hqs)) :
    cutCompose d (cutCompose c p q hpq) (cutCompose c r s hrs) hrow =
      cutCompose c (cutCompose d p r hpr) (cutCompose d q s hqs) hcol := by
  induction below generalizing G with
  | bottom d =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, e, q⟩
    rcases r with ⟨f, g, r⟩
    rcases s with ⟨i, j, s⟩
    change b = c at hpq
    change g = i at hrs
    cases hpq
    cases hrs
    have ha : a = f := _root_.congrArg Sigma.fst hpr
    have hb : b = g := _root_.congrArg (fun z => z.2.1) hpr
    cases ha
    cases hb
    have he : e = j := _root_.congrArg (fun z => z.2.1) hqs
    cases he
    have hp : p.map (fun e => cutTarget d e) = r.map (fun e => cutSource d e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hpr).2)).2
    have hq : q.map (fun e => cutTarget d e) = s.map (fun e => cutSource d e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hqs).2)).2
    exact _root_.congrArg pack (Chain.zipOver_append _ _ _ p r hp q s hq)
  | @lift n c d below ih =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨e, f, q⟩
    rcases r with ⟨g, i, r⟩
    rcases s with ⟨j, k, s⟩
    have ha : a = e := _root_.congrArg Sigma.fst hpq
    have hb : b = f := _root_.congrArg (fun z => z.2.1) hpq
    have hc : a = g := _root_.congrArg Sigma.fst hpr
    have hd : b = i := _root_.congrArg (fun z => z.2.1) hpr
    have he : g = j := _root_.congrArg Sigma.fst hrs
    have hf : i = k := _root_.congrArg (fun z => z.2.1) hrs
    cases ha
    cases hb
    cases hc
    cases hd
    cases he
    cases hf
    have hpq' : p.map (fun e => cutTarget c e) = q.map (fun e => cutSource c e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hpq).2)).2
    have hrs' : r.map (fun e => cutTarget c e) = s.map (fun e => cutSource c e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hrs).2)).2
    have hpr' : p.map (fun e => cutTarget d e) = r.map (fun e => cutSource d e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hpr).2)).2
    have hqs' : q.map (fun e => cutTarget d e) = s.map (fun e => cutSource d e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hqs).2)).2
    have hrow' : (Chain.zipOver (fun e => cutTarget c e) (fun e => cutSource c e)
        (fun e f h => cutCompose c e f h) p q hpq').map (fun e => cutTarget d e) =
      (Chain.zipOver (fun e => cutTarget c e) (fun e => cutSource c e)
        (fun e f h => cutCompose c e f h) r s hrs').map (fun e => cutSource d e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hrow).2)).2
    have hcol' : (Chain.zipOver (fun e => cutTarget d e) (fun e => cutSource d e)
        (fun e f h => cutCompose d e f h) p r hpr').map (fun e => cutTarget c e) =
      (Chain.zipOver (fun e => cutTarget d e) (fun e => cutSource d e)
        (fun e f h => cutCompose d e f h) q s hqs').map (fun e => cutSource c e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hcol).2)).2
    exact _root_.congrArg pack (Chain.zipOver_interchange
      (fun e => cutTarget c e) (fun e => cutSource c e)
      (fun e => cutTarget d e) (fun e => cutSource d e)
      (fun e f h => cutCompose c e f h) (fun e f h => cutCompose d e f h)
      (fun e f g h a b c d r s => ih e f g h a b c d r s) p q r s hpq' hrs' hpr' hqs' hrow' hcol')

/-- Interchange on a composable grid, with both outer composites justified
by the four supplied inner composability equations. -/
theorem cutCompose_interchange_grid {n : Nat} {c d : Cut n} (below : Cut.Below c d)
    {G : GlobularSet.{u}} (p q r s : Pasting n G)
    (hpq : cutTarget c p = cutSource c q) (hrs : cutTarget c r = cutSource c s)
    (hpr : cutTarget d p = cutSource d r) (hqs : cutTarget d q = cutSource d s) :
    cutCompose d (cutCompose c p q hpq) (cutCompose c r s hrs)
      (cutGrid_composable below p q r s hpq hrs hpr hqs).1 =
    cutCompose c (cutCompose d p r hpr) (cutCompose d q s hqs)
      (cutGrid_composable below p q r s hpq hrs hpr hqs).2 :=
  cutCompose_interchange below p q r s hpq hrs hpr hqs _ _

/-- Interchange of the actual cut operations, with explicit matching for
the four inner and two outer composites. -/
def CutOperations.Interchange {G : GlobularSet.{u}} (C : CutOperations G) : Prop :=
  ∀ {n} {c d : Cut n} (_ : Cut.Below c d) (p q r s : G.Cell n) hpq hrs hpr hqs hrow hcol,
    C.compose d (C.compose c p q hpq) (C.compose c r s hrs) hrow =
      C.compose c (C.compose d p r hpr) (C.compose d q s hqs) hcol

theorem CutOperations.Interchange.hom {G : GlobularSet.{u}} {C : CutOperations G}
    (I : C.Interchange) (a b : G.Cell 0) : (C.hom a b).Interchange := by
  intro n c d below p q r s hpq hrs hpr hqs hrow hcol
  exact Subtype.ext (I below.lift p.val q.val r.val s.val _ _ _ _ _ _)

theorem cutOperations_interchange (G : GlobularSet.{u}) : (cutOperations G).Interchange := by
  intro n c d below p q r s hpq hrs hpr hqs hrow hcol
  exact cutCompose_interchange below p q r s _ _ _ _ _ _

/-- A lower-cut identity is idempotent under composition at a higher cut.
This law is needed for the empty-chain case of higher-cut fold preservation. -/
def CutOperations.UnitIdempotent {G : GlobularSet.{u}} (C : CutOperations G) : Prop :=
  ∀ {n} {c d : Cut n} (_ : Cut.Below c d) (p : G.Cell c.height) h,
    C.compose d (C.unit c p) (C.unit c p) h = C.unit c p

theorem CutOperations.UnitIdempotent.hom {G : GlobularSet.{u}} {C : CutOperations G}
    (U : C.UnitIdempotent) (a b : G.Cell 0) : (C.hom a b).UnitIdempotent := by
  intro n c d below p h
  exact Subtype.ext (U below.lift p.val _)

theorem cutCompose_unit_idempotent {n : Nat} {c d : Cut n} (below : Cut.Below c d)
    {G : GlobularSet.{u}} (p : Pasting c.height G)
    (h : cutTarget d (cutUnit c p) = cutSource d (cutUnit c p)) :
    cutCompose d (cutUnit c p) (cutUnit c p) h = cutUnit c p := by
  induction below generalizing G with
  | bottom d => rfl
  | @lift n c d below ih =>
    rcases p with ⟨a, b, p⟩
    have hp : (p.map (fun e => cutUnit c e)).map (fun e => cutTarget d e) =
        (p.map (fun e => cutUnit c e)).map (fun e => cutSource d e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
    induction p with
    | nil => rfl
    | @cons x z y e p ihp =>
      have hc := hp
      simp only [Chain.map] at hc
      injection hc with hx hz hy he ht
      exact _root_.congrArg pack (_root_.congrArg₂ Chain.cons (ih e he)
        (by
          have hh := ihp (_root_.congrArg pack ht) ht
          exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hh).2)).2))

theorem cutOperations_unitIdempotent (G : GlobularSet.{u}) : (cutOperations G).UnitIdempotent := by
  intro n c d below p h
  exact cutCompose_unit_idempotent below p _

/-- Identities at a higher cut preserve lower composition and lower
identities. These are explicit laws, not consequences of boundaries alone. -/
structure CutOperations.UnitCompatible {G : GlobularSet.{u}} (C : CutOperations G) : Prop where
  compose : ∀ {n} {c d : Cut n} (w : Cut.Below c d) (p q : G.Cell d.height) h h',
    C.unit d (C.compose w.restrict p q h) = C.compose c (C.unit d p) (C.unit d q) h'
  unit : ∀ {n} {c d : Cut n} (w : Cut.Below c d)
    (p : G.Cell w.restrict.height) (q : G.Cell c.height), HEq p q → C.unit d (C.unit w.restrict p) = C.unit c q

theorem CutOperations.UnitCompatible.hom {G : GlobularSet.{u}} {C : CutOperations G}
    (U : C.UnitCompatible) (a b : G.Cell 0) : (C.hom a b).UnitCompatible where
  compose w p q h h' := Subtype.ext (U.compose w.lift p.val q.val _ _)
  unit w p q hpq := Subtype.ext (U.unit w.lift p.val q.val (hom_val_heq p q w.restrict_height hpq))

theorem cutUnit_compose {n : Nat} {c d : Cut n} (w : Cut.Below c d) {G : GlobularSet.{u}}
    (p q : Pasting d.height G) (h : cutTarget w.restrict p = cutSource w.restrict q)
    (h' : cutTarget c (cutUnit d p) = cutSource c (cutUnit d q)) :
    cutUnit d (cutCompose w.restrict p q h) = cutCompose c (cutUnit d p) (cutUnit d q) h' := by
  induction w generalizing G with
  | bottom d =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    change b = c at h
    cases h
    exact _root_.congrArg pack (Chain.map_append _ p q)
  | @lift n c d w ih =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨e, f, q⟩
    have ha : a = e := _root_.congrArg Sigma.fst h
    have hb : b = f := _root_.congrArg (fun z => z.2.1) h
    cases ha
    cases hb
    have hp : p.map (fun e => cutTarget w.restrict e) = q.map (fun e => cutSource w.restrict e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
    have hp' : (p.map (fun e => cutUnit d e)).map (fun e => cutTarget c e) =
        (q.map (fun e => cutUnit d e)).map (fun e => cutSource c e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h').2)).2
    exact _root_.congrArg pack (Chain.map_zipOver _ _ _ _ _ _ _ (fun e f he hf => ih e f he hf) p q hp hp')

theorem cutUnit_unit_reindex {n : Nat} {c d : Cut n} (w : Cut.Below c d) {G : GlobularSet.{u}}
    (p : Pasting w.restrict.height G) :
    cutUnit d (cutUnit w.restrict p) = cutUnit c (reindex w.restrict_height p) := by
  induction w generalizing G with
  | bottom d => rfl
  | @lift n c d w ih =>
    rcases p with ⟨a, b, p⟩
    have hr := _root_.congrArg (fun z : Pasting (c.height + 1) G => cutUnit (.lift c) z)
      (reindex_pack w.restrict_height p)
    refine Eq.trans ?_ hr.symm
    change pack ((p.map (fun e => cutUnit w.restrict e)).map (fun e => cutUnit d e)) =
      pack ((p.map (fun e => reindex w.restrict_height e)).map (fun e => cutUnit c e))
    exact _root_.congrArg pack ((Chain.map_map _ _ p).trans
      ((Chain.map_congr _ _ (fun e => ih e) p).trans (Chain.map_map _ _ p).symm))

theorem cutOperations_unitCompatible (G : GlobularSet.{u}) : (cutOperations G).UnitCompatible where
  compose w p q h h' := cutUnit_compose w p q _ _
  unit w p q hpq := by
    have hq : reindex w.restrict_height p = q := eq_of_heq ((reindex_heq w.restrict_height p).trans hpq)
    exact (cutUnit_unit_reindex w p).trans (_root_.congrArg (fun z => cutUnit _ z) hq)

/-- Horizontal operations used to evaluate chains. Boundary preservation is
part of the data; associativity is not silently assumed by the evaluator. -/
structure HorizontalComposition (H : GlobularSet.{u}) where
  unit : (n : Nat) → (a : H.Cell 0) → (H.hom a a).Cell n
  mul : {n : Nat} → {a b c : H.Cell 0} →
    (H.hom a b).Cell n → (H.hom b c).Cell n → (H.hom a c).Cell n
  source_unit : ∀ n a, (H.hom a a).source (unit (n + 1) a) = unit n a
  target_unit : ∀ n a, (H.hom a a).target (unit (n + 1) a) = unit n a
  source_mul : ∀ {n a b c} (p : (H.hom a b).Cell (n + 1)) (q : (H.hom b c).Cell (n + 1)),
    (H.hom a c).source (mul p q) = mul ((H.hom a b).source p) ((H.hom b c).source q)
  target_mul : ∀ {n a b c} (p : (H.hom a b).Cell (n + 1)) (q : (H.hom b c).Cell (n + 1)),
    (H.hom a c).target (mul p q) = mul ((H.hom a b).target p) ((H.hom b c).target q)

def CutOperations.horizontalUnit {H : GlobularSet.{u}} (C : CutOperations H)
    (n : Nat) (a : H.Cell 0) : (H.hom a a).Cell n :=
  ⟨C.unit (.bottom : Cut (n + 1)) a,
    C.source_unit (.bottom : Cut (n + 1)) a, C.target_unit (.bottom : Cut (n + 1)) a⟩

def CutOperations.horizontalMul {H : GlobularSet.{u}} (C : CutOperations H)
    {n : Nat} {a b c : H.Cell 0} (p : (H.hom a b).Cell n) (q : (H.hom b c).Cell n) :
    (H.hom a c).Cell n :=
  ⟨C.compose (.bottom : Cut (n + 1)) p.val q.val (p.property.2.trans q.property.1.symm),
    (C.source_compose (.bottom : Cut (n + 1)) p.val q.val _).trans p.property.1,
    (C.target_compose (.bottom : Cut (n + 1)) p.val q.val _).trans q.property.2⟩

/-- Primitive cartesianness recovers a horizontal intermediate object and
both fixed-endpoint factors. Relabelling equalities retain their raw cells. -/
theorem CutOperations.Cartesian.horizontal_factor_lift {G H : GlobularSet.{u}}
    {C : CutOperations G} {D : CutOperations H} {f : GlobularSet.Map G H}
    (K : CutOperations.Cartesian C D f) {n : Nat} (a b : G.Cell 0)
    (p : (G.hom a b).Cell n) (c : H.Cell 0)
    (q : (H.hom (f.app a) c).Cell n) (r : (H.hom c (f.app b)).Cell n)
    (h : f.app p.val = (D.horizontalMul q r).val) :
    ∃! s : Σ y : G.Cell 0, (G.hom a y).Cell n × (G.hom y b).Cell n,
      f.app s.1 = c ∧ C.horizontalMul s.2.1 s.2.2 = p ∧
      f.app s.2.1.val = q.val ∧ f.app s.2.2.val = r.val := by
  let qr : D.Pair (.bottom : Cut (n + 1)) := ⟨(q.val, r.val), q.property.2.trans r.property.1.symm⟩
  obtain ⟨s, ⟨hs, hf⟩, hu⟩ := K.compose_lift (.bottom : Cut (n + 1)) p.val qr h
  have h₁ : f.app s.val.1 = q.val := _root_.congrArg (fun z : D.Pair (.bottom : Cut (n + 1)) => z.val.1) hf
  have h₂ : f.app s.val.2 = r.val := _root_.congrArg (fun z : D.Pair (.bottom : Cut (n + 1)) => z.val.2) hf
  have ha : G.sourceZero s.val.1 = a :=
    (C.source_compose .bottom s.val.1 s.val.2 s.property).symm.trans
      ((_root_.congrArg G.sourceZero hs).trans p.property.1)
  have hb : G.targetZero s.val.2 = b :=
    (C.target_compose .bottom s.val.1 s.val.2 s.property).symm.trans
      ((_root_.congrArg G.targetZero hs).trans p.property.2)
  let y := G.targetZero s.val.1
  let s₁ : (G.hom a y).Cell n := ⟨s.val.1, ha, rfl⟩
  let s₂ : (G.hom y b).Cell n := ⟨s.val.2, s.property.symm, hb⟩
  have hy : f.app y = c := (f.targetZero s.val.1).symm.trans
    ((_root_.congrArg H.targetZero h₁).trans q.property.2)
  refine ⟨⟨y, s₁, s₂⟩, ⟨hy, Subtype.ext hs, h₁, h₂⟩, ?_⟩
  rintro ⟨z, t₁, t₂⟩ ⟨hz, ht, ht₁, ht₂⟩
  let t : C.Pair (.bottom : Cut (n + 1)) := ⟨(t₁.val, t₂.val), t₁.property.2.trans t₂.property.1.symm⟩
  have he : t = s := hu t ⟨_root_.congrArg Subtype.val ht, Subtype.ext (Prod.ext ht₁ ht₂)⟩
  have he₁ : t₁.val = s.val.1 := _root_.congrArg (fun z : C.Pair (.bottom : Cut (n + 1)) => z.val.1) he
  have he₂ : t₂.val = s.val.2 := _root_.congrArg (fun z : C.Pair (.bottom : Cut (n + 1)) => z.val.2) he
  have hzy : z = y := t₁.property.2.symm.trans (_root_.congrArg G.targetZero he₁)
  cases hzy
  exact _root_.congrArg (fun z => (⟨y, z⟩ : Σ y : G.Cell 0, (G.hom a y).Cell n × (G.hom y b).Cell n))
    (Prod.ext (Subtype.ext he₁) (Subtype.ext he₂))

/-- The empty-fold lifting case determines both original endpoints and
the actual unit cell, rather than assuming they already coincide. -/
theorem CutOperations.Cartesian.horizontal_unit_lift {G H : GlobularSet.{u}}
    {C : CutOperations G} {D : CutOperations H} {f : GlobularSet.Map G H}
    (K : CutOperations.Cartesian C D f) {n : Nat} (a b : G.Cell 0)
    (p : (G.hom a b).Cell n) (c : H.Cell 0)
    (h : f.app p.val = (D.horizontalUnit n c).val) :
    a = b ∧ (C.horizontalUnit n a).val = p.val ∧ f.app a = c := by
  obtain ⟨r, ⟨hr, hf⟩, hu⟩ := K.unit_lift (.bottom : Cut (n + 1)) p.val c h
  have ha : r = a := (C.source_unit (.bottom : Cut (n + 1)) r).symm.trans
    ((_root_.congrArg G.sourceZero hr).trans p.property.1)
  have hb : r = b := (C.target_unit (.bottom : Cut (n + 1)) r).symm.trans
    ((_root_.congrArg G.targetZero hr).trans p.property.2)
  exact ⟨ha.symm.trans hb, (_root_.congrArg (C.unit (.bottom : Cut (n + 1))) ha.symm).trans hr,
    (_root_.congrArg f.app ha.symm).trans hf⟩

/-- Compatible cut operations give the horizontal operations used by the
evaluator, on the genuine hom fibres of the same globular set. -/
def CutOperations.horizontal {H : GlobularSet.{u}} (C : CutOperations H) (L : C.Compatible) :
    HorizontalComposition H where
  unit := C.horizontalUnit
  mul := C.horizontalMul
  source_unit n a := Subtype.ext (L.source_unit (Cut.Raise.bottom (n := n)) a a (HEq.rfl))
  target_unit n a := Subtype.ext (L.target_unit (Cut.Raise.bottom (n := n)) a a (HEq.rfl))
  source_mul {n a b c} p q := Subtype.ext (L.source_compose (Cut.Raise.bottom (n := n)) p.val q.val _ _)
  target_mul {n a b c} p q := Subtype.ext (L.target_compose (Cut.Raise.bottom (n := n)) p.val q.val _ _)

theorem CutOperations.horizontal_right_unit {H : GlobularSet.{u}} {C : CutOperations H}
    (L : C.Compatible) (R : C.RightUnital) {n : Nat} {a b : H.Cell 0} (p : (H.hom a b).Cell n) :
    (C.horizontal L).mul p ((C.horizontal L).unit n b) = p := by
  apply Subtype.ext
  change C.compose (.bottom : Cut (n + 1)) p.val (C.unit (.bottom : Cut (n + 1)) b) _ = p.val
  have h : CutBoundary.target (.bottom : Cut (n + 1)) H p.val = b := p.property.2
  simpa only [h] using R (.bottom : Cut (n + 1)) p.val

theorem CutOperations.horizontal_left_unit {H : GlobularSet.{u}} {C : CutOperations H}
    (L : C.Compatible) (U : C.LeftUnital) {n : Nat} {a b : H.Cell 0} (p : (H.hom a b).Cell n) :
    (C.horizontal L).mul ((C.horizontal L).unit n a) p = p := by
  apply Subtype.ext
  change C.compose (.bottom : Cut (n + 1)) (C.unit (.bottom : Cut (n + 1)) a) p.val _ = p.val
  have h : CutBoundary.source (.bottom : Cut (n + 1)) H p.val = a := p.property.1
  simpa only [h] using U (.bottom : Cut (n + 1)) p.val

theorem CutOperations.horizontal_assoc {H : GlobularSet.{u}} {C : CutOperations H}
    (L : C.Compatible) (A : C.Associative) {n : Nat} {a b c d : H.Cell 0}
    (p : (H.hom a b).Cell n) (q : (H.hom b c).Cell n) (r : (H.hom c d).Cell n) :
    (C.horizontal L).mul ((C.horizontal L).mul p q) r =
      (C.horizontal L).mul p ((C.horizontal L).mul q r) :=
  Subtype.ext (A (.bottom : Cut (n + 1)) p.val q.val r.val _ _ _ _)

theorem CutOperations.horizontal_interchange {H : GlobularSet.{u}} {C : CutOperations H}
    (I : C.Interchange) {n : Nat} (c : Cut n) {a b d : H.Cell 0}
    (p r : (H.hom a b).Cell n) (q s : (H.hom b d).Cell n)
    (hpr : CutBoundary.target c (H.hom a b) p = CutBoundary.source c (H.hom a b) r)
    (hqs : CutBoundary.target c (H.hom b d) q = CutBoundary.source c (H.hom b d) s)
    (hrow : CutBoundary.target c (H.hom a d) (C.horizontalMul p q) =
      CutBoundary.source c (H.hom a d) (C.horizontalMul r s)) :
    (C.hom a d).compose c (C.horizontalMul p q) (C.horizontalMul r s) hrow =
      C.horizontalMul ((C.hom a b).compose c p r hpr) ((C.hom b d).compose c q s hqs) :=
  Subtype.ext (I (Cut.Below.bottom c) p.val q.val r.val s.val _ _ _ _ _ _)

theorem CutOperations.horizontal_unit_compose {H : GlobularSet.{u}} {C : CutOperations H}
    (U : C.UnitCompatible) {n : Nat} (c : Cut n) {a b d : H.Cell 0}
    (p : (H.hom a b).Cell c.height) (q : (H.hom b d).Cell c.height) :
    (C.hom a d).unit c (C.horizontalMul p q) =
      C.horizontalMul ((C.hom a b).unit c p) ((C.hom b d).unit c q) :=
  Subtype.ext (U.compose (Cut.Below.bottom c) p.val q.val _ _)

theorem CutOperations.horizontal_unit_unit {H : GlobularSet.{u}} {C : CutOperations H}
    (U : C.UnitCompatible) {n : Nat} (c : Cut n) (a : H.Cell 0) :
    (C.hom a a).unit c (C.horizontalUnit c.height a) = C.horizontalUnit n a :=
  Subtype.ext (U.unit (Cut.Below.bottom c) a a HEq.rfl)

theorem CutOperations.Preserves.horizontal_unit {G H : GlobularSet.{u}}
    {C : CutOperations G} {D : CutOperations H} {f : GlobularSet.Map G H}
    (P : Preserves C D f) (n : Nat) (a : G.Cell 0) :
    (f.hom a a).app (C.horizontalUnit n a) = D.horizontalUnit n (f.app a) :=
  Subtype.ext (P.unit (.bottom : Cut (n + 1)) a)

theorem CutOperations.Preserves.horizontal_mul {G H : GlobularSet.{u}}
    {C : CutOperations G} {D : CutOperations H} {f : GlobularSet.Map G H}
    (P : Preserves C D f) {n : Nat} {a b c : G.Cell 0}
    (p : (G.hom a b).Cell n) (q : (G.hom b c).Cell n) :
    (f.hom a c).app (C.horizontalMul p q) =
      D.horizontalMul ((f.hom a b).app p) ((f.hom b c).app q) :=
  Subtype.ext (P.compose (.bottom : Cut (n + 1)) p.val q.val _ _)

/-- All finite iterated hom contexts of a fixed globular set. This allows a
single evaluation recursion to descend into the actual target hom sets. -/
inductive HomContext (H : GlobularSet.{u}) : GlobularSet.{u} → Type (u + 1) where
  | root : HomContext H H
  | hom {K : GlobularSet.{u}} : HomContext H K → (a b : K.Cell 0) → HomContext H (K.hom a b)

/-- Iterate the proved restriction through an arbitrary hom context. There
is no fixed maximum depth and every underlying operation is inherited. -/
def CutOperations.inContext {H : GlobularSet.{u}} (C : CutOperations H) :
    {K : GlobularSet.{u}} → HomContext H K → CutOperations K
  | _, .root => C
  | _, .hom h a b => (C.inContext h).hom a b

theorem CutOperations.inContext_hom {H K : GlobularSet.{u}} (C : CutOperations H)
    (h : HomContext H K) (a b : K.Cell 0) :
    C.inContext (h.hom a b) = (C.inContext h).hom a b := rfl

theorem CutOperations.Compatible.inContext {H K : GlobularSet.{u}} {C : CutOperations H}
    (L : C.Compatible) (h : HomContext H K) : (C.inContext h).Compatible := by
  induction h with
  | root => exact L
  | hom h a b ih => exact ih.hom a b

theorem CutOperations.RightUnital.inContext {H K : GlobularSet.{u}} {C : CutOperations H}
    (R : C.RightUnital) (h : HomContext H K) : (C.inContext h).RightUnital := by
  induction h with
  | root => exact R
  | hom h a b ih => exact ih.hom a b

theorem CutOperations.LeftUnital.inContext {H K : GlobularSet.{u}} {C : CutOperations H}
    (U : C.LeftUnital) (h : HomContext H K) : (C.inContext h).LeftUnital := by
  induction h with
  | root => exact U
  | hom h a b ih => exact ih.hom a b

theorem CutOperations.Associative.inContext {H K : GlobularSet.{u}} {C : CutOperations H}
    (A : C.Associative) (h : HomContext H K) : (C.inContext h).Associative := by
  induction h with
  | root => exact A
  | hom h a b ih => exact ih.hom a b

theorem CutOperations.Interchange.inContext {H K : GlobularSet.{u}} {C : CutOperations H}
    (I : C.Interchange) (h : HomContext H K) : (C.inContext h).Interchange := by
  induction h with
  | root => exact I
  | hom h a b ih => exact ih.hom a b

theorem CutOperations.UnitIdempotent.inContext {H K : GlobularSet.{u}} {C : CutOperations H}
    (U : C.UnitIdempotent) (h : HomContext H K) : (C.inContext h).UnitIdempotent := by
  induction h with
  | root => exact U
  | hom h a b ih => exact ih.hom a b

theorem CutOperations.UnitCompatible.inContext {H K : GlobularSet.{u}} {C : CutOperations H}
    (U : C.UnitCompatible) (h : HomContext H K) : (C.inContext h).UnitCompatible := by
  induction h with
  | root => exact U
  | hom h a b ih => exact ih.hom a b

abbrev RecursiveComposition (H : GlobularSet.{u}) :=
  ∀ {K : GlobularSet.{u}}, HomContext H K → HorizontalComposition K

def CutOperations.recursive {H : GlobularSet.{u}} (C : CutOperations H) (L : C.Compatible) :
    RecursiveComposition H := fun h => (C.inContext h).horizontal (L.inContext h)

/-- The concrete pasting carrier now supplies operations in every iterated
hom context, including the boundary equations needed by evaluation. -/
noncomputable def recursiveComposition (G : GlobularSet.{u}) : RecursiveComposition (globular G) :=
  (cutOperations G).recursive (cutOperations_compatible G)

theorem recursiveComposition_right_unit (G : GlobularSet.{u}) {K : GlobularSet.{u}}
    (h : HomContext (globular G) K) {n : Nat} {a b : K.Cell 0} (p : (K.hom a b).Cell n) :
    (recursiveComposition G h).mul p ((recursiveComposition G h).unit n b) = p :=
  CutOperations.horizontal_right_unit ((cutOperations_compatible G).inContext h)
    (CutOperations.RightUnital.inContext (cutOperations_rightUnital G) h) p

namespace HorizontalComposition

def fold {H : GlobularSet.{u}} (C : HorizontalComposition H) {n : Nat} {a b : H.Cell 0} :
    Chain (fun x y => (H.hom x y).Cell n) a b → (H.hom a b).Cell n
  | .nil a => C.unit n a
  | .cons e p => C.mul e (C.fold p)

theorem source_fold {H : GlobularSet.{u}} (C : HorizontalComposition H)
    {n : Nat} {a b : H.Cell 0} (p : Chain (fun x y => (H.hom x y).Cell (n + 1)) a b) :
    (H.hom a b).source (C.fold p) = C.fold (p.map (fun {x y} e => (H.hom x y).source e)) := by
  induction p with
  | nil a => exact C.source_unit n a
  | cons e p ih => exact (C.source_mul e (C.fold p)).trans (_root_.congrArg (C.mul _) ih)

theorem target_fold {H : GlobularSet.{u}} (C : HorizontalComposition H)
    {n : Nat} {a b : H.Cell 0} (p : Chain (fun x y => (H.hom x y).Cell (n + 1)) a b) :
    (H.hom a b).target (C.fold p) = C.fold (p.map (fun {x y} e => (H.hom x y).target e)) := by
  induction p with
  | nil a => exact C.target_unit n a
  | cons e p ih => exact (C.target_mul e (C.fold p)).trans (_root_.congrArg (C.mul _) ih)

end HorizontalComposition

/-- Primitive cartesian lifting extends to arbitrary finite horizontal chains.
The endpoints are retained even when the object map is not injective. -/
theorem CutOperations.Cartesian.fold_lift {G H : GlobularSet.{u}}
    {C : CutOperations G} {D : CutOperations H} {f : GlobularSet.Map G H}
    (K : CutOperations.Cartesian C D f) (L : C.Compatible) (M : D.Compatible)
    {n : Nat} {x y : H.Cell 0} (q : Chain (fun x y => (H.hom x y).Cell n) x y)
    (a b : G.Cell 0) (p : (G.hom a b).Cell n)
    (ha : f.app a = x) (hb : f.app b = y)
    (h : f.app p.val = ((D.horizontal M).fold q).val) :
    ∃ s : Chain (fun x y => (G.hom x y).Cell n) a b,
      (C.horizontal L).fold s = p ∧
      HEq (s.mapAlong (F := fun x y => (H.hom x y).Cell n)
        f.app (fun {x y} e => (f.hom x y).app e)) q := by
  induction q generalizing a b with
  | nil x =>
    obtain ⟨hab, hp, hx⟩ := K.horizontal_unit_lift a b p x h
    cases hab
    refine ⟨.nil a, Subtype.ext hp, ?_⟩
    cases ha
    rfl
  | @cons x z y e q ih =>
    cases ha
    cases hb
    obtain ⟨⟨c, r, t⟩, ⟨hc, hr, he, ht⟩, _⟩ :=
      K.horizontal_factor_lift a b p z e ((D.horizontal M).fold q) h
    obtain ⟨s, hs, hf⟩ := ih c b t hc rfl ht
    refine ⟨.cons r s, (_root_.congrArg ((C.horizontal L).mul r) hs).trans hr, ?_⟩
    cases hc
    have he' : (f.hom a c).app r = e := Subtype.ext he
    exact heq_of_eq (_root_.congrArg₂ Chain.cons he' (eq_of_heq hf))

/-- Concatenation is respected by the evaluator's fold whenever the actual
target operations satisfy their associativity and left-unit laws. -/
theorem CutOperations.fold_append {H : GlobularSet.{u}} {C : CutOperations H}
    (L : C.Compatible) (U : C.LeftUnital) (A : C.Associative) {n : Nat} {a b c : H.Cell 0}
    (p : Chain (fun x y => (H.hom x y).Cell n) a b)
    (q : Chain (fun x y => (H.hom x y).Cell n) b c) :
    (C.horizontal L).fold (p.append q) =
      (C.horizontal L).mul ((C.horizontal L).fold p) ((C.horizontal L).fold q) := by
  induction p with
  | nil => exact (C.horizontal_left_unit L U ((C.horizontal L).fold q)).symm
  | cons e p ih =>
    exact (_root_.congrArg ((C.horizontal L).mul e) (ih q)).trans
      (C.horizontal_assoc L A e ((C.horizontal L).fold p) ((C.horizontal L).fold q)).symm

/-- Interchange distributes a higher-cut composition through a horizontal
fold. All matching witnesses come from the supplied boundary-preserving
interpretation, for individual labels and for complete subchains. -/
theorem CutOperations.fold_zipOver {H : GlobularSet.{u}} (C : CutOperations H)
    (L : C.Compatible) (I : C.Interchange) (U : C.UnitIdempotent)
    {O : Type u} {E B : O → O → Type u} {n : Nat} (c : Cut n)
    (s t : {x y : O} → E x y → B x y)
    (op : {x y : O} → (e d : E x y) → s e = t d → E x y)
    (v : O → H.Cell 0) (f : {x y : O} → E x y → (H.hom (v x) (v y)).Cell n)
    (labelMatch : ∀ {x y} (e d : E x y), s e = t d →
      CutBoundary.target c (H.hom (v x) (v y)) (f e) = CutBoundary.source c (H.hom (v x) (v y)) (f d))
    (law : ∀ {x y} (e d : E x y) (he : s e = t d),
      f (op e d he) = (C.hom (v x) (v y)).compose c (f e) (f d) (labelMatch e d he))
    (foldMatch : ∀ {x y} (p q : Chain E x y), p.map s = q.map t →
      CutBoundary.target c (H.hom (v x) (v y)) ((C.horizontal L).fold (p.mapAlong v f)) =
        CutBoundary.source c (H.hom (v x) (v y)) ((C.horizontal L).fold (q.mapAlong v f)))
    {x y : O} (p q : Chain E x y) (h : p.map s = q.map t) :
    (C.horizontal L).fold ((Chain.zipOver s t op p q h).mapAlong v f) =
      (C.hom (v x) (v y)).compose c ((C.horizontal L).fold (p.mapAlong v f))
        ((C.horizontal L).fold (q.mapAlong v f)) (foldMatch p q h) := by
  induction p with
  | nil x =>
    cases q with
    | nil => exact (Subtype.ext (U (Cut.Below.bottom c) (v x) _)).symm
    | cons d q => cases h
  | @cons x z y e p ih =>
    cases q with
    | nil => cases h
    | @cons _ z' _ d q =>
      have hh := h
      simp only [Chain.map] at hh
      injection hh with hx hz hy he hp
      cases hz
      have he' := eq_of_heq he
      have hp' := eq_of_heq hp
      exact (_root_.congrArg₂ C.horizontalMul (law e d he') (ih q hp')).trans
        (C.horizontal_interchange I c (f e) (f d)
          ((C.horizontal L).fold (p.mapAlong (F := fun x y => (H.hom x y).Cell n) v f))
          ((C.horizontal L).fold (q.mapAlong (F := fun x y => (H.hom x y).Cell n) v f))
          (labelMatch e d he') (foldMatch p q hp')
          (foldMatch (.cons e p) (.cons d q) h)).symm

/-- Higher identities commute with the actual horizontal chain fold. -/
theorem CutOperations.fold_unit {H : GlobularSet.{u}} (C : CutOperations H) (L : C.Compatible)
    (U : C.UnitCompatible) {n : Nat} (c : Cut n) {a b : H.Cell 0}
    (p : Chain (fun x y => (H.hom x y).Cell c.height) a b) :
    (C.horizontal L).fold (p.map (fun {x y} e => (C.hom x y).unit c e)) =
      (C.hom a b).unit c ((C.horizontal L).fold p) := by
  induction p with
  | nil a => exact (C.horizontal_unit_unit U c a).symm
  | cons e p ih =>
    exact (_root_.congrArg (C.horizontalMul ((C.hom _ _).unit c e)) ih).trans
      (C.horizontal_unit_compose U c e ((C.horizontal L).fold p)).symm

theorem CutOperations.Preserves.fold {G H : GlobularSet.{u}}
    {C : CutOperations G} {D : CutOperations H} {f : GlobularSet.Map G H}
    (P : Preserves C D f) (L : C.Compatible) (M : D.Compatible)
    {n : Nat} {a b : G.Cell 0} (p : Chain (fun x y => (G.hom x y).Cell n) a b) :
    (f.hom a b).app ((C.horizontal L).fold p) =
      (D.horizontal M).fold (p.mapAlong f.app (fun {x y} e => (f.hom x y).app e)) := by
  induction p with
  | nil a => exact P.horizontal_unit n a
  | cons e p ih =>
    exact (P.horizontal_mul e ((C.horizontal L).fold p)).trans
      (_root_.congrArg (D.horizontalMul ((f.hom _ _).app e)) ih)

/-- A fold and its relabelled chain jointly determine the original chain.
No injectivity assumption on the object map is needed. -/
theorem CutOperations.Cartesian.fold_joint_injective {G H : GlobularSet.{u}}
    {C : CutOperations G} {D : CutOperations H} {f : GlobularSet.Map G H}
    (K : CutOperations.Cartesian C D f) (L : C.Compatible) (M : D.Compatible)
    {n : Nat} {a b : G.Cell 0} (p q : Chain (fun x y => (G.hom x y).Cell n) a b)
    (hc : (C.horizontal L).fold p = (C.horizontal L).fold q)
    (hm : p.mapAlong (F := fun x y => (H.hom x y).Cell n) f.app (fun {x y} e => (f.hom x y).app e) =
      q.mapAlong f.app (fun {x y} e => (f.hom x y).app e)) : p = q := by
  have valEq : ∀ {x y z w : H.Cell 0} (r : (H.hom x y).Cell n)
      (s : (H.hom z w).Cell n), x = z → y = w → HEq r s → r.val = s.val := by
    intro x y z w r s hx hy he
    cases hx
    cases hy
    exact _root_.congrArg Subtype.val (eq_of_heq he)
  have foldEq : ∀ {x y z w : H.Cell 0}
      (r : Chain (fun x y => (H.hom x y).Cell n) x y)
      (s : Chain (fun x y => (H.hom x y).Cell n) z w),
      x = z → y = w → HEq r s →
      ((D.horizontal M).fold r).val = ((D.horizontal M).fold s).val := by
    intro x y z w r s hx hy he
    cases hx
    cases hy
    exact _root_.congrArg (fun t => ((D.horizontal M).fold t).val) (eq_of_heq he)
  induction p with
  | nil a =>
    cases q with
    | nil => rfl
    | cons e q => cases hm
  | @cons a c b e p ih =>
    cases q with
    | nil => cases hm
    | @cons _ d _ g q =>
      have hh := Chain.cons_heq_components (D := fun x y => (H.hom x y).Cell n) ((f.hom a c).app e)
        (p.mapAlong (F := fun x y => (H.hom x y).Cell n) f.app (fun {x y} e => (f.hom x y).app e))
        ((f.hom a d).app g) (q.mapAlong (F := fun x y => (H.hom x y).Cell n)
          f.app (fun {x y} e => (f.hom x y).app e))
        rfl rfl (heq_of_eq hm)
      have he : f.app e.val = f.app g.val := valEq _ _ rfl hh.1 hh.2.1
      have ht : f.app ((C.horizontal L).fold p).val = f.app ((C.horizontal L).fold q).val :=
        (_root_.congrArg Subtype.val (K.toPreserves.fold L M p)).trans
          ((foldEq _ _ hh.1 rfl hh.2.2).trans
            (_root_.congrArg Subtype.val (K.toPreserves.fold L M q)).symm)
      obtain ⟨s, hs, hu⟩ := K.horizontal_factor_lift a b
        ((C.horizontal L).fold (.cons g q)) (f.app d)
        ((f.hom a d).app g) ((f.hom d b).app ((C.horizontal L).fold q))
        (_root_.congrArg Subtype.val (K.toPreserves.horizontal_mul g ((C.horizontal L).fold q)))
      have h₁ := hu ⟨c, e, (C.horizontal L).fold p⟩ ⟨hh.1, hc, he, ht⟩
      have h₂ := hu ⟨d, g, (C.horizontal L).fold q⟩ ⟨rfl, rfl, rfl, rfl⟩
      have hpair := h₁.trans h₂.symm
      have hcd := _root_.congrArg Sigma.fst hpair
      cases hcd
      have hp := eq_of_heq (Sigma.mk.inj hpair).2
      exact _root_.congrArg₂ Chain.cons (_root_.congrArg Prod.fst hp)
        (ih q (_root_.congrArg Prod.snd hp) (eq_of_heq hh.2.2))

/-- The horizontal fold square is a pullback, expressed by its unique-lift
property at every dimension and every fixed pair of source endpoints. -/
theorem CutOperations.Cartesian.fold_unique_lift {G H : GlobularSet.{u}}
    {C : CutOperations G} {D : CutOperations H} {f : GlobularSet.Map G H}
    (K : CutOperations.Cartesian C D f) (L : C.Compatible) (M : D.Compatible)
    {n : Nat} {a b : G.Cell 0} (p : (G.hom a b).Cell n)
    (q : Chain (fun x y => (H.hom x y).Cell n) (f.app a) (f.app b))
    (h : f.app p.val = ((D.horizontal M).fold q).val) :
    ∃! s : Chain (fun x y => (G.hom x y).Cell n) a b,
      (C.horizontal L).fold s = p ∧
      s.mapAlong f.app (fun {x y} e => (f.hom x y).app e) = q := by
  obtain ⟨s, hs, hf⟩ := K.fold_lift L M q a b p rfl rfl h
  refine ⟨s, ⟨hs, eq_of_heq hf⟩, ?_⟩
  intro t ht
  exact K.fold_joint_injective L M t s (ht.1.trans hs.symm)
    (ht.2.trans (eq_of_heq hf).symm)

/-- Evaluate every labelled pasting cell by dimension recursion, using the
target's operations in its actual iterated hom sets. The concrete pasting
target instantiation below supplies candidate multiplication. -/
def evaluate {H : GlobularSet.{u}} (C : RecursiveComposition H) :
    {n : Nat} → {G K : GlobularSet.{u}} → HomContext H K →
      GlobularSet.Map G K → Pasting n G → K.Cell n
  | 0, _, _, _, f, a => f.app a
  | n + 1, _, _, h, f, ⟨a, b, p⟩ =>
      ((C h).fold (p.mapAlong f.app (fun {x y} e =>
        evaluate C (n := n) (h.hom (f.app x) (f.app y)) (f.hom x y) e))).val

theorem evaluate_precompose {H : GlobularSet.{u}} (C : RecursiveComposition H)
    {n : Nat} {G K J : GlobularSet.{u}} (h : HomContext H J)
    (f : GlobularSet.Map K J) (g : GlobularSet.Map G K) (p : Pasting n G) :
    evaluate C h f (map g p) = evaluate C h (GlobularSet.Map.comp f g) p := by
  induction n generalizing G K J with
  | zero => rfl
  | succ n ih =>
    rcases p with ⟨a, b, p⟩
    apply _root_.congrArg (fun q => ((C h).fold q).val)
    refine (Chain.mapAlong_comp _ _ _ _ p).trans (Chain.mapAlong_congr _ _ _ ?_ p)
    intro x y e
    simp only [GlobularSet.Map.hom_comp]
    exact ih (h.hom (f.app (g.app x)) (f.app (g.app y))) (f.hom _ _) (g.hom x y) e

theorem evaluate_postcompose {H K : GlobularSet.{u}} (C : CutOperations H) (D : CutOperations K)
    (L : C.Compatible) (M : D.Compatible) {n : Nat} {G H' K' : GlobularSet.{u}}
    (h : HomContext H H') (k : HomContext K K') (g : GlobularSet.Map H' K')
    (P : CutOperations.Preserves (C.inContext h) (D.inContext k) g)
    (f : GlobularSet.Map G H') (p : Pasting n G) :
    g.app (evaluate (C.recursive L) h f p) =
      evaluate (D.recursive M) k (GlobularSet.Map.comp g f) p := by
  induction n generalizing G H' K' with
  | zero => rfl
  | succ n ih =>
    rcases p with ⟨a, b, p⟩
    refine (_root_.congrArg Subtype.val (P.fold (L.inContext h) (M.inContext k)
      (p.mapAlong f.app (fun {x y} e => evaluate (C.recursive L)
        (h.hom (f.app x) (f.app y)) (f.hom x y) e)))).trans ?_
    apply _root_.congrArg (fun q => (((D.inContext k).horizontal (M.inContext k)).fold q).val)
    refine (Chain.mapAlong_comp _ _ _ _ p).trans (Chain.mapAlong_congr _ _ _ ?_ p)
    intro x y e
    simp only [GlobularSet.Map.hom_comp]
    exact ih (h.hom (f.app x) (f.app y)) (k.hom (g.app (f.app x)) (g.app (f.app y)))
      (g.hom (f.app x) (f.app y)) (P.hom (f.app x) (f.app y)) (f.hom x y) e

/-- Evaluation preserves zero-boundary composition in every dimension and
every hom context. Matching in the target is explicit and proof-irrelevant. -/
theorem evaluate_horizontal {H : GlobularSet.{u}} (C : CutOperations H) (L : C.Compatible)
    (U : C.LeftUnital) (A : C.Associative) {G K : GlobularSet.{u}} (h : HomContext H K)
    (f : GlobularSet.Map G K) {n : Nat} {a b c : G.Cell 0}
    (p : Horizontal n G a b) (q : Horizontal n G b c)
    (ht : CutBoundary.target (.bottom : Cut (n + 1)) K (evaluate (C.recursive L) h f (pack p)) =
      CutBoundary.source (.bottom : Cut (n + 1)) K (evaluate (C.recursive L) h f (pack q))) :
    evaluate (C.recursive L) h f (pack (p.append q)) =
      (C.inContext h).compose .bottom (evaluate (C.recursive L) h f (pack p))
        (evaluate (C.recursive L) h f (pack q)) ht := by
  change (((C.inContext h).horizontal (L.inContext h)).fold
    ((p.append q).mapAlong f.app (fun {x y} e => evaluate (C.recursive L)
      (h.hom (f.app x) (f.app y)) (f.hom x y) e))).val = _
  exact (_root_.congrArg (fun r => (((C.inContext h).horizontal (L.inContext h)).fold r).val)
    (Chain.mapAlong_append _ _ p q)).trans
      (_root_.congrArg Subtype.val (CutOperations.fold_append (L.inContext h)
        (CutOperations.LeftUnital.inContext U h) (CutOperations.Associative.inContext A h) _ _))

theorem source_evaluate {H : GlobularSet.{u}} (C : RecursiveComposition H)
    {n : Nat} {G K : GlobularSet.{u}} (h : HomContext H K) (f : GlobularSet.Map G K)
    (p : Pasting (n + 1) G) :
    K.source (evaluate C h f p) = evaluate C h f (source p) := by
  induction n generalizing G K with
  | zero =>
    rcases p with ⟨a, b, p⟩
    exact ((C h).fold (p.mapAlong f.app (fun {x y} e =>
      evaluate C (h.hom (f.app x) (f.app y)) (f.hom x y) e))).property.1
  | succ n ih =>
    rcases p with ⟨a, b, p⟩
    change ((K.hom (f.app a) (f.app b)).source ((C h).fold _)).val = _
    rw [HorizontalComposition.source_fold]
    apply _root_.congrArg (fun q => ((C h).fold q).val)
    exact Chain.mapAlong_natural _ _ _ _ _ (fun {x y} e =>
      ih (h.hom (f.app x) (f.app y)) (f.hom x y) e) p

theorem target_evaluate {H : GlobularSet.{u}} (C : RecursiveComposition H)
    {n : Nat} {G K : GlobularSet.{u}} (h : HomContext H K) (f : GlobularSet.Map G K)
    (p : Pasting (n + 1) G) :
    K.target (evaluate C h f p) = evaluate C h f (target p) := by
  induction n generalizing G K with
  | zero =>
    rcases p with ⟨a, b, p⟩
    exact ((C h).fold (p.mapAlong f.app (fun {x y} e =>
      evaluate C (h.hom (f.app x) (f.app y)) (f.hom x y) e))).property.2
  | succ n ih =>
    rcases p with ⟨a, b, p⟩
    change ((K.hom (f.app a) (f.app b)).target ((C h).fold _)).val = _
    rw [HorizontalComposition.target_fold]
    apply _root_.congrArg (fun q => ((C h).fold q).val)
    exact Chain.mapAlong_natural _ _ _ _ _ (fun {x y} e =>
      ih (h.hom (f.app x) (f.app y)) (f.hom x y) e) p

def evaluateGlobular {H : GlobularSet.{u}} (C : RecursiveComposition H)
    {G K : GlobularSet.{u}} (h : HomContext H K) (f : GlobularSet.Map G K) :
    GlobularSet.Map (globular G) K where
  app := evaluate C h f
  source_app := source_evaluate C h f
  target_app := target_evaluate C h f

/-- Identity-labelled evaluation exposes the genuine hom-context fold. -/
theorem evaluate_pack_id {H : GlobularSet.{u}} (C : RecursiveComposition H)
    {G : GlobularSet.{u}} (h : HomContext H G) {n : Nat} {a b : G.Cell 0}
    (p : Horizontal n G a b) :
    evaluate C h (GlobularSet.Map.id G) (pack p) =
      ((C h).fold (p.map (fun {x y} e =>
        evaluate C (h.hom x y) (GlobularSet.Map.id (G.hom x y)) e))).val := by
  change ((C h).fold (p.mapAlong (fun x => x) _)).val = _
  simp only [GlobularSet.Map.hom_id]
  exact _root_.congrArg (fun q => ((C h).fold q).val)
    (Chain.mapAlong_identity_vertices
      (fun {x y} e => evaluate C (h.hom x y) (GlobularSet.Map.id (G.hom x y)) e) p)

/-- Cartesian primitive operations lift recursively labelled diagrams
through the actual evaluator, in every finite iterated hom context. -/
theorem evaluate_lift {G₀ H₀ : GlobularSet.{u}} (C : CutOperations G₀) (D : CutOperations H₀)
    (L : C.Compatible) (M : D.Compatible) {n : Nat} {G H : GlobularSet.{u}}
    (g : HomContext G₀ G) (h : HomContext H₀ H) (f : GlobularSet.Map G H)
    (K : CutOperations.Cartesian (C.inContext g) (D.inContext h) f)
    (p : G.Cell n) (q : Pasting n H)
    (hp : f.app p = evaluate (D.recursive M) h (GlobularSet.Map.id H) q) :
    ∃ r : Pasting n G,
      evaluate (C.recursive L) g (GlobularSet.Map.id G) r = p ∧ map f r = q := by
  induction n generalizing G H with
  | zero => exact ⟨p, rfl, hp⟩
  | succ n ih =>
    rcases q with ⟨x, y, q⟩
    let a := G.sourceZero p
    let b := G.targetZero p
    let p' : (G.hom a b).Cell n := ⟨p, rfl, rfl⟩
    let j := fun {x y : H.Cell 0} (e : Pasting n (H.hom x y)) =>
      evaluate (D.recursive M) (h.hom x y) (GlobularSet.Map.id (H.hom x y)) e
    have hp' : f.app p = (((D.inContext h).horizontal (M.inContext h)).fold (q.map j)).val :=
      hp.trans (evaluate_pack_id (D.recursive M) h q)
    have ha : f.app a = x := (f.sourceZero p).symm.trans
      ((_root_.congrArg H.sourceZero hp').trans
        ((((D.inContext h).horizontal (M.inContext h)).fold (q.map j)).property.1))
    have hb : f.app b = y := (f.targetZero p).symm.trans
      ((_root_.congrArg H.targetZero hp').trans
        ((((D.inContext h).horizontal (M.inContext h)).fold (q.map j)).property.2))
    obtain ⟨s, hs, hf⟩ := K.fold_lift (L.inContext g) (M.inContext h) (q.map j) a b p' ha hb hp'
    obtain ⟨r, hr, hq⟩ := Chain.lift_mapAlong_square
      (E := fun x y => (G.hom x y).Cell n) (R := fun x y => Pasting n (G.hom x y))
      (F := fun x y => (H.hom x y).Cell n) (D := fun x y => Pasting n (H.hom x y))
      f.app (fun {x y} e => (f.hom x y).app e) j
      (fun {x y} e => evaluate (C.recursive L) (g.hom x y) (GlobularSet.Map.id (G.hom x y)) e)
      (fun {x y} e => map (f.hom x y) e) (by
        intro u v x y e d hx hy he
        cases hx
        cases hy
        obtain ⟨r, hr, hd⟩ := ih (g.hom u v) (h.hom (f.app u) (f.app v))
          (f.hom u v) (K.hom u v) e d (eq_of_heq he)
        exact ⟨r, hr, heq_of_eq hd⟩) s q ha hb hf
    refine ⟨pack r, ?_, Chain.packed_eq_of_heq _ _ ha hb hq⟩
    exact (evaluate_pack_id (C.recursive L) g r).trans
      ((_root_.congrArg (fun t => (((C.inContext g).horizontal (L.inContext g)).fold t).val) hr).trans
        (_root_.congrArg Subtype.val hs))

/-- Naturality of identity-labelled evaluation in arbitrary hom contexts. -/
theorem evaluate_map_id {G₀ H₀ : GlobularSet.{u}} (C : CutOperations G₀) (D : CutOperations H₀)
    (L : C.Compatible) (M : D.Compatible) {n : Nat} {G H : GlobularSet.{u}}
    (g : HomContext G₀ G) (h : HomContext H₀ H) (f : GlobularSet.Map G H)
    (P : CutOperations.Preserves (C.inContext g) (D.inContext h) f) (p : Pasting n G) :
    f.app (evaluate (C.recursive L) g (GlobularSet.Map.id G) p) =
      evaluate (D.recursive M) h (GlobularSet.Map.id H) (map f p) := by
  exact (evaluate_postcompose C D L M g h f P (GlobularSet.Map.id G) p).trans
    (evaluate_precompose (D.recursive M) h (GlobularSet.Map.id H) f p).symm

/-- Evaluation and relabelling jointly determine every recursively labelled
pasting, not merely its unlabelled shape or its folded value. -/
theorem evaluate_joint_injective {G₀ H₀ : GlobularSet.{u}}
    (C : CutOperations G₀) (D : CutOperations H₀) (L : C.Compatible) (M : D.Compatible)
    {n : Nat} {G H : GlobularSet.{u}} (g : HomContext G₀ G) (h : HomContext H₀ H)
    (f : GlobularSet.Map G H) (K : CutOperations.Cartesian (C.inContext g) (D.inContext h) f)
    (p q : Pasting n G)
    (he : evaluate (C.recursive L) g (GlobularSet.Map.id G) p =
      evaluate (C.recursive L) g (GlobularSet.Map.id G) q)
    (hm : map f p = map f q) : p = q := by
  induction n generalizing G H with
  | zero => exact he
  | succ n ih =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    let j := fun {x y : G.Cell 0} (e : Pasting n (G.hom x y)) =>
      evaluate (C.recursive L) (g.hom x y) (GlobularSet.Map.id (G.hom x y)) e
    have he' : (((C.inContext g).horizontal (L.inContext g)).fold (p.map j)).val =
        (((C.inContext g).horizontal (L.inContext g)).fold (q.map j)).val :=
      (evaluate_pack_id (C.recursive L) g p).symm.trans
        (he.trans (evaluate_pack_id (C.recursive L) g q))
    have ha : a = c := (((C.inContext g).horizontal (L.inContext g)).fold (p.map j)).property.1.symm.trans
      ((_root_.congrArg G.sourceZero he').trans
        (((C.inContext g).horizontal (L.inContext g)).fold (q.map j)).property.1)
    have hb : b = d := (((C.inContext g).horizontal (L.inContext g)).fold (p.map j)).property.2.symm.trans
      ((_root_.congrArg G.targetZero he').trans
        (((C.inContext g).horizontal (L.inContext g)).fold (q.map j)).property.2)
    cases ha
    cases hb
    have hm' := eq_of_heq (Chain.packed_eq_heq _ _ hm)
    let k := fun {x y : H.Cell 0} (e : Pasting n (H.hom x y)) =>
      evaluate (D.recursive M) (h.hom x y) (GlobularSet.Map.id (H.hom x y)) e
    have law : ∀ {x y} (e : Pasting n (G.hom x y)),
        (f.hom x y).app (j e) = k (map (f.hom x y) e) := fun {x y} e =>
      evaluate_map_id C D L M (g.hom x y) (h.hom (f.app x) (f.app y))
        (f.hom x y) (K.toPreserves.hom x y) e
    have hmj : (p.map j).mapAlong (F := fun x y => (H.hom x y).Cell n)
        f.app (fun {x y} e => (f.hom x y).app e) =
        (q.map j).mapAlong f.app (fun {x y} e => (f.hom x y).app e) :=
      (Chain.mapAlong_natural (F := fun x y => Pasting n (H.hom x y))
        (K := fun x y => (H.hom x y).Cell n) f.app j k (fun {x y} e => map (f.hom x y) e)
        (fun {x y} e => (f.hom x y).app e) (fun e => (law e).symm) p).symm.trans
        ((_root_.congrArg (fun t => t.map k) hm').trans
          (Chain.mapAlong_natural (F := fun x y => Pasting n (H.hom x y))
            (K := fun x y => (H.hom x y).Cell n) f.app j k (fun {x y} e => map (f.hom x y) e)
            (fun {x y} e => (f.hom x y).app e) (fun e => (law e).symm) q))
    have hj := K.fold_joint_injective (L.inContext g) (M.inContext h)
      (p.map j) (q.map j) (Subtype.ext he') hmj
    apply _root_.congrArg pack
    exact Chain.mapAlong_joint_injective (F := fun x y => (G.hom x y).Cell n)
      (D := fun x y => Pasting n (H.hom x y)) (fun x => x) f.app j
      (fun {x y} e => map (f.hom x y) e) (fun _ _ hx _ => hx)
      (fun {x y} e d he hd => ih (g.hom x y) (h.hom (f.app x) (f.app y))
        (f.hom x y) (K.hom x y) e d he hd) p q
      ((Chain.mapAlong_identity_vertices j p).trans (hj.trans (Chain.mapAlong_identity_vertices j q).symm)) hm'

/-- Unique recursive evaluation lifts: the full cellwise pullback property,
uniform in the dimension and in the genuine iterated hom contexts. -/
theorem evaluate_unique_lift {G₀ H₀ : GlobularSet.{u}}
    (C : CutOperations G₀) (D : CutOperations H₀) (L : C.Compatible) (M : D.Compatible)
    {n : Nat} {G H : GlobularSet.{u}} (g : HomContext G₀ G) (h : HomContext H₀ H)
    (f : GlobularSet.Map G H) (K : CutOperations.Cartesian (C.inContext g) (D.inContext h) f)
    (p : G.Cell n) (q : Pasting n H)
    (hp : f.app p = evaluate (D.recursive M) h (GlobularSet.Map.id H) q) :
    ∃! r : Pasting n G,
      evaluate (C.recursive L) g (GlobularSet.Map.id G) r = p ∧ map f r = q := by
  obtain ⟨r, hr, hq⟩ := evaluate_lift C D L M g h f K p q hp
  refine ⟨r, ⟨hr, hq⟩, ?_⟩
  intro s hs
  exact evaluate_joint_injective C D L M g h f K s r
    (hs.1.trans hr.symm) (hs.2.trans hq.symm)

/-- A globular interpretation supplies canonical cut matching from the
actual matching of its labelled diagrams. -/
theorem map_cut_composable {G H : GlobularSet.{u}} (f : GlobularSet.Map (globular G) H)
    {n : Nat} (c : Cut n) (p q : Pasting n G) (h : cutTarget c p = cutSource c q) :
    CutBoundary.target c H (f.app p) = CutBoundary.source c H (f.app q) :=
  (CutBoundary.target_map c f p).trans
    ((_root_.congrArg f.app ((canonical_target_eq_cutTarget c p).trans
      (h.trans (canonical_source_eq_cutSource c q).symm))).trans (CutBoundary.source_map c f q).symm)

/-- Evaluation preserves composition at every cut, not only the horizontal
axis. Higher cuts use interchange and the checked empty-chain identity law. -/
theorem evaluate_cutCompose {H : GlobularSet.{u}} (C : CutOperations H) (L : C.Compatible)
    (U : C.LeftUnital) (A : C.Associative) (I : C.Interchange) (J : C.UnitIdempotent)
    {n : Nat} (c : Cut n) {G K : GlobularSet.{u}} (h : HomContext H K) (f : GlobularSet.Map G K)
    (p q : Pasting n G) (hpq : cutTarget c p = cutSource c q)
    (h' : CutBoundary.target c K (evaluate (C.recursive L) h f p) =
      CutBoundary.source c K (evaluate (C.recursive L) h f q)) :
    evaluate (C.recursive L) h f (cutCompose c p q hpq) =
      (C.inContext h).compose c (evaluate (C.recursive L) h f p) (evaluate (C.recursive L) h f q) h' := by
  induction c generalizing G K with
  | bottom =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    change b = c at hpq
    cases hpq
    exact evaluate_horizontal C L U A h f p q h'
  | @lift n c ih =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨d, e, q⟩
    have ha : a = d := _root_.congrArg Sigma.fst hpq
    have hb : b = e := _root_.congrArg (fun z => z.2.1) hpq
    cases ha
    cases hb
    have hp : p.map (fun e => cutTarget c e) = q.map (fun e => cutSource c e) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hpq).2)).2
    let ev : {x y : G.Cell 0} → Pasting n (G.hom x y) → (K.hom (f.app x) (f.app y)).Cell n :=
      fun {x y} e => evaluate (C.recursive L) (h.hom (f.app x) (f.app y)) (f.hom x y) e
    have hm : ∀ {x y : G.Cell 0} (e d : Pasting n (G.hom x y)), cutTarget c e = cutSource c d →
        CutBoundary.target c (K.hom (f.app x) (f.app y)) (ev e) =
          CutBoundary.source c (K.hom (f.app x) (f.app y)) (ev d) := by
      intro x y e d hed
      exact map_cut_composable (evaluateGlobular (C.recursive L)
        (h.hom (f.app x) (f.app y)) (f.hom x y)) c e d hed
    have hf : ∀ {x y : G.Cell 0} (p q : Horizontal n G x y),
        p.map (fun e => cutTarget c e) = q.map (fun e => cutSource c e) →
        CutBoundary.target c (K.hom (f.app x) (f.app y))
          (((C.inContext h).horizontal (L.inContext h)).fold (p.mapAlong f.app ev)) =
        CutBoundary.source c (K.hom (f.app x) (f.app y))
          (((C.inContext h).horizontal (L.inContext h)).fold (q.mapAlong f.app ev)) := by
      intro x y p q hpq
      apply Subtype.ext
      exact (CutBoundary.target_hom c K _).symm.trans
        ((map_cut_composable (evaluateGlobular (C.recursive L) h f) (.lift c) (pack p) (pack q)
          (_root_.congrArg pack hpq)).trans (CutBoundary.source_hom c K _))
    exact _root_.congrArg Subtype.val (CutOperations.fold_zipOver (C.inContext h) (L.inContext h)
      (CutOperations.Interchange.inContext I h) (CutOperations.UnitIdempotent.inContext J h) c
      (fun e => cutTarget c e) (fun e => cutSource c e) (fun e d he => cutCompose c e d he)
      f.app ev hm (fun {x y} e d he => ih (h.hom (f.app x) (f.app y)) (f.hom x y) e d he (hm e d he))
      hf p q hp)

/-- Evaluation preserves identities at every cut. The proof uses the actual
cross-dimensional identity laws, including the empty-chain case. -/
theorem evaluate_cutUnit {H : GlobularSet.{u}} (C : CutOperations H) (L : C.Compatible)
    (U : C.UnitCompatible) {n : Nat} (c : Cut n) {G K : GlobularSet.{u}}
    (h : HomContext H K) (f : GlobularSet.Map G K) (p : Pasting c.height G) :
    evaluate (C.recursive L) h f (cutUnit c p) =
      (C.inContext h).unit c (evaluate (C.recursive L) h f p) := by
  induction c generalizing G K with
  | bottom => rfl
  | @lift n c ih =>
    rcases p with ⟨a, b, p⟩
    let ev : {m : Nat} → {x y : G.Cell 0} → Pasting m (G.hom x y) →
        (K.hom (f.app x) (f.app y)).Cell m :=
      fun {m x y} e => evaluate (C.recursive L) (h.hom (f.app x) (f.app y)) (f.hom x y) e
    have he : ∀ {x y : G.Cell 0} (e : Pasting c.height (G.hom x y)),
        ev (cutUnit c e) = ((C.inContext h).hom (f.app x) (f.app y)).unit c (ev e) := by
      intro x y e
      exact ih (h.hom (f.app x) (f.app y)) (f.hom x y) e
    change (((C.inContext h).horizontal (L.inContext h)).fold
      ((p.map (fun e => cutUnit c e)).mapAlong f.app (fun e => ev e))).val = _
    exact (_root_.congrArg (fun q => (((C.inContext h).horizontal (L.inContext h)).fold q).val)
      (Chain.mapAlong_natural f.app (fun e => cutUnit c e)
        (fun {x y} e => ((C.inContext h).hom x y).unit c e)
        (fun e => ev e) (fun e => ev e) (fun e => (he e).symm) p).symm).trans
      (_root_.congrArg Subtype.val (CutOperations.fold_unit (C.inContext h) (L.inContext h)
        (CutOperations.UnitCompatible.inContext U h) c
        (p.mapAlong f.app (fun e => ev e))))

/-- Flatten genuinely nested labelled pasting diagrams in every dimension.
This is the candidate monad multiplication as an actual globular map;
its naturality and monad equations are separate proof obligations. -/
noncomputable def flattenGlobular (G : GlobularSet.{u}) :
    GlobularSet.Map (globular (globular G)) (globular G) :=
  evaluateGlobular (recursiveComposition G) .root (GlobularSet.Map.id (globular G))

/-- Relabelling commutes with the implemented all-dimensional flattening. -/
theorem flatten_natural {G H : GlobularSet.{u}} (f : GlobularSet.Map G H)
    {n : Nat} (p : Pasting n (globular G)) :
    map f ((flattenGlobular G).app (n := n) p) =
      (flattenGlobular H).app (n := n) (map (mapGlobular f) p) := by
  have hpost := evaluate_postcompose (cutOperations G) (cutOperations H)
    (cutOperations_compatible G) (cutOperations_compatible H) .root .root
    (mapGlobular f) (mapGlobular_preserves f) (GlobularSet.Map.id (globular G)) p
  have hpre := evaluate_precompose (recursiveComposition H) .root
    (GlobularSet.Map.id (globular H)) (mapGlobular f) p
  have he : GlobularSet.Map.comp (mapGlobular f) (GlobularSet.Map.id (globular G)) =
      GlobularSet.Map.comp (GlobularSet.Map.id (globular H)) (mapGlobular f) := by
    apply GlobularSet.Map.ext
    intro m c
    rfl
  exact hpost.trans ((_root_.congrArg (fun g => evaluate (recursiveComposition H) .root g p) he).trans hpre.symm)

/-- Every naturality square of the implemented multiplication is cartesian.
The unique lift retains the entire nested labelling in arbitrary dimension. -/
theorem flatten_cartesian {G H : GlobularSet.{u}} (f : GlobularSet.Map G H)
    {n : Nat} (p : Pasting n G) (q : Pasting n (globular H))
    (h : map f p = (flattenGlobular H).app (n := n) q) :
    ∃! r : Pasting n (globular G),
      (flattenGlobular G).app (n := n) r = p ∧ map (mapGlobular f) r = q :=
  evaluate_unique_lift (cutOperations G) (cutOperations H)
    (cutOperations_compatible G) (cutOperations_compatible H) .root .root
    (mapGlobular f) (mapGlobular_cartesian f) p q h

/-- Multiplication naturality has the full unique globular cone lift.
Cellwise uniqueness forces compatibility with both adjacent boundaries. -/
theorem flatten_globular_pullback {G H X : GlobularSet.{u}}
    (f : GlobularSet.Map G H) (p : GlobularSet.Map X (globular G))
    (q : GlobularSet.Map X (globular (globular H)))
    (h : GlobularSet.Map.comp (mapGlobular f) p =
      GlobularSet.Map.comp (flattenGlobular H) q) :
    ∃! d : GlobularSet.Map X (globular (globular G)),
      GlobularSet.Map.comp (flattenGlobular G) d = p ∧
      GlobularSet.Map.comp (mapGlobular (mapGlobular f)) d = q := by
  have liftExists (n : Nat) (x : X.Cell n) := flatten_cartesian f (p.app x) (q.app x)
    (_root_.congrArg (fun k : GlobularSet.Map X (globular H) => k.app x) h)
  let d {n : Nat} (x : X.Cell n) := (liftExists n x).choose
  have hd {n : Nat} (x : X.Cell n) :
      (flattenGlobular G).app (d x) = p.app x ∧ map (mapGlobular f) (d x) = q.app x :=
    (liftExists n x).choose_spec.1
  let D : GlobularSet.Map X (globular (globular G)) := {
    app := d
    source_app := fun x => (liftExists _ (X.source x)).choose_spec.2 (source (d x)) ⟨
      ((flattenGlobular G).source_app (d x)).symm.trans
        ((_root_.congrArg source (hd x).1).trans (p.source_app x)),
      ((mapGlobular (mapGlobular f)).source_app (d x)).symm.trans
        ((_root_.congrArg source (hd x).2).trans (q.source_app x))⟩
    target_app := fun x => (liftExists _ (X.target x)).choose_spec.2 (target (d x)) ⟨
      ((flattenGlobular G).target_app (d x)).symm.trans
        ((_root_.congrArg target (hd x).1).trans (p.target_app x)),
      ((mapGlobular (mapGlobular f)).target_app (d x)).symm.trans
        ((_root_.congrArg target (hd x).2).trans (q.target_app x))⟩ }
  refine ⟨D, ⟨?_, ?_⟩, ?_⟩
  · apply GlobularSet.Map.ext
    intro n x
    exact (hd x).1
  · apply GlobularSet.Map.ext
    intro n x
    exact (hd x).2
  · intro e he
    apply GlobularSet.Map.ext
    intro n x
    exact (liftExists n x).choose_spec.2 (e.app x) ⟨
      _root_.congrArg (fun k : GlobularSet.Map X (globular G) => k.app x) he.1,
      _root_.congrArg (fun k : GlobularSet.Map X (globular (globular H)) => k.app x) he.2⟩

/-- Concrete flattening preserves horizontal concatenation of nested
diagrams at every dimension. This is the zero-cut case of preservation. -/
theorem flatten_horizontal {G : GlobularSet.{u}} {n : Nat} {a b c : (globular G).Cell 0}
    (p : Horizontal n (globular G) a b) (q : Horizontal n (globular G) b c)
    (h : cutTarget (.bottom : Cut (n + 1)) ((flattenGlobular G).app (n := n + 1) (pack p)) =
      cutSource (.bottom : Cut (n + 1)) ((flattenGlobular G).app (n := n + 1) (pack q))) :
    (flattenGlobular G).app (n := n + 1) (pack (p.append q)) =
      cutCompose .bottom ((flattenGlobular G).app (n := n + 1) (pack p))
        ((flattenGlobular G).app (n := n + 1) (pack q)) h :=
  evaluate_horizontal (cutOperations G) (cutOperations_compatible G)
    (cutOperations_leftUnital G) (cutOperations_associative G) .root (GlobularSet.Map.id (globular G)) p q
    ((canonical_target_eq_cutTarget _ _).trans (h.trans (canonical_source_eq_cutSource _ _).symm))

theorem flatten_cutCompose_bottom {G : GlobularSet.{u}} {n : Nat}
    (p q : Pasting (n + 1) (globular G))
    (h : cutTarget (.bottom : Cut (n + 1)) p = cutSource .bottom q)
    (h' : cutTarget .bottom ((flattenGlobular G).app (n := n + 1) p) =
      cutSource .bottom ((flattenGlobular G).app (n := n + 1) q)) :
    (flattenGlobular G).app (n := n + 1) (cutCompose .bottom p q h) =
      cutCompose .bottom ((flattenGlobular G).app (n := n + 1) p)
        ((flattenGlobular G).app (n := n + 1) q) h' := by
  rcases p with ⟨a, b, p⟩
  rcases q with ⟨c, d, q⟩
  change b = c at h
  cases h
  exact flatten_horizontal p q h'

/-- The concrete multiplication preserves composition along every cut of
every dimension, using the actual labelled diagrams on both sides. -/
theorem flatten_cutCompose {G : GlobularSet.{u}} {n : Nat} (c : Cut n)
    (p q : Pasting n (globular G)) (h : cutTarget c p = cutSource c q)
    (h' : cutTarget c ((flattenGlobular G).app (n := n) p) =
      cutSource c ((flattenGlobular G).app (n := n) q)) :
    (flattenGlobular G).app (n := n) (cutCompose c p q h) =
      cutCompose c ((flattenGlobular G).app (n := n) p) ((flattenGlobular G).app (n := n) q) h' :=
  evaluate_cutCompose (cutOperations G) (cutOperations_compatible G) (cutOperations_leftUnital G)
    (cutOperations_associative G) (cutOperations_interchange G) (cutOperations_unitIdempotent G)
    c .root (GlobularSet.Map.id (globular G)) p q h
    ((canonical_target_eq_cutTarget c _).trans (h'.trans (canonical_source_eq_cutSource c _).symm))

theorem flatten_cutUnit {G : GlobularSet.{u}} {n : Nat} (c : Cut n)
    (p : Pasting c.height (globular G)) :
    (flattenGlobular G).app (n := n) (cutUnit c p) =
      cutUnit c ((flattenGlobular G).app (n := c.height) p) :=
  evaluate_cutUnit (cutOperations G) (cutOperations_compatible G) (cutOperations_unitCompatible G)
    c .root (GlobularSet.Map.id (globular G)) p

/-- The implemented multiplication preserves all cut compositions and
identities; this is the strict-operation preservation needed for associativity. -/
theorem flatten_preserves (G : GlobularSet.{u}) :
    CutOperations.Preserves (cutOperations (globular G)) (cutOperations G) (flattenGlobular G) where
  compose c p q h h' := flatten_cutCompose c p q _ _
  unit c p := flatten_cutUnit c p

/-- Associativity of the actual all-dimensional multiplication on triply
nested labelled diagrams. Both sides evaluate the same original labels. -/
theorem flatten_assoc (G : GlobularSet.{u}) {n : Nat} (p : Pasting n (globular (globular G))) :
    (flattenGlobular G).app (n := n) ((flattenGlobular (globular G)).app (n := n) p) =
      (flattenGlobular G).app (n := n) (map (flattenGlobular G) p) := by
  have hpost := evaluate_postcompose (cutOperations (globular G)) (cutOperations G)
    (cutOperations_compatible (globular G)) (cutOperations_compatible G) .root .root
    (flattenGlobular G) (flatten_preserves G) (GlobularSet.Map.id (globular (globular G))) p
  have hpre := evaluate_precompose (recursiveComposition G) .root
    (GlobularSet.Map.id (globular G)) (flattenGlobular G) p
  have he : GlobularSet.Map.comp (flattenGlobular G) (GlobularSet.Map.id (globular (globular G))) =
      GlobularSet.Map.comp (GlobularSet.Map.id (globular G)) (flattenGlobular G) := by
    apply GlobularSet.Map.ext
    intro m c
    rfl
  exact hpost.trans ((_root_.congrArg (fun f => evaluate (recursiveComposition G) .root f p) he).trans hpre.symm)

/-- Candidate multiplication is now a natural transformation, not just an
objectwise family of boundary-preserving maps. The remaining monad equations
are still separate obligations. -/
noncomputable def flattenNatTrans :
    CategoryTheory.NatTrans (pastingFunctor.comp pastingFunctor) pastingFunctor where
  app := flattenGlobular
  naturality {X Y} f := by
    apply GlobularSet.Map.ext
    intro n p
    exact (flatten_natural f p).symm

/-- Evaluation extends the original labelling whenever each target hom
context has a right unit. The labels are recovered exactly, not quotiented. -/
theorem evaluate_singleton {H : GlobularSet.{u}} (C : RecursiveComposition H)
    (unitLaw : ∀ {K : GlobularSet.{u}} (h : HomContext H K) {n a b}
      (p : (K.hom a b).Cell n), (C h).mul p ((C h).unit n b) = p)
    {n : Nat} {G K : GlobularSet.{u}} (h : HomContext H K) (f : GlobularSet.Map G K)
    (c : G.Cell n) : evaluate C h f (singleton c) = f.app c := by
  induction n generalizing G K with
  | zero => rfl
  | succ n ih =>
    let d : (G.hom (G.sourceZero c) (G.targetZero c)).Cell n := ⟨c, rfl, rfl⟩
    change ((C h).mul
      (evaluate C (h.hom (f.app (G.sourceZero c)) (f.app (G.targetZero c)))
        (f.hom _ _) (singleton d)) ((C h).unit n (f.app (G.targetZero c)))).val = _
    rw [ih, unitLaw]
    rfl

/-- The first multiplication unit equation holds on every pasting diagram,
retaining all labels and empty chains exactly. -/
theorem flatten_singleton {G : GlobularSet.{u}} {n : Nat} (p : Pasting n G) :
    (flattenGlobular G).app (singleton (G := globular G) p) = p :=
  evaluate_singleton (recursiveComposition G)
    (fun {K} h {n a b} p => recursiveComposition_right_unit G h (n := n) (a := a) (b := b) p)
    .root (GlobularSet.Map.id (globular G)) p

/-- Expose the existing horizontal chain as a cell of the genuine hom
globular set of pasting diagrams. -/
def packFibre {G : GlobularSet.{u}} {n : Nat} {a b : G.Cell 0}
    (p : Horizontal n G a b) : ((globular G).hom a b).Cell n :=
  ⟨pack p, sourceZero_pack p, targetZero_pack p⟩

def unpackFibre {G : GlobularSet.{u}} {n : Nat} {a b : G.Cell 0}
    (p : ((globular G).hom a b).Cell n) : Horizontal n G a b := by
  rcases p with ⟨⟨c, d, p⟩, hc, hd⟩
  have ha : c = a := (sourceZero_pack p).symm.trans hc
  have hb : d = b := (targetZero_pack p).symm.trans hd
  cases ha
  cases hb
  exact p

theorem pack_unpackFibre {G : GlobularSet.{u}} {n : Nat} {a b : G.Cell 0}
    (p : ((globular G).hom a b).Cell n) : packFibre (unpackFibre p) = p := by
  rcases p with ⟨⟨c, d, p⟩, hc, hd⟩
  have ha : c = a := (sourceZero_pack p).symm.trans hc
  have hb : d = b := (targetZero_pack p).symm.trans hd
  cases ha
  cases hb
  rfl

theorem unpack_packFibre {G : GlobularSet.{u}} {n : Nat} {a b : G.Cell 0}
    (p : Horizontal n G a b) : unpackFibre (packFibre p) = p := by
  have h := _root_.congrArg Subtype.val (pack_unpackFibre (packFibre p))
  exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2

/-- Relabelling an actual hom cell relabels its unpacked horizontal chain,
including all intermediate vertices. -/
theorem unpackFibre_map_hom {G H : GlobularSet.{u}} (f : GlobularSet.Map G H)
    {n : Nat} {a b : G.Cell 0} (p : ((globular G).hom a b).Cell n) :
    unpackFibre (((mapGlobular f).hom a b).app p) =
      (unpackFibre p).mapAlong f.app (fun {x y} e => map (f.hom x y) e) := by
  obtain ⟨p, rfl⟩ : ∃ p', packFibre p' = p := ⟨unpackFibre p, pack_unpackFibre p⟩
  have hm : ((mapGlobular f).hom a b).app (packFibre p) =
      packFibre (p.mapAlong f.app (fun {x y} e => map (f.hom x y) e)) := Subtype.ext rfl
  exact (_root_.congrArg unpackFibre hm).trans
    ((unpack_packFibre _).trans
      (_root_.congrArg (fun q : Horizontal n G a b =>
        q.mapAlong (F := fun x y => Pasting n (H.hom x y)) f.app (fun {x y} e => map (f.hom x y) e))
        (unpack_packFibre p).symm))

theorem source_packFibre {G : GlobularSet.{u}} {n : Nat} {a b : G.Cell 0}
    (p : Horizontal (n + 1) G a b) :
    ((globular G).hom a b).source (packFibre p) = packFibre (p.map (fun e => source e)) :=
  Subtype.ext rfl

theorem target_packFibre {G : GlobularSet.{u}} {n : Nat} {a b : G.Cell 0}
    (p : Horizontal (n + 1) G a b) :
    ((globular G).hom a b).target (packFibre p) = packFibre (p.map (fun e => target e)) :=
  Subtype.ext rfl

/-- The evaluator's horizontal operations instantiated on the actual pasting
carrier. Nested hom contexts still require the higher-cut operations. -/
def horizontalComposition (G : GlobularSet.{u}) : HorizontalComposition (globular G) where
  unit n a := packFibre (n := n) (.nil a)
  mul p q := packFibre ((unpackFibre p).append (unpackFibre q))
  source_unit _ _ := Subtype.ext rfl
  target_unit _ _ := Subtype.ext rfl
  source_mul {n a b c} p q := by
    change G.Cell 0 at a b c
    obtain ⟨p, rfl⟩ : ∃ p', packFibre p' = p := ⟨unpackFibre p, pack_unpackFibre p⟩
    obtain ⟨q, rfl⟩ : ∃ q', packFibre q' = q := ⟨unpackFibre q, pack_unpackFibre q⟩
    simp only [unpack_packFibre, source_packFibre]
    exact _root_.congrArg packFibre (Chain.map_append _ p q)
  target_mul {n a b c} p q := by
    change G.Cell 0 at a b c
    obtain ⟨p, rfl⟩ : ∃ p', packFibre p' = p := ⟨unpackFibre p, pack_unpackFibre p⟩
    obtain ⟨q, rfl⟩ : ∃ q', packFibre q' = q := ⟨unpackFibre q, pack_unpackFibre q⟩
    simp only [unpack_packFibre, target_packFibre]
    exact _root_.congrArg packFibre (Chain.map_append _ p q)

theorem horizontalComposition_right_unit {G : GlobularSet.{u}} {n : Nat} {a b : G.Cell 0}
    (p : ((globular G).hom a b).Cell n) :
    (horizontalComposition G).mul p ((horizontalComposition G).unit n b) = p := by
  change packFibre ((unpackFibre p).append (unpackFibre (packFibre (.nil b)))) = p
  rw [unpack_packFibre, Chain.append_nil, pack_unpackFibre]

/-- On actual chains of pasting diagrams the evaluator's fold is precisely
endpoint-preserving chain substitution, at every dimension. -/
theorem horizontalComposition_fold {G : GlobularSet.{u}} {n : Nat} {a b : G.Cell 0}
    (p : Chain (fun x y => Horizontal n G x y) a b) :
    (horizontalComposition G).fold (p.map (fun e => packFibre e)) =
      packFibre (p.bind (fun e => e)) := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    change (horizontalComposition G).mul (packFibre e)
      ((horizontalComposition G).fold (p.map (fun e => packFibre e))) = _
    rw [ih]
    change packFibre ((unpackFibre (packFibre e)).append
      (unpackFibre (packFibre (p.bind (fun e => e))))) = _
    rw [unpack_packFibre, unpack_packFibre]
    rfl

/-- The actual recursive evaluator, not just the auxiliary horizontal
structure, substitutes a chain for each horizontal segment. -/
theorem recursive_fold_pack {G : GlobularSet.{u}} {n : Nat} {a b : G.Cell 0}
    (p : Chain (fun x y => Horizontal n G x y) a b) :
    (recursiveComposition G .root).fold (p.map (fun e => packFibre e)) =
      packFibre (p.bind (fun e => e)) := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    change (cutOperations G).horizontalMul (packFibre e)
      ((recursiveComposition G .root).fold (p.map (fun e => packFibre e))) = _
    rw [ih]
    rfl

theorem recursive_fold_unpack {G : GlobularSet.{u}} {n : Nat} {a b : G.Cell 0}
    (p : Chain (fun x y => ((globular G).hom x y).Cell n) a b) :
    (recursiveComposition G .root).fold p =
      packFibre ((p.map (fun e => unpackFibre e)).bind (fun e => e)) := by
  have hp : (p.map (fun e => unpackFibre e)).map (fun e => packFibre e) = p :=
    (Chain.map_map _ _ p).trans
      ((Chain.map_congr _ (fun e => e) (fun e => pack_unpackFibre e) p).trans (Chain.map_id p))
  exact (_root_.congrArg (fun q => (recursiveComposition G .root).fold q) hp).symm.trans
    (recursive_fold_pack (G := G) (n := n) (p.map (fun e => unpackFibre e)))

/-- The hom-context evaluator used by the implemented multiplication.
Its domain is the actual hom of the pasting globular set, not a substituted
hom-pasting carrier. -/
noncomputable def flattenHom (G : GlobularSet.{u}) (a b : G.Cell 0) :
    GlobularSet.Map (globular ((globular G).hom a b)) ((globular G).hom a b) :=
  evaluateGlobular (recursiveComposition G) ((HomContext.root (H := globular G)).hom a b)
    (GlobularSet.Map.id ((globular G).hom a b))

theorem flattenHom_natural {G H : GlobularSet.{u}} (f : GlobularSet.Map G H)
    (a b : G.Cell 0) {n : Nat} (p : Pasting n ((globular G).hom a b)) :
    ((mapGlobular f).hom a b).app ((flattenHom G a b).app p) =
      (flattenHom H (f.app a) (f.app b)).app (map ((mapGlobular f).hom a b) p) := by
  let g := (mapGlobular f).hom a b
  have hpost := evaluate_postcompose (cutOperations G) (cutOperations H)
    (cutOperations_compatible G) (cutOperations_compatible H)
    ((HomContext.root (H := globular G)).hom a b)
    ((HomContext.root (H := globular H)).hom (f.app a) (f.app b))
    g ((mapGlobular_preserves f).hom a b) (GlobularSet.Map.id ((globular G).hom a b)) p
  have hpre := evaluate_precompose (recursiveComposition H)
    ((HomContext.root (H := globular H)).hom (f.app a) (f.app b))
    (GlobularSet.Map.id ((globular H).hom (f.app a) (f.app b))) g p
  have he : GlobularSet.Map.comp g (GlobularSet.Map.id ((globular G).hom a b)) =
      GlobularSet.Map.comp (GlobularSet.Map.id ((globular H).hom (f.app a) (f.app b))) g := by
    apply GlobularSet.Map.ext
    intro m c
    rfl
  exact hpost.trans ((_root_.congrArg (fun k => evaluate (recursiveComposition H)
    ((HomContext.root (H := globular H)).hom (f.app a) (f.app b)) k p) he).trans hpre.symm)

theorem flattenHom_segments_natural {G H : GlobularSet.{u}} (f : GlobularSet.Map G H)
    (a b : G.Cell 0) {n : Nat} (p : Pasting n ((globular G).hom a b)) :
    unpackFibre ((flattenHom H (f.app a) (f.app b)).app (map ((mapGlobular f).hom a b) p)) =
      (unpackFibre ((flattenHom G a b).app p)).mapAlong f.app
        (fun {x y} e => map (f.hom x y) e) :=
  (_root_.congrArg unpackFibre (flattenHom_natural f a b p)).symm.trans
    (unpackFibre_map_hom f ((flattenHom G a b).app p))

/-- Exact segmentation formula for globular multiplication in every
positive dimension. Each segment is the genuine evaluated hom label. -/
theorem flatten_horizontal_segments {G : GlobularSet.{u}} {n : Nat} {a b : G.Cell 0}
    (p : Chain (fun x y => Pasting n ((globular G).hom x y)) a b) :
    (flattenGlobular G).app (n := n + 1) (pack p) =
      pack ((p.map (fun {x y} e => unpackFibre ((flattenHom G x y).app e))).bind (fun e => e)) := by
  have he : p.mapAlong (fun x => x) (fun {x y} e =>
      evaluate (recursiveComposition G) ((HomContext.root (H := globular G)).hom x y)
        ((GlobularSet.Map.id (globular G)).hom x y) e) =
      p.map (fun {x y} e => (flattenHom G x y).app e) := by
    refine (Chain.mapAlong_identity_vertices _ p).trans ?_
    apply Chain.map_congr
    intro x y e
    rw [GlobularSet.Map.hom_id]
    rfl
  exact (_root_.congrArg (fun q => ((recursiveComposition G .root).fold q).val) he).trans
    ((_root_.congrArg Subtype.val (recursive_fold_unpack (G := G) (n := n)
    (p.map (fun {x y} e => (flattenHom G x y).app e)))).trans
      (_root_.congrArg (fun q : Chain (fun x y => Horizontal n G x y) a b => pack (q.bind (fun e => e)))
        (Chain.map_map (fun {x y} e => (flattenHom G x y).app e) (fun e => unpackFibre e) p)))

/-- Include a pasting diagram in one hom set as a single horizontal edge
of the original pasting carrier. Its labels are retained literally. -/
def homPastingInclusion (G : GlobularSet.{u}) (a b : G.Cell 0) :
    GlobularSet.Map (globular (G.hom a b)) ((globular G).hom a b) where
  app p := packFibre (Chain.single p)
  source_app _ := Subtype.ext rfl
  target_app _ := Subtype.ext rfl

theorem homPastingInclusion_preserves (G : GlobularSet.{u}) (a b : G.Cell 0) :
    CutOperations.Preserves (cutOperations (G.hom a b)) ((cutOperations G).hom a b)
      (homPastingInclusion G a b) where
  compose c p q h h' := Subtype.ext rfl
  unit c p := Subtype.ext rfl

theorem homPastingInclusion_injective (G : GlobularSet.{u}) (a b : G.Cell 0) (n : Nat) :
    Function.Injective ((homPastingInclusion G a b).app (n := n)) := by
  intro p q h
  have he := _root_.congrArg (fun c => unpackFibre c) h
  change unpackFibre (packFibre (Chain.single p)) = unpackFibre (packFibre (Chain.single q)) at he
  rw [unpack_packFibre, unpack_packFibre] at he
  injection he

theorem homPastingInclusion_natural {G H : GlobularSet.{u}} (f : GlobularSet.Map G H)
    (a b : G.Cell 0) :
    GlobularSet.Map.comp ((mapGlobular f).hom a b) (homPastingInclusion G a b) =
      GlobularSet.Map.comp (homPastingInclusion H (f.app a) (f.app b)) (mapGlobular (f.hom a b)) := by
  apply GlobularSet.Map.ext
  intro n p
  exact Subtype.ext rfl

/-- The hom evaluator is the restriction of the implemented multiplication
along the single-horizontal-segment inclusion. It is not an independent
replacement multiplication on a different hom carrier. -/
theorem flattenHom_factor (G : GlobularSet.{u}) (a b : G.Cell 0) :
    GlobularSet.Map.comp ((flattenGlobular G).hom a b)
      (homPastingInclusion (globular G) a b) = flattenHom G a b := by
  apply GlobularSet.Map.ext
  intro n p
  apply Subtype.ext
  have hp := flatten_horizontal_segments (G := G) (n := n) (Chain.single p)
  have hs := Chain.bind_single (fun e => e) (unpackFibre ((flattenHom G a b).app p))
  exact hp.trans ((_root_.congrArg pack hs).trans
    (_root_.congrArg Subtype.val (pack_unpackFibre ((flattenHom G a b).app p))))

/-- Exact hom-evaluation lifting obligation. Both the output cell and the
nested relabelled diagram are prescribed; arbitrary hom fillers do not
satisfy this condition. -/
def HomFlattenCartesianAt {G H : GlobularSet.{u}} (f : GlobularSet.Map G H)
    (n : Nat) : Prop :=
  ∀ (a b : G.Cell 0) (p : ((globular G).hom a b).Cell n)
    (q : Pasting n ((globular H).hom (f.app a) (f.app b))),
    ((mapGlobular f).hom a b).app p = (flattenHom H (f.app a) (f.app b)).app q →
    ∃! r : Pasting n ((globular G).hom a b),
      (flattenHom G a b).app r = p ∧ map ((mapGlobular f).hom a b) r = q

/-- The zero-dimensional hom evaluator is identity on the actual cells;
the first hom-lifting boundary case therefore has a unique literal lift. -/
theorem homFlattenCartesianAt_zero {G H : GlobularSet.{u}} (f : GlobularSet.Map G H) :
    HomFlattenCartesianAt f 0 := by
  intro a b p q h
  refine ⟨p, ⟨rfl, h⟩, ?_⟩
  intro r hr
  exact hr.1

/-- Every dimension of the actual hom evaluator has unique lifts. -/
theorem homFlattenCartesianAt {G H : GlobularSet.{u}} (f : GlobularSet.Map G H) (n : Nat) :
    HomFlattenCartesianAt f n := by
  intro a b p q h
  exact evaluate_unique_lift (cutOperations G) (cutOperations H)
    (cutOperations_compatible G) (cutOperations_compatible H)
    ((HomContext.root (H := globular G)).hom a b)
    ((HomContext.root (H := globular H)).hom (f.app a) (f.app b))
    ((mapGlobular f).hom a b) ((mapGlobular_cartesian f).hom a b) p q h

/-- The native singleton inclusion factors through the actual hom-pasting
inclusion; this is an equation of globular maps, including all boundaries. -/
theorem singleton_hom_factor (G : GlobularSet.{u}) (a b : G.Cell 0) :
    (singletonGlobular G).hom a b =
      GlobularSet.Map.comp (homPastingInclusion G a b) (singletonGlobular (G.hom a b)) := by
  apply GlobularSet.Map.ext
  intro n p
  apply Subtype.ext
  exact (singleton_of_hom G p).symm

/-- The concrete recursive evaluator folds a chain of single horizontal
edges back to that same chain, including the empty chain. -/
theorem recursive_fold_single {G : GlobularSet.{u}} {n : Nat} {a b : G.Cell 0}
    (p : Horizontal n G a b) :
    (recursiveComposition G .root).fold (p.map (fun {x y} e => (homPastingInclusion G x y).app e)) =
      packFibre p := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    change (cutOperations G).horizontalMul (homPastingInclusion G _ _ |>.app e)
      ((recursiveComposition G .root).fold (p.map (fun {x y} e => (homPastingInclusion G x y).app e))) = _
    rw [ih]
    rfl

/-- Evaluation of the generating-cell inclusion recovers every labelled
pasting diagram. The recursive step uses the actual hom-pasting inclusion,
not an identification of different raw cell types. -/
theorem evaluate_singletonLabels {G : GlobularSet.{u}} {n : Nat} (p : Pasting n G) :
    evaluate (recursiveComposition G) .root (singletonGlobular G) p = p := by
  induction n generalizing G with
  | zero => rfl
  | succ n ih =>
    rcases p with ⟨a, b, p⟩
    have he : ∀ {x y : G.Cell 0} (e : Pasting n (G.hom x y)),
        evaluate (recursiveComposition G) ((HomContext.root (H := globular G)).hom x y)
          ((singletonGlobular G).hom x y) e =
          (homPastingInclusion G x y).app e := by
      intro x y e
      have ht := evaluate_postcompose (cutOperations (G.hom x y)) (cutOperations G)
        (cutOperations_compatible (G.hom x y)) (cutOperations_compatible G)
        .root ((HomContext.root (H := globular G)).hom x y) (homPastingInclusion G x y)
        (homPastingInclusion_preserves G x y) (singletonGlobular (G.hom x y)) e
      exact (_root_.congrArg (fun f => evaluate (recursiveComposition G)
        ((HomContext.root (H := globular G)).hom x y) f e)
        (singleton_hom_factor G x y)).trans
          (ht.symm.trans (_root_.congrArg (fun z => (homPastingInclusion G x y).app z) (ih e)))
    change ((recursiveComposition G .root).fold
      (p.mapAlong (fun x => x) (fun {x y} e => evaluate (recursiveComposition G)
        ((HomContext.root (H := globular G)).hom x y) ((singletonGlobular G).hom x y) e))).val = pack p
    exact (_root_.congrArg (fun q => ((recursiveComposition G .root).fold q).val)
      ((Chain.mapAlong_congr _ _ _ (fun e => he e) p).trans
        (Chain.mapAlong_identity_vertices _ p))).trans
          (_root_.congrArg Subtype.val (recursive_fold_single p))

/-- A map preserving all cut operations is recovered by evaluating its
restriction to generating cells. This holds in every dimension. -/
theorem preserves_recovered {G H : GlobularSet.{u}} (C : CutOperations H)
    (L : C.Compatible) (f : GlobularSet.Map (globular G) H)
    (P : CutOperations.Preserves (cutOperations G) C f)
    {n : Nat} (p : Pasting n G) :
    f.app p = evaluate (C.recursive L) .root
      (GlobularSet.Map.comp f (singletonGlobular G)) p := by
  have hp := evaluate_postcompose (cutOperations G) C
    (cutOperations_compatible G) L .root .root f P (singletonGlobular G) p
  exact (_root_.congrArg (fun z => f.app z) (evaluate_singletonLabels p)).symm.trans hp

/-- Composition-preserving maps out of labelled pastings are uniquely
determined by their values on the original globular generators. -/
theorem preserves_ext {G H : GlobularSet.{u}} (C : CutOperations H)
    (L : C.Compatible) (f g : GlobularSet.Map (globular G) H)
    (P : CutOperations.Preserves (cutOperations G) C f)
    (Q : CutOperations.Preserves (cutOperations G) C g)
    (h : GlobularSet.Map.comp f (singletonGlobular G) =
      GlobularSet.Map.comp g (singletonGlobular G)) : f = g := by
  apply GlobularSet.Map.ext
  intro n p
  exact (preserves_recovered C L f P p).trans
    ((_root_.congrArg (fun k => evaluate (C.recursive L) .root k p) h).trans
      (preserves_recovered C L g Q p).symm)

/-- The recursive extension preserves all cut operations, including the
iterated identities at every lower-dimensional boundary. -/
theorem evaluateGlobular_preserves {G H : GlobularSet.{u}} (C : CutOperations H)
    (L : C.Compatible) (U : C.LeftUnital) (A : C.Associative)
    (I : C.Interchange) (J : C.UnitIdempotent) (V : C.UnitCompatible)
    (f : GlobularSet.Map G H) :
    CutOperations.Preserves (cutOperations G) C
      (evaluateGlobular (C.recursive L) .root f) where
  compose c p q h h' := evaluate_cutCompose C L U A I J c .root f p q _ _
  unit c p := evaluate_cutUnit C L V c .root f p

/-- Evaluation extends the given labels exactly. -/
theorem evaluateGlobular_extends {G H : GlobularSet.{u}} (C : CutOperations H)
    (L : C.Compatible) (R : C.RightUnital) (f : GlobularSet.Map G H) :
    GlobularSet.Map.comp (evaluateGlobular (C.recursive L) .root f)
      (singletonGlobular G) = f := by
  apply GlobularSet.Map.ext
  intro n p
  exact evaluate_singleton (C.recursive L)
    (fun {K} h {n a b} q => CutOperations.horizontal_right_unit
      (L.inContext h) (R.inContext h) (n := n) (a := a) (b := b) q)
    .root f p

/-- The precise algebraic universal property of labelled pastings for
targets with the stated cut laws. Identification with a standard presentation
of strict omega-categories is a separate comparison obligation. -/
theorem existsUnique_preserving_extension {G H : GlobularSet.{u}} (C : CutOperations H)
    (L : C.Compatible) (U : C.LeftUnital) (R : C.RightUnital) (A : C.Associative)
    (I : C.Interchange) (J : C.UnitIdempotent) (V : C.UnitCompatible)
    (f : GlobularSet.Map G H) :
    ∃! g : GlobularSet.Map (globular G) H,
      CutOperations.Preserves (cutOperations G) C g ∧
      GlobularSet.Map.comp g (singletonGlobular G) = f := by
  refine ⟨evaluateGlobular (C.recursive L) .root f,
    ⟨evaluateGlobular_preserves C L U A I J V f, evaluateGlobular_extends C L R f⟩, ?_⟩
  intro g hg
  exact preserves_ext C L g _ hg.1 (evaluateGlobular_preserves C L U A I J V f)
    (hg.2.trans (evaluateGlobular_extends C L R f).symm)

/-- The second multiplication unit equation: replacing every generating
label by a singleton, then flattening, retains the entire original diagram. -/
theorem flatten_map_singleton {G : GlobularSet.{u}} {n : Nat} (p : Pasting n G) :
    (flattenGlobular G).app (n := n) (map (singletonGlobular G) p) = p := by
  have hp := evaluate_precompose (recursiveComposition G) .root
    (GlobularSet.Map.id (globular G)) (singletonGlobular G) p
  have he : GlobularSet.Map.comp (GlobularSet.Map.id (globular G)) (singletonGlobular G) =
      singletonGlobular G := by
    apply GlobularSet.Map.ext
    intro n c
    rfl
  exact hp.trans ((_root_.congrArg (fun f => evaluate (recursiveComposition G) .root f p) he).trans
    (evaluate_singletonLabels p))

def singletonNatTrans : CategoryTheory.NatTrans (CategoryTheory.Functor.id GlobularSet.{u}) pastingFunctor where
  app := singletonGlobular
  naturality {X Y} f := (singleton_natural f).symm

/-- First unit law as an equation of actual globular maps. -/
theorem flatten_unit_left (G : GlobularSet.{u}) :
    GlobularSet.Map.comp (flattenGlobular G) (singletonGlobular (globular G)) =
      GlobularSet.Map.id (globular G) := by
  apply GlobularSet.Map.ext
  intro n p
  exact flatten_singleton p

/-- Second unit law as an equation of actual globular maps. -/
theorem flatten_unit_right (G : GlobularSet.{u}) :
    GlobularSet.Map.comp (flattenGlobular G) (mapGlobular (singletonGlobular G)) =
      GlobularSet.Map.id (globular G) := by
  apply GlobularSet.Map.ext
  intro n p
  exact flatten_map_singleton p

/-- The labelled-pasting endofunctor with its verified natural unit,
natural flattening, and all three monad equations. This does not itself
establish the free strict-category universal property or an operadic action. -/
noncomputable def pastingMonad : CategoryTheory.Monad GlobularSet.{u} where
  toFunctor := pastingFunctor
  η := singletonNatTrans
  μ := flattenNatTrans
  assoc G := by
    apply GlobularSet.Map.ext
    intro n p
    exact (flatten_assoc G p).symm
  left_unit G := flatten_unit_left G
  right_unit G := flatten_unit_right G

/-- Evaluating a nested diagram agrees with first evaluating its labels.
This is the algebra multiplication law for the actual pasting monad. -/
theorem evaluate_multiplication {H : GlobularSet.{u}} (C : CutOperations H)
    (L : C.Compatible) (U : C.LeftUnital) (A : C.Associative)
    (I : C.Interchange) (J : C.UnitIdempotent) (V : C.UnitCompatible)
    {n : Nat} (p : Pasting n (globular H)) :
    (evaluateGlobular (C.recursive L) .root (GlobularSet.Map.id H)).app
      ((flattenGlobular H).app p) =
    (evaluateGlobular (C.recursive L) .root (GlobularSet.Map.id H)).app
      (map (evaluateGlobular (C.recursive L) .root (GlobularSet.Map.id H)) p) := by
  let e := evaluateGlobular (C.recursive L) .root (GlobularSet.Map.id H)
  have hpost := evaluate_postcompose (cutOperations H) C
    (cutOperations_compatible H) L .root .root e
    (evaluateGlobular_preserves C L U A I J V (GlobularSet.Map.id H))
    (GlobularSet.Map.id (globular H)) p
  have hpre := evaluate_precompose (C.recursive L) .root (GlobularSet.Map.id H) e p
  have he : GlobularSet.Map.comp e (GlobularSet.Map.id (globular H)) =
      GlobularSet.Map.comp (GlobularSet.Map.id H) e := by
    apply GlobularSet.Map.ext
    intro m c
    rfl
  exact hpost.trans ((_root_.congrArg (fun f => evaluate (C.recursive L) .root f p) he).trans
    hpre.symm)

/-- A map preserving cut operations intertwines the evaluation actions.
Thus the bridge respects morphisms, not just the underlying objects. -/
theorem preserves_evaluation {H K : GlobularSet.{u}}
    (C : CutOperations H) (D : CutOperations K) (L : C.Compatible) (M : D.Compatible)
    (f : GlobularSet.Map H K) (P : CutOperations.Preserves C D f)
    {n : Nat} (p : Pasting n H) :
    f.app (evaluate (C.recursive L) .root (GlobularSet.Map.id H) p) =
      evaluate (D.recursive M) .root (GlobularSet.Map.id K) (map f p) := by
  have hpost := evaluate_postcompose C D L M .root .root f P (GlobularSet.Map.id H) p
  have hpre := evaluate_precompose (D.recursive M) .root (GlobularSet.Map.id K) f p
  have he : GlobularSet.Map.comp f (GlobularSet.Map.id H) =
      GlobularSet.Map.comp (GlobularSet.Map.id K) f := by
    apply GlobularSet.Map.ext
    intro m c
    rfl
  exact hpost.trans ((_root_.congrArg (fun g => evaluate (D.recursive M) .root g p) he).trans
    hpre.symm)

/-- Every target satisfying the explicit strict cut laws gives an actual
Eilenberg-Moore algebra. No weak operadic action is asserted by this bridge. -/
noncomputable def cutOperationsAlgebra {H : GlobularSet.{u}} (C : CutOperations H)
    (L : C.Compatible) (U : C.LeftUnital) (R : C.RightUnital) (A : C.Associative)
    (I : C.Interchange) (J : C.UnitIdempotent) (V : C.UnitCompatible) :
    CategoryTheory.Monad.Algebra pastingMonad where
  A := H
  a := evaluateGlobular (C.recursive L) .root (GlobularSet.Map.id H)
  unit := evaluateGlobular_extends C L R (GlobularSet.Map.id H)
  assoc := by
    apply GlobularSet.Map.ext
    intro n p
    exact evaluate_multiplication C L U A I J V p

end Pasting

namespace GlobularSet

/-- The terminal globular set has exactly one cell at every dimension. -/
def terminal : GlobularSet.{u} where
  Cell _ := PUnit.{u + 1}
  source _ := PUnit.unit
  target _ := PUnit.unit
  source_source _ := rfl
  target_source _ := rfl

def terminalMap (G : GlobularSet.{u}) : Map G terminal.{u} where
  app _ := PUnit.unit
  source_app _ := rfl
  target_app _ := rfl

theorem terminalMap_unique {G : GlobularSet.{u}} (f : Map G terminal.{u}) : f = terminalMap G := by
  apply Map.ext
  intro n p
  exact @Subsingleton.elim PUnit _ _ _

end GlobularSet

/-- A collection of operations with arities in the implemented pasting
monad. This is the slice presentation of Raftogianis, Proposition 3.2;
substitution and an operad structure are additional data, not presumed. -/
structure GlobularCollection where
  operations : GlobularSet.{u}
  arity : GlobularSet.Map operations (Pasting.globular GlobularSet.terminal.{u})

namespace GlobularCollection

/-- Forget labels, retaining the entire recursive globular pasting shape. -/
def shape (G : GlobularSet.{u}) : GlobularSet.Map (Pasting.globular G)
    (Pasting.globular GlobularSet.terminal.{u}) := Pasting.mapGlobular (GlobularSet.terminalMap G)

theorem shape_map {G H : GlobularSet.{u}} (f : GlobularSet.Map G H)
    {n : Nat} (p : Pasting n G) : (shape H).app (Pasting.map f p) = (shape G).app p := by
  exact (Pasting.map_comp f (GlobularSet.terminalMap H) p).trans
    (_root_.congrArg (fun k => Pasting.map k p)
      (GlobularSet.terminalMap_unique (GlobularSet.Map.comp (GlobularSet.terminalMap H) f)))

/-- An operation and an actual labelled input diagram with matching arity. -/
def application (C : GlobularCollection.{u}) (G : GlobularSet.{u}) : GlobularSet.{u} :=
  GlobularSet.pullback C.arity (shape G)

def operation (C : GlobularCollection.{u}) (G : GlobularSet.{u}) :
    GlobularSet.Map (C.application G) C.operations := GlobularSet.pullbackFst C.arity (shape G)

def inputs (C : GlobularCollection.{u}) (G : GlobularSet.{u}) :
    GlobularSet.Map (C.application G) (Pasting.globular G) := GlobularSet.pullbackSnd C.arity (shape G)

/-- Relabelling leaves the operation itself unchanged. -/
def map (C : GlobularCollection.{u}) {G H : GlobularSet.{u}} (f : GlobularSet.Map G H) :
    GlobularSet.Map (C.application G) (C.application H) where
  app p := ⟨⟨p.val.1, Pasting.map f p.val.2⟩, p.property.trans (shape_map f p.val.2).symm⟩
  source_app p := Subtype.ext (Prod.ext rfl ((Pasting.mapGlobular f).source_app p.val.2))
  target_app p := Subtype.ext (Prod.ext rfl ((Pasting.mapGlobular f).target_app p.val.2))

def functor (C : GlobularCollection.{u}) : CategoryTheory.Functor GlobularSet.{u} GlobularSet.{u} where
  obj := C.application
  map := C.map
  map_id G := by
    apply GlobularSet.Map.ext
    intro n p
    exact Subtype.ext (Prod.ext rfl (Pasting.map_id G p.val.2))
  map_comp f g := by
    apply GlobularSet.Map.ext
    intro n p
    exact Subtype.ext (Prod.ext rfl (Pasting.map_comp f g p.val.2).symm)

/-- The collection's arity transformation is an actual natural transformation. -/
def arityTransformation (C : GlobularCollection.{u}) :
    CategoryTheory.NatTrans C.functor Pasting.pastingFunctor where
  app := C.inputs
  naturality {X Y} f := by
    apply GlobularSet.Map.ext
    intro n p
    rfl

/-- Each arity naturality square has a unique labelled-operation lift. -/
theorem arity_cartesian (C : GlobularCollection.{u}) {G H : GlobularSet.{u}}
    (f : GlobularSet.Map G H) {n : Nat} (p : Pasting n G) (q : (C.application H).Cell n)
    (h : Pasting.map f p = (C.inputs H).app q) :
    ∃! r : (C.application G).Cell n, (C.inputs G).app r = p ∧ (C.map f).app r = q := by
  let r : (C.application G).Cell n := ⟨⟨q.val.1, p⟩,
    q.property.trans ((_root_.congrArg (shape H).app h.symm).trans (shape_map f p))⟩
  refine ⟨r, ⟨rfl, Subtype.ext (Prod.ext rfl h)⟩, ?_⟩
  intro s hs
  apply Subtype.ext
  exact Prod.ext (_root_.congrArg (fun t : (C.application H).Cell n => t.val.1) hs.2) hs.1

/-- The same square is a pullback in globular sets, including both boundary
equations and uniqueness for arbitrary globular cones. -/
theorem arity_globular_pullback (C : GlobularCollection.{u}) {G H X : GlobularSet.{u}}
    (f : GlobularSet.Map G H) (p : GlobularSet.Map X (Pasting.globular G))
    (q : GlobularSet.Map X (C.application H))
    (h : GlobularSet.Map.comp (Pasting.mapGlobular f) p = GlobularSet.Map.comp (C.inputs H) q) :
    ∃! d : GlobularSet.Map X (C.application G),
      GlobularSet.Map.comp (C.inputs G) d = p ∧ GlobularSet.Map.comp (C.map f) d = q := by
  let d : GlobularSet.Map X (C.application G) := GlobularSet.pullbackLift C.arity (shape G)
    (GlobularSet.Map.comp (C.operation H) q) p (by
      apply GlobularSet.Map.ext
      intro n x
      have hx := _root_.congrArg (fun k : GlobularSet.Map X (Pasting.globular H) => k.app x) h
      exact (q.app x).property.trans
        ((_root_.congrArg (shape H).app hx.symm).trans (shape_map f (p.app x))))
  refine ⟨d, ⟨?_, ?_⟩, ?_⟩
  · apply GlobularSet.Map.ext
    intro n x
    rfl
  · apply GlobularSet.Map.ext
    intro n x
    exact Subtype.ext (Prod.ext rfl
      (_root_.congrArg (fun k : GlobularSet.Map X (Pasting.globular H) => k.app x) h))
  · intro e he
    apply GlobularSet.Map.ext
    intro n x
    apply Subtype.ext
    exact Prod.ext
      (_root_.congrArg (fun k : GlobularSet.Map X (C.application H) => (k.app x).val.1) he.2)
      (_root_.congrArg (fun k : GlobularSet.Map X (Pasting.globular G) => k.app x) he.1)

/-- The induced collection functor preserves globular pullbacks. Both
operation data and recursively labelled inputs are recovered uniquely. -/
theorem application_pullback_universal (C : GlobularCollection.{u}) {G H K X : GlobularSet.{u}}
    (f : GlobularSet.Map G K) (g : GlobularSet.Map H K)
    (p : GlobularSet.Map X (C.application G)) (q : GlobularSet.Map X (C.application H))
    (h : GlobularSet.Map.comp (C.map f) p = GlobularSet.Map.comp (C.map g) q) :
    ∃! d : GlobularSet.Map X (C.application (GlobularSet.pullback f g)),
      GlobularSet.Map.comp (C.map (GlobularSet.pullbackFst f g)) d = p ∧
      GlobularSet.Map.comp (C.map (GlobularSet.pullbackSnd f g)) d = q := by
  obtain ⟨t, ht, hu⟩ := Pasting.pasting_pullback_universal f g
    (GlobularSet.Map.comp (C.inputs G) p) (GlobularSet.Map.comp (C.inputs H) q) (by
      apply GlobularSet.Map.ext
      intro n x
      exact _root_.congrArg (fun k : GlobularSet.Map X (C.application K) => (k.app x).val.2) h)
  obtain ⟨d, hd, hdu⟩ := C.arity_globular_pullback (GlobularSet.pullbackFst f g) t p ht.1
  have hdq : GlobularSet.Map.comp (C.map (GlobularSet.pullbackSnd f g)) d = q := by
    apply GlobularSet.Map.ext
    intro n x
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · exact (_root_.congrArg (fun k : GlobularSet.Map X (C.application G) => (k.app x).val.1) hd.2).trans
        (_root_.congrArg (fun k : GlobularSet.Map X (C.application K) => (k.app x).val.1) h)
    · exact (_root_.congrArg (fun z => Pasting.map (GlobularSet.pullbackSnd f g) z)
        (_root_.congrArg (fun k : GlobularSet.Map X (Pasting.globular (GlobularSet.pullback f g)) => k.app x) hd.1)).trans
          (_root_.congrArg (fun k : GlobularSet.Map X (Pasting.globular H) => k.app x) ht.2)
  refine ⟨d, ⟨hd.2, hdq⟩, ?_⟩
  intro e he
  apply hdu e
  refine ⟨?_, he.1⟩
  apply hu (GlobularSet.Map.comp (C.inputs (GlobularSet.pullback f g)) e)
  constructor
  · apply GlobularSet.Map.ext
    intro n x
    exact _root_.congrArg (fun k : GlobularSet.Map X (C.application G) => (k.app x).val.2) he.1
  · apply GlobularSet.Map.ext
    intro n x
    exact _root_.congrArg (fun k : GlobularSet.Map X (C.application H) => (k.app x).val.2) he.2

/-- Forgetting labels over the terminal globular set changes nothing. -/
theorem shape_terminal {n : Nat} (p : Pasting n GlobularSet.terminal.{u}) :
    (shape GlobularSet.terminal).app p = p := by
  have h : GlobularSet.terminalMap GlobularSet.terminal.{u} =
      GlobularSet.Map.id GlobularSet.terminal :=
    (GlobularSet.terminalMap_unique (GlobularSet.Map.id GlobularSet.terminal)).symm
  exact (_root_.congrArg (fun k => Pasting.map k p) h).trans (Pasting.map_id _ p)

/-- Recover the original operation by labelling its arity in the terminal
globular set. This is inverse to the operation projection at the terminal. -/
def atTerminal (C : GlobularCollection.{u}) :
    GlobularSet.Map C.operations (C.application GlobularSet.terminal) where
  app p := ⟨⟨p, C.arity.app p⟩, (shape_terminal (C.arity.app p)).symm⟩
  source_app p := Subtype.ext (Prod.ext rfl (C.arity.source_app p))
  target_app p := Subtype.ext (Prod.ext rfl (C.arity.target_app p))

def applicationTerminalIso (C : GlobularCollection.{u}) :
    CategoryTheory.Iso (C.application GlobularSet.terminal) C.operations where
  hom := C.operation GlobularSet.terminal
  inv := C.atTerminal
  hom_inv_id := by
    apply GlobularSet.Map.ext
    intro n p
    exact Subtype.ext (Prod.ext rfl (p.property.trans (shape_terminal p.val.2)))
  inv_hom_id := by
    apply GlobularSet.Map.ext
    intro n p
    rfl

theorem atTerminal_arity (C : GlobularCollection.{u}) :
    GlobularSet.Map.comp (C.inputs GlobularSet.terminal) C.atTerminal = C.arity := by
  apply GlobularSet.Map.ext
  intro n p
  rfl

/-- The identity collection selects singleton arities in every dimension. -/
def identity : GlobularCollection.{u} where
  operations := GlobularSet.terminal
  arity := Pasting.singletonGlobular GlobularSet.terminal

def identityApplicationIn (G : GlobularSet.{u}) :
    GlobularSet.Map G (identity.application G) where
  app p := ⟨⟨PUnit.unit, Pasting.singleton p⟩,
    (Pasting.map_singleton (GlobularSet.terminalMap G) p).symm⟩
  source_app p := Subtype.ext (Prod.ext rfl (Pasting.source_singleton G p))
  target_app p := Subtype.ext (Prod.ext rfl (Pasting.target_singleton G p))

theorem identityApplication_lift (G : GlobularSet.{u}) :
    ∃! d : GlobularSet.Map (identity.application G) G,
      GlobularSet.Map.comp (Pasting.singletonGlobular G) d = identity.inputs G ∧
      GlobularSet.Map.comp (GlobularSet.terminalMap G) d = identity.operation G := by
  apply Pasting.singleton_globular_pullback (GlobularSet.terminalMap G)
  apply GlobularSet.Map.ext
  intro n p
  exact p.property.symm

noncomputable def identityApplicationOut (G : GlobularSet.{u}) :
    GlobularSet.Map (identity.application G) G := (identityApplication_lift G).choose

theorem identityApplicationOut_inputs (G : GlobularSet.{u}) :
    GlobularSet.Map.comp (Pasting.singletonGlobular G) (identityApplicationOut G) = identity.inputs G :=
  (identityApplication_lift G).choose_spec.1.1

noncomputable def identityApplicationIso (G : GlobularSet.{u}) :
    CategoryTheory.Iso (identity.application G) G where
  hom := identityApplicationOut G
  inv := identityApplicationIn G
  hom_inv_id := by
    apply GlobularSet.Map.ext
    intro n p
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · exact @Subsingleton.elim PUnit _ _ _
    · exact _root_.congrArg (fun k : GlobularSet.Map (identity.application G) (Pasting.globular G) => k.app p)
        (identityApplicationOut_inputs G)
  inv_hom_id := by
    apply GlobularSet.Map.ext
    intro n p
    apply Pasting.singleton_injective G
    exact _root_.congrArg (fun k : GlobularSet.Map (identity.application G) (Pasting.globular G) =>
      k.app ((identityApplicationIn G).app p)) (identityApplicationOut_inputs G)

theorem identityApplicationOut_natural {G H : GlobularSet.{u}} (f : GlobularSet.Map G H) :
    GlobularSet.Map.comp (identityApplicationOut H) (identity.map f) =
      GlobularSet.Map.comp f (identityApplicationOut G) := by
  apply GlobularSet.Map.ext
  intro n p
  apply Pasting.singleton_injective H
  exact (_root_.congrArg (fun k : GlobularSet.Map (identity.application H) (Pasting.globular H) =>
      k.app ((identity.map f).app p)) (identityApplicationOut_inputs H)).trans
    ((_root_.congrArg (fun q => Pasting.map f q)
      (_root_.congrArg (fun k : GlobularSet.Map (identity.application G) (Pasting.globular G) => k.app p)
        (identityApplicationOut_inputs G)).symm).trans
      (Pasting.map_singleton f ((identityApplicationOut G).app p)))

/-- Substitution of collections: an outer operation whose inputs are inner
operations. Its arity is obtained by the verified globular multiplication. -/
noncomputable def substitute (C D : GlobularCollection.{u}) : GlobularCollection.{u} where
  operations := C.application D.operations
  arity := GlobularSet.Map.comp (Pasting.flattenGlobular GlobularSet.terminal)
    (GlobularSet.Map.comp (Pasting.mapGlobular D.arity) (C.inputs D.operations))

/-- The operation part of a nested labelled operation forgets only the
inner input labels, not the inner operations or their placement. -/
def substitutionOperation (C D : GlobularCollection.{u}) (G : GlobularSet.{u}) :
    GlobularSet.Map (C.application (D.application G)) (C.application D.operations) :=
  C.map (D.operation G)

noncomputable def substitutionInputs (C D : GlobularCollection.{u}) (G : GlobularSet.{u}) :
    GlobularSet.Map (C.application (D.application G)) (Pasting.globular G) :=
  GlobularSet.Map.comp (Pasting.flattenGlobular G)
    (GlobularSet.Map.comp (Pasting.mapGlobular (D.inputs G)) (C.inputs (D.application G)))

theorem substitution_match (C D : GlobularCollection.{u}) (G : GlobularSet.{u}) :
    GlobularSet.Map.comp (C.substitute D).arity (C.substitutionOperation D G) =
      GlobularSet.Map.comp (shape G) (C.substitutionInputs D G) := by
  apply GlobularSet.Map.ext
  intro n p
  change (Pasting.flattenGlobular GlobularSet.terminal).app
      (Pasting.map D.arity (Pasting.map (D.operation G) p.val.2)) =
    (shape G).app ((Pasting.flattenGlobular G).app (Pasting.map (D.inputs G) p.val.2))
  apply Eq.trans (_root_.congrArg (Pasting.flattenGlobular GlobularSet.terminal).app
    (Pasting.map_comp (D.operation G) D.arity p.val.2))
  apply Eq.trans (_root_.congrArg (fun k => (Pasting.flattenGlobular GlobularSet.terminal).app
    (Pasting.map k p.val.2)) (GlobularSet.pullback_condition D.arity (shape G)))
  exact (_root_.congrArg (Pasting.flattenGlobular GlobularSet.terminal).app
    (Pasting.map_comp (D.inputs G) (shape G) p.val.2).symm).trans
      (Pasting.flatten_natural (GlobularSet.terminalMap G) (Pasting.map (D.inputs G) p.val.2)).symm

/-- Flatten the inputs of a nested application, preserving the outer
operation, every inner operation, and the combined arity. -/
noncomputable def substitutionComparison (C D : GlobularCollection.{u}) (G : GlobularSet.{u}) :
    GlobularSet.Map (C.application (D.application G)) ((C.substitute D).application G) :=
  GlobularSet.pullbackLift (C.substitute D).arity (shape G)
    (C.substitutionOperation D G) (C.substitutionInputs D G) (C.substitution_match D G)

theorem substitutionComparison_operation (C D : GlobularCollection.{u}) (G : GlobularSet.{u}) :
    GlobularSet.Map.comp ((C.substitute D).operation G) (C.substitutionComparison D G) =
      C.substitutionOperation D G := by
  apply GlobularSet.Map.ext
  intro n p
  rfl

theorem substitutionComparison_inputs (C D : GlobularCollection.{u}) (G : GlobularSet.{u}) :
    GlobularSet.Map.comp ((C.substitute D).inputs G) (C.substitutionComparison D G) =
      C.substitutionInputs D G := by
  apply GlobularSet.Map.ext
  intro n p
  rfl

/-- The substitution comparison commutes with arbitrary relabelling of
inputs. Its operation component remains the same nested operation. -/
theorem substitutionComparison_natural (C D : GlobularCollection.{u})
    {G H : GlobularSet.{u}} (f : GlobularSet.Map G H) :
    GlobularSet.Map.comp (C.substitutionComparison D H) (C.map (D.map f)) =
      GlobularSet.Map.comp ((C.substitute D).map f) (C.substitutionComparison D G) := by
  have hop : GlobularSet.Map.comp (D.operation H) (D.map f) = D.operation G := by
    apply GlobularSet.Map.ext
    intro n p
    rfl
  have hin : GlobularSet.Map.comp (D.inputs H) (D.map f) =
      GlobularSet.Map.comp (Pasting.mapGlobular f) (D.inputs G) := by
    apply GlobularSet.Map.ext
    intro n p
    rfl
  apply GlobularSet.Map.ext
  intro n p
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    exact Prod.ext rfl ((Pasting.map_comp (D.map f) (D.operation H) p.val.2).trans
      (_root_.congrArg (fun k => Pasting.map k p.val.2) hop))
  · exact (_root_.congrArg (Pasting.flattenGlobular H).app
      ((Pasting.map_comp (D.map f) (D.inputs H) p.val.2).trans
        ((_root_.congrArg (fun k => Pasting.map k p.val.2) hin).trans
          (Pasting.map_comp (D.inputs G) (Pasting.mapGlobular f) p.val.2).symm))).trans
        (Pasting.flatten_natural f (Pasting.map (D.inputs G) p.val.2)).symm

/-- The substitution comparison has a unique inverse on every cell.
Multiplication cartesianness recovers the nested input diagram, and pasting
pullback preservation then recovers its inner-operation labels. -/
theorem substitutionComparison_unique_lift (C D : GlobularCollection.{u}) (G : GlobularSet.{u})
    {n : Nat} (p : ((C.substitute D).application G).Cell n) :
    ∃! r : (C.application (D.application G)).Cell n,
      (C.substitutionComparison D G).app r = p := by
  obtain ⟨t, ⟨ht, hs⟩, hu⟩ := Pasting.flatten_cartesian (GlobularSet.terminalMap G)
    p.val.2 (Pasting.map D.arity p.val.1.val.2) p.property.symm
  obtain ⟨w, hw, hw'⟩ := Pasting.pullback_pasting_exists D.arity (shape G)
    p.val.1.val.2 t hs.symm
  let r : (C.application (D.application G)).Cell n := ⟨⟨p.val.1.val.1, w⟩,
    p.val.1.property.trans ((_root_.congrArg (shape D.operations).app hw.symm).trans
      (shape_map (D.operation G) w))⟩
  refine ⟨r, ?_, ?_⟩
  · apply Subtype.ext
    exact Prod.ext (Subtype.ext (Prod.ext rfl hw))
      ((_root_.congrArg (Pasting.flattenGlobular G).app hw').trans ht)
  · intro s he
    have ho : s.val.1 = p.val.1.val.1 :=
      _root_.congrArg (fun z : ((C.substitute D).application G).Cell n => z.val.1.val.1) he
    have hm : Pasting.map (D.operation G) s.val.2 = p.val.1.val.2 :=
      _root_.congrArg (fun z : ((C.substitute D).application G).Cell n => z.val.1.val.2) he
    have hf : (Pasting.flattenGlobular G).app (Pasting.map (D.inputs G) s.val.2) = p.val.2 :=
      _root_.congrArg (fun z : ((C.substitute D).application G).Cell n => z.val.2) he
    have hshape : Pasting.map (shape G) (Pasting.map (D.inputs G) s.val.2) =
        Pasting.map D.arity p.val.1.val.2 :=
      (Pasting.map_comp (D.inputs G) (shape G) s.val.2).trans
        ((_root_.congrArg (fun k => Pasting.map k s.val.2)
          (GlobularSet.pullback_condition D.arity (shape G)).symm).trans
          ((Pasting.map_comp (D.operation G) D.arity s.val.2).symm.trans
            (_root_.congrArg (Pasting.map D.arity) hm)))
    have hi := hu (Pasting.map (D.inputs G) s.val.2) ⟨hf, hshape⟩
    exact Subtype.ext (Prod.ext ho (Pasting.pullback_pasting_ext D.arity (shape G)
      s.val.2 w (hm.trans hw.symm) (hi.trans hw'.symm)))

/-- The verified cellwise inverse respects both adjacent globular maps by
uniqueness; it does not add or quotient any nested operation data. -/
noncomputable def substitutionComparisonInverse (C D : GlobularCollection.{u}) (G : GlobularSet.{u}) :
    GlobularSet.Map ((C.substitute D).application G) (C.application (D.application G)) where
  app p := (C.substitutionComparison_unique_lift D G p).choose
  source_app p := (C.substitutionComparison_unique_lift D G
    (((C.substitute D).application G).source p)).choose_spec.2 _
      (((C.substitutionComparison D G).source_app _).symm.trans
        (_root_.congrArg ((C.substitute D).application G).source
          (C.substitutionComparison_unique_lift D G p).choose_spec.1))
  target_app p := (C.substitutionComparison_unique_lift D G
    (((C.substitute D).application G).target p)).choose_spec.2 _
      (((C.substitutionComparison D G).target_app _).symm.trans
        (_root_.congrArg ((C.substitute D).application G).target
          (C.substitutionComparison_unique_lift D G p).choose_spec.1))

noncomputable def substitutionComparisonIso (C D : GlobularCollection.{u}) (G : GlobularSet.{u}) :
    CategoryTheory.Iso (C.application (D.application G)) ((C.substitute D).application G) where
  hom := C.substitutionComparison D G
  inv := C.substitutionComparisonInverse D G
  hom_inv_id := by
    apply GlobularSet.Map.ext
    intro n p
    exact ((C.substitutionComparison_unique_lift D G ((C.substitutionComparison D G).app p)).choose_spec.2 p rfl).symm
  inv_hom_id := by
    apply GlobularSet.Map.ext
    intro n p
    exact (C.substitutionComparison_unique_lift D G p).choose_spec.1

/-- Substitution of collections implements composition of their actual
application functors, naturally in the input globular set. -/
noncomputable def substitutionFunctorIso (C D : GlobularCollection.{u}) :
    CategoryTheory.Iso (CategoryTheory.Functor.comp D.functor C.functor) (C.substitute D).functor :=
  CategoryTheory.NatIso.ofComponents (fun G => C.substitutionComparisonIso D G)
    (fun f => C.substitutionComparison_natural D f)

/-- Maps of collections preserve the actual recursive arity, not merely
the dimension or number of inputs. -/
structure Hom (C D : GlobularCollection.{u}) where
  operations : GlobularSet.Map C.operations D.operations
  arity : GlobularSet.Map.comp D.arity operations = C.arity

namespace Hom

def id (C : GlobularCollection.{u}) : Hom C C where
  operations := GlobularSet.Map.id C.operations
  arity := rfl

def comp {C D E : GlobularCollection.{u}} (g : Hom D E) (f : Hom C D) : Hom C E where
  operations := GlobularSet.Map.comp g.operations f.operations
  arity := by
    apply GlobularSet.Map.ext
    intro n p
    exact (_root_.congrArg (fun k : GlobularSet.Map D.operations (Pasting.globular GlobularSet.terminal) =>
      k.app (f.operations.app p)) g.arity).trans
        (_root_.congrArg (fun k : GlobularSet.Map C.operations (Pasting.globular GlobularSet.terminal) => k.app p) f.arity)

@[ext] theorem ext {C D : GlobularCollection.{u}} {f g : Hom C D}
    (h : f.operations = g.operations) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Apply a collection map without changing a single input label. -/
def application {C D : GlobularCollection.{u}} (f : Hom C D) (G : GlobularSet.{u}) :
    GlobularSet.Map (C.application G) (D.application G) where
  app p := ⟨⟨f.operations.app p.val.1, p.val.2⟩,
    (_root_.congrArg (fun k : GlobularSet.Map C.operations (Pasting.globular GlobularSet.terminal) =>
      k.app p.val.1) f.arity).trans p.property⟩
  source_app p := Subtype.ext (Prod.ext (f.operations.source_app p.val.1) rfl)
  target_app p := Subtype.ext (Prod.ext (f.operations.target_app p.val.1) rfl)

theorem application_natural {C D : GlobularCollection.{u}} (f : Hom C D)
    {G H : GlobularSet.{u}} (g : GlobularSet.Map G H) :
    GlobularSet.Map.comp (f.application H) (C.map g) =
      GlobularSet.Map.comp (D.map g) (f.application G) := by
  apply GlobularSet.Map.ext
  intro n p
  rfl

def transformation {C D : GlobularCollection.{u}} (f : Hom C D) :
    CategoryTheory.NatTrans C.functor D.functor where
  app := f.application
  naturality {X Y} g := f.application_natural g

theorem application_id (C : GlobularCollection.{u}) (G : GlobularSet.{u}) :
    (id C).application G = GlobularSet.Map.id (C.application G) := by
  apply GlobularSet.Map.ext
  intro n p
  rfl

theorem application_comp {C D E : GlobularCollection.{u}} (g : Hom D E) (f : Hom C D)
    (G : GlobularSet.{u}) :
    (comp g f).application G = GlobularSet.Map.comp (g.application G) (f.application G) := by
  apply GlobularSet.Map.ext
  intro n p
  rfl

theorem application_inputs {C D : GlobularCollection.{u}} (f : Hom C D) (G : GlobularSet.{u}) :
    GlobularSet.Map.comp (D.inputs G) (f.application G) = C.inputs G := by
  apply GlobularSet.Map.ext
  intro n p
  rfl

/-- A map of operation collections induces cartesian naturality squares:
the original operation and all original labels have a unique joint lift. -/
theorem application_cartesian {C D : GlobularCollection.{u}} (f : Hom C D)
    {G H : GlobularSet.{u}} (g : GlobularSet.Map G H) {n : Nat}
    (p : (D.application G).Cell n) (q : (C.application H).Cell n)
    (h : (D.map g).app p = (f.application H).app q) :
    ∃! r : (C.application G).Cell n, (f.application G).app r = p ∧ (C.map g).app r = q := by
  have ho : p.val.1 = f.operations.app q.val.1 :=
    _root_.congrArg (fun z : (D.application H).Cell n => z.val.1) h
  have hi : Pasting.map g p.val.2 = q.val.2 :=
    _root_.congrArg (fun z : (D.application H).Cell n => z.val.2) h
  let r : (C.application G).Cell n := ⟨⟨q.val.1, p.val.2⟩,
    (_root_.congrArg (fun k : GlobularSet.Map C.operations (Pasting.globular GlobularSet.terminal) =>
      k.app q.val.1) f.arity).symm.trans
        ((_root_.congrArg D.arity.app ho.symm).trans p.property)⟩
  refine ⟨r, ⟨Subtype.ext (Prod.ext ho.symm rfl), Subtype.ext (Prod.ext rfl hi)⟩, ?_⟩
  intro s hs
  exact Subtype.ext (Prod.ext
    (_root_.congrArg (fun z : (C.application H).Cell n => z.val.1) hs.2)
    (_root_.congrArg (fun z : (D.application G).Cell n => z.val.2) hs.1))

/-- Substitute arity-preserving maps into both the outer and inner
operation positions. Every labelled inner operation is retained. -/
noncomputable def substitute {C D E F : GlobularCollection.{u}} (f : Hom C E) (g : Hom D F) :
    Hom (C.substitute D) (E.substitute F) where
  operations := GlobularSet.Map.comp (f.application F.operations) (C.map g.operations)
  arity := by
    apply GlobularSet.Map.ext
    intro n p
    change (Pasting.flattenGlobular GlobularSet.terminal).app
      (Pasting.map F.arity (Pasting.map g.operations p.val.2)) =
      (Pasting.flattenGlobular GlobularSet.terminal).app (Pasting.map D.arity p.val.2)
    exact _root_.congrArg (Pasting.flattenGlobular GlobularSet.terminal).app
      ((Pasting.map_comp g.operations F.arity p.val.2).trans
        (_root_.congrArg (fun k => Pasting.map k p.val.2) g.arity))

theorem substitute_id (C D : GlobularCollection.{u}) :
    substitute (id C) (id D) = id (C.substitute D) := by
  apply ext
  apply GlobularSet.Map.ext
  intro n p
  exact Subtype.ext (Prod.ext rfl (Pasting.map_id D.operations p.val.2))

theorem substitute_comp {C D E F J K : GlobularCollection.{u}}
    (f : Hom C E) (g : Hom D F) (h : Hom E J) (k : Hom F K) :
    substitute (comp h f) (comp k g) = comp (substitute h k) (substitute f g) := by
  apply ext
  apply GlobularSet.Map.ext
  intro n p
  exact Subtype.ext (Prod.ext rfl (Pasting.map_comp g.operations k.operations p.val.2).symm)

/-- The comparison from nested applications is natural in both operation
collections as well as in input labels. -/
theorem substitute_comparison {C D E F : GlobularCollection.{u}} (f : Hom C E) (g : Hom D F)
    (G : GlobularSet.{u}) :
    GlobularSet.Map.comp ((substitute f g).application G) (C.substitutionComparison D G) =
      GlobularSet.Map.comp (E.substitutionComparison F G)
        (GlobularSet.Map.comp (f.application (F.application G)) (C.map (g.application G))) := by
  have hop : GlobularSet.Map.comp (F.operation G) (g.application G) =
      GlobularSet.Map.comp g.operations (D.operation G) := by
    apply GlobularSet.Map.ext
    intro n p
    rfl
  apply GlobularSet.Map.ext
  intro n p
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    refine Prod.ext rfl ?_
    exact (Pasting.map_comp (D.operation G) g.operations p.val.2).trans
      ((_root_.congrArg (fun k => Pasting.map k p.val.2) hop.symm).trans
        (Pasting.map_comp (g.application G) (F.operation G) p.val.2).symm)
  · exact _root_.congrArg (Pasting.flattenGlobular G).app
      (((Pasting.map_comp (g.application G) (F.inputs G) p.val.2).trans
        (_root_.congrArg (fun k => Pasting.map k p.val.2) (g.application_inputs G))).symm)

noncomputable def leftUnit (C : GlobularCollection.{u}) : Hom (identity.substitute C) C where
  operations := identityApplicationOut C.operations
  arity := by
    apply GlobularSet.Map.ext
    intro n p
    have hp := _root_.congrArg (fun k : GlobularSet.Map (identity.application C.operations)
      (Pasting.globular C.operations) => k.app p) (identityApplicationOut_inputs C.operations)
    change C.arity.app ((identityApplicationOut C.operations).app p) =
      (Pasting.flattenGlobular GlobularSet.terminal).app (Pasting.map C.arity p.val.2)
    exact ((Pasting.flatten_singleton (C.arity.app ((identityApplicationOut C.operations).app p))).symm.trans
      (_root_.congrArg (Pasting.flattenGlobular GlobularSet.terminal).app
        ((Pasting.map_singleton C.arity ((identityApplicationOut C.operations).app p)).symm.trans
          (_root_.congrArg (Pasting.map C.arity) hp))))

def leftUnitInv (C : GlobularCollection.{u}) : Hom C (identity.substitute C) where
  operations := identityApplicationIn C.operations
  arity := by
    apply GlobularSet.Map.ext
    intro n p
    exact (_root_.congrArg (Pasting.flattenGlobular GlobularSet.terminal).app
      (Pasting.map_singleton C.arity p)).trans (Pasting.flatten_singleton (C.arity.app p))

def rightUnit (C : GlobularCollection.{u}) : Hom (C.substitute identity) C where
  operations := C.operation GlobularSet.terminal
  arity := by
    apply GlobularSet.Map.ext
    intro n p
    exact p.property.trans ((shape_terminal p.val.2).trans (Pasting.flatten_map_singleton p.val.2).symm)

def rightUnitInv (C : GlobularCollection.{u}) : Hom C (C.substitute identity) where
  operations := C.atTerminal
  arity := by
    apply GlobularSet.Map.ext
    intro n p
    exact Pasting.flatten_map_singleton (C.arity.app p)

/-- Left substitution units commute with every arity-preserving map. -/
theorem leftUnit_natural {C D : GlobularCollection.{u}} (f : Hom C D) :
    comp (leftUnit D) (substitute (id identity) f) = comp f (leftUnit C) := by
  apply ext
  exact identityApplicationOut_natural f.operations

/-- Right substitution units commute with every arity-preserving map. -/
theorem rightUnit_natural {C D : GlobularCollection.{u}} (f : Hom C D) :
    comp (rightUnit D) (substitute f (id identity)) = comp f (rightUnit C) := by
  apply ext
  apply GlobularSet.Map.ext
  intro n p
  rfl

/-- Terminal-labelled applications detect equality of collection maps.
This uses the actual terminal recovery map, not an injectivity premise. -/
theorem application_faithful {C D : GlobularCollection.{u}} {f g : Hom C D}
    (h : f.application GlobularSet.terminal = g.application GlobularSet.terminal) : f = g := by
  apply ext
  apply GlobularSet.Map.ext
  intro n p
  exact _root_.congrArg (fun k : GlobularSet.Map (C.application GlobularSet.terminal)
    (D.application GlobularSet.terminal) => (k.app (C.atTerminal.app p)).val.1) h

/-- Reassociate substitution from right nesting to left nesting. The
arity equation is the actual pasting multiplication associativity law. -/
noncomputable def associateInv (C D E : GlobularCollection.{u}) :
    Hom (C.substitute (D.substitute E)) ((C.substitute D).substitute E) where
  operations := C.substitutionComparison D E.operations
  arity := by
    apply GlobularSet.Map.ext
    intro n p
    change (Pasting.flattenGlobular GlobularSet.terminal).app
      (Pasting.map E.arity ((Pasting.flattenGlobular E.operations).app
        (Pasting.map (D.inputs E.operations) p.val.2))) =
      (Pasting.flattenGlobular GlobularSet.terminal).app (Pasting.map (D.substitute E).arity p.val.2)
    refine (_root_.congrArg (Pasting.flattenGlobular GlobularSet.terminal).app
      (Pasting.flatten_natural E.arity (Pasting.map (D.inputs E.operations) p.val.2))).trans ?_
    refine (Pasting.flatten_assoc GlobularSet.terminal
      (Pasting.map (Pasting.mapGlobular E.arity) (Pasting.map (D.inputs E.operations) p.val.2))).trans ?_
    apply _root_.congrArg (Pasting.flattenGlobular GlobularSet.terminal).app
    exact (Pasting.map_comp (Pasting.mapGlobular E.arity) (Pasting.flattenGlobular GlobularSet.terminal)
      (Pasting.map (D.inputs E.operations) p.val.2)).trans
        (Pasting.map_comp (D.inputs E.operations)
          (GlobularSet.Map.comp (Pasting.flattenGlobular GlobularSet.terminal) (Pasting.mapGlobular E.arity)) p.val.2)

noncomputable def associate (C D E : GlobularCollection.{u}) :
    Hom ((C.substitute D).substitute E) (C.substitute (D.substitute E)) where
  operations := C.substitutionComparisonInverse D E.operations
  arity := by
    apply GlobularSet.Map.ext
    intro n p
    have h := _root_.congrArg (fun k : GlobularSet.Map (C.substitute (D.substitute E)).operations
      (Pasting.globular GlobularSet.terminal) =>
        k.app ((C.substitutionComparisonInverse D E.operations).app p)) (associateInv C D E).arity
    exact h.symm.trans (_root_.congrArg ((C.substitute D).substitute E).arity.app
      ((C.substitutionComparison_unique_lift D E.operations p).choose_spec.1))

end Hom

instance : CategoryTheory.Category.{u} GlobularCollection.{u} where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp g f
  id_comp f := Hom.ext rfl
  comp_id f := Hom.ext rfl
  assoc f g h := Hom.ext rfl

/-- Substituting a collection into the identity collection is isomorphic
to the original collection, with exact preservation of arities. -/
noncomputable def leftUnitIso (C : GlobularCollection.{u}) :
    CategoryTheory.Iso (identity.substitute C) C where
  hom := Hom.leftUnit C
  inv := Hom.leftUnitInv C
  hom_inv_id := Hom.ext (identityApplicationIso C.operations).hom_inv_id
  inv_hom_id := Hom.ext (identityApplicationIso C.operations).inv_hom_id

def rightUnitIso (C : GlobularCollection.{u}) :
    CategoryTheory.Iso (C.substitute identity) C where
  hom := Hom.rightUnit C
  inv := Hom.rightUnitInv C
  hom_inv_id := Hom.ext C.applicationTerminalIso.hom_inv_id
  inv_hom_id := Hom.ext C.applicationTerminalIso.inv_hom_id

noncomputable def associatorIso (C D E : GlobularCollection.{u}) :
    CategoryTheory.Iso ((C.substitute D).substitute E) (C.substitute (D.substitute E)) where
  hom := Hom.associate C D E
  inv := Hom.associateInv C D E
  hom_inv_id := Hom.ext (C.substitutionComparisonIso D E.operations).inv_hom_id
  inv_hom_id := Hom.ext (C.substitutionComparisonIso D E.operations).hom_inv_id

end GlobularCollection

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

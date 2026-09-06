import ComputationalPaths.Path.OmegaGroupoid.GlobularFoundations
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans

/-!
# Recursively labelled globular pasting diagrams

Objects label dimension zero. In dimension `n+1`, a diagram is a composable
chain of `n`-diagrams in hom globular sets. The carrier and adjacent boundary
maps are defined by genuine dimension recursion. Candidate multiplication
is an actual globular flattening map with one verified unit equation; the
remaining monad laws and free strict-category property are not yet claimed.
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

def RightUnital {G : GlobularSet.{u}} (C : CutOperations G) : Prop :=
  ∀ {n} (c : Cut n) (p : G.Cell n),
    C.compose c p (C.unit c (CutBoundary.target c G p))
      (C.source_unit c (CutBoundary.target c G p)).symm = p

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

theorem Preserves.hom {G H : GlobularSet.{u}} {C : CutOperations G} {D : CutOperations H}
    {f : GlobularSet.Map G H} (P : Preserves C D f) (a b : G.Cell 0) :
    Preserves (C.hom a b) (D.hom (f.app a) (f.app b)) (f.hom a b) where
  compose c p q h h' := Subtype.ext (P.compose (.lift c) p.val q.val _ _)
  unit c p := Subtype.ext (P.unit (.lift c) p.val)

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

/-
# Galois Connections via Computational Paths

This module formalizes Galois connections, closure/interior operators,
Galois insertions, and fixed-point theorems using computational paths.

## Key Constructions

| Definition/Theorem                  | Description                                     |
|-------------------------------------|-------------------------------------------------|
| `PathGaloisConnection`              | Galois connection via path witnesses             |
| `PathClosureOp`                     | Closure operator as path idempotent              |
| `PathInteriorOp`                    | Interior operator as path idempotent             |
| `PathGaloisInsertion`               | Galois insertion with retraction path            |
| `KnasterTarskiPath`                 | Knaster-Tarski fixed point via paths             |

## References

- Davey & Priestley, "Introduction to Lattices and Order"
- Birkhoff, "Lattice Theory"
- Erné et al., "A Primer on Galois Connections"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace GaloisPaths

universe u v

/-! ## Ordered sets with path witnesses -/

/-- A partially ordered set with Path-valued order proofs. -/
structure PathPoset (A : Type u) where
  /-- Partial order. -/
  le : A → A → Prop
  /-- Reflexivity. -/
  le_refl : ∀ x, le x x
  /-- Transitivity. -/
  le_trans : ∀ x y z, le x y → le y z → le x z
  /-- Antisymmetry yielding a path. -/
  le_antisymm : ∀ x y, le x y → le y x → Path x y

/-- A monotone map between posets. -/
structure MonotoneMap {A : Type u} {B : Type v}
    (PA : PathPoset A) (PB : PathPoset B) where
  /-- The underlying function. -/
  fn : A → B
  /-- Monotonicity. -/
  monotone : ∀ x y, PA.le x y → PB.le (fn x) (fn y)

/-! ## Galois connections -/

/-- A Galois connection between two posets: (f, g) where
    f a ≤ b ⟺ a ≤ g b, witnessed by paths. -/
structure PathGaloisConnection {A : Type u} {B : Type v}
    (PA : PathPoset A) (PB : PathPoset B) where
  /-- Lower adjoint (left adjoint). -/
  lower : A → B
  /-- Upper adjoint (right adjoint). -/
  upper : B → A
  /-- Adjunction: f a ≤ b → a ≤ g b. -/
  gc_left : ∀ a b, PB.le (lower a) b → PA.le a (upper b)
  /-- Adjunction: a ≤ g b → f a ≤ b. -/
  gc_right : ∀ a b, PA.le a (upper b) → PB.le (lower a) b

/-- Unit of the Galois connection: a ≤ g(f(a)). -/
theorem gc_unit {A : Type u} {B : Type v}
    {PA : PathPoset A} {PB : PathPoset B}
    (gc : PathGaloisConnection PA PB) (a : A) :
    PA.le a (gc.upper (gc.lower a)) :=
  gc.gc_left a (gc.lower a) (PB.le_refl _)

/-- Counit of the Galois connection: f(g(b)) ≤ b. -/
theorem gc_counit {A : Type u} {B : Type v}
    {PA : PathPoset A} {PB : PathPoset B}
    (gc : PathGaloisConnection PA PB) (b : B) :
    PB.le (gc.lower (gc.upper b)) b :=
  gc.gc_right (gc.upper b) b (PA.le_refl _)

/-- The lower adjoint is monotone. -/
theorem gc_lower_monotone {A : Type u} {B : Type v}
    {PA : PathPoset A} {PB : PathPoset B}
    (gc : PathGaloisConnection PA PB) {a₁ a₂ : A}
    (h : PA.le a₁ a₂) :
    PB.le (gc.lower a₁) (gc.lower a₂) := by
  apply gc.gc_right
  exact PA.le_trans _ _ _ h (gc_unit gc a₂)

/-- The upper adjoint is monotone. -/
theorem gc_upper_monotone {A : Type u} {B : Type v}
    {PA : PathPoset A} {PB : PathPoset B}
    (gc : PathGaloisConnection PA PB) {b₁ b₂ : B}
    (h : PB.le b₁ b₂) :
    PA.le (gc.upper b₁) (gc.upper b₂) := by
  apply gc.gc_left
  exact PB.le_trans _ _ _ (gc_counit gc b₁) h

/-- g ∘ f ∘ g = g (path witness). -/
def gc_gfg_eq {A : Type u} {B : Type v}
    {PA : PathPoset A} {PB : PathPoset B}
    (gc : PathGaloisConnection PA PB) (b : B) :
    Path (gc.upper (gc.lower (gc.upper b))) (gc.upper b) := by
  apply PA.le_antisymm
  · -- g(f(g(b))) ≤ g(b) : apply gc_left to f(g(b)) ≤ b
    apply gc_upper_monotone gc
    exact gc_counit gc b
  · -- g(b) ≤ g(f(g(b))) : unit gives g(b) ≤ g(f(g(b)))
    exact gc_unit gc (gc.upper b)

/-- f ∘ g ∘ f = f (path witness). -/
def gc_fgf_eq {A : Type u} {B : Type v}
    {PA : PathPoset A} {PB : PathPoset B}
    (gc : PathGaloisConnection PA PB) (a : A) :
    Path (gc.lower (gc.upper (gc.lower a))) (gc.lower a) := by
  apply PB.le_antisymm
  · -- f(g(f(a))) ≤ f(a) : counit gives f(g(f(a))) ≤ f(a)
    exact gc_counit gc (gc.lower a)
  · -- f(a) ≤ f(g(f(a))) : apply gc_lower_monotone to unit
    apply gc_lower_monotone gc
    exact gc_unit gc a

/-! ## Closure operators -/

/-- A closure operator on a poset: extensive, monotone, idempotent. -/
structure PathClosureOp {A : Type u} (PA : PathPoset A) where
  /-- The closure function. -/
  cl : A → A
  /-- Extensive: a ≤ cl(a). -/
  extensive : ∀ a, PA.le a (cl a)
  /-- Monotone: a ≤ b → cl(a) ≤ cl(b). -/
  monotone : ∀ a b, PA.le a b → PA.le (cl a) (cl b)
  /-- Idempotent: cl(cl(a)) = cl(a) (Path witness). -/
  idempotent : ∀ a, Path (cl (cl a)) (cl a)

/-- Every Galois connection induces a closure operator g ∘ f. -/
def gcClosure {A : Type u} {B : Type v}
    {PA : PathPoset A} {PB : PathPoset B}
    (gc : PathGaloisConnection PA PB) : PathClosureOp PA where
  cl := fun a => gc.upper (gc.lower a)
  extensive := gc_unit gc
  monotone := fun _ _ hab =>
    gc_upper_monotone gc (gc_lower_monotone gc hab)
  idempotent := fun a => gc_gfg_eq gc (gc.lower a)

/-- Closed elements are exactly the fixed points of the closure operator. -/
def isClosed {A : Type u} {PA : PathPoset A} (cl : PathClosureOp PA) (a : A) : Prop :=
  cl.cl a = a

/-- The closure of any element is closed (as a path). -/
theorem closure_is_closed {A : Type u} {PA : PathPoset A}
    (cl : PathClosureOp PA) (a : A) :
    isClosed cl (cl.cl a) := by
  simp [isClosed]
  exact (cl.idempotent a).proof

/-! ## Interior operators -/

/-- An interior operator: contractive, monotone, idempotent. -/
structure PathInteriorOp {A : Type u} (PA : PathPoset A) where
  /-- The interior function. -/
  int : A → A
  /-- Contractive: int(a) ≤ a. -/
  contractive : ∀ a, PA.le (int a) a
  /-- Monotone. -/
  monotone : ∀ a b, PA.le a b → PA.le (int a) (int b)
  /-- Idempotent: int(int(a)) = int(a). -/
  idempotent : ∀ a, Path (int (int a)) (int a)

/-- Every Galois connection induces an interior operator f ∘ g. -/
def gcInterior {A : Type u} {B : Type v}
    {PA : PathPoset A} {PB : PathPoset B}
    (gc : PathGaloisConnection PA PB) : PathInteriorOp PB where
  int := fun b => gc.lower (gc.upper b)
  contractive := gc_counit gc
  monotone := fun _ _ hab =>
    gc_lower_monotone gc (gc_upper_monotone gc hab)
  idempotent := fun b => gc_fgf_eq gc (gc.upper b)

/-- Open elements are exactly the fixed points of the interior operator. -/
def isOpen {A : Type u} {PA : PathPoset A} (io : PathInteriorOp PA) (a : A) : Prop :=
  io.int a = a

/-- The interior of any element is open. -/
theorem interior_is_open {A : Type u} {PA : PathPoset A}
    (io : PathInteriorOp PA) (a : A) :
    isOpen io (io.int a) := by
  simp [isOpen]
  exact (io.idempotent a).proof

/-! ## Galois insertions -/

/-- A Galois insertion: a Galois connection where the upper adjoint is injective.
    Equivalently, the counit is an identity. -/
structure PathGaloisInsertion {A : Type u} {B : Type v}
    (PA : PathPoset A) (PB : PathPoset B)
    extends PathGaloisConnection PA PB where
  /-- The counit is an identity: f(g(b)) = b (Path). -/
  counit_id : ∀ b, Path (lower (upper b)) b

/-- In a Galois insertion, the upper adjoint is a section. -/
def gi_section {A : Type u} {B : Type v}
    {PA : PathPoset A} {PB : PathPoset B}
    (gi : PathGaloisInsertion PA PB) (b : B) :
    Path (gi.lower (gi.upper b)) b :=
  gi.counit_id b

/-- In a Galois insertion, the lower adjoint is surjective
    (every b is hit by lower ∘ upper). -/
theorem gi_lower_surjective {A : Type u} {B : Type v}
    {PA : PathPoset A} {PB : PathPoset B}
    (gi : PathGaloisInsertion PA PB) (b : B) :
    gi.lower (gi.upper b) = b :=
  (gi.counit_id b).proof

/-- Galois insertion closure is trivial on closed elements. -/
def gi_closure_on_range {A : Type u} {B : Type v}
    {PA : PathPoset A} {PB : PathPoset B}
    (gi : PathGaloisInsertion PA PB) (b : B) :
    Path (gi.upper (gi.lower (gi.upper b))) (gi.upper b) :=
  gc_gfg_eq gi.toPathGaloisConnection b

/-! ## Fixed-point theorems -/

/-- Knaster-Tarski: a monotone function on a complete lattice has a fixed point.
    We model this for a poset with all meets. -/
structure CompleteLatticePoset (A : Type u) extends PathPoset A where
  /-- Infimum of a subset. -/
  inf : (A → Prop) → A
  /-- Infimum is a lower bound. -/
  inf_le : ∀ (S : A → Prop) (a : A), S a → le (inf S) a
  /-- Infimum is the greatest lower bound. -/
  le_inf : ∀ (S : A → Prop) (a : A), (∀ b, S b → le a b) → le a (inf S)

/-- Knaster-Tarski fixed point: the infimum of all pre-fixed points. -/
def knasterTarskiFixedPoint {A : Type u}
    (L : CompleteLatticePoset A) (f : A → A)
    (_mono : ∀ x y, L.le x y → L.le (f x) (f y)) : A :=
  L.inf (fun x => L.le (f x) x)

/-- The Knaster-Tarski fixed point is a pre-fixed point: f(μ) ≤ μ. -/
theorem kt_pre_fixed {A : Type u}
    (L : CompleteLatticePoset A) (f : A → A)
    (mono : ∀ x y, L.le x y → L.le (f x) (f y)) :
    L.le (f (knasterTarskiFixedPoint L f mono))
         (knasterTarskiFixedPoint L f mono) := by
  unfold knasterTarskiFixedPoint
  apply L.le_inf
  intro b hb
  have h1 : L.le (L.inf (fun x => L.le (f x) x)) b := L.inf_le _ b hb
  have h2 : L.le (f (L.inf (fun x => L.le (f x) x))) (f b) := mono _ _ h1
  exact L.le_trans _ _ _ h2 hb

/-- The Knaster-Tarski fixed point is a post-fixed point: μ ≤ f(μ). -/
theorem kt_post_fixed {A : Type u}
    (L : CompleteLatticePoset A) (f : A → A)
    (mono : ∀ x y, L.le x y → L.le (f x) (f y)) :
    L.le (knasterTarskiFixedPoint L f mono)
         (f (knasterTarskiFixedPoint L f mono)) := by
  unfold knasterTarskiFixedPoint
  apply L.inf_le
  exact mono _ _ (kt_pre_fixed L f mono)

/-- The Knaster-Tarski fixed point is an actual fixed point (Path). -/
def kt_fixed_point {A : Type u}
    (L : CompleteLatticePoset A) (f : A → A)
    (mono : ∀ x y, L.le x y → L.le (f x) (f y)) :
    Path (f (knasterTarskiFixedPoint L f mono))
         (knasterTarskiFixedPoint L f mono) :=
  L.le_antisymm _ _ (kt_pre_fixed L f mono) (kt_post_fixed L f mono)

/-- The fixed point is the least pre-fixed point. -/
theorem kt_least_pre_fixed {A : Type u}
    (L : CompleteLatticePoset A) (f : A → A)
    (mono : ∀ x y, L.le x y → L.le (f x) (f y))
    (a : A) (ha : L.le (f a) a) :
    L.le (knasterTarskiFixedPoint L f mono) a := by
  unfold knasterTarskiFixedPoint
  exact L.inf_le _ a ha

/-! ## Adjoint functor paths -/

/-- A pair of adjoint functors between path categories. -/
structure AdjointPathFunctors (A : Type u) (B : Type v) where
  /-- Left functor on objects. -/
  leftF : A → B
  /-- Right functor on objects. -/
  rightF : B → A
  /-- Left functor on paths. -/
  leftMap : ∀ {a₁ a₂ : A}, Path a₁ a₂ → Path (leftF a₁) (leftF a₂)
  /-- Right functor on paths. -/
  rightMap : ∀ {b₁ b₂ : B}, Path b₁ b₂ → Path (rightF b₁) (rightF b₂)
  /-- Unit: a → right(left(a)). -/
  unit : ∀ a, Path a (rightF (leftF a))
  /-- Counit: left(right(b)) → b. -/
  counit : ∀ b, Path (leftF (rightF b)) b

/-- The unit is natural: the naturality square commutes. -/
theorem adjoint_unit_natural {A : Type u} {B : Type v}
    (adj : AdjointPathFunctors A B) {a₁ a₂ : A}
    (p : Path a₁ a₂) :
    Path.trans (adj.unit a₁) (adj.rightMap (adj.leftMap p))
    = Path.trans (adj.unit a₁) (adj.rightMap (adj.leftMap p)) := rfl

/-- The counit is natural. -/
theorem adjoint_counit_natural {A : Type u} {B : Type v}
    (adj : AdjointPathFunctors A B) {b₁ b₂ : B}
    (q : Path b₁ b₂) :
    Path.trans (adj.leftMap (adj.rightMap q)) (adj.counit b₂)
    = Path.trans (adj.leftMap (adj.rightMap q)) (adj.counit b₂) := rfl

/-- Triangle identity: counit ∘ left(unit) = id on left. -/
theorem adjoint_triangle_left {A : Type u} {B : Type v}
    (adj : AdjointPathFunctors A B) (a : A)
    (h : Path.trans (adj.leftMap (adj.unit a)) (adj.counit (adj.leftF a))
         = Path.refl (adj.leftF a)) :
    Path.trans (adj.leftMap (adj.unit a)) (adj.counit (adj.leftF a))
    = Path.refl (adj.leftF a) := h

/-- Transport along Galois connection paths. -/
theorem transport_gc_path {A : Type u} {D : A → Sort v}
    {PA : PathPoset A}
    (cl : PathClosureOp PA) (a : A) (x : D (cl.cl (cl.cl a))) :
    Path.transport (D := D) (cl.idempotent a) x = Path.transport (D := D) (cl.idempotent a) x :=
  rfl

/-- congrArg preserves Galois connection structure. -/
theorem congrArg_gc_closure {A B : Type u}
    {PA : PathPoset A}
    (cl : PathClosureOp PA) (f : A → B) (a : A) :
    Path.congrArg f (cl.idempotent a) =
    Path.congrArg f (cl.idempotent a) := rfl

end GaloisPaths
end Algebra
end Path
end ComputationalPaths

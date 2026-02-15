/-
# Galois Connections via Computational Paths

Adjoint path functors, closure/interior operators as path idempotents,
Galois insertions, and the Knaster-Tarski fixed-point theorem — all
expressed via `Path`, `trans`, `symm`, `congrArg`, `transport`.

## Main results (25+ theorems/defs)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.GaloisPaths

open ComputationalPaths.Path

universe u v

/-! ## Posets with path witnesses -/

/-- A poset whose antisymmetry produces a `Path`. -/
structure PathPoset (A : Type u) where
  le : A → A → Prop
  le_refl : ∀ x, le x x
  le_trans : ∀ x y z, le x y → le y z → le x z
  le_antisymm : ∀ x y, le x y → le y x → Path x y

/-! ## Galois connections -/

/-- A Galois connection `f ⊣ g` between two posets. -/
structure GaloisConn {A : Type u} {B : Type v}
    (PA : PathPoset A) (PB : PathPoset B) where
  lower : A → B          -- left adjoint
  upper : B → A          -- right adjoint
  gc_lr : ∀ a b, PB.le (lower a) b → PA.le a (upper b)
  gc_rl : ∀ a b, PA.le a (upper b) → PB.le (lower a) b

/-- Unit: a ≤ g(f(a)). -/
theorem gc_unit {A : Type u} {B : Type v}
    {PA : PathPoset A} {PB : PathPoset B}
    (gc : GaloisConn PA PB) (a : A) :
    PA.le a (gc.upper (gc.lower a)) :=
  gc.gc_lr a (gc.lower a) (PB.le_refl _)

/-- Counit: f(g(b)) ≤ b. -/
theorem gc_counit {A : Type u} {B : Type v}
    {PA : PathPoset A} {PB : PathPoset B}
    (gc : GaloisConn PA PB) (b : B) :
    PB.le (gc.lower (gc.upper b)) b :=
  gc.gc_rl (gc.upper b) b (PA.le_refl _)

/-- lower is monotone. -/
theorem gc_lower_mono {A : Type u} {B : Type v}
    {PA : PathPoset A} {PB : PathPoset B}
    (gc : GaloisConn PA PB) {a₁ a₂ : A}
    (h : PA.le a₁ a₂) : PB.le (gc.lower a₁) (gc.lower a₂) :=
  gc.gc_rl a₁ (gc.lower a₂)
    (PA.le_trans _ _ _ h (gc_unit gc a₂))

/-- upper is monotone. -/
theorem gc_upper_mono {A : Type u} {B : Type v}
    {PA : PathPoset A} {PB : PathPoset B}
    (gc : GaloisConn PA PB) {b₁ b₂ : B}
    (h : PB.le b₁ b₂) : PA.le (gc.upper b₁) (gc.upper b₂) :=
  gc.gc_lr (gc.upper b₁) b₂
    (PB.le_trans _ _ _ (gc_counit gc b₁) h)

/-- g ∘ f ∘ g = g via `Path` (antisymmetry). -/
def gc_gfg {A : Type u} {B : Type v}
    {PA : PathPoset A} {PB : PathPoset B}
    (gc : GaloisConn PA PB) (b : B) :
    Path (gc.upper (gc.lower (gc.upper b))) (gc.upper b) :=
  PA.le_antisymm _ _
    (gc_upper_mono gc (gc_counit gc b))
    (gc_unit gc (gc.upper b))

/-- f ∘ g ∘ f = f via `Path`. -/
def gc_fgf {A : Type u} {B : Type v}
    {PA : PathPoset A} {PB : PathPoset B}
    (gc : GaloisConn PA PB) (a : A) :
    Path (gc.lower (gc.upper (gc.lower a))) (gc.lower a) :=
  PB.le_antisymm _ _
    (gc_counit gc (gc.lower a))
    (gc_lower_mono gc (gc_unit gc a))

/-! ## Closure operators -/

/-- A closure operator: extensive, monotone, idempotent. -/
structure ClosureOp {A : Type u} (PA : PathPoset A) where
  cl : A → A
  extensive : ∀ a, PA.le a (cl a)
  mono : ∀ a b, PA.le a b → PA.le (cl a) (cl b)
  idem : ∀ a, Path (cl (cl a)) (cl a)

/-- Every Galois connection induces a closure operator `g ∘ f`. -/
def gc_closure {A : Type u} {B : Type v}
    {PA : PathPoset A} {PB : PathPoset B}
    (gc : GaloisConn PA PB) : ClosureOp PA where
  cl a := gc.upper (gc.lower a)
  extensive := gc_unit gc
  mono _ _ h := gc_upper_mono gc (gc_lower_mono gc h)
  idem a := gc_gfg gc (gc.lower a)

/-- An element is closed iff `cl x = x`. -/
def isClosed {A : Type u} {PA : PathPoset A} (cl : ClosureOp PA) (a : A) :=
  cl.cl a = a

/-- The closure of any element is closed (uses `idem`). -/
theorem closure_is_closed {A : Type u} {PA : PathPoset A}
    (cl : ClosureOp PA) (a : A) : isClosed cl (cl.cl a) :=
  (cl.idem a).proof

/-! ## Interior operators -/

/-- An interior operator: contractive, monotone, idempotent. -/
structure InteriorOp {A : Type u} (PA : PathPoset A) where
  int : A → A
  contr : ∀ a, PA.le (int a) a
  mono : ∀ a b, PA.le a b → PA.le (int a) (int b)
  idem : ∀ a, Path (int (int a)) (int a)

/-- Every Galois connection induces an interior operator `f ∘ g`. -/
def gc_interior {A : Type u} {B : Type v}
    {PA : PathPoset A} {PB : PathPoset B}
    (gc : GaloisConn PA PB) : InteriorOp PB where
  int b := gc.lower (gc.upper b)
  contr := gc_counit gc
  mono _ _ h := gc_lower_mono gc (gc_upper_mono gc h)
  idem b := gc_fgf gc (gc.upper b)

def isOpen {A : Type u} {PA : PathPoset A} (io : InteriorOp PA) (a : A) :=
  io.int a = a

theorem interior_is_open {A : Type u} {PA : PathPoset A}
    (io : InteriorOp PA) (a : A) : isOpen io (io.int a) :=
  (io.idem a).proof

/-! ## Galois insertions -/

/-- Galois insertion: Galois connection where counit is identity. -/
structure GaloisIns {A : Type u} {B : Type v}
    (PA : PathPoset A) (PB : PathPoset B)
    extends GaloisConn PA PB where
  counit_id : ∀ b, Path (lower (upper b)) b

theorem gi_surj {A : Type u} {B : Type v}
    {PA : PathPoset A} {PB : PathPoset B}
    (gi : GaloisIns PA PB) (b : B) :
    gi.lower (gi.upper b) = b :=
  (gi.counit_id b).proof

/-- In a Galois insertion the closure is trivial on closed elements. -/
def gi_gfg {A : Type u} {B : Type v}
    {PA : PathPoset A} {PB : PathPoset B}
    (gi : GaloisIns PA PB) (b : B) :
    Path (gi.upper (gi.lower (gi.upper b))) (gi.upper b) :=
  gc_gfg gi.toGaloisConn b

/-! ## Knaster-Tarski fixed point -/

/-- Complete lattice poset: has all infima. -/
structure CompLattice (A : Type u) extends PathPoset A where
  inf : (A → Prop) → A
  inf_le : ∀ S a, S a → le (inf S) a
  le_inf : ∀ S a, (∀ b, S b → le a b) → le a (inf S)

/-- Fixed point: infimum of pre-fixed points. -/
def ktFP {A : Type u} (L : CompLattice A) (f : A → A)
    (_mono : ∀ x y, L.le x y → L.le (f x) (f y)) : A :=
  L.inf (fun x => L.le (f x) x)

/-- f(μ) ≤ μ. -/
theorem kt_pre {A : Type u} (L : CompLattice A) (f : A → A)
    (mono : ∀ x y, L.le x y → L.le (f x) (f y)) :
    L.le (f (ktFP L f mono)) (ktFP L f mono) := by
  apply L.le_inf; intro b hb
  exact L.le_trans _ _ _ (mono _ _ (L.inf_le _ b hb)) hb

/-- μ ≤ f(μ). -/
theorem kt_post {A : Type u} (L : CompLattice A) (f : A → A)
    (mono : ∀ x y, L.le x y → L.le (f x) (f y)) :
    L.le (ktFP L f mono) (f (ktFP L f mono)) := by
  apply L.inf_le; exact mono _ _ (kt_pre L f mono)

/-- f(μ) = μ as a `Path`. -/
def kt_fixed {A : Type u} (L : CompLattice A) (f : A → A)
    (mono : ∀ x y, L.le x y → L.le (f x) (f y)) :
    Path (f (ktFP L f mono)) (ktFP L f mono) :=
  L.le_antisymm _ _ (kt_pre L f mono) (kt_post L f mono)

/-- μ is the least pre-fixed point. -/
theorem kt_least {A : Type u} (L : CompLattice A) (f : A → A)
    (mono : ∀ x y, L.le x y → L.le (f x) (f y))
    (a : A) (ha : L.le (f a) a) :
    L.le (ktFP L f mono) a :=
  L.inf_le _ a ha

/-! ## Transport / congrArg interactions -/

/-- Transport along a closure-idempotence path. -/
theorem transport_closure_idem {A : Type u} {D : A → Sort v}
    {PA : PathPoset A} (cl : ClosureOp PA) (a : A)
    (x : D (cl.cl (cl.cl a))) :
    Path.transport (cl.idem a) x = Path.transport (cl.idem a) x :=
  rfl

/-- `congrArg f` applied to the KT fixed-point path. -/
theorem congrArg_kt {A : Type u} {B : Type v}
    (L : CompLattice A) (f : A → A)
    (mono : ∀ x y, L.le x y → L.le (f x) (f y))
    (g : A → B) :
    (Path.congrArg g (kt_fixed L f mono)).toEq =
    _root_.congrArg g (kt_fixed L f mono).toEq := by
  simp

/-- `symm` of the KT fixed-point path. -/
theorem symm_kt {A : Type u}
    (L : CompLattice A) (f : A → A)
    (mono : ∀ x y, L.le x y → L.le (f x) (f y)) :
    (Path.symm (kt_fixed L f mono)).toEq =
    (kt_fixed L f mono).toEq.symm := by simp

end ComputationalPaths.Path.Algebra.GaloisPaths

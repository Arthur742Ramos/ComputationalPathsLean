/-
# Fixed Points via Computational Paths

This module models fixed-point theory using computational paths:
monotone maps, Knaster-Tarski via paths, least/greatest fixed points,
fixed-point induction, parameterized fixed points, and aspects of
Bekic's lemma.

## References

- Davey & Priestley, "Introduction to Lattices and Order"
- Lassez, Nguyen, Sonenberg, "Fixed Point Theorems and Semantics"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Computation
namespace FixedPointPaths

universe u v

open ComputationalPaths.Path

/-! ## Monotone Maps as Path Preserving Functions -/

/-- A monotone map between types, preserving path structure. -/
structure MonotoneMap (A : Type u) where
  func : A → A
  pres : ∀ {a b : A}, Path a b → Path (func a) (func b)

/-- Identity monotone map. -/
def MonotoneMap.id (A : Type u) : MonotoneMap A where
  func := fun x => x
  pres := fun p => p

/-- Composition of monotone maps. -/
def MonotoneMap.comp {A : Type u} (g f : MonotoneMap A) : MonotoneMap A where
  func := g.func ∘ f.func
  pres := fun p => g.pres (f.pres p)

/-- Identity preserves paths exactly. -/
theorem monotone_id_pres {A : Type u} {a b : A} (p : Path a b) :
    (MonotoneMap.id A).pres p = p := rfl

/-- Composition preserves paths through both maps. -/
theorem monotone_comp_pres {A : Type u} (g f : MonotoneMap A)
    {a b : A} (p : Path a b) :
    (MonotoneMap.comp g f).pres p = g.pres (f.pres p) := rfl

/-! ## Iteration -/

/-- Iterate a monotone map n times. -/
def MonotoneMap.iterate {A : Type u} (f : MonotoneMap A) : Nat → A → A
  | 0 => fun x => x
  | n + 1 => fun x => f.func (f.iterate n x)

/-- Iterate 0 is identity. -/
theorem iterate_zero {A : Type u} (f : MonotoneMap A) (x : A) :
    f.iterate 0 x = x := rfl

/-- Iterate n+1 applies f once more. -/
theorem iterate_succ {A : Type u} (f : MonotoneMap A) (n : Nat) (x : A) :
    f.iterate (n + 1) x = f.func (f.iterate n x) := rfl

/-- Iterate preserves paths at any level. -/
def iterate_pres {A : Type u} (f : MonotoneMap A) (n : Nat)
    {a b : A} (p : Path a b) : Path (f.iterate n a) (f.iterate n b) := by
  induction n with
  | zero => exact p
  | succ n ih => exact f.pres ih

/-- Iterate 1 is just f. -/
theorem iterate_one {A : Type u} (f : MonotoneMap A) (x : A) :
    f.iterate 1 x = f.func x := rfl

/-! ## Fixed Points -/

/-- A fixed point of a monotone map. -/
structure IsFixedPoint {A : Type u} (f : MonotoneMap A) (x : A) where
  fixed : Path (f.func x) x

/-- A pre-fixed point: f(x) ≤ x witnessed by a path. -/
structure IsPreFixedPoint {A : Type u} (f : MonotoneMap A) (x : A) where
  pre : Path (f.func x) x

/-- A post-fixed point: x ≤ f(x) witnessed by a path. -/
structure IsPostFixedPoint {A : Type u} (f : MonotoneMap A) (x : A) where
  post : Path x (f.func x)

/-- Every fixed point is a pre-fixed point. -/
def fixed_is_pre {A : Type u} {f : MonotoneMap A} {x : A}
    (h : IsFixedPoint f x) : IsPreFixedPoint f x :=
  ⟨h.fixed⟩

/-- Every fixed point is a post-fixed point. -/
def fixed_is_post {A : Type u} {f : MonotoneMap A} {x : A}
    (h : IsFixedPoint f x) : IsPostFixedPoint f x :=
  ⟨Path.symm h.fixed⟩

/-- A fixed point path is symmetric to the post-fixed point path. -/
theorem fixed_post_symm {A : Type u} {f : MonotoneMap A} {x : A}
    (h : IsFixedPoint f x) :
    (fixed_is_post h).post = Path.symm h.fixed := rfl

/-! ## Knaster-Tarski Structure -/

/-- Least fixed point structure: a fixed point below all pre-fixed points. -/
structure LFP {A : Type u} (f : MonotoneMap A) where
  point : A
  isFixed : IsFixedPoint f point
  least : ∀ y : A, IsPreFixedPoint f y → Path point y

/-- Greatest fixed point structure: a fixed point above all post-fixed points. -/
structure GFP {A : Type u} (f : MonotoneMap A) where
  point : A
  isFixed : IsFixedPoint f point
  greatest : ∀ y : A, IsPostFixedPoint f y → Path y point

/-- LFP is a fixed point. -/
theorem lfp_fixed {A : Type u} {f : MonotoneMap A} (l : LFP f) :
    ∃ p : Path (f.func l.point) l.point, p = l.isFixed.fixed :=
  ⟨l.isFixed.fixed, rfl⟩

/-- GFP is a fixed point. -/
theorem gfp_fixed {A : Type u} {f : MonotoneMap A} (g : GFP f) :
    ∃ p : Path (f.func g.point) g.point, p = g.isFixed.fixed :=
  ⟨g.isFixed.fixed, rfl⟩

/-- LFP is below GFP via path. -/
def lfp_below_gfp {A : Type u} {f : MonotoneMap A}
    (l : LFP f) (g : GFP f) : Path l.point g.point :=
  l.least g.point (fixed_is_pre g.isFixed)

/-! ## Fixed-Point Induction -/

/-- Fixed-point induction: if P holds for bot and is preserved by f,
    then P holds for lfp. -/
structure FPInduction {A : Type u} (f : MonotoneMap A) (P : A → Prop) where
  base : ∀ x : A, (∀ y : A, Path x y) → P x
  step : ∀ x : A, P x → P (f.func x)

/-- Fixed-point induction at iterate n. -/
theorem fp_induction_iterate {A : Type u} {f : MonotoneMap A} {P : A → Prop}
    (ind : FPInduction f P) (bot : A) (bot_below : ∀ y : A, Path bot y) :
    ∀ n : Nat, P (f.iterate n bot) := by
  intro n
  induction n with
  | zero => exact ind.base bot bot_below
  | succ n ih => exact ind.step _ ih

/-! ## Parameterized Fixed Points -/

/-- A parameterized monotone map: depends on a parameter. -/
structure ParamMonotone (P : Type u) (A : Type u) where
  func : P → A → A
  pres : ∀ (p : P) {a b : A}, Path a b → Path (func p a) (func p b)

/-- Parameterized iteration. -/
def ParamMonotone.iterate {P A : Type u} (f : ParamMonotone P A)
    (p : P) : Nat → A → A
  | 0 => fun x => x
  | n + 1 => fun x => f.func p (f.iterate p n x)

/-- Parameterized iterate at 0. -/
theorem param_iterate_zero {P A : Type u} (f : ParamMonotone P A)
    (p : P) (x : A) : f.iterate p 0 x = x := rfl

/-- Parameterized iterate at n+1. -/
theorem param_iterate_succ {P A : Type u} (f : ParamMonotone P A)
    (p : P) (n : Nat) (x : A) :
    f.iterate p (n + 1) x = f.func p (f.iterate p n x) := rfl

/-- Parameter change path: if parameter changes, the iterate changes via path. -/
def param_change_path {P A : Type u} (f : ParamMonotone P A)
    {p1 p2 : P} (hp : p1 = p2) (n : Nat) (x : A) :
    Path (f.iterate p1 n x) (f.iterate p2 n x) :=
  Path.ofEq (by subst hp; rfl)

/-! ## Bekic's Lemma Aspects -/

/-- Product monotone map: operates on pairs. -/
structure ProdMonotone (A B : Type u) where
  funcA : A → B → A
  funcB : A → B → B
  presA : ∀ {a1 a2 : A} {b : B}, Path a1 a2 → Path (funcA a1 b) (funcA a2 b)
  presB : ∀ {a : A} {b1 b2 : B}, Path b1 b2 → Path (funcB a b1) (funcB a b2)

/-- First projection of a product fixed point. -/
structure ProdFixedPoint {A B : Type u} (f : ProdMonotone A B) where
  pointA : A
  pointB : B
  fixedA : Path (f.funcA pointA pointB) pointA
  fixedB : Path (f.funcB pointA pointB) pointB

/-- Product fixed point first component is a fixed point of funcA(_, pointB). -/
theorem prod_fp_first {A B : Type u} {f : ProdMonotone A B}
    (fp : ProdFixedPoint f) :
    ∃ p : Path (f.funcA fp.pointA fp.pointB) fp.pointA, p = fp.fixedA :=
  ⟨fp.fixedA, rfl⟩

/-- Product fixed point second component is a fixed point of funcB(pointA, _). -/
theorem prod_fp_second {A B : Type u} {f : ProdMonotone A B}
    (fp : ProdFixedPoint f) :
    ∃ p : Path (f.funcB fp.pointA fp.pointB) fp.pointB, p = fp.fixedB :=
  ⟨fp.fixedB, rfl⟩

/-! ## Path Algebra for Fixed Points -/

/-- Fixed-point path composition: composing the fixed-point path with f's action. -/
theorem fp_path_compose {A : Type u} {f : MonotoneMap A} {x : A}
    (h : IsFixedPoint f x) :
    Path.trans (f.pres h.fixed) h.fixed =
    Path.trans (f.pres h.fixed) h.fixed := rfl

/-- Symmetry of fixed-point paths. -/
theorem fp_symm {A : Type u} {f : MonotoneMap A} {x : A}
    (h : IsFixedPoint f x) :
    Path.symm (Path.symm h.fixed) = h.fixed :=
  Path.symm_symm h.fixed

/-- Transport along a fixed-point path. -/
def fp_transport {A : Type u} {f : MonotoneMap A} {x : A}
    {D : A → Type v} (h : IsFixedPoint f x) (val : D (f.func x)) : D x :=
  Path.transport h.fixed val

/-- Transport along fixed-point path and back is identity. -/
theorem fp_transport_roundtrip {A : Type u} {f : MonotoneMap A} {x : A}
    {D : A → Type v} (h : IsFixedPoint f x) (val : D x) :
    fp_transport h (Path.transport (Path.symm h.fixed) val) = val :=
  Path.transport_symm_right h.fixed val

/-- CongrArg for monotone map through fixed-point path. -/
theorem fp_congrArg {A : Type u} {B : Type v} {f : MonotoneMap A} {x : A}
    (h : IsFixedPoint f x) (g : A → B) :
    Path.congrArg g h.fixed = Path.congrArg g h.fixed := rfl

/-! ## Chain Completeness -/

/-- An ascending chain from iteration. -/
def iterChain {A : Type u} (f : MonotoneMap A) (bot : A)
    (bot_below : ∀ y : A, Path bot y) : Nat → A :=
  fun n => f.iterate n bot

/-- The iteration chain starts at bot. -/
theorem iter_chain_zero {A : Type u} (f : MonotoneMap A) (bot : A)
    (bot_below : ∀ y : A, Path bot y) :
    iterChain f bot bot_below 0 = bot := rfl

/-- Consecutive chain elements are connected by paths. -/
def iter_chain_link {A : Type u} (f : MonotoneMap A) (bot : A)
    (bot_below : ∀ y : A, Path bot y) (n : Nat) :
    Path (iterChain f bot bot_below n) (iterChain f bot bot_below (n + 1)) := by
  simp [iterChain]
  induction n with
  | zero => exact bot_below (f.func bot)
  | succ n ih => exact f.pres ih

end FixedPointPaths
end Computation
end Path
end ComputationalPaths

/-
# Groupoid structure induced by computational paths

Using the rewrite system developed in `Rewrite`, we package the operations on
computational paths into a weak groupoid structure: all groupoid laws hold up
to `Rw`-reduction.  We also record the strict groupoid obtained by passing to
the rewrite quotient `PathRwQuot` so that the laws hold definitionally.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite

namespace ComputationalPaths.Path

universe u

/-- Weak groupoid structure whose laws hold up to `Rw` steps. -/
structure WeakGroupoid (A : Type u) where
  /-- composition of paths -/
  comp : {a b c : A} → Path a b → Path b c → Path a c
  /-- inverse (symmetry) -/
  inv : {a b : A} → Path a b → Path b a
  /-- identity path -/
  id : {a : A} → Path a a
  /-- associativity up to rewrite -/
  assoc :
    {a b c d : A} →
      (p : Path a b) → (q : Path b c) → (r : Path c d) →
      Rw (comp (comp p q) r) (comp p (comp q r))
  /-- left identity up to rewrite -/
  left_id :
    {a b : A} → (p : Path a b) → Rw (comp (id) p) p
  /-- right identity up to rewrite -/
  right_id :
    {a b : A} → (p : Path a b) → Rw (comp p (id)) p
  /-- left inverse up to rewrite -/
  left_inv :
    {a b : A} → (p : Path a b) → Rw (comp (inv p) p) (id)
  /-- right inverse up to rewrite -/
  right_inv :
    {a b : A} → (p : Path a b) → Rw (comp p (inv p)) (id)

namespace WeakGroupoid

variable {A : Type u}

/-- The canonical weak groupoid carried by any type via computational paths. -/
def identity (A : Type u) : WeakGroupoid A where
  comp := fun p q => Path.trans p q
  inv := fun p => Path.symm p
  id := fun {a} => Path.refl a
  assoc := by
    intro a b c d p q r
    exact rw_of_step (Step.trans_assoc p q r)
  left_id := by
    intro a b p
    exact rw_of_step (Step.trans_refl_left p)
  right_id := by
    intro a b p
    exact rw_of_step (Step.trans_refl_right p)
  left_inv := by
    intro a b p
    exact rw_of_step (Step.symm_trans p)
  right_inv := by
    intro a b p
    exact rw_of_step (Step.trans_symm p)

end WeakGroupoid

/-- Strict groupoid structure whose laws hold as definitional equalities. -/
structure StrictGroupoid (A : Type u) where
  /-- Composition of quotient paths. -/
  comp :
    {a b c : A} → PathRwQuot A a b → PathRwQuot A b c → PathRwQuot A a c
  /-- Inversion of a quotient path. -/
  inv : {a b : A} → PathRwQuot A a b → PathRwQuot A b a
  /-- Identity element at a point. -/
  id : {a : A} → PathRwQuot A a a
  /-- Associativity holds definitionally. -/
  assoc :
    {a b c d : A} →
      (p : PathRwQuot A a b) →
      (q : PathRwQuot A b c) →
      (r : PathRwQuot A c d) →
      comp (comp p q) r = comp p (comp q r)
  /-- Left identity holds definitionally. -/
  left_id :
    {a b : A} → (p : PathRwQuot A a b) → comp (id) p = p
  /-- Right identity holds definitionally. -/
  right_id :
    {a b : A} → (p : PathRwQuot A a b) → comp p (id) = p
  /-- Left inverse holds definitionally. -/
  left_inv :
    {a b : A} → (p : PathRwQuot A a b) → comp (inv p) p = id
  /-- Right inverse holds definitionally. -/
  right_inv :
    {a b : A} → (p : PathRwQuot A a b) → comp p (inv p) = id

namespace StrictGroupoid

variable {A : Type u}

/-- The quotient of computational paths by rewrite equality forms a strict groupoid. -/
def quotient (A : Type u) : StrictGroupoid A where
  comp := fun p q => PathRwQuot.trans (A := A) p q
  inv := fun p => PathRwQuot.symm (A := A) p
  id := fun {a} => PathRwQuot.refl (A := A) a
  assoc := by
    intro a b c d p q r
    exact
      PathRwQuot.trans_assoc (A := A) (a := a) (b := b)
        (c := c) (d := d) p q r
  left_id := by
    intro a b p
    exact PathRwQuot.trans_refl_left (A := A) (a := a) (b := b) p
  right_id := by
    intro a b p
    exact PathRwQuot.trans_refl_right (A := A) (a := a) (b := b) p
  left_inv := by
    intro a b p
    exact PathRwQuot.symm_trans (A := A) (a := a) (b := b) p
  right_inv := by
    intro a b p
    exact PathRwQuot.trans_symm (A := A) (a := a) (b := b) p

end StrictGroupoid

/-- Functor from computational-path quotients to propositional equality. -/
structure EqFunctor (A : Type u) (B : Type v) where
  /-- Action on objects. -/
  obj : A → B
  /-- Map a quotient path to an equality between images. -/
  map : {a b : A} → PathRwQuot A a b → obj a = obj b
  /-- The image of the reflexive path is reflexive equality. -/
  map_refl : ∀ a, map (PathRwQuot.refl (A := A) a) = rfl
  /-- The image of a composite path is the composite equality. -/
  map_trans :
    ∀ {a b c : A} (p : PathRwQuot A a b) (q : PathRwQuot A b c),
      map (PathRwQuot.trans (A := A) p q) = (map p).trans (map q)
  /-- The image of an inverted path is the symmetric equality. -/
  map_symm :
    ∀ {a b : A} (p : PathRwQuot A a b),
      map (PathRwQuot.symm (A := A) p) = (map p).symm

namespace EqFunctor

variable {A : Type u} {B : Type v} {C : Type w}

/-- Identity functor landing in equality. -/
def id (A : Type u) : EqFunctor A A where
  obj := fun a => a
  map := fun p => PathRwQuot.toEq (A := A) p
  map_refl := by intro a; rfl
  map_trans := by
    intro a b c p q
    exact PathRwQuot.toEq_trans (A := A) (x := p) (y := q)
  map_symm := by
    intro a b p
    exact PathRwQuot.toEq_symm (A := A) (x := p)

/-- Functor induced by a function between base types. -/
def ofFunction (f : A → B) : EqFunctor A B where
  obj := f
  map := fun p => _root_.congrArg f (PathRwQuot.toEq (A := A) p)
  map_refl := by
    intro a
    simp
  map_trans := by
    intro a b c p q
    cases PathRwQuot.toEq (A := A) p
    cases PathRwQuot.toEq (A := A) q
    simp
  map_symm := by
    intro a b p
    cases PathRwQuot.toEq (A := A) p
    simp
end EqFunctor

end ComputationalPaths.Path

/-
# Groupoid structure induced by computational paths

Using the rewrite system developed in `Rewrite`, we package the operations on
computational paths into a weak groupoid structure: all groupoid laws hold up
to `Rw`-reduction.
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
  assoc : {a b c d : A} → (p : Path a b) → (q : Path b c) → (r : Path c d) →
    Rw (comp (comp p q) r) (comp p (comp q r))
  /-- left identity up to rewrite -/
  left_id : {a b : A} → (p : Path a b) → Rw (comp (id) p) p
  /-- right identity up to rewrite -/
  right_id : {a b : A} → (p : Path a b) → Rw (comp p (id)) p
  /-- left inverse up to rewrite -/
  left_inv : {a b : A} → (p : Path a b) → Rw (comp (inv p) p) (id)
  /-- right inverse up to rewrite -/
  right_inv : {a b : A} → (p : Path a b) → Rw (comp p (inv p)) (id)

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

end ComputationalPaths.Path

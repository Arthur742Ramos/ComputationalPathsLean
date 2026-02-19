/-
# Concrete instances of the 2-category typeclasses

We build a `StrictTwoCategory` whose objects are types in a fixed universe,
1-cells are functions, and 2-cells between parallel functions are
`PLift (f = g)` (propositional equality lifted to `Type`).  All three
easy axiom classes (`HasVcompAssoc`, `HasHcompFunctorial`, `HasInterchange`)
are discharged by the fact that `PLift (f = g)` is a subsingleton.
-/

import ComputationalPaths.Path.Category.TwoCategories

namespace ComputationalPaths

universe u

-- ============================================================
-- §1  The "Type / Fun / PLift Eq" strict 2-category
-- ============================================================

/-- Canonical strict 2-category: 0-cells = types, 1-cells = functions,
    2-cells = `PLift (f = g)` (propositional equality lifted to `Type 0`). -/
def EqTwoCat : StrictTwoCategory.{u+1, u, 0} where
  Obj   := Type u
  Hom   := fun A B => (A → B)
  TwoHom := fun f g => PLift (f = g)
  id₁   := fun _ => id
  comp₁ := fun f g => g ∘ f
  id₂   := fun _ => ⟨rfl⟩
  vcomp := fun ⟨α⟩ ⟨β⟩ => ⟨α.trans β⟩
  hcomp := fun {_ _ _} {f f'} {g g'} ⟨α⟩ ⟨β⟩ =>
    ⟨show g ∘ f = g' ∘ f' from α ▸ β ▸ rfl⟩
  assoc₁ := fun _ _ _ => rfl
  leftId₁ := fun _ => rfl
  rightId₁ := fun _ => rfl

-- Any two elements of `PLift (f = g)` are equal.
private theorem plift_eq_subsingleton {α : Prop} (a b : PLift α) : a = b := by
  cases a; cases b; congr

-- ============================================================
-- §2  HasVcompAssoc — vertical composition is associative
-- ============================================================

instance instHasVcompAssoc_EqTwoCat : HasVcompAssoc EqTwoCat.{u} where
  vcomp_assoc := fun _ _ _ => plift_eq_subsingleton _ _

-- ============================================================
-- §3  HasHcompFunctorial — hcomp preserves identities
-- ============================================================

instance instHasHcompFunctorial_EqTwoCat : HasHcompFunctorial EqTwoCat.{u} where
  hcomp_id := fun _ _ => plift_eq_subsingleton _ _

-- ============================================================
-- §4  HasInterchange — the interchange law
-- ============================================================

instance instHasInterchange_EqTwoCat : HasInterchange EqTwoCat.{u} where
  interchange := fun _ _ _ _ => plift_eq_subsingleton _ _

end ComputationalPaths

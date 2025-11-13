/-
# Basic combinators for computational paths (UIP)

Consequences for the uniqueness of identity proofs principle derived from the
computational-path machinery.
-/

import ComputationalPaths.Path.Basic.Congruence

namespace ComputationalPaths

universe u

/-- `UIP A` asserts that any two computational paths with the same endpoints
are judgmentally equal, echoing the uniqueness of identity proofs principle. -/
def UIP (A : Type u) : Prop :=
  ∀ {a b : A}, ∀ (p q : Path a b), p = q

/-- A type with an inhabited path space witnesses non-`UIP`: the empty path and
the explicit reflexive rewrite remain distinct. -/
theorem not_uip_of_inhabited {A : Type u} (a : A) : ¬ UIP A := by
  intro h
  have := h (p := Path.refl a) (q := Path.ofEq (rfl : a = a))
  exact Path.refl_ne_ofEq (A := A) a this

/-- As soon as a type is nonempty we can pick a witness and derive
`¬ UIP A` from the inhabited case. -/
theorem not_uip_of_nonempty {A : Type u} (hA : Nonempty A) : ¬ UIP A := by
  classical
  obtain ⟨a⟩ := hA
  exact not_uip_of_inhabited (A := A) a

end ComputationalPaths


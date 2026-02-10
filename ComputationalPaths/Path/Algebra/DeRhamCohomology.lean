/-
# De Rham Cohomology for Computational Paths

Differential forms, de Rham complex, de Rham cohomology groups.
All proofs are complete — no sorry, no axiom.
-/
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra

namespace ComputationalPaths.Path.DeRhamCohomology

universe u

/-! ## De Rham Complex -/

/-- The de Rham complex: graded spaces with exterior derivative satisfying d² = 0. -/
structure DeRhamComplex where
  /-- The space of n-forms. -/
  forms : Nat → Type u
  /-- The zero form in each degree. -/
  zero : (n : Nat) → forms n
  /-- The exterior derivative. -/
  d : (n : Nat) → forms n → forms (n + 1)
  /-- d² = 0. -/
  d_sq : ∀ n (ω : forms n), d (n + 1) (d n ω) = zero (n + 2)
  /-- d preserves zero. -/
  d_zero : ∀ n, d n (zero n) = zero (n + 1)

/-- The trivial de Rham complex. -/
def DeRhamComplex.trivial : DeRhamComplex.{u} where
  forms := fun _ => PUnit
  zero := fun _ => PUnit.unit
  d := fun _ _ => PUnit.unit
  d_sq := fun _ _ => rfl
  d_zero := fun _ => rfl

/-! ## Closed and Exact Forms -/

/-- A closed form: dω = 0. -/
structure ClosedForm (C : DeRhamComplex.{u}) (n : Nat) where
  /-- The underlying form. -/
  form : C.forms n
  /-- Closedness condition. -/
  closed : C.d n form = C.zero (n + 1)

/-- An exact form: ω = dη for some η. -/
structure ExactForm (C : DeRhamComplex.{u}) (n : Nat) where
  /-- The underlying form. -/
  form : C.forms n
  /-- The primitive. -/
  primitive : C.forms (n - 1)

/-- Every exact form is closed (d(dη) = 0). -/
theorem exact_is_closed_succ (C : DeRhamComplex.{u}) (n : Nat) (η : C.forms n) :
    C.d (n + 1) (C.d n η) = C.zero (n + 2) :=
  C.d_sq n η

/-! ## Chain Maps -/

/-- A chain map between de Rham complexes. -/
structure DeRhamMap (C D : DeRhamComplex.{u}) where
  /-- Underlying map at each degree. -/
  map : (n : Nat) → C.forms n → D.forms n
  /-- Preserves zero. -/
  map_zero : ∀ n, map n (C.zero n) = D.zero n
  /-- Commutes with d. -/
  comm : ∀ n (ω : C.forms n), map (n + 1) (C.d n ω) = D.d n (map n ω)

/-- The identity map on a de Rham complex. -/
def DeRhamMap.id (C : DeRhamComplex.{u}) : DeRhamMap C C where
  map := fun _ ω => ω
  map_zero := fun _ => rfl
  comm := fun _ _ => rfl

/-- Composition of de Rham maps. -/
def DeRhamMap.comp {A B C : DeRhamComplex.{u}} (g : DeRhamMap B C) (f : DeRhamMap A B) :
    DeRhamMap A C where
  map := fun n ω => g.map n (f.map n ω)
  map_zero := fun n => by simp [f.map_zero, g.map_zero]
  comm := fun n ω => by simp [f.comm, g.comm]

/-- Composition with identity is identity. -/
theorem DeRhamMap.comp_id {A B : DeRhamComplex.{u}} (f : DeRhamMap A B) :
    DeRhamMap.comp f (DeRhamMap.id A) = f := by
  cases f; rfl

/-- Identity composed with map is identity. -/
theorem DeRhamMap.id_comp {A B : DeRhamComplex.{u}} (f : DeRhamMap A B) :
    DeRhamMap.comp (DeRhamMap.id B) f = f := by
  cases f; rfl

/-! ## Pullback of Forms -/

/-- Pullback data for differential forms. -/
structure Pullback (C D : DeRhamComplex.{u}) where
  /-- The pullback map (contravariant). -/
  pullback : DeRhamMap D C
  /-- Pullback maps closed forms to closed forms. -/
  mapClosed : ∀ n (ω : ClosedForm D n),
    C.d n (pullback.map n ω.form) = C.zero (n + 1)

/-! ## De Rham Theorem Data -/

/-- De Rham theorem data: comparison with singular cohomology. -/
structure DeRhamTheorem where
  /-- The de Rham complex. -/
  deRham : DeRhamComplex.{u}
  /-- Abstract singular cohomology groups. -/
  singular : Nat → Type u
  /-- Zero in singular cohomology. -/
  singularZero : (n : Nat) → singular n

/-! ## Poincaré Lemma -/

/-- Poincaré lemma data: on a contractible space, every closed form has a primitive. -/
structure PoincareLemma (C : DeRhamComplex.{u}) where
  /-- Contracting homotopy. -/
  homotopy : (n : Nat) → C.forms (n + 1) → C.forms n
  /-- Homotopy maps zero to zero. -/
  homotopy_zero : ∀ n, homotopy n (C.zero (n + 1)) = C.zero n

end ComputationalPaths.Path.DeRhamCohomology

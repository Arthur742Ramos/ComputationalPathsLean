/- 
# Representation Theory Interface

This file provides a compact Lean 4 formalization interface for:
- group representations,
- character theory,
- irreducible representations,
- Schur's lemma (finite-dimensional formulation),
- Maschke's theorem (complement formulation).

All results are proved without `sorry` and without adding axioms.
-/

import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Maschke

open scoped BigOperators

noncomputable section

namespace RepresentationTheory

/-! ## Basic representation definitions -/

section Basic

variable (k G V : Type*) [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

/-- A `k`-linear representation of `G` on `V`. -/
abbrev GroupRep : Type* := Representation k G V

/-- The trivial representation. -/
abbrev trivialRep : GroupRep k G V := Representation.trivial k G V

@[simp]
theorem trivialRep_apply (g : G) (v : V) :
    trivialRep k G V g v = v := by
  simpa [trivialRep] using (Representation.trivial_apply (k := k) (G := G) (V := V) g v)

end Basic

/-! ## Irreducible finite-dimensional representations -/

section Irreducible

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V]

/-- The bundled finite-dimensional representation associated to `ρ`. -/
abbrev toFDRep (ρ : Representation k G V) : FDRep k G := FDRep.of ρ

/-- Irreducibility, expressed via categorical simplicity of `FDRep`. -/
def IsIrreducible (ρ : Representation k G V) : Prop :=
  CategoryTheory.Simple (toFDRep ρ)

theorem isIrreducible_iff (ρ : Representation k G V) :
    IsIrreducible ρ ↔ CategoryTheory.Simple (toFDRep ρ) :=
  Iff.rfl

end Irreducible

/-! ## Character theory -/

section CharacterTheory

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V]

/-- Character of a finite-dimensional representation. -/
def repCharacter (ρ : Representation k G V) : G → k :=
  (toFDRep ρ).character

@[simp]
theorem repCharacter_one (ρ : Representation k G V) :
    repCharacter ρ 1 = Module.finrank k V := by
  simpa [repCharacter, toFDRep] using (FDRep.char_one (V := toFDRep ρ))

theorem repCharacter_mul_comm (ρ : Representation k G V) (g h : G) :
    repCharacter ρ (h * g) = repCharacter ρ (g * h) := by
  simpa [repCharacter, toFDRep] using (FDRep.char_mul_comm (V := toFDRep ρ) (g := g) (h := h))

end CharacterTheory

/-! ## Schur's lemma and orthogonality statements -/

section SchurAndOrthogonality

variable {k G : Type*} [Field k] [Group G] [IsAlgClosed k]
variable [Fintype G] [Invertible (Fintype.card G : k)]

/-- Schur's lemma in finite-dimensional form: the `Hom`-space between irreducibles has
dimension `1` when they are isomorphic and `0` otherwise. -/
theorem schur_finrank_hom (V W : FDRep k G)
    [CategoryTheory.Simple V] [CategoryTheory.Simple W] :
    Module.finrank k (V ⟶ W) = if Nonempty (V ≅ W) then 1 else 0 := by
  simpa using (FDRep.finrank_hom_simple_simple (k := k) (G := G) V W)

/-- Character orthogonality for irreducible finite-dimensional representations. -/
theorem character_orthonormal (V W : FDRep k G)
    [CategoryTheory.Simple V] [CategoryTheory.Simple W] :
    ⅟(Fintype.card G : k) • ∑ g : G, V.character g * W.character g⁻¹ =
      if Nonempty (V ≅ W) then (1 : k) else 0 := by
  simpa using (FDRep.char_orthonormal (k := k) (G := G) V W)

end SchurAndOrthogonality

/-! ## Maschke's theorem -/

section Maschke

variable {k G V : Type*} [Field k] [Group G] [Fintype G]
variable [NeZero (Fintype.card G : k)]
variable [AddCommGroup V] [Module (MonoidAlgebra k G) V]

/-- Maschke's theorem (complement formulation): every submodule has a complement. -/
theorem maschke_exists_complement
    (p : Submodule (MonoidAlgebra k G) V) :
    ∃ q : Submodule (MonoidAlgebra k G) V, IsCompl p q := by
  simpa using (MonoidAlgebra.Submodule.exists_isCompl (k := k) (G := G) (V := V) p)

/-- Maschke's theorem implies semisimplicity of `k[G]`-modules. -/
theorem maschke_semisimple :
    IsSemisimpleModule (MonoidAlgebra k G) V := by
  infer_instance

end Maschke

end RepresentationTheory

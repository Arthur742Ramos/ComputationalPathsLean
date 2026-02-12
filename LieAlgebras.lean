/-!
# Lie algebras: core formalization interface

This module collects standard Lie-theoretic notions from Mathlib in one place:

- Lie algebra bracket operations
- Lie ideals
- Solvable and nilpotent Lie algebras
- Cartan subalgebras
- Root systems

All theorem proofs are complete and axiom-free.
-/

import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.Weights.RootSystem

namespace LieAlgebras

/-! ## Lie brackets and ideals -/

section LieBracketAndIdeals

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The Lie bracket as an explicit binary map. -/
abbrev lieBracket : L → L → L := fun x y => ⁅x, y⁆

@[simp]
theorem lieBracket_apply (x y : L) :
    lieBracket (R := R) (L := L) x y = ⁅x, y⁆ :=
  rfl

@[simp]
theorem lieBracket_self (x : L) :
    lieBracket (R := R) (L := L) x x = 0 := by
  simpa [lieBracket] using (lie_self (x := x))

theorem lieBracket_skew (x y : L) :
    lieBracket (R := R) (L := L) x y = -lieBracket (R := R) (L := L) y x := by
  simpa [lieBracket] using (lie_skew (x := x) (y := y)).symm

/-- Lie ideals of `L` over `R`. -/
abbrev LieIdealType := LieIdeal R L

@[simp]
theorem mem_top_lieIdeal (x : L) :
    x ∈ (⊤ : LieIdealType (R := R) (L := L)) := by
  simp [LieIdealType]

@[simp]
theorem mem_bot_lieIdeal (x : L) :
    x ∈ (⊥ : LieIdealType (R := R) (L := L)) ↔ x = 0 := by
  simp [LieIdealType]

theorem lie_mem_of_mem_ideal (I : LieIdealType (R := R) (L := L)) (x y : L)
    (hy : y ∈ I) : ⁅x, y⁆ ∈ I :=
  I.lie_mem hy

end LieBracketAndIdeals

/-! ## Solvable and nilpotent Lie algebras -/

section SolvableNilpotent

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The derived series `Dⁿ(L)`. -/
abbrev derivedSeries : ℕ → LieIdeal R L := LieAlgebra.derivedSeries R L

/-- The lower central series `γₙ(L)` from the adjoint action. -/
abbrev lowerCentralSeries : ℕ → LieSubmodule R L L := LieModule.lowerCentralSeries R L L

/-- Solvability predicate for Lie algebras. -/
def IsSolvable : Prop := LieAlgebra.IsSolvable L

/-- Nilpotence predicate for Lie algebras. -/
def IsNilpotent : Prop := LieRing.IsNilpotent L

theorem isSolvable_iff_exists_derivedSeries_eq_bot :
    IsSolvable (R := R) (L := L) ↔
      ∃ k, derivedSeries (R := R) (L := L) k = ⊥ := by
  simpa [IsSolvable, derivedSeries] using (LieAlgebra.isSolvable_iff (R := R) (L := L))

theorem isNilpotent_iff_exists_lowerCentralSeries_eq_bot :
    IsNilpotent (L := L) ↔
      ∃ k, lowerCentralSeries (R := R) (L := L) k = ⊥ := by
  simpa [IsNilpotent, lowerCentralSeries, LieRing.IsNilpotent] using
    (LieModule.isNilpotent_iff (R := R) (L := L) (M := L))

theorem solvable_of_nilpotent [IsNilpotent (L := L)] :
    IsSolvable (R := R) (L := L) := by
  infer_instance

end SolvableNilpotent

/-! ## Cartan subalgebras -/

section CartanSubalgebras

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
variable (H : LieSubalgebra R L)

/-- Predicate that `H` is a Cartan subalgebra. -/
abbrev IsCartan : Prop := H.IsCartanSubalgebra

theorem isCartan_iff_isUcsLimit :
    IsCartan (R := R) (L := L) H ↔ H.toLieSubmodule.IsUcsLimit := by
  simpa [IsCartan] using (LieSubalgebra.isCartanSubalgebra_iff_isUcsLimit (H := H))

theorem cartan_nilpotent [IsCartan (R := R) (L := L) H] :
    LieRing.IsNilpotent H := by
  infer_instance

@[simp]
theorem cartan_normalizer_eq_self [IsCartan (R := R) (L := L) H] :
    H.normalizer = H :=
  (inferInstance : H.IsCartanSubalgebra).self_normalizing

end CartanSubalgebras

/-! ## Root systems -/

section AbstractRootSystems

variable {ι R M N : Type*}
variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Abstract root systems in the sense of `Mathlib.LinearAlgebra.RootSystem`. -/
abbrev AbstractRootSystem := RootSystem ι R M N

theorem span_root_eq_top (Φ : AbstractRootSystem (ι := ι) (R := R) (M := M) (N := N)) :
    Submodule.span R (Set.range Φ.root) = ⊤ := by
  simpa [AbstractRootSystem] using Φ.span_root_eq_top

theorem span_coroot_eq_top (Φ : AbstractRootSystem (ι := ι) (R := R) (M := M) (N := N)) :
    Submodule.span R (Set.range Φ.coroot) = ⊤ := by
  simpa [AbstractRootSystem] using Φ.span_coroot_eq_top

end AbstractRootSystems

section LieTheoreticRootSystems

open LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
variable [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
variable (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- The root system attached to a splitting Cartan subalgebra. -/
noncomputable abbrev associatedRootSystem :
    RootSystem H.root K (Dual K H) H :=
  LieAlgebra.IsKilling.rootSystem (K := K) (L := L) (H := H)

@[simp]
theorem associatedRootSystem_pairing (α β : H.root) :
    (associatedRootSystem (K := K) (L := L) H).pairing β α =
      β.1 (LieAlgebra.IsKilling.coroot α.1) := by
  simpa [associatedRootSystem] using
    (LieAlgebra.IsKilling.rootSystem_pairing_apply (K := K) (L := L) (H := H) α β)

theorem associatedRootSystem_isCrystallographic :
    (associatedRootSystem (K := K) (L := L) H).IsCrystallographic := by
  infer_instance

theorem associatedRootSystem_isReduced :
    (associatedRootSystem (K := K) (L := L) H).IsReduced := by
  infer_instance

end LieTheoreticRootSystems

end LieAlgebras

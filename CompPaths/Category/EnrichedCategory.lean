import CompPaths.Core

namespace CompPaths
namespace Category

open ComputationalPaths
open ComputationalPaths.Path

universe u

section PathGroupoidEnrichment

variable {A : Type u}

/-- `Hom(a,b)` as a groupoid: objects are paths `Path a b`, morphisms are `RwEq`. -/
structure PathHomGroupoid (a b : A) where
  id₂ : ∀ p : Path a b, RwEq p p
  vcomp₂ : ∀ {p q r : Path a b}, RwEq p q → RwEq q r → RwEq p r
  inv₂ : ∀ {p q : Path a b}, RwEq p q → RwEq q p

@[simp] def pathHomGroupoid (a b : A) : PathHomGroupoid (A := A) a b where
  id₂ := fun p => RwEq.refl p
  vcomp₂ := fun α β => RwEq.trans α β
  inv₂ := fun α => RwEq.symm α

theorem pathHomGroupoid_vcomp_assoc_toEq
    {a b : A} {p q r s : Path a b}
    (α : RwEq p q) (β : RwEq q r) (γ : RwEq r s) :
    rweq_toEq ((pathHomGroupoid (A := A) a b).vcomp₂
      ((pathHomGroupoid (A := A) a b).vcomp₂ α β) γ) =
    rweq_toEq ((pathHomGroupoid (A := A) a b).vcomp₂
      α ((pathHomGroupoid (A := A) a b).vcomp₂ β γ)) := by
  rfl

theorem pathHomGroupoid_vcomp_left_id_toEq
    {a b : A} {p q : Path a b} (α : RwEq p q) :
    rweq_toEq ((pathHomGroupoid (A := A) a b).vcomp₂
      ((pathHomGroupoid (A := A) a b).id₂ p) α) =
    rweq_toEq α := by
  rfl

theorem pathHomGroupoid_vcomp_right_id_toEq
    {a b : A} {p q : Path a b} (α : RwEq p q) :
    rweq_toEq ((pathHomGroupoid (A := A) a b).vcomp₂
      α ((pathHomGroupoid (A := A) a b).id₂ q)) =
    rweq_toEq α := by
  rfl

end PathGroupoidEnrichment

section CompositionFunctor

variable {A : Type u}

/-- Composition preserves `RwEq` in the left variable via explicit `Step.trans_congr_left`. -/
noncomputable def compMapLeft {a b c : A}
    (r : Path b c) {p p' : Path a b}
    (α : RwEq p p') :
    RwEq (Path.trans p r) (Path.trans p' r) := by
  induction α with
  | refl p =>
      exact RwEq.refl (Path.trans p r)
  | step s =>
      exact RwEq.step (Step.trans_congr_left r s)
  | symm _ ih =>
      exact RwEq.symm ih
  | trans _ _ ih₁ ih₂ =>
      exact RwEq.trans ih₁ ih₂

/-- Composition preserves `RwEq` in the right variable via explicit `Step.trans_congr_right`. -/
noncomputable def compMapRight {a b c : A}
    (l : Path a b) {q q' : Path b c}
    (β : RwEq q q') :
    RwEq (Path.trans l q) (Path.trans l q') := by
  induction β with
  | refl q =>
      exact RwEq.refl (Path.trans l q)
  | step s =>
      exact RwEq.step (Step.trans_congr_right l s)
  | symm _ ih =>
      exact RwEq.symm ih
  | trans _ _ ih₁ ih₂ =>
      exact RwEq.trans ih₁ ih₂

/-- Composition as a groupoid functor on hom-groupoids. -/
noncomputable def compMap {a b c : A}
    {p p' : Path a b} {q q' : Path b c}
    (α : RwEq p p') (β : RwEq q q') :
    RwEq (Path.trans p q) (Path.trans p' q') :=
  RwEq.trans (compMapLeft (A := A) q α) (compMapRight (A := A) p' β)

/-- Single-step functoriality witness for composition, using explicit `Step` constructors. -/
noncomputable def compMap_steps {a b c : A}
    {p p' : Path a b} {q q' : Path b c}
    (sp : Step p p') (sq : Step q q') :
    RwEq (Path.trans p q) (Path.trans p' q') :=
  RwEq.trans
    (RwEq.step (Step.trans_congr_left q sp))
    (RwEq.step (Step.trans_congr_right p' sq))

theorem compMap_preserves_id_toEq
    {a b c : A} (p : Path a b) (q : Path b c) :
    rweq_toEq (compMap (A := A) (RwEq.refl p) (RwEq.refl q)) =
      rweq_toEq (RwEq.refl (Path.trans p q)) := by
  rfl

theorem compMap_preserves_vcomp_toEq
    {a b c : A}
    {p₁ p₂ p₃ : Path a b} {q₁ q₂ q₃ : Path b c}
    (α₁ : RwEq p₁ p₂) (α₂ : RwEq p₂ p₃)
    (β₁ : RwEq q₁ q₂) (β₂ : RwEq q₂ q₃) :
    rweq_toEq (compMap (A := A) (RwEq.trans α₁ α₂) (RwEq.trans β₁ β₂)) =
      rweq_toEq (RwEq.trans (compMap (A := A) α₁ β₁) (compMap (A := A) α₂ β₂)) := by
  rfl

end CompositionFunctor

section EnrichedYoneda

variable {A : Type u}

/-- Enriched natural families `Hom(x,-) ⟹ Hom(a,-)` in the path-groupoid enrichment. -/
structure EnrichedNat (a x : A) where
  app : {y : A} → Path x y → Path a y
  natural :
    ∀ {y z : A} (g : Path x y) (f : Path y z),
      RwEq (app (Path.trans g f)) (Path.trans (app g) f)
  determined_by_base :
    ∀ {y : A} (g : Path x y),
      RwEq (app g) (Path.trans (app (Path.refl x)) g)

/-- Yoneda map: a path `p : a ⟶ x` gives precomposition by `p`. -/
noncomputable def yonedaToNat {a x : A} (p : Path a x) : EnrichedNat (A := A) a x where
  app := fun {_} g => Path.trans p g
  natural := by
    intro y z g f
    exact RwEq.symm (RwEq.step (Step.trans_assoc p g f))
  determined_by_base := by
    intro y g
    exact RwEq.symm
      (RwEq.trans
        (RwEq.step (Step.trans_assoc p (Path.refl x) g))
        (RwEq.step (Step.trans_congr_right p (Step.trans_refl_left g))))

/-- Yoneda evaluation at identity. -/
@[simp] def yonedaFromNat {a x : A} (η : EnrichedNat (A := A) a x) : Path a x :=
  η.app (Path.refl x)

/-- Enriched Yoneda left inverse (up to `RwEq`). -/
noncomputable def enrichedYoneda_left_inv {a x : A} (p : Path a x) :
    RwEq (yonedaFromNat (A := A) (yonedaToNat (A := A) p)) p := by
  simpa [yonedaFromNat, yonedaToNat] using
    (RwEq.step (Step.trans_refl_right p) :
      RwEq (Path.trans p (Path.refl x)) p)

/-- Enriched Yoneda right inverse, pointwise up to `RwEq`. -/
noncomputable def enrichedYoneda_right_inv
    {a x : A} (η : EnrichedNat (A := A) a x)
    {y : A} (g : Path x y) :
    RwEq ((yonedaToNat (A := A) (yonedaFromNat (A := A) η)).app g) (η.app g) := by
  change RwEq (Path.trans (η.app (Path.refl x)) g) (η.app g)
  exact RwEq.symm (η.determined_by_base g)

/-- Enriched Yoneda left inverse: given path `p`, the roundtrip produces `RwEq`. -/
noncomputable def enrichedYoneda_left {a x : A} (p : Path a x) :
    RwEq (yonedaFromNat (A := A) (yonedaToNat (A := A) p)) p :=
  enrichedYoneda_left_inv (A := A) p

/-- Enriched Yoneda right inverse: given `η` and `g`, the roundtrip produces `RwEq`. -/
noncomputable def enrichedYoneda_right {a x : A}
    (η : EnrichedNat (A := A) a x) {y : A} (g : Path x y) :
    RwEq ((yonedaToNat (A := A) (yonedaFromNat (A := A) η)).app g) (η.app g) :=
  enrichedYoneda_right_inv (A := A) η g

end EnrichedYoneda

section LocallyGroupoidal

variable {A : Type u}

/-- Every 2-cell in a hom-groupoid is invertible by symmetry of `RwEq`. -/
@[simp] noncomputable def twoCellInverse
    {a b : A} {p q : Path a b} (α : RwEq p q) : RwEq q p :=
  (pathHomGroupoid (A := A) a b).inv₂ α

/-- Local groupoidality: each 2-cell admits a two-sided inverse (at `toEq` level). -/
theorem locally_groupoidal
    {a b : A} {p q : Path a b} (α : RwEq p q) :
    ∃ β : RwEq q p,
      rweq_toEq ((pathHomGroupoid (A := A) a b).vcomp₂ α β) =
        rweq_toEq ((pathHomGroupoid (A := A) a b).id₂ p) ∧
      rweq_toEq ((pathHomGroupoid (A := A) a b).vcomp₂ β α) =
        rweq_toEq ((pathHomGroupoid (A := A) a b).id₂ q) := by
  refine ⟨twoCellInverse (A := A) α, ?_, ?_⟩
  · apply Subsingleton.elim
  · apply Subsingleton.elim

end LocallyGroupoidal

end Category
end CompPaths

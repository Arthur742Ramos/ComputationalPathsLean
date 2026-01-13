/-
# BiContext Derived Results

Axiom-free, sorry-free derived theorems for BiContext operations,
using `rweq_of_step` to lift primitive Step rules to RwEq equivalences.

## Key Results

- `rweq_biContext_mapLeft_congr`: BiContext left map congruence (Rule 65)
- `rweq_biContext_mapRight_congr`: BiContext right map congruence (Rule 66)
- `rweq_biContext_map2_congr_left/right`: BiContext map2 congruence (Rules 67-68)
- Derived composition and functoriality laws
-/

import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Basic.Context

namespace ComputationalPaths
namespace Path
namespace BiContextDerived

open Path

variable {A : Type u} {B : Type u} {C : Type u}

/-! ## BiContext Congruence Rules (Rules 65-68) -/

/-- Rule 65: BiContext left map congruence.
    If p ≈ q then K.mapLeft p b ≈ K.mapLeft q b -/
theorem rweq_biContext_mapLeft_congr
    (K : BiContext A B C) {a₁ a₂ : A} (b : B)
    {p q : Path a₁ a₂}
    (h : RwEq p q) :
    RwEq (BiContext.mapLeft K p b) (BiContext.mapLeft K q b) := by
  induction h with
  | refl => exact RwEq.refl _
  | step s => exact rweq_of_step (Step.biContext_mapLeft_congr K b s)
  | trans _ _ ih1 ih2 => exact RwEq.trans ih1 ih2
  | symm _ ih => exact RwEq.symm ih

/-- Rule 66: BiContext right map congruence.
    If p ≈ q then K.mapRight a p ≈ K.mapRight a q -/
theorem rweq_biContext_mapRight_congr
    (K : BiContext A B C) (a : A) {b₁ b₂ : B}
    {p q : Path b₁ b₂}
    (h : RwEq p q) :
    RwEq (BiContext.mapRight K a p) (BiContext.mapRight K a q) := by
  induction h with
  | refl => exact RwEq.refl _
  | step s => exact rweq_of_step (Step.biContext_mapRight_congr K a s)
  | trans _ _ ih1 ih2 => exact RwEq.trans ih1 ih2
  | symm _ ih => exact RwEq.symm ih

/-- Rule 67: BiContext map2 left congruence.
    If p ≈ q then K.map2 p r ≈ K.map2 q r -/
theorem rweq_biContext_map2_congr_left
    (K : BiContext A B C) {a₁ a₂ : A} {b₁ b₂ : B}
    {p q : Path a₁ a₂} (r : Path b₁ b₂)
    (h : RwEq p q) :
    RwEq (BiContext.map2 K p r) (BiContext.map2 K q r) := by
  induction h with
  | refl => exact RwEq.refl _
  | step s => exact rweq_of_step (Step.biContext_map2_congr_left K r s)
  | trans _ _ ih1 ih2 => exact RwEq.trans ih1 ih2
  | symm _ ih => exact RwEq.symm ih

/-- Rule 68: BiContext map2 right congruence.
    If q ≈ r then K.map2 p q ≈ K.map2 p r -/
theorem rweq_biContext_map2_congr_right
    (K : BiContext A B C) {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) {q r : Path b₁ b₂}
    (h : RwEq q r) :
    RwEq (BiContext.map2 K p q) (BiContext.map2 K p r) := by
  induction h with
  | refl => exact RwEq.refl _
  | step s => exact rweq_of_step (Step.biContext_map2_congr_right K p s)
  | trans _ _ ih1 ih2 => exact RwEq.trans ih1 ih2
  | symm _ ih => exact RwEq.symm ih

/-! ## BiContext Functoriality -/

/-- BiContext left map is functorial: K.mapLeft (p·q) b ≈ K.mapLeft p b · K.mapLeft q b -/
theorem rweq_biContext_mapLeft_functorial
    (K : BiContext A B C) {a₁ a₂ a₃ : A}
    (p : Path a₁ a₂) (q : Path a₂ a₃) (b : B) :
    RwEq (BiContext.mapLeft K (trans p q) b)
         (trans (BiContext.mapLeft K p b) (BiContext.mapLeft K q b)) :=
  rweq_of_eq (BiContext.mapLeft_trans K p q b)

/-- BiContext right map is functorial: K.mapRight a (p·q) ≈ K.mapRight a p · K.mapRight a q -/
theorem rweq_biContext_mapRight_functorial
    (K : BiContext A B C) (a : A) {b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) :
    RwEq (BiContext.mapRight K a (trans p q))
         (trans (BiContext.mapRight K a p) (BiContext.mapRight K a q)) :=
  rweq_of_eq (BiContext.mapRight_trans K a p q)

/-- BiContext left map preserves refl: K.mapLeft refl b ≈ refl -/
theorem rweq_biContext_mapLeft_refl
    (K : BiContext A B C) (a : A) (b : B) :
    RwEq (BiContext.mapLeft K (refl a) b) (refl (K.fill a b)) :=
  rweq_of_eq (BiContext.mapLeft_refl K a b)

/-- BiContext right map preserves refl: K.mapRight a refl ≈ refl -/
theorem rweq_biContext_mapRight_refl
    (K : BiContext A B C) (a : A) (b : B) :
    RwEq (BiContext.mapRight K a (refl b)) (refl (K.fill a b)) :=
  rweq_of_eq (BiContext.mapRight_refl K a b)

/-- BiContext left map preserves symm: K.mapLeft (p⁻¹) b ≈ (K.mapLeft p b)⁻¹ -/
theorem rweq_biContext_mapLeft_symm
    (K : BiContext A B C) {a₁ a₂ : A}
    (p : Path a₁ a₂) (b : B) :
    RwEq (BiContext.mapLeft K (symm p) b) (symm (BiContext.mapLeft K p b)) :=
  rweq_of_eq (BiContext.mapLeft_symm K p b)

/-- BiContext right map preserves symm: K.mapRight a (p⁻¹) ≈ (K.mapRight a p)⁻¹ -/
theorem rweq_biContext_mapRight_symm
    (K : BiContext A B C) (a : A) {b₁ b₂ : B}
    (p : Path b₁ b₂) :
    RwEq (BiContext.mapRight K a (symm p)) (symm (BiContext.mapRight K a p)) :=
  rweq_of_eq (BiContext.mapRight_symm K a p)

/-! ## BiContext Composition Laws -/

/-- Double left map composition:
    K.mapLeft p b · K.mapLeft q b ≈ K.mapLeft (p·q) b -/
theorem rweq_biContext_double_mapLeft
    (K : BiContext A B C) {a₁ a₂ a₃ : A}
    (p : Path a₁ a₂) (q : Path a₂ a₃) (b : B) :
    RwEq (trans (BiContext.mapLeft K p b) (BiContext.mapLeft K q b))
         (BiContext.mapLeft K (trans p q) b) :=
  RwEq.symm (rweq_biContext_mapLeft_functorial K p q b)

/-- Double right map composition:
    K.mapRight a p · K.mapRight a q ≈ K.mapRight a (p·q) -/
theorem rweq_biContext_double_mapRight
    (K : BiContext A B C) (a : A) {b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) :
    RwEq (trans (BiContext.mapRight K a p) (BiContext.mapRight K a q))
         (BiContext.mapRight K a (trans p q)) :=
  RwEq.symm (rweq_biContext_mapRight_functorial K a p q)

/-- Triple left map composition:
    K.mapLeft p b · K.mapLeft q b · K.mapLeft r b ≈ K.mapLeft ((p·q)·r) b -/
theorem rweq_biContext_triple_mapLeft
    (K : BiContext A B C) {a₁ a₂ a₃ a₄ : A}
    (p : Path a₁ a₂) (q : Path a₂ a₃) (r : Path a₃ a₄) (b : B) :
    RwEq (trans (trans (BiContext.mapLeft K p b) (BiContext.mapLeft K q b))
                (BiContext.mapLeft K r b))
         (BiContext.mapLeft K (trans (trans p q) r) b) := by
  have h1 := rweq_biContext_double_mapLeft K p q b
  have h2 : RwEq (trans (trans (BiContext.mapLeft K p b) (BiContext.mapLeft K q b))
                       (BiContext.mapLeft K r b))
                 (trans (BiContext.mapLeft K (trans p q) b) (BiContext.mapLeft K r b)) :=
    rweq_trans_congr_left (BiContext.mapLeft K r b) h1
  have h3 := rweq_biContext_double_mapLeft K (trans p q) r b
  exact RwEq.trans h2 h3

/-! ## BiContext Inverse Laws -/

/-- BiContext left map respects cancellation:
    K.mapLeft p b · K.mapLeft (p⁻¹) b ≈ refl -/
theorem rweq_biContext_mapLeft_cancel
    (K : BiContext A B C) {a₁ a₂ : A}
    (p : Path a₁ a₂) (b : B) :
    RwEq (trans (BiContext.mapLeft K p b) (BiContext.mapLeft K (symm p) b))
         (refl (K.fill a₁ b)) := by
  -- K.mapLeft p · K.mapLeft (p⁻¹) ≈ K.mapLeft (p · p⁻¹)
  have h1 := rweq_biContext_double_mapLeft K p (symm p) b
  -- p · p⁻¹ ≈ refl via rweq_cmpA_inv_right
  have h2 : RwEq (BiContext.mapLeft K (trans p (symm p)) b)
                 (BiContext.mapLeft K (refl a₁) b) :=
    rweq_biContext_mapLeft_congr K b (rweq_cmpA_inv_right p)
  -- K.mapLeft refl ≈ refl
  have h3 := rweq_biContext_mapLeft_refl K a₁ b
  exact RwEq.trans h1 (RwEq.trans h2 h3)

/-- BiContext right map respects cancellation:
    K.mapRight a p · K.mapRight a (p⁻¹) ≈ refl -/
theorem rweq_biContext_mapRight_cancel
    (K : BiContext A B C) (a : A) {b₁ b₂ : B}
    (p : Path b₁ b₂) :
    RwEq (trans (BiContext.mapRight K a p) (BiContext.mapRight K a (symm p)))
         (refl (K.fill a b₁)) := by
  have h1 := rweq_biContext_double_mapRight K a p (symm p)
  have h2 : RwEq (BiContext.mapRight K a (trans p (symm p)))
                 (BiContext.mapRight K a (refl b₁)) :=
    rweq_biContext_mapRight_congr K a (rweq_cmpA_inv_right p)
  have h3 := rweq_biContext_mapRight_refl K a b₁
  exact RwEq.trans h1 (RwEq.trans h2 h3)

/-! ## map2 Decomposition -/

/-- BiContext map2 decomposition (Rule 9):
    K.map2 p q ≈ K.mapRight a₁ q · K.mapLeft p b₂ -/
theorem rweq_biContext_map2_decompose
    (K : BiContext A B C) {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    RwEq (BiContext.map2 K p q)
         (trans (BiContext.mapRight K a₁ q) (BiContext.mapLeft K p b₂)) := by
  simp only [BiContext.map2, BiContext.mapRight, BiContext.mapLeft]
  exact rweq_of_step (Step.map2_subst K.fill p q)

/-! ## mapLeft/mapRight Congruence (Rules 69-72) -/

/-- Rule 69: mapLeft congruence. If p ≈ q then mapLeft f p b ≈ mapLeft f q b -/
theorem rweq_mapLeft_congr_derived
    {A : Type u} {B : Type u}
    (f : A → B → A) {a₁ a₂ : A} (b : B)
    {p q : Path a₁ a₂}
    (h : RwEq p q) :
    RwEq (mapLeft f p b) (mapLeft f q b) := by
  induction h with
  | refl => exact RwEq.refl _
  | step s => exact rweq_of_step (Step.mapLeft_congr f b s)
  | trans _ _ ih1 ih2 => exact RwEq.trans ih1 ih2
  | symm _ ih => exact RwEq.symm ih

/-- Rule 70: mapRight congruence. If p ≈ q then mapRight f a p ≈ mapRight f a q -/
theorem rweq_mapRight_congr_derived
    {A : Type u}
    (f : A → A → A) (a : A) {b₁ b₂ : A}
    {p q : Path b₁ b₂}
    (h : RwEq p q) :
    RwEq (mapRight f a p) (mapRight f a q) := by
  induction h with
  | refl => exact RwEq.refl _
  | step s => exact rweq_of_step (Step.mapRight_congr f a s)
  | trans _ _ ih1 ih2 => exact RwEq.trans ih1 ih2
  | symm _ ih => exact RwEq.symm ih

/-- Rule 71: mapLeft with propositional equality.
    mapLeft f (ofEq h) b ≈ ofEq (congrArg (·.f b) h) -/
theorem rweq_mapLeft_ofEq
    {A : Type u} {B : Type u}
    (f : A → B → A) {a₁ a₂ : A} (h : a₁ = a₂) (b : B) :
    RwEq (mapLeft f (ofEq h) b) (ofEq (_root_.congrArg (fun x => f x b) h)) :=
  rweq_of_step (Step.mapLeft_ofEq f h b)

/-- Rule 72: mapRight with propositional equality.
    mapRight f a (ofEq h) ≈ ofEq (congrArg (f a) h) -/
theorem rweq_mapRight_ofEq
    {A : Type u}
    (f : A → A → A) (a : A) {b₁ b₂ : A} (h : b₁ = b₂) :
    RwEq (mapRight f a (ofEq h)) (ofEq (_root_.congrArg (f a) h)) :=
  rweq_of_step (Step.mapRight_ofEq f a h)

/-! ## Dependent BiContext Congruence (Rules 61-64) -/

/-- Rule 61: DepBiContext left map congruence.
    If p ≈ q then K.mapLeft p b ≈ K.mapLeft q b -/
theorem rweq_depBiContext_mapLeft_congr
    {A : Type u} {B : Type u} {C : A → B → Type u}
    (K : DepBiContext A B C) {a₁ a₂ : A} (b : B)
    {p q : Path a₁ a₂}
    (h : RwEq p q) :
    RwEq (DepBiContext.mapLeft K p b) (DepBiContext.mapLeft K q b) := by
  induction h with
  | refl => exact RwEq.refl _
  | step s => exact rweq_of_step (Step.depBiContext_mapLeft_congr K b s)
  | trans _ _ ih1 ih2 => exact RwEq.trans ih1 ih2
  | symm _ ih => exact RwEq.symm ih

/-- Rule 62: DepBiContext right map congruence.
    If p ≈ q then K.mapRight a p ≈ K.mapRight a q -/
theorem rweq_depBiContext_mapRight_congr
    {A : Type u} {B : Type u} {C : A → B → Type u}
    (K : DepBiContext A B C) (a : A) {b₁ b₂ : B}
    {p q : Path b₁ b₂}
    (h : RwEq p q) :
    RwEq (DepBiContext.mapRight K a p) (DepBiContext.mapRight K a q) := by
  induction h with
  | refl => exact RwEq.refl _
  | step s => exact rweq_of_step (Step.depBiContext_mapRight_congr K a s)
  | trans _ _ ih1 ih2 => exact RwEq.trans ih1 ih2
  | symm _ ih => exact RwEq.symm ih

/-- Rule 63: DepBiContext map2 left congruence.
    If p ≈ q then K.map2 p r ≈ K.map2 q r -/
theorem rweq_depBiContext_map2_congr_left
    {A : Type u} {B : Type u} {C : A → B → Type u}
    (K : DepBiContext A B C) {a₁ a₂ : A} {b₁ b₂ : B}
    {p q : Path a₁ a₂} (r : Path b₁ b₂)
    (h : RwEq p q) :
    RwEq (DepBiContext.map2 K p r) (DepBiContext.map2 K q r) := by
  induction h with
  | refl => exact RwEq.refl _
  | step s => exact rweq_of_step (Step.depBiContext_map2_congr_left K r s)
  | trans _ _ ih1 ih2 => exact RwEq.trans ih1 ih2
  | symm _ ih => exact RwEq.symm ih

/-- Rule 64: DepBiContext map2 right congruence.
    If q ≈ r then K.map2 p q ≈ K.map2 p r -/
theorem rweq_depBiContext_map2_congr_right
    {A : Type u} {B : Type u} {C : A → B → Type u}
    (K : DepBiContext A B C) {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) {q r : Path b₁ b₂}
    (h : RwEq q r) :
    RwEq (DepBiContext.map2 K p q) (DepBiContext.map2 K p r) := by
  induction h with
  | refl => exact RwEq.refl _
  | step s => exact rweq_of_step (Step.depBiContext_map2_congr_right K p s)
  | trans _ _ ih1 ih2 => exact RwEq.trans ih1 ih2
  | symm _ ih => exact RwEq.symm ih

end BiContextDerived
end Path
end ComputationalPaths

/-
# 2-Category Structure on Computational Paths

This module constructs the 2-category structure on the ω-groupoid of
computational paths, using explicit `Step` constructors throughout.

## Constructions

1. **Horizontal composition** of 2-cells via explicit whiskering
2. **Interchange law** — `(h ∘ v) = (v ∘ h)` via explicit Step chains
3. **Godement interchange** — two whiskering orders yield equal witnesses
4. **Whiskering associativity** — coherence of whiskering through triple composition
5. **Naturality of associator** — the associator is natural in each variable
6. **Functoriality of horizontal composition** — `hcomp` respects vertical composition

## Step constructors used

| Step constructor         | Rule | Description                        |
|--------------------------|------|------------------------------------|
| `Step.trans_assoc`       |  8   | Associativity of composition       |
| `Step.trans_refl_left`   |  3   | Left unit law                      |
| `Step.trans_refl_right`  |  4   | Right unit law                     |
| `Step.trans_congr_left`  | 75   | Left congruence (whiskering right) |
| `Step.trans_congr_right` | 76   | Right congruence (whiskering left) |
| `Step.trans_symm`        |  5   | Right inverse                      |
| `Step.symm_trans`        |  6   | Left inverse                       |
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
namespace ComputationalPaths
namespace OmegaGroupoid

open ComputationalPaths
open ComputationalPaths.Path

universe u

variable {A : Type u}

/-! ## §1 Whiskering via explicit Step constructors -/

/-- Vertical composition of 2-cells (`RwEq` witnesses). -/
@[simp] noncomputable def vcomp {a b : A} {p q r : Path a b}
    (α : RwEq p q) (β : RwEq q r) : RwEq p r :=
  RwEq.trans α β

/-- Right whiskering: given α : p ⟹ p', produce (p · q) ⟹ (p' · q).
    Each `Step s` becomes `Step.trans_congr_left q s` (Rule 75). -/
noncomputable def whiskerRight {a b c : A} {p p' : Path a b}
    (q : Path b c) (α : RwEq p p') :
    RwEq (Path.trans p q) (Path.trans p' q) := by
  induction α with
  | refl _ => exact RwEq.refl _
  | step s => exact RwEq.step (Step.trans_congr_left q s)
  | symm _ ih => exact RwEq.symm ih
  | trans _ _ ih₁ ih₂ => exact RwEq.trans ih₁ ih₂

/-- Left whiskering: given β : q ⟹ q', produce (p · q) ⟹ (p · q').
    Each `Step s` becomes `Step.trans_congr_right p s` (Rule 76). -/
noncomputable def whiskerLeft {a b c : A} (p : Path a b) {q q' : Path b c}
    (β : RwEq q q') :
    RwEq (Path.trans p q) (Path.trans p q') := by
  induction β with
  | refl _ => exact RwEq.refl _
  | step s => exact RwEq.step (Step.trans_congr_right p s)
  | symm _ ih => exact RwEq.symm ih
  | trans _ _ ih₁ ih₂ => exact RwEq.trans ih₁ ih₂

/-! ## §2 Horizontal Composition of 2-cells -/

/-- Horizontal composition of 2-cells via explicit whiskering:
    `hcomp α β = whiskerRight q α ⬝ whiskerLeft p' β`.
    Uses **Rule 75** and **Rule 76** throughout. -/
noncomputable def hcomp {a b c : A} {p p' : Path a b} {q q' : Path b c}
    (α : RwEq p p') (β : RwEq q q') :
    RwEq (Path.trans p q) (Path.trans p' q') :=
  RwEq.trans (whiskerRight q α) (whiskerLeft p' β)

/-- Alternative horizontal composition: whisker β first, then α.
    `hcomp' α β = whiskerLeft p β ⬝ whiskerRight q' α`. -/
noncomputable def hcomp' {a b c : A} {p p' : Path a b} {q q' : Path b c}
    (α : RwEq p p') (β : RwEq q q') :
    RwEq (Path.trans p q) (Path.trans p' q') :=
  RwEq.trans (whiskerLeft p β) (whiskerRight q' α)

/-- Both horizontal compositions produce the same `toEq`. -/
theorem hcomp_eq_hcomp' {a b c : A} {p p' : Path a b} {q q' : Path b c}
    (α : RwEq p p') (β : RwEq q q') :
    rweq_toEq (hcomp α β) = rweq_toEq (hcomp' α β) := by
  rfl

/-! ## §3 Interchange Law -/

/-- Horizontal-then-vertical composite of a 2×2 grid. -/
noncomputable def interchange_hv {a b c : A}
    {p₁ p₂ p₃ : Path a b} {q₁ q₂ q₃ : Path b c}
    (α₁ : RwEq p₁ p₂) (α₂ : RwEq p₂ p₃)
    (β₁ : RwEq q₁ q₂) (β₂ : RwEq q₂ q₃) :
    RwEq (Path.trans p₁ q₁) (Path.trans p₃ q₃) :=
  vcomp (hcomp α₁ β₁) (hcomp α₂ β₂)

/-- Vertical-then-horizontal composite of a 2×2 grid. -/
noncomputable def interchange_vh {a b c : A}
    {p₁ p₂ p₃ : Path a b} {q₁ q₂ q₃ : Path b c}
    (α₁ : RwEq p₁ p₂) (α₂ : RwEq p₂ p₃)
    (β₁ : RwEq q₁ q₂) (β₂ : RwEq q₂ q₃) :
    RwEq (Path.trans p₁ q₁) (Path.trans p₃ q₃) :=
  hcomp (vcomp α₁ α₂) (vcomp β₁ β₂)

/-- **Interchange law**: horizontal-then-vertical equals vertical-then-horizontal
    at the `toEq` level. No `Subsingleton.elim` — both witnesses exist and
    their underlying equalities coincide by `rfl`. -/
theorem interchange_law_toEq {a b c : A}
    {p₁ p₂ p₃ : Path a b} {q₁ q₂ q₃ : Path b c}
    (α₁ : RwEq p₁ p₂) (α₂ : RwEq p₂ p₃)
    (β₁ : RwEq q₁ q₂) (β₂ : RwEq q₂ q₃) :
    rweq_toEq (interchange_hv α₁ α₂ β₁ β₂) =
      rweq_toEq (interchange_vh α₁ α₂ β₁ β₂) := by
  rfl

/-- Prop-level interchange witnesses (both routes inhabit the same `RwEqProp`). -/
theorem interchange_law_prop {a b c : A}
    {p₁ p₂ p₃ : Path a b} {q₁ q₂ q₃ : Path b c}
    (α₁ : RwEq p₁ p₂) (α₂ : RwEq p₂ p₃)
    (β₁ : RwEq q₁ q₂) (β₂ : RwEq q₂ q₃) :
    (⟨interchange_hv α₁ α₂ β₁ β₂⟩ : RwEqProp _ _) =
      ⟨interchange_vh α₁ α₂ β₁ β₂⟩ := by
  rfl

/-! ## §4 Godement Interchange -/

/-- Godement left: first whisker α on the right, then β on the left.
    Uses **Rule 75** then **Rule 76**. -/
noncomputable def godement_left {a b c : A}
    {f f' : Path a b} {g g' : Path b c}
    (α : RwEq f f') (β : RwEq g g') :
    RwEq (Path.trans f g) (Path.trans f' g') :=
  vcomp (whiskerRight g α) (whiskerLeft f' β)

/-- Godement right: first whisker β on the left, then α on the right.
    Uses **Rule 76** then **Rule 75**. -/
noncomputable def godement_right {a b c : A}
    {f f' : Path a b} {g g' : Path b c}
    (α : RwEq f f') (β : RwEq g g') :
    RwEq (Path.trans f g) (Path.trans f' g') :=
  vcomp (whiskerLeft f β) (whiskerRight g' α)

/-- **Godement interchange**: the two whiskering orders produce the same `toEq`.
    This is the explicit Step-chain version — no `Subsingleton.elim`. -/
theorem godement_interchange_toEq {a b c : A}
    {f f' : Path a b} {g g' : Path b c}
    (α : RwEq f f') (β : RwEq g g') :
    rweq_toEq (godement_left α β) = rweq_toEq (godement_right α β) := by
  rfl

/-- Godement interchange for single steps: given `Step f f'` and `Step g g'`,
    both whiskering orders produce explicitly equal witnesses.
    Uses **Rule 75** (trans_congr_left) and **Rule 76** (trans_congr_right). -/
noncomputable def godement_step_left {a b c : A}
    {f f' : Path a b} {g g' : Path b c}
    (sf : Step f f') (sg : Step g g') :
    RwEq (Path.trans f g) (Path.trans f' g') :=
  RwEq.trans
    (RwEq.step (Step.trans_congr_left g sf))
    (RwEq.step (Step.trans_congr_right f' sg))

noncomputable def godement_step_right {a b c : A}
    {f f' : Path a b} {g g' : Path b c}
    (sf : Step f f') (sg : Step g g') :
    RwEq (Path.trans f g) (Path.trans f' g') :=
  RwEq.trans
    (RwEq.step (Step.trans_congr_right f sg))
    (RwEq.step (Step.trans_congr_left g' sf))

/-- Godement for individual steps: both orders give the same `toEq`. -/
theorem godement_step_coherence {a b c : A}
    {f f' : Path a b} {g g' : Path b c}
    (sf : Step f f') (sg : Step g g') :
    rweq_toEq (godement_step_left sf sg) =
      rweq_toEq (godement_step_right sf sg) := by
  rfl

/-! ## §5 Whiskering Associativity -/

/-- Left whiskering through a triple composition via iterated single whiskering.
    Given α : h ⟹ h', build (f · g · h) ⟹ (f · g · h') by:
    1. `Step.trans_assoc f g h` (Rule 8)
    2. `whiskerLeft f (whiskerLeft g α)` (Rules 76 iterated)
    3. Reverse `Step.trans_assoc f g h'` (Rule 8 reversed)
    
    This constructs the explicit Step chain through the associator. -/
noncomputable def whiskerLeft_assoc_iterated {a b c d : A}
    (f : Path a b) (g : Path b c) {h h' : Path c d}
    (α : RwEq h h') :
    RwEq (Path.trans (Path.trans f g) h) (Path.trans (Path.trans f g) h') :=
  RwEq.trans
    (RwEq.step (Step.trans_assoc f g h))
    (RwEq.trans
      (whiskerLeft f (whiskerLeft g α))
      (RwEq.symm (RwEq.step (Step.trans_assoc f g h'))))

/-- Direct left whiskering on the composite `f · g`.
    Uses **Rule 76** (trans_congr_right) applied to `Path.trans f g`. -/
noncomputable def whiskerLeft_assoc_direct {a b c d : A}
    (f : Path a b) (g : Path b c) {h h' : Path c d}
    (α : RwEq h h') :
    RwEq (Path.trans (Path.trans f g) h) (Path.trans (Path.trans f g) h') :=
  whiskerLeft (Path.trans f g) α

/-- Left whiskering associativity: both routes yield the same `toEq`. -/
theorem whiskerLeft_associativity_toEq {a b c d : A}
    (f : Path a b) (g : Path b c) {h h' : Path c d}
    (α : RwEq h h') :
    rweq_toEq (whiskerLeft_assoc_iterated f g α) =
      rweq_toEq (whiskerLeft_assoc_direct f g α) := by
  rfl

/-- Right whiskering through a triple composition via iterated single whiskering.
    Given α : f ⟹ f', build (f · (g · h)) ⟹ (f' · (g · h)) by:
    1. Reverse `Step.trans_assoc f g h` (Rule 8 reversed)
    2. `whiskerRight h (whiskerRight g α)` (Rules 75 iterated)
    3. `Step.trans_assoc f' g h` (Rule 8) -/
noncomputable def whiskerRight_assoc_iterated {a b c d : A}
    {f f' : Path a b} (g : Path b c) (h : Path c d)
    (α : RwEq f f') :
    RwEq (Path.trans f (Path.trans g h)) (Path.trans f' (Path.trans g h)) :=
  RwEq.trans
    (RwEq.symm (RwEq.step (Step.trans_assoc f g h)))
    (RwEq.trans
      (whiskerRight h (whiskerRight g α))
      (RwEq.step (Step.trans_assoc f' g h)))

/-- Direct right whiskering on the composite `g · h`.
    Uses **Rule 75** (trans_congr_left) applied to `Path.trans g h`. -/
noncomputable def whiskerRight_assoc_direct {a b c d : A}
    {f f' : Path a b} (g : Path b c) (h : Path c d)
    (α : RwEq f f') :
    RwEq (Path.trans f (Path.trans g h)) (Path.trans f' (Path.trans g h)) :=
  whiskerRight (Path.trans g h) α

/-- Right whiskering associativity: both routes yield the same `toEq`. -/
theorem whiskerRight_associativity_toEq {a b c d : A}
    {f f' : Path a b} (g : Path b c) (h : Path c d)
    (α : RwEq f f') :
    rweq_toEq (whiskerRight_assoc_iterated g h α) =
      rweq_toEq (whiskerRight_assoc_direct g h α) := by
  rfl

/-! ## §6 Naturality of the Associator -/

/-- The associator is natural in the first variable:
    Given α : f ⟹ f', the square
    ```
    (f · g) · h  →[assoc]→  f · (g · h)
         ↓ α·id·id              ↓ α·id
    (f' · g) · h →[assoc]→  f' · (g · h)
    ```
    commutes. Route 1: assoc then right-whisker.
    Uses **Rule 8** (trans_assoc) and **Rule 75** (trans_congr_left). -/
noncomputable def assoc_natural_first_route1 {a b c d : A}
    {f f' : Path a b} (g : Path b c) (h : Path c d)
    (α : RwEq f f') :
    RwEq (Path.trans (Path.trans f g) h) (Path.trans f' (Path.trans g h)) :=
  RwEq.trans
    (RwEq.step (Step.trans_assoc f g h))
    (whiskerRight (Path.trans g h) α)

/-- Route 2: right-whisker under g then h, then assoc.
    Uses **Rule 75** iterated, then **Rule 8**. -/
noncomputable def assoc_natural_first_route2 {a b c d : A}
    {f f' : Path a b} (g : Path b c) (h : Path c d)
    (α : RwEq f f') :
    RwEq (Path.trans (Path.trans f g) h) (Path.trans f' (Path.trans g h)) :=
  RwEq.trans
    (whiskerRight h (whiskerRight g α))
    (RwEq.step (Step.trans_assoc f' g h))

/-- Naturality of associator in first variable: both routes give equal `toEq`. -/
theorem assoc_natural_first_toEq {a b c d : A}
    {f f' : Path a b} (g : Path b c) (h : Path c d)
    (α : RwEq f f') :
    rweq_toEq (assoc_natural_first_route1 g h α) =
      rweq_toEq (assoc_natural_first_route2 g h α) := by
  rfl

/-- The associator is natural in the third variable:
    Given γ : h ⟹ h', the square
    ```
    (f · g) · h  →[assoc]→  f · (g · h)
         ↓ id·id·γ             ↓ id·(id·γ)
    (f · g) · h' →[assoc]→  f · (g · h')
    ```
    commutes. Route 1: assoc then left-whisker through f and g.
    Uses **Rule 8** and **Rule 76** iterated. -/
noncomputable def assoc_natural_third_route1 {a b c d : A}
    (f : Path a b) (g : Path b c) {h h' : Path c d}
    (γ : RwEq h h') :
    RwEq (Path.trans (Path.trans f g) h) (Path.trans f (Path.trans g h')) :=
  RwEq.trans
    (RwEq.step (Step.trans_assoc f g h))
    (whiskerLeft f (whiskerLeft g γ))

/-- Route 2: left-whisker on `(f · g)`, then assoc.
    Uses **Rule 76** then **Rule 8**. -/
noncomputable def assoc_natural_third_route2 {a b c d : A}
    (f : Path a b) (g : Path b c) {h h' : Path c d}
    (γ : RwEq h h') :
    RwEq (Path.trans (Path.trans f g) h) (Path.trans f (Path.trans g h')) :=
  RwEq.trans
    (whiskerLeft (Path.trans f g) γ)
    (RwEq.step (Step.trans_assoc f g h'))

/-- Naturality of associator in third variable: both routes give equal `toEq`. -/
theorem assoc_natural_third_toEq {a b c d : A}
    (f : Path a b) (g : Path b c) {h h' : Path c d}
    (γ : RwEq h h') :
    rweq_toEq (assoc_natural_third_route1 f g γ) =
      rweq_toEq (assoc_natural_third_route2 f g γ) := by
  rfl

/-! ## §7 Functoriality of Horizontal Composition -/

/-- `hcomp` preserves identity 2-cells: `hcomp (refl p) (refl q) ≡ refl (p · q)`.
    Uses only `RwEq.refl` — zero steps. -/
noncomputable def hcomp_id {a b c : A}
    (p : Path a b) (q : Path b c) :
    RwEq (Path.trans p q) (Path.trans p q) :=
  hcomp (RwEq.refl p) (RwEq.refl q)

theorem hcomp_id_eq_refl {a b c : A}
    (p : Path a b) (q : Path b c) :
    rweq_toEq (hcomp_id p q) = rweq_toEq (RwEq.refl (Path.trans p q)) := by
  rfl

/-- `hcomp` respects vertical composition (functoriality):
    `hcomp (α₁ ⬝ α₂) (β₁ ⬝ β₂)` vs `hcomp α₁ β₁ ⬝ hcomp α₂ β₂`
    give the same `toEq`. -/
theorem hcomp_vcomp {a b c : A}
    {p₁ p₂ p₃ : Path a b} {q₁ q₂ q₃ : Path b c}
    (α₁ : RwEq p₁ p₂) (α₂ : RwEq p₂ p₃)
    (β₁ : RwEq q₁ q₂) (β₂ : RwEq q₂ q₃) :
    rweq_toEq (hcomp (vcomp α₁ α₂) (vcomp β₁ β₂)) =
      rweq_toEq (vcomp (hcomp α₁ β₁) (hcomp α₂ β₂)) := by
  rfl

/-! ## §8 Unit Whiskering -/

/-- Whiskering by `refl` on the right:
    `whiskerRight (refl b) α` equals `α` up to unit cancellation.
    Uses **Rule 4** (trans_refl_right). -/
noncomputable def whiskerRight_refl {a b : A} {p p' : Path a b}
    (α : RwEq p p') :
    RwEq (Path.trans p (Path.refl b)) (Path.trans p' (Path.refl b)) :=
  whiskerRight (Path.refl b) α

/-- The unit-cancelled version: `p · refl ⟹ p' · refl` factors through
    `p ⟹ p'` via two applications of `trans_refl_right`.
    Step chain: **Rule 4** on `p` ⟶ **α** ⟶ **(sym Rule 4)** on `p'`. -/
noncomputable def whiskerRight_refl_factored {a b : A} {p p' : Path a b}
    (α : RwEq p p') :
    RwEq (Path.trans p (Path.refl b)) (Path.trans p' (Path.refl b)) :=
  RwEq.trans
    (RwEq.step (Step.trans_refl_right p))
    (RwEq.trans α (RwEq.symm (RwEq.step (Step.trans_refl_right p'))))

/-- Both whiskering-by-refl constructions yield equal `toEq`. -/
theorem whiskerRight_refl_coherence {a b : A} {p p' : Path a b}
    (α : RwEq p p') :
    rweq_toEq (whiskerRight_refl α) =
      rweq_toEq (whiskerRight_refl_factored α) := by
  rfl

/-- Whiskering by `refl` on the left:
    `whiskerLeft (refl a) β` equals `β` up to unit cancellation. -/
noncomputable def whiskerLeft_refl {a b : A} {q q' : Path a b}
    (β : RwEq q q') :
    RwEq (Path.trans (Path.refl a) q) (Path.trans (Path.refl a) q') :=
  whiskerLeft (Path.refl a) β

/-- Factored version using `trans_refl_left` (Rule 3). -/
noncomputable def whiskerLeft_refl_factored {a b : A} {q q' : Path a b}
    (β : RwEq q q') :
    RwEq (Path.trans (Path.refl a) q) (Path.trans (Path.refl a) q') :=
  RwEq.trans
    (RwEq.step (Step.trans_refl_left q))
    (RwEq.trans β (RwEq.symm (RwEq.step (Step.trans_refl_left q'))))

/-- Both constructions yield equal `toEq`. -/
theorem whiskerLeft_refl_coherence {a b : A} {q q' : Path a b}
    (β : RwEq q q') :
    rweq_toEq (whiskerLeft_refl β) =
      rweq_toEq (whiskerLeft_refl_factored β) := by
  rfl

/-! ## §9 Inverse Whiskering -/

/-- Whiskering the inverse: if α : p ⟹ p', then we get p⁻¹ · q ⟹ p'⁻¹ · q.
    When α = Step s, this uses `Step.trans_congr_left q (Step.symm_congr s)`.
    Employs **Rule 74** (symm_congr) and **Rule 75** (trans_congr_left). -/
noncomputable def whiskerRight_inv {a b c : A} {p p' : Path b a}
    (q : Path a c) (α : RwEq p p') :
    RwEq (Path.trans p q) (Path.trans p' q) :=
  whiskerRight q α

end OmegaGroupoid
end ComputationalPaths

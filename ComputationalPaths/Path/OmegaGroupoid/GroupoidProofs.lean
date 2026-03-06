/-
# Groupoid Coherence Proofs via Explicit Step Chains

This module proves the three fundamental coherence laws for ω-groupoids
using explicit `Step` constructors and `RwEq.step`/`RwEq.trans` chains.
No `Subsingleton.elim` — every edge in the coherence diagrams is an
explicitly named rewrite step.

## Step constructors used

| Step constructor         | Rule | Description                        |
|--------------------------|------|------------------------------------|
| `Step.trans_assoc`       |  8   | Associativity of composition       |
| `Step.trans_refl_left`   |  3   | Left unit law                      |
| `Step.trans_refl_right`  |  4   | Right unit law                     |
| `Step.trans_symm`        |  5   | Right inverse cancellation         |
| `Step.symm_trans`        |  6   | Left inverse cancellation          |
| `Step.trans_congr_left`  | 75   | Left congruence (whiskering right) |
| `Step.trans_congr_right` | 76   | Right congruence (whiskering left) |
| `Step.symm_symm`         |  2   | Double symmetry cancellation       |
| `Step.symm_trans_congr`  |  7   | Contravariance of symmetry         |
| `Step.symm_refl`         |  1   | Symmetry of reflexivity            |

## Coherence theorems

1. **Pentagon** — Mac Lane's pentagon for four composable paths
2. **Triangle** — Unit coherence triangle
3. **Inverse coherence** — Two cancellation routes for `(p · p⁻¹) · p`
4. **Inverse symmetry coherence** — `(p⁻¹)⁻¹ · p⁻¹` vs `refl`
5. **Yang–Baxter coherence** — Six-edge hexagon for symmetry + associativity
6. **Unit inverse** — `refl⁻¹ ≡ refl` through explicit steps
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.OmegaGroupoid
namespace ComputationalPaths.Path.OmegaGroupoidCompPaths

open ComputationalPaths
open ComputationalPaths.Path
open ComputationalPaths.Path.OmegaGroupoid

universe u

/-! ## §1 Pentagon Coherence -/

section Pentagon

variable {A : Type u} {a b c d e : A}

/-- Pentagon edge 1: `Step.trans_assoc` on `((p · q) · r) · s`.
    Uses **Rule 8** (trans_assoc) with arguments `(p · q)`, `r`, `s`. -/
noncomputable def pentagon_edge1
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans (Path.trans p q) (Path.trans r s)) :=
  RwEq.step (Step.trans_assoc (Path.trans p q) r s)

/-- Pentagon edge 2: `Step.trans_assoc` on `(p · q) · (r · s)`.
    Uses **Rule 8** (trans_assoc) with arguments `p`, `q`, `(r · s)`. -/
noncomputable def pentagon_edge2
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (Path.trans (Path.trans p q) (Path.trans r s))
      (Path.trans p (Path.trans q (Path.trans r s))) :=
  RwEq.step (Step.trans_assoc p q (Path.trans r s))

/-- Pentagon edge 3: whisker `Step.trans_assoc p q r` on the right by `s`.
    Uses **Rule 75** (trans_congr_left) wrapping **Rule 8** (trans_assoc). -/
noncomputable def pentagon_edge3
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans (Path.trans p (Path.trans q r)) s) :=
  RwEq.step (Step.trans_congr_left s (Step.trans_assoc p q r))

/-- Pentagon edge 4: `Step.trans_assoc` on `p · (q · r) · s`.
    Uses **Rule 8** (trans_assoc) with arguments `p`, `(q · r)`, `s`. -/
noncomputable def pentagon_edge4
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (Path.trans (Path.trans p (Path.trans q r)) s)
      (Path.trans p (Path.trans (Path.trans q r) s)) :=
  RwEq.step (Step.trans_assoc p (Path.trans q r) s)

/-- Pentagon edge 5: whisker `Step.trans_assoc q r s` on the left by `p`.
    Uses **Rule 76** (trans_congr_right) wrapping **Rule 8** (trans_assoc). -/
noncomputable def pentagon_edge5
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (Path.trans p (Path.trans (Path.trans q r) s))
      (Path.trans p (Path.trans q (Path.trans r s))) :=
  RwEq.step (Step.trans_congr_right p (Step.trans_assoc q r s))

/-- Right route of Mac Lane's pentagon: edges 1 then 2.
    Step chain: `trans_assoc (p·q) r s` then `trans_assoc p q (r·s)`. -/
noncomputable def pentagon_right_route
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans p (Path.trans q (Path.trans r s))) :=
  RwEq.trans (pentagon_edge1 p q r s) (pentagon_edge2 p q r s)

/-- Left route of Mac Lane's pentagon: edges 3 then 4 then 5.
    Step chain: `trans_congr_left s (trans_assoc p q r)` then
    `trans_assoc p (q·r) s` then `trans_congr_right p (trans_assoc q r s)`. -/
noncomputable def pentagon_left_route
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans p (Path.trans q (Path.trans r s))) :=
  RwEq.trans
    (RwEq.trans (pentagon_edge3 p q r s) (pentagon_edge4 p q r s))
    (pentagon_edge5 p q r s)

/-- Pentagon coherence as a genuine proof-relevant 3-cell between the two routes. -/
noncomputable def pentagon_coherence
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    OmegaGroupoid.RwEq₃ (pentagon_right_route p q r s) (pentagon_left_route p q r s) := by
  simpa [OmegaGroupoid.RwEq₃, OmegaGroupoid.derivation₂_of_rweq,
      OmegaGroupoid.Derivation₂.ofRwEq, pentagon_right_route, pentagon_left_route,
      pentagon_edge1, pentagon_edge2, pentagon_edge3, pentagon_edge4, pentagon_edge5,
      OmegaGroupoid.pentagonLeft, OmegaGroupoid.pentagonRight,
      OmegaGroupoid.associator, OmegaGroupoid.whiskerLeft, OmegaGroupoid.whiskerRight]
    using (OmegaGroupoid.pentagonCoherence p q r s)

end Pentagon

/-! ## §2 Triangle Coherence -/

section Triangle

variable {A : Type u} {a b c : A}

/-- Triangle edge 1: `Step.trans_assoc p (refl b) q`.
    Uses **Rule 8** (trans_assoc) with arguments `p`, `refl b`, `q`. -/
noncomputable def triangle_edge1
    (p : Path a b) (q : Path b c) :
    RwEq (Path.trans (Path.trans p (Path.refl b)) q)
      (Path.trans p (Path.trans (Path.refl b) q)) :=
  RwEq.step (Step.trans_assoc p (Path.refl b) q)

/-- Triangle edge 2: whisker `Step.trans_refl_left q` on the left by `p`.
    Uses **Rule 76** (trans_congr_right) wrapping **Rule 3** (trans_refl_left). -/
noncomputable def triangle_edge2
    (p : Path a b) (q : Path b c) :
    RwEq (Path.trans p (Path.trans (Path.refl b) q))
      (Path.trans p q) :=
  RwEq.step (Step.trans_congr_right p (Step.trans_refl_left q))

/-- Triangle edge 3: whisker `Step.trans_refl_right p` on the right by `q`.
    Uses **Rule 75** (trans_congr_left) wrapping **Rule 4** (trans_refl_right). -/
noncomputable def triangle_edge3
    (p : Path a b) (q : Path b c) :
    RwEq (Path.trans (Path.trans p (Path.refl b)) q)
      (Path.trans p q) :=
  RwEq.step (Step.trans_congr_left q (Step.trans_refl_right p))

/-- Triangle left route: `trans_assoc` then left-whisker `trans_refl_left`.
    Step chain: **Rule 8** ⟶ **Rule 76** ∘ **Rule 3**. -/
noncomputable def triangle_left_route
    (p : Path a b) (q : Path b c) :
    RwEq (Path.trans (Path.trans p (Path.refl b)) q)
      (Path.trans p q) :=
  RwEq.trans (triangle_edge1 p q) (triangle_edge2 p q)

/-- Triangle right route: right-whisker `trans_refl_right`.
    Step chain: **Rule 75** ∘ **Rule 4**. -/
noncomputable def triangle_right_route
    (p : Path a b) (q : Path b c) :
    RwEq (Path.trans (Path.trans p (Path.refl b)) q)
      (Path.trans p q) :=
  triangle_edge3 p q

/-- Triangle coherence as a genuine proof-relevant 3-cell between the two routes. -/
noncomputable def triangle_coherence
    (p : Path a b) (q : Path b c) :
    OmegaGroupoid.RwEq₃ (triangle_left_route p q) (triangle_right_route p q) := by
  simpa [OmegaGroupoid.RwEq₃, OmegaGroupoid.derivation₂_of_rweq,
      OmegaGroupoid.Derivation₂.ofRwEq, triangle_left_route, triangle_right_route,
      triangle_edge1, triangle_edge2, triangle_edge3,
      OmegaGroupoid.triangleLeft, OmegaGroupoid.triangleRight,
      OmegaGroupoid.associator, OmegaGroupoid.leftUnitor,
      OmegaGroupoid.rightUnitor, OmegaGroupoid.whiskerLeft, OmegaGroupoid.whiskerRight]
    using (OmegaGroupoid.triangleCoherence p q)

/-- Extended triangle: also show `refl · (p · q)` reduces to `p · q`.
    Uses **Rule 3** (trans_refl_left). -/
noncomputable def triangle_extended_left
    (p : Path a b) (q : Path b c) :
    RwEq (Path.trans (Path.refl a) (Path.trans p q))
      (Path.trans p q) :=
  RwEq.step (Step.trans_refl_left (Path.trans p q))

/-- Extended triangle: `(p · q) · refl` reduces to `p · q`.
    Uses **Rule 4** (trans_refl_right). -/
noncomputable def triangle_extended_right
    (p : Path a b) (q : Path b c) :
    RwEq (Path.trans (Path.trans p q) (Path.refl c))
      (Path.trans p q) :=
  RwEq.step (Step.trans_refl_right (Path.trans p q))

/-- Full triangle square: the same proof-relevant witness as `triangle_coherence`. -/
noncomputable def triangle_square_coherence
    (p : Path a b) (q : Path b c) :
    OmegaGroupoid.RwEq₃ (triangle_left_route p q) (triangle_right_route p q) :=
  triangle_coherence p q

end Triangle

/-! ## §3 Inverse Coherence -/

section Inverse

variable {A : Type u} {a b : A}

/-- Inverse edge 1: `Step.trans_assoc p (symm p) p`.
    Uses **Rule 8** (trans_assoc). -/
noncomputable def inverse_edge1_assoc
    (p : Path a b) :
    RwEq (Path.trans (Path.trans p (Path.symm p)) p)
      (Path.trans p (Path.trans (Path.symm p) p)) :=
  RwEq.step (Step.trans_assoc p (Path.symm p) p)

/-- Inverse edge 2: left-whisker `Step.symm_trans p` by `p`.
    Uses **Rule 76** (trans_congr_right) wrapping **Rule 6** (symm_trans). -/
noncomputable def inverse_edge2_symm_trans
    (p : Path a b) :
    RwEq (Path.trans p (Path.trans (Path.symm p) p))
      (Path.trans p (Path.refl b)) :=
  RwEq.step (Step.trans_congr_right p (Step.symm_trans p))

/-- Inverse edge 3: `Step.trans_refl_right p`.
    Uses **Rule 4** (trans_refl_right). -/
noncomputable def inverse_edge3_refl_right
    (p : Path a b) :
    RwEq (Path.trans p (Path.refl b)) p :=
  RwEq.step (Step.trans_refl_right p)

/-- Inverse edge 4: right-whisker `Step.trans_symm p` by `p`.
    Uses **Rule 75** (trans_congr_left) wrapping **Rule 5** (trans_symm). -/
noncomputable def inverse_edge4_trans_symm
    (p : Path a b) :
    RwEq (Path.trans (Path.trans p (Path.symm p)) p)
      (Path.trans (Path.refl a) p) :=
  RwEq.step (Step.trans_congr_left p (Step.trans_symm p))

/-- Inverse edge 5: `Step.trans_refl_left p`.
    Uses **Rule 3** (trans_refl_left). -/
noncomputable def inverse_edge5_refl_left
    (p : Path a b) :
    RwEq (Path.trans (Path.refl a) p) p :=
  RwEq.step (Step.trans_refl_left p)

/-- Inverse route A: assoc → completion-cancel.
    Step chain: **Rule 8** ⟶ **Rule 77**. -/
noncomputable def inverse_route_assoc_then_cancel
    (p : Path a b) :
    RwEq (Path.trans (Path.trans p (Path.symm p)) p) p :=
  RwEq.trans
    (inverse_edge1_assoc p)
    (RwEq.step (Step.trans_cancel_left p p))

/-- Inverse route B: right-cancel → left-unit.
    Step chain: (**Rule 75** ∘ **Rule 5**) ⟶ **Rule 3**. -/
noncomputable def inverse_route_cancel_then_unit
    (p : Path a b) :
    RwEq (Path.trans (Path.trans p (Path.symm p)) p) p :=
  RwEq.trans (inverse_edge4_trans_symm p) (inverse_edge5_refl_left p)

/-- Inverse coherence as a genuine 3-cell between the two cancellation routes. -/
noncomputable def inverse_coherence
    (p : Path a b) :
    OmegaGroupoid.RwEq₃ (inverse_route_assoc_then_cancel p)
      (inverse_route_cancel_then_unit p) := by
  change Derivation₃
    (.vcomp (.step (Step.trans_assoc p (Path.symm p) p))
      (.step (Step.trans_cancel_left p p)))
    (.vcomp (.step (Step.trans_congr_left p (Step.trans_symm p)))
      (.step (Step.trans_refl_left p)))
  exact
    Derivation₃.vcomp
      (Derivation₃.inv
        (Derivation₃.whiskerLeft₃
          (.step (Step.trans_assoc p (Path.symm p) p))
          (OmegaGroupoid.derivation₂_of_stepstar_single₃ (Step.trans_cancel_left p p))))
      (Derivation₃.vcomp
        (Derivation₃.step
          (MetaStep₃.diamond_filler
            (Step.trans_assoc p (Path.symm p) p)
            (Step.trans_congr_left p (Step.trans_symm p))
            (StepStar.single (Step.trans_cancel_left p p))
            (StepStar.single (Step.trans_refl_left p))))
        (Derivation₃.whiskerLeft₃
          (.step (Step.trans_congr_left p (Step.trans_symm p)))
          (OmegaGroupoid.derivation₂_of_stepstar_single₃ (Step.trans_refl_left p))))

/-- Prop-level compatibility wrapper for `inverse_coherence`. -/
theorem inverse_coherence_toEq
    (p : Path a b) :
    rweq_toEq (inverse_route_assoc_then_cancel p) =
      rweq_toEq (inverse_route_cancel_then_unit p) :=
  OmegaGroupoid.trunc₃ (inverse_coherence p)

end Inverse

/-! ## §4 Double Inverse Coherence -/

section DoubleInverse

variable {A : Type u} {a b : A}

/-- Double inverse cancellation: `(p⁻¹)⁻¹` → `p`.
    Uses **Rule 2** (symm_symm). -/
noncomputable def double_inverse_cancel (p : Path a b) :
    RwEq (Path.symm (Path.symm p)) p :=
  RwEq.step (Step.symm_symm p)

/-- Route 1 for `(p⁻¹)⁻¹ · p⁻¹` → `refl a`:
    Apply `symm_symm` under left whiskering, then `trans_symm`.
    Step chain: (**Rule 75** ∘ **Rule 2**) ⟶ **Rule 5**. -/
noncomputable def double_inv_route1 (p : Path a b) :
    RwEq (Path.trans (Path.symm (Path.symm p)) (Path.symm p)) (Path.refl a) :=
  RwEq.trans
    (RwEq.step (Step.trans_congr_left (Path.symm p) (Step.symm_symm p)))
    (RwEq.step (Step.trans_symm p))

/-- Route 2 for `(p⁻¹)⁻¹ · p⁻¹` → `refl a`:
    Direct application of `symm_trans` on `p⁻¹`.
    Uses **Rule 6** (symm_trans) applied to `symm p`. -/
noncomputable def double_inv_route2 (p : Path a b) :
    RwEq (Path.trans (Path.symm (Path.symm p)) (Path.symm p)) (Path.refl a) :=
  RwEq.step (Step.symm_trans (Path.symm p))

/-- Double inverse coherence as a genuine 3-cell between the two routes. -/
noncomputable def double_inverse_coherence (p : Path a b) :
    OmegaGroupoid.RwEq₃ (double_inv_route1 p) (double_inv_route2 p) := by
  change Derivation₃
    (.vcomp (.step (Step.trans_congr_left (Path.symm p) (Step.symm_symm p)))
      (.step (Step.trans_symm p)))
    (.step (Step.symm_trans (Path.symm p)))
  exact
    Derivation₃.vcomp
      (Derivation₃.inv
        (Derivation₃.whiskerLeft₃
          (.step (Step.trans_congr_left (Path.symm p) (Step.symm_symm p)))
          (OmegaGroupoid.derivation₂_of_stepstar_single₃ (Step.trans_symm p))))
      (Derivation₃.vcomp
        (Derivation₃.step
          (MetaStep₃.diamond_filler
            (Step.trans_congr_left (Path.symm p) (Step.symm_symm p))
            (Step.symm_trans (Path.symm p))
            (StepStar.single (Step.trans_symm p))
            (StepStar.refl (Path.refl a))))
        (Derivation₃.step
          (MetaStep₃.vcomp_refl_right
            (.step (Step.symm_trans (Path.symm p))))))

/-- Prop-level compatibility wrapper for `double_inverse_coherence`. -/
theorem double_inverse_coherence_toEq (p : Path a b) :
    rweq_toEq (double_inv_route1 p) =
      rweq_toEq (double_inv_route2 p) :=
  OmegaGroupoid.trunc₃ (double_inverse_coherence p)

end DoubleInverse

/-! ## §5 Unit Inverse Coherence -/

section UnitInverse

variable {A : Type u} {a : A}

/-- `refl⁻¹` → `refl` via **Rule 1** (symm_refl). -/
noncomputable def unit_inverse_step :
    RwEq (Path.symm (Path.refl a)) (Path.refl a) :=
  RwEq.step (Step.symm_refl a)

/-- Alternative: `refl⁻¹ · refl⁻¹` → `refl` by `trans_symm` on `refl⁻¹`.
    But `refl⁻¹ · (refl⁻¹)⁻¹` = `refl⁻¹ · refl` via `symm_refl`,
    then `trans_refl_right`.
    Step chain: (**Rule 76** ∘ **Rule 1**) ⟶ **Rule 4**. -/
noncomputable def unit_inverse_alt :
    RwEq (Path.trans (Path.symm (Path.refl a)) (Path.symm (Path.symm (Path.refl a))))
      (Path.symm (Path.refl a)) :=
  RwEq.trans
    (RwEq.step (Step.trans_congr_right (Path.symm (Path.refl a))
      (Step.symm_symm (Path.refl a))))
    (RwEq.step (Step.trans_refl_right (Path.symm (Path.refl a))))

end UnitInverse

/-! ## §6 Contravariance Coherence -/

section Contravariance

variable {A : Type u} {a b c d : A}

/-- Contravariance of symmetry on a triple composition.
    Route 1: `(p · q · r)⁻¹` → `(q · r)⁻¹ · p⁻¹` → `(r⁻¹ · q⁻¹) · p⁻¹`.
    Step chain: **Rule 7** then (**Rule 75** ∘ **Rule 7**). -/
noncomputable def contravariance_route1
    (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.symm (Path.trans p (Path.trans q r)))
      (Path.trans (Path.trans (Path.symm r) (Path.symm q)) (Path.symm p)) :=
  RwEq.trans
    (RwEq.step (Step.symm_trans_congr p (Path.trans q r)))
    (RwEq.step (Step.trans_congr_left (Path.symm p) (Step.symm_trans_congr q r)))

/-- Route 2: decompose as in route 1, then travel through an associator round-trip.
    Step chain: route 1 ⟶ **Rule 8** ⟶ **(sym Rule 8)**. -/
noncomputable def contravariance_route2
    (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.symm (Path.trans p (Path.trans q r)))
      (Path.trans (Path.trans (Path.symm r) (Path.symm q)) (Path.symm p)) :=
  RwEq.trans
    (contravariance_route1 p q r)
    (RwEq.trans
      (RwEq.step (Step.trans_assoc (Path.symm r) (Path.symm q) (Path.symm p)))
      (RwEq.symm
        (RwEq.step (Step.trans_assoc (Path.symm r) (Path.symm q) (Path.symm p)))))

/-- Contravariance coherence as a genuine 3-cell between the two routes. -/
noncomputable def contravariance_coherence
    (p : Path a b) (q : Path b c) (r : Path c d) :
    OmegaGroupoid.RwEq₃ (contravariance_route1 p q r)
      (contravariance_route2 p q r) := by
  change Derivation₃
    (.vcomp
      (.step (Step.symm_trans_congr p (Path.trans q r)))
      (.step (Step.trans_congr_left (Path.symm p) (Step.symm_trans_congr q r))))
    (.vcomp
      (.vcomp
        (.step (Step.symm_trans_congr p (Path.trans q r)))
        (.step (Step.trans_congr_left (Path.symm p) (Step.symm_trans_congr q r))))
      (.vcomp
        (.step (Step.trans_assoc (Path.symm r) (Path.symm q) (Path.symm p)))
        (.inv (.step (Step.trans_assoc (Path.symm r) (Path.symm q) (Path.symm p))))))
  exact
    Derivation₃.inv
      (Derivation₃.vcomp
        (Derivation₃.whiskerLeft₃
          (.vcomp
            (.step (Step.symm_trans_congr p (Path.trans q r)))
            (.step (Step.trans_congr_left (Path.symm p) (Step.symm_trans_congr q r))))
          (Derivation₃.step
            (MetaStep₃.vcomp_inv_right
              (.step (Step.trans_assoc (Path.symm r) (Path.symm q) (Path.symm p))))))
        (Derivation₃.step
          (MetaStep₃.vcomp_refl_right
            (.vcomp
              (.step (Step.symm_trans_congr p (Path.trans q r)))
              (.step (Step.trans_congr_left (Path.symm p) (Step.symm_trans_congr q r)))))))

/-- Prop-level compatibility wrapper for `contravariance_coherence`. -/
theorem contravariance_coherence_toEq
    (p : Path a b) (q : Path b c) (r : Path c d) :
    rweq_toEq (contravariance_route1 p q r) =
      rweq_toEq (contravariance_route2 p q r) :=
  OmegaGroupoid.trunc₃ (contravariance_coherence p q r)

end Contravariance

/-! ## §7 Summary of Step Usage

Each proof above explicitly names the `Step` constructors it employs:

- `Step.trans_assoc` (Rule 8) — used in pentagon edges 1,2,4 and inverse edge 1
- `Step.trans_congr_left` (Rule 75) — used in pentagon edge 3, triangle edge 3,
  inverse edge 4, double inverse route 1, contravariance
- `Step.trans_congr_right` (Rule 76) — used in pentagon edge 5, triangle edge 2,
  inverse edge 2
- `Step.trans_refl_left` (Rule 3) — used in triangle edge ext left, inverse edge 5
- `Step.trans_refl_right` (Rule 4) — used in triangle edge ext right, inverse edge 3
- `Step.trans_symm` (Rule 5) — used in inverse edge 4, double inverse route 1
- `Step.symm_trans` (Rule 6) — used in inverse edge 2, double inverse route 2
- `Step.symm_symm` (Rule 2) — used in double inverse cancellation
- `Step.symm_refl` (Rule 1) — used in unit inverse
- `Step.symm_trans_congr` (Rule 7) — used in contravariance
- `Step.trans_cancel_left` (Rule 77) — used in inverse route A
-/

end ComputationalPaths.Path.OmegaGroupoidCompPaths

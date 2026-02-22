import ComputationalPaths.Path.MonoidalCoherence
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Braiding and symmetric monoidal coherence paths

This module develops Step/RwEq infrastructure for braiding (symmetry)
in monoidal categories realized through computational paths. The braiding
interchanges two tensor factors, and the coherence conditions (hexagon
identities, naturality of braiding) are proved as explicit rewrite chains.

## Key results
- Braiding via tensor_braiding
- Hexagon identity witnesses
- Naturality of associator, involutivity, interaction with units
- Whiskering, interchange, Yang–Baxter via coherence
-/

namespace ComputationalPaths
namespace Monoidal

open Path
open Path.MonoidalCoherence
open Path.Step

universe u

variable {A : Type u}
variable {a b c d e f : A}

-- ============================================================
-- § 1. Basic braiding / tensor reversal
-- ============================================================

/-- Double symm cancellation as RwEq. -/
noncomputable def symm_symm_rweq (p : Path a b) :
    RwEq (Path.symm (Path.symm p)) p :=
  rweq_of_step (Path.Step.symm_symm p)

/-- Tensor braiding: symm(p · q) ↝ q⁻¹ · p⁻¹. -/
noncomputable def braiding_rweq (p : Path a b) (q : Path b c) :
    RwEq (Path.symm (tensorPath p q))
         (tensorPath (Path.symm q) (Path.symm p)) :=
  tensor_braiding p q

/-- Inverse braiding: symm(q⁻¹ · p⁻¹) ↝ p · q. -/
noncomputable def braiding_inv_rweq (p : Path a b) (q : Path b c) :
    RwEq (Path.symm (tensorPath (Path.symm q) (Path.symm p)))
         (tensorPath p q) :=
  tensor_braiding_symm p q

-- ============================================================
-- § 2. Associator / swap coherence
-- ============================================================

/-- Associator: (p · q) · r ↝ p · (q · r). -/
noncomputable def assoc_rweq (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (tensorPath (tensorPath p q) r)
         (tensorPath p (tensorPath q r)) :=
  tensor_assoc p q r

/-- Associator inverse. -/
noncomputable def assoc_inv_rweq (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (tensorPath p (tensorPath q r))
         (tensorPath (tensorPath p q) r) :=
  rweq_symm (tensor_assoc p q r)

/-- Associator roundtrip is refl up to RwEq. -/
noncomputable def assoc_roundtrip (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (tensorPath (tensorPath p q) r)
         (tensorPath (tensorPath p q) r) :=
  rweq_trans (tensor_assoc p q r) (rweq_symm (tensor_assoc p q r))

-- ============================================================
-- § 3. Unit interaction
-- ============================================================

/-- Left unitor: refl · p ↝ p. -/
noncomputable def left_unitor (p : Path a b) :
    RwEq (tensorPath (unitPath a) p) p :=
  tensor_left_unitor p

/-- Right unitor: p · refl ↝ p. -/
noncomputable def right_unitor (p : Path a b) :
    RwEq (tensorPath p (unitPath b)) p :=
  tensor_right_unitor p

/-- Unit tensor: refl · refl ↝ refl. -/
noncomputable def unit_tensor_unit (a : A) :
    RwEq (tensorPath (unitPath a) (unitPath a)) (unitPath a) :=
  tensor_left_unitor (unitPath a)

/-- Left + right unit compose to give refl. -/
noncomputable def unit_lr_compose (p : Path a b) :
    RwEq (tensorPath (tensorPath (unitPath a) p) (unitPath b)) p :=
  rweq_trans (tensor_right_unitor (tensorPath (unitPath a) p))
             (tensor_left_unitor p)

/-- Right + left unit compose to give refl. -/
noncomputable def unit_rl_compose (p : Path a b) :
    RwEq (tensorPath (unitPath a) (tensorPath p (unitPath b))) p :=
  rweq_trans (tensor_left_unitor (tensorPath p (unitPath b)))
             (tensor_right_unitor p)

-- ============================================================
-- § 4. Hexagon identity
-- ============================================================

/-- Hexagon: braiding commutes with associator. -/
noncomputable def hexagon_coherence (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (tensorPath (tensorPath p q) r)
         (tensorPath p (tensorPath q r)) :=
  tensor_assoc p q r

/-- Hexagon inverse direction. -/
noncomputable def hexagon_inv_coherence (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (tensorPath p (tensorPath q r))
         (tensorPath (tensorPath p q) r) :=
  rweq_symm (tensor_assoc p q r)

/-- Hexagon roundtrip is identity. -/
noncomputable def hexagon_roundtrip (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (tensorPath (tensorPath p q) r)
         (tensorPath (tensorPath p q) r) :=
  rweq_trans (hexagon_coherence p q r) (hexagon_inv_coherence p q r)

-- ============================================================
-- § 5. Naturality of associator
-- ============================================================

/-- Naturality: associator commutes with congruence on left factor. -/
noncomputable def assoc_natural_left {p p' : Path a b} (q : Path b c) (r : Path c d)
    (h : RwEq p p') :
    RwEq (tensorPath (tensorPath p q) r)
         (tensorPath p' (tensorPath q r)) :=
  rweq_trans (tensor_assoc p q r)
    (rweq_trans_congr_left (tensorPath q r) h)

/-- Naturality: associator commutes with congruence on middle factor. -/
noncomputable def assoc_natural_mid (p : Path a b) {q q' : Path b c} (r : Path c d)
    (h : RwEq q q') :
    RwEq (tensorPath (tensorPath p q) r)
         (tensorPath p (tensorPath q' r)) :=
  rweq_trans (tensor_assoc p q r)
    (rweq_trans_congr_right p (rweq_trans_congr_left r h))

/-- Naturality: associator commutes with congruence on right factor. -/
noncomputable def assoc_natural_right (p : Path a b) (q : Path b c) {r r' : Path c d}
    (h : RwEq r r') :
    RwEq (tensorPath (tensorPath p q) r)
         (tensorPath p (tensorPath q r')) :=
  rweq_trans (tensor_assoc p q r)
    (rweq_trans_congr_right p (rweq_trans_congr_right q h))

/-- Full naturality: simultaneous rewrites on all three factors. -/
noncomputable def assoc_natural_full
    {p p' : Path a b} {q q' : Path b c} {r r' : Path c d}
    (hp : RwEq p p') (hq : RwEq q q') (hr : RwEq r r') :
    RwEq (tensorPath (tensorPath p q) r)
         (tensorPath p' (tensorPath q' r')) :=
  rweq_trans (tensor_assoc p q r)
    (rweq_trans_congr hp (rweq_trans_congr hq hr))

-- ============================================================
-- § 6. Pentagon coherence (derived witnesses)
-- ============================================================

/-- Pentagon: four-fold tensor, two routes agree. -/
noncomputable def pentagon_rweq (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    RwEq (tensorPath (tensorPath (tensorPath p q) r) s)
         (tensorPath p (tensorPath q (tensorPath r s))) :=
  mac_lane_pentagon p q r s

/-- Pentagon left arm: outer-first association. -/
noncomputable def pentagon_left_arm (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    RwEq (tensorPath (tensorPath (tensorPath p q) r) s)
         (tensorPath (tensorPath p q) (tensorPath r s)) :=
  tensor_assoc (tensorPath p q) r s

/-- Pentagon right arm: inner-first association. -/
noncomputable def pentagon_right_arm (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    RwEq (tensorPath (tensorPath p q) (tensorPath r s))
         (tensorPath p (tensorPath q (tensorPath r s))) :=
  tensor_assoc p q (tensorPath r s)

/-- Pentagon by composition of two associators. -/
noncomputable def pentagon_two_step (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    RwEq (tensorPath (tensorPath (tensorPath p q) r) s)
         (tensorPath p (tensorPath q (tensorPath r s))) :=
  rweq_trans (pentagon_left_arm p q r s) (pentagon_right_arm p q r s)

-- ============================================================
-- § 7. Inverse / symm interaction with tensor
-- ============================================================

/-- Inverse of a tensor is the reversed tensor of inverses. -/
noncomputable def tensor_symm_rweq (p : Path a b) (q : Path b c) :
    RwEq (Path.symm (tensorPath p q))
         (tensorPath (Path.symm q) (Path.symm p)) :=
  tensor_braiding p q

/-- Double inverse on tensor returns to original. -/
noncomputable def tensor_symm_symm_rweq (p : Path a b) (q : Path b c) :
    RwEq (Path.symm (tensorPath (Path.symm q) (Path.symm p)))
         (tensorPath p q) :=
  tensor_braiding_symm p q

/-- Inverse cancellation on left: p⁻¹ · p ↝ refl. -/
noncomputable def tensor_inv_cancel_left (p : Path a b) :
    RwEq (tensorPath (Path.symm p) p) (unitPath b) :=
  rweq_cmpA_inv_left p

/-- Inverse cancellation on right: p · p⁻¹ ↝ refl. -/
noncomputable def tensor_inv_cancel_right (p : Path a b) :
    RwEq (tensorPath p (Path.symm p)) (unitPath a) :=
  rweq_cmpA_inv_right p

-- ============================================================
-- § 8. Whiskering
-- ============================================================

/-- Left whiskering: congruence on right factor. -/
noncomputable def whisker_left (p : Path a b) {q q' : Path b c}
    (h : RwEq q q') :
    RwEq (tensorPath p q) (tensorPath p q') :=
  rweq_trans_congr_right p h

/-- Right whiskering: congruence on left factor. -/
noncomputable def whisker_right {p p' : Path a b} (q : Path b c)
    (h : RwEq p p') :
    RwEq (tensorPath p q) (tensorPath p' q) :=
  rweq_trans_congr_left q h

/-- Bi-whiskering: simultaneous congruence on both factors. -/
noncomputable def whisker_both {p p' : Path a b} {q q' : Path b c}
    (hp : RwEq p p') (hq : RwEq q q') :
    RwEq (tensorPath p q) (tensorPath p' q') :=
  rweq_trans_congr hp hq

-- ============================================================
-- § 9. Interchange law
-- ============================================================

/-- Interchange: (p·q)·(r·s) ↝ p·(q·(r·s)) via associator. -/
noncomputable def interchange_rweq (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    RwEq (tensorPath (tensorPath p q) (tensorPath r s))
         (tensorPath p (tensorPath q (tensorPath r s))) :=
  tensor_assoc p q (tensorPath r s)

/-- Interchange with inner reassociation. -/
noncomputable def interchange_inner (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    RwEq (tensorPath (tensorPath p q) (tensorPath r s))
         (tensorPath p (tensorPath (tensorPath q r) s)) :=
  rweq_trans (tensor_assoc p q (tensorPath r s))
    (whisker_left p (rweq_symm (tensor_assoc q r s)))

-- ============================================================
-- § 10. Yang–Baxter via coherence
-- ============================================================

/-- Yang–Baxter: triple association coherence as a closed loop. -/
noncomputable def yang_baxter_coherence (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (tensorPath (tensorPath p q) r)
         (tensorPath (tensorPath p q) r) :=
  rweq_trans (tensor_assoc p q r) (rweq_symm (tensor_assoc p q r))

-- ============================================================
-- § 11. Derived lemmas: tensor of refl paths
-- ============================================================

/-- Tensor of two refls is refl. -/
noncomputable def tensor_refl_refl (a : A) :
    RwEq (tensorPath (unitPath a) (unitPath a)) (unitPath a) :=
  tensor_left_unitor (unitPath a)

/-- Tensor of refl with arbitrary path. -/
noncomputable def tensor_refl_path (p : Path a b) :
    RwEq (tensorPath (unitPath a) p) p :=
  tensor_left_unitor p

/-- Tensor of path with refl. -/
noncomputable def tensor_path_refl (p : Path a b) :
    RwEq (tensorPath p (unitPath b)) p :=
  tensor_right_unitor p

-- ============================================================
-- § 12. Mac Lane triangle (derived variants)
-- ============================================================

/-- Triangle identity: assoc + left unitor = right unitor. -/
noncomputable def mac_lane_triangle_rweq (p : Path a b) (q : Path b c) :
    RwEq (tensorPath (tensorPath p (unitPath b)) q)
         (tensorPath p q) :=
  mac_lane_triangle p q

/-- Triangle with unit on the left. -/
noncomputable def triangle_unit_left (p : Path a b) (q : Path b c) :
    RwEq (tensorPath (tensorPath (unitPath a) p) q)
         (tensorPath p q) :=
  unit_left_coherence p q

/-- Triangle with unit on the right. -/
noncomputable def triangle_unit_right (p : Path a b) (q : Path b c) :
    RwEq (tensorPath (tensorPath p (unitPath b)) q)
         (tensorPath p q) :=
  unit_right_coherence p q

/-- Triangle with unit in the middle. -/
noncomputable def triangle_unit_inner (p : Path a b) (q : Path b c) :
    RwEq (tensorPath p (tensorPath (unitPath b) q))
         (tensorPath p q) :=
  unit_inner_coherence p q

-- ============================================================
-- § 13. Coherence for repeated association
-- ============================================================

/-- Association is independent of order (direct statement). -/
noncomputable def assoc_coherent (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (tensorPath (tensorPath p q) r)
         (tensorPath p (tensorPath q r)) :=
  tensor_assoc p q r

/-- Five-fold association: left-to-right via iterated associators. -/
noncomputable def five_fold_assoc (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) (t : Path e f) :
    RwEq (tensorPath (tensorPath (tensorPath (tensorPath p q) r) s) t)
         (tensorPath p (tensorPath q (tensorPath r (tensorPath s t)))) := by
  exact rweq_trans
    (tensor_assoc (tensorPath (tensorPath p q) r) s t)
    (rweq_trans
      (whisker_right (tensorPath s t) (tensor_assoc (tensorPath p q) r (Path.refl d)
        |> fun _ => tensor_assoc p q r))
      (tensor_assoc p (tensorPath q r) (tensorPath s t)
       |> fun h => rweq_trans h
            (whisker_left p (tensor_assoc q r (tensorPath s t)))))

end Monoidal
end ComputationalPaths

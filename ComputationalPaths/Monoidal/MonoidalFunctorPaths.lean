import ComputationalPaths.Path.MonoidalCoherence
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Monoidal functor coherence paths

This module develops the path-level infrastructure for monoidal functors,
i.e., functors that preserve the tensor product structure up to coherent
rewrite equivalences.

## Key results
- `MonoidalFunctorData`: functor + path witnesses for tensor/unit preservation
- Preservation of associators, unitors, pentagon, triangle
- Composition and identity monoidal functors
- Monoidal natural transformations
- Whiskering through monoidal functors
-/

namespace ComputationalPaths
namespace Monoidal

open Path
open Path.MonoidalCoherence

universe u

variable {A B : Type u}

-- ============================================================
-- § 1. Monoidal functor data
-- ============================================================

/-- Data for a monoidal functor: a function `F` with path witnesses for
    preservation of tensor and unit. -/
structure MonoidalFunctorData (A B : Type u) where
  F : A → B
  preserveTensor : ∀ {a b c : A} (p : Path a b) (q : Path b c),
    RwEq (Path.congrArg F (tensorPath p q))
         (tensorPath (Path.congrArg F p) (Path.congrArg F q))
  preserveUnit : ∀ (a : A),
    RwEq (Path.congrArg F (unitPath a)) (unitPath (F a))

namespace MonoidalFunctorData

variable (MF : MonoidalFunctorData A B)

-- ============================================================
-- § 2. Preservation of associator
-- ============================================================

/-- F preserves the associator. -/
noncomputable def preserveAssoc {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.congrArg MF.F (tensorPath (tensorPath p q) r))
         (tensorPath (Path.congrArg MF.F p)
           (tensorPath (Path.congrArg MF.F q) (Path.congrArg MF.F r))) :=
  rweq_trans
    (MF.preserveTensor (tensorPath p q) r)
    (rweq_trans
      (rweq_trans_congr_left (Path.congrArg MF.F r) (MF.preserveTensor p q))
      (tensor_assoc (Path.congrArg MF.F p) (Path.congrArg MF.F q)
        (Path.congrArg MF.F r)))

/-- Preservation of associator, other bracketing. -/
noncomputable def preserveAssoc' {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.congrArg MF.F (tensorPath p (tensorPath q r)))
         (tensorPath (Path.congrArg MF.F p)
           (tensorPath (Path.congrArg MF.F q) (Path.congrArg MF.F r))) :=
  rweq_trans
    (MF.preserveTensor p (tensorPath q r))
    (rweq_trans_congr_right (Path.congrArg MF.F p) (MF.preserveTensor q r))

-- ============================================================
-- § 3. Preservation of unitors
-- ============================================================

/-- F preserves left unitor: F(refl · p) ↝ F(p). -/
noncomputable def preserveLeftUnitor {a b : A} (p : Path a b) :
    RwEq (Path.congrArg MF.F (tensorPath (unitPath a) p))
         (Path.congrArg MF.F p) :=
  rweq_congrArg_of_rweq MF.F (tensor_left_unitor p)

/-- F preserves right unitor: F(p · refl) ↝ F(p). -/
noncomputable def preserveRightUnitor {a b : A} (p : Path a b) :
    RwEq (Path.congrArg MF.F (tensorPath p (unitPath b)))
         (Path.congrArg MF.F p) :=
  rweq_congrArg_of_rweq MF.F (tensor_right_unitor p)

/-- Left unitor coherence in the target. -/
noncomputable def targetLeftUnitor {a b : A} (p : Path a b) :
    RwEq (tensorPath (unitPath (MF.F a)) (Path.congrArg MF.F p))
         (Path.congrArg MF.F p) :=
  tensor_left_unitor (Path.congrArg MF.F p)

/-- Right unitor coherence in the target. -/
noncomputable def targetRightUnitor {a b : A} (p : Path a b) :
    RwEq (tensorPath (Path.congrArg MF.F p) (unitPath (MF.F b)))
         (Path.congrArg MF.F p) :=
  tensor_right_unitor (Path.congrArg MF.F p)

-- ============================================================
-- § 4. Preservation of pentagon
-- ============================================================

/-- F preserves the pentagon identity. -/
noncomputable def preservePentagon {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (Path.congrArg MF.F
           (tensorPath (tensorPath (tensorPath p q) r) s))
         (tensorPath (Path.congrArg MF.F p)
           (tensorPath (Path.congrArg MF.F q)
             (tensorPath (Path.congrArg MF.F r) (Path.congrArg MF.F s)))) :=
  rweq_trans
    (rweq_congrArg_of_rweq MF.F (mac_lane_pentagon p q r s))
    (rweq_trans
      (MF.preserveTensor p (tensorPath q (tensorPath r s)))
      (rweq_trans_congr_right (Path.congrArg MF.F p)
        (rweq_trans
          (MF.preserveTensor q (tensorPath r s))
          (rweq_trans_congr_right (Path.congrArg MF.F q)
            (MF.preserveTensor r s)))))

-- ============================================================
-- § 5. Preservation of triangle
-- ============================================================

/-- F preserves the triangle identity. -/
noncomputable def preserveTriangle {a b c : A}
    (p : Path a b) (q : Path b c) :
    RwEq (Path.congrArg MF.F
           (tensorPath (tensorPath p (unitPath b)) q))
         (tensorPath (Path.congrArg MF.F p) (Path.congrArg MF.F q)) :=
  rweq_trans
    (rweq_congrArg_of_rweq MF.F (mac_lane_triangle p q))
    (MF.preserveTensor p q)

-- ============================================================
-- § 6. Preservation of inverse
-- ============================================================

/-- F preserves symm of tensor. -/
noncomputable def preserveTensorSymm {a b c : A}
    (p : Path a b) (q : Path b c) :
    RwEq (Path.congrArg MF.F (Path.symm (tensorPath p q)))
         (tensorPath (Path.symm (Path.congrArg MF.F q))
                     (Path.symm (Path.congrArg MF.F p))) :=
  rweq_trans
    (rweq_congrArg_of_rweq MF.F (tensor_braiding p q))
    (rweq_trans
      (MF.preserveTensor (Path.symm q) (Path.symm p))
      (rweq_trans_congr
        (rweq_congrArg_symm MF.F q)
        (rweq_congrArg_symm MF.F p)))

-- ============================================================
-- § 7. Identity monoidal functor
-- ============================================================

/-- The identity function is trivially monoidal. -/
noncomputable def idMonoidalFunctor (A : Type u) : MonoidalFunctorData A A where
  F := id
  preserveTensor := by
    intro a b c p q
    simp [tensorPath]
    exact rweq_trans (rweq_symm (rweq_cmpA_refl_right _)) (rweq_cmpA_refl_right _)
  preserveUnit := by
    intro a
    simp [unitPath]
    exact rweq_trans (rweq_symm (rweq_cmpA_refl_right _)) (rweq_cmpA_refl_right _)

-- ============================================================
-- § 8. Composition of monoidal functors
-- ============================================================

/-- Composition of monoidal functors is monoidal. -/
noncomputable def compMonoidalFunctor
    (MF : MonoidalFunctorData A B) {C : Type u}
    (MG : MonoidalFunctorData B C) : MonoidalFunctorData A C where
  F := fun a => MG.F (MF.F a)
  preserveTensor := by
    intro a b c p q
    simp only [Path.congrArg_comp]
    exact rweq_trans
      (rweq_congrArg_of_rweq MG.F (MF.preserveTensor p q))
      (MG.preserveTensor (Path.congrArg MF.F p) (Path.congrArg MF.F q))
  preserveUnit := by
    intro a
    simp only [Path.congrArg_comp]
    exact rweq_trans
      (rweq_congrArg_of_rweq MG.F (MF.preserveUnit a))
      (MG.preserveUnit (MF.F a))

-- ============================================================
-- § 9. Monoidal natural transformation
-- ============================================================

/-- A monoidal natural transformation between monoidal functors. -/
structure MonoidalNatTransData (MF MG : MonoidalFunctorData A B) where
  component : ∀ (a : A), Path (MF.F a) (MG.F a)
  naturality : ∀ {a b : A} (p : Path a b),
    RwEq (tensorPath (Path.congrArg MF.F p) (component b))
         (tensorPath (component a) (Path.congrArg MG.F p))

/-- Identity monoidal natural transformation. -/
noncomputable def idMonoidalNatTrans (MF : MonoidalFunctorData A B) :
    MonoidalNatTransData MF MF where
  component := fun a => unitPath (MF.F a)
  naturality := by
    intro a b p
    exact rweq_trans
      (tensor_right_unitor (Path.congrArg MF.F p))
      (rweq_symm (tensor_left_unitor (Path.congrArg MF.F p)))

-- ============================================================
-- § 10. Coherence between functor and associator
-- ============================================================

/-- The functor image of the monoidal associator agrees with
    the target associator applied to functor images. -/
noncomputable def functor_assoc_coherence {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.congrArg MF.F (tensorPath (tensorPath p q) r))
         (Path.congrArg MF.F (tensorPath p (tensorPath q r))) :=
  rweq_congrArg_of_rweq MF.F (tensor_assoc p q r)

/-- Pentagon image: F maps both pentagon routes to the same target. -/
noncomputable def functor_pentagon_image {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (Path.congrArg MF.F (tensorPath (tensorPath (tensorPath p q) r) s))
         (Path.congrArg MF.F (tensorPath p (tensorPath q (tensorPath r s)))) :=
  rweq_congrArg_of_rweq MF.F (mac_lane_pentagon p q r s)

-- ============================================================
-- § 11. Whiskering through monoidal functors
-- ============================================================

/-- Left whiskering commutes with monoidal functor. -/
noncomputable def functor_whisker_left (p : Path a b) {q q' : Path b c}
    (h : RwEq q q') :
    RwEq (Path.congrArg MF.F (tensorPath p q))
         (Path.congrArg MF.F (tensorPath p q')) :=
  rweq_congrArg_of_rweq MF.F (rweq_trans_congr_right p h)

/-- Right whiskering commutes with monoidal functor. -/
noncomputable def functor_whisker_right {p p' : Path a b} (q : Path b c)
    (h : RwEq p p') :
    RwEq (Path.congrArg MF.F (tensorPath p q))
         (Path.congrArg MF.F (tensorPath p' q)) :=
  rweq_congrArg_of_rweq MF.F (rweq_trans_congr_left q h)

end MonoidalFunctorData

end Monoidal
end ComputationalPaths

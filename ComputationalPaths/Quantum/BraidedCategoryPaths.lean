import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Quantum group paths: braided categories

This module packages braided-category coherence as computational paths.
Tensor transport and braiding naturality are represented as path-preserving
constructions, with explicit `Path.Step` normalization witnesses.
-/

namespace ComputationalPaths
namespace Quantum
namespace BraidedCategoryPaths

open Path

universe u

/-- Braided-category data on objects with path-preserving tensor structure. -/
structure BraidedCategoryPathData (Obj : Type u) where
  tensor : Obj → Obj → Obj
  braid : (X Y : Obj) → Path (tensor X Y) (tensor Y X)
  tensorMap :
    {X1 X2 Y1 Y2 : Obj} →
      Path X1 X2 → Path Y1 Y2 → Path (tensor X1 Y1) (tensor X2 Y2)
  braidNaturality :
    {X1 X2 Y1 Y2 : Obj} →
      (p : Path X1 X2) → (q : Path Y1 Y2) →
        Path
          (Path.trans (tensorMap p q) (braid X2 Y2))
          (Path.trans (braid X1 Y1) (tensorMap q p))
  hexagonPath :
    (X Y Z : Obj) →
      Path (tensor (tensor X Y) Z) (tensor (tensor Y Z) X)

namespace BraidedCategoryPathData

variable {Obj : Type u} (B : BraidedCategoryPathData Obj)

/-- Step witness: right-unit normalization for tensorial path transport. -/
noncomputable def tensorMap_step {X1 X2 Y1 Y2 : Obj}
    (p : Path X1 X2) (q : Path Y1 Y2) :
    Path.Step
      (Path.trans (B.tensorMap p q) (Path.refl (B.tensor X2 Y2)))
      (B.tensorMap p q) :=
  Path.Step.trans_refl_right (B.tensorMap p q)

noncomputable def tensorMap_rweq {X1 X2 Y1 Y2 : Obj}
    (p : Path X1 X2) (q : Path Y1 Y2) :
    RwEq
      (Path.trans (B.tensorMap p q) (Path.refl (B.tensor X2 Y2)))
      (B.tensorMap p q) :=
  rweq_of_step (B.tensorMap_step p q)

/-- Step witness: right-unit normalization for braiding naturality. -/
noncomputable def braidNaturality_step {X1 X2 Y1 Y2 : Obj}
    (p : Path X1 X2) (q : Path Y1 Y2) :
    Path.Step
      (Path.trans
        (B.braidNaturality p q)
        (Path.refl (Path.trans (B.braid X1 Y1) (B.tensorMap q p))))
      (B.braidNaturality p q) :=
  Path.Step.trans_refl_right (B.braidNaturality p q)

noncomputable def braidNaturality_rweq {X1 X2 Y1 Y2 : Obj}
    (p : Path X1 X2) (q : Path Y1 Y2) :
    RwEq
      (Path.trans
        (B.braidNaturality p q)
        (Path.refl (Path.trans (B.braid X1 Y1) (B.tensorMap q p))))
      (B.braidNaturality p q) :=
  rweq_of_step (B.braidNaturality_step p q)

noncomputable def braidNaturality_cancel_left {X1 X2 Y1 Y2 : Obj}
    (p : Path X1 X2) (q : Path Y1 Y2) :
    RwEq
      (Path.trans
        (Path.symm (B.braidNaturality p q))
        (B.braidNaturality p q))
      (Path.refl (Path.trans (B.braid X1 Y1) (B.tensorMap q p))) :=
  rweq_cmpA_inv_left (B.braidNaturality p q)

noncomputable def braid_cancel_left (X Y : Obj) :
    RwEq
      (Path.trans (Path.symm (B.braid X Y)) (B.braid X Y))
      (Path.refl (B.tensor Y X)) :=
  rweq_cmpA_inv_left (B.braid X Y)

noncomputable def braid_cancel_right (X Y : Obj) :
    RwEq
      (Path.trans (B.braid X Y) (Path.symm (B.braid X Y)))
      (Path.refl (B.tensor X Y)) :=
  rweq_cmpA_inv_right (B.braid X Y)

/-- Step witness: right-unit normalization for the hexagon path. -/
noncomputable def hexagon_step (X Y Z : Obj) :
    Path.Step
      (Path.trans
        (B.hexagonPath X Y Z)
        (Path.refl (B.tensor (B.tensor Y Z) X)))
      (B.hexagonPath X Y Z) :=
  Path.Step.trans_refl_right (B.hexagonPath X Y Z)

noncomputable def hexagon_rweq (X Y Z : Obj) :
    RwEq
      (Path.trans
        (B.hexagonPath X Y Z)
        (Path.refl (B.tensor (B.tensor Y Z) X)))
      (B.hexagonPath X Y Z) :=
  rweq_of_step (B.hexagon_step X Y Z)

noncomputable def hexagon_cancel_right (X Y Z : Obj) :
    RwEq
      (Path.trans (B.hexagonPath X Y Z) (Path.symm (B.hexagonPath X Y Z)))
      (Path.refl (B.tensor (B.tensor X Y) Z)) :=
  rweq_cmpA_inv_right (B.hexagonPath X Y Z)

end BraidedCategoryPathData
end BraidedCategoryPaths
end Quantum
end ComputationalPaths

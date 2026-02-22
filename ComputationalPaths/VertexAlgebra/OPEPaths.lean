import ComputationalPaths.Path.Rewrite.RwEq

/-!
# OPE paths for vertex algebras

This module packages operator-product-expansion (OPE) data with explicit
computational-path coherence and rewrite-equivalence consequences.
-/

namespace ComputationalPaths
namespace VertexAlgebra

open Path

universe u

/-- Minimal carrier for vertex-algebra style path data. -/
structure VertexAlgebraData where
  /-- State space. -/
  State : Type u
  /-- Vacuum state. -/
  vacuum : State

/-- OPE coefficients equipped with computational-path coherence. -/
structure OPEData (V : VertexAlgebraData.{u}) where
  /-- OPE coefficient extraction: singular part at mode `n`. -/
  coeff : V.State → V.State → Int → V.State
  /-- Vacuum insertion at mode `0` acts as identity. -/
  vacuum_left : ∀ a : V.State, Path (coeff V.vacuum a 0) a
  /-- Associativity of OPE coefficients. -/
  assoc :
    ∀ (a b c : V.State) (m n : Int),
      Path (coeff a (coeff b c n) m) (coeff (coeff a b m) c n)

namespace OPEData

variable {V : VertexAlgebraData.{u}} (O : OPEData V)

/-- Associator with two explicit right-unit insertions (left-associated form). -/
noncomputable def assocWithUnitsLeft (a b c : V.State) (m n : Int) :
    Path (O.coeff a (O.coeff b c n) m) (O.coeff (O.coeff a b m) c n) :=
  Path.trans (Path.trans (O.assoc a b c m n) (Path.refl _)) (Path.refl _)

/-- Associator with two explicit right-unit insertions (right-associated form). -/
noncomputable def assocWithUnitsRight (a b c : V.State) (m n : Int) :
    Path (O.coeff a (O.coeff b c n) m) (O.coeff (O.coeff a b m) c n) :=
  Path.trans (O.assoc a b c m n) (Path.trans (Path.refl _) (Path.refl _))

/-- Reassociating the unit-extended associator is a primitive rewrite step. -/
theorem assocWithUnitsStep (a b c : V.State) (m n : Int) :
    Path.Step (O.assocWithUnitsLeft a b c m n) (O.assocWithUnitsRight a b c m n) := by
  simpa [assocWithUnitsLeft, assocWithUnitsRight] using
    (Path.Step.trans_assoc
      (O.assoc a b c m n)
      (Path.refl (O.coeff (O.coeff a b m) c n))
      (Path.refl (O.coeff (O.coeff a b m) c n)))

/-- Reassociating the unit-extended associator as rewrite equivalence. -/
noncomputable def assocWithUnitsRwEq (a b c : V.State) (m n : Int) :
    RwEq (O.assocWithUnitsLeft a b c m n) (O.assocWithUnitsRight a b c m n) :=
  rweq_of_step (O.assocWithUnitsStep a b c m n)

/-- Associator followed by its inverse contracts to reflexivity. -/
noncomputable def assocCancelRightRwEq (a b c : V.State) (m n : Int) :
    RwEq
      (Path.trans (O.assoc a b c m n) (Path.symm (O.assoc a b c m n)))
      (Path.refl (O.coeff a (O.coeff b c n) m)) :=
  rweq_cmpA_inv_right (O.assoc a b c m n)

/-- Inverse associator followed by associator contracts to reflexivity. -/
noncomputable def assocCancelLeftRwEq (a b c : V.State) (m n : Int) :
    RwEq
      (Path.trans (Path.symm (O.assoc a b c m n)) (O.assoc a b c m n))
      (Path.refl (O.coeff (O.coeff a b m) c n)) :=
  rweq_cmpA_inv_left (O.assoc a b c m n)

/-- Left-unit insertion on the vacuum path normalizes by rewrite. -/
noncomputable def vacuumLeftUnitRwEq (a : V.State) :
    RwEq
      (Path.trans (Path.refl (O.coeff V.vacuum a 0)) (O.vacuum_left a))
      (O.vacuum_left a) :=
  rweq_cmpA_refl_left (O.vacuum_left a)

/-- Right-unit insertion on the vacuum path normalizes by rewrite. -/
noncomputable def vacuumRightUnitRwEq (a : V.State) :
    RwEq
      (Path.trans (O.vacuum_left a) (Path.refl a))
      (O.vacuum_left a) :=
  rweq_cmpA_refl_right (O.vacuum_left a)

/-- Vacuum insertion path contracts with its inverse by rewrite normalization. -/
noncomputable def vacuumCancelRwEq (a : V.State) :
    RwEq
      (Path.trans (O.vacuum_left a) (Path.symm (O.vacuum_left a)))
      (Path.refl (O.coeff V.vacuum a 0)) :=
  rweq_cmpA_inv_right (O.vacuum_left a)

end OPEData

/-- Trivial one-state vertex-algebra data. -/
noncomputable def unitVertexAlgebraData : VertexAlgebraData where
  State := PUnit
  vacuum := PUnit.unit

/-- Trivial OPE coefficients on the one-state vertex algebra. -/
noncomputable def unitOPEData : OPEData unitVertexAlgebraData where
  coeff := fun _ _ _ => PUnit.unit
  vacuum_left := fun _ => Path.refl PUnit.unit
  assoc := fun _ _ _ _ _ => Path.refl PUnit.unit

end VertexAlgebra
end ComputationalPaths

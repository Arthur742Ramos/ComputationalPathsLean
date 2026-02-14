import ComputationalPaths.VertexAlgebra.OPEPaths

/-!
# Conformal-block paths for vertex algebras

This module records transport and fusion coherence for conformal blocks using
explicit computational paths and rewrite normalization.
-/

namespace ComputationalPaths
namespace VertexAlgebra

open Path

universe u

/-- Marked-curve data for conformal blocks. -/
structure MarkedCurve where
  /-- Underlying carrier for marked points. -/
  Carrier : Type u
  /-- Number of marked points. -/
  nPoints : Nat
  /-- Chosen marked points. -/
  mark : Fin nPoints → Carrier

/-- Conformal blocks with path-level transport coherence. -/
structure ConformalBlockData (V : VertexAlgebraData.{u}) where
  /-- Underlying marked curve. -/
  curve : MarkedCurve.{u}
  /-- Space of conformal blocks. -/
  Block : Type u
  /-- Field insertion at a marked point. -/
  insert : Fin curve.nPoints → V.State → Block
  /-- Parallel transport along point-paths. -/
  transport :
    {i j : Fin curve.nPoints} →
      Path (curve.mark i) (curve.mark j) → Block → Block
  /-- Transport along reflexivity is identity. -/
  transport_refl :
    ∀ (i : Fin curve.nPoints) (ψ : Block),
      Path (transport (Path.refl (curve.mark i)) ψ) ψ
  /-- Transport along concatenated paths composes. -/
  transport_comp :
    ∀ {i j k : Fin curve.nPoints}
      (p : Path (curve.mark i) (curve.mark j))
      (q : Path (curve.mark j) (curve.mark k))
      (ψ : Block),
      Path (transport (Path.trans p q) ψ) (transport q (transport p ψ))

namespace ConformalBlockData

variable {V : VertexAlgebraData.{u}} (B : ConformalBlockData V)

/-- Left-unit insertion on transport reflexivity coherence. -/
theorem transportReflLeftUnitRwEq (i : Fin B.curve.nPoints) (ψ : B.Block) :
    RwEq
      (Path.trans
        (Path.refl (B.transport (Path.refl (B.curve.mark i)) ψ))
        (B.transport_refl i ψ))
      (B.transport_refl i ψ) :=
  rweq_cmpA_refl_left (B.transport_refl i ψ)

/-- Transport reflexivity path contracts with its inverse. -/
theorem transportReflCancelRwEq (i : Fin B.curve.nPoints) (ψ : B.Block) :
    RwEq
      (Path.trans (B.transport_refl i ψ) (Path.symm (B.transport_refl i ψ)))
      (Path.refl (B.transport (Path.refl (B.curve.mark i)) ψ)) :=
  rweq_cmpA_inv_right (B.transport_refl i ψ)

/-- Composite transport coherence with explicit unit insertions (left-associated). -/
def transportCompWithUnitsLeft {i j k : Fin B.curve.nPoints}
    (p : Path (B.curve.mark i) (B.curve.mark j))
    (q : Path (B.curve.mark j) (B.curve.mark k))
    (ψ : B.Block) :
    Path (B.transport (Path.trans p q) ψ) (B.transport q (B.transport p ψ)) :=
  Path.trans (Path.trans (B.transport_comp p q ψ) (Path.refl _)) (Path.refl _)

/-- Composite transport coherence with explicit unit insertions (right-associated). -/
def transportCompWithUnitsRight {i j k : Fin B.curve.nPoints}
    (p : Path (B.curve.mark i) (B.curve.mark j))
    (q : Path (B.curve.mark j) (B.curve.mark k))
    (ψ : B.Block) :
    Path (B.transport (Path.trans p q) ψ) (B.transport q (B.transport p ψ)) :=
  Path.trans (B.transport_comp p q ψ) (Path.trans (Path.refl _) (Path.refl _))

/-- Reassociation for the unit-extended transport coherence is a primitive step. -/
theorem transportCompWithUnitsStep {i j k : Fin B.curve.nPoints}
    (p : Path (B.curve.mark i) (B.curve.mark j))
    (q : Path (B.curve.mark j) (B.curve.mark k))
    (ψ : B.Block) :
    Path.Step
      (B.transportCompWithUnitsLeft p q ψ)
      (B.transportCompWithUnitsRight p q ψ) := by
  simpa [transportCompWithUnitsLeft, transportCompWithUnitsRight] using
    (Path.Step.trans_assoc
      (B.transport_comp p q ψ)
      (Path.refl (B.transport q (B.transport p ψ)))
      (Path.refl (B.transport q (B.transport p ψ))))

/-- Reassociation for the unit-extended transport coherence in `RwEq`. -/
theorem transportCompWithUnitsRwEq {i j k : Fin B.curve.nPoints}
    (p : Path (B.curve.mark i) (B.curve.mark j))
    (q : Path (B.curve.mark j) (B.curve.mark k))
    (ψ : B.Block) :
    RwEq
      (B.transportCompWithUnitsLeft p q ψ)
      (B.transportCompWithUnitsRight p q ψ) :=
  rweq_of_step (B.transportCompWithUnitsStep p q ψ)

end ConformalBlockData

/-- OPE-to-conformal-block compatibility witnessed by computational paths. -/
structure ConformalBlockOPECompat {V : VertexAlgebraData.{u}}
    (O : OPEData V) (B : ConformalBlockData V) where
  /-- Fusion map landing in conformal blocks. -/
  fuse : Fin B.curve.nPoints → V.State → V.State → Int → B.Block
  /-- OPE associativity respected by fusion. -/
  fusion_assoc :
    ∀ (i : Fin B.curve.nPoints) (a b c : V.State) (m n : Int),
      Path (fuse i a (O.coeff b c n) m) (fuse i (O.coeff a b m) c n)
  /-- Vacuum insertion compatibility. -/
  vacuum_insert :
    ∀ (i : Fin B.curve.nPoints) (a : V.State),
      Path (fuse i V.vacuum a 0) (B.insert i a)

namespace ConformalBlockOPECompat

variable {V : VertexAlgebraData.{u}}
variable {O : OPEData V} {B : ConformalBlockData V}
variable (F : ConformalBlockOPECompat O B)

/-- Fused associativity path contracts with its inverse. -/
theorem fusionAssocCancelRwEq
    (i : Fin B.curve.nPoints) (a b c : V.State) (m n : Int) :
    RwEq
      (Path.trans
        (F.fusion_assoc i a b c m n)
        (Path.symm (F.fusion_assoc i a b c m n)))
      (Path.refl (F.fuse i a (O.coeff b c n) m)) :=
  rweq_cmpA_inv_right (F.fusion_assoc i a b c m n)

/-- Right-unit insertion on the vacuum compatibility path normalizes by rewrite. -/
theorem vacuumInsertRightUnitRwEq (i : Fin B.curve.nPoints) (a : V.State) :
    RwEq
      (Path.trans (F.vacuum_insert i a) (Path.refl (B.insert i a)))
      (F.vacuum_insert i a) :=
  rweq_cmpA_refl_right (F.vacuum_insert i a)

end ConformalBlockOPECompat

/-- One-point marked curve on `PUnit`. -/
def unitMarkedCurve : MarkedCurve where
  Carrier := PUnit
  nPoints := 1
  mark := fun _ => PUnit.unit

/-- Trivial conformal block datum with identity transport. -/
def trivialConformalBlockData (V : VertexAlgebraData.{u}) : ConformalBlockData V where
  curve := unitMarkedCurve
  Block := V.State
  insert := fun _ a => a
  transport := fun {_ _} _ ψ => ψ
  transport_refl := fun _ ψ => Path.refl ψ
  transport_comp := fun {_ _ _} _ _ ψ => Path.refl ψ

/-- Canonical compatibility from any OPE data to the trivial conformal block. -/
def trivialOPECompat {V : VertexAlgebraData.{u}} (O : OPEData V) :
    ConformalBlockOPECompat O (trivialConformalBlockData V) where
  fuse := fun _ a b n => O.coeff a b n
  fusion_assoc := fun _ a b c m n => O.assoc a b c m n
  vacuum_insert := fun _ a => O.vacuum_left a

end VertexAlgebra
end ComputationalPaths

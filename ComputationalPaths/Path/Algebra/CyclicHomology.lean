/-
# Cyclic Homology via Computational Paths

This module introduces a lightweight cyclic homology interface built from mixed
complexes in the computational paths setting. We record Connes' cyclic complex,
cyclic and periodic homology groups (HC and HP), the SBI sequence, Connes
periodicity, and Jones' isomorphism as minimal data with definitional laws and
`Path` witnesses.

## Key Definitions

- `MixedComplex`
- `ConnesCyclicComplex`
- `CyclicHomology` (HC)
- `PeriodicCyclicHomology` (HP)
- `SBISequence`
- `connes_periodicity`
- `JonesIsomorphism`

## References

- Connes, "Noncommutative Geometry"
- Loday, "Cyclic Homology"
- Jones, "Cyclic homology and equivariant homology"
-/
import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace CyclicHomology

universe u

open HomologicalAlgebra

/-! ## Mixed complexes -/

/-- A mixed complex with differentials b and B. -/
structure MixedComplex where
  /-- Object in degree n. -/
  obj : Nat -> PointedSet.{u}
  /-- Hochschild differential b : C_{n+1} -> C_n. -/
  b : (n : Nat) -> PointedHom (obj (n + 1)) (obj n)
  /-- Connes operator B : C_n -> C_{n+1}. -/
  B : (n : Nat) -> PointedHom (obj n) (obj (n + 1))
  /-- b square-zero. -/
  b_sq_zero : forall n (x : (obj (n + 2)).carrier),
    (b n).toFun ((b (n + 1)).toFun x) = (obj n).zero
  /-- B square-zero. -/
  B_sq_zero : forall n (x : (obj n).carrier),
    (B (n + 1)).toFun ((B n).toFun x) = (obj (n + 2)).zero
  /-- Mixed relation bB = Bb (characteristic-2 form). -/
  bB_comm : forall n (x : (obj (n + 1)).carrier),
    (b (n + 1)).toFun ((B (n + 1)).toFun x) =
      (B n).toFun ((b n).toFun x)

namespace MixedComplex

variable {M : MixedComplex}

/-- `Path` witness for b square-zero. -/
def b_sq_zero_path (n : Nat) (x : (M.obj (n + 2)).carrier) :
    Path ((M.b n).toFun ((M.b (n + 1)).toFun x)) (M.obj n).zero :=
  Path.ofEq (M.b_sq_zero n x)

/-- `Path` witness for B square-zero. -/
def B_sq_zero_path (n : Nat) (x : (M.obj n).carrier) :
    Path ((M.B (n + 1)).toFun ((M.B n).toFun x)) (M.obj (n + 2)).zero :=
  Path.ofEq (M.B_sq_zero n x)

/-- `Path` witness for the mixed relation. -/
def bB_comm_path (n : Nat) (x : (M.obj (n + 1)).carrier) :
    Path ((M.b (n + 1)).toFun ((M.B (n + 1)).toFun x))
      ((M.B n).toFun ((M.b n).toFun x)) :=
  Path.ofEq (M.bB_comm n x)

end MixedComplex

/-! ## Connes cyclic complex -/

/-- The Connes cyclic complex as a chain complex. -/
structure ConnesCyclicComplex where
  /-- Object in degree n. -/
  obj : Nat -> PointedSet.{u}
  /-- Differential d : C_{n+1} -> C_n. -/
  d : (n : Nat) -> PointedHom (obj (n + 1)) (obj n)
  /-- d square-zero. -/
  d_sq_zero : forall n (x : (obj (n + 2)).carrier),
    (d n).toFun ((d (n + 1)).toFun x) = (obj n).zero

namespace ConnesCyclicComplex

variable {C : ConnesCyclicComplex}

/-- Build the Connes cyclic complex from a mixed complex (using b). -/
def ofMixed (M : MixedComplex) : ConnesCyclicComplex where
  obj := M.obj
  d := M.b
  d_sq_zero := M.b_sq_zero

/-- `Path` witness for d square-zero. -/
def d_sq_zero_path (n : Nat) (x : (C.obj (n + 2)).carrier) :
    Path ((C.d n).toFun ((C.d (n + 1)).toFun x)) (C.obj n).zero :=
  Path.ofEq (C.d_sq_zero n x)

end ConnesCyclicComplex

/-! ## Cyclic homology and periodicity -/

abbrev HomologyGroups := CohomologyGroups

/-- Cyclic homology groups HC associated to a Connes cyclic complex. -/
structure CyclicHomology (C : ConnesCyclicComplex) extends HomologyGroups where
  /-- The class of a cycle. -/
  classOf : forall n, (C.obj n).carrier -> carrier n
  /-- Zero maps to zero. -/
  classOf_zero : forall n, classOf n (C.obj n).zero = zero n

/-- Notation for cyclic homology (HC). -/
abbrev HC (C : ConnesCyclicComplex) : Type u :=
  CyclicHomology C

/-- Periodic cyclic homology groups HP with Connes periodicity. -/
structure PeriodicCyclicHomology (C : ConnesCyclicComplex) extends CyclicHomology C where
  /-- Connes periodicity: HP_n ≃ HP_{n+2}. -/
  periodicity : forall n, SimpleEquiv (carrier n) (carrier (n + 2))

/-- Notation for periodic cyclic homology (HP). -/
abbrev HP (C : ConnesCyclicComplex) : Type u :=
  PeriodicCyclicHomology C

/-- Connes periodicity as an explicit equivalence. -/
def connes_periodicity {C : ConnesCyclicComplex} (H : PeriodicCyclicHomology C) (n : Nat) :
    SimpleEquiv (H.carrier n) (H.carrier (n + 2)) :=
  H.periodicity n

/-! ## SBI sequence -/

/-- An SBI sequence relating Hochschild and cyclic homology. -/
structure SBISequence (HH HC : HomologyGroups) where
  /-- Inclusion I : HH_n -> HC_n. -/
  I : forall n, HH.carrier n -> HC.carrier n
  /-- Periodicity operator S : HC_n -> HC_{n+2}. -/
  S : forall n, HC.carrier n -> HC.carrier (n + 2)
  /-- Connes boundary B : HC_n -> HH_{n+1}. -/
  B : forall n, HC.carrier n -> HH.carrier (n + 1)
  /-- I preserves zero. -/
  I_zero : forall n, I n (HH.zero n) = HC.zero n
  /-- S preserves zero. -/
  S_zero : forall n, S n (HC.zero n) = HC.zero (n + 2)
  /-- B preserves zero. -/
  B_zero : forall n, B n (HC.zero n) = HH.zero (n + 1)

namespace SBISequence

variable {HH HC : HomologyGroups} (SBI : SBISequence HH HC)

/-- `Path` witness for I mapping zero to zero. -/
def I_zero_path (n : Nat) :
    Path (SBI.I n (HH.zero n)) (HC.zero n) :=
  Path.ofEq (SBI.I_zero n)

/-- `Path` witness for S mapping zero to zero. -/
def S_zero_path (n : Nat) :
    Path (SBI.S n (HC.zero n)) (HC.zero (n + 2)) :=
  Path.ofEq (SBI.S_zero n)

/-- `Path` witness for B mapping zero to zero. -/
def B_zero_path (n : Nat) :
    Path (SBI.B n (HC.zero n)) (HH.zero (n + 1)) :=
  Path.ofEq (SBI.B_zero n)

end SBISequence

/-! ## Jones isomorphism -/

/-- Jones isomorphism data: cyclic homology vs. equivariant loop homology. -/
structure JonesIsomorphism (HC HLoop : HomologyGroups) where
  /-- Degreewise equivalence. -/
  equiv : forall n, SimpleEquiv (HC.carrier n) (HLoop.carrier n)

namespace JonesIsomorphism

variable {HC HLoop : HomologyGroups} (J : JonesIsomorphism HC HLoop)

/-- Access the Jones equivalence in degree n. -/
def equiv_at (n : Nat) : SimpleEquiv (HC.carrier n) (HLoop.carrier n) :=
  J.equiv n

end JonesIsomorphism

/-! ## Summary -/

/-!
We introduced mixed complexes, the Connes cyclic complex, cyclic and periodic
homology interfaces, the SBI sequence, Connes periodicity, and Jones'
isomorphism, all packaged with definitional laws and Path witnesses.
-/

end CyclicHomology
end Algebra
end Path
end ComputationalPaths

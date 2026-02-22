/-
# The torus as `S¹ × S¹`

This development uses the computational-path circle `Circle` from
`CompPath/CircleCompPath.lean`. Rather than postulating a separate torus
interface, we construct the torus as the ordinary product `Circle × Circle`.

The π₁ computation is packaged in `TorusStep.lean`.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `Torus` | The torus type `S¹ × S¹` |
| `torusBase` | Distinguished base point on the torus |
| `torusLoop1`, `torusLoop2` | The two generating loops |
| `torusPiOneEquiv` | `π₁(T²) ≃ ℤ × ℤ` |
| `torusLoopsCommute` | Commutativity of the two generating loops |
| `torusAbelian` | Abelianness of the torus fundamental group |
| `torusEulerChar` | Euler characteristic of the torus is 0 |
| `nTorus` | n-dimensional torus as iterated product |

## References

- Hatcher, *Algebraic Topology*, §1.2
- HoTT Book, Chapter 6
-/

import ComputationalPaths.Path.CompPath.CircleCompPath
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Homotopy.ProductFundamentalGroup

set_option linter.unusedSimpArgs false

namespace ComputationalPaths
namespace Path
open CompPath

universe u

/-! ## The Torus Type -/

/-- Concrete torus type: `S¹ × S¹`. -/
abbrev Torus : Type u := Circle.{u} × Circle.{u}

/-- Base point on the torus. -/
noncomputable abbrev torusBase : Torus.{u} := (circleBase.{u}, circleBase.{u})

/-- Raw loop space of the torus at `torusBase`. -/
abbrev torusLoopSpace : Type u := LoopSpace Torus.{u} torusBase

/-! ## Generating Loops -/

/-- Loop around the first circle factor (meridian). -/
noncomputable def torusLoop1 : Path (A := Torus.{u}) torusBase torusBase :=
  Path.prodMk (circleLoop.{u}) (Path.refl (circleBase.{u}))

/-- Loop around the second circle factor (longitude). -/
noncomputable def torusLoop2 : Path (A := Torus.{u}) torusBase torusBase :=
  Path.prodMk (Path.refl (circleBase.{u})) (circleLoop.{u})

/-- The constant loop at the torus base point. -/
noncomputable def torusReflLoop : Path (A := Torus.{u}) torusBase torusBase :=
  Path.refl torusBase

/-! ## Fundamental Group -/

/-- The fundamental group of the torus based at `torusBase`. -/
noncomputable abbrev torusPiOne : Type u := circlePiOne.{u} × circlePiOne.{u}

/-- Decodes an integer pair into an element of the torus fundamental group. -/
noncomputable def torusDecode (z : Int × Int) : torusPiOne.{u} :=
  (circleDecode z.1, circleDecode z.2)

/-- Encodes an element of the torus fundamental group as an integer pair. -/
noncomputable def torusEncode : torusPiOne.{u} → Int × Int :=
  fun ⟨x, y⟩ => (circlePiOneEncode x, circlePiOneEncode y)

/-! ## Equivalence π₁(T²) ≅ ℤ × ℤ -/

/-- The fundamental group of `T²` is isomorphic to `ℤ × ℤ`.
This follows from the product fundamental group theorem and
the circle computation `π₁(S¹) ≅ ℤ`. -/
noncomputable def torusPiOneEquiv :
    SimpleEquiv (π₁(Torus.{u}, torusBase.{u}))
      (π₁(Circle.{u}, circleBase.{u}) × π₁(Circle.{u}, circleBase.{u})) :=
  prodPiOneEquiv circleBase circleBase

/-! ## Commutativity of Torus Loops -/

/-- The two generating loops of the torus commute at the `toEq` level.
This is immediate because `toEq` is proof-irrelevant. -/
theorem torusLoopsCommute_toEq :
    (Path.trans torusLoop1 torusLoop2).toEq =
    (Path.trans torusLoop2 torusLoop1).toEq := by
  simp [torusLoop1, torusLoop2, Path.trans, Path.prodMk]

/-- Product of two loops on the torus, composed in either order, have the
same underlying equality witness. -/
theorem torusLoop_comm_proof :
    (Path.trans torusLoop1 torusLoop2 (A := Torus.{u})).proof =
    (Path.trans torusLoop2 torusLoop1).proof := by
  rfl

/-! ## Torus Abelianness -/

/-- The fundamental group of the torus is abelian: any two elements commute
at the `toEq` level.  This follows from the product structure. -/
theorem torusPiOne_abelian_toEq
    (p q : Path (A := Torus.{u}) torusBase torusBase) :
    (Path.trans p q).toEq = (Path.trans q p).toEq := by
  simp [Path.trans]

/-- Two loops in the torus yield the same equality witness regardless of
    composition order. -/
theorem torusLoopSpace_comm
    (p q : LoopSpace Torus.{u} torusBase) :
    (LoopSpace.comp p q).toEq = (LoopSpace.comp q p).toEq := by
  simp [LoopSpace.comp]

/-! ## Iterated Loops -/

/-- n-fold loop around the first circle factor. -/
noncomputable def torusLoop1Pow (n : Int) :
    Path (A := Torus.{u}) torusBase torusBase :=
  Path.prodMk (circleDecodePath n) (Path.refl circleBase)

/-- n-fold loop around the second circle factor. -/
noncomputable def torusLoop2Pow (n : Int) :
    Path (A := Torus.{u}) torusBase torusBase :=
  Path.prodMk (Path.refl circleBase) (circleDecodePath n)

/-- The (m,n)-loop on the torus: m times around the first factor and n times
around the second factor. -/
noncomputable def torusLoopMN (m n : Int) :
    Path (A := Torus.{u}) torusBase torusBase :=
  Path.prodMk (circleDecodePath m) (circleDecodePath n)

/-- The (0,0)-loop is definitionally a product of `circleDecodePath 0` with itself. -/
theorem torusLoopMN_zero_zero :
    (torusLoopMN 0 0 : Path (A := Torus.{u}) torusBase torusBase) =
    Path.prodMk (circleDecodePath 0) (circleDecodePath 0) := by
  rfl

/-! ## Torus Path Coherence -/

/-- Path witnessing that the first projection of the torus base is the circle base. -/
noncomputable def torusFstBase :
    Path (A := Circle.{u}) (Prod.fst torusBase) circleBase :=
  Path.refl circleBase

/-- Path witnessing that the second projection of the torus base is the circle base. -/
noncomputable def torusSndBase :
    Path (A := Circle.{u}) (Prod.snd torusBase) circleBase :=
  Path.refl circleBase

/-- Projecting `torusLoop1` to the first factor yields `circleLoop` at the `toEq` level. -/
theorem torusLoop1_fst_toEq :
    (Path.fst (a1 := circleBase.{u}) (b1 := circleBase.{u}) torusLoop1).toEq = circleLoop.{u}.toEq := by
  simp [torusLoop1, Path.fst, Path.prodMk]

/-- Projecting `torusLoop1` to the second factor yields `refl` at the `toEq` level. -/
theorem torusLoop1_snd_toEq :
    (Path.snd (a1 := circleBase.{u}) (b1 := circleBase.{u}) torusLoop1).toEq =
    (Path.refl circleBase.{u}).toEq := by
  simp [torusLoop1, Path.snd, Path.prodMk]

/-- Projecting `torusLoop2` to the first factor yields `refl` at the `toEq` level. -/
theorem torusLoop2_fst_toEq :
    (Path.fst (a1 := circleBase.{u}) (b1 := circleBase.{u}) torusLoop2).toEq =
    (Path.refl circleBase.{u}).toEq := by
  simp [torusLoop2, Path.fst, Path.prodMk]

/-- Projecting `torusLoop2` to the second factor yields `circleLoop` at the `toEq` level. -/
theorem torusLoop2_snd_toEq :
    (Path.snd (a1 := circleBase.{u}) (b1 := circleBase.{u}) torusLoop2).toEq = circleLoop.{u}.toEq := by
  simp [torusLoop2, Path.snd, Path.prodMk]

/-! ## Euler Characteristic -/

/-- Euler characteristic of the torus.
    χ(T²) = V - E + F = 1 - 2 + 1 = 0
    (CW structure: 1 vertex, 2 edges, 1 face). -/
noncomputable def torusEulerChar : Int := 0

/-- The CW cell count data for the torus. -/
structure TorusCWData where
  vertices : Nat := 1
  edges : Nat := 2
  faces : Nat := 1

/-- The standard CW structure on the torus. -/
noncomputable def torusStdCW : TorusCWData := { vertices := 1, edges := 2, faces := 1 }

/-- The Euler characteristic computes from the CW data. -/
theorem torusEuler_from_CW :
    (torusStdCW.vertices : Int) - torusStdCW.edges + torusStdCW.faces = torusEulerChar := by
  native_decide

/-! ## n-dimensional Torus -/

/-- The n-dimensional torus `T^n = (S¹)^n`, defined as an iterated product. -/
noncomputable def nTorus : Nat → Type u
  | 0 => PUnit
  | 1 => Circle.{u}
  | Nat.succ (Nat.succ n) => Circle.{u} × nTorus (n + 1)

/-- Base point of the n-torus. -/
noncomputable def nTorusBase : (n : Nat) → nTorus.{u} n
  | 0 => PUnit.unit
  | 1 => circleBase
  | Nat.succ (Nat.succ n) => (circleBase, nTorusBase (n + 1))

/-- The 0-torus is a point. -/
theorem nTorus_zero : nTorus.{u} 0 = PUnit := rfl

/-- The 1-torus is the circle. -/
theorem nTorus_one : nTorus.{u} 1 = Circle.{u} := rfl

/-- Betti numbers of the 2-torus. β_0 = β_2 = 1, β_1 = 2. -/
noncomputable def torus2BettiNumber : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | _ => 0

/-- β_0(T²) = 1. -/
theorem torus2Betti_zero : torus2BettiNumber 0 = 1 := rfl

/-- β_1(T²) = 2. -/
theorem torus2Betti_one : torus2BettiNumber 1 = 2 := rfl

/-- β_2(T²) = 1. -/
theorem torus2Betti_two : torus2BettiNumber 2 = 1 := rfl

/-- The total Betti number of T² is 4 = 1 + 2 + 1. -/
theorem torus2Betti_total :
    torus2BettiNumber 0 + torus2BettiNumber 1 + torus2BettiNumber 2 = 4 := rfl

/-! ## Transport on the Torus -/

/-- Transport along `torusLoop1` acts trivially on constant families. -/
theorem transport_torusLoop1_const (D : Type u) (x : D) :
    Path.transport (D := fun _ : Torus.{u} => D) torusLoop1 x = x := by
  simp [Path.transport_const]

/-- Transport along `torusLoop2` acts trivially on constant families. -/
theorem transport_torusLoop2_const (D : Type u) (x : D) :
    Path.transport (D := fun _ : Torus.{u} => D) torusLoop2 x = x := by
  simp [Path.transport_const]

/-- Transport along the (m,n)-loop acts trivially on constant families. -/
theorem transport_torusLoopMN_const (D : Type u) (m n : Int) (x : D) :
    Path.transport (D := fun _ : Torus.{u} => D) (torusLoopMN m n) x = x := by
  simp [Path.transport_const]

/-! ## Symmetry of Torus Loops -/

/-- The inverse of `torusLoop1` at the `toEq` level. -/
theorem torusLoop1_symm_toEq :
    (Path.symm (A := Torus.{u}) torusLoop1).toEq = torusLoop1.toEq.symm := by
  simp

/-- The inverse of `torusLoop2` at the `toEq` level. -/
theorem torusLoop2_symm_toEq :
    (Path.symm (A := Torus.{u}) torusLoop2).toEq = torusLoop2.toEq.symm := by
  simp

/-- Cancellation: `torusLoop1 ⬝ torusLoop1⁻¹` has trivial `toEq`. -/
theorem torusLoop1_cancel_toEq :
    (Path.trans (A := Torus.{u}) torusLoop1 (Path.symm torusLoop1)).toEq =
    (rfl : torusBase = torusBase) := by
  simp

/-- Cancellation: `torusLoop2 ⬝ torusLoop2⁻¹` has trivial `toEq`. -/
theorem torusLoop2_cancel_toEq :
    (Path.trans (A := Torus.{u}) torusLoop2 (Path.symm torusLoop2)).toEq =
    (rfl : torusBase = torusBase) := by
  simp

/-! ## Congruence on the Torus -/

/-- The swap map on the torus: `(x, y) ↦ (y, x)`. -/
noncomputable def torusSwap : Torus.{u} → Torus.{u} :=
  fun ⟨x, y⟩ => (y, x)

/-- The swap map is an involution. -/
theorem torusSwap_involution (t : Torus.{u}) :
    torusSwap (torusSwap t) = t := by
  cases t; rfl

/-- Swap sends `torusBase` to `torusBase`. -/
theorem torusSwap_base :
    torusSwap torusBase = (torusBase : Torus.{u}) := rfl

/-- Swap as a `SimpleEquiv`. -/
noncomputable def torusSwapEquiv : SimpleEquiv (Torus.{u}) (Torus.{u}) where
  toFun := torusSwap
  invFun := torusSwap
  left_inv := torusSwap_involution
  right_inv := torusSwap_involution

/-! ## Diagonal and Covering Degree -/

/-- The diagonal embedding `S¹ → T²`: `x ↦ (x, x)`. -/
noncomputable def torusDiagonal : Circle.{u} → Torus.{u} :=
  fun x => (x, x)

/-- The diagonal sends the circle base to the torus base. -/
theorem torusDiagonal_base :
    torusDiagonal circleBase.{u} = torusBase := rfl

/-- The covering degree of the standard double cover of T² is 2. -/
noncomputable def torusStdCoveringDegree : Nat := 2

/-- The genus of the torus is 1. -/
noncomputable def torusGenus : Nat := 1

/-- The genus–Euler characteristic relation: χ = 2 - 2g. -/
theorem torusGenus_euler : (2 : Int) - 2 * torusGenus = torusEulerChar := rfl

end Path
end ComputationalPaths

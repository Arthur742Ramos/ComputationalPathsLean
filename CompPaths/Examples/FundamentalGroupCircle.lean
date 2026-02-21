/-
# π₁(S¹) ≅ ℤ with explicit computational-path traces

This module rewrites the circle example so the core proofs exhibit explicit
`Path.trans`/`Path.symm`/`Path.refl` constructions and named `Step`/`RwEq`
witnesses before connecting to integer encodings.
-/

import CompPaths.Core
import ComputationalPaths.Path.CompPath.CircleCompPath
import ComputationalPaths.Path.CompPath.WindingNumberProperties
import ComputationalPaths.Path.CompPath.CircleStep
import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Rewrite.SimpleEquiv

set_option maxHeartbeats 2000000

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u v

/-! ## Group structure packaging -/

/-- A group isomorphism packages an equivalence with multiplication/identity laws. -/
structure GroupIso (G : Type u) (H : Type v)
    (mulG : G → G → G) (oneG : G)
    (mulH : H → H → H) (oneH : H) : Type (max u v) where
  equiv : SimpleEquiv G H
  map_mul : ∀ x y : G, equiv.toFun (mulG x y) = mulH (equiv.toFun x) (equiv.toFun y)
  map_one : equiv.toFun oneG = oneH

/-- Inverse on `circlePiOne` induced by expression symmetry. -/
noncomputable def circlePiOneInv : circlePiOne → circlePiOne :=
  Quot.lift
    (fun p => Quot.mk _ (CircleCompPathExpr.symm p))
    (by
      intro p q hpq
      apply Quot.sound
      exact hpq)

/-! ## Explicit path powers and rewrite traces -/

/-- Raw loop powers built by explicit `Path.trans` chains. -/
@[simp] noncomputable def circleLoopPowNat : Nat → Path circleBase circleBase
  | 0 => Path.refl circleBase
  | Nat.succ n => Path.trans (circleLoopPowNat n) circleLoop

/-- Integer loop powers at the raw path level. -/
@[simp] noncomputable def circleLoopPowInt : Int → Path circleBase circleBase
  | Int.ofNat n => circleLoopPowNat n
  | Int.negSucc n => Path.symm (circleLoopPowNat (Nat.succ n))

/-- Explicit chain: `loop^m ⬝ loop^n ≈ loop^(m+n)` (natural powers). -/
theorem circleLoopPowNat_add_rweq (m n : Nat) :
    RwEq
      (Path.trans (circleLoopPowNat m) (circleLoopPowNat n))
      (circleLoopPowNat (m + n)) := by
  induction n with
  | zero =>
      simpa [circleLoopPowNat] using
        (rweq_cmpA_refl_right (A := Circle)
          (a := circleBase) (b := circleBase) (p := circleLoopPowNat m))
  | succ n ih =>
      have h_assoc :
          RwEq
            (Path.trans (circleLoopPowNat m)
              (Path.trans (circleLoopPowNat n) circleLoop))
            (Path.trans
              (Path.trans (circleLoopPowNat m) (circleLoopPowNat n))
              circleLoop) :=
        rweq_symm
          (rweq_tt (A := Circle)
            (p := circleLoopPowNat m) (q := circleLoopPowNat n) (r := circleLoop))
      have h_congr :
          RwEq
            (Path.trans
              (Path.trans (circleLoopPowNat m) (circleLoopPowNat n))
              circleLoop)
            (Path.trans (circleLoopPowNat (m + n)) circleLoop) :=
        rweq_trans_congr_left circleLoop ih
      have h_total := rweq_trans h_assoc h_congr
      simpa [circleLoopPowNat, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h_total

@[simp] theorem circleLoopPowInt_neg (z : Int) :
    circleLoopPowInt (-z) = Path.symm (circleLoopPowInt z) := by
  cases z with
  | ofNat n =>
      cases n with
      | zero => simp [circleLoopPowInt]
      | succ n => simp [circleLoopPowInt]
  | negSucc n =>
      simp [circleLoopPowInt]

/-- Explicit cancellation trace: `loop^z ⬝ loop^(-z) ≈ refl` via `Step.trans_symm`. -/
theorem circleLoopPowInt_cancel (z : Int) :
    RwEq
      (Path.trans (circleLoopPowInt z) (circleLoopPowInt (-z)))
      (Path.refl circleBase) := by
  rw [circleLoopPowInt_neg]
  exact
    rweq_of_step
      (Step.trans_symm (A := Circle)
        (a := circleBase) (b := circleBase) (p := circleLoopPowInt z))

/-! ## Step-level interchange (Eckmann-Hilton witness) -/

noncomputable def circleHorizontalAxis (p : Path (A := Circle) circleBase circleBase) :
    Path (A := Circle × Circle) (circleBase, circleBase) (circleBase, circleBase) :=
  Path.mapLeft (A := Circle) (B := Circle) (C := Circle × Circle) Prod.mk p circleBase

noncomputable def circleVerticalAxis (q : Path (A := Circle) circleBase circleBase) :
    Path (A := Circle × Circle) (circleBase, circleBase) (circleBase, circleBase) :=
  Path.mapRight (A := Circle) (B := Circle) (C := Circle × Circle) Prod.mk circleBase q

/-- Interchange witnessed by the primitive step constructor `Step.map2_subst`. -/
noncomputable def circleInterchangeStep
    (p q : Path (A := Circle) circleBase circleBase) :
    Step
      (Path.trans (circleHorizontalAxis p) (circleVerticalAxis q))
      (Path.trans (circleVerticalAxis q) (circleHorizontalAxis p)) := by
  change
    Step
      (Path.map2 (A := Circle) (B := Circle) (C := Circle × Circle) Prod.mk p q)
      (Path.trans
        (Path.mapRight (A := Circle) (B := Circle) (C := Circle × Circle) Prod.mk circleBase q)
        (Path.mapLeft (A := Circle) (B := Circle) (C := Circle × Circle) Prod.mk p circleBase))
  exact
    Step.map2_subst
      (A := Circle × Circle) (A₁ := Circle) (B := Circle) (f := Prod.mk) (p := p) (q := q)

noncomputable def circleInterchangeRwEq
    (p q : Path (A := Circle) circleBase circleBase) :
    RwEq
      (Path.trans (circleHorizontalAxis p) (circleVerticalAxis q))
      (Path.trans (circleVerticalAxis q) (circleHorizontalAxis p)) :=
  RwEq.step (circleInterchangeStep p q)

/-! ## Winding number homomorphism via path-structure induction -/

private theorem windingNumber_mul_expr_induction
    (p q : CircleCompPathExpr circleCompPathBase circleCompPathBase) :
    windingNumber (circlePiOneMul (Quot.mk _ p) (Quot.mk _ q)) =
      windingNumber (Quot.mk _ p) + windingNumber (Quot.mk _ q) := by
  induction p with
  | loop =>
      simp [windingNumber, circlePiOneMul, circleCompPathMulExprRight]
  | refl a =>
      simp [windingNumber, circlePiOneMul, circleCompPathMulExprRight]
  | symm p ih =>
      simp [windingNumber, circlePiOneMul, circleCompPathMulExprRight]
  | trans p r ihp ihr =>
      simp [windingNumber, circlePiOneMul, circleCompPathMulExprRight, Int.add_assoc]

theorem windingNumber_one :
    windingNumber circlePiOneOne = 0 :=
  winding_number_constant

theorem windingNumber_mul (x y : circlePiOne) :
    windingNumber (circlePiOneMul x y) = windingNumber x + windingNumber y := by
  refine Quot.inductionOn x ?_
  intro p
  refine Quot.inductionOn y ?_
  intro q
  exact windingNumber_mul_expr_induction p q

theorem windingNumber_inv (x : circlePiOne) :
    windingNumber (circlePiOneInv x) = -(windingNumber x) := by
  refine Quot.inductionOn x ?_
  intro p
  simp [circlePiOneInv, windingNumber]

theorem windingNumber_pow_nat (x : circlePiOne) (n : Nat) :
    windingNumber (Nat.rec circlePiOneOne (fun _ acc => circlePiOneMul acc x) n) =
      n * windingNumber x := by
  induction n with
  | zero =>
      simp [windingNumber_one]
  | succ n ih =>
      rw [windingNumber_mul, ih]
      simp [Nat.succ_mul]

/-! ## Decode-side multiplication and inverse laws -/

theorem circleDecode_add (m n : Int) :
    circlePiOneMul (circleDecode m) (circleDecode n) = circleDecode (m + n) := by
  apply Quot.sound
  dsimp [circleCompPathRel, circlePiOneMul, circleCompPathMulExprRight, circleDecode]
  simp [circleCompPathEncodeExpr_zpow, Int.add_assoc, Int.add_comm, Int.add_left_comm]

theorem circleDecode_zero_eq_one :
    circleDecode 0 = circlePiOneOne := by
  rfl

theorem circleDecode_neg (z : Int) :
    circlePiOneInv (circleDecode z) = circleDecode (-z) := by
  apply Quot.sound
  dsimp [circleCompPathRel, circlePiOneInv, circleDecode]
  simp [circleCompPathEncodeExpr_zpow]

/-- Decode-level inverse law; the path-level cancellation trace is explicit above. -/
theorem circleDecode_inv_right (z : Int) :
    circlePiOneMul (circleDecode z) (circleDecode (-z)) = circlePiOneOne := by
  have _cancelTrace :
      RwEq
        (Path.trans (circleLoopPowInt z) (circleLoopPowInt (-z)))
        (Path.refl circleBase) :=
    circleLoopPowInt_cancel z
  apply Quot.sound
  dsimp [circleCompPathRel, circlePiOneMul, circleCompPathMulExprRight, circleDecode, circlePiOneOne]
  simp [circleCompPathEncodeExpr_zpow]

/-! ## Group isomorphism package -/

noncomputable def circlePiOneGroupIsoInt :
    GroupIso circlePiOne.{0} Int circlePiOneMul circlePiOneOne (· + ·) 0 where
  equiv := circleCompPathPiOneEquivInt.{0}
  map_mul := windingNumber_mul.{0}
  map_one := windingNumber_one.{0}

/-! ## Equality classification -/

theorem sameWindingNumber_iff_eq (x y : circlePiOne) :
    windingNumber x = windingNumber y ↔ x = y := by
  constructor
  · exact winding_number_injective
  · intro h
    rw [h]

theorem windingNumber_loop :
    windingNumber (circleDecode 1) = 1 := by
  simp [windingNumber]

theorem windingNumber_loop_nfold (n : Nat) :
    windingNumber (circleDecode (Int.ofNat n)) = Int.ofNat n := by
  simp [windingNumber]

theorem circlePiOne_eq_iff_windingNumber_eq (x y : circlePiOne) :
    x = y ↔ windingNumber x = windingNumber y := by
  constructor
  · intro h
    rw [h]
  · exact winding_number_injective

/-! ## Group laws for `circlePiOne` -/

theorem circlePiOneMul_assoc (x y z : circlePiOne) :
    circlePiOneMul (circlePiOneMul x y) z =
    circlePiOneMul x (circlePiOneMul y z) := by
  refine Quot.inductionOn x ?_
  intro p
  refine Quot.inductionOn y ?_
  intro q
  refine Quot.inductionOn z ?_
  intro r
  apply Quot.sound
  dsimp [circleCompPathRel, circlePiOneMul, circleCompPathMulExprRight]
  simp [Int.add_assoc]

theorem circlePiOneMul_one_left (x : circlePiOne) :
    circlePiOneMul circlePiOneOne x = x := by
  refine Quot.inductionOn x ?_
  intro p
  apply Quot.sound
  dsimp [circleCompPathRel, circlePiOneMul, circleCompPathMulExprRight, circlePiOneOne, circleDecode]
  simp

theorem circlePiOneMul_one_right (x : circlePiOne) :
    circlePiOneMul x circlePiOneOne = x := by
  refine Quot.inductionOn x ?_
  intro p
  apply Quot.sound
  dsimp [circleCompPathRel, circlePiOneMul, circleCompPathMulExprRight, circlePiOneOne, circleDecode]
  simp

theorem circlePiOneMul_inv_left (x : circlePiOne) :
    circlePiOneMul (circlePiOneInv x) x = circlePiOneOne := by
  refine Quot.inductionOn x ?_
  intro p
  apply Quot.sound
  dsimp [circleCompPathRel, circlePiOneMul, circleCompPathMulExprRight, circlePiOneInv, circlePiOneOne, circleDecode]
  simp

theorem circlePiOneMul_inv_right (x : circlePiOne) :
    circlePiOneMul x (circlePiOneInv x) = circlePiOneOne := by
  refine Quot.inductionOn x ?_
  intro p
  apply Quot.sound
  dsimp [circleCompPathRel, circlePiOneMul, circleCompPathMulExprRight, circlePiOneInv, circlePiOneOne, circleDecode]
  simp

/-! ## Commutativity -/

theorem circlePiOne_comm (x y : circlePiOne) :
    circlePiOneMul x y = circlePiOneMul y x := by
  let p : Path circleBase circleBase := circleLoopPowInt (windingNumber x)
  let q : Path circleBase circleBase := circleLoopPowInt (windingNumber y)
  have _eh :
      RwEq
        (Path.trans (circleHorizontalAxis p) (circleVerticalAxis q))
        (Path.trans (circleVerticalAxis q) (circleHorizontalAxis p)) :=
    circleInterchangeRwEq p q
  refine Quot.inductionOn x ?_
  intro px
  refine Quot.inductionOn y ?_
  intro py
  apply Quot.sound
  dsimp [circleCompPathRel, circlePiOneMul, circleCompPathMulExprRight]
  simp [Int.add_comm]

end CompPath
end Path
end ComputationalPaths

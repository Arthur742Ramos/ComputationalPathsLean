import ComputationalPaths.Path.HIT.Circle
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Rewrite.Quot
import ComputationalPaths.Path.Rewrite.Quot

namespace ComputationalPaths
namespace Path

open SimpleEquiv

@[simp] theorem circleEncode_circleDecode_add_one (z : Int) :
  circleEncode (circleDecode (z + 1)) = circleEncode (circleDecode z) + 1 := by
  change circleEncode (circleLoopZPow (z + 1))
      = circleEncode (circleLoopZPow z) + 1
  rw [circleLoopZPow_add (m := z) (n := 1), circleLoopZPow_one]
  have hx := circleEncode_comp_loop (x := circleLoopZPow z)
  exact hx

@[simp] theorem circleEncode_circleDecode_add_neg_one (z : Int) :
  circleEncode (circleDecode (z + (-1))) = circleEncode (circleDecode z) - 1 := by
  change circleEncode (circleLoopZPow (z + (-1)))
      = circleEncode (circleLoopZPow z) - 1
  rw [circleLoopZPow_add (m := z) (n := -1), circleLoopZPow_neg_one]
  have hx := circleEncode_comp_inv_loop (x := circleLoopZPow z)
  exact hx

/-- Encode∘decode identity on negative integers by Nat induction. -/
theorem circleEncode_circleDecode_of_negNat (k : Nat) :
  circleEncode (circleDecode (-(k : Int))) = -(k : Int) := by
  induction k with
  | zero =>
      simpa using circleEncode_circleDecode_ofNat 0
  | succ k ih =>
      have step := circleEncode_circleDecode_add_neg_one (z := - (k : Int))
      have hk := (Int.natCast_succ k)
      have hneg := _root_.congrArg (fun t => -t) hk
      have : -((Nat.succ k : Nat) : Int) = - (k : Int) + (-1) := by
        simpa [Int.sub_eq_add_neg, Int.add_comm, Int.add_left_comm, Int.add_assoc] using hneg
      calc
        circleEncode (circleDecode (-(Nat.succ k : Int)))
            = circleEncode (circleDecode (- (k : Int) + (-1))) := by simpa [this]
        _ = circleEncode (circleDecode (-(k : Int))) - 1 := step
        _ = -(k : Int) - 1 := by simpa using ih
        _ = -((Nat.succ k : Nat) : Int) := by simpa [Int.sub_eq_add_neg] using this.symm

@[simp] theorem circleEncode_circleDecode (z : Int) :
  circleEncode (circleDecode z) = z := by
  cases z with
  | ofNat n =>
      exact circleEncode_circleDecode_ofNat n
  | negSucc n =>
      exact circleEncode_circleDecode_of_negNat (Nat.succ n)

-- Equality-level helper: `decodeEq ∘ encodeEq = id` on `(=)`.
private theorem circleDecodeEq_circleEncodeEq
    (e : circleBase = circleBase) :
    (circleLoopPathZPow (circleEncodePath (Path.ofEq e))).toEq = e := by
  cases e with
  | rfl =>
      -- encodeEq rfl = 0 and decodeEq 0 = rfl
      simpa using (by
        have : circleEncodePath (Path.refl circleBase) = (0 : Int) :=
          circleEncodePath_refl
        simpa [this])

/-- `decode ∘ encode = id` on π₁(S¹). -/
theorem circleDecode_circleEncode (x : circlePiOne) :
    circleDecode (circleEncode x) = x := by
  -- Compare via propositional equality using `toEq`.
  apply eq_of_toEq_eq (A := Circle) (a := circleBase) (b := circleBase)
  -- Work with a path representative of `x`.
  refine Quot.inductionOn x (fun p => ?_)
  -- Reduce `decode (encode (ofLoop p))` to an equality on raw z-powers.
  have :
      PathRwQuot.toEq (A := Circle)
        (circleDecode (circleEncode
          (LoopQuot.ofLoop (A := Circle) (a := circleBase) p)))
        = (circleLoopPathZPow (circleEncodePath p)).toEq := by
    -- `toEq (decode z)` calculates to the raw `circleLoopPathZPow`.
    change PathRwQuot.toEq (A := Circle)
        (circleLoopZPow (circleEncodePath p))
        = (circleLoopPathZPow (circleEncodePath p)).toEq
    simpa using circleLoopZPow_toEq (z := circleEncodePath p)
  -- Replace the integer by the canonicalised version built from `p.toEq`.
  have hcanon :
      circleEncodePath (Path.ofEq p.toEq) = circleEncodePath p := by
    have hcanonRw : RwEq (Path.ofEq p.toEq) p := rweq_canon (p := p)
    exact circleEncodePath_rweq (h := hcanonRw)
  -- Finish by equality induction on `e := p.toEq`.
  have hEq := circleDecodeEq_circleEncodeEq (e := p.toEq)
  -- Rewrite the integer using `hcanon` and conclude.
  have :
      (circleLoopPathZPow (circleEncodePath p)).toEq = p.toEq := by
    simpa [hcanon] using hEq
  -- Right-hand side `toEq` is just `p.toEq`.
  have :
      PathRwQuot.toEq (A := Circle)
        (circleDecode (circleEncode
          (LoopQuot.ofLoop (A := Circle) (a := circleBase) p)))
        = PathRwQuot.toEq (A := Circle)
            (LoopQuot.ofLoop (A := Circle) (a := circleBase) p) :=
    this
  simpa using this

noncomputable def circlePiOneEquivInt : SimpleEquiv circlePiOne Int where
  toFun := circleWindingNumber
  invFun := circleDecode
  left_inv := by
    intro x
    change circleDecode (circleEncode x) = x
    exact circleDecode_circleEncode (x := x)
  right_inv := by
    intro z
    change circleEncode (circleDecode z) = z
  exact circleEncode_circleDecode (z := z)

@[simp] theorem circleWindingNumber_decode (z : Int) :
    circleWindingNumber (circleDecode z) = z := by
  change circleEncode (circleDecode z) = z
  exact circleEncode_circleDecode (z := z)

/-!
Decode respects integer addition (circle-specific proof).

We avoid the generic `zpow_add` placeholder by proving that `encode` is
injective (has left-inverse `decode`) and computing
`encode (decode m ⋆ decode n)` via the ±1 step laws.
-/

private theorem circleEncode_comp_decode_ofNat (m : Int) (k : Nat) :
    circleEncode
      (LoopQuot.comp (circleDecode m) (circleDecode (Int.ofNat k)))
      = m + (k : Int) := by
  induction k with
  | zero =>
      -- comp x id = x
      simpa using (by
        change circleEncode (LoopQuot.comp (circleDecode m) LoopQuot.id)
          = m + (0 : Int)
        simp)
  | succ k ih =>
      -- decode (k+1) = decode k ⋆ loop; associate and use the +1 step.
      have hstep : circleDecode (Int.ofNat k.succ)
            = LoopQuot.comp (circleDecode (Int.ofNat k)) circleLoopClass := by
        change circleLoopZPow ((Nat.succ k : Nat) : Int)
          = LoopQuot.comp (circleLoopPow k) circleLoopClass
        simpa using circleLoopPow_succ (n := k)
      calc
        circleEncode (LoopQuot.comp (circleDecode m)
            (circleDecode (Int.ofNat k.succ)))
            = circleEncode (LoopQuot.comp (circleDecode m)
                (LoopQuot.comp (circleDecode (Int.ofNat k)) circleLoopClass)) := by
                  simp [hstep]
        _ = circleEncode (LoopQuot.comp
              (LoopQuot.comp (circleDecode m)
                (circleDecode (Int.ofNat k)))
              circleLoopClass) := by
                  simpa using (LoopQuot.comp_assoc (A := Circle) (a := circleBase)
                    (x := circleDecode m)
                    (y := circleDecode (Int.ofNat k))
                    (z := circleLoopClass))
        _ = circleEncode
              (LoopQuot.comp (circleDecode m) (circleDecode (Int.ofNat k))) + 1 := by
                  simpa using
                    circleEncode_comp_loop
                      (x := LoopQuot.comp (circleDecode m)
                              (circleDecode (Int.ofNat k)))
        _ = (m + (k : Int)) + 1 := by simpa [ih]
        _ = m + (Int.ofNat (Nat.succ k)) := by
              simpa [Int.natCast_succ, Int.add_assoc, Int.add_left_comm,
                Int.add_comm]

private theorem circleEncode_comp_decode_negSucc (m : Int) (n : Nat) :
    circleEncode
      (LoopQuot.comp (circleDecode m)
        (circleDecode (Int.negSucc n)))
      = m - (Nat.succ n : Int) := by
  -- decode (-1) case then iterate using associativity and the -1 step.
  induction n with
  | zero =>
      -- decode (-1) = inv loop
      change circleEncode
          (LoopQuot.comp (circleDecode m) (LoopQuot.inv circleLoopClass))
        = m - 1
      simpa using circleEncode_comp_inv_loop (x := circleDecode m)
  | succ n ih =>
      -- decode (-(n+2)) = inv (pow (n+2)) = (inv loop) ⋆ (inv (pow (n+1)))
      have hneg : circleDecode (Int.negSucc (Nat.succ n))
            = LoopQuot.comp (LoopQuot.inv circleLoopClass)
                (LoopQuot.inv (circleLoopPow (Nat.succ n))) := by
        -- inv (pow (n+2)) = inv (pow (n+1) ⋆ loop) = (inv loop) ⋆ (inv (pow (n+1)))
        change LoopQuot.inv (circleLoopPow (Nat.succ (Nat.succ n)))
          = _
        -- pow_succ then inverse-of-composition
        have hps : circleLoopPow (Nat.succ (Nat.succ n))
              = LoopQuot.comp (circleLoopPow (Nat.succ n)) circleLoopClass := by
          simpa using circleLoopPow_succ (n := Nat.succ n)
        simpa [hps, LoopQuot.inv_comp_rev]
      calc
        circleEncode
            (LoopQuot.comp (circleDecode m)
              (circleDecode (Int.negSucc (Nat.succ n))))
            = circleEncode
                (LoopQuot.comp (circleDecode m)
                  (LoopQuot.comp (LoopQuot.inv circleLoopClass)
                    (LoopQuot.inv (circleLoopPow (Nat.succ n))))) := by
              simp [hneg]
        _ = circleEncode
              (LoopQuot.comp
                (LoopQuot.comp (circleDecode m)
                  (LoopQuot.inv circleLoopClass))
                (LoopQuot.inv (circleLoopPow (Nat.succ n)))) := by
              simpa using (LoopQuot.comp_assoc (A := Circle) (a := circleBase)
                  (x := circleDecode m)
                  (y := LoopQuot.inv circleLoopClass)
                  (z := LoopQuot.inv (circleLoopPow (Nat.succ n))))
        _ = circleEncode
              (LoopQuot.comp (circleDecode m)
                (LoopQuot.inv (circleLoopPow (Nat.succ n)))) - 1 := by
              simpa using circleEncode_comp_inv_loop
                (x := LoopQuot.comp (circleDecode m)
                        (LoopQuot.inv (circleLoopPow (Nat.succ n))))
        _ = (m - (Nat.succ n : Int)) - 1 := by simpa [ih]
        _ = m - (Nat.succ (Nat.succ n) : Int) := by
              -- arithmetic: (m - (n+1)) - 1 = m - (n+2)
              simpa [Int.sub_eq_add_neg, Int.add_assoc, Int.add_left_comm,
                Int.add_comm, Int.natCast_succ]

@[simp] theorem circleDecode_add_proved (m n : Int) :
    circleDecode (m + n) =
      LoopQuot.comp (circleDecode m) (circleDecode n) := by
  -- `circleEncode` is injective since it has left-inverse `circleDecode`.
  have inj : ∀ {x y}, circleEncode x = circleEncode y → x = y := by
    intro x y h
    have := _root_.congrArg circleDecode h
    simpa [circleDecode_circleEncode] using this
  -- Compare encodings on both sides.
  apply inj
  -- Left: encode ∘ decode = id on ℤ
  have hL : circleEncode (circleDecode (m + n)) = m + n := by
    simpa using circleEncode_circleDecode (z := m + n)
  -- Right: compute via the ±1 step laws by induction on `n`.
  have hR : circleEncode
      (LoopQuot.comp (circleDecode m) (circleDecode n)) = m + n := by
    cases n with
    | ofNat k =>
        simpa using circleEncode_comp_decode_ofNat (m := m) (k := k)
    | negSucc k =>
        simpa [Int.sub_eq_add_neg] using
          circleEncode_comp_decode_negSucc (m := m) (n := k)
  simpa [hR] using hL

end Path
end ComputationalPaths

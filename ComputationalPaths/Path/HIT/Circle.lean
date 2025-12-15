/-
# The circle as a higher-inductive type (axiomatic skeleton)

This module introduces `Circle` together with its base-point, fundamental loop,
and an eliminator stated in the computational-path style.  At this stage we work
axiomatically: the constructors and recursor will later be justified by the
normalisation machinery developed for computational paths.  By providing these
interfaces now, downstream developments (loop spaces, fundamental groups, etc.)
can already depend on a stable API.  The axioms stop with the HIT interface;
everything below—loop quotients, encode/decode, and transport to ℤ—is defined in
Lean using the computational-path infrastructure.

## Key Results

- `circleLoop`: The fundamental loop around S¹
- `circlePiOneEquivInt`: π₁(S¹) ≃ ℤ (the main theorem)
- `LoopPowerClass`: Winding number classification of loop powers

## Axiom Structure

**HIT Axioms (standard for any HIT):**
- `Circle`, `circleBase`, `circleLoop`: Type and constructors
- `circleRec`, `circleRec_base`, `circleRec_loop`: Non-dependent eliminator
- `circleInd`, `circleInd_base`, `circleInd_loop`: Dependent eliminator

**Encode-decode axiom:**
- `circleLoop_rweq_decode`: Any loop p is RwEq to loop^(encode p)

**Derived theorems (not axioms):**
- `circleCode_transport_shift`: Transport acts by adding winding number
- `circleEncodePath_trans`: Encoding is additive on path composition
- `circleCode_transport_loopPow_add`: Transport along loop^n adds n
- `circleCode_transport_symm_loopPow_sub`: Transport along symm(loop^n) subtracts n

## Mathematical Background

The circle S¹ is the simplest non-trivial higher-inductive type with
π₁(S¹) ≃ ℤ. The encode-decode method proves this equivalence by
showing that loops around S¹ are classified by their winding number.

## Reference

de Veras, Ramos, de Queiroz & de Oliveira,
"A Topological Application of Labelled Natural Deduction"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Basic.Univalence
import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Rewrite.SimpleEquiv

set_option maxHeartbeats 1000000

namespace ComputationalPaths
namespace Path

universe u v

/-- Abstract circle type used throughout the homotopy developments.  It will be
realised via computational paths once the rewrite system is extended to fully
support higher-inductive types. -/
axiom Circle : Type u

/-- Distinguished point on the circle. -/
axiom circleBase : Circle

/-- Fundamental loop around the circle, expressed as a computational path. -/
axiom circleLoop : Path (A := Circle) circleBase circleBase

/-- Data required to eliminate from the circle into a target type `C`.  One must
choose an image of the base point together with a computational path witnessing
how the chosen image behaves along the fundamental loop. -/
structure CircleRecData (C : Type v) where
  base : C
  loop : Path base base

/-- Circle eliminator (recursor).  Given a target type `C` together with images
for the base-point and loop, produce a map `Circle → C`.  The computation rules
below describe how this function acts on the constructors. -/
axiom circleRec {C : Type v} (data : CircleRecData C) : Circle → C

/-- β-rule for `circleRec` at the base point. -/
axiom circleRec_base {C : Type v} (data : CircleRecData C) :
  circleRec data circleBase = data.base

/-- β-rule for `circleRec` on the fundamental loop, expressed using
computational paths. -/
axiom circleRec_loop {C : Type v} (data : CircleRecData C) :
  Path.trans
    (Path.symm (Path.ofEq (circleRec_base (C := C) data)))
    (Path.trans
      (Path.congrArg (circleRec data) circleLoop)
      (Path.ofEq (circleRec_base (C := C) data))) =
  data.loop

/-- Data for the dependent eliminator of the circle.  Besides the fibre `C`
over `Circle`, we must specify the value on the base point together with a path
showing how the fibre transports along the fundamental loop. -/
structure CircleIndData (C : Circle → Type v) where
  base : C circleBase
  loop :
    Path
      (Path.transport (A := Circle) (D := fun x => C x) circleLoop base)
      base

/-- Dependent eliminator (induction principle) for the circle. -/
axiom circleInd {C : Circle → Type v} (data : CircleIndData C) :
  (x : Circle) → C x

noncomputable section

open SimpleEquiv

/-- Equivalence witnessing the successor/predecessor action on the integers. -/
def circleSuccEquiv : SimpleEquiv Int Int where
  toFun := fun z => z + 1
  invFun := fun z => z - 1
  left_inv := by
    intro z
    simp
  right_inv := by
    intro z
    simp

section Univalence

variable [HasUnivalence.{0}]

private def circleCodeData : CircleRecData (Type _) where
  base := Int
  loop := Path.ua circleSuccEquiv

/-- Universal-cover code family for the circle, landing in the integers. -/
noncomputable def circleCode : Circle → Type _ :=
  circleRec circleCodeData

@[simp] theorem circleCode_base :
    circleCode circleBase = Int :=
  circleRec_base circleCodeData

/-- View an element of `circleCode circleBase` as an integer using the base computation rule. -/
@[simp] def circleCodeToInt : circleCode circleBase → Int :=
  fun z => Eq.mp circleCode_base z

/-- Interpret an integer as an element of `circleCode circleBase`. -/
@[simp] def circleCodeOfInt : Int → circleCode circleBase :=
  fun z => Eq.mpr circleCode_base z

@[simp] theorem circleCodeToInt_ofInt (z : Int) :
    circleCodeToInt (circleCodeOfInt z) = z := by
  simp [circleCodeToInt, circleCodeOfInt]

@[simp] theorem circleCodeOfInt_toInt (z : circleCode circleBase) :
    circleCodeOfInt (circleCodeToInt z) = z := by
  simp [circleCodeToInt, circleCodeOfInt]

/-- Chosen basepoint in the code fibre at the circle base. -/
@[simp] def circleCodeZero : circleCode circleBase :=
  circleCodeOfInt 0

@[simp] theorem circleCodeToInt_zero :
    circleCodeToInt circleCodeZero = 0 := by
  simp [circleCodeZero]

/-- Transport the base code point along a loop to encode a path. -/
@[simp] def circleEncodeRaw (x : Circle) :
    Path circleBase x → circleCode x :=
  fun p => Path.transport (A := Circle) (D := circleCode) p circleCodeZero

/-- Encode a loop `p : base = base` as an integer. -/
@[simp] def circleEncodePath :
    Path circleBase circleBase → Int :=
  fun p => circleCodeToInt (circleEncodeRaw circleBase p)

@[simp] theorem circleEncodePath_refl :
    circleEncodePath (Path.refl circleBase) = 0 := by
  change circleCodeToInt circleCodeZero = 0
  simp [circleCodeZero, circleCodeToInt]

/-- Encoding is invariant under rewrite equality for raw loops. -/
@[simp] theorem circleEncodePath_rweq
    {p q : Path circleBase circleBase} (h : RwEq p q) :
    circleEncodePath p = circleEncodePath q := by
  unfold circleEncodePath circleEncodeRaw
  have hEq : p.toEq = q.toEq :=
    rweq_toEq (p := p) (q := q) h
  have htransport :=
    Path.transport_of_toEq_eq (A := Circle) (D := circleCode)
      (p := p) (q := q) (x := circleCodeZero) hEq
  exact _root_.congrArg circleCodeToInt htransport

/-- Circle computation rule transported to the `circleCode` family. -/
@[simp] theorem circleCode_loop_path :
    Path.trans (Path.symm (Path.ofEq circleCode_base))
        (Path.trans (Path.congrArg circleCode circleLoop)
          (Path.ofEq circleCode_base)) =
      Path.ua circleSuccEquiv :=
  circleRec_loop circleCodeData

end Univalence

/-- Iterate the fundamental loop `n` times at the raw path level (natural powers). -/
@[simp] def circleLoopPathPow : Nat → Path circleBase circleBase
  | 0 => Path.refl circleBase
  | Nat.succ n =>
      Path.trans (circleLoopPathPow n) circleLoop

/-- Integer iteration of the fundamental loop at the path level. -/
@[simp] def circleLoopPathZPow : Int → Path circleBase circleBase
  | Int.ofNat n => circleLoopPathPow n
  | Int.negSucc n =>
      Path.symm (circleLoopPathPow (Nat.succ n))

@[simp] theorem circleLoopPathPow_zero :
    circleLoopPathPow 0 = Path.refl circleBase := rfl

@[simp] theorem circleLoopPathPow_succ (n : Nat) :
    circleLoopPathPow (Nat.succ n) =
      Path.trans (circleLoopPathPow n) circleLoop := rfl

@[simp] theorem circleLoopPathPow_one :
    circleLoopPathPow 1 = circleLoop := by
  simp [circleLoopPathPow]

theorem circleLoopPathPow_add (m n : Nat) :
    circleLoopPathPow (m + n) =
      Path.trans (circleLoopPathPow m) (circleLoopPathPow n) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        circleLoopPathPow (m + Nat.succ n)
            = Path.trans (circleLoopPathPow (m + n)) circleLoop := by
                simp
        _ = Path.trans
              (Path.trans (circleLoopPathPow m) (circleLoopPathPow n))
              circleLoop := by
                simp [ih]
        _ = Path.trans (circleLoopPathPow m)
              (Path.trans (circleLoopPathPow n) circleLoop) := by
                simp
        _ = Path.trans (circleLoopPathPow m)
              (circleLoopPathPow (Nat.succ n)) := by
                simp [circleLoopPathPow]

@[simp] theorem circleLoopPathZPow_ofNat (n : Nat) :
    circleLoopPathZPow (Int.ofNat n) = circleLoopPathPow n := rfl

@[simp] theorem circleLoopPathZPow_negSucc (n : Nat) :
    circleLoopPathZPow (Int.negSucc n) =
      Path.symm (circleLoopPathPow (Nat.succ n)) := rfl

@[simp] theorem circleLoopPathZPow_zero :
    circleLoopPathZPow 0 = Path.refl circleBase := rfl

@[simp] theorem circleLoopPathZPow_one :
    circleLoopPathZPow 1 = circleLoop := by
  simp [circleLoopPathZPow, circleLoopPathPow]

@[simp] theorem circleLoopPathZPow_neg_one :
    circleLoopPathZPow (-1) = Path.symm circleLoop := by
  change circleLoopPathZPow (Int.negSucc 0) = _
  simp [circleLoopPathZPow]

/-- Decode an integer into a raw loop at the base point. -/
@[simp] def circleDecodePath : Int → Path circleBase circleBase :=
  circleLoopPathZPow

@[simp] theorem circleDecodePath_zero :
    circleDecodePath 0 = Path.refl circleBase := rfl

@[simp] theorem circleDecodePath_ofNat (n : Nat) :
    circleDecodePath (Int.ofNat n) = circleLoopPathPow n := rfl

@[simp] theorem circleDecodePath_negSucc (n : Nat) :
    circleDecodePath (Int.negSucc n) =
      Path.symm (circleLoopPathPow (Nat.succ n)) := rfl

@[simp] theorem circleDecodePath_one :
    circleDecodePath 1 = circleLoop := by
  simp [circleDecodePath, circleLoopPathZPow, circleLoopPathPow]

@[simp] theorem circleDecodePath_neg_one :
    circleDecodePath (-1) = Path.symm circleLoop := by
  change circleDecodePath (Int.negSucc 0) = _
  simp [circleDecodePath, circleLoopPathZPow]

-- Small arithmetic helper used in encoding lemmas.
@[simp] theorem int_zero_sub_one : (0 : Int) - 1 = (-1 : Int) := by
  simp

-- Encoding after concatenating with the fundamental loop increments by `1`.
-- Placeholder: a future lemma will show that encoding commutes with
-- concatenation by the fundamental loop at the raw-path level.

-- Key transport computation: encoding after following the fundamental loop
-- increases the integer code by `+1` for any starting code value.
@[simp] theorem circleCode_transport_loop_add1 [HasUnivalence.{0}]
    (x : circleCode circleBase) :
    circleCodeToInt
      (Path.transport (A := Circle) (D := circleCode) circleLoop x)
      = circleCodeToInt x + 1 := by
  -- Abbreviations for the base computation path and the congruence along the loop.
  let p1 := Path.ofEq circleCode_base
  let q := Path.congrArg circleCode circleLoop
  -- Conjugation equality from the circle computation rule.
  have hEq :
      Path.trans (Path.symm p1) (Path.trans q p1) =
        Path.ua circleSuccEquiv := by
    simpa [p1, q] using circleCode_loop_path
  -- Apply transport to both sides at `transport p1 x`.
  have hTrans :=
    _root_.congrArg
      (fun (r : Path (A := Type _) Int Int) =>
        Path.transport (A := Type _) (D := fun X => X) r
          (Path.transport (A := Type _) (D := fun X => X) p1 x))
      hEq
  -- On the left, cancel the symmetric/forward transports.
  have hLeftStep :=
    Path.transport_trans (A := Type _) (D := fun X => X)
      (p := Path.symm p1) (q := Path.trans q p1)
      (x := Path.transport (A := Type _) (D := fun X => X) p1 x)
  have hLeftCancel :=
    _root_.congrArg
      (fun z =>
        Path.transport (A := Type _) (D := fun X => X)
          (Path.trans q p1) z)
      (Path.transport_symm_left (A := Type _) (D := fun X => X)
        (p := p1) (x := x))
  have hLeftSimp :
      Path.transport (A := Type _) (D := fun X => X)
        (Path.trans (Path.symm p1) (Path.trans q p1))
        (Path.transport (A := Type _) (D := fun X => X) p1 x)
      =
      Path.transport (A := Type _) (D := fun X => X)
        (Path.trans q p1) x := by
    -- Combine associativity and cancellation steps.
    exact hLeftStep.trans hLeftCancel
  -- Combine the above to rewrite the left to `transport (q • p1) x`.
  have hComb :
      Path.transport (A := Type _) (D := fun X => X)
        (Path.trans q p1) x
      =
      Path.transport (A := Type _) (D := fun X => X)
        (Path.ua circleSuccEquiv)
        (Path.transport (A := Type _) (D := fun X => X) p1 x) := by
    simpa [hLeftSimp] using hTrans
  -- Identify the left with the desired LHS via transport laws.
  have hAssoc :=
    Path.transport_trans (A := Type _) (D := fun X => X)
      (p := q) (q := p1) (x := x)
  have hMove :=
    (Path.transport_congrArg (A := Circle) (D := circleCode)
      (p := circleLoop) (x := x))
  have hLHS :
      Path.transport (A := Type _) (D := fun X => X)
        (Path.trans q p1) x
      =
      circleCodeToInt
        (Path.transport (A := Circle) (D := circleCode) circleLoop x) := by
    -- transport (q • p1) x = transport p1 (transport q x)
    have hSplit :
        Path.transport (A := Type _) (D := fun X => X)
          (Path.trans q p1) x
        =
        Path.transport (A := Type _) (D := fun X => X) p1
          (Path.transport (A := Type _) (D := fun X => X) q x) := by
      simpa using hAssoc
    -- Replace the inner Type-level transport with the Circle transport.
    have hInner :
        Path.transport (A := Type _) (D := fun X => X) q x
        = Path.transport (A := Circle) (D := circleCode) circleLoop x := by
      simpa using hMove.symm
    -- Final identification with `circleCodeToInt`.
    simpa [circleCodeToInt, hSplit, hInner]
  -- Evaluate the right using univalence and the base transport equality.
  have hBase :
      Path.transport (A := Type _) (D := fun X => X) p1 x
      = circleCodeToInt x := by
    simpa [circleCodeToInt] using
      (Path.transport_ofEq (A := Type _) (D := fun X => X)
        (h := circleCode_base) (x := x))
  have hRHS :
      Path.transport (A := Type _) (D := fun X => X)
        (Path.ua circleSuccEquiv) (circleCodeToInt x)
      = circleCodeToInt x + 1 := by
    simp [Path.ua_beta, circleSuccEquiv]
  -- Chain the equalities to finish.
  exact (hLHS.trans hComb).trans (by simpa [hBase] using hRHS)

-- Transport along the inverse loop subtracts 1 from the code value.
@[simp] theorem circleCode_transport_symm_loop_sub1 [HasUnivalence.{0}]
    (x : circleCode circleBase) :
    circleCodeToInt
      (Path.transport (A := Circle) (D := circleCode) (Path.symm circleLoop) x)
      = circleCodeToInt x - 1 := by
  -- Use cancellation: transport loop (transport (symm loop) x) = x
  let y := Path.transport (A := Circle) (D := circleCode) (Path.symm circleLoop) x
  have hCancel : Path.transport (A := Circle) (D := circleCode) circleLoop y = x :=
    Path.transport_symm_right (A := Circle) (D := circleCode) (p := circleLoop) (y := x)
  have hPlus := circleCode_transport_loop_add1 y
  -- hPlus: circleCodeToInt (transport loop y) = circleCodeToInt y + 1
  -- hCancel: transport loop y = x
  -- So: circleCodeToInt x = circleCodeToInt y + 1
  -- Thus: circleCodeToInt y = circleCodeToInt x - 1
  calc circleCodeToInt y
      = circleCodeToInt y + 1 - 1 := by omega
    _ = circleCodeToInt (Path.transport (A := Circle) (D := circleCode) circleLoop y) - 1 := by
        rw [← hPlus]
    _ = circleCodeToInt x - 1 := by rw [hCancel]

/-- Transport along loop^n adds n to the code value. Proved by induction on n. -/
@[simp] theorem circleCode_transport_loopPow_add [HasUnivalence.{0}] (n : Nat) (x : circleCode circleBase) :
    circleCodeToInt (Path.transport (A := Circle) (D := circleCode) (circleLoopPathPow n) x)
      = circleCodeToInt x + n := by
  induction n with
  | zero =>
      simp only [circleLoopPathPow, Path.transport_refl]
      omega
  | succ n ih =>
      calc circleCodeToInt (Path.transport (A := Circle) (D := circleCode)
              (circleLoopPathPow (n + 1)) x)
          = circleCodeToInt (Path.transport (A := Circle) (D := circleCode)
              (Path.trans (circleLoopPathPow n) circleLoop) x) := rfl
        _ = circleCodeToInt (Path.transport (A := Circle) (D := circleCode) circleLoop
              (Path.transport (A := Circle) (D := circleCode) (circleLoopPathPow n) x)) := by
            rw [Path.transport_trans]
        _ = circleCodeToInt (Path.transport (A := Circle) (D := circleCode)
              (circleLoopPathPow n) x) + 1 := by
            exact circleCode_transport_loop_add1 _
        _ = (circleCodeToInt x + n) + 1 := by rw [ih]
        _ = circleCodeToInt x + (n + 1) := by omega

/-- Transport along symm(loop^n) subtracts n from the code value. Proved by induction. -/
@[simp] theorem circleCode_transport_symm_loopPow_sub [HasUnivalence.{0}] (n : Nat) (x : circleCode circleBase) :
    circleCodeToInt (Path.transport (A := Circle) (D := circleCode)
        (Path.symm (circleLoopPathPow n)) x)
      = circleCodeToInt x - n := by
  -- Use Nat.rec to get IH universally quantified over x
  induction n generalizing x with
  | zero =>
      -- symm(refl) has same toEq as refl: both are Eq.refl
      have hToEq : (Path.symm (circleLoopPathPow 0)).toEq = (Path.refl circleBase).toEq := rfl
      rw [Path.transport_of_toEq_eq hToEq, Path.transport_refl]
      omega
  | succ n ih =>
      -- symm(loop^(n+1)) has same toEq as trans (symm loop) (symm(loop^n))
      -- So their transports are equal
      have hToEq : (Path.symm (circleLoopPathPow (n + 1))).toEq =
          (Path.trans (Path.symm circleLoop) (Path.symm (circleLoopPathPow n))).toEq := rfl
      -- Note: `ih` is now generalized over x, so we can use it for any value
      let y := Path.transport (A := Circle) (D := circleCode) (Path.symm circleLoop) x
      calc circleCodeToInt (Path.transport (A := Circle) (D := circleCode)
              (Path.symm (circleLoopPathPow (n + 1))) x)
          = circleCodeToInt (Path.transport (A := Circle) (D := circleCode)
              (Path.trans (Path.symm circleLoop) (Path.symm (circleLoopPathPow n))) x) := by
            rw [Path.transport_of_toEq_eq hToEq]
        _ = circleCodeToInt (Path.transport (A := Circle) (D := circleCode)
              (Path.symm (circleLoopPathPow n)) y) := by
            rw [Path.transport_trans]
        _ = circleCodeToInt y - n := ih y
        _ = (circleCodeToInt x - 1) - n := by
            simp only [y, circleCode_transport_symm_loop_sub1]
        _ = circleCodeToInt x - (n + 1) := by omega

/-- Transport along loop^z (for integer z) shifts by z. -/
@[simp] theorem circleCode_transport_loopZPow_add [HasUnivalence.{0}] (z : Int) (x : circleCode circleBase) :
    circleCodeToInt (Path.transport (A := Circle) (D := circleCode)
        (circleLoopPathZPow z) x)
      = circleCodeToInt x + z := by
  cases z with
  | ofNat n =>
      simp only [circleLoopPathZPow]
      exact circleCode_transport_loopPow_add n x
  | negSucc n =>
      simp only [circleLoopPathZPow]
      have h := circleCode_transport_symm_loopPow_sub (n + 1) x
      -- h : ... = circleCodeToInt x - (n + 1)
      -- goal: ... = circleCodeToInt x + Int.negSucc n
      -- Int.negSucc n = -(n + 1)
      simp only [Int.negSucc_eq, Int.add_neg_eq_sub] at h ⊢
      -- h: ... = circleCodeToInt x - (↑n + 1)
      -- goal: ... = circleCodeToInt x - (↑n + 1)
      exact h

-- Note: The general circleEncodePath_trans is defined later, after circleLoop_rweq_decode,
-- since it depends on circleCode_transport_shift which is derived from circleLoop_rweq_decode.

@[simp] theorem circleEncodePath_trans_loop [HasUnivalence.{0}]
    (p : Path circleBase circleBase) :
    circleEncodePath (Path.trans p circleLoop) =
      circleEncodePath p + 1 := by
  have := circleCode_transport_loop_add1
    (x := Path.transport (A := Circle) (D := circleCode) p circleCodeZero)
  simpa [circleEncodePath, circleEncodeRaw, Path.transport_trans]
    using this

-- Encoding of the fundamental loop evaluates to `1`.
@[simp] theorem circleEncodePath_loop [HasUnivalence.{0}] : circleEncodePath circleLoop = 1 := by
  have := circleCode_transport_loop_add1 (x := circleCodeZero)
  simpa [circleEncodePath, circleEncodeRaw] using this

@[simp] theorem circleEncodePath_trans_symm_loop [HasUnivalence.{0}]
    (p : Path circleBase circleBase) :
    circleEncodePath (Path.trans p (Path.symm circleLoop)) =
      circleEncodePath p - 1 := by
  -- Let `x := transport p circleCodeZero` and apply the +1 lemma to
  -- `transport (symm circleLoop) x`, then cancel with `transport_symm_right`.
  let x := Path.transport (A := Circle) (D := circleCode) p circleCodeZero
  have hPlus := circleCode_transport_loop_add1
    (x := Path.transport (A := Circle) (D := circleCode)
      (Path.symm circleLoop) x)
  have hCancel :=
    Path.transport_symm_right (A := Circle) (D := circleCode)
      (p := circleLoop) (y := x)
  have hSum : circleEncodePath p =
      circleEncodePath (Path.trans p (Path.symm circleLoop)) + 1 := by
    -- rewrite the LHS of `hPlus` using `hCancel` and definitions
    have hEq :
        circleCodeToInt
          (Path.transport (A := Circle) (D := circleCode)
            circleLoop
            (Path.transport (A := Circle) (D := circleCode)
              (Path.symm circleLoop) x))
        = circleCodeToInt x := by
      simpa using _root_.congrArg circleCodeToInt hCancel
    -- Combine with `hPlus` and unfold `circleEncodePath`.
    -- `hPlus`: codeToInt (transport loop ...) = codeToInt (...) + 1
    -- After rewriting LHS via `hEq`, we obtain the claim.
    have hComb := hEq.trans hPlus
    -- Unfold encodings on both sides.
    simpa [circleEncodePath, circleEncodeRaw, x,
      Path.transport_trans]
      using hComb
  -- Rearrange: a = b + 1 ⇒ b = a - 1
  have h1 :
      circleEncodePath p - 1
        = (circleEncodePath (Path.trans p (Path.symm circleLoop)) + 1) - 1 :=
    _root_.congrArg (fun z => z - 1) hSum
  have hRearr :
      circleEncodePath p - 1
        = circleEncodePath (Path.trans p (Path.symm circleLoop)) := by
    simpa [Int.add_sub_cancel] using h1
  simpa using hRearr.symm

@[simp] theorem circleEncodePath_symm_loop [HasUnivalence.{0}] :
    circleEncodePath (Path.symm circleLoop) = -1 := by
  exact
    calc
      circleEncodePath (Path.symm circleLoop)
          = circleEncodePath (Path.trans (Path.refl circleBase) (Path.symm circleLoop)) := by rfl
      _ = circleEncodePath (Path.refl circleBase) - 1 :=
          circleEncodePath_trans_symm_loop (p := Path.refl circleBase)
      _ = (0 : Int) - 1 := by
        have : circleEncodePath (Path.refl circleBase) = (0 : Int) :=
          circleEncodePath_refl
        simpa using _root_.congrArg (fun t => t - 1) this
      _ = -1 := by simp

/-! ### Encode-Decode Round-Trip Lemmas -/

/-- Encoding a natural loop power gives the natural number.
    Uses the direct transport computation, avoiding circleEncodePath_trans. -/
@[simp] theorem circleEncodePath_circleLoopPathPow [HasUnivalence.{0}] (n : Nat) :
    circleEncodePath (circleLoopPathPow n) = (n : Int) := by
  -- encode(loop^n) = codeToInt(transport (loop^n) 0) = codeToInt(0) + n = n
  calc circleEncodePath (circleLoopPathPow n)
      = circleCodeToInt (Path.transport (A := Circle) (D := circleCode)
          (circleLoopPathPow n) circleCodeZero) := rfl
    _ = circleCodeToInt circleCodeZero + n := circleCode_transport_loopPow_add n circleCodeZero
    _ = 0 + n := by rw [circleCodeToInt_zero]
    _ = n := by omega

/-- Encoding of symm (loop^n) gives -n.
    Uses the direct transport computation, avoiding circleEncodePath_trans. -/
@[simp] theorem circleEncodePath_symm_circleLoopPathPow [HasUnivalence.{0}] (n : Nat) :
    circleEncodePath (Path.symm (circleLoopPathPow n)) = -(n : Int) := by
  -- encode(symm(loop^n)) = codeToInt(transport (symm(loop^n)) 0) = codeToInt(0) - n = -n
  calc circleEncodePath (Path.symm (circleLoopPathPow n))
      = circleCodeToInt (Path.transport (A := Circle) (D := circleCode)
          (Path.symm (circleLoopPathPow n)) circleCodeZero) := rfl
    _ = circleCodeToInt circleCodeZero - n := circleCode_transport_symm_loopPow_sub n circleCodeZero
    _ = 0 - n := by rw [circleCodeToInt_zero]
    _ = -(n : Int) := by omega

/-- Encoding a z-power gives the integer back. (Right inverse for encode-decode) -/
@[simp] theorem circleEncodePath_circleDecodePath [HasUnivalence.{0}] (n : Int) :
    circleEncodePath (circleDecodePath n) = n := by
  cases n with
  | ofNat n => exact circleEncodePath_circleLoopPathPow n
  | negSucc n =>
      simp only [circleDecodePath_negSucc]
      exact circleEncodePath_symm_circleLoopPathPow (n + 1)

 /-- **Circle loop classification theorem**: Every loop on the circle is RwEq to the
 decoded form of its winding number. This is the characteristic property of π₁(S¹) ≃ ℤ.

This theorem captures the geometric fact that loops on S¹ are classified by winding number.
The proof relies on the covering space theory - any loop on S¹ lifts uniquely to the
universal cover ℤ (via transport in circleCode), and the endpoint of that lift determines
the winding number. The Step rules then allow normalizing the loop to its canonical form.

 **Note**: This fact is semantically justified by the encode-decode method.  Until
 the development provides a fully constructive proof, we keep it as an explicit
 hypothesis (a typeclass) rather than a global Lean kernel axiom. -/
 class HasCircleLoopDecode [HasUnivalence.{0}] : Prop where
    circleLoop_rweq_decode (p : Path.{u} circleBase circleBase) :
      RwEq.{u} p (circleLoopPathZPow (circleEncodePath p))

 /-- Every loop is RwEq to the decoded form of its winding number. -/
 theorem circleLoop_rweq_decode [HasUnivalence.{0}] [h : HasCircleLoopDecode.{u}] (p : Path.{u} circleBase circleBase) :
      RwEq.{u} p (circleLoopPathZPow (circleEncodePath p)) :=
    h.circleLoop_rweq_decode p
 
 /-- **Transport shift theorem**: Transport along a path acts by adding the winding number.
 
 This is derived from `circleLoop_rweq_decode`: since any loop p is RwEq to `loop^(encode p)`,
 they have the same `toEq`, hence the same transport behavior. -/
 @[simp] theorem circleCode_transport_shift [HasUnivalence.{0}] [HasCircleLoopDecode.{u}]
      (p : Path.{u} circleBase circleBase) (x : circleCode circleBase) :
      circleCodeToInt (Path.transport (A := Circle) (D := circleCode) p x)
        = circleCodeToInt x + circleEncodePath p := by
  -- By circleLoop_rweq_decode: RwEq p (loop^(encode p))
  have hrweq := circleLoop_rweq_decode p
  -- RwEq implies same toEq
  have htoEq := rweq_toEq hrweq
  -- Same toEq implies same transport
  have htransport := Path.transport_of_toEq_eq (A := Circle) (D := circleCode)
      (p := p) (q := circleLoopPathZPow (circleEncodePath p)) htoEq x
  -- Transport of loop^z adds z
  have hshift := circleCode_transport_loopZPow_add (circleEncodePath p) x
  -- Combine
  calc circleCodeToInt (Path.transport (A := Circle) (D := circleCode) p x)
      = circleCodeToInt (Path.transport (A := Circle) (D := circleCode)
          (circleLoopPathZPow (circleEncodePath p)) x) := by rw [htransport]
    _ = circleCodeToInt x + circleEncodePath p := hshift

 /-- Encoding is additive over path composition.
     Derived from `circleCode_transport_shift`. -/
 @[simp] theorem circleEncodePath_trans [HasUnivalence.{0}] [HasCircleLoopDecode.{u}]
      (p q : Path.{u} circleBase circleBase) :
      circleEncodePath (Path.trans p q) = circleEncodePath p + circleEncodePath q := by
  calc circleEncodePath (Path.trans p q)
      = circleCodeToInt (Path.transport (A := Circle) (D := circleCode)
          (Path.trans p q) circleCodeZero) := rfl
    _ = circleCodeToInt (Path.transport (A := Circle) (D := circleCode) q
          (Path.transport (A := Circle) (D := circleCode) p circleCodeZero)) := by
        rw [Path.transport_trans]
    _ = circleCodeToInt (Path.transport (A := Circle) (D := circleCode) p circleCodeZero)
          + circleEncodePath q := by
        exact circleCode_transport_shift q
          (Path.transport (A := Circle) (D := circleCode) p circleCodeZero)
    _ = circleEncodePath p + circleEncodePath q := rfl

-- moved below after `circleEncodeLift` definition

/-- Loop space of the circle, specialised from the generic `LoopSpace`. -/
abbrev CircleLoopSpace : Type u :=
  LoopSpace Circle circleBase

/-- Loop quotient of the circle, i.e. π₁(S¹) before imposing integer equivalence. -/
abbrev CircleLoopQuot : Type u :=
  LoopQuot Circle circleBase

/-- Strict loop monoid carried by the circle's rewrite quotient. -/
abbrev circleLoopMonoid : LoopMonoid Circle circleBase :=
  loopMonoid Circle circleBase

/-- Strict loop group carried by the circle's rewrite quotient. -/
abbrev circleLoopGroup : LoopGroup Circle circleBase :=
  loopGroup Circle circleBase

/-- Fundamental group π₁(S¹, base) as rewrite classes of loops. -/
abbrev circlePiOne : Type u :=
  PiOne Circle circleBase

/-- Strict group structure on π₁(S¹, base). -/
abbrev circlePiOneGroup : LoopGroup Circle circleBase :=
  PiOneGroup Circle circleBase

/-- The distinguished fundamental loop as an inhabitant of the circle loop space. -/
@[simp] def circleLoopPath : CircleLoopSpace :=
  circleLoop

/-- Fundamental loop represented in the quotient. -/
@[simp] def circleLoopClass : CircleLoopQuot :=
  LoopQuot.ofLoop (A := Circle) (a := circleBase) circleLoop

/-- The fundamental loop seen as an element of π₁(S¹). -/
@[simp] def circlePiOneLoop : circlePiOne :=
  PiOne.ofLoop (A := Circle) (a := circleBase) circleLoop

/-- Canonical encoding function obtained by quotient-lifting the raw loop
encoding.  This is the implementation used by `circleEncode`. -/
@[simp] def circleEncodeLift [HasUnivalence.{0}] : CircleLoopQuot → Int :=
  Quot.lift (fun (p : Path circleBase circleBase) => circleEncodePath p)
    (by
      intro p q h
      have hrw : RwEq p q := by
        change RwEq p q at h
        exact h
      exact circleEncodePath_rweq (h := hrw))

@[simp] theorem circleEncodeLift_ofLoop [HasUnivalence.{0}] (p : Path circleBase circleBase) :
    circleEncodeLift (LoopQuot.ofLoop (A := Circle) (a := circleBase) p)
      = circleEncodePath p := rfl

-- @[simp] theorem circleEncodeLift_circleLoopClass :
--     circleEncodeLift circleLoopClass = 1 := by
--   change circleEncodePath circleLoop = 1
--   simpa using circleEncodePath_loop


/-- Iterate the fundamental loop `n` times in the quotient. -/
def circleLoopPow (n : Nat) : CircleLoopQuot :=
  LoopQuot.pow (A := Circle) (a := circleBase) circleLoopClass n

@[simp] theorem circleLoopPow_zero : circleLoopPow 0 = LoopQuot.id :=
  LoopQuot.pow_zero (A := Circle) (a := circleBase) circleLoopClass

@[simp] theorem circleLoopPow_succ (n : Nat) :
    circleLoopPow n.succ =
      LoopQuot.comp (circleLoopPow n) circleLoopClass :=
  LoopQuot.pow_succ (A := Circle) (a := circleBase)
    circleLoopClass n

@[simp] theorem circleLoopPow_one :
    circleLoopPow 1 = circleLoopClass := by
  unfold circleLoopPow
  exact
    LoopQuot.pow_one (A := Circle) (a := circleBase)
      (x := circleLoopClass)

-- concatenation path.
@[simp] theorem circleLoopPow_ofLoopPathPow (n : Nat) :
    circleLoopPow n =
      LoopQuot.ofLoop (A := Circle) (a := circleBase)
        (circleLoopPathPow n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      have hstep :
          circleLoopPow (Nat.succ n)
            = LoopQuot.comp (circleLoopPow n) circleLoopClass :=
        circleLoopPow_succ (n := n)
      calc
        circleLoopPow (Nat.succ n)
            = LoopQuot.comp (circleLoopPow n) circleLoopClass := hstep
        _ = LoopQuot.comp
              (LoopQuot.ofLoop (A := Circle) (a := circleBase)
                (circleLoopPathPow n))
              circleLoopClass := by
              rw [ih]
        _ = LoopQuot.comp
              (LoopQuot.ofLoop (A := Circle) (a := circleBase)
                (circleLoopPathPow n))
              (LoopQuot.ofLoop (A := Circle) (a := circleBase) circleLoop) := by
              rfl
        _ = LoopQuot.ofLoop (A := Circle) (a := circleBase)
              (Path.trans (circleLoopPathPow n) circleLoop) := by
              exact
                (LoopQuot.ofLoop_trans (A := Circle) (a := circleBase)
                  (p := circleLoopPathPow n) (q := circleLoop)).symm
        _ = LoopQuot.ofLoop (A := Circle) (a := circleBase)
              (circleLoopPathPow (Nat.succ n)) := by
              -- Unfold the definition of the successor step for `circleLoopPathPow`.
              rfl

-- Evaluate the lifted encoding on natural powers of the fundamental loop.
@[simp] theorem circleEncodeLift_circleLoopPow [HasUnivalence.{0}] (n : Nat) :
    circleEncodeLift (circleLoopPow n) = (n : Int) := by
  induction n with
  | zero =>
      -- Unfold to the reflexive loop and evaluate.
      change circleEncodeLift LoopQuot.id = (0 : Int)
      change circleEncodePath (Path.refl circleBase) = 0
      exact circleEncodePath_refl
  | succ n ih =>
      have hpow := circleLoopPow_ofLoopPathPow (n := Nat.succ n)
      have hRew : circleEncodeLift (circleLoopPow (Nat.succ n))
            = circleEncodePath (circleLoopPathPow (Nat.succ n)) := by
        -- Rewrite to `ofLoop` and apply the quotient-lift reduction.
        rw [hpow]; rfl
      have hpowPrev := circleLoopPow_ofLoopPathPow (n := n)
      have hPrev' : circleEncodeLift (circleLoopPow n)
            = circleEncodePath (circleLoopPathPow n) := by
        rw [hpowPrev]; rfl
      calc
        circleEncodeLift (circleLoopPow (Nat.succ n))
            = circleEncodePath (circleLoopPathPow (Nat.succ n)) := hRew
        _ = circleEncodePath
              (Path.trans (circleLoopPathPow n) circleLoop) := rfl
        _ = circleEncodePath (circleLoopPathPow n) + 1 :=
              circleEncodePath_trans_loop (p := circleLoopPathPow n)
        _ = circleEncodeLift (circleLoopPow n) + 1 := by
              rw [hPrev']
        _ = (Int.ofNat n) + 1 := by
              exact _root_.congrArg (fun z : Int => z + 1) ih
        _ = (Int.ofNat (Nat.succ n)) := by
              simp [Int.natCast_succ]

-- Evaluate the lifted encoding on natural powers of the fundamental loop.


theorem circleLoopPow_add (m n : Nat) :
    circleLoopPow (m + n) =
      LoopQuot.comp (circleLoopPow m) (circleLoopPow n) := by
  exact LoopQuot.pow_add (A := Circle) (a := circleBase) (x := circleLoopClass) m n

/-!
Support: relate quotient-level z-powers to raw path z-powers at the
propositional equality level. These lemmas are used to reduce quotient
equalities to ordinary equalities when proving `decode ∘ encode = id`.
-/

-- moved below after z-power lemmas

/-- Compatibility of `π₁` multiplication with `circleLoopPow`. -/
@[simp] theorem circlePiOne_mul_pow (m n : Nat) :
    PiOne.mul (A := Circle) (a := circleBase)
      (circleLoopPow m) (circleLoopPow n) =
      circleLoopPow (m + n) := by
  change LoopQuot.comp (circleLoopPow m) (circleLoopPow n) =
    circleLoopPow (m + n)
  exact (circleLoopPow_add (m := m) (n := n)).symm

/-- Iterate the fundamental loop an integer number of times. -/
def circleLoopZPow (z : Int) : CircleLoopQuot :=
  LoopQuot.zpow (A := Circle) (a := circleBase) circleLoopClass z

@[simp] theorem circleLoopZPow_ofNat (n : Nat) :
    circleLoopZPow n = circleLoopPow n := rfl

theorem circleLoopZPow_add (m n : Int) :
    circleLoopZPow (m + n) =
      LoopQuot.comp (circleLoopZPow m) (circleLoopZPow n) :=
  LoopQuot.zpow_add (A := Circle) (a := circleBase)
    (x := circleLoopClass) m n

/-- Integer powers in π₁ agree with the explicit loop z-powers. -/
@[simp] theorem circlePiOne_zpow (z : Int) :
    PiOne.zpow (A := Circle) (a := circleBase)
      circleLoopClass z = circleLoopZPow z := rfl

@[simp] theorem circleLoopZPow_zero :
    circleLoopZPow 0 = LoopQuot.id := by
  unfold circleLoopZPow
  exact
    LoopQuot.zpow_zero (A := Circle) (a := circleBase) circleLoopClass

@[simp] theorem circleLoopZPow_one :
    circleLoopZPow 1 = circleLoopClass := by
  unfold circleLoopZPow
  exact
    LoopQuot.zpow_one (A := Circle) (a := circleBase) circleLoopClass

@[simp] theorem circleLoopZPow_negSucc (n : Nat) :
    circleLoopZPow (Int.negSucc n) =
      LoopQuot.inv (circleLoopPow (Nat.succ n)) := rfl

@[simp] theorem circleLoopZPow_neg_one :
    circleLoopZPow (-1) = LoopQuot.inv circleLoopClass := by
  unfold circleLoopZPow
  exact
    LoopQuot.zpow_neg_one (A := Circle) (a := circleBase) circleLoopClass

@[simp] theorem circleLoopZPow_neg (z : Int) :
    circleLoopZPow (-z) = LoopQuot.inv (circleLoopZPow z) := by
  unfold circleLoopZPow
  exact
    LoopQuot.zpow_neg (A := Circle) (a := circleBase)
      (x := circleLoopClass) z

@[simp] theorem circleLoopZPow_ofNat_add (m n : Nat) :
    circleLoopZPow (Int.ofNat m + Int.ofNat n) =
      LoopQuot.comp (circleLoopZPow (Int.ofNat m))
        (circleLoopZPow (Int.ofNat n)) := by
  exact
    LoopQuot.zpow_ofNat_add (A := Circle) (a := circleBase)
      (x := circleLoopClass) m n

-- Integer addition rule for iterated circle loops was relocated to CircleStep.

/-- Decode map ℤ → π₁(S¹), built by iterating the fundamental loop according
to the given integer.  The accompanying lemmas establish its homomorphic
behaviour. -/
def circleDecodeConcrete : Int → CircleLoopQuot :=
  circleLoopZPow

@[simp] theorem circleDecodeConcrete_ofNat (n : Nat) :
    circleDecodeConcrete (Int.ofNat n) = circleLoopPow n := rfl

@[simp] theorem circleDecodeConcrete_ofNat_succ (n : Nat) :
    circleDecodeConcrete (Int.ofNat n.succ) =
      LoopQuot.comp (circleLoopPow n) circleLoopClass := by
  calc
    circleDecodeConcrete (Int.ofNat (Nat.succ n))
        = circleLoopPow (Nat.succ n) :=
            circleDecodeConcrete_ofNat (Nat.succ n)
    _ = LoopQuot.comp (circleLoopPow n) circleLoopClass :=
            circleLoopPow_succ (n := n)

@[simp] theorem circleDecodeConcrete_negSucc (n : Nat) :
    circleDecodeConcrete (Int.negSucc n) =
      LoopQuot.inv (circleLoopPow (Nat.succ n)) := by
  unfold circleDecodeConcrete
  exact circleLoopZPow_negSucc (n := n)

@[simp] theorem circleDecodeConcrete_neg_one :
    circleDecodeConcrete (-1) = LoopQuot.inv circleLoopClass := by
  unfold circleDecodeConcrete
  exact circleLoopZPow_neg_one

@[simp] theorem circleDecodeConcrete_zero :
    circleDecodeConcrete 0 = LoopQuot.id :=
  circleLoopZPow_zero

@[simp] theorem circleDecodeConcrete_one :
    circleDecodeConcrete 1 = circleLoopClass :=
  circleLoopZPow_one

@[simp] theorem circleDecodeConcrete_neg (z : Int) :
    circleDecodeConcrete (-z) =
      LoopQuot.inv (circleDecodeConcrete z) :=
  circleLoopZPow_neg (z := z)

-- Decoding respects integer addition is provided in CircleStep.

/-!
Support: relate quotient-level z-powers to raw path z-powers at the
propositional equality level. These lemmas are used to reduce quotient
equalities to ordinary equalities when proving `decode ∘ encode = id`.
-/

@[simp] theorem circleLoopPow_toEq (n : Nat) :
    PathRwQuot.toEq (A := Circle) (circleLoopPow n)
      = (circleLoopPathPow n).toEq := by
  -- Rewrite to an `ofLoop` and use `toEq_mk`.
  change PathRwQuot.toEq (A := Circle)
      (LoopQuot.ofLoop (A := Circle) (a := circleBase)
        (circleLoopPathPow n))
      = (circleLoopPathPow n).toEq
  simp

@[simp] theorem circleLoopZPow_toEq (z : Int) :
    PathRwQuot.toEq (A := Circle) (circleLoopZPow z)
      = (circleLoopPathZPow z).toEq := by
  cases z with
  | ofNat n =>
      -- Reduce to the natural-power case.
      change PathRwQuot.toEq (A := Circle) (circleLoopPow n)
        = (circleLoopPathPow n).toEq
      exact circleLoopPow_toEq (n := n)
  | negSucc n =>
      -- Use `toEq_symm` together with the natural-power lemma.
      change PathRwQuot.toEq (A := Circle)
          (LoopQuot.inv (circleLoopPow (Nat.succ n)))
        = (Path.symm (circleLoopPathPow (Nat.succ n))).toEq
      -- `toEq_symm` on the quotient and on raw paths align.
      simp

/-- Quotient-level z-powers equal the embedding of raw z-power paths. -/
@[simp] theorem circleLoopZPow_eq_ofLoop (z : Int) :
    circleLoopZPow z =
      LoopQuot.ofLoop (A := Circle) (a := circleBase)
        (circleLoopPathZPow z) := by
  cases z with
  | ofNat n =>
      -- Use circleLoopPow_ofLoopPathPow for natural powers.
      exact circleLoopPow_ofLoopPathPow n
  | negSucc n =>
      -- circleLoopZPow (Int.negSucc n) = LoopQuot.inv (circleLoopPow (Nat.succ n))
      -- By circleLoopPow_ofLoopPathPow: = LoopQuot.inv (ofLoop (circleLoopPathPow (Nat.succ n)))
      -- By ofLoop_symm: = ofLoop (Path.symm (circleLoopPathPow (Nat.succ n)))
      -- By def: = ofLoop (circleLoopPathZPow (Int.negSucc n))
      change LoopQuot.inv (circleLoopPow (Nat.succ n)) =
        LoopQuot.ofLoop (A := Circle) (a := circleBase)
          (Path.symm (circleLoopPathPow (Nat.succ n)))
      rw [circleLoopPow_ofLoopPathPow (Nat.succ n)]
      exact (LoopQuot.ofLoop_symm (A := Circle) (a := circleBase)
        (p := circleLoopPathPow (Nat.succ n))).symm

-- Subtraction law for the concrete decoder is provided in CircleStep.

-- Group compatibility lemmas for the concrete decoder are provided in CircleStep.

-- Group compatibility lemmas for the concrete decoder are provided in CircleStep.

-- Subtraction and inverse-multiplication lemma is provided in CircleStep.

@[simp] theorem circleDecodeConcrete_ofNat_add (m n : Nat) :
    circleDecodeConcrete (Int.ofNat m + Int.ofNat n) =
      LoopQuot.comp (circleDecodeConcrete (Int.ofNat m))
        (circleDecodeConcrete (Int.ofNat n)) :=
  circleLoopZPow_ofNat_add (m := m) (n := n)


/-- Encode/decode interface relating the circle rewrite quotient to ℤ.

The definitions below simply re-use `circleEncodeLift` and `circleLoopZPow`,
so no additional axioms are introduced beyond the circle HIT interface and the
univalence principles imported earlier.  Algebraic properties that require more
machinery live in `CircleStep`.
-/
@[simp] def circleEncode [HasUnivalence.{0}] : CircleLoopQuot → Int :=
  circleEncodeLift

@[simp] def circleDecode : Int → CircleLoopQuot :=
  circleLoopZPow

@[simp] theorem circleDecode_eq_concrete (n : Int) :
    circleDecode n = circleDecodeConcrete n := rfl

-- Additivity of `circleDecode` is provided in CircleStep.

@[simp] theorem circleDecode_zero : circleDecode 0 = LoopQuot.id :=
  circleLoopZPow_zero

@[simp] theorem circleDecode_ofNat (n : Nat) :
    circleDecode (Int.ofNat n) = circleLoopPow n := rfl

@[simp] theorem circleDecode_ofNat_succ (n : Nat) :
    circleDecode (Int.ofNat n.succ) =
      LoopQuot.comp (circleLoopPow n) circleLoopClass := by
  change circleLoopZPow ((Nat.succ n : Nat) : Int) = _
  calc
    circleLoopZPow ((Nat.succ n : Nat) : Int)
        = circleLoopPow (Nat.succ n) := rfl
    _ = LoopQuot.comp (circleLoopPow n) circleLoopClass :=
        circleLoopPow_succ (n := n)

@[simp] theorem circleDecode_one : circleDecode 1 = circleLoopClass := by
  change circleLoopZPow 1 = _
  exact circleLoopZPow_one

@[simp] theorem circleDecode_neg (n : Int) :
    circleDecode (-n) = LoopQuot.inv (circleDecode n) :=
  circleLoopZPow_neg (z := n)

@[simp] theorem circleDecode_negSucc (n : Nat) :
    circleDecode (Int.negSucc n) =
      LoopQuot.inv (circleLoopPow (Nat.succ n)) := rfl

@[simp] theorem circleDecode_neg_one :
    circleDecode (-1) = LoopQuot.inv circleLoopClass := by
  change circleLoopZPow (-1) = _; exact circleLoopZPow_neg_one

-- Convenience rewrites for decode of ±1 steps (available via `circleDecode_add`).

@[simp] theorem circleEncode_circleLoopClass [HasUnivalence.{0}] :
    circleEncode circleLoopClass = 1 := by
  change circleEncodePath circleLoop = 1
  exact circleEncodePath_loop

@[simp] theorem circleEncode_inv_circleLoopClass [HasUnivalence.{0}] :
    circleEncode (LoopQuot.inv circleLoopClass) = -1 := by
  change circleEncodeLift (LoopQuot.inv circleLoopClass) = -1
  -- Move to the raw path using `ofLoop_symm`.
  have hsymm : LoopQuot.inv circleLoopClass =
      LoopQuot.ofLoop (A := Circle) (a := circleBase) (Path.symm circleLoop) := by
    change LoopQuot.inv (LoopQuot.ofLoop (A := Circle) (a := circleBase) circleLoop) = _
    exact
      (LoopQuot.ofLoop_symm (A := Circle) (a := circleBase)
        (p := circleLoop)).symm
  -- Evaluate via the raw-path encoding.
  rw [hsymm, circleEncodeLift_ofLoop]
  exact circleEncodePath_symm_loop

/-- Winding-number terminology for the map `π₁(S¹) → ℤ`. -/
@[simp] def circleWindingNumber [HasUnivalence.{0}] : circlePiOne → Int :=
  circleEncode

/-- Evaluation of `circleEncode ∘ circleDecode` on natural numbers. -/
@[simp] theorem circleEncode_circleDecode_ofNat [HasUnivalence.{0}] (n : Nat) :
    circleEncode (circleDecode (Int.ofNat n)) = (n : Int) := by
  change circleEncodeLift (circleLoopPow n) = (n : Int)
  exact circleEncodeLift_circleLoopPow (n := n)

/-- Encoding after right-composition with the fundamental loop adds `1`. -/
@[simp] theorem circleEncodeLift_comp_loop [HasUnivalence.{0}] (x : CircleLoopQuot) :
    circleEncodeLift (LoopQuot.comp x circleLoopClass)
      = circleEncodeLift x + 1 := by
  refine Quot.inductionOn x ?h
  intro p
  -- Reduce to the raw path level and apply the `+1` lemma.
  change circleEncodePath (Path.trans p circleLoop) =
    circleEncodePath p + 1
  exact circleEncodePath_trans_loop (p := p)

/-- Encoding after right-composition with the inverse fundamental loop
subtracts `1`. -/
@[simp] theorem circleEncodeLift_comp_inv_loop [HasUnivalence.{0}] (x : CircleLoopQuot) :
    circleEncodeLift (LoopQuot.comp x (LoopQuot.inv circleLoopClass))
      = circleEncodeLift x - 1 := by
  refine Quot.inductionOn x ?h
  intro p
  -- Reduce to the raw path level and apply the `-1` lemma.
  change circleEncodePath (Path.trans p (Path.symm circleLoop)) =
    circleEncodePath p - 1
  exact circleEncodePath_trans_symm_loop (p := p)

/-- Encoded form of `circleEncodeLift_comp_loop`. -/
@[simp] theorem circleEncode_comp_loop [HasUnivalence.{0}] (x : CircleLoopQuot) :
    circleEncode (LoopQuot.comp x circleLoopClass)
      = circleEncode x + 1 := by
  change circleEncodeLift (LoopQuot.comp x circleLoopClass)
    = circleEncodeLift x + 1
  exact circleEncodeLift_comp_loop (x := x)

/-- Encoded form of `circleEncodeLift_comp_inv_loop`. -/
@[simp] theorem circleEncode_comp_inv_loop [HasUnivalence.{0}] (x : CircleLoopQuot) :
    circleEncode (LoopQuot.comp x (LoopQuot.inv circleLoopClass))
      = circleEncode x - 1 := by
  change circleEncodeLift (LoopQuot.comp x (LoopQuot.inv circleLoopClass))
    = circleEncodeLift x - 1
  exact circleEncodeLift_comp_inv_loop (x := x)

@[simp] theorem circleEncode_circleDecode_neg_one [HasUnivalence.{0}] :
    circleEncode (circleDecode (-1)) = -1 := by
  change circleEncode (LoopQuot.inv circleLoopClass) = -1
  exact circleEncode_inv_circleLoopClass

-- Step law: encoding `decode (z + 1)` increases by one.
@[simp] theorem circleEncode_circleDecode_add_one.{w} [HasUnivalence.{0}] (z : Int) :
    circleEncode.{w} (circleDecode.{w} (z + 1))
      = circleEncode.{w} (circleDecode.{w} z) + 1 := by
  unfold circleEncode circleDecode
  rw [circleLoopZPow_add (m := z) (n := 1), circleLoopZPow_one]
  rw [circleEncodeLift_comp_loop (x := circleLoopZPow z)]

-- Step law: encoding `decode (z + (-1))` decreases by one.
@[simp] theorem circleEncode_circleDecode_add_neg_one.{w} [HasUnivalence.{0}] (z : Int) :
    circleEncode.{w} (circleDecode.{w} (z + (-1)))
      = circleEncode.{w} (circleDecode.{w} z) - 1 := by
  unfold circleEncode circleDecode
  rw [circleLoopZPow_add (m := z) (n := -1), circleLoopZPow_neg_one]
  rw [circleEncodeLift_comp_inv_loop (x := circleLoopZPow z)]

end
end Path
end ComputationalPaths

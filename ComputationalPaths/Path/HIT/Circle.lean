/-
# The circle as a higher-inductive type (axiomatic skeleton)

This module introduces `Circle` together with its base point, fundamental loop,
and eliminators stated in the computational-path style.  At this stage we work
axiomatically: the constructors and recursors will later be justified by the
normalisation machinery developed for computational paths.

## Encode/decode note

The traditional HoTT encode/decode proof of `π₁(S¹) ≃ ℤ` uses a `Type`-valued
family over the circle whose transport along the fundamental loop acts by
successor on ℤ.  In Lean, equality lives in `Prop` and is proof-irrelevant, so
an axiom asserting that `Eq`-transport along a self-equality computes to a
nontrivial autoequivalence is inconsistent (see `docs/axioms.md`).

To keep the development consistent in standard Lean, we axiomatise only the
*winding-number classification data* needed downstream, packaged as the
typeclass `HasCircleLoopDecode`.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Homotopy.FundamentalGroup

set_option maxHeartbeats 1000000

namespace ComputationalPaths
namespace Path

universe u v

/-- Abstract circle type used throughout the homotopy developments. -/
axiom Circle : Type u

/-- Distinguished point on the circle. -/
axiom circleBase : Circle

/-- The circle is inhabited (by `circleBase`). -/
instance : Nonempty Circle := ⟨circleBase⟩

/-- Fundamental loop around the circle, expressed as a computational path. -/
axiom circleLoop : Path (A := Circle) circleBase circleBase

/-- Data required to eliminate from the circle into a target type `C`. -/
structure CircleRecData (C : Type v) where
  base : C
  loop : Path base base

/-- Circle eliminator (recursor). -/
axiom circleRec {C : Type v} (data : CircleRecData C) : Circle → C

/-- β-rule for `circleRec` at the base point. -/
axiom circleRec_base {C : Type v} (data : CircleRecData C) :
  circleRec data circleBase = data.base

/-- β-rule for `circleRec` on the fundamental loop. -/
axiom circleRec_loop {C : Type v} (data : CircleRecData C) :
  Path.trans
      (Path.symm (Path.ofEq (circleRec_base (C := C) data)))
      (Path.trans
        (Path.congrArg (circleRec data) circleLoop)
        (Path.ofEq (circleRec_base (C := C) data))) =
    data.loop

/-- Data for the dependent eliminator of the circle. -/
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

/-! ## Raw loop powers -/

/-- Iterate the fundamental loop `n` times at the raw path level (natural powers). -/
@[simp] def circleLoopPathPow : Nat → Path circleBase circleBase
  | 0 => Path.refl circleBase
  | Nat.succ n => Path.trans (circleLoopPathPow n) circleLoop

/-- Integer iteration of the fundamental loop at the raw path level. -/
@[simp] def circleLoopPathZPow : Int → Path circleBase circleBase
  | Int.ofNat n => circleLoopPathPow n
  | Int.negSucc n => Path.symm (circleLoopPathPow (Nat.succ n))

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
                simp [circleLoopPathPow]
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

/-! ## Winding-number encode/decode interface -/

/-- Encode/decode data for the circle: winding numbers for raw loops. -/
class HasCircleLoopDecode : Type u where
  /-- Integer winding number assigned to a raw loop. -/
  encodePath : Path circleBase circleBase → Int
  /-- The winding number is invariant under rewrite equality. -/
  encodePath_rweq :
      ∀ {p q : Path circleBase circleBase}, RwEq p q → encodePath p = encodePath q
  /-- Encoding the canonical decoded loop returns the integer. -/
  encodePath_circleDecodePath : ∀ n : Int, encodePath (circleDecodePath n) = n
  /-- Every loop is rewrite-equal to the canonical loop power. -/
  circleLoop_rweq_decode :
      ∀ p : Path circleBase circleBase, RwEq p (circleLoopPathZPow (encodePath p))

/-- Encode a raw loop as an integer winding number. -/
@[simp] def circleEncodePath [HasCircleLoopDecode] (p : Path circleBase circleBase) : Int :=
  HasCircleLoopDecode.encodePath p

/-- Encoding is invariant under rewrite equality for raw loops. -/
@[simp] theorem circleEncodePath_rweq [h : HasCircleLoopDecode] {p q : Path circleBase circleBase}
    (hpq : RwEq p q) :
    circleEncodePath p = circleEncodePath q :=
  h.encodePath_rweq hpq

/-- Encoding a canonical decoded raw loop returns the integer. -/
@[simp] theorem circleEncodePath_circleDecodePath [h : HasCircleLoopDecode] (n : Int) :
    circleEncodePath (circleDecodePath n) = n :=
  h.encodePath_circleDecodePath n

@[simp] theorem circleEncodePath_refl [HasCircleLoopDecode] :
    circleEncodePath (Path.refl circleBase) = 0 := by
  simpa [circleDecodePath_zero] using
    (circleEncodePath_circleDecodePath (n := (0 : Int)))

@[simp] theorem circleEncodePath_loop [HasCircleLoopDecode] :
    circleEncodePath circleLoop = 1 := by
  simpa [circleDecodePath_one] using
    (circleEncodePath_circleDecodePath (n := (1 : Int)))

/-- Every loop is RwEq to the decoded form of its winding number. -/
theorem circleLoop_rweq_decode [h : HasCircleLoopDecode] (p : Path circleBase circleBase) :
    RwEq p (circleLoopPathZPow (circleEncodePath p)) :=
  h.circleLoop_rweq_decode p

/-! ## Loop quotient and fundamental group -/

/-- Loop space of the circle, specialised from the generic `LoopSpace`. -/
abbrev CircleLoopSpace : Type u :=
  LoopSpace Circle circleBase

/-- Loop quotient of the circle, i.e. π₁(S¹). -/
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

/-- Quotient-lifted encoding from loop classes to winding numbers. -/
@[simp] def circleEncodeLift [h : HasCircleLoopDecode] : CircleLoopQuot → Int :=
  Quot.lift (fun p : Path circleBase circleBase => circleEncodePath p)
    (by
      intro p q hpq
      exact circleEncodePath_rweq (h := h) hpq)

@[simp] theorem circleEncodeLift_ofLoop [HasCircleLoopDecode] (p : Path circleBase circleBase) :
    circleEncodeLift (LoopQuot.ofLoop (A := Circle) (a := circleBase) p) = circleEncodePath p := rfl

/-- Iterate the fundamental loop `n` times in the quotient (natural powers). -/
def circleLoopPow (n : Nat) : CircleLoopQuot :=
  LoopQuot.pow (A := Circle) (a := circleBase) circleLoopClass n

@[simp] theorem circleLoopPow_zero : circleLoopPow 0 = LoopQuot.id :=
  LoopQuot.pow_zero (A := Circle) (a := circleBase) circleLoopClass

@[simp] theorem circleLoopPow_succ (n : Nat) :
    circleLoopPow n.succ =
      LoopQuot.comp (circleLoopPow n) circleLoopClass :=
  LoopQuot.pow_succ (A := Circle) (a := circleBase) circleLoopClass n

@[simp] theorem circleLoopPow_one :
    circleLoopPow 1 = circleLoopClass := by
  unfold circleLoopPow
  exact
    LoopQuot.pow_one (A := Circle) (a := circleBase)
      (x := circleLoopClass)

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
              simp [ih]
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
              rfl

theorem circleLoopPow_add (m n : Nat) :
    circleLoopPow (m + n) =
      LoopQuot.comp (circleLoopPow m) (circleLoopPow n) := by
  exact LoopQuot.pow_add (A := Circle) (a := circleBase) (x := circleLoopClass) m n

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

/-- Decode map ℤ → π₁(S¹), built by iterating the fundamental loop according
to the given integer. -/
def circleDecodeConcrete : Int → CircleLoopQuot :=
  circleLoopZPow

@[simp] theorem circleDecodeConcrete_ofNat (n : Nat) :
    circleDecodeConcrete (Int.ofNat n) = circleLoopPow n := rfl

@[simp] theorem circleDecodeConcrete_ofNat_succ (n : Nat) :
    circleDecodeConcrete (Int.ofNat n.succ) =
      LoopQuot.comp (circleLoopPow n) circleLoopClass := by
  calc
    circleDecodeConcrete (Int.ofNat (Nat.succ n))
        = circleLoopPow (Nat.succ n) := by
            rfl
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

@[simp] theorem circleDecodeConcrete_ofNat_add (m n : Nat) :
    circleDecodeConcrete (Int.ofNat m + Int.ofNat n) =
      LoopQuot.comp (circleDecodeConcrete (Int.ofNat m))
        (circleDecodeConcrete (Int.ofNat n)) :=
  circleLoopZPow_ofNat_add (m := m) (n := n)

/-!
Support: relate quotient-level z-powers to raw path z-powers at the equality level.
These lemmas are used to reduce quotient equalities to ordinary equalities when
proving `decode ∘ encode = id`.
-/

@[simp] theorem circleLoopPow_toEq (n : Nat) :
    PathRwQuot.toEq (A := Circle) (circleLoopPow n)
      = (circleLoopPathPow n).toEq := by
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
      change PathRwQuot.toEq (A := Circle) (circleLoopPow n)
        = (circleLoopPathPow n).toEq
      exact circleLoopPow_toEq (n := n)
  | negSucc n =>
      change PathRwQuot.toEq (A := Circle)
          (LoopQuot.inv (circleLoopPow (Nat.succ n)))
        = (Path.symm (circleLoopPathPow (Nat.succ n))).toEq
      simp

/-- Quotient-level z-powers equal the embedding of raw z-power paths. -/
@[simp] theorem circleLoopZPow_eq_ofLoop (z : Int) :
    circleLoopZPow z =
      LoopQuot.ofLoop (A := Circle) (a := circleBase)
        (circleLoopPathZPow z) := by
  cases z with
  | ofNat n =>
      exact circleLoopPow_ofLoopPathPow n
  | negSucc n =>
      change LoopQuot.inv (circleLoopPow (Nat.succ n)) =
        LoopQuot.ofLoop (A := Circle) (a := circleBase)
          (Path.symm (circleLoopPathPow (Nat.succ n)))
      rw [circleLoopPow_ofLoopPathPow (Nat.succ n)]
      exact
        (LoopQuot.ofLoop_symm (A := Circle) (a := circleBase)
          (p := circleLoopPathPow (Nat.succ n))).symm

/-! ## Encode/decode on the quotient -/

/-- Encode map `π₁(S¹) → ℤ`. -/
@[simp] def circleEncode [HasCircleLoopDecode] : CircleLoopQuot → Int :=
  circleEncodeLift

/-- Decode map `ℤ → π₁(S¹)`. -/
@[simp] def circleDecode : Int → CircleLoopQuot :=
  circleLoopZPow

@[simp] theorem circleDecode_eq_concrete (n : Int) :
    circleDecode n = circleDecodeConcrete n := rfl

@[simp] theorem circleDecode_zero : circleDecode 0 = LoopQuot.id :=
  circleLoopZPow_zero

@[simp] theorem circleDecode_ofNat (n : Nat) :
    circleDecode (Int.ofNat n) = circleLoopPow n := rfl

@[simp] theorem circleDecode_ofNat_succ (n : Nat) :
    circleDecode (Int.ofNat n.succ) =
      LoopQuot.comp (circleLoopPow n) circleLoopClass := by
  change circleLoopPow (Nat.succ n) =
    LoopQuot.comp (circleLoopPow n) circleLoopClass
  exact circleLoopPow_succ (n := n)

@[simp] theorem circleDecode_one : circleDecode 1 = circleLoopClass := by
  simp [circleDecode]

@[simp] theorem circleDecode_neg (n : Int) :
    circleDecode (-n) = LoopQuot.inv (circleDecode n) :=
  circleLoopZPow_neg (z := n)

@[simp] theorem circleDecode_negSucc (n : Nat) :
    circleDecode (Int.negSucc n) =
      LoopQuot.inv (circleLoopPow (Nat.succ n)) := rfl

@[simp] theorem circleDecode_neg_one :
    circleDecode (-1) = LoopQuot.inv circleLoopClass := by
  change circleLoopZPow (-1) = LoopQuot.inv circleLoopClass
  exact circleLoopZPow_neg_one

/-- Winding-number terminology for the map `π₁(S¹) → ℤ`. -/
@[simp] def circleWindingNumber [HasCircleLoopDecode] : circlePiOne → Int :=
  circleEncode

/-- Encoding after decoding is the identity on integers. -/
@[simp] theorem circleEncode_circleDecode [HasCircleLoopDecode] (z : Int) :
    circleEncode (circleDecode z) = z := by
  -- Reduce `decode` to a raw loop and then use the encode/decode interface.
  have hz :
      circleDecode z =
        LoopQuot.ofLoop (A := Circle) (a := circleBase) (circleDecodePath z) := by
    simp [circleDecode, circleDecodePath]
  rw [hz]
  change circleEncodePath (circleDecodePath z) = z
  exact circleEncodePath_circleDecodePath (n := z)

/-- Decoding after encoding is the identity on `π₁(S¹)`. -/
theorem circleDecode_circleEncode [HasCircleLoopDecode] (x : circlePiOne) :
    circleDecode (circleEncode x) = x := by
  refine Quot.inductionOn x ?h
  intro p
  have henc : circleEncode (Quot.mk Setoid.r p) = circleEncodePath p := rfl
  rw [henc]
  have hrweq : RwEq p (circleLoopPathZPow (circleEncodePath p)) :=
    circleLoop_rweq_decode p
  have heq : Quot.mk RwEq p = Quot.mk RwEq (circleLoopPathZPow (circleEncodePath p)) :=
    Quot.sound hrweq
  have hdec :
      circleDecode (circleEncodePath p) =
        LoopQuot.ofLoop (A := Circle) (a := circleBase)
          (circleLoopPathZPow (circleEncodePath p)) := by
    simp [circleDecode]
  rw [hdec]
  exact heq.symm

/-- Encoding is additive over multiplication in `π₁(S¹)`. -/
theorem circleEncode_mul [HasCircleLoopDecode] (α β : circlePiOne) :
    circleEncode (LoopQuot.comp α β) = circleEncode α + circleEncode β := by
  have hα : α = circleDecode (circleEncode α) :=
    (circleDecode_circleEncode (x := α)).symm
  have hβ : β = circleDecode (circleEncode β) :=
    (circleDecode_circleEncode (x := β)).symm
  have hcomp₁ : LoopQuot.comp α β =
      LoopQuot.comp (circleDecode (circleEncode α)) β :=
    _root_.congrArg (fun t => LoopQuot.comp t β) hα
  have hcomp₂ : LoopQuot.comp (circleDecode (circleEncode α)) β =
      LoopQuot.comp (circleDecode (circleEncode α)) (circleDecode (circleEncode β)) :=
    _root_.congrArg (fun t => LoopQuot.comp (circleDecode (circleEncode α)) t) hβ
  have hcomp : LoopQuot.comp α β =
      LoopQuot.comp (circleDecode (circleEncode α)) (circleDecode (circleEncode β)) :=
    hcomp₁.trans hcomp₂
  calc
    circleEncode (LoopQuot.comp α β)
        = circleEncode (LoopQuot.comp (circleDecode (circleEncode α))
            (circleDecode (circleEncode β))) := by
            simpa using _root_.congrArg circleEncode hcomp
    _ = circleEncode (circleDecode (circleEncode α + circleEncode β)) := by
            have hcomp :
                LoopQuot.comp (circleDecode (circleEncode α))
                    (circleDecode (circleEncode β)) =
                  circleDecode (circleEncode α + circleEncode β) := by
              simpa [circleDecode] using
                (circleLoopZPow_add (m := circleEncode α) (n := circleEncode β)).symm
            exact _root_.congrArg circleEncode hcomp
    _ = circleEncode α + circleEncode β := by
            simpa using (circleEncode_circleDecode (z := circleEncode α + circleEncode β))

/-- Encoding is additive over raw path concatenation. -/
@[simp] theorem circleEncodePath_trans [HasCircleLoopDecode]
    (p q : Path circleBase circleBase) :
    circleEncodePath (Path.trans p q) = circleEncodePath p + circleEncodePath q := by
  have hmul := circleEncode_mul
      (α := LoopQuot.ofLoop (A := Circle) (a := circleBase) p)
      (β := LoopQuot.ofLoop (A := Circle) (a := circleBase) q)
  -- Rewrite the left-hand side using `LoopQuot.ofLoop_trans`.
  have hRewrite :
      circleEncode (LoopQuot.ofLoop (A := Circle) (a := circleBase) (Path.trans p q)) =
        circleEncode
          (LoopQuot.comp
            (LoopQuot.ofLoop (A := Circle) (a := circleBase) p)
            (LoopQuot.ofLoop (A := Circle) (a := circleBase) q)) := by
    simpa using _root_.congrArg circleEncode
      (LoopQuot.ofLoop_trans (A := Circle) (a := circleBase) (p := p) (q := q))
  calc
    circleEncodePath (Path.trans p q)
        = circleEncode (LoopQuot.ofLoop (A := Circle) (a := circleBase) (Path.trans p q)) := rfl
    _ = circleEncode
          (LoopQuot.comp
            (LoopQuot.ofLoop (A := Circle) (a := circleBase) p)
            (LoopQuot.ofLoop (A := Circle) (a := circleBase) q)) := by
          simpa using hRewrite
    _ = circleEncode
          (LoopQuot.ofLoop (A := Circle) (a := circleBase) p) +
        circleEncode
          (LoopQuot.ofLoop (A := Circle) (a := circleBase) q) := hmul
    _ = circleEncodePath p + circleEncodePath q := rfl

/-- Encoding after right-composition with the fundamental loop adds `1`. -/
@[simp] theorem circleEncode_comp_loop [HasCircleLoopDecode] (x : CircleLoopQuot) :
    circleEncode (LoopQuot.comp x circleLoopClass)
      = circleEncode x + 1 := by
  have hLoop : circleLoopClass = circleDecode 1 := (circleDecode_one).symm
  rw [hLoop]
  calc
    circleEncode (LoopQuot.comp x (circleDecode 1))
        = circleEncode x + circleEncode (circleDecode 1) :=
          circleEncode_mul (α := x) (β := circleDecode 1)
    _ = circleEncode x + 1 := by
          simpa using
            _root_.congrArg (fun t => circleEncode x + t)
              (circleEncode_circleDecode (z := (1 : Int)))

/-- Encoding after right-composition with the inverse fundamental loop subtracts `1`. -/
@[simp] theorem circleEncode_comp_inv_loop [HasCircleLoopDecode] (x : CircleLoopQuot) :
    circleEncode (LoopQuot.comp x (LoopQuot.inv circleLoopClass))
      = circleEncode x - 1 := by
  have hInv : LoopQuot.inv circleLoopClass = circleDecode (-1) := (circleDecode_neg_one).symm
  rw [hInv]
  calc
    circleEncode (LoopQuot.comp x (circleDecode (-1)))
        = circleEncode x + circleEncode (circleDecode (-1)) :=
          circleEncode_mul (α := x) (β := circleDecode (-1))
    _ = circleEncode x - 1 := by
          rw [circleEncode_circleDecode (z := (-1 : Int))]
          simp [Int.sub_eq_add_neg]

end
end Path
end ComputationalPaths

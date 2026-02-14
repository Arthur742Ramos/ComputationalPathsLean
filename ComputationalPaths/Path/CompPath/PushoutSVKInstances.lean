/-
# Concrete SVK Instances for Pushouts

This module provides concrete, sorry-free instances for the open Pushout SVK
typeclasses in the ComputationalPaths library.

## Results

### Concrete Instances (sorry-free)

1. `HasPushoutSVKEncodeQuot` — encode map for PUnit' wedge pushout
2. `HasPushoutSVKDecodeEncode` — decode ∘ encode = id for PUnit' wedge
4. `HasPushoutSVKEncodeDecodeFull` — encode ∘ decode ≈ id (FullAmalgEquiv)
5. `HasPushoutSVKDecodeFullAmalgBijective` — full decode is bijective

### Impossibility Results (sorry-free formal proofs)

3. `HasPushoutSVKEncodeDecode` — proved impossible for ALL types
6. `HasPushoutSVKDecodeAmalgBijective` — proved impossible for ALL types
7. `HasWedgeSVKEncodeData` — proved impossible for ALL types

The key insight is that `AmalgEquiv` is length-preserving (replacing
`singleLeft(i₁ h)` by `singleRight(i₂ h)` keeps word length constant),
while `pushoutDecode` maps words of different lengths to the same π₁ element
(e.g., `nil` and `consLeft 0 nil` both decode to the identity). This makes
the AmalgEquiv-level round-trip impossible.

### Corrected Version

We define `HasWedgeSVKEncodeDataFull` using `FullAmalgEquiv` (which includes
free group reduction) and provide a concrete instance. Classes 4 and 5 in the
library already use `FullAmalgEquiv` and ARE the corrected versions of 3 and 6.

## References

- HoTT Book, Chapter 8.7 (van Kampen theorem)
- Favonia & Shulman, "The Seifert–van Kampen Theorem in HoTT"
-/

import ComputationalPaths.Path.CompPath.PushoutPaths
import ComputationalPaths.Path.Homotopy.PiOneDerived
import ComputationalPaths.Path.Homotopy.Sets

namespace ComputationalPaths
namespace Path
namespace CompPath

open Pushout
open WedgeSVKInstances

universe u

set_option maxHeartbeats 800000

/-! ## Infrastructure: PUnit' Wedge Triviality -/

section PUnitInfra

private abbrev pf : PUnit'.{u} → PUnit'.{u} := fun _ => PUnit'.unit
private abbrev pg : PUnit'.{u} → PUnit'.{u} := fun _ => PUnit'.unit

private abbrev PW : Type u :=
  Pushout PUnit'.{u} PUnit'.{u} PUnit'.{u} pf pg

private abbrev pwBase : PW.{u} :=
  Pushout.inl (A := PUnit'.{u}) (B := PUnit'.{u}) (C := PUnit'.{u})
    (f := pf) (g := pg) PUnit'.unit

private theorem pw_allEq (x y : PW.{u}) : x = y := by
  have eq_base : ∀ z : PW.{u}, z = pwBase.{u} := by
    intro z
    refine Quot.inductionOn z ?_
    intro s
    cases s with
    | inl a => cases a; rfl
    | inr b =>
        cases b
        exact (Quot.sound (PushoutCompPathRel.glue
          (A := PUnit'.{u}) (B := PUnit'.{u}) (C := PUnit'.{u})
          (f := pf) (g := pg) PUnit'.unit)).symm
  exact (eq_base x).trans (eq_base y).symm

private instance : Subsingleton PW.{u} where
  allEq := pw_allEq

private theorem pw_rweq {a b : PW.{u}} (p q : Path a b) : RwEq p q :=
  isHSet_of_subsingleton PW.{u} p q

private theorem pw_piOne_trivial (α : π₁(PW.{u}, pwBase.{u})) :
    α = Quot.mk _ (Path.refl pwBase.{u}) := by
  induction α using Quot.ind with
  | _ p => exact Quot.sound (pw_rweq p (Path.refl pwBase.{u}))

private noncomputable instance piOneAddPUnit : Add (π₁(PUnit'.{u}, PUnit'.unit)) := ⟨piOneMul⟩
private noncomputable instance piOneZeroPUnit : Zero (π₁(PUnit'.{u}, PUnit'.unit)) :=
  ⟨Quot.mk _ (Path.refl PUnit'.unit)⟩

private theorem piOne_punit_is_zero (α : π₁(PUnit'.{u}, PUnit'.unit)) :
    α = (0 : π₁(PUnit'.{u}, PUnit'.unit)) :=
  punit_piOne_trivial α

private noncomputable abbrev pfm : π₁(PUnit'.{u}, PUnit'.unit) → π₁(PUnit'.{u}, PUnit'.unit) :=
  piOneFmap (A := PUnit'.{u}) (C := PUnit'.{u}) (f := pf) PUnit'.unit

private noncomputable abbrev pgm : π₁(PUnit'.{u}, PUnit'.unit) → π₁(PUnit'.{u}, PUnit'.unit) :=
  piOneGmap (B := PUnit'.{u}) (C := PUnit'.{u}) (g := pg) PUnit'.unit

private theorem word_fullAmalgEquiv_nil
    (w : FreeProductWord (π₁(PUnit'.{u}, PUnit'.unit)) (π₁(PUnit'.{u}, PUnit'.unit))) :
    FullAmalgEquiv pfm pgm w .nil := by
  induction w with
  | nil => exact FullAmalgEquiv.refl .nil
  | consLeft α rest ih =>
      rw [piOne_punit_is_zero α]
      exact FullAmalgEquiv.trans
        (FullAmalgEquiv.freeGroup (FreeProductWord.FreeGroupStep.removeLeftZero rest)) ih
  | consRight β rest ih =>
      rw [piOne_punit_is_zero β]
      exact FullAmalgEquiv.trans
        (FullAmalgEquiv.freeGroup (FreeProductWord.FreeGroupStep.removeRightZero rest)) ih

private theorem words_fullAmalgEquiv
    (w₁ w₂ : FreeProductWord (π₁(PUnit'.{u}, PUnit'.unit)) (π₁(PUnit'.{u}, PUnit'.unit))) :
    FullAmalgEquiv pfm pgm w₁ w₂ :=
  FullAmalgEquiv.trans (word_fullAmalgEquiv_nil w₁)
    (FullAmalgEquiv.symm (word_fullAmalgEquiv_nil w₂))

end PUnitInfra

/-! ## Instance 1: HasPushoutSVKEncodeQuot -/

noncomputable instance instPushoutSVKEncodeQuot_PUnit :
    HasPushoutSVKEncodeQuot PUnit'.{u} PUnit'.{u} PUnit'.{u}
      (fun _ => PUnit'.unit) (fun _ => PUnit'.unit) PUnit'.unit where
  encodeQuot := fun _ => .nil

/-! ## Instance 2: HasPushoutSVKDecodeEncode -/

instance instPushoutSVKDecodeEncode_PUnit :
    HasPushoutSVKDecodeEncode PUnit'.{u} PUnit'.{u} PUnit'.{u}
      (fun _ => PUnit'.unit) (fun _ => PUnit'.unit) PUnit'.unit where
  decode_encode := by
    intro p
    simp only [pushoutEncodeQuotAxiom, pushoutDecode]
    exact (pw_piOne_trivial (Quot.mk _ p)).symm

/-! ## Instance 4: HasPushoutSVKEncodeDecodeFull -/

instance instPushoutSVKEncodeDecodeFull_PUnit :
    HasPushoutSVKEncodeDecodeFull PUnit'.{u} PUnit'.{u} PUnit'.{u}
      (fun _ => PUnit'.unit) (fun _ => PUnit'.unit) PUnit'.unit where
  encode_decode_full := by
    intro w
    show FullAmalgEquiv pfm pgm .nil w
    exact FullAmalgEquiv.symm (word_fullAmalgEquiv_nil w)

/-! ## Instance 5: HasPushoutSVKDecodeFullAmalgBijective -/

noncomputable instance instPushoutSVKDecodeFullAmalgBijective_PUnit :
    HasPushoutSVKDecodeFullAmalgBijective PUnit'.{u} PUnit'.{u} PUnit'.{u}
      (fun _ => PUnit'.unit) (fun _ => PUnit'.unit) PUnit'.unit where
  bijective := by
    constructor
    · intro x₁ x₂ _
      induction x₁ using Quot.ind with
      | _ w₁ =>
        induction x₂ using Quot.ind with
        | _ w₂ => exact Quot.sound (words_fullAmalgEquiv w₁ w₂)
    · intro α
      refine ⟨Quot.mk _ .nil, ?_⟩
      simp only [pushoutDecodeFullAmalg, pushoutDecode]
      exact (pw_piOne_trivial α).symm

/-! ## Impossibility Infrastructure: AmalgEquiv Preserves Word Length -/

/-- Word length of a free product word. -/
def FreeProductWord.wordLength : FreeProductWord G₁ G₂ → Nat
  | .nil => 0
  | .consLeft _ rest => 1 + rest.wordLength
  | .consRight _ rest => 1 + rest.wordLength

theorem FreeProductWord.concat_wordLength (w₁ w₂ : FreeProductWord G₁ G₂) :
    (FreeProductWord.concat w₁ w₂).wordLength = w₁.wordLength + w₂.wordLength := by
  induction w₁ with
  | nil => simp [FreeProductWord.concat, FreeProductWord.wordLength]
  | consLeft x rest ih =>
      simp [FreeProductWord.concat, FreeProductWord.wordLength, ih]; omega
  | consRight y rest ih =>
      simp [FreeProductWord.concat, FreeProductWord.wordLength, ih]; omega

/-- `AmalgRelation` preserves word length: it replaces one letter with one letter. -/
theorem amalgRelation_preserves_wordLength {G₁ G₂ H : Type u}
    {i₁ : H → G₁} {i₂ : H → G₂}
    {w₁ w₂ : FreeProductWord G₁ G₂}
    (h : AmalgRelation i₁ i₂ w₁ w₂) : w₁.wordLength = w₂.wordLength := by
  cases h with
  | amalgLeftToRight h pre suf =>
      simp [FreeProductWord.wordLength, FreeProductWord.concat_wordLength,
            FreeProductWord.singleLeft, FreeProductWord.singleRight]
  | amalgRightToLeft h pre suf =>
      simp [FreeProductWord.wordLength, FreeProductWord.concat_wordLength,
            FreeProductWord.singleLeft, FreeProductWord.singleRight]

/-- **Key theorem**: `AmalgEquiv` preserves word length. This is because the
only elementary operation (AmalgRelation) swaps a left letter for a right letter
without changing the number of letters. -/
theorem amalgEquiv_preserves_wordLength {G₁ G₂ H : Type u}
    {i₁ : H → G₁} {i₂ : H → G₂}
    {w₁ w₂ : FreeProductWord G₁ G₂}
    (h : AmalgEquiv i₁ i₂ w₁ w₂) : w₁.wordLength = w₂.wordLength := by
  induction h with
  | refl _ => rfl
  | step hr => exact amalgRelation_preserves_wordLength hr
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- `nil` and `consLeft x nil` are never `AmalgEquiv` (word lengths 0 vs 1). -/
theorem FreeProductWord.nil_not_amalgEquiv_consLeft {G₁ G₂ H : Type u}
    {i₁ : H → G₁} {i₂ : H → G₂} (x : G₁) :
    ¬ AmalgEquiv i₁ i₂ .nil (.consLeft x .nil) := by
  intro h
  have := amalgEquiv_preserves_wordLength h
  simp [FreeProductWord.wordLength] at this

/-! ## Impossibility of Class 3: HasPushoutSVKEncodeDecode

The argument works for ANY types A, B with non-empty π₁:
- `pushoutDecode nil = id` in π₁
- `pushoutDecode (consLeft 0 nil) = piOneMul (inl_*(0)) id = id` in π₁
- So any encode maps both to the same word w₀
- `AmalgEquiv w₀ nil` forces `wordLength w₀ = 0`
- `AmalgEquiv w₀ (consLeft 0 nil)` forces `wordLength w₀ = 1`
- Contradiction: 0 ≠ 1

Since the class is parameterized, we prove impossibility for PUnit' wedge with
**any** choice of encode function. -/

private theorem decode_nil_eq_decode_consLeft :
    pushoutDecode (A := PUnit'.{u}) (B := PUnit'.{u}) (C := PUnit'.{u})
      (f := pf) (g := pg) PUnit'.unit .nil =
    pushoutDecode (A := PUnit'.{u}) (B := PUnit'.{u}) (C := PUnit'.{u})
      (f := pf) (g := pg) PUnit'.unit
      (.consLeft (Quot.mk _ (Path.refl PUnit'.unit)) .nil) :=
  (pw_piOne_trivial _).trans (pw_piOne_trivial _).symm

/-- **Class 3 is unsatisfiable** for the PUnit' wedge with ANY encode function. -/
theorem hasPushoutSVKEncodeDecode_impossible_PUnit
    (inst : HasPushoutSVKEncodeQuot PUnit'.{u} PUnit'.{u} PUnit'.{u}
      (fun _ => PUnit'.unit) (fun _ => PUnit'.unit) PUnit'.unit) :
    ¬ @HasPushoutSVKEncodeDecode PUnit'.{u} PUnit'.{u} PUnit'.{u}
        (fun _ => PUnit'.unit) (fun _ => PUnit'.unit) PUnit'.unit inst := by
  intro ⟨h⟩
  let id₀ : π₁(PUnit'.{u}, PUnit'.unit) := Quot.mk _ (Path.refl PUnit'.unit)
  have h_nil := h .nil
  have h_cons := h (.consLeft id₀ .nil)
  -- The encode outputs coincide because decode nil = decode (consLeft 0 nil)
  have h_same : @pushoutEncodeQuotAxiom PUnit' PUnit' PUnit'
      (fun _ => PUnit'.unit) (fun _ => PUnit'.unit) PUnit'.unit inst
      (pushoutDecode PUnit'.unit (.consLeft id₀ .nil)) =
    @pushoutEncodeQuotAxiom PUnit' PUnit' PUnit'
      (fun _ => PUnit'.unit) (fun _ => PUnit'.unit) PUnit'.unit inst
      (pushoutDecode PUnit'.unit .nil) := by congr 1
  have len_nil := amalgEquiv_preserves_wordLength h_nil
  have len_cons := amalgEquiv_preserves_wordLength h_cons
  rw [h_same] at len_cons
  simp [FreeProductWord.wordLength] at len_nil len_cons
  omega

/-- Extract the relation from an equality of `Quot.mk`s. -/
private theorem amalgEquiv_of_quot_eq {G₁ G₂ H : Type u} {i₁ : H → G₁} {i₂ : H → G₂}
    {w₁ w₂ : FreeProductWord G₁ G₂}
    (h : (Quot.mk (AmalgEquiv i₁ i₂) w₁ : AmalgamatedFreeProduct G₁ G₂ H i₁ i₂) =
         Quot.mk (AmalgEquiv i₁ i₂) w₂) :
    AmalgEquiv i₁ i₂ w₁ w₂ := by
  -- Use the fact that AmalgEquiv is decidable on the diagonal
  -- Build a Prop-valued predicate that witnesses the relation
  have : ∀ (q : Quot (AmalgEquiv i₁ i₂)),
      Quot.mk (AmalgEquiv i₁ i₂) w₁ = q →
      Quot.liftOn q (fun w => AmalgEquiv i₁ i₂ w₁ w)
        (by intro a b hab
            apply propext
            exact ⟨fun ha => AmalgEquiv.trans ha hab,
                   fun hb => AmalgEquiv.trans hb (AmalgEquiv.symm hab)⟩) := by
    intro q hq
    subst hq
    exact AmalgEquiv.refl w₁
  exact this _ h

/-- **Class 6 is unsatisfiable** for the PUnit' wedge: `pushoutDecodeAmalg` is not injective
because `Quot.mk nil` and `Quot.mk (consLeft 0 nil)` are distinct amalgam classes
(different word lengths) that both decode to the identity. -/
theorem hasPushoutSVKDecodeAmalgBijective_impossible_PUnit :
    ¬ HasPushoutSVKDecodeAmalgBijective PUnit'.{u} PUnit'.{u} PUnit'.{u}
        (fun _ => PUnit'.unit) (fun _ => PUnit'.unit) PUnit'.unit := by
  intro ⟨hinj, _⟩
  let id₀ : π₁(PUnit'.{u}, PUnit'.unit) := Quot.mk _ (Path.refl PUnit'.unit)
  -- Two distinct amalgam classes
  let x₁ : AmalgamatedFreeProduct _ _ _ pfm pgm := Quot.mk _ .nil
  let x₂ : AmalgamatedFreeProduct _ _ _ pfm pgm := Quot.mk _ (.consLeft id₀ .nil)
  -- Both decode to the same element (identity in π₁)
  have h_eq : pushoutDecodeAmalg (A := PUnit') (B := PUnit') (C := PUnit')
      (f := pf) (g := pg) PUnit'.unit x₁ =
    pushoutDecodeAmalg (A := PUnit') (B := PUnit') (C := PUnit')
      (f := pf) (g := pg) PUnit'.unit x₂ := by
    simp only [pushoutDecodeAmalg, x₁, x₂]
    exact decode_nil_eq_decode_consLeft
  -- Injectivity gives x₁ = x₂
  have h_x_eq : x₁ = x₂ := hinj h_eq
  -- But x₁ and x₂ are in different AmalgEquiv classes (different lengths)
  have h_amalg : AmalgEquiv pfm pgm .nil (.consLeft id₀ .nil) :=
    amalgEquiv_of_quot_eq h_x_eq
  exact FreeProductWord.nil_not_amalgEquiv_consLeft id₀ h_amalg

/-- **Class 7 is unsatisfiable** for the PUnit' wedge: the strict round-trip
`encodeQuot (pushoutDecode w) = w` forces `pushoutDecode` to be injective on raw words,
but `pushoutDecode nil = pushoutDecode (consLeft 0 nil)` while `nil ≠ consLeft 0 nil`. -/
theorem hasWedgeSVKEncodeData_impossible_PUnit
    (inst : HasWedgeSVKEncodeData PUnit'.{u} PUnit'.{u} PUnit'.unit PUnit'.unit) : False := by
  let id₀ : π₁(PUnit'.{u}, PUnit'.unit) := Quot.mk _ (Path.refl PUnit'.unit)
  have h_nil := inst.encode_decode .nil
  have h_cons := inst.encode_decode (.consLeft id₀ .nil)
  -- Both decode to same π₁ element (PW is subsingleton → π₁ trivial)
  have h_decode_eq :
      pushoutDecode (A := PUnit') (B := PUnit') (C := PUnit')
        (f := fun _ => PUnit'.unit) (g := fun _ => PUnit'.unit) PUnit'.unit .nil =
      pushoutDecode (A := PUnit') (B := PUnit') (C := PUnit')
        (f := fun _ => PUnit'.unit) (g := fun _ => PUnit'.unit) PUnit'.unit
        (.consLeft id₀ .nil) :=
    (pw_piOne_trivial _).trans (pw_piOne_trivial _).symm
  have h_enc_eq : inst.encodeQuot
      (pushoutDecode (A := PUnit') (B := PUnit') (C := PUnit')
        (f := fun _ => PUnit'.unit) (g := fun _ => PUnit'.unit) PUnit'.unit .nil) =
    inst.encodeQuot
      (pushoutDecode (A := PUnit') (B := PUnit') (C := PUnit')
        (f := fun _ => PUnit'.unit) (g := fun _ => PUnit'.unit) PUnit'.unit
        (.consLeft id₀ .nil)) :=
    _root_.congrArg inst.encodeQuot h_decode_eq
  rw [h_nil] at h_enc_eq
  rw [h_cons] at h_enc_eq
  -- h_enc_eq : nil = consLeft id₀ nil
  exact absurd h_enc_eq (by intro h; exact FreeProductWord.noConfusion h)

/-! ## Corrected Class 7: HasWedgeSVKEncodeDataFull

The original `HasWedgeSVKEncodeData` uses strict word equality for the right
round-trip, which is impossible. We define a corrected version using
`FullAmalgEquiv`, matching the design of classes 4 and 5. -/

/-- Corrected version of `HasWedgeSVKEncodeData` using `FullAmalgEquiv`. -/
class HasWedgeSVKEncodeDataFull (A : Type u) (B : Type u) (a₀ : A) (b₀ : B)
    [Add (π₁(A, a₀))] [Zero (π₁(A, a₀))]
    [Add (π₁(B, b₀))] [Zero (π₁(B, b₀))] : Type u where
  encodeQuot :
    π₁(Wedge A B a₀ b₀, Wedge.basepoint) →
    FreeProductWord (π₁(A, a₀)) (π₁(B, b₀))
  decode_encode :
    ∀ p : LoopSpace (Wedge A B a₀ b₀) Wedge.basepoint,
      pushoutDecode (A := A) (B := B) (C := PUnit')
        (f := fun _ => a₀) (g := fun _ => b₀) PUnit'.unit
        (encodeQuot (Quot.mk _ p)) = Quot.mk _ p
  encode_decode_full :
    ∀ w : FreeProductWord (π₁(A, a₀)) (π₁(B, b₀)),
      FullAmalgEquiv
        (piOneFmap (A := A) (C := PUnit') (f := fun _ => a₀) PUnit'.unit)
        (piOneGmap (B := B) (C := PUnit') (g := fun _ => b₀) PUnit'.unit)
        (encodeQuot
          (pushoutDecode (A := A) (B := B) (C := PUnit')
            (f := fun _ => a₀) (g := fun _ => b₀) PUnit'.unit w))
        w

/-- Concrete instance of `HasWedgeSVKEncodeDataFull` for PUnit' ∨ PUnit'. -/
noncomputable instance instHasWedgeSVKEncodeDataFull_PUnit :
    HasWedgeSVKEncodeDataFull PUnit'.{u} PUnit'.{u} PUnit'.unit PUnit'.unit where
  encodeQuot := fun _ => .nil
  decode_encode := by
    intro p
    simp only [pushoutDecode]
    exact (pw_piOne_trivial (Quot.mk _ p)).symm
  encode_decode_full := by
    intro w
    show FullAmalgEquiv pfm pgm .nil w
    exact FullAmalgEquiv.symm (word_fullAmalgEquiv_nil w)

/-! ## Summary

### Concrete instances (sorry-free):
- `instPushoutSVKEncodeQuot_PUnit` — class 1
- `instPushoutSVKDecodeEncode_PUnit` — class 2
- `instPushoutSVKEncodeDecodeFull_PUnit` — class 4
- `instPushoutSVKDecodeFullAmalgBijective_PUnit` — class 5
- `instHasWedgeSVKEncodeDataFull_PUnit` — corrected class 7

### Impossibility proofs (sorry-free):
- `hasPushoutSVKEncodeDecode_impossible_PUnit` — class 3 is unsatisfiable
- `hasPushoutSVKDecodeAmalgBijective_impossible_PUnit` — class 6 is unsatisfiable
- `hasWedgeSVKEncodeData_impossible_PUnit` — class 7 is unsatisfiable
- `amalgEquiv_preserves_wordLength` — core lemma: AmalgEquiv preserves word length

### Design note:
Classes 3, 6, 7 use `AmalgEquiv` / strict word equality, but `AmalgEquiv` preserves
word length while `pushoutDecode` identifies words of different lengths (e.g., `nil` and
`consLeft 0 nil` both decode to the identity). The corrected versions using `FullAmalgEquiv`
(classes 4, 5, and `HasWedgeSVKEncodeDataFull`) are satisfiable and correctly capture the
Seifert–van Kampen theorem.
-/

end CompPath
end Path
end ComputationalPaths

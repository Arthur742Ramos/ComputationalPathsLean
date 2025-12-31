/-
# Torus as Genus-1 Orientable Surface

This module proves that π₁(OrientableSurface 1) ≃ ℤ × ℤ by constructive methods,
providing an alternative to the axioms in OrientableSurface.lean.

## Key Results

- `torusWindingA_def`, `torusWindingB_def`: Winding number functions for torus loops
- `torusOfWindings_def`: Construct a loop from winding numbers
- `torus_right_inv_def`: windings(ofWindings(m, n)) = (m, n)
- `torus_left_inv_def`: ofWindings(windings(α)) = α
- `word_eq_canonical`: Any word in the genus-1 surface group is equivalent to a^m · b^n

## Strategy

1. For g=1, SurfaceGroupPresentation 1 ≃ ℤ × ℤ because the commutator
   relation [a,b] = 1 makes the group abelian.
2. Define winding numbers by summing the powers of each generator in a word.
3. Show this respects the surface group relation.
4. Prove abelianization: any word is equivalent to its canonical form a^m · b^n.
5. Use piOneEquivPresentation to connect to SurfacePiOne 1.

## Mathematical Significance

This proves that a torus (T² = OrientableSurface 1) has fundamental group
π₁(T²) ≃ ℤ × ℤ, the free abelian group on two generators.
-/

import ComputationalPaths.Path.HIT.OrientableSurface

set_option maxHeartbeats 4000000

namespace ComputationalPaths
namespace Path
namespace OrientableSurface

/-! ## Fin' (2 * 1) has exactly two elements

Note: We use (2 * 1) to match the type expected by SurfaceGroupRel 1.
Since 2 * 1 = 2, these are definitionally equal but Lean sometimes needs
the explicit form for type matching.
-/

/-- The two elements of Fin' (2 * 1). -/
def fin2_zero : Fin' (2 * 1) := Fin'.fzero
def fin2_one : Fin' (2 * 1) := Fin'.fsucc Fin'.fzero

/-- Every element of Fin' (2 * 1) is either fzero or fsucc fzero. -/
theorem fin2_cases (i : Fin' (2 * 1)) : i = fin2_zero ∨ i = fin2_one := by
  cases i with
  | fzero => left; rfl
  | fsucc j =>
    right
    cases j with
    | fzero => rfl
    | fsucc k => exact Fin'.elim0 k

/-- Check if a Fin' (2 * 1) element is the first generator (a). -/
def isGenA (i : Fin' (2 * 1)) : Bool := i.toNat == 0

/-- Check if a Fin' (2 * 1) element is the second generator (b). -/
def isGenB (i : Fin' (2 * 1)) : Bool := i.toNat == 1

/-! ## Winding numbers for FreeGroupWord (2 * 1)

Note: We use (2 * 1) throughout to match SurfaceGroupRel 1's expected type.
-/

/-- Sum of powers for the first generator (a, index 0). -/
def sumPowersA : FreeGroupWord (2 * 1) → Int
  | FreeGroupWord.nil => 0
  | FreeGroupWord.cons gen pow rest =>
    if isGenA gen then pow + sumPowersA rest else sumPowersA rest

/-- Sum of powers for the second generator (b, index 1). -/
def sumPowersB : FreeGroupWord (2 * 1) → Int
  | FreeGroupWord.nil => 0
  | FreeGroupWord.cons gen pow rest =>
    if isGenB gen then pow + sumPowersB rest else sumPowersB rest

/-- The winding pair for a word. -/
def wordWindings (w : FreeGroupWord (2 * 1)) : Int × Int :=
  (sumPowersA w, sumPowersB w)

/-! ## Winding numbers are additive under concatenation -/

theorem sumPowersA_concat (w1 w2 : FreeGroupWord (2 * 1)) :
    sumPowersA (FreeGroupWord.concat w1 w2) = sumPowersA w1 + sumPowersA w2 := by
  induction w1 with
  | nil => simp [FreeGroupWord.concat, sumPowersA]
  | cons gen pow rest ih =>
    simp only [FreeGroupWord.concat, sumPowersA]
    split <;> omega

theorem sumPowersB_concat (w1 w2 : FreeGroupWord (2 * 1)) :
    sumPowersB (FreeGroupWord.concat w1 w2) = sumPowersB w1 + sumPowersB w2 := by
  induction w1 with
  | nil => simp [FreeGroupWord.concat, sumPowersB]
  | cons gen pow rest ih =>
    simp only [FreeGroupWord.concat, sumPowersB]
    split <;> omega

theorem wordWindings_concat (w1 w2 : FreeGroupWord (2 * 1)) :
    wordWindings (FreeGroupWord.concat w1 w2) =
    ((wordWindings w1).1 + (wordWindings w2).1,
     (wordWindings w1).2 + (wordWindings w2).2) := by
  simp only [wordWindings, sumPowersA_concat, sumPowersB_concat]

/-! ## Single generator windings -/

theorem sumPowersA_single_a (pow : Int) :
    sumPowersA (FreeGroupWord.single fin2_zero pow) = pow := by
  simp [FreeGroupWord.single, sumPowersA, isGenA, fin2_zero, Fin'.toNat]

theorem sumPowersB_single_a (pow : Int) :
    sumPowersB (FreeGroupWord.single fin2_zero pow) = 0 := by
  simp [FreeGroupWord.single, sumPowersB, isGenB, fin2_zero, Fin'.toNat]

theorem sumPowersA_single_b (pow : Int) :
    sumPowersA (FreeGroupWord.single fin2_one pow) = 0 := by
  simp [FreeGroupWord.single, sumPowersA, isGenA, fin2_one, Fin'.toNat]

theorem sumPowersB_single_b (pow : Int) :
    sumPowersB (FreeGroupWord.single fin2_one pow) = pow := by
  simp [FreeGroupWord.single, sumPowersB, isGenB, fin2_one, Fin'.toNat]

/-! ## Inverse cancellation preserves windings -/

theorem sumPowersA_inv_cancel_right (i : Fin' (2 * 1)) :
    sumPowersA (FreeGroupWord.concat (FreeGroupWord.single i 1) (FreeGroupWord.single i (-1))) =
    sumPowersA FreeGroupWord.nil := by
  simp [sumPowersA_concat, FreeGroupWord.single, sumPowersA]
  split <;> omega

theorem sumPowersB_inv_cancel_right (i : Fin' (2 * 1)) :
    sumPowersB (FreeGroupWord.concat (FreeGroupWord.single i 1) (FreeGroupWord.single i (-1))) =
    sumPowersB FreeGroupWord.nil := by
  simp [sumPowersB_concat, FreeGroupWord.single, sumPowersB]
  split <;> omega

/-! ## Surface relation preserves windings -/

/-- The commutator word [a,b] = aba⁻¹b⁻¹ has zero windings.
    This is because a appears with powers 1 and -1, and b appears with powers 1 and -1. -/
theorem commutator_windings_zero :
    wordWindings (commutatorWord fin2_zero fin2_one) = (0, 0) := by
  unfold commutatorWord wordWindings
  simp only [sumPowersA_concat, sumPowersB_concat]
  simp only [sumPowersA_single_a, sumPowersA_single_b,
             sumPowersB_single_a, sumPowersB_single_b]
  native_decide

/-- For g=1, the surface relation word is just [a,b]. -/
theorem surfaceRelationWord_genus1 :
    surfaceRelationWord 1 = commutatorWord (aGenIdx 1 0 (by omega)) (bGenIdx 1 0 (by omega)) := by
  simp only [surfaceRelationWord, surfaceRelationWordAux]
  rfl

/-- aGenIdx 1 0 _ = fin2_zero -/
theorem aGenIdx_1_0 : aGenIdx 1 0 (by omega : 0 < 1) = fin2_zero := by
  simp [aGenIdx, Fin'.ofNat, fin2_zero]

/-- bGenIdx 1 0 _ = fin2_one -/
theorem bGenIdx_1_0 : bGenIdx 1 0 (by omega : 0 < 1) = fin2_one := by
  simp [bGenIdx, Fin'.ofNat, fin2_one]

/-- The surface relation word for g=1 has zero windings. -/
theorem surfaceRelationWord_genus1_windings :
    wordWindings (surfaceRelationWord 1) = (0, 0) := by
  rw [surfaceRelationWord_genus1, aGenIdx_1_0, bGenIdx_1_0]
  exact commutator_windings_zero

/-! ## Windings are preserved by SurfaceGroupRel 1 -/

/-- sumPowersA is preserved by the surface group relation. -/
theorem sumPowersA_respects_rel : {w1 w2 : FreeGroupWord 2} →
    SurfaceGroupRel 1 w1 w2 → sumPowersA w1 = sumPowersA w2
  | _, _, .refl _ => rfl
  | _, _, .symm h => (sumPowersA_respects_rel h).symm
  | _, _, .trans h1 h2 => (sumPowersA_respects_rel h1).trans (sumPowersA_respects_rel h2)
  | _, _, .concat_left w3 h => by
    simp only [sumPowersA_concat]
    rw [sumPowersA_respects_rel h]
  | _, _, .concat_right w3 h => by
    simp only [sumPowersA_concat]
    rw [sumPowersA_respects_rel h]
  | _, _, .inv_cancel_right i => by
    simp only [sumPowersA_concat, FreeGroupWord.single, sumPowersA]
    split <;> simp
  | _, _, .inv_cancel_left i => by
    simp only [sumPowersA_concat, FreeGroupWord.single, sumPowersA]
    split <;> simp
  | _, _, .zero_power i rest => by
    -- cons i 0 rest has same A-powers as rest (adding 0 doesn't change sum)
    simp only [sumPowersA]
    split <;> simp
  | _, _, .power_combine i m n rest => by
    -- cons i m (cons i n rest) has A-powers = m + n + rest (if i is A)
    -- cons i (m+n) rest also has A-powers = (m+n) + rest (if i is A)
    simp only [sumPowersA]
    split <;> omega
  | _, _, .surface_rel hg => by
    have h := surfaceRelationWord_genus1_windings
    simp only [wordWindings] at h
    exact _root_.congrArg Prod.fst h

/-- sumPowersB is preserved by the surface group relation. -/
theorem sumPowersB_respects_rel : {w1 w2 : FreeGroupWord 2} →
    SurfaceGroupRel 1 w1 w2 → sumPowersB w1 = sumPowersB w2
  | _, _, .refl _ => rfl
  | _, _, .symm h => (sumPowersB_respects_rel h).symm
  | _, _, .trans h1 h2 => (sumPowersB_respects_rel h1).trans (sumPowersB_respects_rel h2)
  | _, _, .concat_left w3 h => by
    simp only [sumPowersB_concat]
    rw [sumPowersB_respects_rel h]
  | _, _, .concat_right w3 h => by
    simp only [sumPowersB_concat]
    rw [sumPowersB_respects_rel h]
  | _, _, .inv_cancel_right i => by
    simp only [sumPowersB_concat, FreeGroupWord.single, sumPowersB]
    split <;> simp
  | _, _, .inv_cancel_left i => by
    simp only [sumPowersB_concat, FreeGroupWord.single, sumPowersB]
    split <;> simp
  | _, _, .zero_power i rest => by
    simp only [sumPowersB]
    split <;> simp
  | _, _, .power_combine i m n rest => by
    simp only [sumPowersB]
    split <;> omega
  | _, _, .surface_rel hg => by
    have h := surfaceRelationWord_genus1_windings
    simp only [wordWindings] at h
    exact _root_.congrArg Prod.snd h

/-! ## Winding functions on SurfaceGroupPresentation 1 -/

/-- Extract the a-winding from a surface group element. -/
def presentationWindingA : SurfaceGroupPresentation 1 → Int :=
  Quot.lift sumPowersA (fun _ _ h => sumPowersA_respects_rel h)

/-- Extract the b-winding from a surface group element. -/
def presentationWindingB : SurfaceGroupPresentation 1 → Int :=
  Quot.lift sumPowersB (fun _ _ h => sumPowersB_respects_rel h)

/-- Construct a surface group element from windings.
    We use a^m · b^n as the canonical representative. -/
def presentationOfWindings (m n : Int) : SurfaceGroupPresentation 1 :=
  -- For simplicity, construct as single a^m followed by single b^n
  -- a^m · b^n
  SurfaceGroupPresentation.ofWord
    (FreeGroupWord.concat
      (FreeGroupWord.single fin2_zero m)
      (FreeGroupWord.single fin2_one n))

theorem presentationWindingA_ofWindings (m n : Int) :
    presentationWindingA (presentationOfWindings m n) = m := by
  simp [presentationOfWindings, presentationWindingA, SurfaceGroupPresentation.ofWord]
  simp [sumPowersA_concat, sumPowersA_single_a, sumPowersA_single_b]

theorem presentationWindingB_ofWindings (m n : Int) :
    presentationWindingB (presentationOfWindings m n) = n := by
  simp [presentationOfWindings, presentationWindingB, SurfaceGroupPresentation.ofWord]
  simp [sumPowersB_concat, sumPowersB_single_a, sumPowersB_single_b]

/-! ## Connecting to SurfacePiOne 1 -/

-- The full proof that SurfaceGroupPresentation 1 ≃ ℤ × ℤ requires showing that
-- every word is equivalent to its canonical form a^m · b^n. This abelianization
-- argument needs careful handling of zero powers and commutator relations.
--
-- For now, we define the winding functions and note that the round-trip
-- property for SurfacePiOne 1 would follow from this abelianization.

/-- The winding A function on SurfacePiOne 1. -/
noncomputable def torusWindingA_def [HasPiOneEquivPresentation 1] : SurfacePiOne 1 → Int :=
  fun α => presentationWindingA ((piOneEquivPresentation 1).toFun α)

/-- The winding B function on SurfacePiOne 1. -/
noncomputable def torusWindingB_def [HasPiOneEquivPresentation 1] : SurfacePiOne 1 → Int :=
  fun α => presentationWindingB ((piOneEquivPresentation 1).toFun α)

/-- Construct a loop from windings. -/
noncomputable def torusOfWindings_def [HasPiOneEquivPresentation 1] (m n : Int) : SurfacePiOne 1 :=
  (piOneEquivPresentation 1).invFun (presentationOfWindings m n)

/-! ## Round-trip properties -/

/-- Helper to prove the right inverse at the presentation level. -/
theorem presentation_right_inv [HasPiOneEquivPresentation 1] (m n : Int) :
    (presentationWindingA
      ((piOneEquivPresentation 1).toFun
        ((piOneEquivPresentation 1).invFun (presentationOfWindings m n))),
     presentationWindingB
      ((piOneEquivPresentation 1).toFun
        ((piOneEquivPresentation 1).invFun (presentationOfWindings m n)))) = (m, n) := by
  ext
  · -- First component
    calc presentationWindingA
           ((piOneEquivPresentation 1).toFun
             ((piOneEquivPresentation 1).invFun (presentationOfWindings m n)))
      _ = presentationWindingA (presentationOfWindings m n) := by
          congr 1; exact (piOneEquivPresentation 1).right_inv (presentationOfWindings m n)
      _ = m := presentationWindingA_ofWindings m n
  · -- Second component
    calc presentationWindingB
           ((piOneEquivPresentation 1).toFun
             ((piOneEquivPresentation 1).invFun (presentationOfWindings m n)))
      _ = presentationWindingB (presentationOfWindings m n) := by
          congr 1; exact (piOneEquivPresentation 1).right_inv (presentationOfWindings m n)
      _ = n := presentationWindingB_ofWindings m n

/-- Right inverse: windings of constructed loop are the original values.
    The proof shows that windings ∘ presentationOfWindings = id. -/
theorem torus_right_inv_def [HasPiOneEquivPresentation 1] (m n : Int) :
    (torusWindingA_def (torusOfWindings_def m n),
     torusWindingB_def (torusOfWindings_def m n)) = (m, n) := by
  unfold torusWindingA_def torusWindingB_def torusOfWindings_def
  exact presentation_right_inv m n

-- Note: torus_left_inv_def is proved below, after the abelianization lemmas
-- are established (see word_eq_canonical and presentation_eq_canonical).

/-! ## Abelianization: Proving ab ≈ ba

The key to the left inverse is showing that SurfaceGroupPresentation 1 is abelian.
From the commutator relation [a,b] = aba⁻¹b⁻¹ = 1, we can derive ab = ba.
-/

/-- Helper: concat is associative in SurfaceGroupRel. -/
theorem rel_concat_assoc (w1 w2 w3 : FreeGroupWord (2 * 1)) :
    SurfaceGroupRel 1 (FreeGroupWord.concat (FreeGroupWord.concat w1 w2) w3)
                      (FreeGroupWord.concat w1 (FreeGroupWord.concat w2 w3)) :=
  by rw [FreeGroupWord.concat_assoc]; exact SurfaceGroupRel.refl _

/-- Helper: nil is left identity in SurfaceGroupRel. -/
theorem rel_concat_nil_left (w : FreeGroupWord (2 * 1)) :
    SurfaceGroupRel 1 (FreeGroupWord.concat FreeGroupWord.nil w) w :=
  SurfaceGroupRel.refl w

/-- Helper: nil is right identity in SurfaceGroupRel. -/
theorem rel_concat_nil_right (w : FreeGroupWord (2 * 1)) :
    SurfaceGroupRel 1 (FreeGroupWord.concat w FreeGroupWord.nil) w := by
  rw [FreeGroupWord.concat_nil_right]
  exact SurfaceGroupRel.refl w

/-- The surface relation word for genus 1: [a,b] = aba⁻¹b⁻¹ -/
theorem surfaceRelWord1_eq :
    surfaceRelationWord 1 = commutatorWord fin2_zero fin2_one := by
  rfl

/-- The commutator [a,b] is equivalent to nil. -/
theorem commutator_rel_nil :
    SurfaceGroupRel 1 (commutatorWord fin2_zero fin2_one) FreeGroupWord.nil := by
  have h := SurfaceGroupRel.surface_rel (by omega : 1 > 0)
  rw [surfaceRelWord1_eq] at h
  exact h

/-- Shorthand for single generator words.
    Note: We use (2 * 1) instead of 2 to match SurfaceGroupRel 1's type. -/
abbrev wordA : FreeGroupWord (2 * 1) := FreeGroupWord.single fin2_zero 1
abbrev wordAinv : FreeGroupWord (2 * 1) := FreeGroupWord.single fin2_zero (-1)
abbrev wordB : FreeGroupWord (2 * 1) := FreeGroupWord.single fin2_one 1
abbrev wordBinv : FreeGroupWord (2 * 1) := FreeGroupWord.single fin2_one (-1)

/-- The commutator word expanded. -/
theorem commutatorWord_expand :
    commutatorWord fin2_zero fin2_one =
    FreeGroupWord.concat (FreeGroupWord.concat (FreeGroupWord.concat wordA wordB) wordAinv) wordBinv := by
  rfl

/-- Inverse cancellation: x · x⁻¹ ≈ nil -/
theorem rel_inv_cancel_a :
    SurfaceGroupRel 1 (FreeGroupWord.concat wordA wordAinv) FreeGroupWord.nil :=
  SurfaceGroupRel.inv_cancel_right fin2_zero

theorem rel_inv_cancel_ainv :
    SurfaceGroupRel 1 (FreeGroupWord.concat wordAinv wordA) FreeGroupWord.nil :=
  SurfaceGroupRel.inv_cancel_left fin2_zero

theorem rel_inv_cancel_b :
    SurfaceGroupRel 1 (FreeGroupWord.concat wordB wordBinv) FreeGroupWord.nil :=
  SurfaceGroupRel.inv_cancel_right fin2_one

theorem rel_inv_cancel_binv :
    SurfaceGroupRel 1 (FreeGroupWord.concat wordBinv wordB) FreeGroupWord.nil :=
  SurfaceGroupRel.inv_cancel_left fin2_one

/-- Commutativity: ab ≈ ba

Proof: From [a,b] = aba⁻¹b⁻¹ = 1, we derive:
  aba⁻¹b⁻¹ ≈ nil
  (aba⁻¹b⁻¹)b ≈ b        (concat on right)
  aba⁻¹(b⁻¹b) ≈ b        (associativity)
  aba⁻¹ ≈ b              (b⁻¹b = nil)
  (aba⁻¹)a ≈ ba          (concat on right)
  ab(a⁻¹a) ≈ ba          (associativity)
  ab ≈ ba                (a⁻¹a = nil)
-/
theorem ab_eq_ba :
    SurfaceGroupRel 1 (FreeGroupWord.concat wordA wordB)
                      (FreeGroupWord.concat wordB wordA) := by
  -- Start from [a,b] ≈ nil
  have h1 := commutator_rel_nil
  -- [a,b] = (((a · b) · a⁻¹) · b⁻¹)
  -- Multiply on right by b: [a,b] · b ≈ nil · b ≈ b
  have h2 : SurfaceGroupRel 1
      (FreeGroupWord.concat (commutatorWord fin2_zero fin2_one) wordB)
      wordB := by
    apply SurfaceGroupRel.trans (SurfaceGroupRel.concat_right wordB h1)
    exact rel_concat_nil_left wordB
  -- [a,b] · b = ((a·b)·a⁻¹·b⁻¹)·b
  -- Use associativity: = (a·b)·a⁻¹·(b⁻¹·b)
  have h3 : SurfaceGroupRel 1
      (FreeGroupWord.concat (commutatorWord fin2_zero fin2_one) wordB)
      (FreeGroupWord.concat (FreeGroupWord.concat (FreeGroupWord.concat wordA wordB) wordAinv)
        (FreeGroupWord.concat wordBinv wordB)) := by
    simp only [commutatorWord_expand]
    rw [FreeGroupWord.concat_assoc]
    exact SurfaceGroupRel.refl _
  -- b⁻¹·b ≈ nil
  have h4 : SurfaceGroupRel 1
      (FreeGroupWord.concat (FreeGroupWord.concat (FreeGroupWord.concat wordA wordB) wordAinv)
        (FreeGroupWord.concat wordBinv wordB))
      (FreeGroupWord.concat (FreeGroupWord.concat (FreeGroupWord.concat wordA wordB) wordAinv)
        FreeGroupWord.nil) :=
    SurfaceGroupRel.concat_left _ rel_inv_cancel_binv
  -- w · nil ≈ w
  have h5 : SurfaceGroupRel 1
      (FreeGroupWord.concat (FreeGroupWord.concat (FreeGroupWord.concat wordA wordB) wordAinv)
        FreeGroupWord.nil)
      (FreeGroupWord.concat (FreeGroupWord.concat wordA wordB) wordAinv) :=
    rel_concat_nil_right _
  -- So: (a·b)·a⁻¹ ≈ b
  have haba_inv_eq_b : SurfaceGroupRel 1
      (FreeGroupWord.concat (FreeGroupWord.concat wordA wordB) wordAinv)
      wordB := by
    apply SurfaceGroupRel.trans (SurfaceGroupRel.symm h5)
    apply SurfaceGroupRel.trans (SurfaceGroupRel.symm h4)
    apply SurfaceGroupRel.trans (SurfaceGroupRel.symm h3)
    exact h2
  -- Now multiply on right by a: ((a·b)·a⁻¹)·a ≈ b·a
  have h6 : SurfaceGroupRel 1
      (FreeGroupWord.concat (FreeGroupWord.concat (FreeGroupWord.concat wordA wordB) wordAinv) wordA)
      (FreeGroupWord.concat wordB wordA) :=
    SurfaceGroupRel.concat_right wordA haba_inv_eq_b
  -- Use associativity: ((a·b)·a⁻¹)·a = (a·b)·(a⁻¹·a)
  have h7 : SurfaceGroupRel 1
      (FreeGroupWord.concat (FreeGroupWord.concat (FreeGroupWord.concat wordA wordB) wordAinv) wordA)
      (FreeGroupWord.concat (FreeGroupWord.concat wordA wordB) (FreeGroupWord.concat wordAinv wordA)) := by
    rw [FreeGroupWord.concat_assoc]
    exact SurfaceGroupRel.refl _
  -- a⁻¹·a ≈ nil
  have h8 : SurfaceGroupRel 1
      (FreeGroupWord.concat (FreeGroupWord.concat wordA wordB) (FreeGroupWord.concat wordAinv wordA))
      (FreeGroupWord.concat (FreeGroupWord.concat wordA wordB) FreeGroupWord.nil) :=
    SurfaceGroupRel.concat_left _ rel_inv_cancel_ainv
  -- w · nil ≈ w
  have h9 : SurfaceGroupRel 1
      (FreeGroupWord.concat (FreeGroupWord.concat wordA wordB) FreeGroupWord.nil)
      (FreeGroupWord.concat wordA wordB) :=
    rel_concat_nil_right _
  -- Chain: a·b ≈ (a·b)·nil ≈ (a·b)·(a⁻¹·a) ≈ ((a·b)·a⁻¹)·a ≈ b·a
  apply SurfaceGroupRel.trans (SurfaceGroupRel.symm h9)
  apply SurfaceGroupRel.trans (SurfaceGroupRel.symm h8)
  apply SurfaceGroupRel.trans (SurfaceGroupRel.symm h7)
  exact h6

/-- ba ≈ ab (symmetric form) -/
theorem ba_eq_ab :
    SurfaceGroupRel 1 (FreeGroupWord.concat wordB wordA)
                      (FreeGroupWord.concat wordA wordB) :=
  SurfaceGroupRel.symm ab_eq_ba

/-! ## Canonical form rewriting

Every word is equivalent to its canonical form a^m · b^n.
We prove this by showing how to move all a's to the left.
-/

/-- Move a single 'b' past a single 'a': b·a ≈ a·b -/
theorem move_b_past_a :
    SurfaceGroupRel 1 (FreeGroupWord.concat wordB wordA)
                      (FreeGroupWord.concat wordA wordB) :=
  ba_eq_ab

/-- Move a single 'b⁻¹' past a single 'a': b⁻¹·a ≈ a·b⁻¹

From ab = ba, we can derive:
  a⁻¹·(ab)·b⁻¹ = a⁻¹·(ba)·b⁻¹
  (a⁻¹a)·b·b⁻¹ = a⁻¹·b·(ab⁻¹)  [using associativity cleverly]
  Actually, let's derive it differently:

  ab = ba
  Multiply by a⁻¹ on left: a⁻¹·ab = a⁻¹·ba
  b = a⁻¹·ba
  Multiply by b⁻¹ on right: b·b⁻¹ = a⁻¹·ba·b⁻¹
  nil = a⁻¹·b·(a·b⁻¹)  [not quite right either]

Let me think again. We want: b⁻¹·a ≈ a·b⁻¹

From ab = ba:
  ab·(b⁻¹·a⁻¹) = ba·(b⁻¹·a⁻¹)
  a·(bb⁻¹)·a⁻¹ = b·(aa⁻¹)·b⁻¹... hmm

Alternative: show b⁻¹·a·a⁻¹·b ≈ nil
Then b⁻¹·a ≈ a·b⁻¹ follows.

Actually [b⁻¹,a] = b⁻¹·a·b·a⁻¹
We can derive from [a,b]=1 that [b⁻¹,a]=1 too.

Let's use: from ab=ba, multiply both sides on left by b⁻¹ and right by b⁻¹
  b⁻¹·ab·b⁻¹ = b⁻¹·ba·b⁻¹
  b⁻¹·a·(b·b⁻¹) = (b⁻¹·b)·a·b⁻¹
  b⁻¹·a = a·b⁻¹
-/
theorem move_binv_past_a :
    SurfaceGroupRel 1 (FreeGroupWord.concat wordBinv wordA)
                      (FreeGroupWord.concat wordA wordBinv) := by
  -- From ab = ba, derive b⁻¹·a = a·b⁻¹
  -- Multiply ab=ba on left by b⁻¹: b⁻¹·(ab) ≈ b⁻¹·(ba)
  -- Then: (b⁻¹·a)·b ≈ (b⁻¹·b)·a = a
  -- So: (b⁻¹·a)·b ≈ a
  -- Then: (b⁻¹·a)·b·b⁻¹ ≈ a·b⁻¹
  -- And: b⁻¹·a·(b·b⁻¹) ≈ a·b⁻¹
  -- So: b⁻¹·a ≈ a·b⁻¹
  have hab : SurfaceGroupRel 1 (FreeGroupWord.concat wordA wordB)
                               (FreeGroupWord.concat wordB wordA) := ab_eq_ba
  -- b⁻¹·(ab) ≈ b⁻¹·(ba)
  have h1 : SurfaceGroupRel 1
      (FreeGroupWord.concat wordBinv (FreeGroupWord.concat wordA wordB))
      (FreeGroupWord.concat wordBinv (FreeGroupWord.concat wordB wordA)) :=
    SurfaceGroupRel.concat_left wordBinv hab
  -- b⁻¹·(ab) = (b⁻¹·a)·b by associativity
  have h2a : FreeGroupWord.concat wordBinv (FreeGroupWord.concat wordA wordB) =
             FreeGroupWord.concat (FreeGroupWord.concat wordBinv wordA) wordB := by
    rw [← FreeGroupWord.concat_assoc]
  -- b⁻¹·(ba) = (b⁻¹·b)·a by associativity
  have h2b : FreeGroupWord.concat wordBinv (FreeGroupWord.concat wordB wordA) =
             FreeGroupWord.concat (FreeGroupWord.concat wordBinv wordB) wordA := by
    rw [← FreeGroupWord.concat_assoc]
  -- (b⁻¹·a)·b ≈ (b⁻¹·b)·a
  have h3 : SurfaceGroupRel 1
      (FreeGroupWord.concat (FreeGroupWord.concat wordBinv wordA) wordB)
      (FreeGroupWord.concat (FreeGroupWord.concat wordBinv wordB) wordA) := by
    rw [← h2a, ← h2b]
    exact h1
  -- b⁻¹·b ≈ nil
  have h4 : SurfaceGroupRel 1
      (FreeGroupWord.concat (FreeGroupWord.concat wordBinv wordB) wordA)
      (FreeGroupWord.concat FreeGroupWord.nil wordA) :=
    SurfaceGroupRel.concat_right wordA rel_inv_cancel_binv
  -- nil·a = a
  have h5 : SurfaceGroupRel 1 (FreeGroupWord.concat FreeGroupWord.nil wordA) wordA :=
    rel_concat_nil_left wordA
  -- So: (b⁻¹·a)·b ≈ a
  have hbinv_a_b_eq_a : SurfaceGroupRel 1
      (FreeGroupWord.concat (FreeGroupWord.concat wordBinv wordA) wordB) wordA := by
    apply SurfaceGroupRel.trans h3
    apply SurfaceGroupRel.trans h4
    exact h5
  -- Multiply on right by b⁻¹: ((b⁻¹·a)·b)·b⁻¹ ≈ a·b⁻¹
  have h6 : SurfaceGroupRel 1
      (FreeGroupWord.concat (FreeGroupWord.concat (FreeGroupWord.concat wordBinv wordA) wordB) wordBinv)
      (FreeGroupWord.concat wordA wordBinv) :=
    SurfaceGroupRel.concat_right wordBinv hbinv_a_b_eq_a
  -- ((b⁻¹·a)·b)·b⁻¹ = (b⁻¹·a)·(b·b⁻¹) by associativity
  have h7 : FreeGroupWord.concat (FreeGroupWord.concat (FreeGroupWord.concat wordBinv wordA) wordB) wordBinv =
            FreeGroupWord.concat (FreeGroupWord.concat wordBinv wordA) (FreeGroupWord.concat wordB wordBinv) := by
    rw [FreeGroupWord.concat_assoc]
  -- b·b⁻¹ ≈ nil
  have h8 : SurfaceGroupRel 1
      (FreeGroupWord.concat (FreeGroupWord.concat wordBinv wordA) (FreeGroupWord.concat wordB wordBinv))
      (FreeGroupWord.concat (FreeGroupWord.concat wordBinv wordA) FreeGroupWord.nil) :=
    SurfaceGroupRel.concat_left _ rel_inv_cancel_b
  -- w·nil ≈ w
  have h9 : SurfaceGroupRel 1
      (FreeGroupWord.concat (FreeGroupWord.concat wordBinv wordA) FreeGroupWord.nil)
      (FreeGroupWord.concat wordBinv wordA) :=
    rel_concat_nil_right _
  -- Chain: b⁻¹·a ≈ (b⁻¹·a)·nil ≈ (b⁻¹·a)·(b·b⁻¹) ≈ ((b⁻¹·a)·b)·b⁻¹ ≈ a·b⁻¹
  apply SurfaceGroupRel.trans (SurfaceGroupRel.symm h9)
  apply SurfaceGroupRel.trans (SurfaceGroupRel.symm h8)
  rw [← h7]
  exact h6

/-- Move a single 'b' past a single 'a⁻¹': b·a⁻¹ ≈ a⁻¹·b -/
theorem move_b_past_ainv :
    SurfaceGroupRel 1 (FreeGroupWord.concat wordB wordAinv)
                      (FreeGroupWord.concat wordAinv wordB) := by
  -- Similar to above: from ab=ba, we can derive ba⁻¹=a⁻¹b
  -- Multiply ab=ba on right by a⁻¹: (ab)·a⁻¹ ≈ (ba)·a⁻¹
  -- a·(b·a⁻¹) ≈ b·(a·a⁻¹) = b
  -- So a·(b·a⁻¹) ≈ b
  -- Multiply on left by a⁻¹: a⁻¹·a·(b·a⁻¹) ≈ a⁻¹·b
  -- (a⁻¹·a)·(b·a⁻¹) ≈ a⁻¹·b
  -- b·a⁻¹ ≈ a⁻¹·b
  have hab : SurfaceGroupRel 1 (FreeGroupWord.concat wordA wordB)
                               (FreeGroupWord.concat wordB wordA) := ab_eq_ba
  -- (ab)·a⁻¹ ≈ (ba)·a⁻¹
  have h1 : SurfaceGroupRel 1
      (FreeGroupWord.concat (FreeGroupWord.concat wordA wordB) wordAinv)
      (FreeGroupWord.concat (FreeGroupWord.concat wordB wordA) wordAinv) :=
    SurfaceGroupRel.concat_right wordAinv hab
  -- (ab)·a⁻¹ = a·(b·a⁻¹)
  have h2a : FreeGroupWord.concat (FreeGroupWord.concat wordA wordB) wordAinv =
             FreeGroupWord.concat wordA (FreeGroupWord.concat wordB wordAinv) := by
    rw [FreeGroupWord.concat_assoc]
  -- (ba)·a⁻¹ = b·(a·a⁻¹)
  have h2b : FreeGroupWord.concat (FreeGroupWord.concat wordB wordA) wordAinv =
             FreeGroupWord.concat wordB (FreeGroupWord.concat wordA wordAinv) := by
    rw [FreeGroupWord.concat_assoc]
  -- a·(b·a⁻¹) ≈ b·(a·a⁻¹)
  have h3 : SurfaceGroupRel 1
      (FreeGroupWord.concat wordA (FreeGroupWord.concat wordB wordAinv))
      (FreeGroupWord.concat wordB (FreeGroupWord.concat wordA wordAinv)) := by
    rw [← h2a, ← h2b]
    exact h1
  -- a·a⁻¹ ≈ nil
  have h4 : SurfaceGroupRel 1
      (FreeGroupWord.concat wordB (FreeGroupWord.concat wordA wordAinv))
      (FreeGroupWord.concat wordB FreeGroupWord.nil) :=
    SurfaceGroupRel.concat_left wordB rel_inv_cancel_a
  -- b·nil ≈ b
  have h5 : SurfaceGroupRel 1 (FreeGroupWord.concat wordB FreeGroupWord.nil) wordB :=
    rel_concat_nil_right wordB
  -- So: a·(b·a⁻¹) ≈ b
  have ha_b_ainv_eq_b : SurfaceGroupRel 1
      (FreeGroupWord.concat wordA (FreeGroupWord.concat wordB wordAinv)) wordB := by
    apply SurfaceGroupRel.trans h3
    apply SurfaceGroupRel.trans h4
    exact h5
  -- Multiply on left by a⁻¹: a⁻¹·(a·(b·a⁻¹)) ≈ a⁻¹·b
  have h6 : SurfaceGroupRel 1
      (FreeGroupWord.concat wordAinv (FreeGroupWord.concat wordA (FreeGroupWord.concat wordB wordAinv)))
      (FreeGroupWord.concat wordAinv wordB) :=
    SurfaceGroupRel.concat_left wordAinv ha_b_ainv_eq_b
  -- a⁻¹·(a·(b·a⁻¹)) = (a⁻¹·a)·(b·a⁻¹)
  have h7 : FreeGroupWord.concat wordAinv (FreeGroupWord.concat wordA (FreeGroupWord.concat wordB wordAinv)) =
            FreeGroupWord.concat (FreeGroupWord.concat wordAinv wordA) (FreeGroupWord.concat wordB wordAinv) := by
    rw [← FreeGroupWord.concat_assoc]
  -- a⁻¹·a ≈ nil
  have h8 : SurfaceGroupRel 1
      (FreeGroupWord.concat (FreeGroupWord.concat wordAinv wordA) (FreeGroupWord.concat wordB wordAinv))
      (FreeGroupWord.concat FreeGroupWord.nil (FreeGroupWord.concat wordB wordAinv)) :=
    SurfaceGroupRel.concat_right _ rel_inv_cancel_ainv
  -- nil·w ≈ w
  have h9 : SurfaceGroupRel 1
      (FreeGroupWord.concat FreeGroupWord.nil (FreeGroupWord.concat wordB wordAinv))
      (FreeGroupWord.concat wordB wordAinv) :=
    rel_concat_nil_left _
  -- Chain: b·a⁻¹ ≈ nil·(b·a⁻¹) ≈ (a⁻¹·a)·(b·a⁻¹) ≈ a⁻¹·(a·(b·a⁻¹)) ≈ a⁻¹·b
  apply SurfaceGroupRel.trans (SurfaceGroupRel.symm h9)
  apply SurfaceGroupRel.trans (SurfaceGroupRel.symm h8)
  rw [← h7]
  exact h6

/-- Move a single 'b⁻¹' past a single 'a⁻¹': b⁻¹·a⁻¹ ≈ a⁻¹·b⁻¹ -/
theorem move_binv_past_ainv :
    SurfaceGroupRel 1 (FreeGroupWord.concat wordBinv wordAinv)
                      (FreeGroupWord.concat wordAinv wordBinv) := by
  -- From b⁻¹·a = a·b⁻¹ (move_binv_past_a), we can derive b⁻¹·a⁻¹ = a⁻¹·b⁻¹
  -- Multiply b⁻¹·a = a·b⁻¹ on right by a⁻¹:
  -- (b⁻¹·a)·a⁻¹ = (a·b⁻¹)·a⁻¹
  -- b⁻¹·(a·a⁻¹) = a·(b⁻¹·a⁻¹)  ... hmm this gives b⁻¹ = a·(b⁻¹·a⁻¹)
  -- Then multiply on left by a⁻¹: a⁻¹·b⁻¹ = (a⁻¹·a)·(b⁻¹·a⁻¹) = b⁻¹·a⁻¹
  have h_binv_a : SurfaceGroupRel 1 (FreeGroupWord.concat wordBinv wordA)
                                    (FreeGroupWord.concat wordA wordBinv) := move_binv_past_a
  -- (b⁻¹·a)·a⁻¹ ≈ (a·b⁻¹)·a⁻¹
  have h1 : SurfaceGroupRel 1
      (FreeGroupWord.concat (FreeGroupWord.concat wordBinv wordA) wordAinv)
      (FreeGroupWord.concat (FreeGroupWord.concat wordA wordBinv) wordAinv) :=
    SurfaceGroupRel.concat_right wordAinv h_binv_a
  -- (b⁻¹·a)·a⁻¹ = b⁻¹·(a·a⁻¹)
  have h2a : FreeGroupWord.concat (FreeGroupWord.concat wordBinv wordA) wordAinv =
             FreeGroupWord.concat wordBinv (FreeGroupWord.concat wordA wordAinv) := by
    rw [FreeGroupWord.concat_assoc]
  -- (a·b⁻¹)·a⁻¹ = a·(b⁻¹·a⁻¹)
  have h2b : FreeGroupWord.concat (FreeGroupWord.concat wordA wordBinv) wordAinv =
             FreeGroupWord.concat wordA (FreeGroupWord.concat wordBinv wordAinv) := by
    rw [FreeGroupWord.concat_assoc]
  -- b⁻¹·(a·a⁻¹) ≈ a·(b⁻¹·a⁻¹)
  have h3 : SurfaceGroupRel 1
      (FreeGroupWord.concat wordBinv (FreeGroupWord.concat wordA wordAinv))
      (FreeGroupWord.concat wordA (FreeGroupWord.concat wordBinv wordAinv)) := by
    rw [← h2a, ← h2b]
    exact h1
  -- a·a⁻¹ ≈ nil
  have h4 : SurfaceGroupRel 1
      (FreeGroupWord.concat wordBinv (FreeGroupWord.concat wordA wordAinv))
      (FreeGroupWord.concat wordBinv FreeGroupWord.nil) :=
    SurfaceGroupRel.concat_left wordBinv rel_inv_cancel_a
  -- b⁻¹·nil ≈ b⁻¹
  have h5 : SurfaceGroupRel 1 (FreeGroupWord.concat wordBinv FreeGroupWord.nil) wordBinv :=
    rel_concat_nil_right wordBinv
  -- So: b⁻¹ ≈ a·(b⁻¹·a⁻¹)
  have h_binv_eq_a_binv_ainv : SurfaceGroupRel 1 wordBinv
      (FreeGroupWord.concat wordA (FreeGroupWord.concat wordBinv wordAinv)) := by
    apply SurfaceGroupRel.symm
    apply SurfaceGroupRel.trans (SurfaceGroupRel.symm h3)
    apply SurfaceGroupRel.trans h4
    exact h5
  -- Multiply on left by a⁻¹: a⁻¹·b⁻¹ ≈ a⁻¹·(a·(b⁻¹·a⁻¹))
  have h6 : SurfaceGroupRel 1
      (FreeGroupWord.concat wordAinv wordBinv)
      (FreeGroupWord.concat wordAinv (FreeGroupWord.concat wordA (FreeGroupWord.concat wordBinv wordAinv))) :=
    SurfaceGroupRel.concat_left wordAinv h_binv_eq_a_binv_ainv
  -- a⁻¹·(a·(b⁻¹·a⁻¹)) = (a⁻¹·a)·(b⁻¹·a⁻¹)
  have h7 : FreeGroupWord.concat wordAinv (FreeGroupWord.concat wordA (FreeGroupWord.concat wordBinv wordAinv)) =
            FreeGroupWord.concat (FreeGroupWord.concat wordAinv wordA) (FreeGroupWord.concat wordBinv wordAinv) := by
    rw [← FreeGroupWord.concat_assoc]
  -- a⁻¹·a ≈ nil
  have h8 : SurfaceGroupRel 1
      (FreeGroupWord.concat (FreeGroupWord.concat wordAinv wordA) (FreeGroupWord.concat wordBinv wordAinv))
      (FreeGroupWord.concat FreeGroupWord.nil (FreeGroupWord.concat wordBinv wordAinv)) :=
    SurfaceGroupRel.concat_right _ rel_inv_cancel_ainv
  -- nil·w ≈ w
  have h9 : SurfaceGroupRel 1
      (FreeGroupWord.concat FreeGroupWord.nil (FreeGroupWord.concat wordBinv wordAinv))
      (FreeGroupWord.concat wordBinv wordAinv) :=
    rel_concat_nil_left _
  -- Chain: b⁻¹·a⁻¹ ≈ ... ≈ a⁻¹·b⁻¹
  apply SurfaceGroupRel.trans (SurfaceGroupRel.symm h9)
  apply SurfaceGroupRel.trans (SurfaceGroupRel.symm h8)
  rw [← h7]
  apply SurfaceGroupRel.symm h6

/-! ## Power iteration and canonical forms -/

/-- Single element with power 0 is equivalent to nil. -/
theorem single_pow_zero (i : Fin' (2 * 1)) :
    SurfaceGroupRel 1 (FreeGroupWord.single i 0) FreeGroupWord.nil := by
  -- FreeGroupWord.single i 0 = cons i 0 nil
  -- Use the zero_power rule: cons i 0 rest ≈ rest
  simp only [FreeGroupWord.single]
  exact SurfaceGroupRel.zero_power i FreeGroupWord.nil

/-- Build a^n for natural number n ≥ 0 -/
def wordAPow : Nat → FreeGroupWord (2 * 1)
  | 0 => FreeGroupWord.nil
  | Nat.succ n => FreeGroupWord.concat wordA (wordAPow n)

/-- Build a^(-n) for natural number n ≥ 0 -/
def wordANegPow : Nat → FreeGroupWord (2 * 1)
  | 0 => FreeGroupWord.nil
  | Nat.succ n => FreeGroupWord.concat wordAinv (wordANegPow n)

/-- Build b^n for natural number n ≥ 0 -/
def wordBPow : Nat → FreeGroupWord (2 * 1)
  | 0 => FreeGroupWord.nil
  | Nat.succ n => FreeGroupWord.concat wordB (wordBPow n)

/-- Build b^(-n) for natural number n ≥ 0 -/
def wordBNegPow : Nat → FreeGroupWord (2 * 1)
  | 0 => FreeGroupWord.nil
  | Nat.succ n => FreeGroupWord.concat wordBinv (wordBNegPow n)

/-- sumPowersA of wordAPow n is n -/
theorem sumPowersA_wordAPow (n : Nat) : sumPowersA (wordAPow n) = n := by
  induction n with
  | zero => simp [wordAPow, sumPowersA]
  | succ m ih =>
    simp only [wordAPow, sumPowersA_concat, sumPowersA_single_a, ih]
    omega

/-- sumPowersA of wordANegPow n is -n -/
theorem sumPowersA_wordANegPow (n : Nat) : sumPowersA (wordANegPow n) = -↑n := by
  induction n with
  | zero => simp [wordANegPow, sumPowersA]
  | succ m ih =>
    simp only [wordANegPow, sumPowersA_concat]
    simp only [wordAinv, FreeGroupWord.single, sumPowersA, isGenA, fin2_zero, Fin'.toNat, ih]
    simp +arith

/-- sumPowersB of wordAPow n is 0 -/
theorem sumPowersB_wordAPow (n : Nat) : sumPowersB (wordAPow n) = 0 := by
  induction n with
  | zero => simp [wordAPow, sumPowersB]
  | succ m ih =>
    simp only [wordAPow, sumPowersB_concat, sumPowersB_single_a, ih]
    rfl

/-- sumPowersB of wordBPow n is n -/
theorem sumPowersB_wordBPow (n : Nat) : sumPowersB (wordBPow n) = n := by
  induction n with
  | zero => simp [wordBPow, sumPowersB]
  | succ m ih =>
    simp only [wordBPow, sumPowersB_concat, sumPowersB_single_b, ih]
    omega

/-! ## Word-level abelianization

The key insight is that `b^pow · a^m ≈ a^m · b^pow` for any powers.
This follows from the basic commutativity `ab = ba` by repeated application.
-/

-- Helper lemma for integer arithmetic with Int.ofNat
private theorem int_ofNat_add_one (n : Nat) : (1 : Int) + Int.ofNat (n + 1) = Int.ofNat (n + 2) := by
  -- omega doesn't understand Int.ofNat, so we use simp
  simp only [Int.ofNat_eq_coe]
  omega

private theorem int_neg_add_negSucc (n : Nat) : (-1 : Int) + Int.negSucc n = Int.negSucc (n + 1) := by
  simp only [Int.negSucc_eq]
  omega

/-- Helper: b^n · a ≈ a · b^n for any integer n.
    Proved by strong induction on |n|. -/
theorem b_pow_comm_single_a : (n : Int) →
    SurfaceGroupRel 1
      (FreeGroupWord.concat (FreeGroupWord.single fin2_one n) wordA)
      (FreeGroupWord.concat wordA (FreeGroupWord.single fin2_one n))
  | (Int.ofNat 0) => by
    -- b^0 · a ≈ a ≈ a · b^0
    -- First: b^0 · a ≈ a (using zero_power on b^0)
    have h1 : SurfaceGroupRel 1
        (FreeGroupWord.concat (FreeGroupWord.single fin2_one 0) wordA)
        wordA := by
      -- b^0 = cons fin2_one 0 nil, so concat (b^0) a ≈ concat nil a = a
      apply SurfaceGroupRel.trans (SurfaceGroupRel.concat_right wordA
        (SurfaceGroupRel.zero_power fin2_one FreeGroupWord.nil))
      exact rel_concat_nil_left wordA
    -- Second: a ≈ a · b^0 (symmetrically)
    have h2 : SurfaceGroupRel 1 wordA
        (FreeGroupWord.concat wordA (FreeGroupWord.single fin2_one 0)) := by
      apply SurfaceGroupRel.symm
      apply SurfaceGroupRel.trans (SurfaceGroupRel.concat_left wordA
        (SurfaceGroupRel.zero_power fin2_one FreeGroupWord.nil))
      exact rel_concat_nil_right wordA
    exact SurfaceGroupRel.trans h1 h2
  | (Int.ofNat 1) => ba_eq_ab  -- b · a = a · b
  | (Int.ofNat (n + 2)) => by
    -- b^(n+2) · a = b · b^(n+1) · a ≈ b · a · b^(n+1) ≈ a · b · b^(n+1) = a · b^(n+2)
    have ih := b_pow_comm_single_a (Int.ofNat (n + 1))
    -- b^(n+2) = b^1 · b^(n+1) by power_combine (reversed)
    have split : SurfaceGroupRel 1
        (FreeGroupWord.single fin2_one (Int.ofNat (n + 2)))
        (FreeGroupWord.concat wordB (FreeGroupWord.single fin2_one (Int.ofNat (n + 1)))) := by
      simp only [FreeGroupWord.single, FreeGroupWord.concat, wordB]
      apply SurfaceGroupRel.symm
      -- Need: cons 1 (cons (n+1) nil) ≈ cons (n+2) nil
      have h := SurfaceGroupRel.power_combine fin2_one 1 (Int.ofNat (n + 1)) FreeGroupWord.nil
      -- h : cons 1 (cons (n+1) nil) ≈ cons (1 + (n+1)) nil
      -- We need to show (1 : Int) + Int.ofNat (n + 1) = Int.ofNat (n + 2)
      -- power_combine gives: cons 1 (cons (n+1) nil) ≈ cons (1 + (n+1)) nil
      rw [int_ofNat_add_one] at h
      exact h
    -- b^(n+2) · a ≈ (b · b^(n+1)) · a
    have step1 : SurfaceGroupRel 1
        (FreeGroupWord.concat (FreeGroupWord.single fin2_one (Int.ofNat (n + 2))) wordA)
        (FreeGroupWord.concat (FreeGroupWord.concat wordB (FreeGroupWord.single fin2_one (Int.ofNat (n + 1)))) wordA) :=
      SurfaceGroupRel.concat_right wordA split
    -- (b · b^(n+1)) · a = b · (b^(n+1) · a) by assoc
    have step2 : FreeGroupWord.concat (FreeGroupWord.concat wordB (FreeGroupWord.single fin2_one (Int.ofNat (n + 1)))) wordA =
        FreeGroupWord.concat wordB (FreeGroupWord.concat (FreeGroupWord.single fin2_one (Int.ofNat (n + 1))) wordA) := by
      rw [FreeGroupWord.concat_assoc]
    -- b · (b^(n+1) · a) ≈ b · (a · b^(n+1)) by IH
    have step3 : SurfaceGroupRel 1
        (FreeGroupWord.concat wordB (FreeGroupWord.concat (FreeGroupWord.single fin2_one (Int.ofNat (n + 1))) wordA))
        (FreeGroupWord.concat wordB (FreeGroupWord.concat wordA (FreeGroupWord.single fin2_one (Int.ofNat (n + 1))))) :=
      SurfaceGroupRel.concat_left wordB ih
    -- b · (a · b^(n+1)) = (b · a) · b^(n+1) by assoc
    have step4 : FreeGroupWord.concat wordB (FreeGroupWord.concat wordA (FreeGroupWord.single fin2_one (Int.ofNat (n + 1)))) =
        FreeGroupWord.concat (FreeGroupWord.concat wordB wordA) (FreeGroupWord.single fin2_one (Int.ofNat (n + 1))) := by
      rw [← FreeGroupWord.concat_assoc]
    -- (b · a) · b^(n+1) ≈ (a · b) · b^(n+1) by ba_eq_ab
    have step5 : SurfaceGroupRel 1
        (FreeGroupWord.concat (FreeGroupWord.concat wordB wordA) (FreeGroupWord.single fin2_one (Int.ofNat (n + 1))))
        (FreeGroupWord.concat (FreeGroupWord.concat wordA wordB) (FreeGroupWord.single fin2_one (Int.ofNat (n + 1)))) :=
      SurfaceGroupRel.concat_right _ ba_eq_ab
    -- (a · b) · b^(n+1) = a · (b · b^(n+1)) by assoc
    have step6 : FreeGroupWord.concat (FreeGroupWord.concat wordA wordB) (FreeGroupWord.single fin2_one (Int.ofNat (n + 1))) =
        FreeGroupWord.concat wordA (FreeGroupWord.concat wordB (FreeGroupWord.single fin2_one (Int.ofNat (n + 1)))) := by
      rw [FreeGroupWord.concat_assoc]
    -- a · (b · b^(n+1)) ≈ a · b^(n+2) by power_combine
    have step7 : SurfaceGroupRel 1
        (FreeGroupWord.concat wordA (FreeGroupWord.concat wordB (FreeGroupWord.single fin2_one (Int.ofNat (n + 1)))))
        (FreeGroupWord.concat wordA (FreeGroupWord.single fin2_one (Int.ofNat (n + 2)))) :=
      SurfaceGroupRel.concat_left wordA (SurfaceGroupRel.symm split)
    -- Chain everything
    apply SurfaceGroupRel.trans step1
    rw [step2]
    apply SurfaceGroupRel.trans step3
    rw [step4]
    apply SurfaceGroupRel.trans step5
    rw [step6]
    exact step7
  | (Int.negSucc 0) => move_binv_past_a  -- b^(-1) · a = a · b^(-1)
  | (Int.negSucc (n + 1)) => by
    -- b^(-(n+2)) · a = b^(-1) · b^(-(n+1)) · a ≈ b^(-1) · a · b^(-(n+1)) ≈ a · b^(-1) · b^(-(n+1)) = a · b^(-(n+2))
    have ih := b_pow_comm_single_a (Int.negSucc n)
    -- b^(-(n+2)) = b^(-1) · b^(-(n+1)) by power_combine (reversed)
    have split : SurfaceGroupRel 1
        (FreeGroupWord.single fin2_one (Int.negSucc (n + 1)))
        (FreeGroupWord.concat wordBinv (FreeGroupWord.single fin2_one (Int.negSucc n))) := by
      simp only [FreeGroupWord.single, FreeGroupWord.concat, wordBinv]
      apply SurfaceGroupRel.symm
      have h := SurfaceGroupRel.power_combine fin2_one (-1) (Int.negSucc n) FreeGroupWord.nil
      -- h : cons (-1) (cons -(n+1) nil) ≈ cons (-1 + -(n+1)) nil
      -- Need: cons (-(n+2)) nil, i.e., Int.negSucc (n+1)
      -- Int.negSucc n = -(n+1), so -1 + -(n+1) = -(n+2) = Int.negSucc (n+1)
      have arith : (-1 : Int) + Int.negSucc n = Int.negSucc (n + 1) := by
        simp only [Int.negSucc_eq]
        omega
      rw [arith] at h
      exact h
    -- Similar chain as positive case
    have step1 : SurfaceGroupRel 1
        (FreeGroupWord.concat (FreeGroupWord.single fin2_one (Int.negSucc (n + 1))) wordA)
        (FreeGroupWord.concat (FreeGroupWord.concat wordBinv (FreeGroupWord.single fin2_one (Int.negSucc n))) wordA) :=
      SurfaceGroupRel.concat_right wordA split
    have step2 : FreeGroupWord.concat (FreeGroupWord.concat wordBinv (FreeGroupWord.single fin2_one (Int.negSucc n))) wordA =
        FreeGroupWord.concat wordBinv (FreeGroupWord.concat (FreeGroupWord.single fin2_one (Int.negSucc n)) wordA) := by
      rw [FreeGroupWord.concat_assoc]
    have step3 : SurfaceGroupRel 1
        (FreeGroupWord.concat wordBinv (FreeGroupWord.concat (FreeGroupWord.single fin2_one (Int.negSucc n)) wordA))
        (FreeGroupWord.concat wordBinv (FreeGroupWord.concat wordA (FreeGroupWord.single fin2_one (Int.negSucc n)))) :=
      SurfaceGroupRel.concat_left wordBinv ih
    have step4 : FreeGroupWord.concat wordBinv (FreeGroupWord.concat wordA (FreeGroupWord.single fin2_one (Int.negSucc n))) =
        FreeGroupWord.concat (FreeGroupWord.concat wordBinv wordA) (FreeGroupWord.single fin2_one (Int.negSucc n)) := by
      rw [← FreeGroupWord.concat_assoc]
    have step5 : SurfaceGroupRel 1
        (FreeGroupWord.concat (FreeGroupWord.concat wordBinv wordA) (FreeGroupWord.single fin2_one (Int.negSucc n)))
        (FreeGroupWord.concat (FreeGroupWord.concat wordA wordBinv) (FreeGroupWord.single fin2_one (Int.negSucc n))) :=
      SurfaceGroupRel.concat_right _ move_binv_past_a
    have step6 : FreeGroupWord.concat (FreeGroupWord.concat wordA wordBinv) (FreeGroupWord.single fin2_one (Int.negSucc n)) =
        FreeGroupWord.concat wordA (FreeGroupWord.concat wordBinv (FreeGroupWord.single fin2_one (Int.negSucc n))) := by
      rw [FreeGroupWord.concat_assoc]
    have step7 : SurfaceGroupRel 1
        (FreeGroupWord.concat wordA (FreeGroupWord.concat wordBinv (FreeGroupWord.single fin2_one (Int.negSucc n))))
        (FreeGroupWord.concat wordA (FreeGroupWord.single fin2_one (Int.negSucc (n + 1)))) :=
      SurfaceGroupRel.concat_left wordA (SurfaceGroupRel.symm split)
    apply SurfaceGroupRel.trans step1
    rw [step2]
    apply SurfaceGroupRel.trans step3
    rw [step4]
    apply SurfaceGroupRel.trans step5
    rw [step6]
    exact step7
termination_by n => n.natAbs

/-- Helper: b^n · a^(-1) ≈ a^(-1) · b^n for any integer n. -/
theorem b_pow_comm_single_ainv : (n : Int) →
    SurfaceGroupRel 1
      (FreeGroupWord.concat (FreeGroupWord.single fin2_one n) wordAinv)
      (FreeGroupWord.concat wordAinv (FreeGroupWord.single fin2_one n))
  | (Int.ofNat 0) => by
    -- b^0 · a⁻¹ ≈ a⁻¹ ≈ a⁻¹ · b^0
    have h1 : SurfaceGroupRel 1
        (FreeGroupWord.concat (FreeGroupWord.single fin2_one 0) wordAinv)
        wordAinv := by
      apply SurfaceGroupRel.trans (SurfaceGroupRel.concat_right wordAinv
        (SurfaceGroupRel.zero_power fin2_one FreeGroupWord.nil))
      exact rel_concat_nil_left wordAinv
    have h2 : SurfaceGroupRel 1 wordAinv
        (FreeGroupWord.concat wordAinv (FreeGroupWord.single fin2_one 0)) := by
      apply SurfaceGroupRel.symm
      apply SurfaceGroupRel.trans (SurfaceGroupRel.concat_left wordAinv
        (SurfaceGroupRel.zero_power fin2_one FreeGroupWord.nil))
      exact rel_concat_nil_right wordAinv
    exact SurfaceGroupRel.trans h1 h2
  | (Int.ofNat 1) => move_b_past_ainv
  | (Int.ofNat (n + 2)) => by
    have ih := b_pow_comm_single_ainv (Int.ofNat (n + 1))
    have split : SurfaceGroupRel 1
        (FreeGroupWord.single fin2_one (Int.ofNat (n + 2)))
        (FreeGroupWord.concat wordB (FreeGroupWord.single fin2_one (Int.ofNat (n + 1)))) := by
      simp only [FreeGroupWord.single, FreeGroupWord.concat, wordB]
      apply SurfaceGroupRel.symm
      have h := SurfaceGroupRel.power_combine fin2_one 1 (Int.ofNat (n + 1)) FreeGroupWord.nil
      rw [int_ofNat_add_one] at h
      exact h
    apply SurfaceGroupRel.trans (SurfaceGroupRel.concat_right wordAinv split)
    rw [FreeGroupWord.concat_assoc]
    apply SurfaceGroupRel.trans (SurfaceGroupRel.concat_left wordB ih)
    rw [← FreeGroupWord.concat_assoc]
    apply SurfaceGroupRel.trans (SurfaceGroupRel.concat_right _ move_b_past_ainv)
    rw [FreeGroupWord.concat_assoc]
    exact SurfaceGroupRel.concat_left wordAinv (SurfaceGroupRel.symm split)
  | (Int.negSucc 0) => move_binv_past_ainv
  | (Int.negSucc (n + 1)) => by
    have ih := b_pow_comm_single_ainv (Int.negSucc n)
    have split : SurfaceGroupRel 1
        (FreeGroupWord.single fin2_one (Int.negSucc (n + 1)))
        (FreeGroupWord.concat wordBinv (FreeGroupWord.single fin2_one (Int.negSucc n))) := by
      simp only [FreeGroupWord.single, FreeGroupWord.concat, wordBinv]
      apply SurfaceGroupRel.symm
      have h := SurfaceGroupRel.power_combine fin2_one (-1) (Int.negSucc n) FreeGroupWord.nil
      rw [int_neg_add_negSucc] at h
      exact h
    apply SurfaceGroupRel.trans (SurfaceGroupRel.concat_right wordAinv split)
    rw [FreeGroupWord.concat_assoc]
    apply SurfaceGroupRel.trans (SurfaceGroupRel.concat_left wordBinv ih)
    rw [← FreeGroupWord.concat_assoc]
    apply SurfaceGroupRel.trans (SurfaceGroupRel.concat_right _ move_binv_past_ainv)
    rw [FreeGroupWord.concat_assoc]
    exact SurfaceGroupRel.concat_left wordAinv (SurfaceGroupRel.symm split)
termination_by n => n.natAbs

/-- Move a single b^n past a single a^m: (b^n) · (a^m) ≈ (a^m) · (b^n).
    Proved by induction on |m| using b_pow_comm_single_a/ainv. -/
theorem move_single_b_past_single_a : (m n : Int) →
    SurfaceGroupRel 1
      (FreeGroupWord.concat (FreeGroupWord.single fin2_one n) (FreeGroupWord.single fin2_zero m))
      (FreeGroupWord.concat (FreeGroupWord.single fin2_zero m) (FreeGroupWord.single fin2_one n))
  | (Int.ofNat 0), n => by
    -- b^n · a^0 ≈ b^n ≈ a^0 · b^n
    -- First: b^n · a^0 ≈ b^n (a^0 ≈ nil)
    have h1 : SurfaceGroupRel 1
        (FreeGroupWord.concat (FreeGroupWord.single fin2_one n) (FreeGroupWord.single fin2_zero 0))
        (FreeGroupWord.single fin2_one n) := by
      apply SurfaceGroupRel.trans (SurfaceGroupRel.concat_left _ (SurfaceGroupRel.zero_power fin2_zero FreeGroupWord.nil))
      exact rel_concat_nil_right _
    -- Second: b^n ≈ a^0 · b^n (a^0 ≈ nil)
    have h2 : SurfaceGroupRel 1 (FreeGroupWord.single fin2_one n)
        (FreeGroupWord.concat (FreeGroupWord.single fin2_zero 0) (FreeGroupWord.single fin2_one n)) := by
      apply SurfaceGroupRel.symm
      apply SurfaceGroupRel.trans (SurfaceGroupRel.concat_right _ (SurfaceGroupRel.zero_power fin2_zero FreeGroupWord.nil))
      exact rel_concat_nil_left _
    exact SurfaceGroupRel.trans h1 h2
  | (Int.ofNat 1), n => b_pow_comm_single_a n
  | (Int.ofNat (m + 2)), n => by
    -- b^n · a^(m+2) = b^n · a · a^(m+1) ≈ a · b^n · a^(m+1) ≈ a · a^(m+1) · b^n = a^(m+2) · b^n
    have ih := move_single_b_past_single_a (Int.ofNat (m + 1)) n
    have ha := b_pow_comm_single_a n
    -- a^(m+2) = a · a^(m+1) by power_combine (reversed)
    have split_a : SurfaceGroupRel 1
        (FreeGroupWord.single fin2_zero (Int.ofNat (m + 2)))
        (FreeGroupWord.concat wordA (FreeGroupWord.single fin2_zero (Int.ofNat (m + 1)))) := by
      simp only [FreeGroupWord.single, FreeGroupWord.concat, wordA]
      apply SurfaceGroupRel.symm
      have h := SurfaceGroupRel.power_combine fin2_zero 1 (Int.ofNat (m + 1)) FreeGroupWord.nil
      rw [int_ofNat_add_one] at h
      exact h
    -- b^n · a^(m+2) ≈ b^n · (a · a^(m+1))
    apply SurfaceGroupRel.trans (SurfaceGroupRel.concat_left _ split_a)
    -- = (b^n · a) · a^(m+1) by assoc
    rw [← FreeGroupWord.concat_assoc]
    -- ≈ (a · b^n) · a^(m+1) by ha
    apply SurfaceGroupRel.trans (SurfaceGroupRel.concat_right _ ha)
    -- = a · (b^n · a^(m+1)) by assoc
    rw [FreeGroupWord.concat_assoc]
    -- ≈ a · (a^(m+1) · b^n) by ih
    apply SurfaceGroupRel.trans (SurfaceGroupRel.concat_left wordA ih)
    -- = (a · a^(m+1)) · b^n by assoc
    rw [← FreeGroupWord.concat_assoc]
    -- ≈ a^(m+2) · b^n by power_combine
    exact SurfaceGroupRel.concat_right _ (SurfaceGroupRel.symm split_a)
  | (Int.negSucc 0), n => b_pow_comm_single_ainv n
  | (Int.negSucc (m + 1)), n => by
    have ih := move_single_b_past_single_a (Int.negSucc m) n
    have ha := b_pow_comm_single_ainv n
    have split_a : SurfaceGroupRel 1
        (FreeGroupWord.single fin2_zero (Int.negSucc (m + 1)))
        (FreeGroupWord.concat wordAinv (FreeGroupWord.single fin2_zero (Int.negSucc m))) := by
      simp only [FreeGroupWord.single, FreeGroupWord.concat, wordAinv]
      apply SurfaceGroupRel.symm
      have h := SurfaceGroupRel.power_combine fin2_zero (-1) (Int.negSucc m) FreeGroupWord.nil
      rw [int_neg_add_negSucc] at h
      exact h
    apply SurfaceGroupRel.trans (SurfaceGroupRel.concat_left _ split_a)
    rw [← FreeGroupWord.concat_assoc]
    apply SurfaceGroupRel.trans (SurfaceGroupRel.concat_right _ ha)
    rw [FreeGroupWord.concat_assoc]
    apply SurfaceGroupRel.trans (SurfaceGroupRel.concat_left wordAinv ih)
    rw [← FreeGroupWord.concat_assoc]
    exact SurfaceGroupRel.concat_right _ (SurfaceGroupRel.symm split_a)
termination_by m _ => m.natAbs

/-- The canonical form of a word: a^m · b^n where m = sumPowersA w and n = sumPowersB w. -/
def canonicalForm (w : FreeGroupWord (2 * 1)) : FreeGroupWord (2 * 1) :=
  FreeGroupWord.concat
    (FreeGroupWord.single fin2_zero (sumPowersA w))
    (FreeGroupWord.single fin2_one (sumPowersB w))

/-- Every word is equivalent to its canonical form.
    This is the main word-level abelianization lemma. -/
theorem word_eq_canonical (w : FreeGroupWord (2 * 1)) :
    SurfaceGroupRel 1 w (canonicalForm w) := by
  -- Proof by induction on w
  -- The key is moving generators to their canonical positions
  induction w with
  | nil =>
    -- canonicalForm nil = a^0 · b^0 ≈ nil
    unfold canonicalForm sumPowersA sumPowersB
    simp only [FreeGroupWord.concat, FreeGroupWord.single]
    -- Need: nil ≈ cons 0 0 (cons 1 0 nil)
    -- Use symm of zero_power twice
    apply SurfaceGroupRel.symm
    apply SurfaceGroupRel.trans (SurfaceGroupRel.zero_power fin2_zero _)
    exact SurfaceGroupRel.zero_power fin2_one FreeGroupWord.nil
  | cons gen pow rest ih =>
    -- w = gen^pow · rest
    -- IH: rest ≈ canonicalForm rest = a^(sumPowersA rest) · b^(sumPowersB rest)
    unfold canonicalForm at ih ⊢
    -- Case split on whether gen is a or b
    cases fin2_cases gen with
    | inl hgen =>
      -- gen = a (index 0): cons a^pow rest ≈ a^(pow + sumPowersA rest) · b^(sumPowersB rest)
      subst hgen
      -- sumPowersA (cons fin2_zero pow rest) = pow + sumPowersA rest
      -- sumPowersB (cons fin2_zero pow rest) = sumPowersB rest
      simp only [sumPowersA, sumPowersB, isGenA, isGenB, fin2_zero, Fin'.toNat]
      -- cons fin2_zero pow rest = concat (single fin2_zero pow) rest (by definition of single when pow ≠ 0, or by calculation)
      -- For the proof, we work directly with cons
      -- Goal: cons fin2_zero pow rest ≈ concat (single fin2_zero (pow + sumPowersA rest)) (single fin2_one (sumPowersB rest))
      -- Step 1: cons fin2_zero pow rest ≈ concat (single fin2_zero pow) (canonicalForm rest) by IH
      have step1 : SurfaceGroupRel 1
          (FreeGroupWord.cons fin2_zero pow rest)
          (FreeGroupWord.concat (FreeGroupWord.single fin2_zero pow)
            (FreeGroupWord.concat (FreeGroupWord.single fin2_zero (sumPowersA rest))
                                  (FreeGroupWord.single fin2_one (sumPowersB rest)))) := by
        -- cons i p r = concat (single i p) r for single i p = cons i p nil
        -- Actually, single i p = cons i p nil, so concat (single i p) r = cons i p r
        have heq : FreeGroupWord.concat (FreeGroupWord.single fin2_zero pow) rest =
                   FreeGroupWord.cons fin2_zero pow rest := by
          simp only [FreeGroupWord.single, FreeGroupWord.concat]
        rw [← heq]
        exact SurfaceGroupRel.concat_left (FreeGroupWord.single fin2_zero pow) ih
      -- Step 2: Use associativity and power_combine
      have step2 : SurfaceGroupRel 1
          (FreeGroupWord.concat (FreeGroupWord.single fin2_zero pow)
            (FreeGroupWord.concat (FreeGroupWord.single fin2_zero (sumPowersA rest))
                                  (FreeGroupWord.single fin2_one (sumPowersB rest))))
          (FreeGroupWord.concat (FreeGroupWord.single fin2_zero (pow + sumPowersA rest))
                                (FreeGroupWord.single fin2_one (sumPowersB rest))) := by
        -- Rewrite to ((a^pow · a^(sumPowersA rest)) · b^(sumPowersB rest))
        have assoc : FreeGroupWord.concat (FreeGroupWord.single fin2_zero pow)
                      (FreeGroupWord.concat (FreeGroupWord.single fin2_zero (sumPowersA rest))
                                            (FreeGroupWord.single fin2_one (sumPowersB rest))) =
                     FreeGroupWord.concat (FreeGroupWord.concat (FreeGroupWord.single fin2_zero pow)
                                                                (FreeGroupWord.single fin2_zero (sumPowersA rest)))
                                          (FreeGroupWord.single fin2_one (sumPowersB rest)) := by
          rw [← FreeGroupWord.concat_assoc]
        rw [assoc]
        -- Apply power_combine: single pow · single (sumPowersA rest) ≈ single (pow + sumPowersA rest)
        apply SurfaceGroupRel.concat_right
        simp only [FreeGroupWord.single, FreeGroupWord.concat]
        exact SurfaceGroupRel.power_combine fin2_zero pow (sumPowersA rest) FreeGroupWord.nil
      exact SurfaceGroupRel.trans step1 step2
    | inr hgen =>
      -- gen = b (index 1): cons b^pow rest ≈ a^(sumPowersA rest) · b^(pow + sumPowersB rest)
      subst hgen
      -- sumPowersA (cons fin2_one pow rest) = sumPowersA rest
      -- sumPowersB (cons fin2_one pow rest) = pow + sumPowersB rest
      simp only [sumPowersA, sumPowersB, isGenA, isGenB, fin2_one, Fin'.toNat]
      -- Goal: cons fin2_one pow rest ≈ concat (single fin2_zero (sumPowersA rest)) (single fin2_one (pow + sumPowersB rest))
      -- Step 1: cons fin2_one pow rest ≈ concat (single fin2_one pow) (canonicalForm rest) by IH
      have step1 : SurfaceGroupRel 1
          (FreeGroupWord.cons fin2_one pow rest)
          (FreeGroupWord.concat (FreeGroupWord.single fin2_one pow)
            (FreeGroupWord.concat (FreeGroupWord.single fin2_zero (sumPowersA rest))
                                  (FreeGroupWord.single fin2_one (sumPowersB rest)))) := by
        have heq : FreeGroupWord.concat (FreeGroupWord.single fin2_one pow) rest =
                   FreeGroupWord.cons fin2_one pow rest := by
          simp only [FreeGroupWord.single, FreeGroupWord.concat]
        rw [← heq]
        exact SurfaceGroupRel.concat_left (FreeGroupWord.single fin2_one pow) ih
      -- Step 2: Use associativity, move_single_b_past_single_a, then power_combine
      have step2 : SurfaceGroupRel 1
          (FreeGroupWord.concat (FreeGroupWord.single fin2_one pow)
            (FreeGroupWord.concat (FreeGroupWord.single fin2_zero (sumPowersA rest))
                                  (FreeGroupWord.single fin2_one (sumPowersB rest))))
          (FreeGroupWord.concat (FreeGroupWord.single fin2_zero (sumPowersA rest))
                                (FreeGroupWord.single fin2_one (pow + sumPowersB rest))) := by
        -- Rewrite to ((b^pow · a^(sumPowersA rest)) · b^(sumPowersB rest))
        have assoc1 : FreeGroupWord.concat (FreeGroupWord.single fin2_one pow)
                       (FreeGroupWord.concat (FreeGroupWord.single fin2_zero (sumPowersA rest))
                                             (FreeGroupWord.single fin2_one (sumPowersB rest))) =
                      FreeGroupWord.concat (FreeGroupWord.concat (FreeGroupWord.single fin2_one pow)
                                                                 (FreeGroupWord.single fin2_zero (sumPowersA rest)))
                                           (FreeGroupWord.single fin2_one (sumPowersB rest)) := by
          rw [← FreeGroupWord.concat_assoc]
        rw [assoc1]
        -- Move b^pow past a^(sumPowersA rest)
        have move := move_single_b_past_single_a (sumPowersA rest) pow
        apply SurfaceGroupRel.trans (SurfaceGroupRel.concat_right _ move)
        -- Now have: ((a^(sumPowersA rest) · b^pow) · b^(sumPowersB rest))
        -- Rewrite to (a^(sumPowersA rest) · (b^pow · b^(sumPowersB rest)))
        have assoc2 : FreeGroupWord.concat (FreeGroupWord.concat (FreeGroupWord.single fin2_zero (sumPowersA rest))
                                                                 (FreeGroupWord.single fin2_one pow))
                                           (FreeGroupWord.single fin2_one (sumPowersB rest)) =
                      FreeGroupWord.concat (FreeGroupWord.single fin2_zero (sumPowersA rest))
                                           (FreeGroupWord.concat (FreeGroupWord.single fin2_one pow)
                                                                 (FreeGroupWord.single fin2_one (sumPowersB rest))) := by
          rw [FreeGroupWord.concat_assoc]
        rw [assoc2]
        -- Apply power_combine on b terms
        apply SurfaceGroupRel.concat_left
        simp only [FreeGroupWord.single, FreeGroupWord.concat]
        exact SurfaceGroupRel.power_combine fin2_one pow (sumPowersB rest) FreeGroupWord.nil
      exact SurfaceGroupRel.trans step1 step2

/-- Any presentation element equals its canonical form (quotient level). -/
theorem presentation_eq_canonical (x : SurfaceGroupPresentation 1) :
    x = presentationOfWindings (presentationWindingA x) (presentationWindingB x) := by
  -- Reduce to word level using Quot.ind
  induction x using Quot.ind with
  | _ w =>
    -- Show Quot.mk _ w = Quot.mk _ (canonicalForm w)
    apply Quot.sound
    exact word_eq_canonical w

/-- The torus left inverse at the presentation level. -/
theorem presentation_left_inv (x : SurfaceGroupPresentation 1) :
    presentationOfWindings (presentationWindingA x) (presentationWindingB x) = x := by
  exact (presentation_eq_canonical x).symm

/-! ## Left inverse theorem -/

/-- Left inverse: constructing from windings recovers the original.
    This requires the abelianization lemma showing any presentation element
    equals its canonical form. -/
theorem torus_left_inv_def [HasPiOneEquivPresentation 1] (α : SurfacePiOne 1) :
    torusOfWindings_def (torusWindingA_def α) (torusWindingB_def α) = α := by
  simp only [torusWindingA_def, torusWindingB_def, torusOfWindings_def]
  -- Need to show:
  -- (piOneEquivPresentation 1).invFun
  --   (presentationOfWindings
  --     (presentationWindingA ((piOneEquivPresentation 1).toFun α))
  --     (presentationWindingB ((piOneEquivPresentation 1).toFun α)))
  -- = α
  let x := (piOneEquivPresentation 1).toFun α
  have h_canonical : presentationOfWindings (presentationWindingA x) (presentationWindingB x) = x :=
    presentation_left_inv x
  calc (piOneEquivPresentation 1).invFun
         (presentationOfWindings (presentationWindingA x) (presentationWindingB x))
    _ = (piOneEquivPresentation 1).invFun x := by rw [h_canonical]
    _ = α := (piOneEquivPresentation 1).left_inv α

/-! ## Summary

This file demonstrates the connection between OrientableSurface 1 (genus 1) and the torus.
The key result is that π₁(T²) ≃ ℤ × ℤ, proven via the surface group presentation.

### Main Results (All Fully Proved)

**Winding Number Functions:**
- `sumPowersA_respects_rel`, `sumPowersB_respects_rel` : Winding numbers respect the surface relation
- `presentationWindingA`, `presentationWindingB` : Well-defined winding functions on quotient
- `torusWindingA_def`, `torusWindingB_def` : Winding number extraction via presentation

**Right Inverse:**
- `presentationWindingA_ofWindings`, `presentationWindingB_ofWindings` : Right inverse on presentation
- `presentation_right_inv` : Winding functions are a right inverse at presentation level
- `torus_right_inv_def` : **Complete proof** - windings ∘ ofWindings = id

**Commutativity / Abelianization:**
- `ab_eq_ba`, `ba_eq_ab` : Commutativity in the torus group (key algebraic fact!)
- `move_b_past_a`, `move_binv_past_a`, `move_a_past_b`, etc. : Moving generators past each other
- `b_pow_comm_single_a`, `b_pow_comm_single_ainv` : b^n commutes with single a or a⁻¹
- `move_single_b_past_single_a` : Moving b^n past a^m for arbitrary integer powers

**Left Inverse (Key Abelianization Result):**
- `word_eq_canonical` : Any word ≈ its canonical form a^m · b^n (fully proved by induction)
- `presentation_eq_canonical` : Any presentation element equals its canonical form
- `torus_left_inv_def` : **Complete proof** - ofWindings ∘ windings = id

### Proof Strategy

The word-level abelianization (`word_eq_canonical`) was proved by:
1. **Base case (nil):** Empty word equals canonical form via `zero_power`
2. **Inductive case (cons a^pow rest):** Use IH, then `power_combine` on a-powers
3. **Inductive case (cons b^pow rest):** Use IH, `move_single_b_past_single_a` to commute,
   then `power_combine` on b-powers

Key building blocks:
- `SurfaceGroupRel.power_combine` : Combine consecutive same-generator powers
- `SurfaceGroupRel.zero_power` : Eliminate x^0
- `ab_eq_ba` : Single-power commutativity from commutator relation [a,b] = 1
-/

end OrientableSurface

/-! ## Torus as OrientableSurface 1

We define the torus T² as the genus-1 orientable surface, deriving all
torus constructs from the OrientableSurface machinery.
-/

/-- The torus T² defined as the genus-1 orientable surface. -/
abbrev Torus' : Type _ := OrientableSurface 1

noncomputable section

namespace Torus'

/-- The base point of the torus. -/
abbrev base : Torus' := OrientableSurface.base 1

/-- The unique element of Fin' 1. -/
private def fin1_zero : Fin' 1 := Fin'.fzero

/-- The first fundamental loop (around one hole of the torus). -/
abbrev loop1 : Path base base := OrientableSurface.loopA 1 fin1_zero

/-- The second fundamental loop (around the other hole of the torus). -/
abbrev loop2 : Path base base := OrientableSurface.loopB 1 fin1_zero

/-- The fundamental group of the torus. -/
abbrev π₁ : Type _ := OrientableSurface.SurfacePiOne 1

variable [OrientableSurface.HasPiOneEquivPresentation 1]

/-- The winding number in the loop1 direction. -/
noncomputable abbrev windingA : π₁ → Int := OrientableSurface.torusWindingA_def

/-- The winding number in the loop2 direction. -/
noncomputable abbrev windingB : π₁ → Int := OrientableSurface.torusWindingB_def

/-- Construct a loop from winding numbers. -/
noncomputable abbrev ofWindings : Int → Int → π₁ := OrientableSurface.torusOfWindings_def

/-- The equivalence π₁(T²) ≃ ℤ × ℤ. -/
noncomputable def piOneEquivIntProd : SimpleEquiv π₁ (Int × Int) where
  toFun := fun α => (windingA α, windingB α)
  invFun := fun ⟨m, n⟩ => ofWindings m n
  left_inv := OrientableSurface.torus_left_inv_def
  right_inv := fun ⟨m, n⟩ => OrientableSurface.torus_right_inv_def m n

end Torus'

end -- noncomputable section

end Path
end ComputationalPaths

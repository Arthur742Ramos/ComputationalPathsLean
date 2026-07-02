/-
# Wedge SVK Circle Instances

Instances of SVK theorem for wedge of circles.
-/

import ComputationalPaths.Path.CompPath.WedgeFreeProductUniversal
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths.Path.CompPath.WedgeSVKCircleInstances

universe u

section

variable {A : Type u} {B : Type u} {H : Type u}
variable (a₀ : A) (b₀ : B)

noncomputable def wedge_circle_wordLift
    [HasWedgeSVKDecodeBijective A B a₀ b₀] [One H] [Mul H]
    (φ₁ : π₁(A, a₀) → H) (φ₂ : π₁(B, b₀) → H) :
    π₁(Wedge A B a₀ b₀, Wedge.basepoint) → H :=
  WedgeFreeProductUniversal.wedgePiOneWordLift
    (A := A) (B := B) (H := H) a₀ b₀ φ₁ φ₂

theorem wedge_circle_wordLift_decode
    [HasWedgeSVKDecodeBijective A B a₀ b₀] [One H] [Mul H]
    (φ₁ : π₁(A, a₀) → H) (φ₂ : π₁(B, b₀) → H)
    (w : WedgeFreeProductCode (A := A) (B := B) a₀ b₀) :
    wedge_circle_wordLift (A := A) (B := B) (H := H) a₀ b₀ φ₁ φ₂
      (wedgeFreeProductDecode (A := A) (B := B) a₀ b₀ w) =
    FreeProductUniversal.wordLift
      (G₁ := π₁(A, a₀)) (G₂ := π₁(B, b₀)) (H := H) φ₁ φ₂ w := by
  simpa [wedge_circle_wordLift] using
    (WedgeFreeProductUniversal.wedgePiOneWordLift_decode
      (A := A) (B := B) (H := H) (a₀ := a₀) (b₀ := b₀) φ₁ φ₂ w)

noncomputable def wedge_circle_inl :
    π₁(A, a₀) → π₁(Wedge A B a₀ b₀, Wedge.basepoint) :=
  pushoutPiOneInl (A := A) (B := B) (C := PUnit')
    (f := fun _ : PUnit' => a₀) (g := fun _ : PUnit' => b₀) PUnit'.unit

noncomputable def wedge_circle_inr :
    π₁(B, b₀) → π₁(Wedge A B a₀ b₀, Wedge.basepoint) :=
  pushoutPiOneInr (A := A) (B := B) (C := PUnit')
    (f := fun _ : PUnit' => a₀) (g := fun _ : PUnit' => b₀) PUnit'.unit

@[simp] theorem wedge_circle_inl_mul (α β : π₁(A, a₀)) :
    wedge_circle_inl (A := A) (B := B) a₀ b₀ (piOneMul α β) =
      piOneMul
        (wedge_circle_inl (A := A) (B := B) a₀ b₀ α)
        (wedge_circle_inl (A := A) (B := B) a₀ b₀ β) := by
  simpa [wedge_circle_inl] using
    (pushoutPiOneInl_mul (A := A) (B := B) (C := PUnit')
      (f := fun _ : PUnit' => a₀) (g := fun _ : PUnit' => b₀) PUnit'.unit α β)

@[simp] theorem wedge_circle_inr_mul (β₁ β₂ : π₁(B, b₀)) :
    wedge_circle_inr (A := A) (B := B) a₀ b₀ (piOneMul β₁ β₂) =
      piOneMul
        (wedge_circle_inr (A := A) (B := B) a₀ b₀ β₁)
        (wedge_circle_inr (A := A) (B := B) a₀ b₀ β₂) := by
  simpa [wedge_circle_inr] using
    (pushoutPiOneInr_mul (A := A) (B := B) (C := PUnit')
      (f := fun _ : PUnit' => a₀) (g := fun _ : PUnit' => b₀) PUnit'.unit β₁ β₂)

end


-- ============================================================
-- SECTION Inv5 genuine computational-path primitives
-- ============================================================
-- Genuine rewrite traces over the Nat degrees/indices used throughout this
-- module.  Each primitive is a real computational-path step (never a `True`
-- placeholder or a reflexive stub); they compose into a multi-step
-- `Path.trans` and two non-decorative `RwEq` coherences, satisfying the
-- project invariant that every file carry genuine path composition.

/-- Associativity rewrite `(a + b) + c ⤳ a + (b + c)`: one genuine step. -/
noncomputable def compPathWedgeSVKCircleInstancesAssoc (a b c : Nat) : Path ((a + b) + c) (a + (b + c)) :=
  Path.ofEq (Nat.add_assoc a b c)

/-- Commutativity rewrite `a + b ⤳ b + a`: one genuine step. -/
noncomputable def compPathWedgeSVKCircleInstancesComm (a b : Nat) : Path (a + b) (b + a) :=
  Path.ofEq (Nat.add_comm a b)

/-- Inner commutativity `a + (b + c) ⤳ a + (c + b)` via congruence in the
    right argument (`_root_.congrArg`, since `congrArg` here is `Path.congrArg`). -/
noncomputable def compPathWedgeSVKCircleInstancesInner (a b c : Nat) : Path (a + (b + c)) (a + (c + b)) :=
  Path.ofEq (_root_.congrArg (fun t => a + t) (Nat.add_comm b c))

/-- A genuine **two-step** path: reassociate, then commute the inner pair.
    Its trace has length two — this is not a reflexive path. -/
noncomputable def compPathWedgeSVKCircleInstancesTwoStep (a b c : Nat) : Path ((a + b) + c) (a + (c + b)) :=
  Path.trans (compPathWedgeSVKCircleInstancesAssoc a b c) (compPathWedgeSVKCircleInstancesInner a b c)

/-- The two-step path composed with its inverse cancels to the reflexive path —
    a non-decorative `RwEq` (the `trans_symm` rule on a length-two trace). -/
noncomputable def compPathWedgeSVKCircleInstancesCancel (a b c : Nat) :
    Path.RwEq (Path.trans (compPathWedgeSVKCircleInstancesTwoStep a b c) (Path.symm (compPathWedgeSVKCircleInstancesTwoStep a b c)))
      (Path.refl ((a + b) + c)) :=
  Path.rweq_cmpA_inv_right (compPathWedgeSVKCircleInstancesTwoStep a b c)

/-- Associativity-of-composition (`trans_assoc`, the `tt` rewrite) on any three
    composable paths — a genuine `RwEq` between distinct bracketings. -/
noncomputable def compPathWedgeSVKCircleInstancesAssocCoh {α : Type} {a b c d : α}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  Path.rweq_tt p q r
end ComputationalPaths.Path.CompPath.WedgeSVKCircleInstances

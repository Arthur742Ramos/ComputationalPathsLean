/-
# The Real Projective Plane as a Higher-Inductive Type

This module introduces `ProjectivePlane` (RP²) together with its base-point,
a fundamental loop `α`, and the key axiom `cicl : α ∘ α = refl`.

The real projective plane can be viewed as a disk with antipodal boundary
points identified. This gives rise to a fundamental group π₁(RP²) ≃ ℤ₂.

## Key Results

- `projectiveLoop`: The fundamental loop around RP²
- `projectiveLoopSquare`: α ∘ α = refl (the `cicl` axiom from the paper)
- `projectivePiOneEquivZ2`: π₁(RP²) ≃ ℤ₂ (represented as `Bool`)

## Reference

de Veras, Ramos, de Queiroz & de Oliveira,
"A Topological Application of Labelled Natural Deduction",
South American Journal of Logic (Advance Access)
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Basic.Univalence
import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Rewrite.Quot

namespace ComputationalPaths
namespace Path

universe u v

/-! ## HIT Definition -/

/-- Abstract real projective plane type. -/
axiom ProjectivePlane : Type u

/-- Distinguished point on the projective plane. -/
axiom projectiveBase : ProjectivePlane

/-- Fundamental loop around the projective plane.
    This is the path `α` connecting antipodal points. -/
axiom projectiveLoop : Path (A := ProjectivePlane) projectiveBase projectiveBase

/-- The key axiom: the loop squared equals reflexivity.
    In the paper this is called `cicl : α ∘ α = ρ`. -/
axiom projectiveLoopSquare :
  Path.trans projectiveLoop projectiveLoop = Path.refl projectiveBase

/-- Data required to eliminate from the projective plane into a target type `C`. -/
structure ProjectivePlaneRecData (C : Type v) where
  base : C
  loop : Path base base
  loopSquare : Path.trans loop loop = Path.refl base

/-- Projective plane eliminator (recursor). -/
axiom projectivePlaneRec {C : Type v} (data : ProjectivePlaneRecData C) :
  ProjectivePlane → C

/-- β-rule for `projectivePlaneRec` at the base point. -/
axiom projectivePlaneRec_base {C : Type v} (data : ProjectivePlaneRecData C) :
  projectivePlaneRec data projectiveBase = data.base

/-- β-rule for `projectivePlaneRec` on the fundamental loop. -/
axiom projectivePlaneRec_loop {C : Type v} (data : ProjectivePlaneRecData C) :
  Path.trans
    (Path.symm (Path.ofEq (projectivePlaneRec_base (C := C) data)))
    (Path.trans
      (Path.congrArg (projectivePlaneRec data) projectiveLoop)
      (Path.ofEq (projectivePlaneRec_base (C := C) data))) =
  data.loop

noncomputable section

open SimpleEquiv

/-! ## ℤ₂ as Bool

We represent ℤ₂ using `Bool` with XOR as addition:
- `false` = 0
- `true` = 1
- Addition is XOR (since 1+1=0 in ℤ₂)
-/

/-- XOR operation representing addition in ℤ₂. -/
abbrev z2Add (x y : Bool) : Bool := xor x y

@[simp] theorem z2Add_false_left (x : Bool) : z2Add false x = x := by
  simp [z2Add]

@[simp] theorem z2Add_false_right (x : Bool) : z2Add x false = x := by
  simp [z2Add]

@[simp] theorem z2Add_self (x : Bool) : z2Add x x = false := by
  cases x <;> rfl

@[simp] theorem z2Add_comm (x y : Bool) : z2Add x y = z2Add y x := by
  cases x <;> cases y <;> rfl

@[simp] theorem z2Add_assoc (x y z : Bool) :
    z2Add (z2Add x y) z = z2Add x (z2Add y z) := by
  cases x <;> cases y <;> cases z <;> rfl

/-! ## Code Family into Bool (ℤ₂)

The code family maps the projective plane to `Bool`. Transport along
the loop corresponds to negation (adding 1 in ℤ₂).
-/

/-- Equivalence on Bool that negates (adds 1 in ℤ₂). -/
def projectiveEquiv : SimpleEquiv Bool Bool where
  toFun := not
  invFun := not  -- Negation is its own inverse
  left_inv := by intro x; simp
  right_inv := by intro x; simp

/-- The equivalence squared is the identity (since ¬¬x = x). -/
theorem projectiveEquiv_square :
    SimpleEquiv.comp projectiveEquiv projectiveEquiv = SimpleEquiv.refl Bool := by
  apply SimpleEquiv.ext
  · intro x
    simp [SimpleEquiv.comp, projectiveEquiv, SimpleEquiv.refl]
  · intro x
    simp [SimpleEquiv.comp, projectiveEquiv, SimpleEquiv.refl]

section Univalence

variable [HasUnivalence.{0}]

/-- Code family data for the projective plane recursor. -/
def projectiveCodeData : ProjectivePlaneRecData (Type _) where
  base := Bool
  loop := Path.ua projectiveEquiv
  loopSquare := by
    rw [ua_trans, projectiveEquiv_square]
    exact ua_refl Bool

/-- The code family for the projective plane. -/
def projectiveCode : ProjectivePlane → Type _ :=
  projectivePlaneRec projectiveCodeData

/-- Code at the base point is Bool. -/
theorem projectiveCode_base : projectiveCode projectiveBase = Bool :=
  projectivePlaneRec_base projectiveCodeData

/-- The loop on the code family corresponds to univalence of negation. -/
theorem projectiveCode_loop_path :
    Path.trans (Path.symm (Path.ofEq projectiveCode_base))
        (Path.trans (Path.congrArg projectiveCode projectiveLoop)
          (Path.ofEq projectiveCode_base)) =
      Path.ua projectiveEquiv :=
  projectivePlaneRec_loop projectiveCodeData

/-- Coercion helper: cast from `projectiveCode projectiveBase` to `Bool`. -/
abbrev projectiveCodeToBool (x : projectiveCode projectiveBase) : Bool :=
  cast projectiveCode_base x

/-- Coercion helper: cast from `Bool` to `projectiveCode projectiveBase`. -/
abbrev boolToProjectiveCode (b : Bool) : projectiveCode projectiveBase :=
  cast projectiveCode_base.symm b

@[simp] theorem projectiveCodeToBool_boolToProjectiveCode (b : Bool) :
    projectiveCodeToBool (boolToProjectiveCode b) = b := by
  simp only [projectiveCodeToBool, boolToProjectiveCode]
  simp [cast_cast]

/-- Transport along the projective loop applies negation. -/
@[simp] theorem projectiveCode_transport_loop (b : Bool) :
    projectiveCodeToBool (Path.transport (A := ProjectivePlane) (D := projectiveCode)
      projectiveLoop (boolToProjectiveCode b)) = not b := by
  let p1 := Path.ofEq projectiveCode_base
  let q := Path.congrArg projectiveCode projectiveLoop
  let b_code := boolToProjectiveCode b
  have hEq : Path.trans (Path.symm p1) (Path.trans q p1) = Path.ua projectiveEquiv :=
    projectiveCode_loop_path
  -- Transport along trans decomposes
  have hAssoc :=
    Path.transport_trans (A := Type _) (D := fun X => X)
      (p := q) (q := p1) (x := b_code)
  -- Transport along congrArg is transport in the family
  have hMove :=
    (Path.transport_congrArg (A := ProjectivePlane) (D := projectiveCode)
      (p := projectiveLoop) (x := b_code))
  -- Combine to get the LHS
  have hLHS :
      Path.transport (A := Type _) (D := fun X => X)
        (Path.trans q p1) b_code
      = projectiveCodeToBool
          (Path.transport (A := ProjectivePlane) (D := projectiveCode) projectiveLoop b_code) := by
    have hSplit :
        Path.transport (A := Type _) (D := fun X => X)
          (Path.trans q p1) b_code
        = Path.transport (A := Type _) (D := fun X => X) p1
            (Path.transport (A := Type _) (D := fun X => X) q b_code) := by
      simpa using hAssoc
    have hInner :
        Path.transport (A := Type _) (D := fun X => X) q b_code
        = Path.transport (A := ProjectivePlane) (D := projectiveCode) projectiveLoop b_code := by
      exact hMove.symm
    simp only [projectiveCodeToBool]
    rw [hSplit, hInner]
    rfl
  -- Now compute the other side using univalence
  have hLeftStep :=
    Path.transport_trans (A := Type _) (D := fun X => X)
      (p := Path.symm p1) (q := Path.trans q p1)
      (x := Path.transport (A := Type _) (D := fun X => X) p1 b_code)
  have hLeftCancel :=
    _root_.congrArg
      (fun w =>
        Path.transport (A := Type _) (D := fun X => X)
          (Path.trans q p1) w)
      (Path.transport_symm_left (A := Type _) (D := fun X => X)
        (p := p1) (x := b_code))
  have hLeftSimp :
      Path.transport (A := Type _) (D := fun X => X)
        (Path.trans (Path.symm p1) (Path.trans q p1))
        (Path.transport (A := Type _) (D := fun X => X) p1 b_code)
      = Path.transport (A := Type _) (D := fun X => X)
          (Path.trans q p1) b_code := by
    exact hLeftStep.trans hLeftCancel
  have hComb :
      Path.transport (A := Type _) (D := fun X => X)
        (Path.trans q p1) b_code
      = Path.transport (A := Type _) (D := fun X => X)
          (Path.ua projectiveEquiv)
          (Path.transport (A := Type _) (D := fun X => X) p1 b_code) := by
    rw [← hLeftSimp]
    rw [hEq]
  have hBase :
      Path.transport (A := Type _) (D := fun X => X) p1 b_code = b := by
    simp only [p1, b_code, boolToProjectiveCode, Path.transport_ofEq]
    -- Goal: cast projectiveCode_base (cast projectiveCode_base.symm b) = b
    exact cast_cast projectiveCode_base.symm projectiveCode_base b
  have hRHS :
      Path.transport (A := Type _) (D := fun X => X)
        (Path.ua projectiveEquiv) b
      = not b := by
    simp [ua_beta, projectiveEquiv]
  rw [← hLHS, hComb, hBase, hRHS]

/-! ## Encoding and Decoding -/

/-- Encode a loop on the projective plane as an element of Bool (ℤ2).
    Uses the transport along the code family. -/
def projectiveEncodePath : Path projectiveBase projectiveBase → Bool :=
  fun p =>
    projectiveCodeToBool (Path.transport (A := ProjectivePlane) (D := projectiveCode) p
      (boolToProjectiveCode false))

/-- Encoding the reflexivity path gives false. -/
@[simp] theorem projectiveEncodePath_refl :
    projectiveEncodePath (Path.refl projectiveBase) = false := by
  simp only [projectiveEncodePath]
  simp only [Path.transport_refl]
  exact projectiveCodeToBool_boolToProjectiveCode false

/-- Encoding the fundamental loop gives true. -/
@[simp] theorem projectiveEncodePath_loop :
    projectiveEncodePath projectiveLoop = true := by
  simp only [projectiveEncodePath]
  simp only [projectiveCode_transport_loop]
  rfl

end Univalence

/-- Decode an element of Bool (ℤ₂) to a loop on the projective plane. -/
def projectiveDecode : Bool → Path projectiveBase projectiveBase
  | false => Path.refl projectiveBase
  | true => projectiveLoop

/-- Decode path helper (definitionally the same as `projectiveDecode`). -/
abbrev projectiveDecodePath : Bool → Path projectiveBase projectiveBase :=
  projectiveDecode

/-- Decode respects the group structure. -/
theorem projectiveDecode_add (x y : Bool) :
    RwEq (Path.trans (projectiveDecode x) (projectiveDecode y))
         (projectiveDecode (z2Add x y)) := by
  match x, y with
  | false, false =>
    simp only [projectiveDecode, z2Add]
    exact rweq_of_step (Step.trans_refl_left _)
  | false, true =>
    simp only [projectiveDecode, z2Add]
    exact rweq_of_step (Step.trans_refl_left _)
  | true, false =>
    simp only [projectiveDecode, z2Add]
    exact rweq_of_step (Step.trans_refl_right _)
  | true, true =>
    simp only [projectiveDecode, z2Add]
    exact rweq_of_eq projectiveLoopSquare

/-! ## Fundamental Group

All paths in RP² are rw-equal to either `refl` or `projectiveLoop`.
This gives π₁(RP²) ≃ ℤ₂.
-/

/-- The class of the trivial loop in the fundamental group. -/
def projectiveReflClass : LoopQuot ProjectivePlane projectiveBase :=
  LoopQuot.ofLoop (Path.refl projectiveBase)

/-- The class of the fundamental loop in the fundamental group. -/
def projectiveLoopClass : LoopQuot ProjectivePlane projectiveBase :=
  LoopQuot.ofLoop projectiveLoop

/-- The fundamental loop squared equals the identity in π₁(RP²). -/
theorem projectiveLoopClass_square :
    LoopQuot.comp projectiveLoopClass projectiveLoopClass = projectiveReflClass := by
  simp only [projectiveLoopClass, projectiveReflClass, LoopQuot.ofLoop, LoopQuot.comp,
             PathRwQuot.trans]
  apply Quot.sound
  exact rweq_of_eq projectiveLoopSquare

/-- Map from Bool (ℤ₂) to π₁(RP²). -/
def toPathZ2 : Bool → LoopQuot ProjectivePlane projectiveBase
  | false => projectiveReflClass
  | true => projectiveLoopClass

/-- Helper: toPathZ2 is definitionally LoopQuot.ofLoop ∘ projectiveDecodePath. -/
theorem toPathZ2_eq_ofLoop_decode (b : Bool) :
    toPathZ2 b = LoopQuot.ofLoop (projectiveDecodePath b) := by
  cases b <;> rfl

set_option maxHeartbeats 400000 in
/-- The map is a homomorphism (respects group operation). -/
theorem toPathZ2_add (x y : Bool) :
    LoopQuot.comp (toPathZ2 x) (toPathZ2 y) = toPathZ2 (z2Add x y) := by
  match x, y with
  | false, false => exact LoopQuot.id_comp projectiveReflClass
  | false, true => exact LoopQuot.id_comp projectiveLoopClass
  | true, false => exact LoopQuot.comp_id projectiveLoopClass
  | true, true => exact projectiveLoopClass_square

section Univalence

variable [HasUnivalence.{0}]

/-- RwEq paths have the same encoding. -/
theorem projectiveEncodePath_rweq {p q : Path projectiveBase projectiveBase}
    (h : RwEq p q) : projectiveEncodePath p = projectiveEncodePath q := by
  simp only [projectiveEncodePath]
  -- RwEq paths have the same toEq, so transports are equal
  have heq : p.toEq = q.toEq := rweq_toEq h
  rw [Path.transport_of_toEq_eq (h := heq)]

/-- Encode quotient paths in π₁(RP²) to Bool (ℤ₂). -/
def projectiveEncodeQuot : LoopQuot ProjectivePlane projectiveBase → Bool :=
  Quot.lift projectiveEncodePath (fun _ _ h => projectiveEncodePath_rweq h)

/-- The encoding and decoding are inverse (on ℤ2). -/
theorem projectiveEncode_decode (z : Bool) :
    projectiveEncodeQuot (toPathZ2 z) = z := by
  match z with
  | false =>
    simp only [toPathZ2, projectiveReflClass, projectiveEncodeQuot]
    simp only [LoopQuot.ofLoop]
    exact projectiveEncodePath_refl
  | true =>
    simp only [toPathZ2, projectiveLoopClass, projectiveEncodeQuot]
    simp only [LoopQuot.ofLoop]
    exact projectiveEncodePath_loop
/-- Equality-level helper: `decode ∘ encode = id` on propositional equalities.

    For any `e : projectiveBase = projectiveBase`, decoding the encoding
    gives back the same equality. This uses the fact that the only loops
    in RP² are refl and projectiveLoop (and projectiveLoop² = refl). -/
theorem projectiveDecodeEq_projectiveEncodeEq
    (e : projectiveBase = projectiveBase) :
    (projectiveDecodePath (projectiveEncodePath (Path.ofEq e))).toEq = e := by
  cases e
  rfl

/-- **RP² loop classification axiom**: Every loop on RP² is RwEq to
the decoded form of its ℤ₂ value. -/
class HasProjectiveLoopDecode : Prop where
  projectiveLoop_rweq_decode (p : Path.{u} projectiveBase projectiveBase) :
    RwEq.{u} p (projectiveDecodePath (projectiveEncodePath p))

/-- Every loop is RwEq to the decoded form of its ℤ₂ value. -/
theorem projectiveLoop_rweq_decode [h : HasProjectiveLoopDecode.{u}]
    (p : Path.{u} projectiveBase projectiveBase) :
    RwEq.{u} p (projectiveDecodePath (projectiveEncodePath p)) :=
  h.projectiveLoop_rweq_decode p

theorem projectiveDecode_encode [h : HasProjectiveLoopDecode.{u}]
    (x : LoopQuot ProjectivePlane.{u} projectiveBase) :
    toPathZ2 (projectiveEncodeQuot x) = x := by
  induction x using Quot.ind with
  | _ p =>
    simp only [projectiveEncodeQuot]
    rw [toPathZ2_eq_ofLoop_decode]
    exact Quot.sound (rweq_symm (projectiveLoop_rweq_decode (h := h) p))

/-- The fundamental group of the real projective plane is ℤ₂.

    This is Theorem 3.6 from the paper:
    "π₁(P²) ≃ ℤ₂"

    Here ℤ₂ is represented as `Bool` with XOR as addition.
-/
def projectivePiOneEquivZ2 [HasProjectiveLoopDecode.{u}] :
    SimpleEquiv (LoopQuot ProjectivePlane projectiveBase) Bool where
  toFun := projectiveEncodeQuot
  invFun := toPathZ2
  left_inv := projectiveDecode_encode
  right_inv := projectiveEncode_decode

end Univalence

end

end Path
end ComputationalPaths

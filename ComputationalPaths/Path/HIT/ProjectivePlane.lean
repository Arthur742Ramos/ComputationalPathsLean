/-
# The real projective plane as a higher-inductive type (axiomatic skeleton)

This module introduces `ProjectivePlane` (RP²) together with its base-point,
a fundamental loop `α`, and the key relation `α ⬝ α = refl`.

## Encode/decode note

Some HoTT-style developments model the RP² covering argument using a
univalence interface. In standard Lean, that interface is inconsistent
(see `docs/axioms.md`). As with `Circle.lean` and `Torus.lean`, we instead
axiomatise only the **loop classification data** needed to state `π₁(RP²) ≃ ℤ₂`,
packaged as `HasProjectiveLoopDecode`.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Rewrite.SimpleEquiv

set_option maxHeartbeats 1000000

namespace ComputationalPaths
namespace Path

universe u v

/-! ## HIT interface -/

/-- Abstract real projective plane type. -/
axiom ProjectivePlane : Type u

/-- Distinguished point on the projective plane. -/
axiom projectiveBase : ProjectivePlane

/-- Fundamental loop around the projective plane (`α`). -/
axiom projectiveLoop : Path (A := ProjectivePlane) projectiveBase projectiveBase

/-- The key axiom: the loop squared equals reflexivity (`α ⬝ α = ρ`). -/
axiom projectiveLoopSquare :
  Path.trans projectiveLoop projectiveLoop = Path.refl projectiveBase

noncomputable section

/-! ## Decoding -/

/-- Decode `Bool` as a loop: `false ↦ refl`, `true ↦ α`. -/
@[simp] def projectiveDecodePath : Bool → Path projectiveBase projectiveBase
  | false => Path.refl projectiveBase
  | true => projectiveLoop

/-! ## Loop encode/decode interface -/

/-- Encode/decode data for RP² loops. -/
class HasProjectiveLoopDecode : Type u where
  /-- `Bool`-valued invariant assigned to a loop. -/
  encodePath : Path projectiveBase projectiveBase → Bool
  /-- Encoding is invariant under rewrite equality. -/
  encodePath_rweq :
      ∀ {p q : Path projectiveBase projectiveBase}, RwEq p q → encodePath p = encodePath q
  /-- Encoding a decoded loop returns the boolean. -/
  encodePath_decode : ∀ b : Bool, encodePath (projectiveDecodePath b) = b
  /-- Every loop is rewrite-equal to the decoded form of its encoding. -/
  loop_rweq_decode :
      ∀ p : Path projectiveBase projectiveBase, RwEq p (projectiveDecodePath (encodePath p))

/-- Encode a raw loop as a boolean. -/
@[simp] def projectiveEncodePath [HasProjectiveLoopDecode]
    (p : Path projectiveBase projectiveBase) : Bool :=
  HasProjectiveLoopDecode.encodePath p

/-- Encoding respects rewrite equality. -/
@[simp] theorem projectiveEncodePath_rweq [h : HasProjectiveLoopDecode]
    {p q : Path projectiveBase projectiveBase} (hpq : RwEq p q) :
    projectiveEncodePath p = projectiveEncodePath q :=
  h.encodePath_rweq hpq

/-- Encoding after decoding is the identity on `Bool`. -/
@[simp] theorem projectiveEncodePath_decode [h : HasProjectiveLoopDecode] (b : Bool) :
    projectiveEncodePath (projectiveDecodePath b) = b :=
  h.encodePath_decode b

/-- Every loop is `RwEq` to the decoded form of its encoding. -/
theorem projectiveLoop_rweq_decode [h : HasProjectiveLoopDecode]
    (p : Path projectiveBase projectiveBase) :
    RwEq p (projectiveDecodePath (projectiveEncodePath p)) :=
  h.loop_rweq_decode p

/-! ## Quotient-level encode/decode and π₁ equivalence -/

/-- Fundamental group π₁(RP², base) as rewrite classes of loops. -/
abbrev projectivePiOne : Type u :=
  PiOne ProjectivePlane projectiveBase

/-- Encode map `π₁(RP²) → Bool`. -/
@[simp] def projectiveEncode [h : HasProjectiveLoopDecode] : projectivePiOne → Bool :=
  Quot.lift (fun p : Path projectiveBase projectiveBase => projectiveEncodePath p)
    (by
      intro p q hpq
      exact projectiveEncodePath_rweq (h := h) hpq)

/-- Decode map `Bool → π₁(RP²)`. -/
@[simp] def projectiveDecode : Bool → projectivePiOne :=
  fun b =>
    LoopQuot.ofLoop (A := ProjectivePlane) (a := projectiveBase) (projectiveDecodePath b)

/-- Encoding after decoding is the identity on `Bool`. -/
@[simp] theorem projectiveEncode_projectiveDecode [HasProjectiveLoopDecode] (b : Bool) :
    projectiveEncode (projectiveDecode b) = b := by
  change projectiveEncodePath (projectiveDecodePath b) = b
  exact projectiveEncodePath_decode (b := b)

/-- Decoding after encoding is the identity on `π₁(RP²)`. -/
theorem projectiveDecode_projectiveEncode [HasProjectiveLoopDecode]
    (x : projectivePiOne) :
    projectiveDecode (projectiveEncode x) = x := by
  refine Quot.inductionOn x ?_
  intro p
  have hrweq : RwEq p (projectiveDecodePath (projectiveEncodePath p)) :=
    projectiveLoop_rweq_decode (p := p)
  exact Quot.sound (rweq_symm hrweq)

/-- Fundamental group of RP² is equivalent to `ℤ₂`, represented as `Bool`. -/
noncomputable def projectivePiOneEquivZ2_ofLoopDecode [HasProjectiveLoopDecode] :
    SimpleEquiv projectivePiOne Bool where
  toFun := projectiveEncode
  invFun := projectiveDecode
  left_inv := projectiveDecode_projectiveEncode
  right_inv := projectiveEncode_projectiveDecode

end

end Path
end ComputationalPaths

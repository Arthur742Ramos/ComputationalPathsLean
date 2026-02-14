/-
# Wedge SVK Typeclass Instances for the Figure-Eight (Circle ∨ Circle)

This module provides concrete, sorry-free instances of the Wedge SVK
typeclasses for the figure-eight space `Wedge Circle Circle circleBase circleBase`.

## Results

### Proved (sorry-free, no axioms)

1. `instHasWedgeSVKEncodeQuot_Circle` — encode map (const nil)
2. `instHasWedgeSVKDecodeEncode_Circle` — decode ∘ encode = id (π₁ trivial)

### Proved Impossible (sorry-free refutation)

3. `not_hasWedgeSVKEncodeDecode_Circle` — proves `¬ HasWedgeSVKEncodeDecode` for
   ANY `HasWedgeSVKEncodeQuot` instance. The encode_decode round-trip law requires
   `encodeQuot (pushoutDecode w) = w` for all words `w`, but since `π₁(Wedge)` is
   trivial (one element), `pushoutDecode` maps all words to the same π₁ element,
   forcing `encodeQuot` to return the same word for all inputs. Since
   `FreeProductWord` has structurally distinct elements (nil ≠ consLeft id nil),
   this is contradictory.

## Mathematical Explanation

`Circle` (= `CircleCompPath`) is a single-constructor inductive type (`base`),
making it a `Subsingleton`. The wedge `Wedge Circle Circle circleBase circleBase`
is also a `Subsingleton` (all points identified: `inl base = inr base` via glue).

For subsingletons, `π₁` is trivial: all loops are `RwEq` to `refl` because
every `Core.Step` in a loop has `src = tgt` (by `Subsingleton.elim`), so each
step is `stepChain rfl ≈ refl` (by `rweq_ofEq_rfl_refl`).

The `HasWedgeSVKEncodeDecode` class requires `pushoutDecode` to be injective
on raw words (not just up to amalgamation). When `π₁(A)` and `π₁(B)` are
both trivial, `pushoutDecode` maps all words to the identity, so it is NOT
injective. This makes the class unsatisfiable.

Note: the downstream `HasWedgeSVKDecodeBijective` (and hence `figureEightPiOneEquiv`)
requires all 3 instances, and is therefore also unsatisfiable for the Circle wedge.
These downstream results take it as an uninstantiated assumption `[HasWedgeSVKDecodeBijective ...]`.

## See Also

- `PushoutSVKInstances.lean`: provides 4 concrete instances for the PUnit' wedge
  (using `FullAmalgEquiv`, which correctly handles free group reduction)
- `PushoutPaths.lean`: defines all SVK typeclasses and generic derivations
-/

import ComputationalPaths.Path.CompPath.FigureEight
import ComputationalPaths.Path.CompPath.PushoutPaths
import ComputationalPaths.Path.Homotopy.Sets

namespace ComputationalPaths
namespace Path
namespace CompPath

open Pushout WedgeSVKInstances

set_option maxHeartbeats 1600000

universe u

/-! ## Infrastructure: Circle and Wedge Triviality -/

/-- `Circle` (= `CircleCompPath`) has a single constructor `base`, so it is a subsingleton. -/
instance circleSubsingleton : Subsingleton Circle.{u} where
  allEq a b := by cases a; cases b; rfl

/-- The wedge `Circle ∨ Circle` is a subsingleton: all points are identified.
`inl base` and `inr base` are the only constructors, and `glue` identifies them. -/
instance wedgeCircleSubsingleton :
    Subsingleton (Wedge Circle.{u} Circle.{u} circleBase circleBase) where
  allEq x y := by
    refine Quot.inductionOn x ?_
    refine fun s => Quot.inductionOn y ?_
    intro t
    match s, t with
    | .inl a, .inl a' => cases a; cases a'; rfl
    | .inl a, .inr b' =>
        cases a; cases b'
        exact Quot.sound (PushoutCompPathRel.glue PUnit'.unit)
    | .inr b, .inl a' =>
        cases b; cases a'
        exact (Quot.sound (PushoutCompPathRel.glue PUnit'.unit)).symm
    | .inr b, .inr b' => cases b; cases b'; rfl

/-- Short name for the Circle wedge type. -/
private abbrev WC := Wedge Circle.{u} Circle.{u} circleBase circleBase

/-- Every element of `π₁(Wedge Circle Circle, base)` equals the identity.
Since the wedge is a subsingleton, it is an h-set, so all loops are RwEq to refl. -/
private theorem wedgeCircle_piOne_trivial
    (α : π₁(WC.{u}, Wedge.basepoint)) :
    α = Quot.mk _ (Path.refl Wedge.basepoint) :=
  pi1_trivial_of_subsingleton WC Wedge.basepoint α

/-- Every element of `π₁(Circle, circleBase)` equals the identity. -/
private theorem circle_piOne_trivial
    (α : π₁(Circle.{u}, circleBase)) :
    α = Quot.mk _ (Path.refl circleBase) :=
  pi1_trivial_of_subsingleton Circle circleBase α

/-! ## Instance 1: HasWedgeSVKEncodeQuot

Encode map: every π₁ element maps to the empty word `nil`.
Since `π₁(Wedge Circle Circle, base)` is trivial (one element), there is
only one element to encode, and `nil` is the natural choice. -/

noncomputable instance instHasWedgeSVKEncodeQuot_Circle :
    HasWedgeSVKEncodeQuot Circle.{u} Circle.{u} circleBase circleBase where
  encodeQuot := fun _ => .nil

/-! ## Instance 2: HasWedgeSVKDecodeEncode

Round-trip: `pushoutDecode (encodeQuot (Quot.mk _ p)) = Quot.mk _ p`.

Since `encodeQuot` always returns `nil`, we have:
  `pushoutDecode nil = Quot.mk _ (Path.refl base)` (the identity in π₁)

And `Quot.mk _ (Path.refl base) = Quot.mk _ p` because `π₁` is trivial
(all loops at the basepoint are RwEq to refl). -/

instance instHasWedgeSVKDecodeEncode_Circle :
    HasWedgeSVKDecodeEncode Circle.{u} Circle.{u} circleBase circleBase where
  decode_encode := by
    intro p
    -- The LHS unfolds to: pushoutDecode ... nil = Quot.mk _ (Path.refl base)
    -- The RHS is: Quot.mk _ p
    -- These are equal by π₁ triviality.
    exact (wedgeCircle_piOne_trivial (Quot.mk _ p)).symm

/-! ## Instance 3: HasWedgeSVKEncodeDecode — Proved Impossible

We prove that `HasWedgeSVKEncodeDecode Circle Circle circleBase circleBase`
is false for ANY choice of `HasWedgeSVKEncodeQuot` instance.

The proof constructs two distinct words (`nil` and `consLeft id nil`) that
map to the same π₁ element under `pushoutDecode`. Since `encodeQuot` is a
function, it must return the same word for both, but `encode_decode` requires
it to return `nil` for the first and `consLeft id nil` for the second. -/

/-- For ANY `HasWedgeSVKEncodeQuot` instance on the Circle wedge,
`HasWedgeSVKEncodeDecode` is false.

This shows the class is intrinsically unsatisfiable for Circle ∨ Circle,
regardless of how the encode function is defined. -/
theorem not_hasWedgeSVKEncodeDecode_Circle
    (inst : HasWedgeSVKEncodeQuot Circle.{u} Circle.{u} circleBase circleBase) :
    ¬ @HasWedgeSVKEncodeDecode Circle.{u} Circle.{u} circleBase circleBase inst := by
  intro ⟨h⟩
  -- Apply encode_decode to nil and to consLeft id nil
  have h_nil := h FreeProductWord.nil
  have h_cons := h (FreeProductWord.consLeft (Quot.mk _ (Path.refl circleBase)) .nil)
  -- pushoutDecode maps both words to the same π₁ element (π₁ is trivial)
  have eq_decode :
      pushoutDecode (A := Circle.{u}) (B := Circle.{u}) (C := PUnit')
        (f := fun _ => circleBase) (g := fun _ => circleBase) PUnit'.unit
        FreeProductWord.nil =
      pushoutDecode (A := Circle.{u}) (B := Circle.{u}) (C := PUnit')
        (f := fun _ => circleBase) (g := fun _ => circleBase) PUnit'.unit
        (.consLeft (Quot.mk _ (Path.refl circleBase)) .nil) := by
    have t1 := wedgeCircle_piOne_trivial
          (pushoutDecode (A := Circle.{u}) (B := Circle.{u}) (C := PUnit')
            (f := fun _ => circleBase) (g := fun _ => circleBase) PUnit'.unit
            FreeProductWord.nil)
    have t2 := wedgeCircle_piOne_trivial
          (pushoutDecode (A := Circle.{u}) (B := Circle.{u}) (C := PUnit')
            (f := fun _ => circleBase) (g := fun _ => circleBase) PUnit'.unit
            (.consLeft (Quot.mk _ (Path.refl circleBase)) .nil))
    exact t1.symm.trans t2
  -- encodeQuot is a function: same input gives same output
  have enc_eq := _root_.congrArg
    (@wedgeEncodeQuotPrim Circle.{u} Circle.{u} circleBase circleBase inst) eq_decode
  -- From h_nil: LHS = nil. From h_cons: RHS = consLeft id nil.
  rw [h_nil, h_cons] at enc_eq
  -- nil = consLeft id nil is absurd (distinct constructors)
  exact FreeProductWord.noConfusion enc_eq

/-! ## Corollary: HasWedgeSVKEncodeData is also impossible

Since `HasWedgeSVKEncodeData` bundles both `HasWedgeSVKDecodeEncode` and
`HasWedgeSVKEncodeDecode`, and the latter is impossible, the bundle is also impossible. -/

/-- `HasWedgeSVKEncodeData Circle Circle circleBase circleBase` is false. -/
theorem not_hasWedgeSVKEncodeData_Circle :
    HasWedgeSVKEncodeData Circle.{u} Circle.{u} circleBase circleBase → False := by
  intro inst
  -- inst.encode_decode says: for all w,
  --   inst.toHasWedgeSVKEncodeQuot.encodeQuot (pushoutDecode w) = w
  -- Taking w = nil and w = consLeft id nil:
  have h_nil := inst.encode_decode FreeProductWord.nil
  have h_cons := inst.encode_decode
    (FreeProductWord.consLeft (Quot.mk _ (Path.refl circleBase)) .nil)
  -- Both pushoutDecode results are equal (π₁ is trivial)
  have eq_decode :
      pushoutDecode (A := Circle.{u}) (B := Circle.{u}) (C := PUnit')
        (f := fun _ => circleBase) (g := fun _ => circleBase) PUnit'.unit
        FreeProductWord.nil =
      pushoutDecode (A := Circle.{u}) (B := Circle.{u}) (C := PUnit')
        (f := fun _ => circleBase) (g := fun _ => circleBase) PUnit'.unit
        (.consLeft (Quot.mk _ (Path.refl circleBase)) .nil) := by
    have t1 := wedgeCircle_piOne_trivial
          (pushoutDecode (A := Circle.{u}) (B := Circle.{u}) (C := PUnit')
            (f := fun _ => circleBase) (g := fun _ => circleBase) PUnit'.unit
            FreeProductWord.nil)
    have t2 := wedgeCircle_piOne_trivial
          (pushoutDecode (A := Circle.{u}) (B := Circle.{u}) (C := PUnit')
            (f := fun _ => circleBase) (g := fun _ => circleBase) PUnit'.unit
            (.consLeft (Quot.mk _ (Path.refl circleBase)) .nil))
    exact t1.symm.trans t2
  -- encodeQuot is a function: same input → same output
  have enc_eq := _root_.congrArg inst.toHasWedgeSVKEncodeQuot.encodeQuot eq_decode
  -- From h_nil and h_cons, we get nil = consLeft id nil
  rw [h_nil, h_cons] at enc_eq
  exact FreeProductWord.noConfusion enc_eq

/-! ## Corollary: HasWedgeSVKDecodeBijective is also impossible

The decode map `wedgeFreeProductDecode` is not injective for the Circle wedge:
`nil` and `consLeft id nil` both decode to the identity in π₁. -/

/-- The wedge decode map is not injective for Circle ∨ Circle. -/
theorem not_wedgeDecode_injective_Circle :
    ¬ Function.Injective
      (wedgeFreeProductDecode (A := Circle.{u}) (B := Circle.{u}) circleBase circleBase) := by
  intro hinj
  -- wedgeFreeProductDecode nil = wedgeFreeProductDecode (consLeft id nil) (π₁ trivial)
  have h_eq : wedgeFreeProductDecode circleBase circleBase FreeProductWord.nil =
      wedgeFreeProductDecode circleBase circleBase
        (.consLeft (Quot.mk _ (Path.refl circleBase)) .nil) := by
    simp only [wedgeFreeProductDecode]
    have t1 := wedgeCircle_piOne_trivial
          (pushoutDecode (A := Circle.{u}) (B := Circle.{u}) (C := PUnit')
            (f := fun _ => circleBase) (g := fun _ => circleBase) PUnit'.unit
            FreeProductWord.nil)
    have t2 := wedgeCircle_piOne_trivial
          (pushoutDecode (A := Circle.{u}) (B := Circle.{u}) (C := PUnit')
            (f := fun _ => circleBase) (g := fun _ => circleBase) PUnit'.unit
            (.consLeft (Quot.mk _ (Path.refl circleBase)) .nil))
    exact t1.symm.trans t2
  -- Injectivity would give nil = consLeft id nil
  have h_word_eq := hinj h_eq
  exact FreeProductWord.noConfusion h_word_eq

/-- `HasWedgeSVKDecodeBijective Circle Circle circleBase circleBase` is false. -/
theorem not_hasWedgeSVKDecodeBijective_Circle :
    ¬ HasWedgeSVKDecodeBijective Circle.{u} Circle.{u} circleBase circleBase := by
  intro ⟨hinj, _⟩
  exact not_wedgeDecode_injective_Circle hinj

end CompPath
end Path
end ComputationalPaths

/-
# π₁(T²) ≃ ℤ × ℤ

This module packages the torus π₁ computation as a `PathSimpleEquiv`
between `π₁(T²)` and `ℤ × ℤ`.

## Key Results

- `torusPiOneEncode_torusDecode`: encoding after decoding is the identity (as a `Path`).
- `torusDecode_torusPiOneEncode`: decoding after encoding is the identity (as a `Path`).
- `torusPiOneEquivIntProd`: `π₁(T²)` is `PathSimpleEquiv` to `ℤ × ℤ`.
-/

import ComputationalPaths.Path.CompPath.Torus
import ComputationalPaths.Path.CompPath.CircleCompPath
import ComputationalPaths.Path.Rewrite.Normalization
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Rewrite.SimpleEquiv

set_option maxHeartbeats 1000000

namespace ComputationalPaths
namespace Path
open CompPath
open SimpleEquiv

universe u v

/-- Path-based equivalence structure (inverse laws witnessed by `Path`). -/
structure PathSimpleEquiv (α : Type u) (β : Type v) where
  /-- Forward map. -/
  toFun : α → β
  /-- Inverse map. -/
  invFun : β → α
  /-- Inverse after forward map is the identity, as a `Path`. -/
  left_inv : ∀ x : α, Path (invFun (toFun x)) x
  /-- Forward after inverse map is the identity, as a `Path`. -/
  right_inv : ∀ y : β, Path (toFun (invFun y)) y

/-- Convert a `PathSimpleEquiv` into a `SimpleEquiv`. -/
noncomputable def pathSimpleEquivToSimpleEquiv {α : Type u} {β : Type v}
    (e : PathSimpleEquiv α β) : SimpleEquiv α β :=
  { toFun := e.toFun
    invFun := e.invFun
    left_inv := fun x => (e.left_inv x).toEq
    right_inv := fun y => (e.right_inv y).toEq }

/-- A discharge-friendly interface for `π₁(T²) ≃ ℤ × ℤ`.

Unlike `HasTorusLoopDecode`, this class only talks about the loop *quotient*
(`π₁`) rather than raw loop normal forms.  Downstream developments that only
need the fundamental group can depend on this weaker hypothesis.
-/
class HasTorusPiOneEncode : Type u where
  /-- Winding-number map `π₁(T²) → ℤ × ℤ`. -/
  encode : torusPiOne → Int × Int
  /-- Encoding after decoding is the identity on `ℤ × ℤ`. -/
  encode_torusDecode : ∀ z : Int × Int, Path (encode (torusDecode z)) z
  /-- Decoding after encoding is the identity on `π₁(T²)`. -/
  torusDecode_encode : ∀ x : torusPiOne, Path (torusDecode (encode x)) x

/-- Winding-number map specialised from `HasTorusPiOneEncode`. -/
@[simp] noncomputable def torusPiOneEncode [HasTorusPiOneEncode] : torusPiOne → Int × Int :=
  HasTorusPiOneEncode.encode

noncomputable def torusPiOneEncode_torusDecode [HasTorusPiOneEncode] (z : Int × Int) :
    Path (torusPiOneEncode (torusDecode z)) z :=
  HasTorusPiOneEncode.encode_torusDecode z

noncomputable def torusDecode_torusPiOneEncode [HasTorusPiOneEncode] (x : torusPiOne) :
    Path (torusDecode (torusPiOneEncode x)) x :=
  HasTorusPiOneEncode.torusDecode_encode x

@[simp] theorem torusPiOneEncode_torusDecode_eq [HasTorusPiOneEncode] (z : Int × Int) :
    torusPiOneEncode (torusDecode z) = z :=
  (torusPiOneEncode_torusDecode (z := z)).toEq

@[simp] theorem torusDecode_torusPiOneEncode_eq [HasTorusPiOneEncode] (x : torusPiOne) :
    torusDecode (torusPiOneEncode x) = x :=
  (torusDecode_torusPiOneEncode (x := x)).toEq

/-!
## Canonical instance from the circle π₁ computation

Because `Torus` is defined as `Circle × Circle`, we can construct the torus
π₁ encode/decode data from:
- the product fundamental group equivalence, and
- the circle π₁ encode/decode interface (`HasCirclePiOneEncode`).
-/
noncomputable instance instHasTorusPiOneEncode_ofCircle :
    HasTorusPiOneEncode.{u} where
  encode := fun x =>
    (circlePiOneEncode x.1, circlePiOneEncode x.2)
  encode_torusDecode := by
    intro z
    cases z with
    | mk z1 z2 =>
        exact
          Path.prodMk
            (Path.stepChain (circlePiOneEncode_circleDecode z1))
            (Path.stepChain (circlePiOneEncode_circleDecode z2))
  torusDecode_encode := by
    intro x
    cases x with
    | mk x1 x2 =>
        exact
          Path.prodMk
            (Path.stepChain (circleDecode_circlePiOneEncode x1))
            (Path.stepChain (circleDecode_circlePiOneEncode x2))

/-
## Loop-space commutator
-/

/-- The torus commutator loop `aba⁻¹b⁻¹` built from `torusLoop1` and `torusLoop2`. -/
noncomputable def torusCommutator : torusLoopSpace :=
  Path.trans
    (Path.trans (Path.trans torusLoop1 torusLoop2) (Path.symm torusLoop1))
    (Path.symm torusLoop2)

private noncomputable def commutator_refl_right_rw {A : Type u} {a : A}
    (p : LoopSpace A a) :
    Rw
      (Path.trans (Path.trans (Path.trans p (Path.refl a)) (Path.symm p))
        (Path.symm (Path.refl a)))
      (Path.refl a) := by
  -- (p ⬝ refl) ⬝ p⁻¹ ⬝ refl⁻¹  →  (p ⬝ refl) ⬝ p⁻¹ ⬝ refl  (symm_refl on tail)
  -- →  (p ⬝ refl) ⬝ p⁻¹         (trans_refl_right)
  -- →  p ⬝ p⁻¹                   (trans_congr_left . trans_refl_right)
  -- →  refl                       (trans_symm)
  apply rw_trans
  · exact rw_of_step (Step.trans_congr_right
      (Path.trans (Path.trans p (Path.refl a)) (Path.symm p))
      (Step.symm_refl a))
  apply rw_trans
  · exact rw_of_step (Step.trans_refl_right _)
  apply rw_trans
  · exact rw_of_step (Step.trans_congr_left (Path.symm p) (Step.trans_refl_right p))
  exact rw_of_step (Step.trans_symm p)

private noncomputable def commutator_refl_left_rw {A : Type u} {a : A}
    (p : LoopSpace A a) :
    Rw
      (Path.trans (Path.trans (Path.trans (Path.refl a) p) (Path.symm (Path.refl a)))
        (Path.symm p))
      (Path.refl a) := by
  -- (refl ⬝ p) ⬝ refl⁻¹ ⬝ p⁻¹  →  (refl ⬝ p) ⬝ refl ⬝ p⁻¹  (symm_refl in inner)
  -- →  (refl ⬝ p) ⬝ p⁻¹         (trans_refl_right in inner, then congr)
  -- →  p ⬝ p⁻¹                   (trans_refl_left)
  -- →  refl                       (trans_symm)
  apply rw_trans
  · exact rw_of_step (Step.trans_congr_left (Path.symm p)
      (Step.trans_congr_right (Path.trans (Path.refl a) p) (Step.symm_refl a)))
  apply rw_trans
  · exact rw_of_step (Step.trans_congr_left (Path.symm p)
      (Step.trans_refl_right (Path.trans (Path.refl a) p)))
  apply rw_trans
  · exact rw_of_step (Step.trans_congr_left (Path.symm p)
      (Step.trans_refl_left p))
  exact rw_of_step (Step.trans_symm p)

private noncomputable def commutator_refl_right_rweq {A : Type u} {a : A}
    (p : LoopSpace A a) :
    RwEq
      (Path.trans (Path.trans (Path.trans p (Path.refl a)) (Path.symm p))
        (Path.symm (Path.refl a)))
      (Path.refl a) :=
  rweq_of_rw (commutator_refl_right_rw (A := A) (a := a) p)

private noncomputable def commutator_refl_left_rweq {A : Type u} {a : A}
    (p : LoopSpace A a) :
    RwEq
      (Path.trans (Path.trans (Path.trans (Path.refl a) p) (Path.symm (Path.refl a)))
        (Path.symm p))
      (Path.refl a) :=
  rweq_of_rw (commutator_refl_left_rw (A := A) (a := a) p)

/-! ### Component-wise commutator reduction -/

private noncomputable def torusCommutator_fst_refl :
    RwEq (Path.fst torusCommutator) (Path.refl circleBase) := by
  -- fst distributes over trans/symm (congrArg_trans, congrArg_symm are @[simp])
  -- then fst(prodMk p q) ≈ p (rweq_fst_prodMk)
  -- finally the commutator with refl reduces to refl
  unfold torusCommutator
  simp only [Path.fst, congrArg_trans, congrArg_symm]
  apply rweq_trans
  · apply rweq_trans_congr
    · apply rweq_trans_congr
      · apply rweq_trans_congr
        · exact rweq_fst_prodMk circleLoop (Path.refl circleBase)
        · exact rweq_fst_prodMk (Path.refl circleBase) circleLoop
      · exact rweq_symm_congr (rweq_fst_prodMk circleLoop (Path.refl circleBase))
    · exact rweq_symm_congr (rweq_fst_prodMk (Path.refl circleBase) circleLoop)
  · exact commutator_refl_right_rweq circleLoop

private noncomputable def torusCommutator_snd_refl :
    RwEq (Path.snd torusCommutator) (Path.refl circleBase) := by
  unfold torusCommutator
  simp only [Path.snd, congrArg_trans, congrArg_symm]
  apply rweq_trans
  · apply rweq_trans_congr
    · apply rweq_trans_congr
      · apply rweq_trans_congr
        · exact rweq_snd_prodMk circleLoop (Path.refl circleBase)
        · exact rweq_snd_prodMk (Path.refl circleBase) circleLoop
      · exact rweq_symm_congr (rweq_snd_prodMk circleLoop (Path.refl circleBase))
    · exact rweq_symm_congr (rweq_snd_prodMk (Path.refl circleBase) circleLoop)
  · exact commutator_refl_left_rweq circleLoop

/-- The torus commutator is rewrite-equivalent to the reflexive loop. -/
noncomputable def torusCommutator_rweq_refl :
    RwEq torusCommutator (Path.refl torusBase) := by
  have h_eta : RwEq torusCommutator
      (Path.prodMk (Path.fst torusCommutator) (Path.snd torusCommutator)) :=
    rweq_symm (rweq_prod_eta torusCommutator)
  have h_prod : RwEq
      (Path.prodMk (Path.fst torusCommutator) (Path.snd torusCommutator))
      (Path.prodMk (Path.refl circleBase) (Path.refl circleBase)) :=
    rweq_map2_of_rweq (f := Prod.mk) torusCommutator_fst_refl torusCommutator_snd_refl
  have h_refl : Path.prodMk (Path.refl circleBase) (Path.refl circleBase) =
      Path.refl torusBase :=
    Path.prodMk_refl_refl circleBase circleBase
  exact rweq_trans h_eta (rweq_trans h_prod (rweq_of_eq h_refl))

/-- Two partial commutator reductions (canceling either component first). -/
noncomputable def torusCommutatorReduceFst : torusLoopSpace :=
  Path.prodMk (Path.refl circleBase) (Path.snd torusCommutator)

noncomputable def torusCommutatorReduceSnd : torusLoopSpace :=
  Path.prodMk (Path.fst torusCommutator) (Path.refl circleBase)

/-- Two partial reductions are rewrite-equivalent. -/
noncomputable def torusCommutator_reduction_equiv :
    RwEq torusCommutatorReduceFst torusCommutatorReduceSnd := by
  have h_left : RwEq torusCommutatorReduceFst
      (Path.prodMk (Path.refl circleBase) (Path.refl circleBase)) :=
    rweq_map2_of_rweq (f := Prod.mk)
      (rweq_refl (Path.refl circleBase)) torusCommutator_snd_refl
  have h_right : RwEq torusCommutatorReduceSnd
      (Path.prodMk (Path.refl circleBase) (Path.refl circleBase)) :=
    rweq_map2_of_rweq (f := Prod.mk)
      torusCommutator_fst_refl (rweq_refl (Path.refl circleBase))
  exact rweq_trans h_left (rweq_symm h_right)

/-! ### Step-level commutator reduction sequence

We record the full reduction of `aba⁻¹b⁻¹ = refl` as a sequence of
RwEq steps on the product components. -/

/-- First RwEq reduction: cancel the first-component commutator
`a refl a⁻¹ refl⁻¹ → refl` via `commutator_refl_right_rweq`. -/
noncomputable def torusCommutator_rweq_step1 :
    RwEq (Path.fst torusCommutator) (Path.refl circleBase) :=
  torusCommutator_fst_refl

/-- Second RwEq reduction: cancel the second-component commutator
`refl b refl⁻¹ b⁻¹ → refl` via `commutator_refl_left_rweq`. -/
noncomputable def torusCommutator_rweq_step2 :
    RwEq (Path.snd torusCommutator) (Path.refl circleBase) :=
  torusCommutator_snd_refl

/-- Combined: both projections reduce, so the product reduces to refl.
This demonstrates the encode/decode proof that `aba⁻¹b⁻¹ = refl`
on the torus, witnessing commutativity of π₁(T²). -/
noncomputable def torusCommutator_rweq_refl_via_steps :
    RwEq torusCommutator (Path.refl torusBase) := by
  -- Step 1: η-expand the commutator to prodMk(fst, snd)
  have h_eta := rweq_symm (rweq_prod_eta torusCommutator)
  -- Step 2: reduce each component to refl via Step sequences
  have h_prod := rweq_map2_of_rweq (f := Prod.mk)
    torusCommutator_rweq_step1 torusCommutator_rweq_step2
  -- Step 3: collapse prodMk(refl, refl) = refl
  have h_refl : Path.prodMk (Path.refl circleBase) (Path.refl circleBase) =
      Path.refl torusBase := Path.prodMk_refl_refl circleBase circleBase
  exact rweq_trans h_eta (rweq_trans h_prod (rweq_of_eq h_refl))



/-- Fundamental group of the torus is equivalent to `ℤ × ℤ`. -/
noncomputable def torusPiOneEquivIntProd [HasTorusPiOneEncode] :
    PathSimpleEquiv torusPiOne (Int × Int) where
  toFun := torusPiOneEncode
  invFun := torusDecode
  left_inv := by
    intro x
    simpa using (torusDecode_torusPiOneEncode (x := x))
  right_inv := by
    intro z
    simpa using (torusPiOneEncode_torusDecode (z := z))

/-- Step-normalized path witnesses for the torus π₁ equivalence. -/
noncomputable def torusPiOneEquivIntProdNormalized [HasTorusPiOneEncode] :
    PathSimpleEquiv torusPiOne (Int × Int) where
  toFun := torusPiOneEncode
  invFun := torusDecode
  left_inv := by
    intro x
    exact
      normalize (A := torusPiOne)
        (a := torusDecode (torusPiOneEncode x)) (b := x)
        (torusDecode_torusPiOneEncode (x := x))
  right_inv := by
    intro z
    exact
      normalize (A := Int × Int)
        (a := torusPiOneEncode (torusDecode z)) (b := z)
        (torusPiOneEncode_torusDecode (z := z))

/-- Eq-based equivalence for downstream developments. -/
noncomputable def torusPiOneEquivIntProdSimple [HasTorusPiOneEncode] :
    SimpleEquiv torusPiOne (Int × Int) :=
  pathSimpleEquivToSimpleEquiv torusPiOneEquivIntProd

end Path
end ComputationalPaths

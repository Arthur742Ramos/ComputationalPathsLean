import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.HIT.Pushout
import ComputationalPaths.Path.Homotopy.FundamentalGroupoid
import ComputationalPaths.Path.CompPath.PushoutPaths
import ComputationalPaths.Path.CompPath.CircleCompPath
namespace ComputationalPaths.Path.Homotopy

open ComputationalPaths
open ComputationalPaths.Path
open ComputationalPaths.Path.CompPath

universe u

section PushoutDecomposition

variable {U : Type u} {V : Type u} {I : Type u}
variable {iU : I → U} {iV : I → V}

/-- A loop in the right piece, transported back to the left basepoint through glue. -/
noncomputable def inVSegment (i0 : I) (q : Path (iV i0) (iV i0)) :
    Path (Pushout.inl (iU i0) : Pushout U V I iU iV) (Pushout.inl (iU i0)) :=
  Path.trans (Pushout.glue (A := U) (B := V) (C := I) (f := iU) (g := iV) i0)
    (Path.trans
      (Pushout.inrPath (A := U) (B := V) (C := I) (f := iU) (g := iV) q)
      (Path.symm (Pushout.glue (A := U) (B := V) (C := I) (f := iU) (g := iV) i0)))

inductive Side : Type where
  | left
  | right
deriving DecidableEq, Repr

/-- Alternating words of loop segments from `U` and `V`. -/
inductive AlternatingWord (i0 : I) : Side → Type u where
  | nil (s : Side) : AlternatingWord i0 s
  | consLeft (p : Path (iU i0) (iU i0))
      (rest : AlternatingWord i0 Side.right) :
      AlternatingWord i0 Side.left
  | consRight (q : Path (iV i0) (iV i0))
      (rest : AlternatingWord i0 Side.left) :
      AlternatingWord i0 Side.right

/-- Decode an alternating `U/V` word into an explicit `Path.trans` chain in the pushout. -/
noncomputable def decodeAlternating (i0 : I) :
    {s : Side} → AlternatingWord (iU := iU) (iV := iV) i0 s →
      Path (Pushout.inl (iU i0) : Pushout U V I iU iV) (Pushout.inl (iU i0))
  | _, .nil _ => Path.refl _
  | _, .consLeft p rest =>
      Path.trans
        (Pushout.inlPath (A := U) (B := V) (C := I) (f := iU) (g := iV) p)
        (decodeAlternating i0 rest)
  | _, .consRight q rest =>
      Path.trans
        (inVSegment (U := U) (V := V) (I := I) (iU := iU) (iV := iV) i0 q)
        (decodeAlternating i0 rest)

/-- Syntactic witness that a pushout loop is decomposed into alternating `U/V` segments. -/
inductive HasAlternatingDecomposition (i0 : I) :
    Path (Pushout.inl (iU i0) : Pushout U V I iU iV) (Pushout.inl (iU i0)) → Prop where
  | refl :
      HasAlternatingDecomposition i0
        (Path.refl (Pushout.inl (iU i0) : Pushout U V I iU iV))
  | transLeft {p r}
      (hr : HasAlternatingDecomposition i0 r) :
      HasAlternatingDecomposition i0
        (Path.trans
          (Pushout.inlPath (A := U) (B := V) (C := I) (f := iU) (g := iV) p)
          r)
  | transRight {q r}
      (hr : HasAlternatingDecomposition i0 r) :
      HasAlternatingDecomposition i0
        (Path.trans
          (inVSegment (U := U) (V := V) (I := I) (iU := iU) (iV := iV) i0 q)
          r)

/-- Every alternating word decodes to a path with the corresponding alternating decomposition. -/
theorem decodeAlternating_hasDecomposition (i0 : I) :
    {s : Side} → (w : AlternatingWord (iU := iU) (iV := iV) i0 s) →
      HasAlternatingDecomposition (U := U) (V := V) (I := I) (iU := iU) (iV := iV) i0
        (decodeAlternating (U := U) (V := V) (I := I) (iU := iU) (iV := iV) i0 w)
  | _, .nil _ => by
    simpa [decodeAlternating] using
        (HasAlternatingDecomposition.refl (i0 := i0))
  | _, .consLeft p rest => by
      simpa [decodeAlternating] using
        (HasAlternatingDecomposition.transLeft
          (i0 := i0) (p := p)
          (decodeAlternating_hasDecomposition (i0 := i0) rest))
  | _, .consRight q rest => by
      simpa [decodeAlternating] using
        (HasAlternatingDecomposition.transRight
          (i0 := i0) (q := q)
          (decodeAlternating_hasDecomposition (i0 := i0) rest))

/-- Explicit `Step` witness: appending a reflexive segment on the right is removable. -/
noncomputable def decodeSingleLeft_rwEq (i0 : I) (p : Path (iU i0) (iU i0)) :
    RwEq
      (decodeAlternating (U := U) (V := V) (I := I) (iU := iU) (iV := iV) i0
        (AlternatingWord.consLeft p (AlternatingWord.nil Side.right)))
      (Pushout.inlPath (A := U) (B := V) (C := I) (f := iU) (g := iV) p) :=
  rweq_of_step
    (Step.trans_refl_right
      (Pushout.inlPath (A := U) (B := V) (C := I) (f := iU) (g := iV) p))

/-- Explicit `Step` witness for a right-side segment decoded through glue. -/
noncomputable def decodeSingleRight_rwEq (i0 : I) (q : Path (iV i0) (iV i0)) :
    RwEq
      (decodeAlternating (U := U) (V := V) (I := I) (iU := iU) (iV := iV) i0
        (AlternatingWord.consRight q (AlternatingWord.nil Side.left)))
      (inVSegment (U := U) (V := V) (I := I) (iU := iU) (iV := iV) i0 q) :=
  rweq_of_step
    (Step.trans_refl_right
      (inVSegment (U := U) (V := V) (I := I) (iU := iU) (iV := iV) i0 q))

/-- Overlap amalgamation witness from the pushout loop-naturality interface. -/
noncomputable def overlapAmalgamation_rwEq (i0 : I)
    [CompPath.Pushout.HasGlueNaturalLoopRwEq
      (A := U) (B := V) (C := I) (f := iU) (g := iV) i0]
    (p : Path i0 i0) :
    RwEqProp
      (Path.trans
        (Path.symm
          (CompPath.Pushout.inlPath (A := U) (B := V) (C := I) (f := iU) (g := iV) (Path.congrArg iU p)))
        (Path.trans
          (CompPath.Pushout.glue (A := U) (B := V) (C := I) (f := iU) (g := iV) i0)
          (CompPath.Pushout.inrPath (A := U) (B := V) (C := I) (f := iU) (g := iV) (Path.congrArg iV p))))
      (CompPath.Pushout.glue (A := U) (B := V) (C := I) (f := iU) (g := iV) i0) :=
  CompPath.Pushout.HasGlueNaturalLoopRwEq.eq
    (A := U) (B := V) (C := I) (f := iU) (g := iV) (c₀ := i0) i0 p

/-- Type-valued overlap amalgamation witness. -/
noncomputable def overlapAmalgamation_rweq (i0 : I)
    [CompPath.Pushout.HasGlueNaturalLoopRwEq
      (A := U) (B := V) (C := I) (f := iU) (g := iV) i0]
    (p : Path i0 i0) :
    RwEq
      (Path.trans
        (Path.symm
          (CompPath.Pushout.inlPath (A := U) (B := V) (C := I) (f := iU) (g := iV) (Path.congrArg iU p)))
        (Path.trans
          (CompPath.Pushout.glue (A := U) (B := V) (C := I) (f := iU) (g := iV) i0)
          (CompPath.Pushout.inrPath (A := U) (B := V) (C := I) (f := iU) (g := iV) (Path.congrArg iV p))))
      (CompPath.Pushout.glue (A := U) (B := V) (C := I) (f := iU) (g := iV) i0) :=
  rweq_of_rweqProp (overlapAmalgamation_rwEq (U := U) (V := V) (I := I) (iU := iU) (iV := iV) i0 p)

/-- Seifert-van Kampen for computational paths, stated on automorphisms in the fundamental
groupoid of the pushout. -/
noncomputable def seifertVanKampenFundamentalGroupoidPushout (i0 : I)
    [CompPath.Pushout.HasGlueNaturalLoopRwEq
      (A := U) (B := V) (C := I) (f := iU) (g := iV) i0]
    [HasPushoutSVKEncodeQuot U V I iU iV i0]
    [HasPushoutSVKDecodeEncode U V I iU iV i0]
    [HasPushoutSVKEncodeDecode U V I iU iV i0] :
    SimpleEquiv
      (FundamentalGroupoid.Hom
        (CompPath.Pushout U V I iU iV)
        (CompPath.Pushout.inl (A := U) (B := V) (C := I) (f := iU) (g := iV) (iU i0))
        (CompPath.Pushout.inl (A := U) (B := V) (C := I) (f := iU) (g := iV) (iU i0)))
      (AmalgamatedFreeProduct
        (PiOne U (iU i0))
        (PiOne V (iV i0))
        (PiOne I i0)
        (piOneFmap (A := U) (C := I) (f := iU) (c₀ := i0))
        (piOneGmap (B := V) (C := I) (g := iV) (c₀ := i0))) :=
  vanKampenPathLevelEquiv (A := U) (B := V) (C := I) (f := iU) (g := iV) i0

/-- `Path` witness for the left inverse of the Seifert-van Kampen equivalence. -/
noncomputable def seifertVanKampenFundamentalGroupoidPushout_left_inv_path (i0 : I)
    [CompPath.Pushout.HasGlueNaturalLoopRwEq
      (A := U) (B := V) (C := I) (f := iU) (g := iV) i0]
    [HasPushoutSVKEncodeQuot U V I iU iV i0]
    [HasPushoutSVKDecodeEncode U V I iU iV i0]
    [HasPushoutSVKEncodeDecode U V I iU iV i0]
    (α :
      FundamentalGroupoid.Hom
        (CompPath.Pushout U V I iU iV)
        (CompPath.Pushout.inl (A := U) (B := V) (C := I) (f := iU) (g := iV) (iU i0))
        (CompPath.Pushout.inl (A := U) (B := V) (C := I) (f := iU) (g := iV) (iU i0))) :=
  let e := seifertVanKampenFundamentalGroupoidPushout
    (U := U) (V := V) (I := I) (iU := iU) (iV := iV) i0
  show Path (e.invFun (e.toFun α)) α from
    Path.stepChain (e.left_inv α)

/-- `Path` witness for the right inverse of the Seifert-van Kampen equivalence. -/
noncomputable def seifertVanKampenFundamentalGroupoidPushout_right_inv_path (i0 : I)
    [CompPath.Pushout.HasGlueNaturalLoopRwEq
      (A := U) (B := V) (C := I) (f := iU) (g := iV) i0]
    [HasPushoutSVKEncodeQuot U V I iU iV i0]
    [HasPushoutSVKDecodeEncode U V I iU iV i0]
    [HasPushoutSVKEncodeDecode U V I iU iV i0]
    (w :
      AmalgamatedFreeProduct
        (PiOne U (iU i0))
        (PiOne V (iV i0))
        (PiOne I i0)
        (piOneFmap (A := U) (C := I) (f := iU) (c₀ := i0))
        (piOneGmap (B := V) (C := I) (g := iV) (c₀ := i0))) :=
  let e := seifertVanKampenFundamentalGroupoidPushout
    (U := U) (V := V) (I := I) (iU := iU) (iV := iV) i0
  show Path (e.toFun (e.invFun w)) w from
    Path.stepChain (e.right_inv w)

end PushoutDecomposition

section WedgeOfCircles

/-- Computational presentation of the free group on two generators via wedge loops. -/
abbrev FreeGroupTwoCode : Type :=
  WedgeFreeProductCode (A := Circle) (B := Circle) circleBase circleBase

/-- First wedge generator: left circle loop at the wedge basepoint. -/
noncomputable def wedgeGeneratorA :
    Path (Wedge.basepoint (A := Circle) (B := Circle) (a₀ := circleBase) (b₀ := circleBase))
      (Wedge.basepoint (A := Circle) (B := Circle) (a₀ := circleBase) (b₀ := circleBase)) :=
  Path.congrArg
    (Wedge.inl (A := Circle) (B := Circle) (a₀ := circleBase) (b₀ := circleBase))
    circleLoop

/-- Second wedge generator: right circle loop conjugated by glue back to the basepoint. -/
noncomputable def wedgeGeneratorB :
    Path (Wedge.basepoint (A := Circle) (B := Circle) (a₀ := circleBase) (b₀ := circleBase))
      (Wedge.basepoint (A := Circle) (B := Circle) (a₀ := circleBase) (b₀ := circleBase)) :=
  Path.trans
    (Wedge.glue (A := Circle) (B := Circle) (a₀ := circleBase) (b₀ := circleBase))
    (Path.trans
      (Path.congrArg
        (Wedge.inr (A := Circle) (B := Circle) (a₀ := circleBase) (b₀ := circleBase))
        circleLoop)
      (Path.symm (Wedge.glue (A := Circle) (B := Circle) (a₀ := circleBase) (b₀ := circleBase))))

/-- A concrete one-step rewrite showing right-unit elimination for a wedge generator. -/
noncomputable def wedgeGeneratorA_rightUnit_rwEq :
    RwEq
      (Path.trans
        wedgeGeneratorA
        (Path.refl (Wedge.basepoint (A := Circle) (B := Circle) (a₀ := circleBase) (b₀ := circleBase))))
      wedgeGeneratorA :=
  rweq_of_step (Step.trans_refl_right wedgeGeneratorA)

/-- `pi_1(S^1 \/ S^1)` is the free group on two generators in the computational model. -/
noncomputable def wedgeCirclePiOneEquivFreeGroupTwo
    [HasWedgeSVKDecodeBijective Circle Circle circleBase circleBase] :
    SimpleEquiv
      (PiOne
        (CompPath.Wedge Circle Circle circleBase circleBase)
        (CompPath.Wedge.basepoint (A := Circle) (B := Circle) (a₀ := circleBase) (b₀ := circleBase)))
      FreeGroupTwoCode :=
  wedgeFundamentalGroupEquiv_of_decode_bijective
    (A := Circle) (B := Circle) (a₀ := circleBase) (b₀ := circleBase)

/-- `Path` witness for the left inverse of the wedge-circle equivalence. -/
noncomputable def wedgeCirclePiOneEquivFreeGroupTwo_left_inv_path
    [HasWedgeSVKDecodeBijective Circle Circle circleBase circleBase]
    (α :
      PiOne
        (CompPath.Wedge Circle Circle circleBase circleBase)
        (CompPath.Wedge.basepoint (A := Circle) (B := Circle) (a₀ := circleBase) (b₀ := circleBase))) :=
  let e := wedgeCirclePiOneEquivFreeGroupTwo
  show Path (e.invFun (e.toFun α)) α from
    Path.stepChain (e.left_inv α)

/-- `Path` witness for the right inverse of the wedge-circle equivalence. -/
noncomputable def wedgeCirclePiOneEquivFreeGroupTwo_right_inv_path
    [HasWedgeSVKDecodeBijective Circle Circle circleBase circleBase]
    (w : FreeGroupTwoCode) :=
  let e := wedgeCirclePiOneEquivFreeGroupTwo
  show Path (e.toFun (e.invFun w)) w from
    Path.stepChain (e.right_inv w)

end WedgeOfCircles

end ComputationalPaths.Path.Homotopy

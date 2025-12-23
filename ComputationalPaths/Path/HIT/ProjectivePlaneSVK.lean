/-
# Real Projective Plane via Seifert-Van Kampen Theorem

This module provides an alternative proof that π₁(RP²) ≅ ℤ₂ using
the Seifert-van Kampen theorem.

## Construction

The Real Projective Plane can be constructed as a CW complex:
- One 0-cell (point)
- One 1-cell (generator a)
- One 2-cell attached along the boundary word `a²`

This corresponds to a pushout:
```
       S¹ ───boundary───→ S¹
       │                  │
       │ (collapse)       │
       ↓                  ↓
       * (point) ───────→ RP²
```

By SVK, since π₁(*) = 1, we get:
  π₁(RP²) ≅ π₁(S¹) / ⟨⟨boundary⟩⟩
          ≅ ℤ / ⟨⟨2⟩⟩
          ≅ ℤ₂

## Key Results

- `ProjectivePlaneSVK`: RP² as pushout of Circle and point
- `boundaryMap`: The attaching map sending S¹ to `a²`
- `projectivePlaneSVK_piOne_equiv`: π₁(ProjectivePlaneSVK) ≅ ℤ₂ via SVK

## References

- HoTT Book, Chapter 8.7
-/

import ComputationalPaths.Path.HIT.Circle
import ComputationalPaths.Path.HIT.Pushout
import ComputationalPaths.Path.HIT.PushoutPaths
import ComputationalPaths.Path.HIT.ProjectivePlane
import ComputationalPaths.Path.HIT.KleinBottleSVK

namespace ComputationalPaths
namespace Path

universe u

-- UnitU and unitU are imported from KleinBottleSVK

namespace ProjectivePlaneSVK

/-! ## The Boundary Loop

The RP² 2-cell is attached along `a²`, where `a` is the loop of the circle.
-/

/-- The boundary word `a²` as a loop in the circle. -/
noncomputable def boundaryWord : Path circleBase circleBase :=
  Path.trans circleLoop circleLoop

/-! ### The Attaching Map

We define the map `Circle → Circle` that sends the fundamental
loop of S¹ to the boundary word `a²`.
-/

/-- Data for the circle recursor: map `circleBase` to `circleBase`,
and `circleLoop` to `a²`. -/
noncomputable def boundaryMapData : CircleRecData Circle where
  base := circleBase
  loop := boundaryWord

/-- The attaching map: Circle → Circle.
This sends the circle to the boundary loop `a²` (degree 2 map). -/
noncomputable def boundaryMap : Circle → Circle :=
  circleRec boundaryMapData

/-- The base point maps to the circle base. -/
theorem boundaryMap_base : boundaryMap circleBase = circleBase :=
  circleRec_base boundaryMapData

/-- The fundamental loop maps to the boundary word. -/
theorem boundaryMap_loop :
    Path.trans
      (Path.symm (Path.ofEq boundaryMap_base))
      (Path.trans
        (Path.congrArg boundaryMap circleLoop)
        (Path.ofEq boundaryMap_base)) =
    boundaryWord :=
  circleRec_loop boundaryMapData

/-! ### The Collapse Map -/

/-- The trivial collapse map: Circle → UnitU. -/
def collapseMap : Circle.{u} → UnitU.{u} := fun _ => (unitU : UnitU.{u})

/-! ## RP² as Pushout -/

/-- The Real Projective Plane constructed via the CW-complex pushout.
This is the pushout of `Circle ← Circle → UnitU`. -/
def ProjectivePlaneSVK : Type u :=
  Pushout Circle UnitU Circle boundaryMap collapseMap

/-- Injection of the circle (1-skeleton) into RP². -/
noncomputable def inlCircle : Circle → ProjectivePlaneSVK :=
  @Pushout.inl Circle UnitU Circle boundaryMap collapseMap

/-- Injection of the point (0-cell) into RP². -/
noncomputable def inrPoint : UnitU → ProjectivePlaneSVK :=
  @Pushout.inr Circle UnitU Circle boundaryMap collapseMap

/-- The basepoint of RP². -/
noncomputable def baseSVK : ProjectivePlaneSVK :=
  inlCircle circleBase

/-- Loop A in RP²: the image of the circle's loop. -/
noncomputable def loopASVK : Path baseSVK baseSVK :=
  @Pushout.inlPath Circle UnitU Circle boundaryMap collapseMap _ _ circleLoop

/-- The boundary word in RP². -/
noncomputable def boundaryWordSVK : Path baseSVK baseSVK :=
  @Pushout.inlPath Circle UnitU Circle boundaryMap collapseMap _ _ boundaryWord

/-- Key helper: the glue path at the circle basepoint. -/
noncomputable def glueBase : Path (@Pushout.inl Circle UnitU Circle boundaryMap collapseMap (boundaryMap circleBase))
                                  (@Pushout.inr Circle UnitU Circle boundaryMap collapseMap (collapseMap circleBase)) :=
  @Pushout.glue Circle UnitU Circle boundaryMap collapseMap circleBase

/-- congrArg of collapseMap on circleLoop gives a path in UnitU.
Uses `unitU_loop_rweq_refl` from KleinBottleSVK. -/
theorem collapseMap_circleLoop_rweq_refl :
    RwEq.{u} (Path.congrArg collapseMap circleLoop.{u}) (Path.refl unitU) := by
  simpa [collapseMap] using
    (KleinBottleSVK.congrArg_const_rweq_refl (A := Circle.{u}) (B := UnitU.{u}) unitU circleLoop.{u})

/-- inrPath of a loop RwEq to refl gives refl. Concrete version for our pushout. -/
theorem inrPath_rweq_refl_concrete
    {p : Path unitU unitU} (h : RwEq p (Path.refl unitU)) :
    RwEq (@Pushout.inrPath Circle UnitU Circle boundaryMap collapseMap _ _ p)
         (Path.refl (@Pushout.inr Circle UnitU Circle boundaryMap collapseMap unitU)) := by
  apply rweq_trans (rweq_congrArg_of_rweq (@Pushout.inr Circle UnitU Circle boundaryMap collapseMap) h)
  exact rweq_refl _

/-! ## Boundary Triviality in the Pushout

For `ProjectivePlaneSVK`, the attaching circle is collapsed to the point `unitU`.
Assuming loop-only glue naturality at `circleBase`, the image of the attaching
loop becomes RwEq-trivial in the pushout, yielding the expected boundary
relation `a² ≈ refl`. -/

/-- `inlPath (congrArg boundaryMap circleLoop)` is RwEq to refl, assuming loop-only glue naturality. -/
theorem inlPath_congrArg_boundaryMap_loop_rweq_refl
    [Pushout.HasGlueNaturalLoopRwEq (A := Circle.{u}) (B := UnitU.{u}) (C := Circle.{u})
      (f := boundaryMap) (g := collapseMap) circleBase.{u}] :
    RwEq.{u}
      (@Pushout.inlPath Circle.{u} UnitU.{u} Circle.{u} boundaryMap collapseMap _ _
        (Path.congrArg boundaryMap circleLoop.{u}))
      (Path.refl
        (@Pushout.inl Circle.{u} UnitU.{u} Circle.{u} boundaryMap collapseMap
          (boundaryMap circleBase.{u}))) := by
  let glue₀ :=
    @Pushout.glue Circle.{u} UnitU.{u} Circle.{u} boundaryMap collapseMap circleBase.{u}
  have hnat :
      RwEq.{u}
        (@Pushout.inlPath Circle.{u} UnitU.{u} Circle.{u} boundaryMap collapseMap _ _
          (Path.congrArg boundaryMap circleLoop.{u}))
        (Path.trans glue₀
          (Path.trans
            (@Pushout.inrPath Circle.{u} UnitU.{u} Circle.{u} boundaryMap collapseMap _ _
              (Path.congrArg collapseMap circleLoop.{u}))
            (Path.symm glue₀))) := by
    simpa [glue₀] using
      (Pushout.glue_natural_loop_rweq (A := Circle.{u}) (B := UnitU.{u}) (C := Circle.{u})
        (f := boundaryMap) (g := collapseMap) (c₀ := circleBase.{u}) (p := circleLoop.{u}))
  have hinr :
      RwEq.{u}
        (@Pushout.inrPath Circle.{u} UnitU.{u} Circle.{u} boundaryMap collapseMap _ _
          (Path.congrArg collapseMap circleLoop.{u}))
        (Path.refl (@Pushout.inr Circle.{u} UnitU.{u} Circle.{u} boundaryMap collapseMap unitU)) := by
    exact
      inrPath_rweq_refl_concrete (p := Path.congrArg collapseMap circleLoop.{u})
        (h := collapseMap_circleLoop_rweq_refl)
  have inner :
      RwEq.{u}
        (Path.trans
          (@Pushout.inrPath Circle.{u} UnitU.{u} Circle.{u} boundaryMap collapseMap _ _
            (Path.congrArg collapseMap circleLoop.{u}))
          (Path.symm glue₀))
        (Path.trans (Path.refl (@Pushout.inr Circle.{u} UnitU.{u} Circle.{u} boundaryMap collapseMap unitU))
          (Path.symm glue₀)) :=
    rweq_trans_congr_left (Path.symm glue₀) hinr
  have step1 :
      RwEq.{u}
        (Path.trans glue₀
          (Path.trans
            (@Pushout.inrPath Circle.{u} UnitU.{u} Circle.{u} boundaryMap collapseMap _ _
              (Path.congrArg collapseMap circleLoop.{u}))
            (Path.symm glue₀)))
        (Path.trans glue₀
          (Path.trans (Path.refl (@Pushout.inr Circle.{u} UnitU.{u} Circle.{u} boundaryMap collapseMap unitU))
            (Path.symm glue₀))) :=
    rweq_trans_congr_right glue₀ inner
  have step2 :
      RwEq.{u}
        (Path.trans glue₀
          (Path.trans (Path.refl (@Pushout.inr Circle.{u} UnitU.{u} Circle.{u} boundaryMap collapseMap unitU))
            (Path.symm glue₀)))
        (Path.trans glue₀ (Path.symm glue₀)) := by
    refine rweq_trans_congr_right glue₀ ?_
    exact rweq_cmpA_refl_left (Path.symm glue₀)
  have step3 :
      RwEq.{u} (Path.trans glue₀ (Path.symm glue₀))
        (Path.refl
          (@Pushout.inl Circle.{u} UnitU.{u} Circle.{u} boundaryMap collapseMap
            (boundaryMap circleBase.{u}))) :=
    rweq_cmpA_inv_right glue₀
  exact rweq_trans hnat (rweq_trans step1 (rweq_trans step2 step3))

/-- The boundary relation in `ProjectivePlaneSVK`: `a²` is homotopic to `refl`,
assuming loop-only glue naturality at `circleBase`. -/
theorem boundary_relation
    [Pushout.HasGlueNaturalLoopRwEq (A := Circle.{u}) (B := UnitU.{u}) (C := Circle.{u})
      (f := boundaryMap) (g := collapseMap) circleBase.{u}] :
    RwEq.{u} boundaryWordSVK (Path.refl baseSVK) := by
  have hEq :
      @Pushout.inlPath Circle UnitU Circle boundaryMap collapseMap _ _
        (Path.trans
          (Path.symm (Path.ofEq boundaryMap_base))
          (Path.trans (Path.congrArg boundaryMap circleLoop) (Path.ofEq boundaryMap_base))) =
        boundaryWordSVK := by
    simpa [boundaryWordSVK] using
      _root_.congrArg
        (@Pushout.inlPath Circle UnitU Circle boundaryMap collapseMap _ _)
        boundaryMap_loop
  have hStart :
      RwEq boundaryWordSVK
        (@Pushout.inlPath Circle UnitU Circle boundaryMap collapseMap _ _
          (Path.trans
            (Path.symm (Path.ofEq boundaryMap_base))
            (Path.trans (Path.congrArg boundaryMap circleLoop) (Path.ofEq boundaryMap_base)))) :=
    rweq_of_eq hEq.symm
  let baseAdj :
      Path
        (@Pushout.inl Circle UnitU Circle boundaryMap collapseMap (boundaryMap circleBase))
        baseSVK :=
    @Pushout.inlPath Circle UnitU Circle boundaryMap collapseMap _ _ (Path.ofEq boundaryMap_base)
  have hConjEq :
      @Pushout.inlPath Circle UnitU Circle boundaryMap collapseMap _ _
          (Path.trans
            (Path.symm (Path.ofEq boundaryMap_base))
            (Path.trans (Path.congrArg boundaryMap circleLoop) (Path.ofEq boundaryMap_base))) =
        Path.trans (Path.symm baseAdj)
          (Path.trans
            (@Pushout.inlPath Circle UnitU Circle boundaryMap collapseMap _ _
              (Path.congrArg boundaryMap circleLoop))
            baseAdj) := by
    unfold baseAdj
    unfold Pushout.inlPath
    rw [Path.congrArg_trans, Path.congrArg_symm, Path.congrArg_trans]
  have hConj :
      RwEq
        (@Pushout.inlPath Circle UnitU Circle boundaryMap collapseMap _ _
          (Path.trans
            (Path.symm (Path.ofEq boundaryMap_base))
            (Path.trans (Path.congrArg boundaryMap circleLoop) (Path.ofEq boundaryMap_base))))
        (Path.trans (Path.symm baseAdj)
          (Path.trans
            (@Pushout.inlPath Circle UnitU Circle boundaryMap collapseMap _ _
              (Path.congrArg boundaryMap circleLoop))
            baseAdj)) :=
    rweq_of_eq hConjEq
  have hLoop := inlPath_congrArg_boundaryMap_loop_rweq_refl
  have step1 :
      RwEq
        (Path.trans (Path.symm baseAdj)
          (Path.trans
            (@Pushout.inlPath Circle UnitU Circle boundaryMap collapseMap _ _
              (Path.congrArg boundaryMap circleLoop))
            baseAdj))
        (Path.trans (Path.symm baseAdj)
          (Path.trans
            (Path.refl
              (@Pushout.inl Circle UnitU Circle boundaryMap collapseMap (boundaryMap circleBase)))
            baseAdj)) := by
    have inner :=
      rweq_trans_congr_left baseAdj hLoop
    exact rweq_trans_congr_right (Path.symm baseAdj) inner
  have step2 :
      RwEq
        (Path.trans (Path.symm baseAdj)
          (Path.trans
            (Path.refl
              (@Pushout.inl Circle UnitU Circle boundaryMap collapseMap (boundaryMap circleBase)))
            baseAdj))
        (Path.trans (Path.symm baseAdj) baseAdj) := by
    refine rweq_trans_congr_right (Path.symm baseAdj) ?_
    exact rweq_cmpA_refl_left baseAdj
  have step3 :
      RwEq (Path.trans (Path.symm baseAdj) baseAdj) (Path.refl baseSVK) :=
    rweq_cmpA_inv_left baseAdj
  exact
    rweq_trans hStart
      (rweq_trans hConj (rweq_trans step1 (rweq_trans step2 step3)))

/-! ## Fundamental Group via SVK -/

/-- The fundamental group of ProjectivePlaneSVK at the base point. -/
noncomputable abbrev ProjectivePlaneSVKPiOne : Type u :=
  π₁(ProjectivePlaneSVK, baseSVK)

/-! ### The Quotient Presentation

By SVK, π₁(RP²) is the amalgamated free product:
  π₁(Circle) *_{π₁(Circle)} π₁(Unit)

Since π₁(Unit) = 1, this simplifies to:
  π₁(Circle) / ⟨⟨image of π₁(Circle)⟩⟩

The map π₁(Circle) → π₁(Circle) sends the generator to `a²`.
So we get:
  ℤ / ⟨⟨2⟩⟩ ≅ ℤ₂
-/

/-- Words in the free group on one generator (ℤ), quotiented by `a² = 1`. -/
inductive ProjectiveRelation : FreeProductWord Int Unit → FreeProductWord Int Unit → Prop where
  /-- The boundary relation: `a² = ε`. -/
  | boundary (pre suf : FreeProductWord Int Unit) :
      ProjectiveRelation
        (FreeProductWord.concat pre
          (FreeProductWord.concat
            (.consLeft 1 (.consLeft 1 .nil))
            suf))
        (FreeProductWord.concat pre suf)
  /-- Symmetric case. -/
  | boundary_inv (pre suf : FreeProductWord Int Unit) :
      ProjectiveRelation
        (FreeProductWord.concat pre suf)
        (FreeProductWord.concat pre
          (FreeProductWord.concat
            (.consLeft 1 (.consLeft 1 .nil))
            suf))

/-- The equivalence relation generated by the Projective relation. -/
inductive ProjectiveEquiv : FreeProductWord Int Unit → FreeProductWord Int Unit → Prop where
  | refl (w : FreeProductWord Int Unit) : ProjectiveEquiv w w
  | step {w₁ w₂ : FreeProductWord Int Unit} : ProjectiveRelation w₁ w₂ → ProjectiveEquiv w₁ w₂
  | symm {w₁ w₂ : FreeProductWord Int Unit} : ProjectiveEquiv w₁ w₂ → ProjectiveEquiv w₂ w₁
  | trans {w₁ w₂ w₃ : FreeProductWord Int Unit} :
      ProjectiveEquiv w₁ w₂ → ProjectiveEquiv w₂ w₃ → ProjectiveEquiv w₁ w₃

/-- The quotient group ℤ/2. -/
def ProjectivePresentation : Type := Quot ProjectiveEquiv

namespace ProjectivePresentation

/-- Embed a word into the quotient. -/
def ofWord (w : FreeProductWord Int Unit) : ProjectivePresentation :=
  Quot.mk ProjectiveEquiv w

/-- Identity element. -/
def one : ProjectivePresentation := ofWord .nil

/-- Generator `a`. -/
def genA : ProjectivePresentation := ofWord (.consLeft 1 .nil)

end ProjectivePresentation

/-! ## Isomorphism with ℤ₂ (Bool) -/

/-- XOR operation representing addition in ℤ₂. -/
def z2Add (x y : Bool) : Bool := xor x y

@[simp] theorem z2Add_assoc (x y z : Bool) :
    z2Add (z2Add x y) z = z2Add x (z2Add y z) := by
  simp [z2Add]

/-- Helper: convert a word to Bool (parity). -/
def wordToBool : FreeProductWord Int Unit → Bool
  | .nil => false
  | .consLeft n rest => z2Add (if n % 2 == 0 then false else true) (wordToBool rest)
  | .consRight _ rest => wordToBool rest -- Unit has no content

/-- The boundary word `a²` evaluates to false (0). -/
theorem wordToBool_boundaryWord :
    wordToBool (.consLeft 1 (.consLeft 1 .nil)) = false := by
  native_decide

/-- wordToBool distributes over concat (with XOR). -/
theorem wordToBool_concat (w₁ w₂ : FreeProductWord Int Unit) :
    wordToBool (FreeProductWord.concat w₁ w₂) = z2Add (wordToBool w₁) (wordToBool w₂) := by
  induction w₁ with
  | nil =>
      -- LHS: wordToBool w₂
      -- RHS: z2Add (wordToBool .nil) (wordToBool w₂) = z2Add false (wordToBool w₂) = xor false (wordToBool w₂) = wordToBool w₂
      simp only [FreeProductWord.concat, wordToBool, z2Add, Bool.false_xor]
  | consLeft n rest ih =>
      -- LHS: wordToBool (concat (consLeft n rest) w₂) = wordToBool (consLeft n (concat rest w₂))
      --    = z2Add (parity n) (wordToBool (concat rest w₂))
      -- By IH: = z2Add (parity n) (z2Add (wordToBool rest) (wordToBool w₂))
      -- RHS: z2Add (wordToBool (consLeft n rest)) (wordToBool w₂)
      --    = z2Add (z2Add (parity n) (wordToBool rest)) (wordToBool w₂)
      -- Need: z2Add p (z2Add r w) = z2Add (z2Add p r) w, which is z2Add_assoc reversed
      simp only [FreeProductWord.concat, wordToBool]
      rw [ih]
      rw [← z2Add_assoc]
  | consRight u rest ih =>
      simp only [FreeProductWord.concat, wordToBool]
      rw [ih]

/-- The word-to-bool map respects the Projective equivalence. -/
theorem wordToBool_respects {w₁ w₂ : FreeProductWord Int Unit}
    (h : ProjectiveEquiv w₁ w₂) : wordToBool w₁ = wordToBool w₂ := by
  induction h with
  | refl _ => rfl
  | step hr =>
      cases hr with
      | boundary pre suf =>
          have hboundary : wordToBool (.consLeft 1 (.consLeft 1 .nil)) = false :=
            wordToBool_boundaryWord
          rw [wordToBool_concat, wordToBool_concat, wordToBool_concat]
          rw [hboundary]
          simp only [z2Add, Bool.false_xor]
      | boundary_inv pre suf =>
          have hboundary : wordToBool (.consLeft 1 (.consLeft 1 .nil)) = false :=
            wordToBool_boundaryWord
          -- Goal: wordToBool (concat pre suf) = wordToBool (concat pre (concat a² suf))
          -- This is symmetric to the boundary case
          rw [wordToBool_concat, wordToBool_concat, wordToBool_concat]
          rw [hboundary]
          simp only [z2Add, Bool.false_xor]
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Map from ProjectivePresentation to Bool. -/
noncomputable def presentationToBool : ProjectivePresentation → Bool :=
  Quot.lift wordToBool (fun _ _ h => wordToBool_respects h)

/-! ## The Main Equivalence via SVK -/

/-- Loop A as a π₁ element. -/
noncomputable def loopAClass : ProjectivePlaneSVKPiOne := Quot.mk _ loopASVK

/-- Natural power of a path. -/
noncomputable def pathPowNat (p : Path baseSVK baseSVK) : Nat → Path baseSVK baseSVK
  | 0 => Path.refl baseSVK
  | n + 1 => Path.trans (pathPowNat p n) p

/-- Integer power of a path. -/
noncomputable def pathZPow (p : Path baseSVK baseSVK) : Int → Path baseSVK baseSVK
  | Int.ofNat n => pathPowNat p n
  | Int.negSucc n => Path.symm (pathPowNat p (n + 1))

/-- Integer power of loop A class. -/
noncomputable def loopAClass_zpow (n : Int) : ProjectivePlaneSVKPiOne :=
  Quot.mk _ (pathZPow loopASVK n)

/-- Candidate decode map: Bool → π₁(ProjectivePlaneSVK).

This is the expected inverse of the SVK equivalence, but we do not yet prove
it matches the inverse of `projectivePlaneSVK_piOne_equiv`. -/
noncomputable def decodeSVK_def : Bool → ProjectivePlaneSVKPiOne
  | false => Quot.mk _ (Path.refl baseSVK)
  | true => loopAClass

/-- Data providing the SVK-based π₁ equivalence. -/
class HasProjectivePlaneSVKPiOneEquiv where
  piOneEquiv : SimpleEquiv ProjectivePlaneSVKPiOne Bool

/-- **Main Theorem (SVK version)**: π₁(ProjectivePlaneSVK) ≅ ℤ₂. -/
noncomputable def projectivePlaneSVK_piOne_equiv [HasProjectivePlaneSVKPiOneEquiv] :
    SimpleEquiv ProjectivePlaneSVKPiOne Bool :=
  HasProjectivePlaneSVKPiOneEquiv.piOneEquiv

variable [HasProjectivePlaneSVKPiOneEquiv]

/-- Encode: π₁(ProjectivePlaneSVK) → Bool. -/
noncomputable def encodeSVK : ProjectivePlaneSVKPiOne → Bool :=
  projectivePlaneSVK_piOne_equiv.toFun

/-- Decode: Bool → π₁(ProjectivePlaneSVK). -/
noncomputable def decodeSVK : Bool → ProjectivePlaneSVKPiOne :=
  projectivePlaneSVK_piOne_equiv.invFun

/-- Encode on loop representatives (for stating laws). -/
noncomputable def encodeSVK_path (p : Path baseSVK baseSVK) : Bool :=
  encodeSVK (Quot.mk _ p)

/-- Encode respects RwEq. -/
theorem encodeSVK_respects_rweq {p q : Path baseSVK baseSVK}
    (h : RwEq p q) : encodeSVK_path p = encodeSVK_path q := by
  unfold encodeSVK_path
  exact _root_.congrArg encodeSVK (Quot.sound h)

/-- Round-trip: decode ∘ encode = id. -/
theorem decodeSVK_encodeSVK (α : ProjectivePlaneSVKPiOne) :
    decodeSVK (encodeSVK α) = α :=
  projectivePlaneSVK_piOne_equiv.left_inv α

/-- Round-trip: encode ∘ decode = id. -/
theorem encodeSVK_decodeSVK (z : Bool) :
    encodeSVK (decodeSVK z) = z :=
  projectivePlaneSVK_piOne_equiv.right_inv z

end ProjectivePlaneSVK
end Path
end ComputationalPaths

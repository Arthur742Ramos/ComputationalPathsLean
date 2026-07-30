/-
# Pushout SVK Instances

Instances of the Seifert-van Kampen theorem for pushouts.
-/

import ComputationalPaths.Path.CompPath.PushoutPaths
import ComputationalPaths.Path.TypeTheory.QuotientPathInduction

namespace ComputationalPaths.Path.CompPath.PushoutSVKInstances

universe u

section

variable {A : Type u} {B : Type u} {C : Type u}
variable {f : C → A} {g : C → B} (c₀ : C)

@[simp] theorem pushout_svk_inl_mul (α β : π₁(A, f c₀)) :
    pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀ (piOneMul α β) =
      piOneMul
        (pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀ α)
        (pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀ β) := by
  simpa using pushoutPiOneInl_mul (A := A) (B := B) (C := C) (f := f) (g := g) c₀ α β

@[simp] theorem pushout_svk_inr_mul (β₁ β₂ : π₁(B, g c₀)) :
    pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀ (piOneMul β₁ β₂) =
      piOneMul
        (pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀ β₁)
        (pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀ β₂) := by
  simpa using pushoutPiOneInr_mul (A := A) (B := B) (C := C) (f := f) (g := g) c₀ β₁ β₂

@[simp] theorem pushout_svk_decode_cons_left
    (α : π₁(A, f c₀)) (rest : PushoutCode A B C f g c₀) :
    pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀ (.consLeft α rest) =
      piOneMul
        (pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀ α)
        (pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀ rest) := by
  simpa using pushoutDecode_consLeft (A := A) (B := B) (C := C) (f := f) (g := g) c₀ α rest

@[simp] theorem pushout_svk_decode_cons_right
    (β : π₁(B, g c₀)) (rest : PushoutCode A B C f g c₀) :
    pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀ (.consRight β rest) =
      piOneMul
        (pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀ β)
        (pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀ rest) := by
  simpa using pushoutDecode_consRight (A := A) (B := B) (C := C) (f := f) (g := g) c₀ β rest

end

/-! ## The amalgamation-only target is too coarse

`AmalgEquiv` only replaces one amalgamating letter by another, so it preserves
raw word length.  In particular it cannot remove an identity letter.  The
decoder does remove such a letter, which makes the old amalgamation-only
encode/decode and bijectivity interfaces impossible.  The corrected SVK target
is `FullAmalgamatedFreeProduct`, whose relation also contains
`FreeGroupStep.removeLeftZero` and the other group reductions.
-/

namespace AmalgamationOnlyObstruction

variable {G₁ : Type u} {G₂ : Type u} {H : Type u}
variable {i₁ : H → G₁} {i₂ : H → G₂}

@[simp] theorem word_length_nil :
    FreeProductWord.length (FreeProductWord.nil : FreeProductWord G₁ G₂) = 0 :=
  rfl

@[simp] theorem word_length_consLeft (x : G₁) (w : FreeProductWord G₁ G₂) :
    FreeProductWord.length (.consLeft x w) = 1 + FreeProductWord.length w :=
  rfl

@[simp] theorem word_length_consRight (y : G₂) (w : FreeProductWord G₁ G₂) :
    FreeProductWord.length (.consRight y w) = 1 + FreeProductWord.length w :=
  rfl

theorem word_length_concat (w₁ w₂ : FreeProductWord G₁ G₂) :
    FreeProductWord.length (FreeProductWord.concat w₁ w₂) =
      FreeProductWord.length w₁ + FreeProductWord.length w₂ := by
  induction w₁ with
  | nil =>
      simp [FreeProductWord.concat, FreeProductWord.length]
  | consLeft x rest ih =>
      simp only [FreeProductWord.concat, word_length_consLeft, ih]
      omega
  | consRight y rest ih =>
      simp only [FreeProductWord.concat, word_length_consRight, ih]
      omega

theorem amalgRelation_preserves_length
    {w₁ w₂ : FreeProductWord G₁ G₂}
    (h : AmalgRelation i₁ i₂ w₁ w₂) :
    FreeProductWord.length w₁ = FreeProductWord.length w₂ := by
  cases h <;>
    simp only [word_length_concat, FreeProductWord.singleLeft,
      FreeProductWord.singleRight, word_length_consLeft, word_length_consRight,
      word_length_nil] <;>
    omega

theorem amalgEquiv_preserves_length
    {w₁ w₂ : FreeProductWord G₁ G₂}
    (h : AmalgEquiv i₁ i₂ w₁ w₂) :
    FreeProductWord.length w₁ = FreeProductWord.length w₂ := by
  induction h with
  | refl _ => rfl
  | step h => exact amalgRelation_preserves_length h
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Word length descends to the amalgamation-only quotient. -/
noncomputable def amalgLength :
    AmalgamatedFreeProduct G₁ G₂ H i₁ i₂ → Nat :=
  Quot.lift FreeProductWord.length (fun _ _ h => amalgEquiv_preserves_length h)

@[simp] theorem amalgLength_ofWord (w : FreeProductWord G₁ G₂) :
    amalgLength
      (AmalgamatedFreeProduct.ofWord
        (G₁ := G₁) (G₂ := G₂) (H := H) (i₁ := i₁) (i₂ := i₂) w) =
      FreeProductWord.length w :=
  rfl

theorem amalg_nil_ne_singleLeft (x : G₁) :
    AmalgamatedFreeProduct.ofWord
        (G₁ := G₁) (G₂ := G₂) (H := H) (i₁ := i₁) (i₂ := i₂)
        (FreeProductWord.nil : FreeProductWord G₁ G₂) ≠
      AmalgamatedFreeProduct.ofWord
        (G₁ := G₁) (G₂ := G₂) (H := H) (i₁ := i₁) (i₂ := i₂)
        (.consLeft x .nil) := by
  intro h
  have hlen := _root_.congrArg (amalgLength (i₁ := i₁) (i₂ := i₂)) h
  simp at hlen

section Pushout

variable {A : Type u} {B : Type u} {C : Type u}
variable {f : C → A} {g : C → B} (c₀ : C)

private noncomputable def leftIdentity :
    π₁(A, f c₀) :=
  Quot.mk _ (Path.refl (f c₀))

private theorem decode_nil_eq_decode_left_zero :
    pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀
        (FreeProductWord.nil :
          PushoutCode A B C f g c₀) =
      pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀
        (.consLeft
          (leftIdentity (A := A) (C := C) (f := f) c₀)
          .nil) := by
  rw [pushoutDecode_consLeft]
  have hz :
      pushoutPiOneInl
          (A := A) (B := B) (C := C) (f := f) (g := g) c₀
          (leftIdentity (A := A) (C := C) (f := f) c₀) =
        Quot.mk _ (Path.refl (Pushout.inl (f c₀))) := by
    simpa [leftIdentity] using
      (pushoutPiOneInl_zero
        (A := A) (B := B) (C := C) (f := f) (g := g) c₀)
  rw [hz]
  exact (piOneMul_refl_left _).symm

/-- The amalgamation-only encode/decode round trip is impossible. -/
theorem hasPushoutSVKEncodeDecode_impossible
    [HasPushoutSVKEncodeQuot A B C f g c₀] :
    ¬ HasPushoutSVKEncodeDecode A B C f g c₀ := by
  intro h
  let nilWord : PushoutCode A B C f g c₀ := .nil
  let zeroWord : PushoutCode A B C f g c₀ :=
    .consLeft
      (leftIdentity (A := A) (C := C) (f := f) c₀)
      .nil
  have hdecode :
      pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀ nilWord =
        pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀ zeroWord := by
    simpa [nilWord, zeroWord] using
      decode_nil_eq_decode_left_zero
        (A := A) (B := B) (C := C) (f := f) (g := g) c₀
  have hnil :=
    h.encode_decode nilWord
  have hzero :=
    h.encode_decode zeroWord
  rw [← hdecode] at hzero
  have hrel :
      AmalgEquiv (piOneFmap c₀) (piOneGmap c₀) nilWord zeroWord :=
    AmalgEquiv.trans (AmalgEquiv.symm hnil) hzero
  have hlen := amalgEquiv_preserves_length hrel
  simp [nilWord, zeroWord] at hlen

/-- The amalgamation-only quotient decoder is never injective, hence its old
bijectivity interface is impossible. -/
theorem hasPushoutSVKDecodeAmalgBijective_impossible
    [Pushout.HasGlueNaturalLoopRwEq
      (A := A) (B := B) (C := C) (f := f) (g := g) c₀] :
    ¬ HasPushoutSVKDecodeAmalgBijective A B C f g c₀ := by
  intro h
  let nilClass :
      AmalgamatedFreeProduct
        (π₁(A, f c₀)) (π₁(B, g c₀)) (π₁(C, c₀))
        (piOneFmap c₀) (piOneGmap c₀) :=
    AmalgamatedFreeProduct.ofWord .nil
  let zeroClass :
      AmalgamatedFreeProduct
        (π₁(A, f c₀)) (π₁(B, g c₀)) (π₁(C, c₀))
        (piOneFmap c₀) (piOneGmap c₀) :=
    AmalgamatedFreeProduct.ofWord
      (.consLeft
        (leftIdentity (A := A) (C := C) (f := f) c₀)
        .nil)
  have hdecode :
      pushoutDecodeAmalg
          (A := A) (B := B) (C := C) (f := f) (g := g) c₀ nilClass =
        pushoutDecodeAmalg
          (A := A) (B := B) (C := C) (f := f) (g := g) c₀ zeroClass := by
    simpa [nilClass, zeroClass, pushoutDecodeAmalg] using
      decode_nil_eq_decode_left_zero
        (A := A) (B := B) (C := C) (f := f) (g := g) c₀
  have heq := h.bijective.1 hdecode
  exact
    amalg_nil_ne_singleLeft
      (i₁ := piOneFmap c₀) (i₂ := piOneGmap c₀)
      (leftIdentity (A := A) (C := C) (f := f) c₀)
      (by simpa [nilClass, zeroClass] using heq)

end Pushout

section Wedge

variable {A : Type u} {B : Type u} (a₀ : A) (b₀ : B)

private noncomputable def wedgeLeftIdentity :
    π₁(A, a₀) :=
  Quot.mk _ (Path.refl a₀)

/-- The old strict wedge word round trip is impossible for every pair of
pointed types, not only for the circle specialization. -/
theorem hasWedgeSVKEncodeDecode_impossible
    [WedgeSVKInstances.HasWedgeSVKEncodeQuot A B a₀ b₀] :
    ¬ WedgeSVKInstances.HasWedgeSVKEncodeDecode A B a₀ b₀ := by
  intro h
  let nilWord : FreeProductWord (π₁(A, a₀)) (π₁(B, b₀)) := .nil
  let zeroWord : FreeProductWord (π₁(A, a₀)) (π₁(B, b₀)) :=
    .consLeft (wedgeLeftIdentity (A := A) a₀) .nil
  have hdecode :
      pushoutDecode
          (A := A) (B := B) (C := PUnit')
          (f := fun _ => a₀) (g := fun _ => b₀) PUnit'.unit nilWord =
        pushoutDecode
          (A := A) (B := B) (C := PUnit')
          (f := fun _ => a₀) (g := fun _ => b₀) PUnit'.unit zeroWord := by
    simpa [nilWord, zeroWord, wedgeLeftIdentity] using
      (decode_nil_eq_decode_left_zero
        (A := A) (B := B) (C := PUnit')
        (f := fun _ => a₀) (g := fun _ => b₀) PUnit'.unit)
  have hnil := h.encode_decode nilWord
  have hzero := h.encode_decode zeroWord
  have hwords : nilWord = zeroWord := by
    calc
      nilWord =
          WedgeSVKInstances.wedgeEncodeQuotPrim
            (A := A) (B := B) a₀ b₀
            (pushoutDecode
              (A := A) (B := B) (C := PUnit')
              (f := fun _ => a₀) (g := fun _ => b₀) PUnit'.unit nilWord) :=
        hnil.symm
      _ =
          WedgeSVKInstances.wedgeEncodeQuotPrim
            (A := A) (B := B) a₀ b₀
            (pushoutDecode
              (A := A) (B := B) (C := PUnit')
              (f := fun _ => a₀) (g := fun _ => b₀) PUnit'.unit zeroWord) :=
        _root_.congrArg
          (WedgeSVKInstances.wedgeEncodeQuotPrim
            (A := A) (B := B) a₀ b₀)
          hdecode
      _ = zeroWord := hzero
  have hlen := _root_.congrArg FreeProductWord.length hwords
  simp [nilWord, zeroWord] at hlen

end Wedge

end AmalgamationOnlyObstruction

/-! ## The collapsed full-target theorem

The current `RwEq` relation is total on parallel paths, so every genuine
`PathRwQuot` loop fiber is a subsingleton.  Consequently the full amalgamated
word quotient is also a subsingleton: every letter equals the identity letter,
which `FreeGroupStep` removes.  This yields a fully proved SVK equivalence under
the current definitions.  It is intentionally named `collapsed`: it does not
recover the nontrivial classical fundamental groups represented elsewhere by
synthetic winding or presentation quotients.
-/

namespace CollapsedFullTarget

open QuotientPathInduction

variable {G₁ : Type u} {G₂ : Type u} {H : Type u}
variable [Add G₁] [Add G₂] [Zero G₁] [Zero G₂]
variable [Subsingleton G₁] [Subsingleton G₂]
variable {i₁ : H → G₁} {i₂ : H → G₂}

theorem word_fullAmalgEquiv_nil :
    ∀ w : FreeProductWord G₁ G₂,
      FullAmalgEquiv i₁ i₂ w .nil
  | .nil => FullAmalgEquiv.refl .nil
  | .consLeft x rest => by
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      exact
        FullAmalgEquiv.trans
          (FullAmalgEquiv.freeGroup
            (FreeProductWord.FreeGroupStep.removeLeftZero rest))
          (word_fullAmalgEquiv_nil rest)
  | .consRight y rest => by
      have hy : y = 0 := Subsingleton.elim _ _
      subst y
      exact
        FullAmalgEquiv.trans
          (FullAmalgEquiv.freeGroup
            (FreeProductWord.FreeGroupStep.removeRightZero rest))
          (word_fullAmalgEquiv_nil rest)

theorem fullAmalgamatedFreeProduct_subsingleton
    (x y : FullAmalgamatedFreeProduct G₁ G₂ H i₁ i₂) :
    x = y := by
  induction x using Quot.ind with
  | _ wx =>
      induction y using Quot.ind with
      | _ wy =>
          exact
            (Quot.sound (word_fullAmalgEquiv_nil (i₁ := i₁) (i₂ := i₂) wx)).trans
              (Quot.sound
                (word_fullAmalgEquiv_nil (i₁ := i₁) (i₂ := i₂) wy)).symm

section Pushout

variable {A : Type u} {B : Type u} {C : Type u}
variable {f : C → A} {g : C → B} (c₀ : C)

noncomputable local instance : Add (π₁(A, f c₀)) := ⟨piOneMul⟩
noncomputable local instance : Zero (π₁(A, f c₀)) :=
  ⟨Quot.mk _ (Path.refl (f c₀))⟩
noncomputable local instance : Add (π₁(B, g c₀)) := ⟨piOneMul⟩
noncomputable local instance : Zero (π₁(B, g c₀)) :=
  ⟨Quot.mk _ (Path.refl (g c₀))⟩

/-- Glue naturality is derivable without an extra assumption once the totality
of `RwEq` is taken into account. -/
noncomputable def hasGlueNaturalLoopRwEq_collapsed :
    Pushout.HasGlueNaturalLoopRwEq
      (A := A) (B := B) (C := C) (f := f) (g := g) c₀ where
  eq := by
    intro c p
    exact
      rweqProp_of_rweq
        (rweq_total
          (Path.trans
            (Path.symm
              (Pushout.inlPath
                (A := A) (B := B) (C := C) (f := f) (g := g)
                (Path.congrArg f p)))
            (Path.trans
              (Pushout.glue
                (A := A) (B := B) (C := C) (f := f) (g := g) c₀)
              (Pushout.inrPath
                (A := A) (B := B) (C := C) (f := f) (g := g)
                (Path.congrArg g p))))
          (Pushout.glue
            (A := A) (B := B) (C := C) (f := f) (g := g) c))

/-- The corrected full-target SVK equivalence is provable under the current
total rewrite quotient.  Both sides are subsingletons, so this theorem records
the formal schema but also its degeneracy. -/
noncomputable def seifertVanKampenFullEquiv_collapsed :
    SimpleEquiv
      (π₁(Pushout A B C f g, Pushout.inl (f c₀)))
      (PushoutFullAmalgamatedFreeProduct
        (A := A) (B := B) (C := C) (f := f) (g := g) c₀) := by
  letI :
      Pushout.HasGlueNaturalLoopRwEq
        (A := A) (B := B) (C := C) (f := f) (g := g) c₀ :=
    hasGlueNaturalLoopRwEq_collapsed
      (A := A) (B := B) (C := C) (f := f) (g := g) c₀
  exact
    { toFun := fun _ => FullAmalgamatedFreeProduct.ofWord .nil
      invFun :=
        pushoutDecodeFullAmalg
          (A := A) (B := B) (C := C) (f := f) (g := g) c₀
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun x =>
        fullAmalgamatedFreeProduct_subsingleton
          (i₁ := piOneFmap c₀) (i₂ := piOneGmap c₀) _ x }

end Pushout

end CollapsedFullTarget

end ComputationalPaths.Path.CompPath.PushoutSVKInstances

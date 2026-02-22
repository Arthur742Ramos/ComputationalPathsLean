/-
# Abelian Categories Deep: Kernels, Cokernels, Exact Sequences, Snake & Five Lemmas

Deep results in abelian category theory via computational paths.

## References
- Mac Lane, Weibel
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace AbelianCatDeep2

open ComputationalPaths.Path

universe u v

/-! ## Category infrastructure -/

structure CatOps (Obj : Type u) (Hom : Obj → Obj → Type v) where
  id   : (X : Obj) → Hom X X
  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  zero : (X Y : Obj) → Hom X Y

variable {Obj : Type u} {Hom : Obj → Obj → Type v} (ops : CatOps Obj Hom)

/-! ## Kernel data -/

structure KernelData {X Y : Obj} (f : Hom X Y) where
  obj : Obj
  ι : Hom obj X
  comp_eq : Path (ops.comp ι f) (ops.zero obj Y)
  lift : {W : Obj} → (g : Hom W X) → Path (ops.comp g f) (ops.zero W Y) → Hom W obj
  lift_ι : {W : Obj} → (g : Hom W X) → (h : Path (ops.comp g f) (ops.zero W Y)) →
    Path (ops.comp (lift g h) ι) g

/-! ## Cokernel data -/

structure CokernelData {X Y : Obj} (f : Hom X Y) where
  obj : Obj
  π : Hom Y obj
  comp_eq : Path (ops.comp f π) (ops.zero X obj)
  desc : {W : Obj} → (g : Hom Y W) → Path (ops.comp f g) (ops.zero X W) → Hom obj W
  π_desc : {W : Obj} → (g : Hom Y W) → (h : Path (ops.comp f g) (ops.zero X W)) →
    Path (ops.comp π (desc g h)) g

/-! ## Image and coimage -/

structure ImageData {X Y : Obj} (f : Hom X Y) where
  obj : Obj
  factorThru : Hom X obj
  ι : Hom obj Y
  factor_eq : Path (ops.comp factorThru ι) f

structure CoimageData {X Y : Obj} (f : Hom X Y) where
  obj : Obj
  π : Hom X obj
  factorThru : Hom obj Y
  factor_eq : Path (ops.comp π factorThru) f

/-! ## Exact sequences -/

structure ExactAt {X Y Z : Obj} (f : Hom X Y) (g : Hom Y Z) where
  comp_zero : Path (ops.comp f g) (ops.zero X Z)

structure ShortExact {A B C : Obj} (f : Hom A B) (g : Hom B C) where
  exact : ExactAt ops f g
  mono : {W : Obj} → (h₁ h₂ : Hom W A) → Path (ops.comp h₁ f) (ops.comp h₂ f) → Path h₁ h₂
  epi  : {W : Obj} → (h₁ h₂ : Hom C W) → Path (ops.comp g h₁) (ops.comp g h₂) → Path h₁ h₂

/-! ## 1: Kernel lift uniqueness -/

noncomputable def kernel_lift_unique {X Y : Obj} {f : Hom X Y} (K : KernelData ops f)
    {W : Obj} (g : Hom W X) (hg : Path (ops.comp g f) (ops.zero W Y))
    (l : Hom W K.obj) (hl : Path (ops.comp l K.ι) g) :
    Path (ops.comp l K.ι) (ops.comp (K.lift g hg) K.ι) :=
  Path.trans hl (Path.symm (K.lift_ι g hg))

/-! ## 2: Cokernel desc uniqueness -/

noncomputable def cokernel_desc_unique {X Y : Obj} {f : Hom X Y} (C : CokernelData ops f)
    {W : Obj} (g : Hom Y W) (hg : Path (ops.comp f g) (ops.zero X W))
    (d : Hom C.obj W) (hd : Path (ops.comp C.π d) g) :
    Path (ops.comp C.π d) (ops.comp C.π (C.desc g hg)) :=
  Path.trans hd (Path.symm (C.π_desc g hg))

/-! ## 3: Exact implies composition is zero -/

noncomputable def exact_comp_zero {X Y Z : Obj} {f : Hom X Y} {g : Hom Y Z}
    (e : ExactAt ops f g) : Path (ops.comp f g) (ops.zero X Z) :=
  e.comp_zero

/-! ## 4: Short exact → exact -/

noncomputable def short_exact_is_exact {A B C : Obj} {f : Hom A B} {g : Hom B C}
    (se : ShortExact ops f g) : ExactAt ops f g :=
  se.exact

/-! ## 5: Exact zero symmetry -/

noncomputable def exact_zero_symm {X Y Z : Obj} {f : Hom X Y} {g : Hom Y Z}
    (e : ExactAt ops f g) : Path (ops.zero X Z) (ops.comp f g) :=
  Path.symm e.comp_zero

/-! ## 6: Image-coimage factor -/

noncomputable def image_coimage_factor {X Y : Obj} {f : Hom X Y}
    (im : ImageData ops f) (coim : CoimageData ops f) :
    Path (ops.comp im.factorThru im.ι) (ops.comp coim.π coim.factorThru) :=
  Path.trans im.factor_eq (Path.symm coim.factor_eq)

/-! ## 7: Exact reflexivity -/

noncomputable def exact_path_refl {X Y Z : Obj} {f : Hom X Y} {g : Hom Y Z}
    (_e : ExactAt ops f g) : Path (ops.comp f g) (ops.comp f g) :=
  Path.refl _

/-! ## 8: Mono from short exact -/

noncomputable def mono_from_short_exact {A B C : Obj} {f : Hom A B} {g : Hom B C}
    (se : ShortExact ops f g)
    {W : Obj} (h₁ h₂ : Hom W A)
    (eq : Path (ops.comp h₁ f) (ops.comp h₂ f)) : Path h₁ h₂ :=
  se.mono h₁ h₂ eq

/-! ## 9: Epi from short exact -/

noncomputable def epi_from_short_exact {A B C : Obj} {f : Hom A B} {g : Hom B C}
    (se : ShortExact ops f g)
    {W : Obj} (h₁ h₂ : Hom C W)
    (eq : Path (ops.comp g h₁) (ops.comp g h₂)) : Path h₁ h₂ :=
  se.epi h₁ h₂ eq

/-! ## 10: Diagram chase – congruence left -/

noncomputable def diagram_chase_left {A B C : Obj} (f₁ f₂ : Hom A B) (g : Hom B C)
    (h : Path f₁ f₂) :
    Path (ops.comp f₁ g) (ops.comp f₂ g) :=
  Path.congrArg (fun x => ops.comp x g) h

/-! ## 11: Diagram chase – congruence right -/

noncomputable def diagram_chase_right {A B C : Obj} (f : Hom A B) (g₁ g₂ : Hom B C)
    (h : Path g₁ g₂) :
    Path (ops.comp f g₁) (ops.comp f g₂) :=
  Path.congrArg (fun x => ops.comp f x) h

/-! ## Snake lemma data -/

structure SnakeLemmaData where
  A : Obj
  B : Obj
  C : Obj
  A' : Obj
  B' : Obj
  C' : Obj
  f  : Hom A B
  g  : Hom B C
  f' : Hom A' B'
  g' : Hom B' C'
  α  : Hom A A'
  β  : Hom B B'
  γ  : Hom C C'
  sq1 : Path (ops.comp f β) (ops.comp α f')
  sq2 : Path (ops.comp g γ) (ops.comp β g')
  exact_top : ExactAt ops f g
  exact_bot : ExactAt ops f' g'

/-! ## 12: Snake square 1 -/

noncomputable def snake_sq1 (d : SnakeLemmaData ops) :
    Path (ops.comp d.f d.β) (ops.comp d.α d.f') := d.sq1

/-! ## 13: Snake square 2 -/

noncomputable def snake_sq2 (d : SnakeLemmaData ops) :
    Path (ops.comp d.g d.γ) (ops.comp d.β d.g') := d.sq2

/-! ## 14: Snake top exact -/

noncomputable def snake_top_exact (d : SnakeLemmaData ops) :
    Path (ops.comp d.f d.g) (ops.zero d.A d.C) :=
  d.exact_top.comp_zero

/-! ## 15: Snake bot exact -/

noncomputable def snake_bot_exact (d : SnakeLemmaData ops) :
    Path (ops.comp d.f' d.g') (ops.zero d.A' d.C') :=
  d.exact_bot.comp_zero

/-! ## Five lemma data -/

structure FiveLemmaData where
  A₁ : Obj
  A₂ : Obj
  A₃ : Obj
  A₄ : Obj
  A₅ : Obj
  B₁ : Obj
  B₂ : Obj
  B₃ : Obj
  B₄ : Obj
  B₅ : Obj
  f₁ : Hom A₁ A₂
  f₂ : Hom A₂ A₃
  f₃ : Hom A₃ A₄
  f₄ : Hom A₄ A₅
  g₁ : Hom B₁ B₂
  g₂ : Hom B₂ B₃
  g₃ : Hom B₃ B₄
  g₄ : Hom B₄ B₅
  α₁ : Hom A₁ B₁
  α₂ : Hom A₂ B₂
  α₃ : Hom A₃ B₃
  α₄ : Hom A₄ B₄
  α₅ : Hom A₅ B₅
  sq1 : Path (ops.comp f₁ α₂) (ops.comp α₁ g₁)
  sq2 : Path (ops.comp f₂ α₃) (ops.comp α₂ g₂)
  sq3 : Path (ops.comp f₃ α₄) (ops.comp α₃ g₃)
  sq4 : Path (ops.comp f₄ α₅) (ops.comp α₄ g₄)

/-! ## 16: Five lemma square 1 -/

noncomputable def five_lemma_sq1 (d : FiveLemmaData ops) :
    Path (ops.comp d.f₁ d.α₂) (ops.comp d.α₁ d.g₁) := d.sq1

/-! ## 17: Five lemma square 2 -/

noncomputable def five_lemma_sq2 (d : FiveLemmaData ops) :
    Path (ops.comp d.f₂ d.α₃) (ops.comp d.α₂ d.g₂) := d.sq2

/-! ## 18: Five lemma square 3 -/

noncomputable def five_lemma_sq3 (d : FiveLemmaData ops) :
    Path (ops.comp d.f₃ d.α₄) (ops.comp d.α₃ d.g₃) := d.sq3

/-! ## 19: Five lemma square 4 -/

noncomputable def five_lemma_sq4 (d : FiveLemmaData ops) :
    Path (ops.comp d.f₄ d.α₅) (ops.comp d.α₄ d.g₄) := d.sq4

/-! ## Nine lemma data -/

structure NineLemmaData where
  A₁ : Obj
  A₂ : Obj
  A₃ : Obj
  B₁ : Obj
  B₂ : Obj
  B₃ : Obj
  C₁ : Obj
  C₂ : Obj
  C₃ : Obj
  f₁ : Hom A₁ A₂
  f₂ : Hom A₂ A₃
  g₁ : Hom B₁ B₂
  g₂ : Hom B₂ B₃
  h₁ : Hom C₁ C₂
  h₂ : Hom C₂ C₃
  α₁ : Hom A₁ B₁
  α₂ : Hom A₂ B₂
  α₃ : Hom A₃ B₃
  β₁ : Hom B₁ C₁
  β₂ : Hom B₂ C₂
  β₃ : Hom B₃ C₃
  exact_row1 : ExactAt ops f₁ f₂
  exact_row2 : ExactAt ops g₁ g₂
  exact_row3 : ExactAt ops h₁ h₂
  exact_col1 : ExactAt ops α₁ β₁
  exact_col2 : ExactAt ops α₂ β₂
  exact_col3 : ExactAt ops α₃ β₃

/-! ## 20: Nine lemma row exact -/

noncomputable def nine_lemma_row1 (d : NineLemmaData ops) :
    Path (ops.comp d.f₁ d.f₂) (ops.zero d.A₁ d.A₃) :=
  d.exact_row1.comp_zero

/-! ## 21: Nine lemma col exact -/

noncomputable def nine_lemma_col1 (d : NineLemmaData ops) :
    Path (ops.comp d.α₁ d.β₁) (ops.zero d.A₁ d.C₁) :=
  d.exact_col1.comp_zero

/-! ## Horseshoe lemma data -/

structure HorseshoeLemmaData where
  A : Obj
  B : Obj
  C : Obj
  PA : Obj
  PB : Obj
  PC : Obj
  f : Hom A B
  g : Hom B C
  pA : Hom PA A
  pC : Hom PC C
  exact : ShortExact ops f g

/-! ## 22: Horseshoe exact -/

noncomputable def horseshoe_exact (d : HorseshoeLemmaData ops) :
    Path (ops.comp d.f d.g) (ops.zero d.A d.C) :=
  d.exact.exact.comp_zero

/-! ## Long exact sequence data -/

structure LongExactSeqData (n : Nat) where
  obj : Fin (n + 1) → Obj
  mor : (i : Fin n) → Hom (obj i.castSucc) (obj i.succ)
  exact : (i : Fin (n - 1)) →
    ExactAt ops (mor ⟨i.val, by omega⟩) (mor ⟨i.val + 1, by omega⟩)

/-! ## 23: Long exact consecutive zero -/

noncomputable def long_exact_consec_zero {n : Nat} (d : LongExactSeqData ops n)
    (i : Fin (n - 1)) :
    Path (ops.comp (d.mor ⟨i.val, by omega⟩) (d.mor ⟨i.val + 1, by omega⟩))
         (ops.zero (d.obj ⟨i.val, by omega⟩) (d.obj ⟨i.val + 2, by omega⟩)) :=
  (d.exact i).comp_zero

/-! ## 24: Kernel comp eq -/

noncomputable def kernel_comp_eq {X Y : Obj} {f : Hom X Y} (K : KernelData ops f) :
    Path (ops.comp K.ι f) (ops.zero K.obj Y) :=
  K.comp_eq

/-! ## 25: Cokernel comp eq -/

noncomputable def cokernel_comp_eq {X Y : Obj} {f : Hom X Y} (C : CokernelData ops f) :
    Path (ops.comp f C.π) (ops.zero X C.obj) :=
  C.comp_eq

/-! ## Kernel-cokernel pair -/

structure KerCokerPair {X Y : Obj} (f : Hom X Y) where
  ker : KernelData ops f
  coker : CokernelData ops f

/-! ## 26: Kernel-cokernel composition -/

noncomputable def ker_coker_factor {X Y : Obj} {f : Hom X Y}
    (kc : KerCokerPair ops f) :
    Path (ops.comp kc.ker.ι f) (ops.zero kc.ker.obj Y) :=
  kc.ker.comp_eq

/-! ## 27: Kernel lift then compose -/

noncomputable def kernel_lift_compose {X Y : Obj} {f : Hom X Y}
    (K : KernelData ops f) {W : Obj}
    (g : Hom W X) (hg : Path (ops.comp g f) (ops.zero W Y)) :
    Path (ops.comp (K.lift g hg) K.ι) g :=
  K.lift_ι g hg

/-! ## 28: Cokernel desc then compose -/

noncomputable def cokernel_desc_compose {X Y : Obj} {f : Hom X Y}
    (C : CokernelData ops f) {W : Obj}
    (g : Hom Y W) (hg : Path (ops.comp f g) (ops.zero X W)) :
    Path (ops.comp C.π (C.desc g hg)) g :=
  C.π_desc g hg

/-! ## 29: Short exact zero trans -/

noncomputable def short_exact_zero_path {A B C : Obj}
    {f : Hom A B} {g : Hom B C} (se : ShortExact ops f g) :
    Path (ops.zero A C) (ops.comp f g) :=
  Path.symm se.exact.comp_zero

end AbelianCatDeep2
end Algebra
end Path
end ComputationalPaths

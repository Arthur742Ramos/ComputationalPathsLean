/-
# Abelian Category Data via Computational Paths

This module packages kernels, cokernels, images, and exact sequences using
`Path`-witnessed universal properties, keeping the setup lightweight and
fully proved.

## Key Definitions

- `CategoryOps`, `KernelData`, `CokernelData`, `ImageData`
- `ExactSequenceData`, `SnakeLemmaData`, `FiveLemmaData`

## References

- Mac Lane, "Categories for the Working Mathematician"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u v

/-! ## Core Category Operations -/

/-- Minimal category operations with a zero morphism. -/
structure CategoryOps (Obj : Type u) (Hom : Obj → Obj → Type v) where
  id : (X : Obj) → Hom X X
  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  zero : (X Y : Obj) → Hom X Y

/-! ## Kernels and Cokernels -/

/-- Kernel data with a Path-witnessed universal property. -/
structure KernelData {Obj : Type u} {Hom : Obj → Obj → Type v}
    (ops : CategoryOps Obj Hom) {X Y : Obj} (f : Hom X Y) where
  obj : Obj
  kernelIn : Hom obj X
  comp_zero : Path (ops.comp kernelIn f) (ops.zero obj Y)
  lift : ∀ {Z : Obj} (g : Hom Z X),
    Path (ops.comp g f) (ops.zero Z Y) → Hom Z obj
  lift_comp : ∀ {Z : Obj} (g : Hom Z X)
      (h : Path (ops.comp g f) (ops.zero Z Y)),
    Path (ops.comp (lift g h) kernelIn) g

/-- Cokernel data with a Path-witnessed universal property. -/
structure CokernelData {Obj : Type u} {Hom : Obj → Obj → Type v}
    (ops : CategoryOps Obj Hom) {X Y : Obj} (f : Hom X Y) where
  obj : Obj
  cokernelOut : Hom Y obj
  zero_comp : Path (ops.comp f cokernelOut) (ops.zero X obj)
  desc : ∀ {Z : Obj} (g : Hom Y Z),
    Path (ops.comp f g) (ops.zero X Z) → Hom obj Z
  desc_comp : ∀ {Z : Obj} (g : Hom Y Z)
      (h : Path (ops.comp f g) (ops.zero X Z)),
    Path (ops.comp cokernelOut (desc g h)) g

/-! ## Images and Exact Sequences -/

/-- Image data as a factorization of a morphism. -/
structure ImageData {Obj : Type u} {Hom : Obj → Obj → Type v}
    (ops : CategoryOps Obj Hom) {X Y : Obj} (f : Hom X Y) where
  obj : Obj
  factor : Hom X obj
  imageIn : Hom obj Y
  factor_comp : Path (ops.comp factor imageIn) f

/-- Exact sequence data for X -f→ Y -g→ Z. -/
structure ExactSequenceData {Obj : Type u} {Hom : Obj → Obj → Type v}
    (ops : CategoryOps Obj Hom) {X Y Z : Obj} (f : Hom X Y) (g : Hom Y Z) where
  comp_zero : Path (ops.comp f g) (ops.zero X Z)
  kernel : KernelData ops g
  image : ImageData ops f
  toKernel : Hom image.obj kernel.obj
  toKernel_comp : Path (ops.comp toKernel kernel.kernelIn) image.imageIn

/-! ## Snake Lemma Data -/

/-- Data for the snake lemma connecting morphism. -/
structure SnakeLemmaData {Obj : Type u} {Hom : Obj → Obj → Type v}
    (ops : CategoryOps Obj Hom) where
  A₁ : Obj
  A₂ : Obj
  A₃ : Obj
  B₁ : Obj
  B₂ : Obj
  B₃ : Obj
  f₁ : Hom A₁ A₂
  f₂ : Hom A₂ A₃
  g₁ : Hom B₁ B₂
  g₂ : Hom B₂ B₃
  α₁ : Hom A₁ B₁
  α₂ : Hom A₂ B₂
  α₃ : Hom A₃ B₃
  comm_left : Path (ops.comp f₁ α₂) (ops.comp α₁ g₁)
  comm_right : Path (ops.comp f₂ α₃) (ops.comp α₂ g₂)

/-! ## Five Lemma Data -/

/-- Row data for the five lemma. -/
structure FiveRow (Obj : Type u) (Hom : Obj → Obj → Type v) where
  X₁ : Obj
  X₂ : Obj
  X₃ : Obj
  X₄ : Obj
  X₅ : Obj
  d₁ : Hom X₁ X₂
  d₂ : Hom X₂ X₃
  d₃ : Hom X₃ X₄
  d₄ : Hom X₄ X₅

/-- Five lemma data: two rows with vertical comparisons. -/
structure FiveLemmaData {Obj : Type u} {Hom : Obj → Obj → Type v}
    (ops : CategoryOps Obj Hom) where
  top : FiveRow Obj Hom
  bot : FiveRow Obj Hom
  v₁ : Hom top.X₁ bot.X₁
  v₂ : Hom top.X₂ bot.X₂
  v₃ : Hom top.X₃ bot.X₃
  v₄ : Hom top.X₄ bot.X₄
  v₅ : Hom top.X₅ bot.X₅
  comm₁ : Path (ops.comp top.d₁ v₂) (ops.comp v₁ bot.d₁)
  comm₂ : Path (ops.comp top.d₂ v₃) (ops.comp v₂ bot.d₂)
  comm₃ : Path (ops.comp top.d₃ v₄) (ops.comp v₃ bot.d₃)
  comm₄ : Path (ops.comp top.d₄ v₅) (ops.comp v₄ bot.d₄)

/-! ## Trivial PUnit Instances -/

private def pp : Path (a : PUnit) (b : PUnit) := by
  cases a; cases b; exact Path.refl _

private def pOps : CategoryOps PUnit (fun _ _ => PUnit) where
  id := fun _ => .unit
  comp := fun _ _ => .unit
  zero := fun _ _ => .unit

def punitKernelData :
    KernelData (ops := pOps) (X := PUnit.unit) (Y := PUnit.unit) PUnit.unit where
  obj := .unit
  kernelIn := .unit
  comp_zero := pp
  lift := fun _ _ => .unit
  lift_comp := fun _ _ => pp

def punitCokernelData :
    CokernelData (ops := pOps) (X := PUnit.unit) (Y := PUnit.unit) PUnit.unit where
  obj := .unit
  cokernelOut := .unit
  zero_comp := pp
  desc := fun _ _ => .unit
  desc_comp := fun _ _ => pp

def punitImageData :
    ImageData (ops := pOps) (X := PUnit.unit) (Y := PUnit.unit) PUnit.unit where
  obj := .unit
  factor := .unit
  imageIn := .unit
  factor_comp := pp

def punitExactData :
    ExactSequenceData (ops := pOps)
      (X := PUnit.unit) (Y := PUnit.unit) (Z := PUnit.unit) .unit .unit where
  comp_zero := pp
  kernel := punitKernelData
  image := punitImageData
  toKernel := .unit
  toKernel_comp := pp

end Algebra
end Path
end ComputationalPaths

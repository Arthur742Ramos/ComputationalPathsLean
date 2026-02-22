/-
# Quotient Constructions on Path Algebras

This module formalizes quotient constructions on fundamental groups: group
homomorphisms, kernel, and the first isomorphism theorem.

## Key Results

- `PiOneHom`: group homomorphisms of π₁
- `PiOneHom.map_id`: preserves identity
- `PiOneHom.map_inv`: preserves inverses
- `PiOneHom.kernelNormal`: kernel is a normal subgroup
- `KernelQuot`: quotient by the kernel
- `firstIsoTheorem`: injectivity of the first iso map

## References

- Lang, "Algebra"
-/

import ComputationalPaths.Path.Homotopy.FundamentalGroup

set_option maxHeartbeats 400000

namespace ComputationalPaths
namespace Path
namespace PathAlgebraQuotient

universe u

variable {A B : Type u}

/-! ## Normal subgroups of π₁ -/

/-- A normal subgroup of π₁(A, a). -/
structure NormalSubgroup (A : Type u) (a : A) where
  mem : π₁(A, a) → Prop
  mem_id : mem PiOne.id
  mem_mul : ∀ {x y}, mem x → mem y → mem (PiOne.mul x y)
  mem_inv : ∀ {x}, mem x → mem (PiOne.inv x)
  mem_conj : ∀ (g : π₁(A, a)) {n}, mem n →
    mem (PiOne.mul (PiOne.mul g n) (PiOne.inv g))

/-! ## Group homomorphisms -/

/-- A group homomorphism between fundamental groups. -/
structure PiOneHom (A : Type u) (a : A) (B : Type u) (b : B) where
  toFun : π₁(A, a) → π₁(B, b)
  map_mul : ∀ x y, toFun (PiOne.mul x y) = PiOne.mul (toFun x) (toFun y)

namespace PiOneHom

variable {a : A} {b : B}

/-- A homomorphism preserves the identity. -/
theorem map_id (f : PiOneHom A a B b) : f.toFun PiOne.id = PiOne.id := by
  have h := f.map_mul PiOne.id PiOne.id
  have h2 : PiOne.mul PiOne.id PiOne.id = (PiOne.id : π₁(A, a)) := PiOne.id_mul _
  rw [h2] at h
  -- h : f(id) = f(id) * f(id)
  have h3 : PiOne.mul (f.toFun PiOne.id) (PiOne.inv (f.toFun PiOne.id)) =
    PiOne.mul (PiOne.mul (f.toFun PiOne.id) (f.toFun PiOne.id))
      (PiOne.inv (f.toFun PiOne.id)) := by rw [← h]
  rw [PiOne.mul_right_inv, PiOne.mul_assoc, PiOne.mul_right_inv, PiOne.mul_id] at h3
  exact h3.symm

/-- A homomorphism preserves inverses. -/
theorem map_inv (f : PiOneHom A a B b) (x : π₁(A, a)) :
    f.toFun (PiOne.inv x) = PiOne.inv (f.toFun x) := by
  have h1 : PiOne.mul (PiOne.inv x) x = (PiOne.id : π₁(A, a)) := by simp
  have h2 : f.toFun (PiOne.mul (PiOne.inv x) x) = f.toFun PiOne.id := by
    rw [h1]
  rw [f.map_mul] at h2
  rw [f.map_id] at h2
  -- h2 : f(x⁻¹) * f(x) = id
  calc f.toFun (PiOne.inv x)
      = PiOne.mul (f.toFun (PiOne.inv x)) PiOne.id := by simp
    _ = PiOne.mul (f.toFun (PiOne.inv x))
          (PiOne.mul (f.toFun x) (PiOne.inv (f.toFun x))) := by simp
    _ = PiOne.mul (PiOne.mul (f.toFun (PiOne.inv x)) (f.toFun x))
          (PiOne.inv (f.toFun x)) := by rw [PiOne.mul_assoc]
    _ = PiOne.mul PiOne.id (PiOne.inv (f.toFun x)) := by rw [h2]
    _ = PiOne.inv (f.toFun x) := by simp

/-- The kernel of a homomorphism. -/
noncomputable def kernel (f : PiOneHom A a B b) (x : π₁(A, a)) : Prop :=
  f.toFun x = PiOne.id

theorem kernel_id (f : PiOneHom A a B b) : f.kernel PiOne.id := f.map_id

theorem kernel_mul (f : PiOneHom A a B b) {x y : π₁(A, a)}
    (hx : f.kernel x) (hy : f.kernel y) :
    f.kernel (PiOne.mul x y) := by
  unfold kernel
  rw [f.map_mul, hx, hy]; simp

theorem kernel_inv (f : PiOneHom A a B b) {x : π₁(A, a)}
    (hx : f.kernel x) :
    f.kernel (PiOne.inv x) := by
  unfold kernel
  rw [f.map_inv, hx]
  exact LoopQuot.inv_id

/-- The kernel is a normal subgroup. -/
noncomputable def kernelNormal (f : PiOneHom A a B b) : NormalSubgroup A a where
  mem := f.kernel
  mem_id := f.kernel_id
  mem_mul := fun hx hy => f.kernel_mul hx hy
  mem_inv := fun hx => f.kernel_inv hx
  mem_conj := by
    intro g n hn
    unfold kernel
    rw [f.map_mul, f.map_mul, f.map_inv, hn]; simp

end PiOneHom

/-! ## Quotient by kernel -/

/-- Two elements are in the same kernel coset. -/
noncomputable def kernelCoset {a : A} {b : B} (f : PiOneHom A a B b)
    (x y : π₁(A, a)) : Prop :=
  f.toFun x = f.toFun y

/-- The quotient of π₁ by the kernel. -/
noncomputable def KernelQuot {a : A} {b : B} (f : PiOneHom A a B b) : Type u :=
  Quot (kernelCoset f)

namespace KernelQuot

variable {a : A} {b : B} (f : PiOneHom A a B b)

/-- Projection. -/
noncomputable def proj : π₁(A, a) → KernelQuot f := Quot.mk _

/-- The identity element. -/
noncomputable def id : KernelQuot f := proj f PiOne.id

/-- The first isomorphism map. -/
noncomputable def isoMap : KernelQuot f → π₁(B, b) :=
  Quot.lift f.toFun (fun _ _ h => h)

/-- The iso map is injective. -/
theorem isoMap_injective (x y : KernelQuot f)
    (h : isoMap f x = isoMap f y) : x = y := by
  induction x using Quot.ind with
  | _ p =>
    induction y using Quot.ind with
    | _ q => exact Quot.sound h

/-- The iso map preserves identity. -/
@[simp] theorem isoMap_id : isoMap f (id f) = PiOne.id := f.map_id

/-- The iso map preserves multiplication on projections. -/
theorem isoMap_proj_mul (x y : π₁(A, a)) :
    isoMap f (proj f (PiOne.mul x y)) =
      PiOne.mul (isoMap f (proj f x)) (isoMap f (proj f y)) :=
  f.map_mul x y

end KernelQuot

/-! ## First isomorphism theorem -/

/-- First isomorphism theorem: `π₁/ker(f)` injects into `π₁(B,b)`. -/
theorem firstIsoTheorem {a : A} {b : B} (f : PiOneHom A a B b) :
    ∀ x y : KernelQuot f,
      KernelQuot.isoMap f x = KernelQuot.isoMap f y → x = y :=
  KernelQuot.isoMap_injective f

/-- Surjectivity onto the image. -/
theorem firstIsoTheorem_surj {a : A} {b : B} (f : PiOneHom A a B b)
    (y : π₁(B, b)) (hy : ∃ x : π₁(A, a), f.toFun x = y) :
    ∃ q : KernelQuot f, KernelQuot.isoMap f q = y := by
  obtain ⟨x, hx⟩ := hy
  exact ⟨KernelQuot.proj f x, hx⟩

end PathAlgebraQuotient
end Path
end ComputationalPaths

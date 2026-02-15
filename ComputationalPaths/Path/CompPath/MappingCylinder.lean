/-
# Mapping cylinder via computational paths

This module defines the mapping cylinder of a map `f : A → B` using the
computational pushout construction. The mapping cylinder is the pushout of
the cylinder `A × Interval` and `B` along `A`, where `A` includes into the
cylinder at the left endpoint of the interval.

## Key Results

- `Interval`: two-point interval type
- `Cylinder`: product `A × Interval`
- `MappingCylinder`: mapping cylinder as a pushout
- `MappingCylinder.inCylinder` and `MappingCylinder.inTarget`: canonical inclusions
- `MappingCylinder.bottom`, `MappingCylinder.top`: endpoint embeddings of `A`
- `MappingCylinder.glue`: path identifying the bottom with `f`

## References

- HoTT Book, Chapter 6 (mapping cylinders)
- Computational paths pushout construction
-/

import ComputationalPaths.Path.CompPath.PushoutCompPath

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u

/-! ## Interval and cylinder -/

/-- The interval with two endpoints. -/
inductive Interval : Type u
  | /-- Left endpoint. -/ left : Interval
  | /-- Right endpoint. -/ right : Interval

/-- The cylinder over `A`, defined as `A × Interval`. -/
abbrev Cylinder (A : Type u) : Type u := A × Interval

/-! ## Mapping cylinder -/

variable {A B : Type u}

/-- The mapping cylinder of `f : A → B`. -/
def MappingCylinder (f : A → B) : Type u :=
  Pushout (Cylinder A) B A (fun a => (a, Interval.left)) f

@[simp] theorem mappingCylinder_def (f : A → B) :
    MappingCylinder f = Pushout (Cylinder A) B A (fun a => (a, Interval.left)) f := by
  rfl

namespace MappingCylinder

variable {A B : Type u} (f : A → B)

/-- Include the cylinder into the mapping cylinder. -/
def inCylinder : Cylinder A → MappingCylinder f :=
  Pushout.inl (A := Cylinder A) (B := B) (C := A)
    (f := fun a => (a, Interval.left)) (g := f)

/-- Include the target `B` into the mapping cylinder. -/
def inTarget : B → MappingCylinder f :=
  Pushout.inr (A := Cylinder A) (B := B) (C := A)
    (f := fun a => (a, Interval.left)) (g := f)

/-- The bottom embedding of `A` at the left endpoint. -/
def bottom (a : A) : MappingCylinder f :=
  inCylinder (f := f) (a, Interval.left)

/-- The top embedding of `A` at the right endpoint. -/
def top (a : A) : MappingCylinder f :=
  inCylinder (f := f) (a, Interval.right)

/-- The gluing path identifying `bottom a` with `f a` in the mapping cylinder. -/
def glue (a : A) :
    Path (bottom (f := f) a) (inTarget (f := f) (f a)) :=
  Pushout.glue (A := Cylinder A) (B := B) (C := A)
    (f := fun a => (a, Interval.left)) (g := f) a

@[simp] theorem inCylinder_def :
    inCylinder (f := f) =
      Pushout.inl (A := Cylinder A) (B := B) (C := A)
        (f := fun a => (a, Interval.left)) (g := f) := by
  rfl

@[simp] theorem inTarget_def :
    inTarget (f := f) =
      Pushout.inr (A := Cylinder A) (B := B) (C := A)
        (f := fun a => (a, Interval.left)) (g := f) := by
  rfl

@[simp] theorem bottom_def (a : A) :
    bottom (f := f) a = inCylinder (f := f) (a, Interval.left) := by
  rfl

@[simp] theorem top_def (a : A) :
    top (f := f) a = inCylinder (f := f) (a, Interval.right) := by
  rfl

@[simp] theorem glue_def (a : A) :
    glue (f := f) a =
      Pushout.glue (A := Cylinder A) (B := B) (C := A)
        (f := fun a => (a, Interval.left)) (g := f) a := by
  rfl

theorem inCylinder_congr {x y : Cylinder A} (p : Path x y) :
    Path.congrArg (inCylinder (f := f)) p =
      Path.congrArg
        (Pushout.inl (A := Cylinder A) (B := B) (C := A)
          (f := fun a => (a, Interval.left)) (g := f)) p := by
  rfl

theorem inTarget_congr {b b' : B} (q : Path b b') :
    Path.congrArg (inTarget (f := f)) q =
      Path.congrArg
        (Pushout.inr (A := Cylinder A) (B := B) (C := A)
          (f := fun a => (a, Interval.left)) (g := f)) q := by
  rfl

theorem bottom_congr {a a' : A} (p : Path a a') :
    Path.congrArg (bottom (f := f)) p =
      Path.congrArg (inCylinder (f := f))
        (Path.congrArg (fun x => (x, Interval.left)) p) := by
  exact Path.congrArg_comp (inCylinder (f := f)) (fun x => (x, Interval.left)) p

theorem top_congr {a a' : A} (p : Path a a') :
    Path.congrArg (top (f := f)) p =
      Path.congrArg (inCylinder (f := f))
        (Path.congrArg (fun x => (x, Interval.right)) p) := by
  exact Path.congrArg_comp (inCylinder (f := f)) (fun x => (x, Interval.right)) p

theorem glue_comp_assoc {a : A} {x y : MappingCylinder f}
    (q : Path (inTarget (f := f) (f a)) x) (r : Path x y) :
    Path.trans (Path.trans (glue (f := f) a) q) r =
      Path.trans (glue (f := f) a) (Path.trans q r) :=
  Path.trans_assoc _ q r

theorem glue_trans_refl_left (a : A) :
    Path.trans (Path.refl (bottom (f := f) a)) (glue (f := f) a) = glue (f := f) a :=
  Path.trans_refl_left _

theorem glue_trans_refl_right (a : A) :
    Path.trans (glue (f := f) a) (Path.refl (inTarget (f := f) (f a))) = glue (f := f) a :=
  Path.trans_refl_right _

-- Note: glue_trans_symm and glue_symm_trans claim
-- `Path.trans p (Path.symm p) = Path.refl _` which requires the steps list
-- `p.steps ++ (p.steps.reverse.map Step.symm)` to equal `[]`.
-- This is only true when p.steps is empty, not for arbitrary glue paths.
-- These statements are removed as unprovable.

end MappingCylinder

/-! ## Summary -/

end CompPath
end Path
end ComputationalPaths

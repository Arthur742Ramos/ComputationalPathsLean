/-
# Normalization of computational paths

Defines normal forms for `Path` by collapsing to the canonical witness of the
underlying propositional equality.

## Key Results

- `IsNormal` and `normalize`
- `NormalForm` and `normalizeForm`
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path

universe u

variable {A : Type u} {a b : A}

/-! ## Normal forms and normalization -/

def IsNormal {A : Type u} {a b : A} (p : Path a b) : Prop :=
  p = Path.ofEq p.toEq

@[simp] theorem isNormal_iff {A : Type u} {a b : A} (p : Path a b) :
    IsNormal (A := A) (a := a) (b := b) p ↔ p = Path.ofEq p.toEq :=
  Iff.rfl

@[simp] theorem isNormal_ofEq {A : Type u} {a b : A} (h : a = b) :
    IsNormal (A := A) (a := a) (b := b) (Path.ofEq (A := A) (a := a) (b := b) h) := by
  unfold IsNormal
  simp

@[simp] def normalize {A : Type u} {a b : A} (p : Path a b) : Path a b :=
  Path.ofEq (A := A) (a := a) (b := b) p.toEq

@[simp] theorem normalize_isNormal {A : Type u} {a b : A}
    (p : Path a b) :
    IsNormal (A := A) (a := a) (b := b) (normalize p) := by
  unfold normalize IsNormal
  simp

structure NormalForm (A : Type u) (a b : A) where
  path : Path a b
  isNormal : IsNormal (A := A) (a := a) (b := b) path

@[simp] def normalizeForm {A : Type u} {a b : A}
    (p : Path a b) : NormalForm A a b :=
  { path := normalize p
    isNormal := normalize_isNormal (A := A) (a := a) (b := b) p }

@[simp] theorem normalizeForm_path {A : Type u} {a b : A}
    (p : Path a b) :
    (normalizeForm (A := A) (a := a) (b := b) p).path = normalize p := rfl

end Path
end ComputationalPaths

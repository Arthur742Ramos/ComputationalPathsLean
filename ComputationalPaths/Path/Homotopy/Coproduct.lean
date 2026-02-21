/-
# Coproduct (Sum) Path Characterization

This file characterizes the path space of coproducts (sums).

## Key Results

1. `(Sum.inl a₀ = Sum.inl a) ≃ (a₀ = a)` - paths between inl values
2. `(Sum.inr b₀ = Sum.inr b) ≃ (b₀ = b)` - paths between inr values
3. `(Sum.inl a = Sum.inr b) ≃ Empty` - no paths between different injections

## Implementation

These follow from the structure of `Path`:
- `Path (Sum.inl a₀) (Sum.inl a)` requires a proof `Sum.inl a₀ = Sum.inl a`
- This is equivalent to `a₀ = a` by `Sum.inl.injEq`
- `Path (Sum.inl a) (Sum.inr b)` would require `Sum.inl a = Sum.inr b`, which is impossible
-/

import ComputationalPaths.Path.Homotopy.Sets

namespace ComputationalPaths.Path

universe u

variable {A : Type u} {B : Type u}

/-- Helper: Sum.inl a ≠ Sum.inr b -/
private theorem sum_inl_ne_inr (a : A) (b : B) : Sum.inl a ≠ Sum.inr b := fun h => nomatch h

/-- Helper: Sum.inr b ≠ Sum.inl a -/
private theorem sum_inr_ne_inl (b : B) (a : A) : Sum.inr b ≠ Sum.inl a := fun h => nomatch h

/-- The code family for characterizing paths in Sum A B from Sum.inl a₀.
    code(inl a) = (a₀ = a)
    code(inr b) = PEmpty (universe-polymorphic empty type) -/
def sumCode (a₀ : A) : Sum A B → Type u
  | Sum.inl a => Path a₀ a
  | Sum.inr _ => PEmpty.{u+1}

/-- encode: (Sum.inl a₀ = x) → code(x)
    For x = inl a, we extract the underlying path
    For x = inr b, this case is impossible -/
def sumEncode {a₀ : A} {x : Sum A B} (p : Path (Sum.inl a₀) x) : sumCode a₀ x := by
  cases x with
  | inl a =>
      -- p : Path (Sum.inl a₀) (Sum.inl a)
      -- We need Path a₀ a
      -- p.toEq : Sum.inl a₀ = Sum.inl a
      exact Path.stepChain (Sum.inl.injEq a₀ a ▸ p.toEq)
  | inr b =>
      -- p : Path (Sum.inl a₀) (Sum.inr b)
      -- p.toEq : Sum.inl a₀ = Sum.inr b, which is impossible
      exact absurd p.toEq (sum_inl_ne_inr a₀ b)

/-- decode: code(x) → (Sum.inl a₀ = x)
    For x = inl a, we lift the path via congrArg
    For x = inr b, code is PEmpty so this is vacuously true -/
def sumDecode {a₀ : A} {x : Sum A B} (c : sumCode a₀ x) : Path (Sum.inl a₀ : Sum A B) x := by
  cases x with
  | inl a => exact inlCongr c
  | inr _ => exact c.elim

/-- Similarly for inr values -/
def sumCodeR (b₀ : B) : Sum A B → Type u
  | Sum.inl _ => PEmpty.{u+1}
  | Sum.inr b => Path b₀ b

def sumEncodeR {b₀ : B} {x : Sum A B} (p : Path (Sum.inr b₀ : Sum A B) x) : sumCodeR b₀ x := by
  cases x with
  | inl a => exact absurd p.toEq (sum_inr_ne_inl b₀ a)
  | inr b => exact Path.stepChain (Sum.inr.injEq b₀ b ▸ p.toEq)

def sumDecodeR {b₀ : B} {x : Sum A B} (c : sumCodeR b₀ x) : Path (Sum.inr b₀ : Sum A B) x := by
  cases x with
  | inl _ => exact c.elim
  | inr b => exact inrCongr c

/-- `sumDecode` preserves `RwEq` (by functoriality of `congrArg`). -/
noncomputable def sumDecode_respects_rweq (a₀ a : A) {c₁ c₂ : Path a₀ a} (h : RwEq c₁ c₂) :
    RwEq (sumDecode (a₀ := a₀) (x := (Sum.inl a : Sum A B)) c₁)
      (sumDecode (a₀ := a₀) (x := (Sum.inl a : Sum A B)) c₂) := by
  simpa [sumDecode] using
    (rweq_congrArg_of_rweq (A := A) (B := Sum A B) Sum.inl h)

/-- `sumDecodeR` preserves `RwEq` (by functoriality of `congrArg`). -/
noncomputable def sumDecodeR_respects_rweq (b₀ b : B) {c₁ c₂ : Path b₀ b} (h : RwEq c₁ c₂) :
    RwEq (sumDecodeR (b₀ := b₀) (x := (Sum.inr b : Sum A B)) c₁)
      (sumDecodeR (b₀ := b₀) (x := (Sum.inr b : Sum A B)) c₂) := by
  simpa [sumDecodeR] using
    (rweq_congrArg_of_rweq (A := B) (B := Sum A B) Sum.inr h)

/-- No paths between inl and inr (the path type is uninhabited) -/
theorem sum_inl_inr_path_empty (a : A) (b : B) (p : Path (Sum.inl a : Sum A B) (Sum.inr b)) :
    False :=
  absurd p.toEq (sum_inl_ne_inr a b)

/-- No paths between inr and inl (the path type is uninhabited) -/
theorem sum_inr_inl_path_empty (a : A) (b : B) (p : Path (Sum.inr b : Sum A B) (Sum.inl a)) :
    False :=
  absurd p.toEq (sum_inr_ne_inl b a)

end ComputationalPaths.Path

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
      exact Path.ofEq (Sum.inl.injEq a₀ a ▸ p.toEq)
  | inr b =>
      -- p : Path (Sum.inl a₀) (Sum.inr b)
      -- p.toEq : Sum.inl a₀ = Sum.inr b, which is impossible
      exact absurd p.toEq (Sum.noConfusion)

/-- decode: code(x) → (Sum.inl a₀ = x)
    For x = inl a, we lift the path via congrArg
    For x = inr b, code is PEmpty so this is vacuously true -/
def sumDecode {a₀ : A} {x : Sum A B} (c : sumCode a₀ x) : Path (Sum.inl a₀ : Sum A B) x := by
  cases x with
  | inl a => exact inlCongr c
  | inr _ => exact c.elim

/-- Paths in Sum between inl values correspond to paths in A.

This establishes `(Sum.inl a₀ = Sum.inl a) ≃ (a₀ = a)` at the type level:
- `sumEncode` extracts a path in A from a path in Sum
- `sumDecode` lifts a path in A to a path in Sum via `inlCongr`

The composition produces paths that are RwEq (not definitionally equal
due to different step lists). -/
theorem sumEncode_decode_rweq (a₀ a : A) (c : Path a₀ a) :
    RwEq (sumEncode (sumDecode c : Path (Sum.inl a₀ : Sum A B) (Sum.inl a))) c := by
  simp only [sumEncode]
  -- Both produce paths with the same underlying proof, hence RwEq via rweq_canon
  apply rweq_trans (rweq_canon _)
  apply rweq_symm (rweq_canon _)

theorem sumDecode_encode_rweq (a₀ a : A) (p : Path (Sum.inl a₀ : Sum A B) (Sum.inl a)) :
    RwEq (sumDecode (sumEncode p)) p := by
  simp only [sumDecode, sumEncode]
  -- Both paths have the same .toEq, so RwEq via rweq_canon
  apply rweq_trans (rweq_canon _)
  apply rweq_symm (rweq_canon _)

/-- Similarly for inr values -/
def sumCodeR (b₀ : B) : Sum A B → Type u
  | Sum.inl _ => PEmpty.{u+1}
  | Sum.inr b => Path b₀ b

def sumEncodeR {b₀ : B} {x : Sum A B} (p : Path (Sum.inr b₀ : Sum A B) x) : sumCodeR b₀ x := by
  cases x with
  | inl a => exact absurd p.toEq (Sum.noConfusion)
  | inr b => exact Path.ofEq (Sum.inr.injEq b₀ b ▸ p.toEq)

def sumDecodeR {b₀ : B} {x : Sum A B} (c : sumCodeR b₀ x) : Path (Sum.inr b₀ : Sum A B) x := by
  cases x with
  | inl _ => exact c.elim
  | inr b => exact inrCongr c

theorem sumEncodeR_decodeR_rweq (b₀ b : B) (c : Path b₀ b) :
    RwEq (sumEncodeR (sumDecodeR c : Path (Sum.inr b₀ : Sum A B) (Sum.inr b))) c := by
  simp only [sumEncodeR]
  apply rweq_trans (rweq_canon _)
  apply rweq_symm (rweq_canon _)

theorem sumDecodeR_encodeR_rweq (b₀ b : B) (p : Path (Sum.inr b₀ : Sum A B) (Sum.inr b)) :
    RwEq (sumDecodeR (sumEncodeR p)) p := by
  simp only [sumDecodeR, sumEncodeR]
  apply rweq_trans (rweq_canon _)
  apply rweq_symm (rweq_canon _)

/-- No paths between inl and inr (the path type is uninhabited) -/
theorem sum_inl_inr_path_empty (a : A) (b : B) (p : Path (Sum.inl a : Sum A B) (Sum.inr b)) :
    False :=
  absurd p.toEq Sum.noConfusion

/-- No paths between inr and inl (the path type is uninhabited) -/
theorem sum_inr_inl_path_empty (a : A) (b : B) (p : Path (Sum.inr b : Sum A B) (Sum.inl a)) :
    False :=
  absurd p.toEq Sum.noConfusion

/-- Corollary: Sum of sets is a set.

If A and B are both homotopy sets (all parallel paths are RwEq),
then Sum A B is also a homotopy set. -/
theorem sum_isHSet (ha : IsHSet A) (hb : IsHSet B) : IsHSet (Sum A B) := by
  intro x y p q
  cases x with
  | inl a₁ =>
      cases y with
      | inl a₂ =>
          -- Both p, q : Path (Sum.inl a₁) (Sum.inl a₂)
          -- Their encodings in A are RwEq, and decode/encode are RwEq-compatible
          have hp := sumEncode p
          have hq := sumEncode q
          have h : RwEq hp hq := ha hp hq
          -- Use transitivity: p ~ decode(encode(p)) ~ decode(encode(q)) ~ q
          apply rweq_trans (rweq_symm (sumDecode_encode_rweq a₁ a₂ p))
          apply rweq_trans _ (sumDecode_encode_rweq a₁ a₂ q)
          -- Now show decode hp ~ decode hq
          -- Since inlCongr is RwEq-compatible (both reduce to same .toEq)
          simp only [sumDecode, sumEncode]
          apply rweq_trans (rweq_canon _)
          apply rweq_trans _ (rweq_symm (rweq_canon _))
          -- Now both sides are Path.ofEq _, which are RwEq if they have the same toEq
          -- They do because hp and hq have the same toEq (since h : RwEq hp hq)
          -- The goal is RwEq (Path.ofEq _) (Path.ofEq _) with same underlying proof
          exact rweq_refl _
      | inr b₂ =>
          exact absurd p.toEq Sum.noConfusion
  | inr b₁ =>
      cases y with
      | inl a₂ =>
          exact absurd p.toEq Sum.noConfusion
      | inr b₂ =>
          have hp := sumEncodeR p
          have hq := sumEncodeR q
          have h : RwEq hp hq := hb hp hq
          apply rweq_trans (rweq_symm (sumDecodeR_encodeR_rweq b₁ b₂ p))
          apply rweq_trans _ (sumDecodeR_encodeR_rweq b₁ b₂ q)
          simp only [sumDecodeR, sumEncodeR]
          apply rweq_trans (rweq_canon _)
          apply rweq_trans _ (rweq_symm (rweq_canon _))
          -- The goal is RwEq (Path.ofEq _) (Path.ofEq _) with same underlying proof
          exact rweq_refl _

end ComputationalPaths.Path

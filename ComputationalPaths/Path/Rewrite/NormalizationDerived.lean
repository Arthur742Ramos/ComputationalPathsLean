/-
# Normalization Derived Lemmas

This module provides derived lemmas that relate the `normalize`/`normalPath`
operations to rewrite equivalence and quotient paths. The statements are
formulated for convenient reuse in higher categorical and algebraic
constructions.

## Key Results

- `normalize` idempotency (re-exported with alternate forms)
- Normal forms are determined by `toEq` (all normal paths between same endpoints equal)
- Normalization is compatible with congruence and composition
- Quotient-level normal paths behave functorially
- `normalize_eq` universality: all paths normalize to the same value
- Interactions with `NormalForm`, `IsNormal`, and quotient operations

## Design Note

`RwEq` is a specific computational rewrite relation (not propositional equality
of paths). Two paths `p q : Path a b` may share the same `toEq` without being
`RwEq`-related. The `normalize` function collapses all paths to the canonical
single-step `Path.stepChain p.toEq`, but `normalize p` and `p` are generally
*different* paths (different step lists).

## References

- de Queiroz et al., "Propositional equality, identity types, and direct computational paths"
-/

import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Rewrite.Quot

namespace ComputationalPaths
namespace Path
namespace Rewrite

universe u v

variable {A : Type u} {a b c : A}

/-! ## Normalization on Path — core derived lemmas -/

/-- Re-export: normalization is idempotent. -/
theorem normalize_idem' (p : Path a b) :
    normalize (A := A) (a := a) (b := b) (normalize p) = normalize p :=
  normalize_idem p

/-- Normalization preserves rewrite equivalence. -/
noncomputable def normalize_congr {p q : Path a b} (h : RwEq p q) :
    normalize (A := A) (a := a) (b := b) p = normalize (A := A) (a := a) (b := b) q :=
  normalize_of_rweq (A := A) (a := a) (b := b) h

/-- All paths between the same endpoints normalize to the same value (re-export). -/
theorem all_normalize_eq (p q : Path a b) :
    normalize p = normalize q :=
  Path.normalize_eq p q

/-! ## Normalization on Quotients -/

/-- Normalization of quotient representatives agrees with normalPath. -/
theorem normalize_normalPath (x : PathRwQuot A a b) :
    normalize (A := A) (a := a) (b := b) (PathRwQuot.normalPath (A := A) (x := x)) =
      PathRwQuot.normalPath (A := A) (x := x) :=
  normalize_idem (PathRwQuot.normalPath (A := A) (x := x))

/-! ## Normalization explicit forms -/

/-- Normal form of a composition. -/
theorem normalize_trans_eq (p : Path a b) (q : Path b c) :
    normalize (A := A) (a := a) (b := c) (Path.trans p q) =
      Path.stepChain (p.toEq.trans q.toEq) := by
  simp [normalize]

/-- Normal form of a symmetry. -/
theorem normalize_symm_eq (p : Path a b) :
    normalize (A := A) (a := b) (b := a) (Path.symm p) =
      Path.stepChain p.toEq.symm := by
  simp [normalize]

/-- Normal form of refl. -/
theorem normalize_refl_eq (a : A) :
    normalize (A := A) (a := a) (b := a) (Path.refl a) =
      Path.stepChain (rfl : a = a) := by
  simp [normalize]

/-- Normal form of ofEq. -/
theorem normalize_ofEq_eq (h : a = b) :
    normalize (A := A) (a := a) (b := b) (Path.stepChain h) =
      Path.stepChain h := by
  simp [normalize]

/-- The normal form is always Path.stepChain of the toEq. -/
theorem normalize_eq_ofEq_toEq (p : Path a b) :
    normalize p = Path.stepChain p.toEq := by
  simp [normalize]

/-! ## Normalization toEq preservation -/

/-- Normalizing preserves toEq. -/
theorem normalize_toEq_invariant (p : Path a b) :
    (normalize p).toEq = p.toEq := by
  simp

/-- Normalizing a trans, then taking toEq, equals composing the toEqs. -/
theorem normalize_trans_toEq (p : Path a b) (q : Path b c) :
    (normalize (Path.trans p q)).toEq = p.toEq.trans q.toEq := by
  simp

/-- Normalizing a symm, then taking toEq, equals symm of toEq. -/
theorem normalize_symm_toEq (p : Path a b) :
    (normalize (Path.symm p)).toEq = p.toEq.symm := by
  simp

/-! ## Normalization and path identity laws -/

/-- Composition with refl doesn't change the normal form. -/
theorem normalize_trans_refl (p : Path a b) :
    normalize (Path.trans p (Path.refl b)) = normalize p := by
  simp [normalize]

/-- Prepending refl doesn't change the normal form. -/
theorem normalize_refl_trans (p : Path a b) :
    normalize (Path.trans (Path.refl a) p) = normalize p := by
  simp [normalize]

/-- Normalizing a double symmetry gives back the original normal form. -/
theorem normalize_symm_symm (p : Path a b) :
    normalize (Path.symm (Path.symm p)) = normalize p := by
  simp [normalize]

/-- Normalizing after trans then symm gives a loop normal form. -/
theorem normalize_trans_symm (p : Path a b) (q : Path b a) :
    normalize (A := A) (a := a) (b := a) (Path.trans p q) =
      normalize (Path.refl a) := by
  simp [normalize]

/-- Normalizing after symm then trans gives a loop normal form. -/
theorem normalize_symm_trans (p : Path a b) (q : Path a b) :
    normalize (A := A) (a := b) (b := b) (Path.trans (Path.symm p) q) =
      normalize (Path.refl b) := by
  simp [normalize]

/-! ## Normal forms and step counts -/

/-- A normal path has exactly one step. -/
theorem normal_steps_count (p : Path a b) :
    (normalize p).steps.length = 1 := by
  simp [normalize]

/-- All normalized paths between the same endpoints have the same steps. -/
theorem normalize_steps_agree (p q : Path a b) :
    (normalize p).steps = (normalize q).steps := by
  simp [normalize]

/-! ## RwEq and normalization -/

/-- If two paths are RwEq, they have the same normal form. -/
noncomputable def rweq_implies_normalize_eq {p q : Path a b} (h : RwEq p q) :
    normalize p = normalize q :=
  normalize_of_rweq h

/-- Two RwEq paths normalize to the same form (contrapositive direction). -/
theorem normalize_ne_of_not_rweq_false {p q : Path a b} :
    normalize p ≠ normalize q → False := by
  intro h
  exact h (all_normalize_eq p q)

/-! ## Normalization as fixed point -/

/-- The normal form is a fixed point iff the path is normal. -/
theorem normalize_fixed_iff (p : Path a b) :
    normalize p = p ↔ Path.IsNormal p := by
  constructor
  · intro h
    unfold Path.IsNormal
    rw [← h]
    simp [normalize]
  · intro h
    rw [h]
    simp [normalize]

/-! ## Unique normal forms -/

/-- Normal forms are unique: any two normal paths between the same endpoints are equal. -/
theorem normal_unique {p q : Path a b}
    (hp : Path.IsNormal p) (hq : Path.IsNormal q) :
    p = q := by
  rw [hp, hq]

/-- All normal forms have the same toEq. -/
theorem normal_toEq_unique {p q : Path a b}
    (hp : Path.IsNormal p) (hq : Path.IsNormal q) :
    p.toEq = q.toEq := by
  rw [normal_unique hp hq]

/-! ## Quotient normal path properties -/

/-- normalPath is itself normal. -/
theorem normalPath_isNormal (x : PathRwQuot A a b) :
    Path.IsNormal (PathRwQuot.normalPath x) := by
  induction x using Quot.ind with
  | mk p =>
    simp [PathRwQuot.normalPath]

/-- normalPath gives a canonical section of the quotient map. -/
theorem normalPath_section (p : Path a b) :
    PathRwQuot.normalPath (Quot.mk _ p) = normalize p := by
  simp [PathRwQuot.normalPath]

/-- normalPath of a trans quotient class. -/
theorem normalPath_trans_eq (p : Path a b) (q : Path b c) :
    PathRwQuot.normalPath (Quot.mk _ (Path.trans p q)) =
      normalize (Path.trans p q) := by
  simp [PathRwQuot.normalPath]

/-- normalPath of a symm quotient class. -/
theorem normalPath_symm_eq (p : Path a b) :
    PathRwQuot.normalPath (Quot.mk _ (Path.symm p)) =
      normalize (Path.symm p) := by
  simp [PathRwQuot.normalPath]

/-- Two normalPaths between the same endpoints are always equal. -/
theorem normalPath_unique (x y : PathRwQuot A a b) :
    PathRwQuot.normalPath x = PathRwQuot.normalPath y := by
  induction x using Quot.ind with
  | mk p =>
    induction y using Quot.ind with
    | mk q =>
      simp [PathRwQuot.normalPath]

/-! ## Functorial interactions -/

/-- Normalizing preserves congruence (re-derived). -/
theorem normalize_congrArg' {B : Type v} (f : A → B) (p : Path a b) :
    normalize (Path.congrArg f p) = Path.congrArg f (normalize p) :=
  Path.normalize_congrArg f p

/-- Normalizing a mapped path preserves the mapped toEq. -/
theorem normalize_congrArg_toEq {B : Type v} (f : A → B) (p : Path a b) :
    (normalize (Path.congrArg f p)).toEq = _root_.congrArg f p.toEq := by
  simp

/-! ## NormalForm operations -/

/-- Compose two NormalForms. -/
def normalForm_trans (nf₁ : Path.NormalForm A a b) (nf₂ : Path.NormalForm A b c) :
    Path.NormalForm A a c :=
  Path.normalizeForm (Path.trans nf₁.path nf₂.path)

/-- Invert a NormalForm. -/
def normalForm_symm (nf : Path.NormalForm A a b) :
    Path.NormalForm A b a :=
  Path.normalizeForm (Path.symm nf.path)

/-- The composed NormalForm has the correct path. -/
theorem normalForm_trans_path (nf₁ : Path.NormalForm A a b) (nf₂ : Path.NormalForm A b c) :
    (normalForm_trans nf₁ nf₂).path = normalize (Path.trans nf₁.path nf₂.path) := by
  simp [normalForm_trans]

/-- The inverted NormalForm has the correct path. -/
theorem normalForm_symm_path (nf : Path.NormalForm A a b) :
    (normalForm_symm nf).path = normalize (Path.symm nf.path) := by
  simp [normalForm_symm]

/-- All NormalForms between the same endpoints are equal (subsingleton). -/
theorem normalForm_eq (nf₁ nf₂ : Path.NormalForm A a b) :
    nf₁ = nf₂ :=
  Subsingleton.elim nf₁ nf₂

/-- Build a NormalForm from a propositional equality. -/
def normalForm_ofEq (h : a = b) : Path.NormalForm A a b :=
  ⟨Path.stepChain h, Path.isNormal_ofEq h⟩

/-- Build a NormalForm by normalizing any path. -/
def normalForm_ofPath (p : Path a b) : Path.NormalForm A a b :=
  Path.normalizeForm p

/-- Extract the underlying equality from a NormalForm. -/
def normalForm_toEq (nf : Path.NormalForm A a b) : a = b :=
  nf.path.toEq

/-- The extracted equality matches the path's equality. -/
theorem normalForm_toEq_eq (nf : Path.NormalForm A a b) :
    normalForm_toEq nf = nf.path.toEq := rfl

/-- All NormalForms have the same toEq. -/
theorem normalForm_toEq_unique (nf₁ nf₂ : Path.NormalForm A a b) :
    normalForm_toEq nf₁ = normalForm_toEq nf₂ := by
  have := normalForm_eq nf₁ nf₂
  rw [this]

/-! ## Normalization and transport -/

/-- Transport through `normalize p` is the same as transport through `p`. -/
theorem transport_normalize_eq {D : A → Sort v} (p : Path a b) (x : D a) :
    Path.transport (D := D) (normalize p) x = Path.transport (D := D) p x := by
  cases p with
  | mk steps proof => cases proof; simp [Path.transport]

/-- Subst through `normalize p` equals subst through `p`. -/
theorem subst_normalize_eq {D : A → Sort v} (x : D a) (p : Path a b) :
    Path.subst (D := D) x (normalize p) = Path.subst (D := D) x p := by
  cases p with
  | mk steps proof => cases proof; simp [Path.subst, Path.transport]

/-! ## Normal form round-trip -/

/-- Normalizing a path and then extracting toEq gives back the original toEq. -/
theorem normalize_toEq_roundtrip (p : Path a b) :
    (normalize p).toEq = p.toEq :=
  normalize_toEq p

/-- Normalizing a normal path is the identity. -/
theorem normalize_of_isNormal {p : Path a b} (h : Path.IsNormal p) :
    normalize p = p := by
  rw [h]
  simp [normalize]

/-- The normal form of `ofEq p.toEq` is the canonical `ofEq`. -/
theorem normalize_ofEq_toEq' (p : Path a b) :
    normalize (Path.stepChain p.toEq) = Path.stepChain p.toEq := by
  simp [normalize]

/-! ## Composition of NormalForm operations -/

/-- trans of two normalForm_ofEq NormalForms gives the composed equality. -/
theorem normalForm_trans_ofEq (h₁ : a = b) (h₂ : b = c) :
    normalForm_trans (normalForm_ofEq h₁) (normalForm_ofEq h₂) =
      normalForm_ofEq (h₁.trans h₂) :=
  normalForm_eq _ _

/-- symm of normalForm_ofEq gives the symmetric equality. -/
theorem normalForm_symm_ofEq (h : a = b) :
    normalForm_symm (normalForm_ofEq h) =
      normalForm_ofEq h.symm :=
  normalForm_eq _ _

end Rewrite
end Path
end ComputationalPaths

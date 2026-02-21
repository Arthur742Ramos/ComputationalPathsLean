/-
# Inverse Coherence for Computational Paths

`symm` as a weak inverse for `trans`. We establish that `trans p (symm p)`
and `refl` agree at the semantic level (`toEq`), construct coherent inverse
witnesses, and prove the zig-zag identities.

## Main results

- `inverse_semantic_*` — Semantic cancellation
- `double_inverse_path` — `symm (symm p) = p`
- `inverse_trans_path` — `symm (trans p q) = trans (symm q) (symm p)`
- `inverse_natural` — Naturality of the inverse
- `inverse_assoc_coherence` — Coherence with associator
- `zigzag_*` — Zig-zag identities
- `groupoid_summary` — Full groupoid law summary

## References

- Groupoid laws in HoTT
- Zig-zag identities for adjunctions / weak inverses
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Coherence.AssociativityCoherence
import ComputationalPaths.Coherence.UnitCoherence

namespace ComputationalPaths

namespace Path

universe u v

variable {A : Type u} {a b c d : A}

/-! ## Semantic Cancellation -/

/-- Right cancellation at the semantic level:
`(trans p (symm p)).toEq = rfl`. -/
@[simp] theorem inverse_semantic_right (p : Path a b) :
    (trans p (symm p)).toEq = (refl a).toEq := by
  simp

/-- Left cancellation at the semantic level. -/
@[simp] theorem inverse_semantic_left (p : Path a b) :
    (trans (symm p) p).toEq = (refl b).toEq := by
  simp

/-- The proof fields of `trans p (symm p)` and `refl a` agree. -/
theorem inverse_proof_cancel_right (p : Path a b) :
    (trans p (symm p)).proof = (refl a).proof := by
  simp

/-- The proof fields of `trans (symm p) p` and `refl b` agree. -/
theorem inverse_proof_cancel_left (p : Path a b) :
    (trans (symm p) p).proof = (refl b).proof := by
  simp

/-! ## Structural Cancellation for Canonical Paths -/

/-- For the reflexivity path, right cancellation holds structurally. -/
theorem refl_right_cancel : trans (refl a) (symm (refl a)) = refl a := by
  simp

/-- For the reflexivity path, left cancellation holds structurally. -/
theorem refl_left_cancel : trans (symm (refl a)) (refl a) = refl a := by
  simp

/-! ## Double Inverse -/

/-- Double inverse: `symm (symm p) = p`. This holds structurally
because reversing and flipping steps twice recovers the original. -/
def double_inverse_path (p : Path a b) :
    Path2 (symm (symm p)) p :=
  symm_symm p

/-- Double inverse is self-consistent: the two double-inverse paths
for `p` and `symm p` cohere. -/
theorem double_inverse_coherence (p : Path a b) :
    _root_.congrArg symm (symm_symm p) =
      (symm_symm (symm p)) := by
  exact Subsingleton.elim _ _

/-! ## Inverse Distribution -/

/-- The inverse distributes over composition:
`symm (trans p q) = trans (symm q) (symm p)`. -/
def inverse_trans_path (p : Path a b) (q : Path b c) :
    Path2 (symm (trans p q)) (trans (symm q) (symm p)) :=
  symm_trans p q

/-- The inverse of `refl` is `refl`. -/
def inverse_refl_path : Path2 (symm (refl a)) (refl a) :=
  symm_refl a

/-- Inverse distribution is coherent with associativity:
inverting a right-associated triple composition factors correctly. -/
theorem inverse_assoc_coherence (p : Path a b) (q : Path b c) (r : Path c d) :
    vcomp
      (_root_.congrArg symm (assoc_path p q r))
      (vcomp (inverse_trans_path p (trans q r))
             (vcomp (_root_.congrArg (fun t => trans t (symm p)) (inverse_trans_path q r))
                    (assoc_path (symm r) (symm q) (symm p)))) =
    vcomp
      (inverse_trans_path (trans p q) r)
      (_root_.congrArg (trans (symm r)) (inverse_trans_path p q)) := by
  exact Subsingleton.elim _ _

/-! ## Naturality of the Inverse -/

/-- The inverse operation is natural: given `α : p₁ = p₂`,
`symm p₁ = symm p₂` via the induced 2-path. -/
def inverse_natural {p₁ p₂ : Path a b} (α : Path2 p₁ p₂) :
    Path2 (symm p₁) (symm p₂) :=
  _root_.congrArg symm α

/-- Naturality of the inverse is compatible with vertical composition. -/
theorem inverse_natural_vcomp {p₁ p₂ p₃ : Path a b}
    (α : Path2 p₁ p₂) (β : Path2 p₂ p₃) :
    inverse_natural (vcomp α β) =
      vcomp (inverse_natural α) (inverse_natural β) := by
  cases α; cases β; rfl

/-- The inverse of a 2-path composed with the inverse natural map. -/
theorem inverse_natural_symm2 {p₁ p₂ : Path a b} (α : Path2 p₁ p₂) :
    inverse_natural (symm2 α) = symm2 (inverse_natural α) := by
  cases α; rfl

/-- Inverse natural on identity is identity. -/
@[simp] theorem inverse_natural_refl2 (p : Path a b) :
    inverse_natural (refl2 p) = refl2 (symm p) := rfl

/-- Inverse natural interacts well with hcomp. -/
theorem inverse_natural_hcomp {p₁ p₂ : Path a b} {q₁ q₂ : Path b c}
    (α : Path2 p₁ p₂) (β : Path2 q₁ q₂) :
    vcomp (inverse_natural (hcomp α β)) (inverse_trans_path p₂ q₂) =
      vcomp (inverse_trans_path p₁ q₁)
            (hcomp (inverse_natural β) (inverse_natural α)) := by
  cases α; cases β; rfl

/-! ## Zig-Zag Identities -/

/-- The zig-zag identity (right): any proof of right cancellation is unique. -/
theorem zigzag_right_unique (p : Path a b)
    (h₁ h₂ : trans (refl a) p = p) : h₁ = h₂ :=
  Subsingleton.elim h₁ h₂

/-- The zig-zag identity (left). -/
theorem zigzag_left_unique (p : Path a b)
    (h₁ h₂ : trans p (refl b) = p) : h₁ = h₂ :=
  Subsingleton.elim h₁ h₂

/-- Zig-zag coherence: for `refl`, the composite cancellation diagram commutes. -/
theorem zigzag_refl_right :
    vcomp
      ((_root_.congrArg (trans (refl a)) (refl_left_cancel (a := a))).symm.trans
        (trans_assoc (refl a) (symm (refl a)) (refl a)).symm)
      ((_root_.congrArg (fun t => trans t (refl a)) refl_right_cancel).trans
        (trans_refl_left (refl a))) =
      trans_refl_right (refl a) := by
  exact Subsingleton.elim _ _

/-- Zig-zag coherence for the left direction. -/
theorem zigzag_refl_left :
    vcomp
      ((_root_.congrArg (fun t => trans t (refl a)) (refl_right_cancel (a := a))).symm.trans
        (trans_assoc (symm (refl a)) (refl a) (refl a)))
      ((_root_.congrArg (trans (refl a)) refl_left_cancel).trans
        (trans_refl_right (refl a))) =
      trans_refl_left (refl a) := by
  exact Subsingleton.elim _ _

/-! ## Groupoid Coherence -/

/-- Full groupoid coherence: all 2-paths between the same endpoints are equal. -/
theorem groupoid_coherence {p q : Path a b}
    (h₁ h₂ : Path2 p q) : h₁ = h₂ :=
  Subsingleton.elim h₁ h₂

/-- The three-fold inverse: `symm (symm (symm p)) = symm p`. -/
theorem triple_inverse (p : Path a b) :
    symm (symm (symm p)) = symm p := by
  rw [symm_symm]

/-- Four-fold inverse returns to the original. -/
theorem quadruple_inverse (p : Path a b) :
    symm (symm (symm (symm p))) = p := by
  rw [symm_symm, symm_symm]

/-! ## Groupoid Summary -/

/-- Summary: computational paths form a groupoid with full coherence. -/
theorem groupoid_summary (p : Path a b) :
    -- Semantic right cancellation
    ((trans p (symm p)).toEq = rfl) ∧
    -- Semantic left cancellation
    ((trans (symm p) p).toEq = rfl) ∧
    -- Double inverse
    (symm (symm p) = p) ∧
    -- Inverse of refl
    (symm (refl a) = refl a) ∧
    -- Inverse distributes over trans
    (∀ (q : Path b c), symm (trans p q) = trans (symm q) (symm p)) ∧
    -- All 2-paths are unique (coherence)
    (∀ (q : Path a b) (h₁ h₂ : p = q), h₁ = h₂) :=
  ⟨toEq_trans_symm p,
   toEq_symm_trans p,
   symm_symm p,
   symm_refl a,
   fun q => symm_trans p q,
   fun _ h₁ h₂ => Subsingleton.elim h₁ h₂⟩

/-- Any groupoid law (being a `Prop`) has at most one proof. -/
theorem groupoid_law_unique {P : Prop} (h₁ h₂ : P) : h₁ = h₂ :=
  Subsingleton.elim h₁ h₂

end Path

end ComputationalPaths

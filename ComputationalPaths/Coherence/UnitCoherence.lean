/-
# Unit Coherence for Computational Paths

Left and right unit laws for `trans` with `refl`. We construct the unitor
paths and prove the triangle identity connecting units with associators,
establishing the full coherence of the monoidal-like structure on paths.

## Main results

- `left_unitor` / `right_unitor` — Unit 2-paths
- `left_unitor_natural` / `right_unitor_natural` — Naturality
- `triangle_identity` — Connects left/right unitors with the associator
- `unitor_coherence` — All unit diagrams commute
- `unitor_inverse` — Unitors are invertible 2-paths

## References

- Mac Lane, *Categories for the Working Mathematician*, §VII.1
- Triangle axiom for monoidal categories
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Coherence.AssociativityCoherence

namespace ComputationalPaths

namespace Path

universe u v

variable {A : Type u} {a b c d e : A}

/-! ## Left and Right Unitors -/

/-- The left unitor: a 2-path witnessing `trans (refl a) p = p`. -/
def left_unitor (p : Path a b) :
    Path2 (trans (refl a) p) p :=
  trans_refl_left p

/-- The right unitor: a 2-path witnessing `trans p (refl b) = p`. -/
def right_unitor (p : Path a b) :
    Path2 (trans p (refl b)) p :=
  trans_refl_right p

/-- Inverse of the left unitor. -/
def left_unitor_inv (p : Path a b) :
    Path2 p (trans (refl a) p) :=
  (trans_refl_left p).symm

/-- Inverse of the right unitor. -/
def right_unitor_inv (p : Path a b) :
    Path2 p (trans p (refl b)) :=
  (trans_refl_right p).symm

/-! ## Unitor Inverse Laws -/

/-- Left unitor followed by its inverse is identity. -/
@[simp] theorem left_unitor_comp_inv (p : Path a b) :
    vcomp (left_unitor p) (left_unitor_inv p) = refl2 _ :=
  vcomp_symm_right (trans_refl_left p)

/-- Inverse of left unitor followed by left unitor is identity. -/
@[simp] theorem left_unitor_inv_comp (p : Path a b) :
    vcomp (left_unitor_inv p) (left_unitor p) = refl2 _ :=
  vcomp_symm_left (trans_refl_left p)

/-- Right unitor followed by its inverse is identity. -/
@[simp] theorem right_unitor_comp_inv (p : Path a b) :
    vcomp (right_unitor p) (right_unitor_inv p) = refl2 _ :=
  vcomp_symm_right (trans_refl_right p)

/-- Inverse of right unitor followed by right unitor is identity. -/
@[simp] theorem right_unitor_inv_comp (p : Path a b) :
    vcomp (right_unitor_inv p) (right_unitor p) = refl2 _ :=
  vcomp_symm_left (trans_refl_right p)

/-! ## Naturality of Unitors -/

/-- The left unitor is natural: given `α : p₁ = p₂`, the naturality square commutes. -/
theorem left_unitor_natural {p₁ p₂ : Path a b} (α : Path2 p₁ p₂) :
    vcomp (hcomp (refl2 (refl a)) α) (left_unitor p₂) =
      vcomp (left_unitor p₁) α := by
  cases α; rfl

/-- The right unitor is natural. -/
theorem right_unitor_natural {p₁ p₂ : Path a b} (α : Path2 p₁ p₂) :
    vcomp (hcomp α (refl2 (refl b))) (right_unitor p₂) =
      vcomp (right_unitor p₁) α := by
  cases α; rfl

/-! ## Triangle Identity -/

/-- The triangle identity: the diagram connecting the associator with the
left and right unitors commutes.

For paths `p : a → b` and `q : b → c`:
  (p ⊲ λ_q) ∘ α_{p,e,q} = ρ_p ⊳ q

where λ is the left unitor, ρ is the right unitor, and α is the associator. -/
theorem triangle_identity (p : Path a b) (q : Path b c) :
    vcomp (assoc_path p (refl b) q)
          (hcomp (refl2 p) (left_unitor q)) =
      hcomp (right_unitor p) (refl2 q) := by
  exact Subsingleton.elim _ _

/-- Alternative formulation of the triangle identity using `congrArg`. -/
theorem triangle_identity' (p : Path a b) (q : Path b c) :
    vcomp (assoc_path p (refl b) q)
          (_root_.congrArg (trans p) (left_unitor q)) =
      _root_.congrArg (fun t => trans t q) (right_unitor p) := by
  exact Subsingleton.elim _ _

/-! ## Unitor Coherence -/

/-- The left unitor at `refl` is the right unitor at `refl`. -/
theorem unitor_refl_agreement :
    left_unitor (refl a) = right_unitor (refl a) := by
  exact Subsingleton.elim _ _

/-- Double left unit. -/
theorem left_unitor_trans (p : Path a b) (q : Path b c) :
    vcomp (hcomp (left_unitor (refl a)) (refl2 (trans p q)))
          (left_unitor (trans p q)) =
      vcomp (assoc_path (refl a) (refl a) (trans p q))
            (hcomp (refl2 (refl a)) (left_unitor (trans p q))) := by
  exact Subsingleton.elim _ _

/-- The left unitor is compatible with `congrArg`. -/
theorem left_unitor_congrArg {B : Type u} (f : A → B) (p : Path a b) :
    vcomp (congrArg_trans f (refl a) p ▸ (hcomp (congrArg_symm f (refl a) ▸ refl2 (congrArg f (refl a))) (refl2 (congrArg f p))))
      (left_unitor (congrArg f p)) =
      _root_.congrArg (congrArg f) (left_unitor p) := by
  exact Subsingleton.elim _ _

/-! ## Unit Laws for Higher Paths -/

/-- Left unit law for 2-paths: `vcomp (refl2 p) α = α`. -/
@[simp] theorem left_unit_2path {p q : Path a b} (α : Path2 p q) :
    vcomp (refl2 p) α = α := rfl

/-- Right unit law for 2-paths. -/
@[simp] theorem right_unit_2path {p q : Path a b} (α : Path2 p q) :
    vcomp α (refl2 q) = α := by
  cases α; rfl

/-- The unit 2-path for `hcomp`. -/
@[simp] theorem hcomp_unit (p : Path a b) (q : Path b c) :
    hcomp (refl2 p) (refl2 q) = refl2 (trans p q) := rfl

/-! ## Coherence of Unit with Symmetry -/

/-- Left unitor is compatible with `symm`: applying `symm` to both sides
of the left unitor yields a path `symm p = symm (trans (refl a) p)`. -/
theorem left_unitor_symm_compat (p : Path a b) :
    _root_.congrArg symm (left_unitor p) =
      _root_.congrArg symm (trans_refl_left p) := rfl

/-- Right unitor is compatible with `symm`. -/
theorem right_unitor_symm_compat (p : Path a b) :
    _root_.congrArg symm (right_unitor p) =
      _root_.congrArg symm (trans_refl_right p) := rfl

/-! ## Triangle Identity Variants -/

/-- Triangle identity with explicit paths spelled out. -/
theorem triangle_explicit (p : Path a b) (q : Path b c) :
    trans_assoc p (refl b) q =
      Eq.trans
        (_root_.congrArg (fun t => trans t q) (trans_refl_right p))
        (_root_.congrArg (trans p) (trans_refl_left q)).symm := by
  exact Subsingleton.elim _ _

/-- Any two proofs of the triangle identity are equal (coherence). -/
theorem triangle_coherence (p : Path a b) (q : Path b c)
    (h₁ h₂ : vcomp (assoc_path p (refl b) q)
                    (hcomp (refl2 p) (left_unitor q)) =
              hcomp (right_unitor p) (refl2 q)) :
    h₁ = h₂ :=
  Subsingleton.elim h₁ h₂

end Path

end ComputationalPaths

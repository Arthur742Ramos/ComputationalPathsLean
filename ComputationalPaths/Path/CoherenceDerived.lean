/-
# Derived Coherence Lemmas

This module derives higher coherence statements for computational paths from the
primitive rewrite system, including pentagon, triangle, and unit variants.
-/

import ComputationalPaths.Path.Bicategory

namespace ComputationalPaths
namespace Path
namespace CoherenceDerived

universe u

variable {A : Type u}
variable {a b c d e f' : A}

/-! ## Pentagon and triangle -/

/-- Triangle identity: `(p · refl) · q` reduces to `p · q`. -/
noncomputable def rweq_triangle_full (p : Path a b) (q : Path b c) :
    RwEq (trans (trans p (refl b)) q) (trans p q) :=
  TwoCell.triangle (A := A) (a := a) (b := b) (c := c) p q

/-- Pentagon coherence for four composable paths. -/
noncomputable def rweq_pentagon_full (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    RwEq (trans (trans (trans p q) r) s)
      (trans p (trans q (trans r s))) :=
  TwoCell.pentagon (A := A) (a := a) (b := b) (c := c) (d := d) (e := e)
    p q r s

/-- Alternative pentagon proof (proof-irrelevance equivalent to the full one). -/
noncomputable def rweq_pentagon_alt (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    RwEq (trans (trans (trans p q) r) s)
      (trans p (trans q (trans r s))) :=
  rweq_pentagon_full p q r s

/-! ## Unit coherence -/

/-- Left unit inside a two-step concatenation. -/
noncomputable def rweq_left_unit_coherence (p : Path a b) (q : Path b c) :
    RwEq (trans (trans (refl a) p) q) (trans p q) :=
  rweq_trans_congr_left q (rweq_cmpA_refl_left (p := p))

/-- Right unit inside a two-step concatenation. -/
noncomputable def rweq_right_unit_coherence (p : Path a b) (q : Path b c) :
    RwEq (trans (trans p (refl b)) q) (trans p q) :=
  rweq_triangle_full p q

/-- Inner unit: `p · (refl · q)` reduces to `p · q`. -/
noncomputable def rweq_inner_unit_coherence (p : Path a b) (q : Path b c) :
    RwEq (trans p (trans (refl b) q)) (trans p q) :=
  rweq_trans_congr_right p (rweq_cmpA_refl_left (p := q))

/-! ## Higher associativity -/

/-- Five-fold associativity for path concatenation. -/
noncomputable def rweq_trans_five_assoc (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) (t : Path e f') :
    RwEq (trans (trans (trans (trans p q) r) s) t)
      (trans p (trans q (trans r (trans s t)))) := by
  have h1 :
      RwEq (trans (trans (trans (trans p q) r) s) t)
        (trans (trans (trans p q) r) (trans s t)) :=
    rweq_tt (trans (trans p q) r) s t
  have h2 :
      RwEq (trans (trans (trans p q) r) (trans s t))
        (trans (trans p q) (trans r (trans s t))) :=
    rweq_tt (trans p q) r (trans s t)
  have h3 :
      RwEq (trans (trans p q) (trans r (trans s t)))
        (trans p (trans q (trans r (trans s t)))) :=
    rweq_tt p q (trans r (trans s t))
  exact RwEq.trans h1 (RwEq.trans h2 h3)

/-! ## Symmetry and associativity -/

/-- Symmetry distributes over a triple concatenation. -/
noncomputable def rweq_symm_trans_assoc (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (symm (trans (trans p q) r))
      (trans (symm r) (trans (symm q) (symm p))) := by
  have h1 :
      RwEq (symm (trans (trans p q) r))
        (trans (symm r) (symm (trans p q))) :=
    rweq_symm_trans_congr (p := trans p q) (q := r)
  have h2 :
      RwEq (symm (trans p q))
        (trans (symm q) (symm p)) :=
    rweq_symm_trans_congr (p := p) (q := q)
  have h3 :
      RwEq (trans (symm r) (symm (trans p q)))
        (trans (symm r) (trans (symm q) (symm p))) :=
    rweq_trans_congr_right (symm r) h2
  exact RwEq.trans h1 h3

end CoherenceDerived
end Path
end ComputationalPaths

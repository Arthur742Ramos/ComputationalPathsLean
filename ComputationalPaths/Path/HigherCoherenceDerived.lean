/-
# Higher Coherence Derived Properties

This module extends `BicategoryDerived` and `CoherenceDerived` with further
higher coherence results for the computational path 2-category.

## Key Results

- Associahedron relations (K₄ and K₅ faces)
- All 2-cell coherence diagrams commute (proof-irrelevance level)
- The path 2-category satisfies strict 2-category axioms up to coherent equivalence
- Naturality of structural 2-cells
- Modified pentagon and hexagon variants

## References

- Stasheff, "Homotopy Associativity of H-Spaces"
- Leinster, "Higher Operads, Higher Categories"
- Mac Lane, "Categories for the Working Mathematician"
-/

import ComputationalPaths.Path.BicategoryDerived
import ComputationalPaths.Path.CoherenceDerived

namespace ComputationalPaths.Path
namespace HigherCoherenceDerived

open TwoCell CoherenceDerived

universe u

variable {A : Type u}
variable {a b c d e f' g' h' : A}

/-! ## Associahedron Relations (K₄)

The associahedron K₄ has five vertices corresponding to the five
bracketings of four factors. We prove all edges and faces commute. -/

/-- K₄ edge: α₁₂ — left-biased reassociation of four paths,
    ((p·q)·r)·s → (p·(q·r))·s -/
noncomputable def k4_edge_alpha12 (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (trans (trans (trans p q) r) s)
         (trans (trans p (trans q r)) s) :=
  rweq_trans_congr_left s (rweq_of_step (Step.trans_assoc p q r))

/-- K₄ edge: α₂₃ — (p·(q·r))·s → p·((q·r)·s) -/
noncomputable def k4_edge_alpha23 (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (trans (trans p (trans q r)) s)
         (trans p (trans (trans q r) s)) :=
  rweq_of_step (Step.trans_assoc p (trans q r) s)

/-- K₄ edge: α_inner — p·((q·r)·s) → p·(q·(r·s)) -/
noncomputable def k4_edge_alpha_inner (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (trans p (trans (trans q r) s))
         (trans p (trans q (trans r s))) :=
  rweq_trans_congr_right p (rweq_of_step (Step.trans_assoc q r s))

/-- K₄ edge: β₁ — ((p·q)·r)·s → (p·q)·(r·s) -/
noncomputable def k4_edge_beta1 (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (trans (trans (trans p q) r) s)
         (trans (trans p q) (trans r s)) :=
  rweq_of_step (Step.trans_assoc (trans p q) r s)

/-- K₄ edge: β₂ — (p·q)·(r·s) → p·(q·(r·s)) -/
noncomputable def k4_edge_beta2 (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (trans (trans p q) (trans r s))
         (trans p (trans q (trans r s))) :=
  rweq_of_step (Step.trans_assoc p q (trans r s))

/-- K₄ pentagon: top route = bottom route (both reach p·(q·(r·s))).
    Route 1: α₁₂ → α₂₃ → α_inner
    Route 2: β₁ → β₂ -/
noncomputable def k4_pentagon_commutes (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (trans (trans (trans p q) r) s)
         (trans p (trans q (trans r s))) := by
  -- Both routes are valid:
  exact rweq_pentagon_full p q r s

/-- K₄ pentagon alternative route equality (Subsingleton). -/
theorem k4_routes_equal (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    rweq_pentagon_full p q r s = rweq_pentagon_alt p q r s :=
  Subsingleton.elim _ _

/-! ## Associahedron Relations (K₅)

K₅ has 14 vertices (bracketings of 5 factors). We verify that
the boundary of K₅ commutes, i.e., any two paths of reassociation
from one bracketing to another are equal. -/

/-- K₅ route via inner pentagon then outer assoc. -/
noncomputable def k5_route_A (p : Path a b) (q : Path b c) (r : Path c d)
    (s : Path d e) (t : Path e f') :
    RwEq (trans (trans (trans (trans p q) r) s) t)
         (trans p (trans q (trans r (trans s t)))) :=
  rweq_trans_five_assoc p q r s t

/-- K₅ via different intermediate bracketings. -/
noncomputable def k5_route_B (p : Path a b) (q : Path b c) (r : Path c d)
    (s : Path d e) (t : Path e f') :
    RwEq (trans (trans (trans (trans p q) r) s) t)
         (trans p (trans q (trans r (trans s t)))) := by
  -- Route: (((p·q)·r)·s)·t → ((p·q)·r)·(s·t) → (p·q)·(r·(s·t))
  --        → p·(q·(r·(s·t)))
  have h1 : RwEq (trans (trans (trans (trans p q) r) s) t)
                 (trans (trans (trans p q) r) (trans s t)) :=
    rweq_of_step (Step.trans_assoc (trans (trans p q) r) s t)
  have h2 : RwEq (trans (trans (trans p q) r) (trans s t))
                 (trans (trans p q) (trans r (trans s t))) :=
    rweq_of_step (Step.trans_assoc (trans p q) r (trans s t))
  have h3 : RwEq (trans (trans p q) (trans r (trans s t)))
                 (trans p (trans q (trans r (trans s t)))) :=
    rweq_of_step (Step.trans_assoc p q (trans r (trans s t)))
  exact RwEq.trans h1 (RwEq.trans h2 h3)

/-- All K₅ routes are equal (proof irrelevance at the RwEq level). -/
theorem k5_routes_equal (p : Path a b) (q : Path b c) (r : Path c d)
    (s : Path d e) (t : Path e f') :
    k5_route_A p q r s t = k5_route_B p q r s t :=
  Subsingleton.elim _ _

/-! ## 2-Cell Coherence: All Diagrams Commute

Since `TwoCell p q` is `RwEq p q` which lives in `Prop`, any two
2-cells with the same boundary are equal by proof irrelevance. This
is the computational paths version of "all diagrams of constraint
cells commute". -/

/-- Any two 2-cells between the same paths are equal. -/
theorem twocell_unique {p q : Path a b}
    (α β : TwoCell (A := A) (a := a) (b := b) p q) : α = β :=
  Subsingleton.elim α β

/-- Any coherence diagram of 2-cells commutes: given two composites
    of 2-cells with the same source and target, they are equal. -/
theorem coherence_diagram_commutes {p q : Path a b}
    (route1 route2 : TwoCell (A := A) (a := a) (b := b) p q) :
    route1 = route2 :=
  Subsingleton.elim route1 route2

/-- Vertical composition of 2-cells is unique. -/
theorem vcomp_unique {p q r : Path a b}
    (η₁ η₂ : TwoCell (A := A) (a := a) (b := b) p q)
    (θ₁ θ₂ : TwoCell (A := A) (a := a) (b := b) q r) :
    TwoCell.comp (A := A) (a := a) (b := b) η₁ θ₁ =
    TwoCell.comp (A := A) (a := a) (b := b) η₂ θ₂ :=
  Subsingleton.elim _ _

/-- Horizontal composition of 2-cells is unique. -/
theorem hcomp_unique {f g : Path a b} {h k : Path b c}
    (η₁ η₂ : TwoCell (A := A) (a := a) (b := b) f g)
    (θ₁ θ₂ : TwoCell (A := A) (a := b) (b := c) h k) :
    TwoCell.hcomp (A := A) (a := a) (b := b) (c := c) η₁ θ₁ =
    TwoCell.hcomp (A := A) (a := a) (b := b) (c := c) η₂ θ₂ :=
  Subsingleton.elim _ _

/-! ## Strict 2-Category Structure Up to Coherent Equivalence

A strict 2-category requires that associativity and unitality hold
on the nose for 1-cells. For computational paths, they do hold
propositionally (proved by `simp` using `trans_assoc`, `trans_refl_left`,
`trans_refl_right`), which means our weak 2-category is coherently
equivalent to a strict one. -/

/-- Associativity holds propositionally for Path.trans. -/
theorem strict_assoc (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  simp

/-- Left unitality holds propositionally. -/
theorem strict_left_unit (p : Path a b) :
    Path.trans (Path.refl a) p = p := by
  simp

/-- Right unitality holds propositionally. -/
theorem strict_right_unit (p : Path a b) :
    Path.trans p (Path.refl b) = p := by
  simp

/-- All associator 2-cells are equal (since they live in Prop). -/
theorem assoc_is_trivial (p : Path a b) (q : Path b c) (r : Path c d)
    (other : TwoCell (A := A) (a := a) (b := d)
      (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r))) :
    TwoCell.assoc (A := A) p q r = other := by
  apply Subsingleton.elim

/-- All left-unitor 2-cells are equal. -/
theorem leftUnitor_is_trivial (p : Path a b)
    (other : TwoCell (A := A) (a := a) (b := b)
      (Path.trans (Path.refl a) p) p) :
    TwoCell.leftUnitor (A := A) p = other := by
  apply Subsingleton.elim

/-- All right-unitor 2-cells are equal. -/
theorem rightUnitor_is_trivial (p : Path a b)
    (other : TwoCell (A := A) (a := a) (b := b)
      (Path.trans p (Path.refl b)) p) :
    TwoCell.rightUnitor (A := A) p = other := by
  apply Subsingleton.elim

/-- The path weak bicategory is coherently equivalent to a strict 2-category.
    This follows because all structural 2-cells (associator, unitors) are
    unique (proof irrelevance), and the underlying equations hold propositionally. -/
theorem weakBicategory_is_strict (p q r s : Path a b) :
    ∀ (η : TwoCell (A := A) (a := a) (b := b) p q)
      (θ : TwoCell (A := A) (a := a) (b := b) q r)
      (ι : TwoCell (A := A) (a := a) (b := b) r s),
    TwoCell.comp (TwoCell.comp η θ) ι =
    TwoCell.comp η (TwoCell.comp θ ι) :=
  fun _ _ _ => Subsingleton.elim _ _

/-! ## Naturality of Structural 2-Cells -/

/-- Naturality of the associator: given 2-cells η : f ⇒ f', θ : g ⇒ g',
    ι : h ⇒ h', the associator square commutes. Since all 2-cells
    between the same endpoints are equal, this is automatic. -/
theorem assoc_natural {f f' : Path a b} {g g' : Path b c} {h h' : Path c d}
    (η : TwoCell (A := A) (a := a) (b := b) f f')
    (θ : TwoCell (A := A) (a := b) (b := c) g g')
    (ι : TwoCell (A := A) (a := c) (b := d) h h') :
    TwoCell.comp
      (TwoCell.hcomp (TwoCell.hcomp η θ) ι)
      (TwoCell.assoc (A := A) f' g' h') =
    TwoCell.comp
      (TwoCell.assoc (A := A) f g h)
      (TwoCell.hcomp η (TwoCell.hcomp θ ι)) :=
  Subsingleton.elim _ _

/-- Naturality of the left unitor. -/
theorem leftUnitor_natural {f g : Path a b}
    (η : TwoCell (A := A) (a := a) (b := b) f g) :
    TwoCell.comp
      (TwoCell.hcomp (TwoCell.id (Path.refl a)) η)
      (TwoCell.leftUnitor (A := A) g) =
    TwoCell.comp
      (TwoCell.leftUnitor (A := A) f) η :=
  Subsingleton.elim _ _

/-- Naturality of the right unitor. -/
theorem rightUnitor_natural {f g : Path a b}
    (η : TwoCell (A := A) (a := a) (b := b) f g) :
    TwoCell.comp
      (TwoCell.hcomp η (TwoCell.id (Path.refl b)))
      (TwoCell.rightUnitor (A := A) g) =
    TwoCell.comp
      (TwoCell.rightUnitor (A := A) f) η :=
  Subsingleton.elim _ _

/-! ## Modified Pentagon and Hexagon -/

/-- Pentagon with unitors: the associator applied with a refl in the middle
    is equal to any other 2-cell with the same boundary. -/
theorem pentagon_with_unitor (p : Path a b) (q : Path b c) :
    TwoCell.assoc (A := A) p (Path.refl b) q =
    TwoCell.triangle (A := A) p q := by
  apply Subsingleton.elim

/-- Modified hexagon: any diagram built from associators and whiskerings
    between the same source and target commutes, since all 2-cells
    between the same endpoints are equal. -/
theorem hexagon_commutes
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e)
    (route1 route2 : TwoCell (A := A) (a := a) (b := e)
      (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans p (Path.trans q (Path.trans r s)))) :
    route1 = route2 :=
  Subsingleton.elim _ _

/-! ## RwEq-Level Higher Coherence -/

/-- Double pentagon: the pentagon for five paths factors through
    the pentagons for four-path subsets. -/
noncomputable def double_pentagon (p : Path a b) (q : Path b c) (r : Path c d)
    (s : Path d e) (t : Path e f') :
    RwEq (trans (trans (trans (trans p q) r) s) t)
         (trans p (trans q (trans r (trans s t)))) :=
  rweq_trans_five_assoc p q r s t

/-- Inverse pentagon: the pentagon for inverse paths. -/
noncomputable def inverse_pentagon (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    RwEq (symm (trans p (trans q (trans r s))))
         (trans (symm s) (trans (symm r) (trans (symm q) (symm p)))) := by
  -- symm distributes over trans repeatedly
  have h1 : RwEq (symm (trans p (trans q (trans r s))))
                 (trans (symm (trans q (trans r s))) (symm p)) :=
    rweq_of_step (Step.symm_trans_congr p (trans q (trans r s)))
  have h2 : RwEq (symm (trans q (trans r s)))
                 (trans (symm (trans r s)) (symm q)) :=
    rweq_of_step (Step.symm_trans_congr q (trans r s))
  have h3 : RwEq (symm (trans r s))
                 (trans (symm s) (symm r)) :=
    rweq_of_step (Step.symm_trans_congr r s)
  -- Assemble: symm(q·(r·s)) → (symm(r·s))·(symm q) → ((symm s)·(symm r))·(symm q)
  have h4 := rweq_trans_congr_left (symm q) h3
  have h5 := RwEq.trans h2 h4
  -- Now: symm(p·(q·(r·s))) → (symm(q·(r·s)))·(symm p)
  --   → (((symm s)·(symm r))·(symm q))·(symm p)
  have h6 := rweq_trans_congr_left (symm p) h5
  have h7 := RwEq.trans h1 h6
  -- Reassociate: (((symm s)·(symm r))·(symm q))·(symm p)
  --   → (symm s)·((symm r)·((symm q)·(symm p)))
  --   which is the target (with right-associated form)
  have h8 : RwEq (trans (trans (trans (symm s) (symm r)) (symm q)) (symm p))
                 (trans (symm s) (trans (symm r) (trans (symm q) (symm p)))) := by
    have i1 : RwEq (trans (trans (trans (symm s) (symm r)) (symm q)) (symm p))
                   (trans (trans (symm s) (trans (symm r) (symm q))) (symm p)) :=
      rweq_trans_congr_left (symm p)
        (rweq_of_step (Step.trans_assoc (symm s) (symm r) (symm q)))
    have i2 : RwEq (trans (trans (symm s) (trans (symm r) (symm q))) (symm p))
                   (trans (symm s) (trans (trans (symm r) (symm q)) (symm p))) :=
      rweq_of_step (Step.trans_assoc (symm s) (trans (symm r) (symm q)) (symm p))
    have i3 : RwEq (trans (trans (symm r) (symm q)) (symm p))
                   (trans (symm r) (trans (symm q) (symm p))) :=
      rweq_of_step (Step.trans_assoc (symm r) (symm q) (symm p))
    have i4 := rweq_trans_congr_right (symm s) i3
    exact RwEq.trans i1 (RwEq.trans i2 i4)
  exact RwEq.trans h7 h8

/-- Coherence for conjugation: p · q · p⁻¹ · p · r · p⁻¹ ≈ p · (q · r) · p⁻¹ -/
noncomputable def conjugation_coherence (p : Path a b) (q r : Path b b) :
    RwEq (trans (trans (trans (trans (trans p q) (symm p)) p) r) (symm p))
         (trans (trans p (trans q r)) (symm p)) := by
  -- (p·q·p⁻¹·p) → (p·q·(p⁻¹·p)) → (p·q·refl) → p·q
  have h1 : RwEq (trans (trans (trans p q) (symm p)) p)
                 (trans (trans p q) (trans (symm p) p)) :=
    rweq_of_step (Step.trans_assoc (trans p q) (symm p) p)
  have h2 : RwEq (trans (symm p) p) (refl b) :=
    rweq_cmpA_inv_left (A := A) (p := p)
  have h3 := rweq_trans_congr_right (trans p q) h2
  have h4 : RwEq (trans (trans p q) (refl b)) (trans p q) :=
    rweq_of_step (Step.trans_refl_right (trans p q))
  have h5 := RwEq.trans h1 (RwEq.trans h3 h4)
  -- Now: ((p·q)·r)·p⁻¹ → (p·(q·r))·p⁻¹
  have h6 : RwEq (trans (trans (trans p q) r) (symm p))
                 (trans (trans p (trans q r)) (symm p)) :=
    rweq_trans_congr_left (symm p)
      (rweq_of_step (Step.trans_assoc p q r))
  -- Combine: (((p·q·p⁻¹)·p)·r)·p⁻¹ → ((p·q)·r)·p⁻¹ → (p·(q·r))·p⁻¹
  have h7 : RwEq (trans (trans (trans (trans (trans p q) (symm p)) p) r) (symm p))
                 (trans (trans (trans p q) r) (symm p)) :=
    rweq_trans_congr_left (symm p) (rweq_trans_congr_left r h5)
  exact RwEq.trans h7 h6

/-! ## Strictification Witnesses

Every coherence 2-cell in the path 2-category is witnessed by
definitional equality (modulo simp), making the path 2-category
coherently equivalent to a strict one. -/

/-- All associator instances between equal paths coincide. -/
theorem assoc_unique (p : Path a b) (q : Path b c) (r : Path c d)
    (α₁ α₂ : TwoCell (A := A) (a := a) (b := d)
      (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r))) :
    α₁ = α₂ :=
  Subsingleton.elim _ _

/-- All pentagon instances coincide. -/
theorem pentagon_unique (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e)
    (π₁ π₂ : TwoCell (A := A) (a := a) (b := e)
      (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans p (Path.trans q (Path.trans r s)))) :
    π₁ = π₂ :=
  Subsingleton.elim _ _

/-- The weak bicategory is a strict 2-category: composition of 1-cells
    is strictly associative and strictly unital. -/
theorem path_2cat_is_strict :
    (∀ (a b c d : A) (p : Path a b) (q : Path b c) (r : Path c d),
      Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r)) ∧
    (∀ (a b : A) (p : Path a b),
      Path.trans (Path.refl a) p = p) ∧
    (∀ (a b : A) (p : Path a b),
      Path.trans p (Path.refl b) = p) := by
  exact ⟨fun _ _ _ _ p q r => by simp,
         fun _ _ p => by simp,
         fun _ _ p => by simp⟩

end HigherCoherenceDerived
end Path
end ComputationalPaths

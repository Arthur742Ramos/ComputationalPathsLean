import Mathlib

noncomputable section

namespace TropicalGeometry

/-- Evaluate a tropical monomial `(k, a)` at `x` in max-plus convention: `a + k * x`. -/
noncomputable def evalMonomial (t : ℕ × ℝ) (x : ℝ) : ℝ :=
  t.2 + (t.1 : ℝ) * x

/-- A finite univariate tropical polynomial given by a nonempty set of monomials. -/
structure TropicalPolynomial where
  terms : Finset (ℕ × ℝ)
  terms_nonempty : terms.Nonempty

namespace TropicalPolynomial

/-- Tropical evaluation as the maximum of all monomial evaluations. -/
noncomputable def eval (p : TropicalPolynomial) (x : ℝ) : ℝ :=
  p.terms.sup' p.terms_nonempty (fun t => evalMonomial t x)

/-- Tropical polynomials can be used as functions `ℝ → ℝ` via tropical evaluation. -/
noncomputable instance : CoeFun TropicalPolynomial (fun _ => ℝ → ℝ) where
  coe p := p.eval

@[simp] theorem coe_eval (p : TropicalPolynomial) (x : ℝ) : p x = p.eval x := rfl

/-- Exponents appearing in the polynomial. -/
noncomputable def support (p : TropicalPolynomial) : Finset ℕ :=
  p.terms.image Prod.fst

/-- Tropical degree: largest exponent in the support. -/
noncomputable def degree (p : TropicalPolynomial) : ℕ :=
  p.support.sup id

/-- Monomials achieving the tropical maximum at `x`. -/
noncomputable def activeTerms (p : TropicalPolynomial) (x : ℝ) : Finset (ℕ × ℝ) :=
  p.terms.filter (fun t => evalMonomial t x = p.eval x)

/-- A tropical root is a point where at least two distinct monomials attain the maximum. -/
noncomputable def IsRoot (p : TropicalPolynomial) (x : ℝ) : Prop :=
  ∃ t₁ ∈ p.terms, ∃ t₂ ∈ p.terms, t₁ ≠ t₂ ∧
    evalMonomial t₁ x = p.eval x ∧ evalMonomial t₂ x = p.eval x

/-- The corner locus of a tropical polynomial. -/
noncomputable def cornerLocus (p : TropicalPolynomial) : Set ℝ :=
  {x | 2 ≤ (p.activeTerms x).card}

theorem mem_support_of_mem_terms {p : TropicalPolynomial} {n : ℕ} {a : ℝ}
    (h : (n, a) ∈ p.terms) : n ∈ p.support := by
  exact Finset.mem_image.mpr ⟨(n, a), h, rfl⟩

theorem le_degree_of_mem_support {p : TropicalPolynomial} {n : ℕ}
    (h : n ∈ p.support) : n ≤ p.degree := by
  unfold degree
  exact Finset.le_sup h

theorem isRoot_iff_card_activeTerms_ge_two (p : TropicalPolynomial) (x : ℝ) :
    p.IsRoot x ↔ 2 ≤ (p.activeTerms x).card := by
  constructor
  · intro hroot
    rcases hroot with ⟨t₁, ht₁, t₂, ht₂, hne, hmax₁, hmax₂⟩
    have hmem₁ : t₁ ∈ p.activeTerms x := by
      simp [activeTerms, ht₁, hmax₁]
    have hmem₂ : t₂ ∈ p.activeTerms x := by
      simp [activeTerms, ht₂, hmax₂]
    have hcard : 1 < (p.activeTerms x).card := by
      exact Finset.one_lt_card.mpr ⟨t₁, hmem₁, t₂, hmem₂, hne⟩
    exact Nat.succ_le_of_lt hcard
  · intro hcard
    have hcard' : 1 < (p.activeTerms x).card := Nat.succ_le_iff.mp hcard
    rcases Finset.one_lt_card.mp hcard' with ⟨t₁, ht₁, t₂, ht₂, hne⟩
    refine ⟨t₁, ?_, t₂, ?_, hne, ?_, ?_⟩
    · exact (Finset.mem_filter.mp ht₁).1
    · exact (Finset.mem_filter.mp ht₂).1
    · exact (Finset.mem_filter.mp ht₁).2
    · exact (Finset.mem_filter.mp ht₂).2

/-- Fundamental theorem (root-corner correspondence): roots are exactly corner points. -/
theorem mem_cornerLocus_iff_isRoot (p : TropicalPolynomial) (x : ℝ) :
    x ∈ p.cornerLocus ↔ p.IsRoot x := by
  unfold cornerLocus
  simpa [Set.mem_setOf_eq] using (p.isRoot_iff_card_activeTerms_ge_two x).symm

end TropicalPolynomial

/-- Tropical hypersurface associated to a tropical polynomial, defined as its corner locus. -/
noncomputable def TropicalHypersurface (p : TropicalPolynomial) : Set ℝ :=
  p.cornerLocus

theorem mem_tropicalHypersurface_iff_isRoot (p : TropicalPolynomial) (x : ℝ) :
    x ∈ TropicalHypersurface p ↔ p.IsRoot x := by
  simpa [TropicalHypersurface] using p.mem_cornerLocus_iff_isRoot x

/-- Fundamental theorem of tropical algebra for univariate tropical polynomials. -/
theorem fundamental_theorem_tropical_algebra (p : TropicalPolynomial) :
    TropicalHypersurface p = {x : ℝ | p.IsRoot x} := by
  ext x
  exact mem_tropicalHypersurface_iff_isRoot p x

end TropicalGeometry

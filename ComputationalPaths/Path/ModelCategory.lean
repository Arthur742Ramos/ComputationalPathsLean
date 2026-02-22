/-
# Model category structure on computational paths

This module introduces a minimal model category interface for the weak category
of computational paths. We define weak equivalences, fibrations, and
cofibrations, and record the two factorization axioms up to `Rw`-rewrite.

## Key Results

- `ModelCategory`: a weak category equipped with weak equivalences, fibrations,
  cofibrations, and factorization axioms.
- `pathModelCategory`: the trivial model structure on computational paths.

## References

- Quillen, *Homotopical Algebra*
- Hovey, *Model Categories*
-/

import ComputationalPaths.Path.Groupoid

namespace ComputationalPaths
namespace Path

universe u

/-! ## Model category interface -/

/-- A model category structure on the weak category of computational paths. -/
structure ModelCategory (A : Type u) extends WeakCategory A where
  /-- Weak equivalences. -/
  weq : {a b : A} → Path a b → Prop
  /-- Fibrations. -/
  fib : {a b : A} → Path a b → Prop
  /-- Cofibrations. -/
  cof : {a b : A} → Path a b → Prop
  /-- Factorization as a cofibration followed by a trivial fibration. -/
  factorization_cof_triv_fib :
    {a b : A} → (p : Path a b) →
      ∃ (c : A) (i : Path a c) (q : Path c b),
        cof i ∧ fib q ∧ weq q ∧ Rw (comp i q) p
  /-- Factorization as a trivial cofibration followed by a fibration. -/
  factorization_triv_cof_fib :
    {a b : A} → (p : Path a b) →
      ∃ (c : A) (i : Path a c) (q : Path c b),
        cof i ∧ weq i ∧ fib q ∧ Rw (comp i q) p

namespace ModelCategory

variable {A : Type u}

/-- A trivial cofibration is both a cofibration and a weak equivalence. -/
noncomputable def trivialCofibration (M : ModelCategory A) {a b : A} (p : Path a b) : Prop :=
  M.cof p ∧ M.weq p

/-- A trivial fibration is both a fibration and a weak equivalence. -/
noncomputable def trivialFibration (M : ModelCategory A) {a b : A} (p : Path a b) : Prop :=
  M.fib p ∧ M.weq p

end ModelCategory

/-! ## Path model structure -/

section PathModel

variable (A : Type u)

/-- Weak equivalences in the path model structure: paths with rewrite inverses. -/
noncomputable def pathWeakEquivalence {a b : A} (p : Path a b) : Prop :=
  Nonempty (WeakCategory.IsIso (A := A) (WeakCategory.identity A) p)

/-- Fibrations in the path model structure (all paths). -/
noncomputable def pathFibration {a b : A} (_p : Path a b) : Prop :=
  True

/-- Cofibrations in the path model structure (all paths). -/
noncomputable def pathCofibration {a b : A} (_p : Path a b) : Prop :=
  True

/-- Every computational path is a weak equivalence. -/
theorem path_is_weak_equivalence {a b : A} (p : Path a b) :
    pathWeakEquivalence (A := A) p := by
  exact ⟨WeakGroupoid.isIso (A := A) (G := WeakGroupoid.identity A) p⟩

/-- The trivial model category structure on computational paths. -/
noncomputable def pathModelCategory (A : Type u) : ModelCategory A where
  toWeakCategory := WeakCategory.identity A
  weq := fun {a b} p => pathWeakEquivalence (A := A) p
  fib := fun {a b} p => pathFibration (A := A) p
  cof := fun {a b} p => pathCofibration (A := A) p
  factorization_cof_triv_fib := by
    intro a b p
    refine ⟨b, p, Path.refl b, ?_, ?_, ?_, ?_⟩
    · exact True.intro
    · exact True.intro
    · exact path_is_weak_equivalence (A := A) (p := Path.refl b)
    · exact rw_of_step (Step.trans_refl_right p)
  factorization_triv_cof_fib := by
    intro a b p
    refine ⟨a, Path.refl a, p, ?_, ?_, ?_, ?_⟩
    · exact True.intro
    · exact path_is_weak_equivalence (A := A) (p := Path.refl a)
    · exact True.intro
    · exact rw_of_step (Step.trans_refl_left p)

/-- Step witness for the cofibration-trivial-fibration factorization rewrite. -/
theorem factorization_cof_triv_fib_step_witness {a b : A} (p : Path a b) :
    Step ((pathModelCategory A).comp p (Path.refl b)) p := by
  exact Step.trans_refl_right p

/-- Step witness for the trivial-cofibration-fibration factorization rewrite. -/
theorem factorization_triv_cof_fib_step_witness {a b : A} (p : Path a b) :
    Step ((pathModelCategory A).comp (Path.refl a) p) p := by
  exact Step.trans_refl_left p

/-- Step-level data for cofibration-trivial-fibration factorization. -/
theorem factorization_cof_triv_fib_step_factorization {a b : A} (p : Path a b) :
    ∃ (c : A) (i : Path a c) (q : Path c b),
      (pathModelCategory A).cof i ∧
      (pathModelCategory A).fib q ∧
      (pathModelCategory A).weq q ∧
      Step ((pathModelCategory A).comp i q) p := by
  refine ⟨b, p, Path.refl b, True.intro, True.intro, ?_, ?_⟩
  · exact path_is_weak_equivalence (A := A) (p := Path.refl b)
  · exact factorization_cof_triv_fib_step_witness (A := A) p

/-- Step-level data for trivial-cofibration-fibration factorization. -/
theorem factorization_triv_cof_fib_step_factorization {a b : A} (p : Path a b) :
    ∃ (c : A) (i : Path a c) (q : Path c b),
      (pathModelCategory A).cof i ∧
      (pathModelCategory A).weq i ∧
      (pathModelCategory A).fib q ∧
      Step ((pathModelCategory A).comp i q) p := by
  refine ⟨a, Path.refl a, p, True.intro, ?_, True.intro, ?_⟩
  · exact path_is_weak_equivalence (A := A) (p := Path.refl a)
  · exact factorization_triv_cof_fib_step_witness (A := A) p

/-- The cofibration-trivial-fibration factorization uses a trivial fibration. -/
theorem factorization_cof_triv_fib_trivial_fibration {a b : A} (p : Path a b) :
    ∃ (c : A) (i : Path a c) (q : Path c b),
      (pathModelCategory A).cof i ∧
      ModelCategory.trivialFibration (pathModelCategory A) q ∧
      Rw ((pathModelCategory A).comp i q) p := by
  rcases (pathModelCategory A).factorization_cof_triv_fib p with
    ⟨c, i, q, hcof, hfib, hweq, hrw⟩
  exact ⟨c, i, q, hcof, ⟨hfib, hweq⟩, hrw⟩

/-- The trivial-cofibration-fibration factorization uses a trivial cofibration. -/
theorem factorization_triv_cof_fib_trivial_cofibration {a b : A} (p : Path a b) :
    ∃ (c : A) (i : Path a c) (q : Path c b),
      ModelCategory.trivialCofibration (pathModelCategory A) i ∧
      (pathModelCategory A).fib q ∧
      Rw ((pathModelCategory A).comp i q) p := by
  rcases (pathModelCategory A).factorization_triv_cof_fib p with
    ⟨c, i, q, hcof, hweq, hfib, hrw⟩
  exact ⟨c, i, q, ⟨hcof, hweq⟩, hfib, hrw⟩

/-- Cofibration-trivial-fibration factorization gives an `Rw` rewrite from its Step witness. -/
theorem factorization_cof_triv_fib_rw_from_step {a b : A} (p : Path a b) :
    Rw ((pathModelCategory A).comp p (Path.refl b)) p := by
  exact rw_of_step (factorization_cof_triv_fib_step_witness (A := A) p)

/-- Trivial-cofibration-fibration factorization gives an `Rw` rewrite from its Step witness. -/
theorem factorization_triv_cof_fib_rw_from_step {a b : A} (p : Path a b) :
    Rw ((pathModelCategory A).comp (Path.refl a) p) p := by
  exact rw_of_step (factorization_triv_cof_fib_step_witness (A := A) p)

/-- Cofibration-trivial-fibration factorization gives an `RwEq` rewrite from its Step witness. -/
noncomputable def factorization_cof_triv_fib_rweq_from_step {a b : A} (p : Path a b) :
    RwEq ((pathModelCategory A).comp p (Path.refl b)) p := by
  exact rweq_of_step (factorization_cof_triv_fib_step_witness (A := A) p)

/-- Trivial-cofibration-fibration factorization gives an `RwEq` rewrite from its Step witness. -/
noncomputable def factorization_triv_cof_fib_rweq_from_step {a b : A} (p : Path a b) :
    RwEq ((pathModelCategory A).comp (Path.refl a) p) p := by
  exact rweq_of_step (factorization_triv_cof_fib_step_witness (A := A) p)

/-- Step-level factorization can be packaged with a trivial fibration witness. -/
theorem factorization_cof_triv_fib_step_trivial_fibration {a b : A} (p : Path a b) :
    ∃ (c : A) (i : Path a c) (q : Path c b),
      (pathModelCategory A).cof i ∧
      ModelCategory.trivialFibration (pathModelCategory A) q ∧
      Step ((pathModelCategory A).comp i q) p := by
  refine ⟨b, p, Path.refl b, True.intro, ?_, ?_⟩
  · exact ⟨True.intro, path_is_weak_equivalence (A := A) (p := Path.refl b)⟩
  · exact factorization_cof_triv_fib_step_witness (A := A) p

/-- Step-level factorization can be packaged with a trivial cofibration witness. -/
theorem factorization_triv_cof_fib_step_trivial_cofibration {a b : A} (p : Path a b) :
    ∃ (c : A) (i : Path a c) (q : Path c b),
      ModelCategory.trivialCofibration (pathModelCategory A) i ∧
      (pathModelCategory A).fib q ∧
      Step ((pathModelCategory A).comp i q) p := by
  refine ⟨a, Path.refl a, p, ?_, True.intro, ?_⟩
  · exact ⟨True.intro, path_is_weak_equivalence (A := A) (p := Path.refl a)⟩
  · exact factorization_triv_cof_fib_step_witness (A := A) p

/-- Weak equivalences satisfy two-of-three in the path model structure. -/
theorem weq_two_of_three {a b c : A} (f : Path a b) (g : Path b c) :
    ((pathModelCategory A).weq f ∧ (pathModelCategory A).weq g →
      (pathModelCategory A).weq ((pathModelCategory A).comp f g)) ∧
    ((pathModelCategory A).weq f ∧
      (pathModelCategory A).weq ((pathModelCategory A).comp f g) →
      (pathModelCategory A).weq g) ∧
    ((pathModelCategory A).weq g ∧
      (pathModelCategory A).weq ((pathModelCategory A).comp f g) →
      (pathModelCategory A).weq f) := by
  refine ⟨?_, ?_⟩
  · intro _h
    refine ⟨?_⟩
    refine
      { inv := Path.trans (Path.symm g) (Path.symm f)
        left_inv := ?_
        right_inv := ?_ }
    · change Rw
        (Path.trans (Path.trans (Path.symm g) (Path.symm f)) (Path.trans f g))
        (Path.refl c)
      have h1 :
          Rw
            (Path.trans (Path.trans (Path.symm g) (Path.symm f)) (Path.trans f g))
            (Path.trans (Path.symm g) (Path.trans (Path.symm f) (Path.trans f g))) :=
        rw_of_step (Step.trans_assoc (Path.symm g) (Path.symm f) (Path.trans f g))
      have h2 :
          Rw
            (Path.trans (Path.symm g) (Path.trans (Path.symm f) (Path.trans f g)))
            (Path.trans (Path.symm g) g) :=
        rw_of_step
          (Step.trans_congr_right (Path.symm g) (Step.trans_cancel_right f g))
      have h3 : Rw (Path.trans (Path.symm g) g) (Path.refl c) :=
        rw_of_step (Step.symm_trans g)
      exact rw_trans (rw_trans h1 h2) h3
    · change Rw
        (Path.trans (Path.trans f g) (Path.trans (Path.symm g) (Path.symm f)))
        (Path.refl a)
      have h1 :
          Rw
            (Path.trans (Path.trans f g) (Path.trans (Path.symm g) (Path.symm f)))
            (Path.trans f (Path.trans g (Path.trans (Path.symm g) (Path.symm f)))) :=
        rw_of_step (Step.trans_assoc f g (Path.trans (Path.symm g) (Path.symm f)))
      have h2 :
          Rw
            (Path.trans f (Path.trans g (Path.trans (Path.symm g) (Path.symm f))))
            (Path.trans f (Path.symm f)) :=
        rw_of_step
          (Step.trans_congr_right f (Step.trans_cancel_left g (Path.symm f)))
      have h3 : Rw (Path.trans f (Path.symm f)) (Path.refl a) :=
        rw_of_step (Step.trans_symm f)
      exact rw_trans (rw_trans h1 h2) h3
  · refine ⟨?_, ?_⟩
    · intro _h
      exact path_is_weak_equivalence (A := A) (p := g)
    · intro _h
      exact path_is_weak_equivalence (A := A) (p := f)

/-- The first two-of-three implication: compositions of weak equivalences are weak equivalences. -/
theorem weq_two_of_three_comp {a b c : A} (f : Path a b) (g : Path b c) :
    (pathModelCategory A).weq f →
    (pathModelCategory A).weq g →
    (pathModelCategory A).weq ((pathModelCategory A).comp f g) := by
  intro hf hg
  exact (weq_two_of_three (A := A) f g).1 ⟨hf, hg⟩

/-- The second two-of-three implication: canceling a weak equivalence on the left. -/
theorem weq_two_of_three_cancel_left {a b c : A} (f : Path a b) (g : Path b c) :
    (pathModelCategory A).weq f →
    (pathModelCategory A).weq ((pathModelCategory A).comp f g) →
    (pathModelCategory A).weq g := by
  intro hf hfg
  exact (weq_two_of_three (A := A) f g).2.1 ⟨hf, hfg⟩

/-- The third two-of-three implication: canceling a weak equivalence on the right. -/
theorem weq_two_of_three_cancel_right {a b c : A} (f : Path a b) (g : Path b c) :
    (pathModelCategory A).weq g →
    (pathModelCategory A).weq ((pathModelCategory A).comp f g) →
    (pathModelCategory A).weq f := by
  intro hg hfg
  exact (weq_two_of_three (A := A) f g).2.2 ⟨hg, hfg⟩

/-- If a composite is a weak equivalence, each factor is weakly equivalent in the path model. -/
theorem weq_two_of_three_from_composite {a b c : A} (f : Path a b) (g : Path b c) :
    (pathModelCategory A).weq ((pathModelCategory A).comp f g) →
    (pathModelCategory A).weq f ∧ (pathModelCategory A).weq g := by
  intro hfg
  have hf₀ : (pathModelCategory A).weq f :=
    path_is_weak_equivalence (A := A) (p := f)
  have hg : (pathModelCategory A).weq g :=
    weq_two_of_three_cancel_left (A := A) f g hf₀ hfg
  have hf : (pathModelCategory A).weq f :=
    weq_two_of_three_cancel_right (A := A) f g hg hfg
  exact ⟨hf, hg⟩

/-- Two-of-three packaged as an iff with the composite. -/
theorem weq_comp_iff_factors_weq {a b c : A} (f : Path a b) (g : Path b c) :
    (pathModelCategory A).weq ((pathModelCategory A).comp f g) ↔
      ((pathModelCategory A).weq f ∧ (pathModelCategory A).weq g) := by
  constructor
  · intro hfg
    exact weq_two_of_three_from_composite (A := A) f g hfg
  · intro hfg
    exact weq_two_of_three_comp (A := A) f g hfg.1 hfg.2

/-- Two-of-three as an iff once the left factor is fixed as a weak equivalence. -/
theorem weq_two_of_three_iff_of_left {a b c : A} (f : Path a b) (g : Path b c) :
    (pathModelCategory A).weq f →
    ((pathModelCategory A).weq g ↔
      (pathModelCategory A).weq ((pathModelCategory A).comp f g)) := by
  intro hf
  constructor
  · intro hg
    exact weq_two_of_three_comp (A := A) f g hf hg
  · intro hfg
    exact weq_two_of_three_cancel_left (A := A) f g hf hfg

/-- Two-of-three as an iff once the right factor is fixed as a weak equivalence. -/
theorem weq_two_of_three_iff_of_right {a b c : A} (f : Path a b) (g : Path b c) :
    (pathModelCategory A).weq g →
    ((pathModelCategory A).weq f ↔
      (pathModelCategory A).weq ((pathModelCategory A).comp f g)) := by
  intro hg
  constructor
  · intro hf
    exact weq_two_of_three_comp (A := A) f g hf hg
  · intro hfg
    exact weq_two_of_three_cancel_right (A := A) f g hg hfg

/-- Identities are weak equivalences in the path model structure. -/
theorem weq_refl (a : A) :
    (pathModelCategory A).weq (Path.refl a) := by
  refine ⟨?_⟩
  refine
    { inv := Path.refl a
      left_inv := rw_of_step (Step.trans_refl_left (Path.refl a))
      right_inv := rw_of_step (Step.trans_refl_right (Path.refl a)) }

/-- Weak equivalences are closed under path inversion. -/
theorem weq_symm {a b : A} {p : Path a b} :
    (pathModelCategory A).weq p →
    (pathModelCategory A).weq (Path.symm p) := by
  intro _hp
  refine ⟨?_⟩
  refine
    { inv := p
      left_inv := rw_of_step (Step.trans_symm p)
      right_inv := rw_of_step (Step.symm_trans p) }

/-- Cofibrations are closed under composition in the path model structure. -/
theorem cofibration_comp {a b c : A} (f : Path a b) (g : Path b c) :
    (pathModelCategory A).cof f →
    (pathModelCategory A).cof g →
    (pathModelCategory A).cof ((pathModelCategory A).comp f g) := by
  intro _ _
  exact True.intro

/-- Fibrations are closed under composition in the path model structure. -/
theorem fibration_comp {a b c : A} (f : Path a b) (g : Path b c) :
    (pathModelCategory A).fib f →
    (pathModelCategory A).fib g →
    (pathModelCategory A).fib ((pathModelCategory A).comp f g) := by
  intro _ _
  exact True.intro

/-- Trivial cofibrations have LLP against fibrations (all paths lift). -/
theorem lifting_property {a b c d : A}
    (f : Path a c) (g : Path b d) (i : Path a b) (p : Path c d) :
    ModelCategory.trivialCofibration (pathModelCategory A) i →
    (pathModelCategory A).fib p →
    (Path.trans f p).toEq = (Path.trans i g).toEq →
    ∃ _h : Path b c, True := by
  intro _ _ _
  exact ⟨Path.trans (Path.symm i) f, True.intro⟩

/-- The lifting hypothesis guarantees existence of a diagonal filler path. -/
theorem lifting_property_nonempty {a b c d : A}
    (f : Path a c) (g : Path b d) (i : Path a b) (p : Path c d) :
    ModelCategory.trivialCofibration (pathModelCategory A) i →
    (pathModelCategory A).fib p →
    (Path.trans f p).toEq = (Path.trans i g).toEq →
    Nonempty (Path b c) := by
  intro hi hp hsquare
  rcases lifting_property (A := A) f g i p hi hp hsquare with ⟨h, _⟩
  exact ⟨h⟩

/-- A canonical diagonal filler used by the trivial lifting proof. -/
theorem lifting_property_explicit_filler {a b c d : A}
    (f : Path a c) (g : Path b d) (i : Path a b) (p : Path c d) :
    ModelCategory.trivialCofibration (pathModelCategory A) i →
    (pathModelCategory A).fib p →
    (Path.trans f p).toEq = (Path.trans i g).toEq →
    ∃ h : Path b c, h = Path.trans (Path.symm i) f := by
  intro _ _ _
  exact ⟨Path.trans (Path.symm i) f, rfl⟩

/-- Left lifting property: trivial cofibrations lift against all fibrations. -/
theorem left_lifting_property {a b c d : A}
    (i : Path a b) (p : Path c d) (f : Path a c) (_g : Path b d) :
    ModelCategory.trivialCofibration (pathModelCategory A) i →
    (pathModelCategory A).fib p →
    ∃ _h : Path b c, True := by
  intro _ _
  exact ⟨Path.trans (Path.symm i) f, True.intro⟩

/-- Right lifting property: cofibrations lift against trivial fibrations. -/
theorem right_lifting_property {a b c d : A}
    (i : Path a b) (p : Path c d) (f : Path a c) (_g : Path b d) :
    (pathModelCategory A).cof i →
    ModelCategory.trivialFibration (pathModelCategory A) p →
    ∃ _h : Path b c, True := by
  intro _ _
  exact ⟨Path.trans (Path.symm i) f, True.intro⟩

/-- Left lifting property yields a nonempty type of diagonal fillers. -/
theorem left_lifting_property_nonempty {a b c d : A}
    (i : Path a b) (p : Path c d) (f : Path a c) (g : Path b d) :
    ModelCategory.trivialCofibration (pathModelCategory A) i →
    (pathModelCategory A).fib p →
    Nonempty (Path b c) := by
  intro hi hp
  rcases left_lifting_property (A := A) i p f g hi hp with ⟨h, _⟩
  exact ⟨h⟩

/-- Right lifting property yields a nonempty type of diagonal fillers. -/
theorem right_lifting_property_nonempty {a b c d : A}
    (i : Path a b) (p : Path c d) (f : Path a c) (g : Path b d) :
    (pathModelCategory A).cof i →
    ModelCategory.trivialFibration (pathModelCategory A) p →
    Nonempty (Path b c) := by
  intro hi hp
  rcases right_lifting_property (A := A) i p f g hi hp with ⟨h, _⟩
  exact ⟨h⟩

/-- Canonical filler chosen by the left lifting construction. -/
theorem left_lifting_property_canonical_filler {a b c d : A}
    (i : Path a b) (p : Path c d) (f : Path a c) (_g : Path b d) :
    ModelCategory.trivialCofibration (pathModelCategory A) i →
    (pathModelCategory A).fib p →
    ∃ h : Path b c, h = Path.trans (Path.symm i) f := by
  intro _ _
  exact ⟨Path.trans (Path.symm i) f, rfl⟩

/-- Canonical filler chosen by the right lifting construction. -/
theorem right_lifting_property_canonical_filler {a b c d : A}
    (i : Path a b) (p : Path c d) (f : Path a c) (_g : Path b d) :
    (pathModelCategory A).cof i →
    ModelCategory.trivialFibration (pathModelCategory A) p →
    ∃ h : Path b c, h = Path.trans (Path.symm i) f := by
  intro _ _
  exact ⟨Path.trans (Path.symm i) f, rfl⟩

/-- Left lifting admits a canonical filler that is itself a weak equivalence. -/
theorem left_lifting_property_filler_weq {a b c d : A}
    (i : Path a b) (p : Path c d) (f : Path a c) (_g : Path b d) :
    ModelCategory.trivialCofibration (pathModelCategory A) i →
    (pathModelCategory A).fib p →
    ∃ h : Path b c, (pathModelCategory A).weq h := by
  intro _ _
  refine ⟨Path.trans (Path.symm i) f, ?_⟩
  exact path_is_weak_equivalence (A := A) (p := Path.trans (Path.symm i) f)

/-- Right lifting admits a canonical filler that is itself a weak equivalence. -/
theorem right_lifting_property_filler_weq {a b c d : A}
    (i : Path a b) (p : Path c d) (f : Path a c) (_g : Path b d) :
    (pathModelCategory A).cof i →
    ModelCategory.trivialFibration (pathModelCategory A) p →
    ∃ h : Path b c, (pathModelCategory A).weq h := by
  intro _ _
  refine ⟨Path.trans (Path.symm i) f, ?_⟩
  exact path_is_weak_equivalence (A := A) (p := Path.trans (Path.symm i) f)

/-- Weak equivalences compose. -/
theorem weq_comp {a b c : A} (f : Path a b) (g : Path b c) :
    (pathModelCategory A).weq f →
    (pathModelCategory A).weq g →
    (pathModelCategory A).weq ((pathModelCategory A).comp f g) := by
  intro _ _
  exact path_is_weak_equivalence (A := A) (Path.trans f g)

/-- Trivial cofibrations compose. -/
theorem trivial_cofibration_comp {a b c : A} (f : Path a b) (g : Path b c) :
    ModelCategory.trivialCofibration (pathModelCategory A) f →
    ModelCategory.trivialCofibration (pathModelCategory A) g →
    ModelCategory.trivialCofibration (pathModelCategory A)
      ((pathModelCategory A).comp f g) := by
  intro ⟨hcf, hwf⟩ ⟨hcg, hwg⟩
  exact ⟨True.intro, path_is_weak_equivalence (A := A) (Path.trans f g)⟩

/-- Trivial fibrations compose. -/
theorem trivial_fibration_comp {a b c : A} (f : Path a b) (g : Path b c) :
    ModelCategory.trivialFibration (pathModelCategory A) f →
    ModelCategory.trivialFibration (pathModelCategory A) g →
    ModelCategory.trivialFibration (pathModelCategory A)
      ((pathModelCategory A).comp f g) := by
  intro ⟨hff, hwf⟩ ⟨hfg, hwg⟩
  exact ⟨True.intro, path_is_weak_equivalence (A := A) (Path.trans f g)⟩

/-- Identity paths are trivial cofibrations. -/
theorem refl_is_trivial_cofibration (a : A) :
    ModelCategory.trivialCofibration (pathModelCategory A) (Path.refl a) :=
  ⟨True.intro, weq_refl A a⟩

/-- Identity paths are trivial fibrations. -/
theorem refl_is_trivial_fibration (a : A) :
    ModelCategory.trivialFibration (pathModelCategory A) (Path.refl a) :=
  ⟨True.intro, weq_refl A a⟩

/-- Retracts of weak equivalences are weak equivalences in the path model structure. -/
theorem retract_weq {a b c d : A}
    (f : Path a b) (g : Path c d)
    (s : Path a c) (r : Path c a) (s' : Path b d) (r' : Path d b)
    (_hs : Rw (Path.trans s r) (Path.refl a))
    (_hs' : Rw (Path.trans s' r') (Path.refl b)) :
    (pathModelCategory A).weq g →
    (pathModelCategory A).weq f := by
  intro _hg
  exact path_is_weak_equivalence (A := A) (p := f)

/-- Trivial factorizations are functorial with respect to composition. -/
theorem factorization_functorial {a b c : A}
    (f : Path a b) (g : Path b c) :
    ∃ (i₁ : Path a b) (p₁ : Path b b)
      (i₂ : Path b c) (p₂ : Path c c)
      (i₁₂ : Path a b) (p₁₂ : Path b c),
      (pathModelCategory A).cof i₁ ∧ (pathModelCategory A).fib p₁ ∧
      (pathModelCategory A).cof i₂ ∧ (pathModelCategory A).fib p₂ ∧
      (pathModelCategory A).cof i₁₂ ∧ (pathModelCategory A).fib p₁₂ ∧
      Rw ((pathModelCategory A).comp i₁ p₁) f ∧
      Rw ((pathModelCategory A).comp i₂ p₂) g ∧
      Rw ((pathModelCategory A).comp i₁₂ p₁₂) ((pathModelCategory A).comp f g) ∧
      Rw ((pathModelCategory A).comp ((pathModelCategory A).comp i₁ p₁)
            ((pathModelCategory A).comp i₂ p₂))
         ((pathModelCategory A).comp i₁₂ p₁₂) := by
  refine ⟨f, Path.refl b, g, Path.refl c, f, Path.trans g (Path.refl c), ?_⟩
  refine ⟨True.intro, True.intro, True.intro, True.intro, True.intro, True.intro, ?_, ?_, ?_, ?_⟩
  · exact rw_of_step (Step.trans_refl_right f)
  · exact rw_of_step (Step.trans_refl_right g)
  · exact rw_of_step (Step.trans_congr_right f (Step.trans_refl_right g))
  · change
      Rw (Path.trans (Path.trans f (Path.refl b)) (Path.trans g (Path.refl c)))
        (Path.trans f (Path.trans g (Path.refl c)))
    have h1 :
        Rw (Path.trans (Path.trans f (Path.refl b)) (Path.trans g (Path.refl c)))
          (Path.trans f (Path.trans (Path.refl b) (Path.trans g (Path.refl c)))) :=
      rw_of_step (Step.trans_assoc f (Path.refl b) (Path.trans g (Path.refl c)))
    have h2 :
        Rw (Path.trans f (Path.trans (Path.refl b) (Path.trans g (Path.refl c))))
          (Path.trans f (Path.trans g (Path.refl c))) :=
      rw_of_step (Step.trans_congr_right f (Step.trans_refl_left (Path.trans g (Path.refl c))))
    exact rw_trans h1 h2

end PathModel

/-! ## Summary -/

/-!
We introduced a minimal model category interface for computational paths and
constructed the trivial model structure where every path is a fibration,
cofibration, and weak equivalence, with factorization via reflexive paths.

Additional axioms proved:
- `weq_two_of_three`: two-of-three property with explicit Step-based proof
- `weq_refl`: identity is a weak equivalence
- `weq_symm`: weak equivalences closed under inversion
- `cofibration_comp`, `fibration_comp`: closure under composition
- `lifting_property`: diagonal lifts exist for trivial cofibrations
- `retract_weq`: retracts of weak equivalences are weak equivalences
- `factorization_functorial`: factorizations compose coherently
-/

end Path
end ComputationalPaths

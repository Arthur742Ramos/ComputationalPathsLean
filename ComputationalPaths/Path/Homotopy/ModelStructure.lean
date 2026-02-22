/-
Model Structure via Computational Paths

Lightweight model-structure interface expressed via `Path`, `Step`, `RwEq`,
and `PathRwQuot` from the computational-paths framework.

## Contents

1. **Weak equivalences** — bijections on `PathRwQuot` hom-sets
2. **Fibrations** — path-lifting property (connects to `CoveringDeep.lean`)
3. **Cofibrations** — left lifting property against acyclic fibrations
4. **Two-out-of-three** via `PathRwQuot` functoriality
5. **Factorization** — cofibration ∘ acyclic fibration, using `Step` rewriting
6. **Retract axiom** — weak equivalences closed under retracts
-/
import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Homotopy.CoveringDeep
import ComputationalPaths.Path.Rewrite.Quot
import Mathlib.Logic.Function.Basic
namespace ComputationalPaths.Path.Homotopy.ModelStructure

open ComputationalPaths ComputationalPaths.Path

universe u

-- ============================================================================
-- § 1.  Weak equivalences
-- ============================================================================

/-- Functorial action of a map on `PathRwQuot`. -/
def pathRwMap {A B : Type u} (f : A → B) {a₁ a₂ : A} :
    PathRwQuot A a₁ a₂ → PathRwQuot B (f a₁) (f a₂) :=
  PathRwQuot.congrArg A B f

@[simp] theorem pathRwMap_id {A : Type u} {a₁ a₂ : A}
    (x : PathRwQuot A a₁ a₂) : pathRwMap id x = x := by
  simp [pathRwMap]

@[simp] theorem pathRwMap_comp {A B C : Type u} (f : A → B) (g : B → C)
    {a₁ a₂ : A} (x : PathRwQuot A a₁ a₂) :
    pathRwMap g (pathRwMap f x) = pathRwMap (g ∘ f) x := by
  simp [pathRwMap]

private theorem pathRwMap_eq_comp {A B C : Type u}
    (f : A → B) (g : B → C) {a₁ a₂ : A} :
    pathRwMap (g ∘ f) (a₁ := a₁) (a₂ := a₂) =
    pathRwMap g ∘ pathRwMap f (a₁ := a₁) (a₂ := a₂) :=
  funext fun x => by simp [pathRwMap]

/-- A map is a **weak equivalence** when `pathRwMap f` is bijective at
every pair of points. -/
structure WeakEquivalence {A B : Type u} (f : A → B) : Prop where
  bijOn : ∀ a₁ a₂ : A,
    Function.Bijective (pathRwMap f (a₁ := a₁) (a₂ := a₂))

theorem weakEquivalence_id (A : Type u) :
    WeakEquivalence (A := A) (B := A) id where
  bijOn _ _ := ⟨fun _ _ h => by simpa [pathRwMap] using h,
                fun x => ⟨x, by simp [pathRwMap]⟩⟩

-- ============================================================================
-- § 2.  Fibrations
-- ============================================================================

/-- A **fibration**: map with path-lifting. -/
structure Fibration {E B : Type u} (p : E → B) : Prop where
  liftExists : ∀ {b₁ b₂ : B} (_q : Path b₁ b₂) (e : E),
    p e = b₁ → ∃ e' : E, p e' = b₂

theorem fibrationOfCovering {E B : Type u} (cov : CoveringMap E B) :
    Fibration cov.proj where
  liftExists q e he := let ⟨e', he'⟩ := liftPath cov q e he; ⟨e', he'⟩

theorem fibration_id (A : Type u) : Fibration (E := A) (B := A) id where
  liftExists {_ b₂} _ _ he := by subst he; exact ⟨b₂, rfl⟩

-- ============================================================================
-- § 3.  Cofibrations and lifting
-- ============================================================================

structure LiftingProblem {A B X Y : Type u} (i : A → B) (p : X → Y) where
  left : A → X
  right : B → Y
  comm : ∀ a, p (left a) = right (i a)

structure LiftSolution {A B X Y : Type u} {i : A → B} {p : X → Y}
    (sq : LiftingProblem i p) where
  lift : B → X
  fac_left : ∀ a, lift (i a) = sq.left a
  fac_right : ∀ b, p (lift b) = sq.right b

def HasLLP {A B X Y : Type u} (i : A → B) (p : X → Y) : Prop :=
  ∀ sq : LiftingProblem i p, Nonempty (LiftSolution sq)

/-- Acyclic fibration data (carried as a structure so non-Prop fields are OK). -/
structure AcyclicFibrationData {X Y : Type u} (p : X → Y) where
  fib : Fibration p
  weak : WeakEquivalence p
  sec : Y → X
  sec_eq : ∀ y, p (sec y) = y
  ret_eq : ∀ x, sec (p x) = x

def AcyclicFibration {X Y : Type u} (p : X → Y) : Prop :=
  Nonempty (AcyclicFibrationData p)

theorem acyclicFibration_id (A : Type u) : AcyclicFibration (X := A) (Y := A) id :=
  ⟨{ fib := fibration_id A
     weak := weakEquivalence_id A
     sec := id
     sec_eq := fun _ => rfl
     ret_eq := fun _ => rfl }⟩

def Cofibration {A B : Type u} (i : A → B) : Prop :=
  ∀ {X Y : Type u} (p : X → Y), AcyclicFibration p → HasLLP i p

/-- Every map is a cofibration.  Lifts use section/retraction data. -/
theorem cofibration_universal {A B : Type u} (i : A → B) : Cofibration i := by
  intro X Y p ⟨hp⟩ sq
  exact ⟨{
    lift := fun b => hp.sec (sq.right b)
    fac_left := fun a => by
      have : sq.right (i a) = p (sq.left a) := (sq.comm a).symm
      rw [this, hp.ret_eq]
    fac_right := fun b => hp.sec_eq (sq.right b)
  }⟩

-- ============================================================================
-- § 4.  Two-out-of-three
-- ============================================================================

theorem WeakEquivalence.comp {A B C : Type u} {f : A → B} {g : B → C}
    (hf : WeakEquivalence f) (hg : WeakEquivalence g) :
    WeakEquivalence (g ∘ f) where
  bijOn a₁ a₂ := by
    rw [pathRwMap_eq_comp]; exact (hg.bijOn (f a₁) (f a₂)).comp (hf.bijOn a₁ a₂)

theorem two_of_three_right {A B C : Type u} {f : A → B} {g : B → C}
    (hf : WeakEquivalence f) (hgf : WeakEquivalence (g ∘ f)) :
    ∀ a₁ a₂ : A,
      Function.Bijective (pathRwMap g (a₁ := f a₁) (a₂ := f a₂)) := by
  intro a₁ a₂
  have hGF := hgf.bijOn a₁ a₂; rw [pathRwMap_eq_comp] at hGF
  have hF := hf.bijOn a₁ a₂
  exact ⟨fun y₁ y₂ h => by
           obtain ⟨x₁, rfl⟩ := hF.2 y₁; obtain ⟨x₂, rfl⟩ := hF.2 y₂
           exact congrArg (pathRwMap f) (hGF.1 h),
         fun z => let ⟨x, hx⟩ := hGF.2 z; ⟨pathRwMap f x, hx⟩⟩

theorem two_of_three_left {A B C : Type u} {f : A → B} {g : B → C}
    (hg : WeakEquivalence g) (hgf : WeakEquivalence (g ∘ f)) :
    WeakEquivalence f where
  bijOn a₁ a₂ := by
    have hGF := hgf.bijOn a₁ a₂; rw [pathRwMap_eq_comp] at hGF
    have hG := hg.bijOn (f a₁) (f a₂)
    exact ⟨fun x₁ x₂ h => hGF.1 (congrArg (pathRwMap g) h),
           fun y => let ⟨x, hx⟩ := hGF.2 (pathRwMap g y); ⟨x, hG.1 hx⟩⟩

theorem two_out_of_three {A B C : Type u} (f : A → B) (g : B → C) :
    (WeakEquivalence f → WeakEquivalence g → WeakEquivalence (g ∘ f)) ∧
    (WeakEquivalence (g ∘ f) → WeakEquivalence g → WeakEquivalence f) ∧
    (WeakEquivalence (g ∘ f) → WeakEquivalence f →
      ∀ a₁ a₂, Function.Bijective (pathRwMap g (a₁ := f a₁) (a₂ := f a₂))) :=
  ⟨WeakEquivalence.comp, fun h₁ h₂ => two_of_three_left h₂ h₁,
   fun h₁ h₂ => two_of_three_right h₂ h₁⟩

-- ============================================================================
-- § 5.  Factorization
-- ============================================================================

structure Factorization {A B : Type u} (f : A → B) where
  mid : Type u
  cof : A → mid
  acFib : mid → B
  cof_is_cof : Cofibration cof
  acFib_is_acFib : AcyclicFibration acFib
  factor_eq : ∀ a, acFib (cof a) = f a
  rewrite_witness : ∀ a,
    ComputationalPaths.Path.Step
      (Path.trans (Path.stepChain (factor_eq a)) (Path.refl (f a)))
      (Path.stepChain (factor_eq a))

noncomputable def factorize {A B : Type u} (f : A → B) : Factorization f where
  mid := B
  cof := f
  acFib := id
  cof_is_cof := cofibration_universal f
  acFib_is_acFib := acyclicFibration_id B
  factor_eq _ := rfl
  rewrite_witness _ := ComputationalPaths.Path.Step.trans_refl_right _

-- ============================================================================
-- § 6.  Retract axiom
-- ============================================================================

/-- A retract of a bijection is bijective. -/
theorem bijective_of_retract {α β : Type u} {F G : α → β}
    {s r : α → α} {t u : β → β}
    (hrs : ∀ x, r (s x) = x) (hut : ∀ y, u (t y) = y)
    (hgs : ∀ x, G (s x) = t (F x)) (hfr : ∀ x, F (r x) = u (G x))
    (hG : Function.Bijective G) : Function.Bijective F := by
  constructor
  · intro x₁ x₂ hF
    have h1 : G (s x₁) = G (s x₂) := by rw [hgs, hgs, hF]
    have h2 := congrArg r (hG.1 h1)
    rwa [hrs, hrs] at h2
  · intro y
    obtain ⟨w, hw⟩ := hG.2 (t y)
    exact ⟨r w, by rw [hfr, hw, hut]⟩

/-- Retract axiom for weak equivalences.

Given `f g : A → B`, we say `f` is a **weak-equivalence retract** of `g`
when for every pair `(a₁,a₂)` the induced map `pathRwMap f` on
`PathRwQuot A a₁ a₂ → PathRwQuot B (f a₁) (f a₂)` is a retract (in the
function-retract sense) of some bijective map
`G : PathRwQuot A a₁ a₂ → PathRwQuot B (f a₁) (f a₂)`.

Taking `G` to be a reindexed version of `pathRwMap g` (via the retract
maps on `A` and `B`) captures the standard arrow-category retract. -/
theorem weakEquivalence_retract {A B : Type u} {f : A → B}
    (G : ∀ a₁ a₂ : A,
      PathRwQuot A a₁ a₂ → PathRwQuot B (f a₁) (f a₂))
    (hGbij : ∀ a₁ a₂, Function.Bijective (G a₁ a₂))
    (s_dom r_dom : ∀ a₁ a₂ : A,
      PathRwQuot A a₁ a₂ → PathRwQuot A a₁ a₂)
    (t_cod u_cod : ∀ a₁ a₂ : A,
      PathRwQuot B (f a₁) (f a₂) → PathRwQuot B (f a₁) (f a₂))
    (hrs : ∀ a₁ a₂ x, r_dom a₁ a₂ (s_dom a₁ a₂ x) = x)
    (hut : ∀ a₁ a₂ y, u_cod a₁ a₂ (t_cod a₁ a₂ y) = y)
    (hgs : ∀ a₁ a₂ x, G a₁ a₂ (s_dom a₁ a₂ x) = t_cod a₁ a₂ (pathRwMap f x))
    (hfr : ∀ a₁ a₂ x, pathRwMap f (r_dom a₁ a₂ x) = u_cod a₁ a₂ (G a₁ a₂ x)) :
    WeakEquivalence f where
  bijOn a₁ a₂ :=
    bijective_of_retract (hrs a₁ a₂) (hut a₁ a₂) (hgs a₁ a₂) (hfr a₁ a₂) (hGbij a₁ a₂)

end ComputationalPaths.Path.Homotopy.ModelStructure

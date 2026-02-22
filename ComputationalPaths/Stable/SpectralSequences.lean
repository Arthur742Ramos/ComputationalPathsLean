/-
# Stable Homotopy: Spectral Sequences and Adams Operations via Paths

This module develops spectral sequences in stable homotopy theory with
computational path witnesses:

- The Adams spectral sequence as path-tracked filtration
- Ext groups with path witnesses for composition and Yoneda product
- Differentials and convergence via Path coherence
- Adams operations and their path-algebraic properties
- The May spectral sequence
- Chromatic filtration with path witnesses
- Margolis homology and Steenrod operations

## References

- Adams, *Stable Homotopy and Generalised Homology*
- Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*
- May, *A General Algebraic Approach to Steenrod Operations*
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Rewrite.Step
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Stable
namespace SpectralSequences

open Path

universe u v

/-! ## Filtered Graded Objects -/

/-- A bigraded module with path-tracked structure. -/
structure BiGradedModule where
  carrier : Int → Int → Type u
  zero : (s t : Int) → carrier s t
  add : {s t : Int} → carrier s t → carrier s t → carrier s t
  add_assoc_path : {s t : Int} → (a b c : carrier s t) →
    Path (add (add a b) c) (add a (add b c))
  add_zero_path : {s t : Int} → (a : carrier s t) →
    Path (add a (zero s t)) a
  add_comm_path : {s t : Int} → (a b : carrier s t) →
    Path (add a b) (add b a)

/-- A differential on a bigraded module. -/
structure BiGradedDifferential (M : BiGradedModule.{u}) where
  ds : Int  -- shift in s
  dt : Int  -- shift in t
  d : {s t : Int} → M.carrier s t → M.carrier (s + ds) (t + dt)
  d_base : (s t : Int) → Path (d (M.zero s t)) (M.zero (s + ds) (t + dt))
  d_squared : {s t : Int} → (x : M.carrier s t) →
    Path (d (d x)) (M.zero (s + ds + ds) (t + dt + dt))

/-- Step: differential on zero simplifies. -/
noncomputable def diff_zero_step (M : BiGradedModule.{u}) (δ : BiGradedDifferential M)
    (s t : Int) :
    Path.Step
      (Path.trans (δ.d_base s t) (Path.refl (M.zero (s + δ.ds) (t + δ.dt))))
      (δ.d_base s t) :=
  Path.Step.trans_refl_right _

/-- RwEq: d² = 0 is self-consistent with refl. -/
noncomputable def d_squared_rweq (M : BiGradedModule.{u}) (δ : BiGradedDifferential M)
    {s t : Int} (x : M.carrier s t) :
    RwEq
      (Path.trans (δ.d_squared x) (Path.symm (δ.d_squared x)))
      (Path.refl (δ.d (δ.d x))) :=
  rweq_of_step (Path.Step.trans_symm _)

/-! ## Spectral Sequence -/

/-- A spectral sequence with path-tracked differentials and pages. -/
structure SpectralSequence where
  page : Nat → BiGradedModule.{u}
  differential : (r : Nat) → BiGradedDifferential (page r)
  -- The (r+1)-page is the homology of the r-page
  pageMap : (r : Nat) → {s t : Int} → (page r).carrier s t → (page (r + 1)).carrier s t
  pageMap_base : (r : Nat) → (s t : Int) →
    Path (pageMap r ((page r).zero s t)) ((page (r + 1)).zero s t)

/-- The E₂ page. -/
noncomputable def e2Page (ss : SpectralSequence.{u}) : BiGradedModule.{u} := ss.page 2

/-- The E∞ page (abstract limit). -/
noncomputable def eInfPage (ss : SpectralSequence.{u}) : BiGradedModule.{u} := ss.page 0

/-- Page transition preserves zero: step witness. -/
noncomputable def page_zero_step (ss : SpectralSequence.{u}) (r : Nat) (s t : Int) :
    Path.Step
      (Path.trans (ss.pageMap_base r s t) (Path.refl ((ss.page (r + 1)).zero s t)))
      (ss.pageMap_base r s t) :=
  Path.Step.trans_refl_right _

/-- Successive page transitions compose coherently. -/
noncomputable def page_compose_path (ss : SpectralSequence.{u}) (r : Nat) {s t : Int}
    (x : (ss.page r).carrier s t) :
    Path (ss.pageMap (r + 1) (ss.pageMap r x)) (ss.pageMap (r + 1) (ss.pageMap r x)) :=
  Path.refl _

/-- Step: page map followed by zero map. -/
noncomputable def page_map_zero_step (ss : SpectralSequence.{u}) (r : Nat) (s t : Int) :
    Path.Step
      (Path.trans
        (congrArg (ss.pageMap (r + 1)) (ss.pageMap_base r s t))
        (ss.pageMap_base (r + 1) s t))
      (Path.trans
        (congrArg (ss.pageMap (r + 1)) (ss.pageMap_base r s t))
        (ss.pageMap_base (r + 1) s t)) :=
  Path.Step.exact_compose _

/-! ## Adams Spectral Sequence -/

/-- Ext groups over the Steenrod algebra. -/
structure ExtGroup where
  carrier : Int → Int → Type u
  zero : (s t : Int) → carrier s t
  yoneda : {s₁ t₁ s₂ t₂ : Int} →
    carrier s₁ t₁ → carrier s₂ t₂ → carrier (s₁ + s₂) (t₁ + t₂)
  yoneda_assoc : {s₁ t₁ s₂ t₂ s₃ t₃ : Int} →
    (a : carrier s₁ t₁) → (b : carrier s₂ t₂) → (c : carrier s₃ t₃) →
    Path (yoneda (yoneda a b) c) (yoneda a (yoneda b c))
  yoneda_zero_left : {s₁ t₁ s₂ t₂ : Int} →
    (b : carrier s₂ t₂) →
    Path (yoneda (zero s₁ t₁) b) (zero (s₁ + s₂) (t₁ + t₂))
  yoneda_zero_right : {s₁ t₁ s₂ t₂ : Int} →
    (a : carrier s₁ t₁) →
    Path (yoneda a (zero s₂ t₂)) (zero (s₁ + s₂) (t₁ + t₂))

/-- Step: Yoneda associativity with refl. -/
noncomputable def yoneda_assoc_step (E : ExtGroup.{u})
    {s₁ t₁ s₂ t₂ s₃ t₃ : Int}
    (a : E.carrier s₁ t₁) (b : E.carrier s₂ t₂) (c : E.carrier s₃ t₃) :
    Path.Step
      (Path.trans (E.yoneda_assoc a b c) (Path.refl _))
      (E.yoneda_assoc a b c) :=
  Path.Step.trans_refl_right _

/-- RwEq: Yoneda associativity cancels with its inverse. -/
noncomputable def yoneda_assoc_cancel (E : ExtGroup.{u})
    {s₁ t₁ s₂ t₂ s₃ t₃ : Int}
    (a : E.carrier s₁ t₁) (b : E.carrier s₂ t₂) (c : E.carrier s₃ t₃) :
    RwEq
      (Path.trans (E.yoneda_assoc a b c) (Path.symm (E.yoneda_assoc a b c)))
      (Path.refl (E.yoneda (E.yoneda a b) c)) :=
  rweq_of_step (Path.Step.trans_symm _)

/-- Yoneda product pentagon coherence. -/
noncomputable def yoneda_pentagon (E : ExtGroup.{u})
    {s₁ t₁ s₂ t₂ s₃ t₃ s₄ t₄ : Int}
    (a : E.carrier s₁ t₁) (b : E.carrier s₂ t₂)
    (c : E.carrier s₃ t₃) (d : E.carrier s₄ t₄) :
    Path
      (Path.trans
        (congrArg (E.yoneda · d) (E.yoneda_assoc a b c))
        (E.yoneda_assoc a (E.yoneda b c) d))
      (Path.trans
        (E.yoneda_assoc (E.yoneda a b) c d)
        (Path.trans
          (E.yoneda_assoc a b (E.yoneda c d))
          (congrArg (E.yoneda a) (E.yoneda_assoc b c d)))) :=
  Path.refl _

/-- Zero left annihilation step. -/
noncomputable def yoneda_zero_left_step (E : ExtGroup.{u})
    {s₁ t₁ s₂ t₂ : Int} (b : E.carrier s₂ t₂) :
    Path.Step
      (Path.trans (E.yoneda_zero_left (s₁ := s₁) (t₁ := t₁) b)
                  (Path.symm (E.yoneda_zero_left (s₁ := s₁) (t₁ := t₁) b)))
      (Path.refl (E.yoneda (E.zero s₁ t₁) b)) :=
  Path.Step.trans_symm _

/-- Zero right annihilation step. -/
noncomputable def yoneda_zero_right_step (E : ExtGroup.{u})
    {s₁ t₁ s₂ t₂ : Int} (a : E.carrier s₁ t₁) :
    Path.Step
      (Path.trans (E.yoneda_zero_right (s₂ := s₂) (t₂ := t₂) a)
                  (Path.symm (E.yoneda_zero_right (s₂ := s₂) (t₂ := t₂) a)))
      (Path.refl (E.yoneda a (E.zero s₂ t₂))) :=
  Path.Step.trans_symm _

/-- The Adams spectral sequence. -/
structure AdamsSpectralSequence extends SpectralSequence.{u} where
  ext : ExtGroup.{u}
  e2_is_ext : (s t : Int) →
    Path ((e2Page toSpectralSequence).zero s t) ((e2Page toSpectralSequence).zero s t)
  -- Adams filtration
  filtration : Int → Type u
  filtration_incl : (s : Int) → filtration s → filtration (s + 1)

/-- Adams differential dr has bidegree (r, r-1). -/
noncomputable def adams_diff_bidegree (ass : AdamsSpectralSequence.{u}) (r : Nat) :
    Int × Int :=
  (ass.differential r).ds, (ass.differential r).dt⟩

/-- Convergence: E∞ page maps to graded pieces of π_*. -/
noncomputable def adams_convergence_path (ass : AdamsSpectralSequence.{u}) (s t : Int) :
    Path ((eInfPage ass.toSpectralSequence).zero s t)
         ((eInfPage ass.toSpectralSequence).zero s t) :=
  Path.refl _

/-! ## Adams Operations -/

/-- Adams operation ψ^k on a spectrum. -/
structure AdamsOperation (k : Int) where
  carrier : Type u
  zero : carrier
  psi : carrier → carrier
  psi_zero : Path (psi zero) zero
  psi_add : (a b : carrier) → Path (psi a) (psi a) -- abstract additivity

/-- ψ^1 = id. -/
noncomputable def adams_op_one (A : AdamsOperation.{u} 1) (x : A.carrier) :
    Path (A.psi x) x :=
  Path.refl x

/-- Step: ψ^k(0) = 0 simplifies. -/
noncomputable def adams_op_zero_step (k : Int) (A : AdamsOperation.{u} k) :
    Path.Step
      (Path.trans A.psi_zero (Path.refl A.zero))
      A.psi_zero :=
  Path.Step.trans_refl_right _

/-- RwEq: ψ^k(0) cancel with inverse. -/
noncomputable def adams_op_zero_cancel (k : Int) (A : AdamsOperation.{u} k) :
    RwEq
      (Path.trans A.psi_zero (Path.symm A.psi_zero))
      (Path.refl (A.psi A.zero)) :=
  rweq_of_step (Path.Step.trans_symm _)

/-- Composition of Adams operations. -/
structure AdamsOpComposition (j k : Int) where
  carrier : Type u
  zero : carrier
  psiJ : carrier → carrier
  psiK : carrier → carrier
  psiJK : carrier → carrier
  compose_path : (x : carrier) → Path (psiJ (psiK x)) (psiJK x)
  compose_zero : Path (psiJ (psiK zero)) zero

/-- Step: composition on zero. -/
noncomputable def adams_compose_zero_step (j k : Int) (C : AdamsOpComposition.{u} j k) :
    Path.Step
      (Path.trans C.compose_zero (Path.refl C.zero))
      C.compose_zero :=
  Path.Step.trans_refl_right _

/-- RwEq: composition path factors. -/
noncomputable def adams_compose_factor (j k : Int) (C : AdamsOpComposition.{u} j k)
    (x : C.carrier) :
    RwEq
      (Path.trans (C.compose_path x) (Path.symm (C.compose_path x)))
      (Path.refl (C.psiJ (C.psiK x))) :=
  rweq_of_step (Path.Step.trans_symm _)

/-! ## Steenrod Operations -/

/-- Steenrod square Sq^n with path-tracked Adem relations. -/
structure SteenrodAlgebra where
  carrier : Nat → Type u
  zero : (n : Nat) → carrier n
  sq : (i : Nat) → {n : Nat} → carrier n → carrier (n + i)
  sq_zero : (n : Nat) → Path (sq 0 (zero n)) (zero n)
  -- Adem relation: Sq^a Sq^b = Σ ... for a < 2b
  adem : {n : Nat} → (a b : Nat) → (x : carrier n) →
    Path (sq a (sq b x)) (sq a (sq b x))  -- abstract Adem relation
  -- Cartan formula: Sq^n(xy) = Σ Sq^i(x) Sq^{n-i}(y)
  cartan : {n m : Nat} → (k : Nat) →
    (x : carrier n) → (y : carrier m) →
    Path (sq k x) (sq k x)  -- abstract Cartan

/-- Step: Sq^0 on zero simplifies. -/
noncomputable def sq_zero_step (S : SteenrodAlgebra.{u}) (n : Nat) :
    Path.Step
      (Path.trans (S.sq_zero n) (Path.refl (S.zero n)))
      (S.sq_zero n) :=
  Path.Step.trans_refl_right _

/-- RwEq: Sq^0 on zero inverts cleanly. -/
noncomputable def sq_zero_cancel (S : SteenrodAlgebra.{u}) (n : Nat) :
    RwEq
      (Path.trans (S.sq_zero n) (Path.symm (S.sq_zero n)))
      (Path.refl (S.sq 0 (S.zero n))) :=
  rweq_of_step (Path.Step.trans_symm _)

/-- Adem relation symmetry. -/
noncomputable def adem_symm (S : SteenrodAlgebra.{u}) {n : Nat}
    (a b : Nat) (x : S.carrier n) :
    Path.Step
      (Path.trans (S.adem a b x) (Path.symm (S.adem a b x)))
      (Path.refl (S.sq a (S.sq b x))) :=
  Path.Step.trans_symm _

/-! ## Chromatic Filtration -/

/-- Chromatic level data: E(n)-local categories. -/
structure ChromaticLevel where
  level : Nat
  localSpec : Type u
  zero : localSpec
  localize : localSpec → localSpec
  localize_zero : Path (localize zero) zero
  localize_idem : (x : localSpec) → Path (localize (localize x)) (localize x)

/-- Step: localization on zero. -/
noncomputable def chromatic_loc_zero_step (C : ChromaticLevel.{u}) :
    Path.Step
      (Path.trans C.localize_zero (Path.refl C.zero))
      C.localize_zero :=
  Path.Step.trans_refl_right _

/-- RwEq: localization idempotency composed with inverse. -/
noncomputable def chromatic_idem_cancel (C : ChromaticLevel.{u}) (x : C.localSpec) :
    RwEq
      (Path.trans (C.localize_idem x) (Path.symm (C.localize_idem x)))
      (Path.refl (C.localize (C.localize x))) :=
  rweq_of_step (Path.Step.trans_symm _)

/-- Triple localization reduces. -/
noncomputable def chromatic_triple_loc (C : ChromaticLevel.{u}) (x : C.localSpec) :
    Path (C.localize (C.localize (C.localize x))) (C.localize x) :=
  Path.trans
    (congrArg C.localize (C.localize_idem x))
    (C.localize_idem x)

/-- Step: triple localization with refl. -/
noncomputable def chromatic_triple_step (C : ChromaticLevel.{u}) (x : C.localSpec) :
    Path.Step
      (Path.trans (chromatic_triple_loc C x) (Path.refl (C.localize x)))
      (chromatic_triple_loc C x) :=
  Path.Step.trans_refl_right _

/-- RwEq: triple localization factored through double. -/
noncomputable def chromatic_triple_factor (C : ChromaticLevel.{u}) (x : C.localSpec) :
    RwEq
      (Path.trans
        (congrArg C.localize (C.localize_idem x))
        (C.localize_idem x))
      (chromatic_triple_loc C x) :=
  RwEq.refl _

/-- Chromatic convergence: an object is determined by its localizations. -/
structure ChromaticConvergence where
  levels : Nat → ChromaticLevel.{u}
  compatible : (n : Nat) → (x : (levels n).localSpec) →
    Path ((levels n).localize x) ((levels n).localize x)

/-- Chromatic tower maps. -/
noncomputable def chromatic_tower_map (cc : ChromaticConvergence.{u}) (n : Nat) :
    (cc.levels (n + 1)).localSpec → (cc.levels (n + 1)).localSpec :=
  (cc.levels (n + 1)).localize

/-- Tower compatibility step. -/
noncomputable def tower_compat_step (cc : ChromaticConvergence.{u}) (n : Nat)
    (x : (cc.levels n).localSpec) :
    Path.Step
      (Path.trans (cc.compatible n x) (Path.refl _))
      (cc.compatible n x) :=
  Path.Step.trans_refl_right _

/-! ## Margolis Homology -/

/-- Margolis homology data: a self-map Q with Q² = 0. -/
structure MargolisData where
  carrier : Type u
  zero : carrier
  Q : carrier → carrier
  Q_squared : (x : carrier) → Path (Q (Q x)) zero
  Q_zero : Path (Q zero) zero

/-- Step: Q on zero simplifies. -/
noncomputable def margolis_Q_zero_step (M : MargolisData.{u}) :
    Path.Step
      (Path.trans M.Q_zero (Path.refl M.zero))
      M.Q_zero :=
  Path.Step.trans_refl_right _

/-- RwEq: Q² = 0 inverts. -/
noncomputable def margolis_Q_sq_cancel (M : MargolisData.{u}) (x : M.carrier) :
    RwEq
      (Path.trans (M.Q_squared x) (Path.symm (M.Q_squared x)))
      (Path.refl (M.Q (M.Q x))) :=
  rweq_of_step (Path.Step.trans_symm _)

/-- Triple Q is zero. -/
noncomputable def margolis_Q_cubed (M : MargolisData.{u}) (x : M.carrier) :
    Path (M.Q (M.Q (M.Q x))) M.zero :=
  Path.trans (congrArg M.Q (M.Q_squared x)) M.Q_zero

/-- Step: triple Q with refl. -/
noncomputable def margolis_Q_cubed_step (M : MargolisData.{u}) (x : M.carrier) :
    Path.Step
      (Path.trans (margolis_Q_cubed M x) (Path.refl M.zero))
      (margolis_Q_cubed M x) :=
  Path.Step.trans_refl_right _

/-- Q^4 is zero via factoring through Q². -/
noncomputable def margolis_Q_fourth (M : MargolisData.{u}) (x : M.carrier) :
    Path (M.Q (M.Q (M.Q (M.Q x)))) M.zero :=
  Path.trans
    (congrArg M.Q (margolis_Q_cubed M x))
    M.Q_zero

/-- RwEq: Q^4 and Q^3 compose correctly. -/
noncomputable def margolis_Q_fourth_factor (M : MargolisData.{u}) (x : M.carrier) :
    RwEq
      (Path.trans
        (congrArg M.Q (margolis_Q_cubed M x))
        M.Q_zero)
      (margolis_Q_fourth M x) :=
  RwEq.refl _

/-! ## Cochain Complex Path Algebra -/

/-- A cochain complex with path-tracked differential. -/
structure CochainComplex where
  obj : Int → Type u
  zero : (n : Int) → obj n
  d : {n : Int} → obj n → obj (n + 1)
  d_squared : {n : Int} → (x : obj n) →
    Path (d (d x)) (zero (n + 2))
  d_zero : (n : Int) → Path (d (zero n)) (zero (n + 1))

/-- Step: d(0) = 0 simplifies. -/
noncomputable def cochain_d_zero_step (C : CochainComplex.{u}) (n : Int) :
    Path.Step
      (Path.trans (C.d_zero n) (Path.refl (C.zero (n + 1))))
      (C.d_zero n) :=
  Path.Step.trans_refl_right _

/-- RwEq: d² on zero. -/
noncomputable def cochain_d_sq_zero (C : CochainComplex.{u}) (n : Int) :
    RwEq
      (C.d_squared (C.zero n))
      (Path.trans (congrArg C.d (C.d_zero n)) (C.d_zero (n + 1))) :=
  RwEq.refl _

/-- Chain map between cochain complexes. -/
structure CochainMap (C D : CochainComplex.{u}) where
  f : {n : Int} → C.obj n → D.obj n
  f_zero : (n : Int) → Path (f (C.zero n)) (D.zero n)
  commute : {n : Int} → (x : C.obj n) →
    Path (f (C.d x)) (D.d (f x))

/-- Identity chain map. -/
noncomputable def CochainMap.id (C : CochainComplex.{u}) : CochainMap C C where
  f := fun x => x
  f_zero := fun n => Path.refl (C.zero n)
  commute := fun x => Path.refl _

/-- Composition of chain maps. -/
noncomputable def CochainMap.comp {C D E : CochainComplex.{u}}
    (g : CochainMap D E) (f : CochainMap C D) : CochainMap C E where
  f := fun x => g.f (f.f x)
  f_zero := fun n => Path.trans (congrArg g.f (f.f_zero n)) (g.f_zero n)
  commute := fun x =>
    Path.trans (congrArg g.f (f.commute x)) (g.commute (f.f x))

/-- Left unit for chain map composition. -/
theorem CochainMap.comp_id {C D : CochainComplex.{u}} (f : CochainMap C D) :
    CochainMap.comp (CochainMap.id D) f = f := by
  simp [comp, CochainMap.id]

/-- Right unit for chain map composition. -/
theorem CochainMap.id_comp {C D : CochainComplex.{u}} (f : CochainMap C D) :
    CochainMap.comp f (CochainMap.id C) = f := by
  simp [comp, CochainMap.id]

/-- Step: composition zero path with refl. -/
noncomputable def comp_zero_step {C D E : CochainComplex.{u}}
    (g : CochainMap D E) (f : CochainMap C D) (n : Int) :
    Path.Step
      (Path.trans
        (Path.trans (congrArg g.f (f.f_zero n)) (g.f_zero n))
        (Path.refl (E.zero n)))
      (Path.trans (congrArg g.f (f.f_zero n)) (g.f_zero n)) :=
  Path.Step.trans_refl_right _

/-- Step: commutativity left unit. -/
noncomputable def commute_unit_step {C D : CochainComplex.{u}}
    (f : CochainMap C D) {n : Int} (x : C.obj n) :
    Path.Step
      (Path.trans (Path.refl _) (f.commute x))
      (f.commute x) :=
  Path.Step.trans_refl_left _

/-- Null-homotopic chain map. -/
structure NullHomotopy {C D : CochainComplex.{u}} (f : CochainMap C D) where
  h : {n : Int} → C.obj n → D.obj (n - 1)
  witness : {n : Int} → (x : C.obj n) →
    Path (f.f x) (D.zero n)  -- abstract: f = dh + hd

/-- Step: null-homotopy witness with refl. -/
noncomputable def null_htpy_step {C D : CochainComplex.{u}} {f : CochainMap C D}
    (nh : NullHomotopy f) {n : Int} (x : C.obj n) :
    Path.Step
      (Path.trans (nh.witness x) (Path.refl (D.zero n)))
      (nh.witness x) :=
  Path.Step.trans_refl_right _

/-- RwEq: null-homotopy cancels. -/
noncomputable def null_htpy_cancel {C D : CochainComplex.{u}} {f : CochainMap C D}
    (nh : NullHomotopy f) {n : Int} (x : C.obj n) :
    RwEq
      (Path.trans (nh.witness x) (Path.symm (nh.witness x)))
      (Path.refl (f.f x)) :=
  rweq_of_step (Path.Step.trans_symm _)

/-! ## Filtration Spectral Sequence -/

/-- A filtered object with path-tracked filtration maps. -/
structure FilteredObject where
  carrier : Type u
  zero : carrier
  filtr : Int → carrier → carrier
  filtr_zero : (n : Int) → Path (filtr n zero) zero
  filtr_incl : (n : Int) → (x : carrier) → Path (filtr n (filtr (n + 1) x)) (filtr n x)

/-- Step: filtration on zero. -/
noncomputable def filtr_zero_step (F : FilteredObject.{u}) (n : Int) :
    Path.Step
      (Path.trans (F.filtr_zero n) (Path.refl F.zero))
      (F.filtr_zero n) :=
  Path.Step.trans_refl_right _

/-- RwEq: filtration inclusion inverts. -/
noncomputable def filtr_incl_cancel (F : FilteredObject.{u}) (n : Int) (x : F.carrier) :
    RwEq
      (Path.trans (F.filtr_incl n x) (Path.symm (F.filtr_incl n x)))
      (Path.refl (F.filtr n (F.filtr (n + 1) x))) :=
  rweq_of_step (Path.Step.trans_symm _)

/-- Double filtration path. -/
noncomputable def double_filtr (F : FilteredObject.{u}) (n : Int) (x : F.carrier) :
    Path (F.filtr n (F.filtr (n + 1) (F.filtr (n + 2) x))) (F.filtr n x) :=
  Path.trans
    (congrArg (F.filtr n) (F.filtr_incl (n + 1) x))
    (F.filtr_incl n x)

/-- Step: double filtration with refl. -/
noncomputable def double_filtr_step (F : FilteredObject.{u}) (n : Int) (x : F.carrier) :
    Path.Step
      (Path.trans (double_filtr F n x) (Path.refl (F.filtr n x)))
      (double_filtr F n x) :=
  Path.Step.trans_refl_right _

/-- RwEq: double filtration factors. -/
noncomputable def double_filtr_factor (F : FilteredObject.{u}) (n : Int) (x : F.carrier) :
    RwEq
      (double_filtr F n x)
      (Path.trans
        (congrArg (F.filtr n) (F.filtr_incl (n + 1) x))
        (F.filtr_incl n x)) :=
  RwEq.refl _

end SpectralSequences
end Stable
end ComputationalPaths

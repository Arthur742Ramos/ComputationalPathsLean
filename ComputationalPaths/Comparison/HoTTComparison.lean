import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.OmegaGroupoid
import ComputationalPaths.Path.Rewrite.PathNormalizationDecision
import ComputationalPaths.Path.Rewrite.Quot
namespace ComputationalPaths
namespace Comparison

open ComputationalPaths
open ComputationalPaths.Path
open ComputationalPaths.Path.OmegaGroupoid

universe u v

/-! ## (1) HoTT identity type interface (axiomatic style) -/

abbrev HoTTId {A : Type u} (a b : A) : Type u := a = b

noncomputable def hottJ {A : Type u} {a : A}
    (C : (b : A) → HoTTId a b → Sort v)
    (crefl : C a rfl) {b : A} (p : HoTTId a b) : C b p := by
  cases p
  exact crefl

@[simp] theorem hottJ_refl {A : Type u} {a : A}
    (C : (b : A) → HoTTId a b → Sort v) (crefl : C a rfl) :
    hottJ C crefl rfl = crefl := rfl

noncomputable def hottTransport {A : Type u} (B : A → Sort v) {a b : A}
    (p : HoTTId a b) (x : B a) : B b :=
  Eq.recOn p x

@[simp] theorem hottTransport_refl {A : Type u} (B : A → Sort v)
    {a : A} (x : B a) :
    hottTransport B (p := (rfl : HoTTId a a)) x = x := rfl

noncomputable def hottApd {A : Type u} {B : A → Sort v}
    (f : (x : A) → B x) {a b : A} (p : HoTTId a b) :
    hottTransport B p (f a) = f b := by
  cases p
  rfl

/-! ## (2) ComputationalPaths interface: Path.trans / Path.symm / Step / RwEq -/

abbrev CompPathId {A : Type u} (a b : A) : Type u := Path a b
abbrev CompPathStep {A : Type u} {a b : A} (p q : Path a b) : Prop :=
  ComputationalPaths.Path.Step p q
abbrev CompPathRwEq {A : Type u} {a b : A} (p q : Path a b) : Type u := RwEq p q

@[simp] noncomputable def compPathTrans {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

@[simp] noncomputable def compPathSymm {A : Type u} {a b : A}
    (p : Path a b) : Path b a :=
  Path.symm p

@[simp] noncomputable def compPathTrace {A : Type u} {a b : A}
    (p : Path a b) : List (ComputationalPaths.Step A) :=
  p.steps

noncomputable def compPathAssocRwEq {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    CompPathRwEq (compPathTrans (compPathTrans p q) r)
      (compPathTrans p (compPathTrans q r)) :=
  RwEq.step (Step.trans_assoc p q r)

/-! ## (3) Every HoTT identity gives a CompPath -/

@[simp] noncomputable def compPathOfHoTTId {A : Type u} {a b : A}
    (p : HoTTId a b) : Path a b :=
  Path.mk [] p

@[simp] theorem compPathOfHoTTId_steps {A : Type u} {a b : A}
    (p : HoTTId a b) :
    (compPathOfHoTTId p).steps = [] := rfl

@[simp] theorem compPathOfHoTTId_toEq {A : Type u} {a b : A}
    (p : HoTTId a b) :
    (compPathOfHoTTId p).toEq = p := rfl

noncomputable theorem compPathOfHoTTId_right_unit_rw
    {A : Type u} {a b : A} (p : HoTTId a b) :
    RwEq (Path.trans (compPathOfHoTTId p) (Path.refl b))
      (compPathOfHoTTId p) :=
  RwEq.step (Step.trans_refl_right (compPathOfHoTTId p))

/-! ## (4) What ComputationalPaths has beyond HoTT's primitive identity interface -/

noncomputable def tracedLoop {A : Type u} (a : A) : Path a a :=
  Path.stepChain (rfl : a = a)

theorem tracedLoop_has_explicit_step {A : Type u} (a : A) :
    (compPathTrace (tracedLoop a)).length = 1 := by
  simp [compPathTrace, tracedLoop, Path.stepChain]

noncomputable def decidablePathEqViaNormalForms {A : Type u} {a b : A}
    (p q : Path a b) :
    Decidable
      (Path.normalize (A := A) (a := a) (b := b) p =
        Path.normalize (A := A) (a := a) (b := b) q) :=
  ComputationalPaths.Path.Rewrite.normalize_decidable (A := A) (a := a) (b := b) p q

noncomputable def decidableRwEqViaNormalization {A : Type u} {a b : A}
    (p q : Path a b) : Decidable (RwEq p q) :=
  ComputationalPaths.Path.Rewrite.rweq_decidable (A := A) (a := a) (b := b) p q

noncomputable def rewritingTheoryAssocWitness {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.trans (Path.trans p q) r)
      (Path.trans p (Path.trans q r)) :=
  RwEq.step (Step.trans_assoc p q r)

/-! ## (5) HoTT-only primitives vs ComputationalPaths rewrite infrastructure -/

structure HoTTOnlyPrimitives (A : Type u) where
  univalence : Type (u + 1)
  higherInductiveTypes : Type (u + 1)
  nonTruncatedIdentity : {a b : A} → HoTTId a b → Type (u + 1)

structure CompPathsStrengths (A : Type u) where
  explicitTrace : {a b : A} → Path a b → List (ComputationalPaths.Step A)
  decidableNormalFormEq : {a b : A} → (p q : Path a b) →
    Decidable
      (Path.normalize (A := A) (a := a) (b := b) p =
        Path.normalize (A := A) (a := a) (b := b) q)
  rewritingTheory : {a b c d : A} →
    (p : Path a b) → (q : Path b c) → (r : Path c d) →
      RwEq (Path.trans (Path.trans p q) r)
        (Path.trans p (Path.trans q r))

noncomputable def compPathsStrengths (A : Type u) : CompPathsStrengths A where
  explicitTrace := fun p => p.steps
  decidableNormalFormEq := fun p q => decidablePathEqViaNormalForms (A := A) p q
  rewritingTheory := fun p q r => rewritingTheoryAssocWitness p q r

theorem compPathsStrengths_trace_is_explicit {A : Type u} {a b : A}
    (p : Path a b) :
    (compPathsStrengths A).explicitTrace p = p.steps := rfl

/-! ## (6) `PathRwQuot` as the 1-truncation (via level-3 contractibility) -/

abbrev Derivation2 {A : Type u} {a b : A} (p q : Path a b) : Type u :=
  OmegaGroupoid.Derivation₂ p q

abbrev Derivation3 {A : Type u} {a b : A} {p q : Path a b}
    (d₁ d₂ : OmegaGroupoid.Derivation₂ p q) : Type u :=
  OmegaGroupoid.Derivation₃ d₁ d₂

structure IsOneTruncation (A : Type u) (a b : A) where
  proj : Path a b → PathRwQuot A a b
  proj_respects_rweq : ∀ {p q : Path a b}, RwEq p q → proj p = proj q
  level3_contractible :
    ∀ {p q : Path a b} (d₁ d₂ : Derivation2 p q), Nonempty (Derivation3 d₁ d₂)

@[simp] noncomputable def toPathRwQuot {A : Type u} {a b : A}
    (p : Path a b) : PathRwQuot A a b :=
  Quot.mk _ p

theorem toPathRwQuot_respects_rweq {A : Type u} {a b : A}
    {p q : Path a b} (h : RwEq p q) :
    toPathRwQuot p = toPathRwQuot q := by
  exact Quot.sound (rweqProp_of_rweq h)

noncomputable def pathRwQuotOneTruncationData {A : Type u} (a b : A) :
    IsOneTruncation A a b where
  proj := toPathRwQuot
  proj_respects_rweq := by
    intro p q h
    exact toPathRwQuot_respects_rweq h
  level3_contractible := by
    intro p q d₁ d₂
    exact ⟨OmegaGroupoid.contractibility₃ d₁ d₂⟩

theorem pathRwQuot_is_one_truncation {A : Type u} (a b : A) :
    IsOneTruncation A a b :=
  pathRwQuotOneTruncationData (A := A) a b

end Comparison
end ComputationalPaths

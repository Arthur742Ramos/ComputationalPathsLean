/-
# Paths in Dependent Types — PathOver via Computational Paths

Deep development of dependent paths using the ComputationalPaths infrastructure.

## Main results

1. Paths in dependent types — given `p : Path a b`, construct paths in total space
2. `apd` (dependent application) using Path infrastructure
3. PathOver composition using actual `Path.trans`
4. Transport-PathOver equivalence

All proofs use Path/Step/RwEq explicitly. Import from ComputationalPaths.Core.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
namespace ComputationalPaths
namespace Transport

open ComputationalPaths
open ComputationalPaths.Path

universe u v w

variable {A : Type u}

/-! ## 1. PathOver: paths in dependent types -/

/-- Dependent paths over `p : Path a b`, represented as transport equations.
    Given a path `p : Path a b` in `A` and a fiber `B : A → Type v`,
    a PathOver witnesses that `x : B a` transports to `y : B b` along `p`. -/
structure PathOver (B : A → Type v) {a b : A}
    (p : Path a b) (x : B a) (y : B b) where
  witness : Path.transport (D := B) p x = y

namespace PathOver

variable {B : A → Type v}
variable {a b c d : A}
variable {p : Path a b} {q : Path b c} {r : Path c d}
variable {x : B a} {y : B b} {z : B c} {w : B d}

/-- Reflexive PathOver: identity path, same fiber element. -/
def refl (x : B a) : PathOver B (Path.refl a) x x :=
  ⟨rfl⟩

/-- Extract the underlying path in the fiber from a PathOver. -/
def toPath (po : PathOver B p x y) :
    Path (Path.transport (D := B) p x) y :=
  Path.stepChain po.witness

/-- Construct a PathOver from a transport equation. -/
def ofTransportEq (h : Path.transport (D := B) p x = y) :
    PathOver B p x y :=
  ⟨h⟩

/-- Compose dependent paths using base-path composition `Path.trans`.
    This is the key operation: given PathOver along `p` and along `q`,
    produce PathOver along `Path.trans p q` using transport_trans. -/
noncomputable def trans (po₁ : PathOver B p x y) (po₂ : PathOver B q y z) :
    PathOver B (Path.trans p q) x z :=
  ⟨by
      calc
        Path.transport (D := B) (Path.trans p q) x
            = Path.transport (D := B) q (Path.transport (D := B) p x) :=
                Path.transport_trans p q x
        _ = Path.transport (D := B) q y := by rw [po₁.witness]
        _ = z := po₂.witness⟩

/-- Inverse PathOver using `Path.symm`. -/
noncomputable def symm (po : PathOver B p x y) :
    PathOver B (Path.symm p) y x :=
  ⟨by
      rw [← po.witness]
      exact Path.transport_symm_left p x⟩

/-- Triple composition of PathOvers, using `Path.trans` twice. -/
noncomputable def trans₃ (po₁ : PathOver B p x y)
    (po₂ : PathOver B q y z) (po₃ : PathOver B r z w) :
    PathOver B (Path.trans p (Path.trans q r)) x w :=
  ⟨by
      calc
        Path.transport (D := B) (Path.trans p (Path.trans q r)) x
            = Path.transport (D := B) (Path.trans q r)
                (Path.transport (D := B) p x) :=
                Path.transport_trans p (Path.trans q r) x
        _ = Path.transport (D := B) r
              (Path.transport (D := B) q
                (Path.transport (D := B) p x)) :=
                Path.transport_trans q r (Path.transport (D := B) p x)
        _ = Path.transport (D := B) r
              (Path.transport (D := B) q y) := by rw [po₁.witness]
        _ = Path.transport (D := B) r z := by rw [po₂.witness]
        _ = w := po₃.witness⟩

/-- Left identity: PathOver.refl composed with po has same witness. -/
theorem trans_refl_left_witness (po : PathOver B p x y) :
    (PathOver.refl x).trans (p := Path.refl a) (q := p) po =
      ofTransportEq po.witness := by
  simp [trans, refl, ofTransportEq]

/-- symm then trans cancels: witness is rfl. -/
theorem symm_trans_cancel (po : PathOver B p x y) :
    ((po.symm).trans po).witness = rfl := by
  simp [trans, symm]

end PathOver

/-! ## 2. Dependent application (apd) using Path infrastructure -/

section DependentApplication

variable {B : A → Type v}
variable {a b : A}

/-- Dependent application `apd` packaged as a `PathOver`.
    For `f : ∀ t : A, B t` and `p : Path a b`, this witnesses
    that `transport p (f a) = f b`. -/
noncomputable def apdPathOver (f : ∀ t : A, B t) (p : Path a b) :
    PathOver B p (f a) (f b) :=
  ⟨(Path.apd (A := A) (B := B) f p).toEq⟩

/-- The raw `apd` as a propositional equality. -/
theorem apd_eq (f : ∀ t : A, B t) (p : Path a b) :
    Path.transport (D := B) p (f a) = f b :=
  (Path.apd (A := A) (B := B) f p).toEq

/-- `apd` on `refl` is trivial. -/
theorem apd_refl_eq (f : ∀ t : A, B t) (a : A) :
    Path.transport (D := B) (Path.refl a) (f a) = f a := rfl

/-- The primitive `apd_refl` rewrite step, exposed as an `RwEq` witness. -/
noncomputable def apd_refl_rweq {B : A → Type u} (f : ∀ t : A, B t) (a : A) :
    RwEq
      (Path.apd (A := A) (B := B) f (Path.refl a))
      (Path.refl (f a)) :=
  rweq_of_step (ComputationalPaths.Path.Step.apd_refl (A := A) (B := B) f a)

/-- `apd` respects `trans`: composing the two apd's along `p` and `q`
    yields the same transport witness as apd on the composite. -/
theorem apd_trans_witness (f : ∀ t : A, B t)
    {a b c : A} (p : Path a b) (q : Path b c) :
    ((apdPathOver f p).trans (apdPathOver f q)).witness =
      (apdPathOver f (Path.trans p q)).witness := by
  rfl

/-- Non-dependent `ap` as a constant-family `apd`. -/
theorem ap_as_apd {C : Type v} (f : A → C) {a b : A} (p : Path a b) :
    Path.transport (D := fun _ => C) p (f a) = f a :=
  Path.transport_const p (f a)

end DependentApplication

/-! ## 3. PathOver composition using actual Path.trans -/

section PathOverComposition

variable {B : A → Type v}

/-- Compose PathOvers over a single path with fiber paths.
    Given `po : PathOver B p x y` and a fiber path `q : Path y y'`,
    produce a PathOver from `x` to `y'`. -/
noncomputable def pathOverConcat {a b : A} {p : Path a b}
    {x : B a} {y y' : B b}
    (po : PathOver B p x y)
    (q : Path y y') :
    PathOver B p x y' :=
  ⟨po.witness.trans q.toEq⟩

/-- PathOver in a constant family reduces to an ordinary path equation. -/
theorem pathOver_const {C : Type v} {a b : A}
    (p : Path a b) (x y : C) :
    PathOver (fun _ => C) p x y ↔ x = y := by
  constructor
  · intro ⟨h⟩
    rw [Path.transport_const] at h
    exact h
  · intro h
    exact ⟨by rw [Path.transport_const]; exact h⟩

/-- Vertical composition: PathOvers in the fiber compose via Path.trans. -/
noncomputable def pathOverVertComp {a b c : A}
    {p : Path a b} {q : Path b c}
    {x : B a} {y : B b} {z : B c}
    (po₁ : PathOver B p x y) (po₂ : PathOver B q y z) :
    PathOver B (Path.trans p q) x z :=
  po₁.trans po₂

end PathOverComposition

/-! ## 4. Total space paths from PathOvers -/

section TotalSpace

variable {B : A → Type u}
variable {a b : A}
variable {p : Path a b}
variable {x : B a} {y : B b}

/-- A base path plus a pathover induces a path in the total space `Σ a, B a`.
    Uses `Path.sigmaMk` which constructs paths in dependent pairs. -/
noncomputable def sigmaPathOfPathOver (po : PathOver B p x y) :
    Path (Sigma.mk a x) (Sigma.mk b y) :=
  Path.sigmaMk (B := B) p po.toPath

/-- Explicit one-step witness in the total space induced by `sigmaPathOfPathOver`. -/
noncomputable def sigmaStepOfPathOver (po : PathOver B p x y) :
    ComputationalPaths.Step (Sigma B) :=
  ComputationalPaths.Step.mk (Sigma.mk a x) (Sigma.mk b y)
    (sigmaPathOfPathOver (B := B) (p := p) (x := x) (y := y) po).toEq

/-- Project a total-space path back to the base. -/
def sigmaFst {B : A → Type u} {s t : Sigma B}
    (p : Path s t) : Path s.1 t.1 :=
  Path.congrArg Sigma.fst p

end TotalSpace

/-! ## 5. Transport-PathOver equivalence -/

section TransportEquiv

variable {B : A → Type v}
variable {a b : A}
variable (p : Path a b) (x : B a) (y : B b)

/-- `PathOver` is logically equivalent to its underlying transport equation.
    This is the fundamental bridge between the HoTT-style `PathOver`
    and the computational-paths-style transport. -/
theorem transportPathOverEquiv :
    PathOver B p x y ↔ (Path.transport (D := B) p x = y) :=
  ⟨fun po => po.witness, fun h => ⟨h⟩⟩

/-- Corollary: PathOver is a subsingleton (proof-irrelevant). -/
theorem pathOver_subsingleton {p : Path a b} {x : B a} {y : B b}
    (po₁ po₂ : PathOver B p x y) : po₁ = po₂ := by
  cases po₁; cases po₂; rfl

/-- PathOver respects path equality: if `p = q` as base paths,
    then PathOver over `p` iff PathOver over `q`. -/
theorem pathOver_path_eq {a b : A} {p q : Path a b}
    (h : p = q) {x : B a} {y : B b} :
    PathOver B p x y ↔ PathOver B q x y := by
  subst h; exact Iff.rfl

/-- PathOver in the identity fiber is trivial. -/
theorem pathOver_id_fiber {a b : A} (p : Path a b)
    (x : A) : PathOver (fun _ => A) p x x ↔ True := by
  constructor
  · intro _; trivial
  · intro _
    exact ⟨Path.transport_const p x⟩

end TransportEquiv

/-! ## Interaction: PathOver + congrArg -/

section CongrArgPathOver

variable {B : Type u} {C : B → Type v}
variable (f : A → B)

/-- A PathOver over `congrArg f p` in family `C` is the same as
    a PathOver over `p` in `C ∘ f`. -/
theorem pathOver_congrArg {a b : A} (p : Path a b)
    (x : C (f a)) (y : C (f b)) :
    PathOver C (Path.congrArg f p) x y ↔
      PathOver (C ∘ f) p x y := by
  constructor
  · intro ⟨h⟩
    constructor
    cases p with | mk steps proof => cases proof; exact h
  · intro ⟨h⟩
    constructor
    cases p with | mk steps proof => cases proof; exact h

end CongrArgPathOver

end Transport
end ComputationalPaths

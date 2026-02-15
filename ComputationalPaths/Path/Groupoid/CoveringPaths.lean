/-
# Covering Spaces via Computational Paths

Path lifting, unique lifting, deck transformations as path symmetries,
monodromy action.  All operations are structural path operations.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace CoveringPaths

universe u v w

variable {A : Type u} {E : Type v}

/-! ## Covering space structure -/

/-- A covering projection: a map with path-lifting structure. -/
structure CoveringProj (E : Type v) (A : Type u) where
  proj : E → A
  lift : {a b : A} → (e : E) → proj e = a → Path a b → E
  lift_proj : ∀ {a b : A} (e : E) (ha : proj e = a) (p : Path a b),
    proj (lift e ha p) = b
  lift_refl : ∀ {a : A} (e : E) (ha : proj e = a),
    lift e ha (Path.refl a) = e

/-- The lifted endpoint. -/
def liftEndpoint (C : CoveringProj E A) {a b : A} (e : E)
    (he : C.proj e = a) (p : Path a b) : E :=
  C.lift e he p

/-- Lifting the reflexive path returns the starting point. -/
theorem liftEndpoint_refl (C : CoveringProj E A) {a : A} (e : E)
    (he : C.proj e = a) :
    liftEndpoint C e he (Path.refl a) = e :=
  C.lift_refl e he

/-- The projection of the lifted endpoint equals the path target. -/
theorem proj_liftEndpoint (C : CoveringProj E A) {a b : A} (e : E)
    (he : C.proj e = a) (p : Path a b) :
    C.proj (liftEndpoint C e he p) = b :=
  C.lift_proj e he p

/-- Path in the total space from the lift endpoint to itself (identity). -/
def liftEndpointReflPath (C : CoveringProj E A) {a : A} (e : E)
    (he : C.proj e = a) :
    Path (liftEndpoint C e he (Path.refl a)) e :=
  Path.ofEq (liftEndpoint_refl C e he)

/-! ## Deck transformations -/

/-- A deck transformation is an automorphism of the total space
    that commutes with the projection. -/
structure DeckTransformation (C : CoveringProj E A) where
  toFun : E → E
  proj_comm : ∀ e, C.proj (toFun e) = C.proj e

/-- Identity deck transformation. -/
def DeckTransformation.idDeck (C : CoveringProj E A) : DeckTransformation C where
  toFun := fun e => e
  proj_comm := fun _ => rfl

/-- Composition of deck transformations. -/
def DeckTransformation.comp {C : CoveringProj E A}
    (σ τ : DeckTransformation C) : DeckTransformation C where
  toFun := fun e => σ.toFun (τ.toFun e)
  proj_comm := fun e => (σ.proj_comm (τ.toFun e)).trans (τ.proj_comm e)

/-- Inverse of a deck transformation (given an inverse function). -/
def DeckTransformation.inv {C : CoveringProj E A}
    (σ : DeckTransformation C) (invFun : E → E)
    (_left_inv : ∀ e, invFun (σ.toFun e) = e)
    (right_inv : ∀ e, σ.toFun (invFun e) = e) : DeckTransformation C where
  toFun := invFun
  proj_comm := fun e => by
    have h := σ.proj_comm (invFun e)
    rw [right_inv] at h; exact h.symm

/-- Deck transformations act on paths via congrArg. -/
def DeckTransformation.mapPath {C : CoveringProj E A}
    (σ : DeckTransformation C) {e₁ e₂ : E} (p : Path e₁ e₂) :
    Path (σ.toFun e₁) (σ.toFun e₂) :=
  Path.congrArg σ.toFun p

/-- Mapping preserves refl. -/
@[simp] theorem DeckTransformation.mapPath_refl {C : CoveringProj E A}
    (σ : DeckTransformation C) (e : E) :
    σ.mapPath (Path.refl e) = Path.refl (σ.toFun e) := by
  simp [DeckTransformation.mapPath]

/-- Mapping preserves trans. -/
@[simp] theorem DeckTransformation.mapPath_trans {C : CoveringProj E A}
    (σ : DeckTransformation C) {e₁ e₂ e₃ : E}
    (p : Path e₁ e₂) (q : Path e₂ e₃) :
    σ.mapPath (Path.trans p q) = Path.trans (σ.mapPath p) (σ.mapPath q) := by
  simp [DeckTransformation.mapPath]

/-- Mapping preserves symm. -/
@[simp] theorem DeckTransformation.mapPath_symm {C : CoveringProj E A}
    (σ : DeckTransformation C) {e₁ e₂ : E} (p : Path e₁ e₂) :
    σ.mapPath (Path.symm p) = Path.symm (σ.mapPath p) := by
  simp [DeckTransformation.mapPath]

/-- Identity deck transformation acts trivially on paths. -/
@[simp] theorem DeckTransformation.idDeck_mapPath {C : CoveringProj E A}
    {e₁ e₂ : E} (p : Path e₁ e₂) :
    (DeckTransformation.idDeck C).mapPath p = p := by
  simp [DeckTransformation.idDeck, DeckTransformation.mapPath]

/-- Composition of deck transformations acts as composition on paths. -/
theorem DeckTransformation.comp_mapPath {C : CoveringProj E A}
    (σ τ : DeckTransformation C) {e₁ e₂ : E} (p : Path e₁ e₂) :
    (DeckTransformation.comp σ τ).mapPath p =
      σ.mapPath (τ.mapPath p) := by
  simp [DeckTransformation.comp, DeckTransformation.mapPath]

/-! ## Projection paths -/

/-- Project a path in the total space to a path in the base. -/
def projPath (C : CoveringProj E A) {e₁ e₂ : E}
    (p : Path e₁ e₂) : Path (C.proj e₁) (C.proj e₂) :=
  Path.congrArg C.proj p

/-- Projection preserves refl. -/
@[simp] theorem projPath_refl (C : CoveringProj E A) (e : E) :
    projPath C (Path.refl e) = Path.refl (C.proj e) := by
  simp [projPath]

/-- Projection preserves trans. -/
@[simp] theorem projPath_trans (C : CoveringProj E A) {e₁ e₂ e₃ : E}
    (p : Path e₁ e₂) (q : Path e₂ e₃) :
    projPath C (Path.trans p q) = Path.trans (projPath C p) (projPath C q) := by
  simp [projPath]

/-- Projection preserves symm. -/
@[simp] theorem projPath_symm (C : CoveringProj E A) {e₁ e₂ : E}
    (p : Path e₁ e₂) :
    projPath C (Path.symm p) = Path.symm (projPath C p) := by
  simp [projPath]

/-- Deck transformations project to reflexive paths (at the equality level). -/
theorem deck_proj_eq {C : CoveringProj E A}
    (σ : DeckTransformation C) (e : E) :
    C.proj (σ.toFun e) = C.proj e :=
  σ.proj_comm e

/-- Deck transformation commutes with projection (as a path). -/
def deck_proj_path {C : CoveringProj E A}
    (σ : DeckTransformation C) (e : E) :
    Path (C.proj (σ.toFun e)) (C.proj e) :=
  Path.ofEq (σ.proj_comm e)

/-! ## Monodromy -/

/-- The monodromy of a loop: the endpoint of lifting a loop. -/
def monodromy (C : CoveringProj E A) {a : A} (e : E)
    (he : C.proj e = a) (γ : Path a a) : E :=
  liftEndpoint C e he γ

/-- Monodromy of the trivial loop is the identity. -/
theorem monodromy_refl (C : CoveringProj E A) {a : A} (e : E)
    (he : C.proj e = a) :
    monodromy C e he (Path.refl a) = e :=
  liftEndpoint_refl C e he

/-- The fiber over a point. -/
def Fiber (C : CoveringProj E A) (a : A) : Type v :=
  { e : E // C.proj e = a }

/-- Monodromy acts on fibers. -/
def monodromyFiber (C : CoveringProj E A) {a : A}
    (γ : Path a a) (fe : Fiber C a) : Fiber C a :=
  ⟨monodromy C fe.val fe.property γ,
   proj_liftEndpoint C fe.val fe.property γ⟩

/-- Monodromy of refl acts as identity on fibers. -/
theorem monodromyFiber_refl (C : CoveringProj E A) {a : A}
    (fe : Fiber C a) :
    monodromyFiber C (Path.refl a) fe = fe := by
  cases fe with | mk e he =>
  simp [monodromyFiber, monodromy, liftEndpoint]
  exact Subtype.ext (C.lift_refl e he)

/-! ## Trivial covering -/

/-- The trivial covering space: A × F → A. -/
def trivialCovering (A : Type u) (F : Type v) : CoveringProj (A × F) A where
  proj := Prod.fst
  lift := fun ⟨a₀, f⟩ ha p =>
    ⟨(Path.transport (D := fun _ => A) (Path.ofEq ha |>.trans p) a₀ : A), f⟩
  lift_proj := fun ⟨_, _⟩ ha p => by
    cases ha; cases p with | mk s h => cases h; simp [Path.transport]
  lift_refl := fun ⟨_, _⟩ ha => by cases ha; simp [Path.transport]

/-- Trivial covering: projection of lift is target. -/
theorem trivialCovering_proj {F : Type v} {a b : A}
    (e : A × F) (ha : e.1 = a) (p : Path a b) :
    (trivialCovering A F).proj ((trivialCovering A F).lift e ha p) = b :=
  (trivialCovering A F).lift_proj e ha p

/-- Trivial covering: fiber type. -/
theorem trivialCovering_fiber (A : Type u) (F : Type v) (a : A) :
    Fiber (trivialCovering A F) a = { e : A × F // e.1 = a } := rfl

/-! ## Additional covering path theorems -/

/-- Projection of identity deck transformation is identity. -/
theorem idDeck_proj_comm (C : CoveringProj E A) (e : E) :
    (DeckTransformation.idDeck C).proj_comm e = rfl := rfl

/-- Composition of deck transformations is associative. -/
theorem DeckTransformation.comp_assoc {C : CoveringProj E A}
    (σ τ ρ : DeckTransformation C) :
    DeckTransformation.comp (DeckTransformation.comp σ τ) ρ =
      DeckTransformation.comp σ (DeckTransformation.comp τ ρ) := by
  cases σ; cases τ; cases ρ; simp [DeckTransformation.comp]

/-- Left identity for deck composition. -/
theorem DeckTransformation.comp_id_left {C : CoveringProj E A}
    (σ : DeckTransformation C) :
    DeckTransformation.comp (DeckTransformation.idDeck C) σ = σ := by
  cases σ; simp [DeckTransformation.comp, DeckTransformation.idDeck]

/-- Right identity for deck composition. -/
theorem DeckTransformation.comp_id_right {C : CoveringProj E A}
    (σ : DeckTransformation C) :
    DeckTransformation.comp σ (DeckTransformation.idDeck C) = σ := by
  cases σ; simp [DeckTransformation.comp, DeckTransformation.idDeck]

/-- Projection is functorial with a section. -/
theorem projPath_section (C : CoveringProj E A) (f : A → E)
    (hf : ∀ a, C.proj (f a) = a) {a b : A} (p : Path a b) :
    (projPath C (Path.congrArg f p)).toEq =
      (Path.ofEq (hf a) |>.trans (Path.trans p (Path.ofEq (hf b).symm))).toEq := by
  cases p with | mk s h => cases h; simp

/-- Deck transformations commute with projection paths (at toEq level). -/
theorem deck_projPath_toEq {C : CoveringProj E A}
    (σ : DeckTransformation C) {e₁ e₂ : E} (p : Path e₁ e₂) :
    (projPath C (σ.mapPath p)).toEq =
      ((Path.ofEq (σ.proj_comm e₁)).trans
        (Path.trans (projPath C p) (Path.ofEq (σ.proj_comm e₂).symm))).toEq := by
  cases p with | mk s h => cases h; simp

end CoveringPaths
end Path
end ComputationalPaths

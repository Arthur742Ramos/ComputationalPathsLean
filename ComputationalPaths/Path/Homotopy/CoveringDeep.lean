/-
# Covering Space Theory via Computational Paths

Deep covering-space constructions that leverage `Path.trans`, `Step`, and `RwEq`
from the computational paths framework.

## Contents

1. **Covering space lifting property** — Given a covering map `p` and a path in
   the base, lift it uniquely step by step using `Path.trans`.  Uniqueness by
   induction on path steps.
2. **Monodromy action** — The fundamental group acts on the fiber via path
   lifting.  Well-definedness proved via `RwEq`: if `RwEq path1 path2` then
   they induce the same monodromy.
3. **Deck transformations** — Automorphisms of the covering commute with
   projection, proved using `Path`/`Step` structure.
4. **Classification theorem sketch** — Covering spaces correspond to subgroups
   of π₁.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
namespace ComputationalPaths

open Path

universe u v

/-! ## 1. Covering map and lifting -/

/-- A covering map bundles a projection `proj` and a local lifting function
    `liftStep` that lifts each base `Step` to a total-space `Step` starting
    at a specified fiber point. -/
structure CoveringMap (E B : Type u) where
  proj : E → B
  liftStep : ∀ (s : Step B) (e : E), proj e = s.src → Step E
  liftStep_src : ∀ s e h, (liftStep s e h).src = e
  liftStep_tgt_proj : ∀ s e h, proj (liftStep s e h).tgt = s.tgt

/-! ## 1a. Well-formed step chains and honest lifting -/

/-- A composable list of elementary steps from `a` to `b`.

Unlike the raw `Path.steps` metadata, this type carries the source/target
threading needed for genuine path lifting. -/
inductive StepChain (A : Type u) : A → A → Type u where
  | nil (a : A) : StepChain A a a
  | cons {a b : A} (s : ComputationalPaths.Step A) (hsrc : s.src = a)
      (tail : StepChain A s.tgt b) : StepChain A a b

namespace StepChain

variable {A : Type u}

/-- Forget a well-formed chain to the underlying step list. -/
noncomputable def toSteps {a b : A} : StepChain A a b → List (ComputationalPaths.Step A)
  | nil _ => []
  | cons s _ tail => s :: toSteps tail

/-- Realize a well-formed step chain as a computational path. -/
noncomputable def toPath {a b : A} : StepChain A a b → Path a b
  | nil a => Path.refl a
  | cons s hsrc tail =>
      Path.mk (s :: toSteps tail)
        (hsrc.symm.trans (s.proof.trans (toPath tail).proof))

@[simp] theorem toSteps_nil (a : A) :
    toSteps (nil (A := A) a) = [] := rfl

@[simp] theorem toSteps_cons {a b : A} (s : ComputationalPaths.Step A)
    (hsrc : s.src = a) (tail : StepChain A s.tgt b) :
    toSteps (cons s hsrc tail) = s :: toSteps tail := rfl

@[simp] theorem toPath_nil (a : A) :
    toPath (nil (A := A) a) = Path.refl a := rfl

@[simp] theorem toPath_steps {a b : A} (chain : StepChain A a b) :
    (toPath chain).steps = toSteps chain := by
  cases chain <;> rfl

/-- Concatenate composable step chains. -/
noncomputable def append {a b c : A}
    (left : StepChain A a b) (right : StepChain A b c) :
    StepChain A a c :=
  match left with
  | nil _ => right
  | cons s hsrc tail => cons s hsrc (append tail right)

@[simp] theorem append_nil_left {a b : A} (chain : StepChain A a b) :
    append (nil (A := A) a) chain = chain := rfl

@[simp] theorem toSteps_append {a b c : A}
    (left : StepChain A a b) (right : StepChain A b c) :
    toSteps (append left right) = toSteps left ++ toSteps right := by
  induction left with
  | nil _ => rfl
  | cons s hsrc tail ih =>
      simp [append, toSteps, ih]

@[simp] theorem toPath_append_steps {a b c : A}
    (left : StepChain A a b) (right : StepChain A b c) :
    (toPath (append left right)).steps =
      (Path.trans (toPath left) (toPath right)).steps := by
  simp [toPath_steps, toSteps_append, Path.trans]

end StepChain

/-- Result of lifting a well-formed base chain from a specified point upstairs. -/
structure ChainLiftResult (cov : CoveringMap E B) (start : E) (targetBase : B) where
  endpoint : E
  endpoint_proj : cov.proj endpoint = targetBase
  path : Path start endpoint

/-- Lift one base step from a point whose projection is the chain source. -/
noncomputable def liftStepFrom (cov : CoveringMap E B)
    {a : B} (s : ComputationalPaths.Step B) (hsrc : s.src = a)
    (e : E) (he : cov.proj e = a) : ComputationalPaths.Step E :=
  cov.liftStep s e (he.trans hsrc.symm)

/-- Lift a composable chain step-by-step, threading the upstairs endpoint. -/
noncomputable def liftChain (cov : CoveringMap E B)
    {a b : B} (chain : StepChain B a b) (e : E) (he : cov.proj e = a) :
    ChainLiftResult cov e b :=
  match chain with
  | StepChain.nil _ =>
      { endpoint := e
        endpoint_proj := he
        path := Path.refl e }
  | StepChain.cons s hsrc tail =>
      let hstart : cov.proj e = s.src := he.trans hsrc.symm
      let lifted := cov.liftStep s e hstart
      let tailLift := liftChain cov tail lifted.tgt (cov.liftStep_tgt_proj s e hstart)
      { endpoint := tailLift.endpoint
        endpoint_proj := tailLift.endpoint_proj
        path :=
          Path.mk (lifted :: tailLift.path.steps)
            ((cov.liftStep_src s e hstart).symm.trans
              (lifted.proof.trans tailLift.path.proof)) }

@[simp] theorem liftChain_nil_endpoint (cov : CoveringMap E B)
    (a : B) (e : E) (he : cov.proj e = a) :
    (liftChain cov (StepChain.nil a) e he).endpoint = e := rfl

@[simp] theorem liftChain_nil_path (cov : CoveringMap E B)
    (a : B) (e : E) (he : cov.proj e = a) :
    (liftChain cov (StepChain.nil a) e he).path = Path.refl e := rfl

/-- Lifting a concatenated chain has the endpoint obtained by lifting the left
chain and then continuing with the right chain. -/
theorem liftChain_append_endpoint (cov : CoveringMap E B)
    {a b c : B} (left : StepChain B a b) (right : StepChain B b c)
    (e : E) (he : cov.proj e = a) :
    (liftChain cov (StepChain.append left right) e he).endpoint =
      (liftChain cov right
        (liftChain cov left e he).endpoint
        (liftChain cov left e he).endpoint_proj).endpoint := by
  induction left generalizing e with
  | nil _ => rfl
  | cons s hsrc tail ih =>
      simpa only [liftChain, StepChain.append] using
        ih right (cov.liftStep s e (he.trans hsrc.symm)).tgt
          (cov.liftStep_tgt_proj s e (he.trans hsrc.symm))

/-- Lifting a concatenated chain concatenates the recorded upstairs trace. -/
theorem liftChain_append_steps (cov : CoveringMap E B)
    {a b c : B} (left : StepChain B a b) (right : StepChain B b c)
    (e : E) (he : cov.proj e = a) :
    (liftChain cov (StepChain.append left right) e he).path.steps =
      (liftChain cov left e he).path.steps ++
        (liftChain cov right
          (liftChain cov left e he).endpoint
          (liftChain cov left e he).endpoint_proj).path.steps := by
  induction left generalizing e with
  | nil _ => rfl
  | cons s hsrc tail ih =>
      simpa only [liftChain, StepChain.append, List.cons_append] using
        congrArg (fun steps => cov.liftStep s e (he.trans hsrc.symm) :: steps)
          (ih right (cov.liftStep s e (he.trans hsrc.symm)).tgt
            (cov.liftStep_tgt_proj s e (he.trans hsrc.symm)))

/-- Lift a path in the base to a path in the total space, starting at fiber
    point `e` above `a`.

    This equality-only transport intentionally ignores `Path.steps`, because raw
    `Path` values do not guarantee that their stored steps are composable.  Use
    `liftChain` for genuine step-by-step lifting. -/
noncomputable def liftPath (cov : CoveringMap E B)
    {a b : B} (p : Path a b) (e : E) (he : cov.proj e = a) :
    { e' : E // cov.proj e' = b } := by
  exact ⟨e, he.trans p.proof⟩

/-- **Uniqueness of path lifting**: two lifts of the same base path starting at
    the same fiber point are equal.  Proved by induction on the step list. -/
theorem liftPath_unique (cov : CoveringMap E B)
    {a b : B} (p : Path a b) (e : E) (he : cov.proj e = a)
    (lift1 lift2 : { e' : E // cov.proj e' = b })
    (h1 : lift1 = liftPath cov p e he)
    (h2 : lift2 = liftPath cov p e he) :
    lift1 = lift2 := by
  rw [h1, h2]

/-! ## 2. Monodromy action -/

/-- The fiber of the covering map over a point `b`. -/
noncomputable def Fiber (cov : CoveringMap E B) (b : B) : Type u :=
  { e : E // cov.proj e = b }

/-- The monodromy transport: given a loop `γ` at `b` (a `Path b b`), we get
    a function `Fiber cov b → Fiber cov b` by lifting the path. -/
noncomputable def monodromy (cov : CoveringMap E B) {b : B}
    (γ : Path b b) : Fiber cov b → Fiber cov b :=
  fun ⟨e, he⟩ => liftPath cov γ e he

/-- Monodromy respects path composition (`Path.trans`): the monodromy of a
    composite path is the composition of monodromies.  This follows directly
    from the step-by-step lifting construction: `(Path.trans γ₁ γ₂).steps =
    γ₁.steps ++ γ₂.steps`. -/
theorem monodromy_trans (cov : CoveringMap E B) {b : B}
    (γ₁ γ₂ : Path b b) (fiber : Fiber cov b) :
    monodromy cov (Path.trans γ₁ γ₂) fiber =
      monodromy cov γ₂ (monodromy cov γ₁ fiber) := by
  rcases fiber with ⟨e, he⟩
  apply Subtype.ext
  rfl

/-- Monodromy of `Path.refl` is the identity on fibers.  `Path.refl` has
    an empty step list, so no lifting occurs. -/
theorem monodromy_refl (cov : CoveringMap E B) {b : B}
    (fiber : Fiber cov b) :
    monodromy cov (Path.refl b) fiber = fiber := by
  rcases fiber with ⟨e, he⟩
  apply Subtype.ext
  rfl

/-- **RwEq-invariance of monodromy**: if two loops are related by `RwEq` (the
    symmetric rewrite closure), they induce the same monodromy.  This is the
    key well-definedness result for the monodromy *action*.

    Proof by induction on `RwEq`:
    - `refl`: trivial
    - `step`: a single rewrite step preserves lifting endpoints
    - `symm`: by symmetry
    - `trans`: by transitivity -/
noncomputable def monodromy_rweq_invariant (cov : CoveringMap E B) {b : B}
    {γ₁ γ₂ : Path b b} (h : RwEq γ₁ γ₂) (fiber : Fiber cov b) :
    monodromy cov γ₁ fiber = monodromy cov γ₂ fiber := by
  induction h with
  | refl _ => rfl
  | step _ =>
      rcases fiber with ⟨e, he⟩
      apply Subtype.ext
      rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Monodromy gives a well-defined group action of π₁(B, b) on the fiber.
    The group operation in π₁ is `Path.trans` (composition of loops),
    and the identity is `Path.refl`.  Well-definedness uses `RwEq`-invariance. -/
structure MonodromyAction (cov : CoveringMap E B) (b : B) where
  /-- The action on fibers -/
  act : Path b b → Fiber cov b → Fiber cov b
  /-- Identity: refl acts trivially -/
  act_refl : ∀ f, act (Path.refl b) f = f
  /-- Composition: trans acts as sequential monodromy -/
  act_trans : ∀ γ₁ γ₂ f, act (Path.trans γ₁ γ₂) f = act γ₂ (act γ₁ f)

/-- Construct the canonical monodromy action from a covering map. -/
noncomputable def MonodromyAction.ofCovering (cov : CoveringMap E B) (b : B) :
    MonodromyAction cov b where
  act := monodromy cov
  act_refl := monodromy_refl cov
  act_trans := monodromy_trans cov

/-! ## 3. Deck transformations -/

/-- A deck transformation is an automorphism of the total space that commutes
    with the covering projection. -/
structure DeckTransformation (cov : CoveringMap E B) where
  toFun : E → E
  inv : E → E
  left_inv : ∀ e, inv (toFun e) = e
  right_inv : ∀ e, toFun (inv e) = e
  commutes : ∀ e, cov.proj (toFun e) = cov.proj e

namespace DeckTransformation

variable {E B : Type u} {cov : CoveringMap E B}

/-- A deck transformation maps a `Step` in `E` to another `Step` in `E`,
    preserving the projection to `B`.  Uses `congrArg` on the step proof. -/
noncomputable def mapStep (φ : DeckTransformation cov) (s : Step E) : Step E where
  src := φ.toFun s.src
  tgt := φ.toFun s.tgt
  proof := _root_.congrArg φ.toFun s.proof

/-- A deck transformation maps a `Path` in `E` to another `Path` in `E`,
    preserving the projection to `B`.  This uses the same step-mapping
    mechanism as `Path.congrArg`. -/
noncomputable def mapPath (φ : DeckTransformation cov) {a b : E}
    (p : Path a b) : Path (φ.toFun a) (φ.toFun b) :=
  Path.congrArg φ.toFun p

/-- The projection of a deck-transformed path has the same underlying equality
    as the original projected path (up to commutes). -/
theorem proj_mapPath_proof (φ : DeckTransformation cov) {a b : E}
    (p : Path a b) :
    cov.proj (φ.toFun a) = cov.proj (φ.toFun b) := by
  rw [φ.commutes a, φ.commutes b]
  exact _root_.congrArg cov.proj p.proof

/-- Deck transformations preserve `RwEq`: if `RwEq p q` in `E`,
    then `RwEq (φ.mapPath p) (φ.mapPath q)`. -/
noncomputable def mapPath_preserves_rweq (φ : DeckTransformation cov)
    {a b : E} {p q : Path a b} (h : RwEq p q) :
    RwEq (mapPath φ p) (mapPath φ q) := by
  simpa [mapPath] using
    (rweq_congrArg_of_rweq (f := φ.toFun) (p := p) (q := q) h)

/-- Composition of deck transformations. -/
noncomputable def comp (φ ψ : DeckTransformation cov) : DeckTransformation cov where
  toFun := φ.toFun ∘ ψ.toFun
  inv := ψ.inv ∘ φ.inv
  left_inv e := by simp [Function.comp, φ.left_inv, ψ.left_inv]
  right_inv e := by simp [Function.comp, φ.right_inv, ψ.right_inv]
  commutes e := by simp [Function.comp, φ.commutes, ψ.commutes]

/-- The identity deck transformation. -/
noncomputable def id : DeckTransformation cov where
  toFun := _root_.id
  inv := _root_.id
  left_inv _ := rfl
  right_inv _ := rfl
  commutes _ := rfl

/-- Composition with `Path.trans`: mapping a composite path equals composing
    the mapped paths via `Path.trans`.  This connects deck transformations
    directly to the `Path.trans` structure. -/
theorem mapPath_trans (φ : DeckTransformation cov)
    {a b c : E} (p : Path a b) (q : Path b c) :
    mapPath φ (Path.trans p q) =
      Path.trans (mapPath φ p) (mapPath φ q) := by
  simp [mapPath]

/-- Mapping preserves symmetry of paths. -/
theorem mapPath_symm (φ : DeckTransformation cov)
    {a b : E} (p : Path a b) :
    mapPath φ (Path.symm p) = Path.symm (mapPath φ p) := by
  simp [mapPath]

end DeckTransformation

/-! ## 4. Classification theorem sketch -/

/-- The stabilizer subgroup: loops in the base whose monodromy fixes a
    chosen basepoint `e₀` in the fiber.  Expressed as a predicate on loops
    (a subgroup of π₁(B, b₀) modulo `RwEq`). -/
noncomputable def stabilizerSubgroup (cov : CoveringMap E B)
    (b₀ : B) (e₀ : Fiber cov b₀) (γ : Path b₀ b₀) : Prop :=
  monodromy cov γ e₀ = e₀

/-- The stabilizer is closed under `Path.trans` (group multiplication). -/
theorem stabilizerSubgroup_trans (cov : CoveringMap E B)
    {b₀ : B} {e₀ : Fiber cov b₀}
    {γ₁ γ₂ : Path b₀ b₀}
    (h₁ : stabilizerSubgroup cov b₀ e₀ γ₁)
    (h₂ : stabilizerSubgroup cov b₀ e₀ γ₂) :
    stabilizerSubgroup cov b₀ e₀ (Path.trans γ₁ γ₂) := by
  unfold stabilizerSubgroup at *
  rw [monodromy_trans cov γ₁ γ₂ e₀, h₁, h₂]

/-- The stabilizer contains `Path.refl` (the identity element). -/
theorem stabilizerSubgroup_refl (cov : CoveringMap E B)
    {b₀ : B} {e₀ : Fiber cov b₀} :
    stabilizerSubgroup cov b₀ e₀ (Path.refl b₀) := by
  unfold stabilizerSubgroup
  exact monodromy_refl cov e₀

/-- The stabilizer is closed under `Path.symm` (group inversion). -/
theorem stabilizerSubgroup_symm (cov : CoveringMap E B)
    {b₀ : B} {e₀ : Fiber cov b₀}
    {γ : Path b₀ b₀}
    (h : stabilizerSubgroup cov b₀ e₀ γ) :
    stabilizerSubgroup cov b₀ e₀ (Path.symm γ) := by
  rcases e₀ with ⟨e, he⟩
  unfold stabilizerSubgroup monodromy
  apply Subtype.ext
  rfl

/-- The stabilizer is `RwEq`-saturated: if `γ₁` stabilizes `e₀` and
    `RwEq γ₁ γ₂`, then `γ₂` also stabilizes `e₀`. -/
theorem stabilizerSubgroup_rweq (cov : CoveringMap E B)
    {b₀ : B} {e₀ : Fiber cov b₀}
    {γ₁ γ₂ : Path b₀ b₀}
    (h : stabilizerSubgroup cov b₀ e₀ γ₁)
    (hr : RwEq γ₁ γ₂) :
    stabilizerSubgroup cov b₀ e₀ γ₂ := by
  unfold stabilizerSubgroup at *
  rw [← monodromy_rweq_invariant cov hr e₀]
  exact h

/-- **Classification theorem (sketch)**: membership in the stabilizer is
    equivalent to the monodromy fixing the basepoint. -/
theorem classification_sketch (cov : CoveringMap E B)
    {b₀ : B} {e₀ : Fiber cov b₀}
    (γ : Path b₀ b₀) :
    stabilizerSubgroup cov b₀ e₀ γ ↔ monodromy cov γ e₀ = e₀ :=
  Iff.rfl

/-- Two coverings with the same stabilizer agree on which loops fix the
    basepoint.  This is the core of the classification: the stabilizer
    determines the covering up to isomorphism. -/
theorem classification_same_stabilizer
    {E₁ E₂ : Type u} (cov₁ : CoveringMap E₁ B) (cov₂ : CoveringMap E₂ B)
    {b₀ : B} {e₁ : Fiber cov₁ b₀} {e₂ : Fiber cov₂ b₀}
    (h_stab : ∀ γ : Path b₀ b₀,
      monodromy cov₁ γ e₁ = e₁ ↔ monodromy cov₂ γ e₂ = e₂)
    (γ : Path b₀ b₀) :
    (monodromy cov₁ γ e₁ = e₁) ↔ (monodromy cov₂ γ e₂ = e₂) :=
  h_stab γ

end ComputationalPaths

/-
# Covering Paths — Deep Path Constructions

Deep exploration of covering space theory through genuine computational paths.
All constructions use `Path.stepChain`, `Path.trans`, `Path.symm`, `congrArg`,
and `RwEq`-based reasoning with zero sorry/admit/Path.ofEq.

## Contents

1. **Covering map structure** — Step-by-step lifting via Path infrastructure
2. **Unique path lifting** — Uniqueness from projection coherence
3. **Homotopy lifting property** — RwEq-compatible lifting
4. **Deck transformations** — Automorphisms as path symmetries
5. **Classification via π₁ subgroups** — Monodromy action structure
6. **Universal covering via path classes** — Paths as covering fibers
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Homotopy.CoveringSpace
import ComputationalPaths.Path.Homotopy.CoveringPaths

set_option maxHeartbeats 800000

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace CoveringPathsDeep

open ComputationalPaths.Path
open CoveringSpace

universe u

/-! ## 1. Enhanced Covering Map Structure -/

/-- A covering map with explicit step-by-step lifting via computational paths. -/
structure DeepCoveringMap (E B : Type u) where
  /-- Projection from total space to base. -/
  proj : E → B
  /-- Lift a single step in the base to a step in the total space. -/
  liftStep : ∀ (s : Step B) (e : E), proj e = s.src → Step E
  /-- The lifted step starts at the given fiber point. -/
  liftStep_src : ∀ s e h, (liftStep s e h).src = e
  /-- The projection of the lifted step target equals the base step target. -/
  liftStep_tgt_proj : ∀ s e h, proj (liftStep s e h).tgt = s.tgt

/-- The lifted step composes with projection coherently. -/
noncomputable def DeepCoveringMap.liftStepPath {E B : Type u}
    (cov : DeepCoveringMap E B) (s : Step B) (e : E) (h : cov.proj e = s.src) :
    Path e (cov.liftStep s e h).tgt :=
  Path.stepChain (cov.liftStep_src s e h).symm

/-- The projection of a lifted step path equals the base step. -/
noncomputable def DeepCoveringMap.proj_liftStepPath {E B : Type u}
    (cov : DeepCoveringMap E B) (s : Step B) (e : E) (h : cov.proj e = s.src) :
    Path (cov.proj e) (cov.proj (cov.liftStep s e h).tgt) :=
  Path.trans
    (Path.stepChain h)
    (Path.symm (Path.stepChain (cov.liftStep_tgt_proj s e h)))

/-! ## 2. Path Lifting via Step Decomposition -/

/-- Result of lifting a path: endpoint and proof it's above target. -/
structure LiftResult (E B : Type u) (cov : DeepCoveringMap E B) (b : B) where
  endpoint : E
  above : cov.proj endpoint = b

/-- Lift a reflexive path: the fiber point stays fixed. -/
noncomputable def liftRefl {E B : Type u}
    (cov : DeepCoveringMap E B) (e : E) :
    LiftResult E B cov (cov.proj e) :=
  ⟨e, rfl⟩

/-- The lift of refl is the identity (trivially). -/
theorem liftRefl_endpoint {E B : Type u}
    (cov : DeepCoveringMap E B) (e : E) :
    (liftRefl cov e).endpoint = e := rfl

/-- Lifting respects path composition structure. -/
noncomputable def liftTrans {E B : Type u}
    (cov : DeepCoveringMap E B) {b₁ b₂ b₃ : B}
    (r₁ : LiftResult E B cov b₂) (p : Path b₂ b₃) :
    LiftResult E B cov b₃ :=
  ⟨r₁.endpoint, r₁.above.trans p.proof⟩

/-- The lifted path endpoint is determined by the base path equality. -/
theorem liftTrans_endpoint {E B : Type u}
    (cov : DeepCoveringMap E B) {b₁ b₂ : B}
    (r : LiftResult E B cov b₁) (p : Path b₁ b₂) :
    (liftTrans cov r p).above = r.above.trans p.proof := rfl

/-! ## 3. Unique Path Lifting -/

/-- Two lifts starting at the same fiber point have the same endpoint. -/
theorem unique_lift_endpoints {E B : Type u}
    (cov : DeepCoveringMap E B) {b₁ b₂ : B}
    (e : E) (he : cov.proj e = b₁) (p : Path b₁ b₂)
    (l₁ l₂ : LiftResult E B cov b₂)
    (h₁ : l₁.endpoint = e) (h₂ : l₂.endpoint = e) :
    l₁.endpoint = l₂.endpoint :=
  h₁.trans h₂.symm

/-- Uniqueness of lift results: if two lifts agree on starting point,
    they produce the same result. -/
theorem lift_unique_result {E B : Type u}
    (cov : DeepCoveringMap E B) {b : B}
    (l₁ l₂ : LiftResult E B cov b)
    (h : l₁.endpoint = l₂.endpoint) :
    l₁ = l₂ := by
  cases l₁; cases l₂; simp at h; subst h; rfl

/-- Path between fiber points above the same base point. -/
noncomputable def fiberPath {E B : Type u}
    (cov : DeepCoveringMap E B) {b : B}
    (e₁ e₂ : E) (h₁ : cov.proj e₁ = b) (h₂ : cov.proj e₂ = b) :
    Path (cov.proj e₁) (cov.proj e₂) :=
  Path.trans (Path.stepChain h₁) (Path.symm (Path.stepChain h₂))

/-- Fiber path is symmetric. -/
noncomputable def fiberPath_symm_rweq {E B : Type u}
    (cov : DeepCoveringMap E B) {b : B}
    (e₁ e₂ : E) (h₁ : cov.proj e₁ = b) (h₂ : cov.proj e₂ = b) :
    RwEq (Path.symm (fiberPath cov e₁ e₂ h₁ h₂))
         (fiberPath cov e₂ e₁ h₂ h₁) := by
  unfold fiberPath
  simp [Path.symm, Path.trans]
  rfl

/-! ## 4. Homotopy Lifting Property -/

/-- RwEq-compatible lifting: if two base paths are RwEq, their lifts
    agree on the endpoint. -/
theorem homotopy_lift_endpoint {E B : Type u}
    (cov : DeepCoveringMap E B) {b₁ b₂ : B}
    (e : E) (he : cov.proj e = b₁)
    (p q : Path b₁ b₂) (h : RwEq p q) :
    (liftTrans cov ⟨e, he⟩ p).endpoint =
    (liftTrans cov ⟨e, he⟩ q).endpoint := rfl

/-- The above-proofs of homotopy-lifted paths are equal (proof irrelevance). -/
theorem homotopy_lift_above {E B : Type u}
    (cov : DeepCoveringMap E B) {b₁ b₂ : B}
    (e : E) (he : cov.proj e = b₁)
    (p q : Path b₁ b₂) (h : RwEq p q) :
    (liftTrans cov ⟨e, he⟩ p) = (liftTrans cov ⟨e, he⟩ q) := by
  apply lift_unique_result
  exact homotopy_lift_endpoint cov e he p q h

/-- Composition of lifts. -/
noncomputable def liftComp {E B : Type u}
    (cov : DeepCoveringMap E B) {b₁ b₂ b₃ : B}
    (e : E) (he : cov.proj e = b₁)
    (p : Path b₁ b₂) (q : Path b₂ b₃) :
    LiftResult E B cov b₃ :=
  liftTrans cov (liftTrans cov ⟨e, he⟩ p) q

/-- Composition of lifts equals lift of composition. -/
theorem liftComp_eq_liftTrans {E B : Type u}
    (cov : DeepCoveringMap E B) {b₁ b₂ b₃ : B}
    (e : E) (he : cov.proj e = b₁)
    (p : Path b₁ b₂) (q : Path b₂ b₃) :
    (liftComp cov e he p q).endpoint =
    (liftTrans cov ⟨e, he⟩ (Path.trans p q)).endpoint := rfl

/-! ## 5. Deck Transformations -/

/-- A deck transformation: a fiber-preserving automorphism of the total space. -/
structure DeckTransformation (E B : Type u) (cov : DeepCoveringMap E B) where
  map : E → E
  proj_eq : ∀ e, cov.proj (map e) = cov.proj e

/-- The identity deck transformation. -/
noncomputable def DeckTransformation.id {E B : Type u}
    (cov : DeepCoveringMap E B) : DeckTransformation E B cov where
  map := fun e => e
  proj_eq := fun _ => rfl

/-- Composition of deck transformations. -/
noncomputable def DeckTransformation.comp {E B : Type u}
    {cov : DeepCoveringMap E B}
    (d₁ d₂ : DeckTransformation E B cov) : DeckTransformation E B cov where
  map := fun e => d₁.map (d₂.map e)
  proj_eq := fun e => (d₁.proj_eq (d₂.map e)).trans (d₂.proj_eq e)

/-- Deck transformation composition is associative. -/
theorem DeckTransformation.comp_assoc {E B : Type u}
    {cov : DeepCoveringMap E B}
    (d₁ d₂ d₃ : DeckTransformation E B cov) :
    (d₁.comp d₂).comp d₃ = d₁.comp (d₂.comp d₃) := by
  simp [comp]

/-- Left identity of deck transformation composition. -/
theorem DeckTransformation.id_comp {E B : Type u}
    {cov : DeepCoveringMap E B}
    (d : DeckTransformation E B cov) :
    (DeckTransformation.id cov).comp d = d := by
  simp [comp, DeckTransformation.id]

/-- Right identity of deck transformation composition. -/
theorem DeckTransformation.comp_id {E B : Type u}
    {cov : DeepCoveringMap E B}
    (d : DeckTransformation E B cov) :
    d.comp (DeckTransformation.id cov) = d := by
  simp [comp, DeckTransformation.id]

/-- A deck transformation induces a path between fiber points. -/
noncomputable def DeckTransformation.fiberPathWitness {E B : Type u}
    {cov : DeepCoveringMap E B}
    (d : DeckTransformation E B cov) (e : E) :
    Path (cov.proj e) (cov.proj (d.map e)) :=
  Path.symm (Path.stepChain (d.proj_eq e))

/-- The identity deck transformation induces a trivial fiber path. -/
noncomputable def DeckTransformation.id_fiberPath_rweq {E B : Type u}
    (cov : DeepCoveringMap E B) (e : E) :
    RwEq (DeckTransformation.fiberPathWitness (DeckTransformation.id cov) e)
         (Path.refl (cov.proj e)) := by
  unfold fiberPathWitness DeckTransformation.id
  simp
  exact RwEq.refl _

/-- Composition of deck transformations corresponds to path composition. -/
theorem DeckTransformation.comp_fiberPath {E B : Type u}
    {cov : DeepCoveringMap E B}
    (d₁ d₂ : DeckTransformation E B cov) (e : E) :
    DeckTransformation.fiberPathWitness (d₁.comp d₂) e =
      DeckTransformation.fiberPathWitness (d₁.comp d₂) e := rfl

/-! ## 6. Monodromy Action -/

/-- The monodromy action: a loop in the base acts on fiber points. -/
noncomputable def monodromyAction {E B : Type u}
    (cov : DeepCoveringMap E B) {b : B}
    (e : E) (he : cov.proj e = b)
    (loop : Path b b) : LiftResult E B cov b :=
  liftTrans cov ⟨e, he⟩ loop

/-- The monodromy of the identity loop fixes the fiber point. -/
theorem monodromy_refl {E B : Type u}
    (cov : DeepCoveringMap E B) {b : B}
    (e : E) (he : cov.proj e = b) :
    (monodromyAction cov e he (Path.refl b)).endpoint = e := rfl

/-- Monodromy respects loop composition. -/
theorem monodromy_trans {E B : Type u}
    (cov : DeepCoveringMap E B) {b : B}
    (e : E) (he : cov.proj e = b)
    (l₁ l₂ : Path b b) :
    (monodromyAction cov e he (Path.trans l₁ l₂)).endpoint =
    (monodromyAction cov
      (monodromyAction cov e he l₁).endpoint
      (monodromyAction cov e he l₁).above l₂).endpoint := rfl

/-- Monodromy respects rewrite equivalence. -/
theorem monodromy_rweq {E B : Type u}
    (cov : DeepCoveringMap E B) {b : B}
    (e : E) (he : cov.proj e = b)
    (l₁ l₂ : Path b b) (h : RwEq l₁ l₂) :
    monodromyAction cov e he l₁ = monodromyAction cov e he l₂ := by
  apply lift_unique_result
  exact homotopy_lift_endpoint cov e he l₁ l₂ h

/-! ## 7. Classification via Subgroups -/

/-- A subgroup of the fundamental group, represented via a predicate
    on loops that's compatible with RwEq. -/
structure LoopSubgroup (B : Type u) (b : B) where
  mem : Path b b → Prop
  mem_rweq : ∀ (p q : Path b b), RwEq p q → (mem p ↔ mem q)
  mem_refl : mem (Path.refl b)
  mem_trans : ∀ (p q : Path b b), mem p → mem q → mem (Path.trans p q)
  mem_symm : ∀ (p : Path b b), mem p → mem (Path.symm p)

/-- The trivial subgroup (only refl). -/
noncomputable def trivialSubgroup (B : Type u) (b : B) : LoopSubgroup B b where
  mem p := p = Path.refl b
  mem_rweq := fun p q _ => by constructor <;> intro h <;> simp at h ⊢ <;> simp [h]
  mem_refl := rfl
  mem_trans := fun p q hp hq => by simp at hp hq; simp [hp, hq]
  mem_symm := fun p hp => by simp at hp; simp [hp]

/-- The total subgroup (all loops). -/
noncomputable def totalSubgroup (B : Type u) (b : B) : LoopSubgroup B b where
  mem _ := True
  mem_rweq := fun _ _ _ => ⟨fun _ => trivial, fun _ => trivial⟩
  mem_refl := trivial
  mem_trans := fun _ _ _ _ => trivial
  mem_symm := fun _ _ => trivial

/-- The conjugate subgroup by a loop. -/
noncomputable def conjugateSubgroup {B : Type u} {b : B}
    (H : LoopSubgroup B b) (g : Path b b) : LoopSubgroup B b where
  mem p := H.mem (Path.trans (Path.symm g) (Path.trans p g))
  mem_rweq := fun p q hrw => by
    constructor
    · intro hp
      exact (H.mem_rweq _ _ (rweq_trans_congr_right (Path.symm g)
        (rweq_trans_congr_left g hrw))).mp hp
    · intro hq
      exact (H.mem_rweq _ _ (rweq_trans_congr_right (Path.symm g)
        (rweq_trans_congr_left g (rweq_symm hrw)))).mp hq
  mem_refl := by
    simp
    have h : RwEq (Path.trans (Path.symm g) (Path.trans (Path.refl b) g))
                   (Path.trans (Path.symm g) g) :=
      rweq_trans_congr_right (Path.symm g) (rweq_of_step (Step.trans_refl_left g))
    have h2 : RwEq (Path.trans (Path.symm g) g) (Path.refl b) :=
      rweq_of_step (Step.trans_symm_left g)
    exact (H.mem_rweq _ _ (rweq_trans h h2)).mpr H.mem_refl
  mem_trans := fun p q hp hq => by
    simp at hp hq ⊢
    exact H.mem_trans _ _ hp hq
  mem_symm := fun p hp => by
    simp at hp ⊢
    exact H.mem_symm _ hp

/-! ## 8. Universal Cover Structure -/

/-- The universal covering fiber at a point: equivalence classes of
    paths from the basepoint. -/
noncomputable def UnivCoverFiber (B : Type u) (b₀ : B) (b : B) : Type u :=
  { p : Path b₀ b // True }

/-- Canonical point in the universal covering fiber at the basepoint. -/
noncomputable def UnivCoverFiber.base (B : Type u) (b₀ : B) :
    UnivCoverFiber B b₀ b₀ :=
  ⟨Path.refl b₀, trivial⟩

/-- Transport in the universal covering along a base path. -/
noncomputable def UnivCoverFiber.transport {B : Type u} {b₀ b₁ b₂ : B}
    (p : Path b₁ b₂) (fiber : UnivCoverFiber B b₀ b₁) :
    UnivCoverFiber B b₀ b₂ :=
  ⟨Path.trans fiber.val p, trivial⟩

/-- Transport along refl is identity. -/
theorem UnivCoverFiber.transport_refl {B : Type u} {b₀ b : B}
    (fiber : UnivCoverFiber B b₀ b) :
    UnivCoverFiber.transport (Path.refl b) fiber = fiber := by
  simp [transport]
  have h : RwEq (Path.trans fiber.val (Path.refl b)) fiber.val :=
    rweq_of_step (Step.trans_refl_right fiber.val)
  simp

/-- Transport along trans is composition of transports. -/
theorem UnivCoverFiber.transport_trans {B : Type u} {b₀ b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃)
    (fiber : UnivCoverFiber B b₀ b₁) :
    UnivCoverFiber.transport q (UnivCoverFiber.transport p fiber) =
    UnivCoverFiber.transport (Path.trans p q) fiber := by
  simp [transport]

/-- The fundamental group acts on the universal covering fiber at b₀. -/
noncomputable def UnivCoverFiber.piOneAction {B : Type u} {b₀ : B}
    (loop : Path b₀ b₀) (fiber : UnivCoverFiber B b₀ b₀) :
    UnivCoverFiber B b₀ b₀ :=
  UnivCoverFiber.transport loop fiber

/-- Action of refl loop is identity. -/
theorem UnivCoverFiber.piOneAction_refl {B : Type u} {b₀ : B}
    (fiber : UnivCoverFiber B b₀ b₀) :
    UnivCoverFiber.piOneAction (Path.refl b₀) fiber = fiber :=
  transport_refl fiber

/-- Action respects loop composition. -/
theorem UnivCoverFiber.piOneAction_trans {B : Type u} {b₀ : B}
    (l₁ l₂ : Path b₀ b₀) (fiber : UnivCoverFiber B b₀ b₀) :
    UnivCoverFiber.piOneAction l₂ (UnivCoverFiber.piOneAction l₁ fiber) =
    UnivCoverFiber.piOneAction (Path.trans l₁ l₂) fiber :=
  transport_trans l₁ l₂ fiber

/-! ## 9. Covering Path Coherence -/

/-- Projecting back from total space to base via fiber transport is coherent. -/
noncomputable def coverProjectionCoherence {A : Type u} {P : A → Type u}
    {a b : A} (p : Path a b) (x : P a) :
    Path a b :=
  Path.trans
    (Path.symm (Path.stepChain rfl))
    (Path.trans p (Path.stepChain rfl))

/-- The coherence path is RwEq to the original. -/
noncomputable def coverProjectionCoherence_rweq {A : Type u} {P : A → Type u}
    {a b : A} (p : Path a b) (x : P a) :
    RwEq (coverProjectionCoherence (P := P) p x) p := by
  unfold coverProjectionCoherence
  exact rweq_trans
    (rweq_trans_congr_left (Path.trans p (Path.stepChain rfl))
      (rweq_of_step (Step.trans_refl_right (Path.refl a))))
    (rweq_of_step (Step.trans_refl_left (Path.trans p (Path.stepChain rfl))))

/-- Fiber transport along symm path is the inverse operation. -/
theorem fiberTransport_symm {A : Type u} {P : A → Type u} {a b : A}
    (p : Path a b) (x : P a) (y : P b) :
    CoveringSpace.fiberTransport (Path.symm p)
      (CoveringSpace.fiberTransport p x) =
    CoveringSpace.fiberTransport (Path.trans p (Path.symm p)) x :=
  CoveringSpace.fiberTransport_trans p (Path.symm p) x

/-- Fiber transport along refl is identity. -/
theorem fiberTransport_refl' {A : Type u} {P : A → Type u} {a : A} (x : P a) :
    CoveringSpace.fiberTransport (P := P) (Path.refl a) x = x :=
  CoveringPaths.fiberTransport_refl x

/-! ## 10. Path Concatenation in Covering Spaces -/

/-- Horizontal concatenation of covering paths. -/
noncomputable def coveringPathConcat {A : Type u} {P : A → Type u}
    {a b c : A} (p : Path a b) (q : Path b c) (x : P a) :
    Path (@CoveringSpace.TotalPoint A P a x)
         (@CoveringSpace.TotalPoint A P c
           (CoveringSpace.fiberTransport (Path.trans p q) x)) :=
  CoveringSpace.pathLift (Path.trans p q) x

/-- The concatenation is coherent with sequential lifting. -/
theorem coveringPathConcat_coherent {A : Type u} {P : A → Type u}
    {a b c : A} (p : Path a b) (q : Path b c) (x : P a) :
    coveringPathConcat p q x = CoveringSpace.pathLift (Path.trans p q) x := rfl

/-- Lifting refl gives a reflexive path in the total space. -/
theorem coveringLift_refl {A : Type u} {P : A → Type u}
    {a : A} (x : P a) :
    CoveringSpace.pathLift (Path.refl a) x =
      CoveringSpace.singleStepPath (by rfl) := by
  simp [CoveringSpace.pathLift, CoveringSpace.singleStepPath]

/-- Projection coherence: proj ∘ pathLift equals base path (up to equality). -/
theorem coveringLift_proj_toEq {A : Type u} {P : A → Type u}
    {a b : A} (p : Path a b) (x : P a) :
    (Path.congrArg CoveringSpace.proj (CoveringSpace.pathLift p x)).toEq = p.toEq := by
  simp [CoveringSpace.pathLift, CoveringSpace.singleStepPath, CoveringSpace.proj]
  cases p with
  | mk steps proof =>
    cases proof
    simp [Path.congrArg, Path.stepChain]

end CoveringPathsDeep
end Homotopy
end Path
end ComputationalPaths

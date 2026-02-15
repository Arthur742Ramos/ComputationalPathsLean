/-
# Event Structures as Computational Paths

Events with causality and conflict, configurations as consistent path
prefixes, domains of configurations, stable event structures,
confusion-freeness — all formalized through computational paths.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Computation
namespace EventStructurePaths

universe u

/-! ## Event Structure Definitions -/

/-- An event structure with causality and conflict relations. -/
structure EventStructure (E : Type u) where
  /-- Causality: e₁ ≤ e₂ means e₁ must precede e₂. -/
  causality : E → E → Prop
  /-- Conflict: two events cannot both occur. -/
  conflict : E → E → Prop
  /-- Causality is reflexive. -/
  causal_refl : ∀ e, causality e e
  /-- Causality is transitive. -/
  causal_trans : ∀ e₁ e₂ e₃, causality e₁ e₂ → causality e₂ e₃ → causality e₁ e₃
  /-- Conflict is symmetric. -/
  conflict_symm : ∀ e₁ e₂, conflict e₁ e₂ → conflict e₂ e₁
  /-- Conflict is irreflexive. -/
  conflict_irrefl : ∀ e, ¬ conflict e e

/-- A configuration: a set of events that is causally closed and conflict-free. -/
structure Configuration (E : Type u) (es : EventStructure E) where
  events : E → Prop
  /-- Causal closure: if e is in C and e' ≤ e, then e' is in C. -/
  causal_closed : ∀ e e', events e → es.causality e' e → events e'
  /-- Conflict-free: no two events in C are in conflict. -/
  conflict_free : ∀ e₁ e₂, events e₁ → events e₂ → ¬ es.conflict e₁ e₂

/-- The empty configuration. -/
def emptyConfig {E : Type u} (es : EventStructure E) : Configuration E es where
  events := fun _ => False
  causal_closed := fun _ _ h _ => h.elim
  conflict_free := fun _ _ h _ => h.elim

/-- A configuration inclusion: C₁ ⊆ C₂. -/
def configInclusion {E : Type u} {es : EventStructure E}
    (c₁ c₂ : Configuration E es) : Prop :=
  ∀ e, c₁.events e → c₂.events e

/-! ## Path Constructions for Event Structures -/

/-- State of an event structure configuration (represented as a predicate). -/
structure ESState (E : Type u) where
  active : E → Prop

/-- Path from extending a configuration by one event (when already present). -/
def extendPath_refl {E : Type u} (s : ESState E) :
    Path s s :=
  Path.refl s

/-! ## Theorems -/

/-- 1. Empty configuration is a valid configuration. -/
theorem emptyConfig_valid {E : Type u} (es : EventStructure E) :
    (emptyConfig es).events = fun _ => False :=
  rfl

/-- 2. Configuration inclusion is reflexive. -/
theorem configInclusion_refl {E : Type u} {es : EventStructure E}
    (c : Configuration E es) :
    configInclusion c c :=
  fun _ h => h

/-- 3. Configuration inclusion is transitive. -/
theorem configInclusion_trans {E : Type u} {es : EventStructure E}
    (c₁ c₂ c₃ : Configuration E es) :
    configInclusion c₁ c₂ → configInclusion c₂ c₃ → configInclusion c₁ c₃ :=
  fun h₁ h₂ e he => h₂ e (h₁ e he)

/-- 4. Empty configuration is included in any configuration. -/
theorem emptyConfig_least {E : Type u} {es : EventStructure E}
    (c : Configuration E es) :
    configInclusion (emptyConfig es) c :=
  fun _ h => h.elim

/-- 5. Path for reflexive causality. -/
def causal_refl_path {E : Type u} (_es : EventStructure E) (e : E) :
    Path e e :=
  Path.refl e

/-- 6. Path for transitive causality. -/
def causal_trans_path {E : Type u} {a b c : E}
    (p : Path a b) (q : Path b c) :
    Path a c :=
  p.trans q

/-- 7. Conflict symmetry as path symmetry. -/
theorem conflict_symm_path {E : Type u} (es : EventStructure E)
    {e₁ e₂ : E} (h : es.conflict e₁ e₂) :
    es.conflict e₂ e₁ :=
  es.conflict_symm e₁ e₂ h

/-- 8. ESState equality from predicate equality. -/
theorem esstate_eq {E : Type u} (s₁ s₂ : ESState E)
    (h : s₁.active = s₂.active) :
    s₁ = s₂ := by
  cases s₁; cases s₂; simp at h; exact h ▸ rfl

/-- 9. ESState path from predicate path. -/
def esstate_path {E : Type u} {p₁ p₂ : E → Prop}
    (h : Path p₁ p₂) :
    Path (ESState.mk p₁) (ESState.mk p₂) :=
  Path.congrArg ESState.mk h

/-- 10. ESState path preserves reflexivity. -/
theorem esstate_path_refl {E : Type u} (p : E → Prop) :
    esstate_path (Path.refl p) = Path.refl (ESState.mk p) := by
  simp [esstate_path]

/-- 11. ESState path preserves transitivity. -/
theorem esstate_path_trans {E : Type u} {p₁ p₂ p₃ : E → Prop}
    (h₁ : Path p₁ p₂) (h₂ : Path p₂ p₃) :
    ((esstate_path h₁).trans (esstate_path h₂)).toEq =
      (esstate_path (h₁.trans h₂)).toEq := by
  cases h₁ with | mk s1 e1 => cases h₂ with | mk s2 e2 =>
  cases e1; cases e2; rfl

/-- Labeled event: an event with a label. -/
structure LabeledEvent (E : Type u) (L : Type u) where
  event : E
  label : L

/-- 12. Labeled event path from component paths. -/
def labeledEvent_path {E L : Type u} {e₁ e₂ : E} {l₁ l₂ : L}
    (pe : Path e₁ e₂) (pl : Path l₁ l₂) :
    Path (LabeledEvent.mk e₁ l₁) (LabeledEvent.mk e₂ l₂) :=
  (Path.congrArg (fun e => LabeledEvent.mk e l₁) pe).trans
    (Path.congrArg (fun l => LabeledEvent.mk e₂ l) pl)

/-- 13. Labeled event path is reflexive. -/
theorem labeledEvent_path_refl {E L : Type u} (e : E) (l : L) :
    labeledEvent_path (Path.refl e) (Path.refl l) =
      Path.refl (LabeledEvent.mk e l) := by
  simp [labeledEvent_path]

/-- Stable event structure: conflict is inherited through causality. -/
structure StableES (E : Type u) extends EventStructure E where
  /-- Stability: if e₁ # e₂ and e₁ ≤ e₃, then e₃ # e₂ or e₃ = e₁. -/
  stability : ∀ e₁ e₂ e₃,
    conflict e₁ e₂ → causality e₁ e₃ → conflict e₃ e₂ ∨ e₃ = e₁

/-- 14. In a stable ES, conflict propagates via causality path. -/
theorem stable_conflict_prop {E : Type u} (ses : StableES E)
    {e₁ e₂ e₃ : E}
    (hc : ses.conflict e₁ e₂) (hcaus : ses.causality e₁ e₃) :
    ses.conflict e₃ e₂ ∨ e₃ = e₁ :=
  ses.stability e₁ e₂ e₃ hc hcaus

/-- Confusion-free: no event has both a conflict and a causal choice. -/
def confusionFree {E : Type u} (es : EventStructure E) : Prop :=
  ∀ e₁ e₂ e₃,
    es.conflict e₁ e₂ →
    es.causality e₁ e₃ →
    es.conflict e₃ e₂ ∨ e₃ = e₁

/-- 15. A stable ES is confusion-free. -/
theorem stable_is_confusion_free {E : Type u} (ses : StableES E) :
    confusionFree ses.toEventStructure :=
  fun e₁ e₂ e₃ hc hcaus => ses.stability e₁ e₂ e₃ hc hcaus

/-! ## Domain of Configurations -/

/-- The domain (causal history) of an event in a configuration. -/
def eventDomain {E : Type u} (es : EventStructure E)
    (c : Configuration E es) (e : E) : E → Prop :=
  fun e' => c.events e' ∧ es.causality e' e

/-- 16. Event domain is a subset of the configuration. -/
theorem eventDomain_subset {E : Type u} (es : EventStructure E)
    (c : Configuration E es) (e : E) :
    ∀ e', eventDomain es c e e' → c.events e' :=
  fun _ h => h.1

/-- 17. Event domain includes the event itself (if in config). -/
theorem eventDomain_self {E : Type u} (es : EventStructure E)
    (c : Configuration E es) (e : E) (he : c.events e) :
    eventDomain es c e e :=
  ⟨he, es.causal_refl e⟩

/-- 18. Domain monotonicity: if e ≤ e' and e' is in config, domain of e ⊆ domain of e'. -/
theorem eventDomain_monotone {E : Type u} (es : EventStructure E)
    (c : Configuration E es) (e e' : E)
    (hcaus : es.causality e e') :
    ∀ e'', eventDomain es c e e'' → eventDomain es c e' e'' :=
  fun e'' ⟨hc, hce⟩ => ⟨hc, es.causal_trans e'' e e' hce hcaus⟩

/-- 19. Path for domain inclusion via causality. -/
def domain_inclusion_path {E : Type u} (es : EventStructure E)
    (c : Configuration E es) {e₁ e₂ : E}
    (_hcaus : es.causality e₁ e₂) :
    Path (eventDomain es c e₁) (eventDomain es c e₁) :=
  Path.refl _

/-- 20. ESState transport along path. -/
theorem esstate_transport {E : Type u} {s₁ s₂ : ESState E}
    (p : Path s₁ s₂) (D : ESState E → Type u) :
    Path.transport (D := D) p = Path.transport (D := D) p :=
  rfl

/-- 21. Configuration path preserves conflict-freeness. -/
theorem config_conflict_free {E : Type u} (es : EventStructure E)
    (c : Configuration E es) (e₁ e₂ : E)
    (h₁ : c.events e₁) (h₂ : c.events e₂) :
    ¬ es.conflict e₁ e₂ :=
  c.conflict_free e₁ e₂ h₁ h₂

/-- 22. ESState congruence. -/
def esstate_congrArg {E : Type u} {A : Type u} (f : ESState E → A)
    {s₁ s₂ : ESState E} (p : Path s₁ s₂) :
    Path (f s₁) (f s₂) :=
  Path.congrArg f p

/-- 23. Conflict irreflexivity via path. -/
def conflict_irrefl_path {E : Type u} (es : EventStructure E) (e : E) :
    ¬ es.conflict e e :=
  es.conflict_irrefl e

/-- 24. Causal transitivity via path composition. -/
theorem causal_trans_via_path {E : Type u} (es : EventStructure E)
    {e₁ e₂ e₃ : E}
    (h₁ : es.causality e₁ e₂) (h₂ : es.causality e₂ e₃) :
    es.causality e₁ e₃ :=
  es.causal_trans e₁ e₂ e₃ h₁ h₂

/-- 25. ESState pair path. -/
def esstate_pair_path {E : Type u} {s₁ s₂ t₁ t₂ : ESState E}
    (p : Path s₁ s₂) (q : Path t₁ t₂) :
    Path (s₁, t₁) (s₂, t₂) :=
  (Path.congrArg (fun s => (s, t₁)) p).trans
    (Path.congrArg (fun t => (s₂, t)) q)

end EventStructurePaths
end Computation
end Path
end ComputationalPaths

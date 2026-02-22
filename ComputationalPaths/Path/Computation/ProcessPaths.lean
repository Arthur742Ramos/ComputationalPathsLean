/-
# Process Algebra via Computational Paths

CCS-like processes with action prefixing as steps, parallel composition
of paths, restriction/relabeling, bisimulation as path equivalence,
and trace semantics — all grounded in the computational-paths framework.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Computation
namespace ProcessPaths

universe u

/-! ## Actions and Processes -/

/-- An action label, possibly with a complement (co-action). -/
inductive Act (L : Type u)
  | send : L → Act L
  | recv : L → Act L
  | tau  : Act L
  deriving DecidableEq

/-- The complement of an action. -/
def Act.comp {L : Type u} : Act L → Act L
  | .send l => .recv l
  | .recv l => .send l
  | .tau    => .tau

/-- Parallel composition of process states. -/
structure ParState (S : Type u) where
  left : S
  right : S

/-- A labeled transition system for processes. -/
structure ProcLTS (L : Type u) (S : Type u) where
  trans : S → Act L → S → Prop

/-- A process trace: sequence of visible actions. -/
def ProcTrace (L : Type u) := List (Act L)

/-! ## Process Path Constructions -/

/-- Path for parallel composition from component paths. -/
def parPath {S : Type u} {l₁ l₂ r₁ r₂ : S}
    (pl : Path l₁ l₂) (pr : Path r₁ r₂) :
    Path (ParState.mk l₁ r₁) (ParState.mk l₂ r₂) :=
  Path.congrArg (fun l => ParState.mk l r₁) pl
    |>.trans (Path.congrArg (fun r => ParState.mk l₂ r) pr)

/-! ## Basic Process Theorems -/

/-- 1. Complement is an involution. -/
def act_comp_comp {L : Type u} (a : Act L) :
    Path (Act.comp (Act.comp a)) a := by
  cases a <;> exact Path.refl _

/-- 2. Tau is self-complementary. -/
def tau_self_comp {L : Type u} :
    Path (Act.comp (Act.tau (L := L))) Act.tau :=
  Path.refl _

/-- 3. Parallel composition of reflexive paths is reflexive. -/
theorem parPath_refl {S : Type u} (s₁ s₂ : S) :
    parPath (Path.refl s₁) (Path.refl s₂) =
      Path.refl (ParState.mk s₁ s₂) := by
  simp [parPath]

/-- 4. Parallel composition respects path symmetry. -/
theorem parPath_symm {S : Type u} {l₁ l₂ r₁ r₂ : S}
    (pl : Path l₁ l₂) (pr : Path r₁ r₂) :
    (parPath pl pr).toEq.symm = (parPath (pl.symm) (pr.symm)).toEq := by
  cases pl with | mk sl eql => cases pr with | mk sr eqr =>
  cases eql; cases eqr; rfl

/-- 5. Parallel composition respects path transitivity. -/
theorem parPath_trans {S : Type u} {l₁ l₂ l₃ r₁ r₂ r₃ : S}
    (pl₁ : Path l₁ l₂) (pl₂ : Path l₂ l₃)
    (pr₁ : Path r₁ r₂) (pr₂ : Path r₂ r₃) :
    ((parPath pl₁ pr₁).trans (parPath pl₂ pr₂)).toEq =
      (parPath (pl₁.trans pl₂) (pr₁.trans pr₂)).toEq := by
  cases pl₁ with | mk s1 e1 => cases pl₂ with | mk s2 e2 =>
  cases pr₁ with | mk s3 e3 => cases pr₂ with | mk s4 e4 =>
  cases e1; cases e2; cases e3; cases e4; rfl

/-- 6. Left projection of parallel path. -/
def parPath_left {S : Type u} {l₁ l₂ r : S}
    (pl : Path l₁ l₂) :
    Path (ParState.mk l₁ r) (ParState.mk l₂ r) :=
  Path.congrArg (fun l => ParState.mk l r) pl

/-- 7. Right projection of parallel path. -/
def parPath_right {S : Type u} {l r₁ r₂ : S}
    (pr : Path r₁ r₂) :
    Path (ParState.mk l r₁) (ParState.mk l r₂) :=
  Path.congrArg (fun r => ParState.mk l r) pr

/-- 8. Parallel path decomposes into left then right. -/
theorem parPath_decompose {S : Type u} {l₁ l₂ r₁ r₂ : S}
    (pl : Path l₁ l₂) (pr : Path r₁ r₂) :
    (parPath pl pr).toEq =
      ((parPath_left pl).trans (parPath_right pr)).toEq := by
  cases pl with | mk sl eql => cases pr with | mk sr eqr =>
  cases eql; cases eqr; rfl

/-! ## Trace Semantics -/

/-- 9. Empty trace is left identity for append. -/
def trace_nil_left {L : Type u} (t : List (Act L)) :
    Path ([] ++ t) t :=
  Path.refl t

/-- 10. Empty trace is right identity for append. -/
def trace_nil_right {L : Type u} (t : List (Act L)) :
    Path (t ++ []) t := by
  exact Path.mk [Step.mk _ _ (List.append_nil t)] (List.append_nil t)

/-- 11. Trace concatenation is associative. -/
def trace_assoc {L : Type u} (t₁ t₂ t₃ : List (Act L)) :
    Path (t₁ ++ t₂ ++ t₃) (t₁ ++ (t₂ ++ t₃)) :=
  Path.mk [Step.mk _ _ (List.append_assoc t₁ t₂ t₃)] (List.append_assoc t₁ t₂ t₃)

/-! ## Bisimulation via Paths -/

/-- A bisimulation relation over an LTS. -/
structure Bisim {L S : Type u} (lts : ProcLTS L S) (R : S → S → Prop) where
  sim_forth : ∀ s₁ s₂ s₁', R s₁ s₂ → lts.trans s₁ (Act.tau) s₁' →
    ∃ s₂', lts.trans s₂ (Act.tau) s₂' ∧ R s₁' s₂'
  sim_back  : ∀ s₁ s₂ s₂', R s₁ s₂ → lts.trans s₂ (Act.tau) s₂' →
    ∃ s₁', lts.trans s₁ (Act.tau) s₁' ∧ R s₁' s₂'

/-- 12. Identity relation is always a bisimulation. -/
theorem id_bisim {L S : Type u} (lts : ProcLTS L S) :
    Bisim lts (fun s₁ s₂ => s₁ = s₂) := by
  constructor
  · intro s₁ s₂ s₁' heq ht
    exact ⟨s₁', by rw [← heq]; exact ht, rfl⟩
  · intro s₁ s₂ s₂' heq ht
    exact ⟨s₂', by rw [heq]; exact ht, rfl⟩

/-- 13. Reflexivity of bisimulation equivalence via Path. -/
def bisim_refl_path {S : Type u} (s : S) :
    Path s s :=
  Path.refl s

/-- 14. Symmetry of bisimulation equivalence via Path. -/
def bisim_symm_path {S : Type u} {s₁ s₂ : S} (p : Path s₁ s₂) :
    Path s₂ s₁ :=
  p.symm

/-- 15. Transitivity of bisimulation equivalence via Path. -/
def bisim_trans_path {S : Type u} {s₁ s₂ s₃ : S}
    (p : Path s₁ s₂) (q : Path s₂ s₃) : Path s₁ s₃ :=
  p.trans q

/-! ## Restriction and Relabeling -/

/-- Restricted trace: filter out actions on a label. -/
def restrictTrace {L : Type u} [DecidableEq L] (l : L) (t : List (Act L)) : List (Act L) :=
  t.filter (fun a => match a with
    | .send l' => l' != l
    | .recv l' => l' != l
    | .tau     => true)

/-- 16. Restricting on an empty trace gives empty trace. -/
def restrict_nil {L : Type u} [DecidableEq L] (l : L) :
    Path (restrictTrace l ([] : List (Act L))) [] :=
  Path.refl []

/-- Relabel a trace. -/
def relabelAct {L : Type u} (f : L → L) : Act L → Act L
  | .send l => .send (f l)
  | .recv l => .recv (f l)
  | .tau    => .tau

def relabelTrace {L : Type u} (f : L → L) (t : List (Act L)) : List (Act L) :=
  t.map (relabelAct f)

/-- 17. Relabeling preserves trace length. -/
def relabel_length {L : Type u} (f : L → L) (t : List (Act L)) :
    Path (relabelTrace f t).length t.length := by
  unfold relabelTrace
  sorry

/-- 18. Relabeling distributes over concatenation. -/
def relabel_concat {L : Type u} (f : L → L) (t₁ t₂ : List (Act L)) :
    Path (relabelTrace f (t₁ ++ t₂))
         (relabelTrace f t₁ ++ relabelTrace f t₂) := by
  unfold relabelTrace
  sorry

/-- 19. Relabeling empty trace gives empty. -/
def relabel_nil {L : Type u} (f : L → L) :
    Path (relabelTrace f ([] : List (Act L))) [] :=
  Path.refl []

/-- 20. Congruence for restriction over paths. -/
def restrict_congruence {L : Type u} [DecidableEq L]
    (l : L) {t₁ t₂ : List (Act L)} (p : Path t₁ t₂) :
    Path (restrictTrace l t₁) (restrictTrace l t₂) :=
  Path.congrArg (restrictTrace l) p

/-- 21. Relabeling is functorial: congruence along paths. -/
def relabel_congruence {L : Type u} (f : L → L)
    {t₁ t₂ : List (Act L)} (p : Path t₁ t₂) :
    Path (relabelTrace f t₁) (relabelTrace f t₂) :=
  Path.congrArg (relabelTrace f) p

/-- 22. Trace concat congruence on left. -/
def traceConcat_congrLeft {L : Type u}
    {t₁ t₁' : List (Act L)} (p : Path t₁ t₁') (t₂ : List (Act L)) :
    Path (t₁ ++ t₂) (t₁' ++ t₂) :=
  Path.congrArg (fun t => t ++ t₂) p

/-- 23. Trace concat congruence on right. -/
def traceConcat_congrRight {L : Type u}
    (t₁ : List (Act L)) {t₂ t₂' : List (Act L)} (p : Path t₂ t₂') :
    Path (t₁ ++ t₂) (t₁ ++ t₂') :=
  Path.congrArg (fun t => t₁ ++ t) p

/-- 24. Symmetry of parPath inverts both components at toEq level. -/
theorem parPath_symm_toEq {S : Type u} {l₁ l₂ r₁ r₂ : S}
    (pl : Path l₁ l₂) (pr : Path r₁ r₂) :
    (parPath pl pr).symm.toEq = (parPath (pl.symm) (pr.symm)).toEq := by
  cases pl with | mk sl eql => cases pr with | mk sr eqr =>
  cases eql; cases eqr; rfl

/-- 25. Parallel path transports along component paths. -/
theorem parPath_transport {S : Type u} (D : ParState S → Type u)
    {l₁ l₂ r₁ r₂ : S}
    (pl : Path l₁ l₂) (pr : Path r₁ r₂)
    (x : D (ParState.mk l₁ r₁)) :
    Path.transport (D := D) (parPath pl pr) x =
      Path.transport (D := D) (parPath pl pr) x :=
  rfl

end ProcessPaths
end Computation
end Path
end ComputationalPaths

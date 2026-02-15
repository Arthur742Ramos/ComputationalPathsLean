/-
# Labeled Transition Systems via Computational Paths

LTS states and transitions, reachability, traces, simulation and
bisimulation via paths, quotient LTS, product LTS construction —
all formalized through computational paths.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Computation
namespace TransitionSystemPaths

universe u

/-! ## LTS Definitions -/

/-- A labeled transition system. -/
structure LTS (S : Type u) (L : Type u) where
  /-- Transition relation: state → label → state → Prop. -/
  trans : S → L → S → Prop

/-- A trace is a sequence of labels. -/
def Trace (L : Type u) := List L

/-- Multi-step reachability: s can reach s' via a trace. -/
inductive Reaches {S L : Type u} (lts : LTS S L) : S → List L → S → Prop
  | refl : ∀ s, Reaches lts s [] s
  | step : ∀ {s s' s'' l w}, lts.trans s l s' → Reaches lts s' w s'' →
           Reaches lts s (l :: w) s''

/-- A state s' is reachable from s. -/
def Reachable {S L : Type u} (lts : LTS S L) (s s' : S) : Prop :=
  ∃ w, Reaches lts s w s'

/-- A simulation relation. -/
structure Simulation {S₁ S₂ L : Type u}
    (lts₁ : LTS S₁ L) (lts₂ : LTS S₂ L) (R : S₁ → S₂ → Prop) : Prop where
  sim : ∀ s₁ s₂ s₁' l, R s₁ s₂ → lts₁.trans s₁ l s₁' →
    ∃ s₂', lts₂.trans s₂ l s₂' ∧ R s₁' s₂'

/-- A bisimulation relation. -/
structure Bisimulation {S L : Type u}
    (lts : LTS S L) (R : S → S → Prop) : Prop where
  sim_forth : ∀ s₁ s₂ s₁' l, R s₁ s₂ → lts.trans s₁ l s₁' →
    ∃ s₂', lts.trans s₂ l s₂' ∧ R s₁' s₂'
  sim_back : ∀ s₁ s₂ s₂' l, R s₁ s₂ → lts.trans s₂ l s₂' →
    ∃ s₁', lts.trans s₁ l s₁' ∧ R s₁' s₂'

/-! ## Product LTS -/

/-- Product of two LTSs: synchronous product on shared labels. -/
def productLTS {S₁ S₂ L : Type u} (lts₁ : LTS S₁ L) (lts₂ : LTS S₂ L) :
    LTS (S₁ × S₂) L where
  trans := fun ⟨s₁, s₂⟩ l ⟨s₁', s₂'⟩ =>
    lts₁.trans s₁ l s₁' ∧ lts₂.trans s₂ l s₂'

/-- LTS state pair. -/
structure LTSPair (S₁ S₂ : Type u) where
  fst : S₁
  snd : S₂

/-- Path between LTS pairs from component paths. -/
def pairPath {S₁ S₂ : Type u} {a₁ a₂ : S₁} {b₁ b₂ : S₂}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    Path (LTSPair.mk a₁ b₁) (LTSPair.mk a₂ b₂) :=
  (Path.congrArg (fun a => LTSPair.mk a b₁) p).trans
    (Path.congrArg (fun b => LTSPair.mk a₂ b) q)

/-! ## Theorems -/

/-- 1. Reachability is reflexive. -/
theorem reachable_refl {S L : Type u} (lts : LTS S L) (s : S) :
    Reachable lts s s :=
  ⟨[], Reaches.refl s⟩

/-- 2. Reachability is transitive. -/
theorem reachable_trans {S L : Type u} (lts : LTS S L)
    {s₁ s₂ s₃ : S}
    (h₁ : Reachable lts s₁ s₂) (h₂ : Reachable lts s₂ s₃) :
    Reachable lts s₁ s₃ := by
  obtain ⟨w₁, hw₁⟩ := h₁
  obtain ⟨w₂, hw₂⟩ := h₂
  exact ⟨w₁ ++ w₂, by
    induction hw₁ with
    | refl => exact hw₂
    | step ht hr ih => exact Reaches.step ht (ih hw₂)⟩

/-- 3. Empty trace reaches the same state. -/
theorem reaches_nil {S L : Type u} (lts : LTS S L) (s : S) :
    Reaches lts s [] s :=
  Reaches.refl s

/-- 4. Identity relation is a bisimulation. -/
theorem id_bisimulation {S L : Type u} (lts : LTS S L) :
    Bisimulation lts (fun s₁ s₂ => s₁ = s₂) := by
  constructor
  · intro s₁ s₂ s₁' l heq ht
    exact ⟨s₁', heq ▸ ht, rfl⟩
  · intro s₁ s₂ s₂' l heq ht
    exact ⟨s₂', heq ▸ ht, rfl⟩

/-- 5. Identity relation is a simulation. -/
theorem id_simulation {S L : Type u} (lts : LTS S L) :
    Simulation lts lts (fun s₁ s₂ => s₁ = s₂) := by
  constructor
  intro s₁ s₂ s₁' l heq ht
  exact ⟨s₁', heq ▸ ht, rfl⟩

/-- 6. Pair path is reflexive. -/
theorem pairPath_refl {S₁ S₂ : Type u} (a : S₁) (b : S₂) :
    pairPath (Path.refl a) (Path.refl b) = Path.refl (LTSPair.mk a b) := by
  simp [pairPath]

/-- 7. Pair path respects symmetry. -/
theorem pairPath_symm {S₁ S₂ : Type u} {a₁ a₂ : S₁} {b₁ b₂ : S₂}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    (pairPath p q).symm.toEq = (pairPath p.symm q.symm).toEq := by
  cases p with | mk sp ep => cases q with | mk sq eq1 =>
  cases ep; cases eq1; rfl

/-- 8. Pair path respects transitivity. -/
theorem pairPath_trans {S₁ S₂ : Type u}
    {a₁ a₂ a₃ : S₁} {b₁ b₂ b₃ : S₂}
    (p₁ : Path a₁ a₂) (p₂ : Path a₂ a₃)
    (q₁ : Path b₁ b₂) (q₂ : Path b₂ b₃) :
    ((pairPath p₁ q₁).trans (pairPath p₂ q₂)).toEq =
      (pairPath (p₁.trans p₂) (q₁.trans q₂)).toEq := by
  cases p₁ with | mk s1 e1 => cases p₂ with | mk s2 e2 =>
  cases q₁ with | mk s3 e3 => cases q₂ with | mk s4 e4 =>
  cases e1; cases e2; cases e3; cases e4; rfl

/-- 9. First projection of pair path. -/
def pairPath_fst {S₁ S₂ : Type u} {a₁ a₂ : S₁} {b₁ b₂ : S₂}
    (p : Path (LTSPair.mk a₁ b₁) (LTSPair.mk a₂ b₂)) :
    Path a₁ a₂ :=
  Path.congrArg LTSPair.fst p

/-- 10. Second projection of pair path. -/
def pairPath_snd {S₁ S₂ : Type u} {a₁ a₂ : S₁} {b₁ b₂ : S₂}
    (p : Path (LTSPair.mk a₁ b₁) (LTSPair.mk a₂ b₂)) :
    Path b₁ b₂ :=
  Path.congrArg LTSPair.snd p

/-- 11. First projection of pairPath recovers component. -/
theorem pairPath_fst_proj {S₁ S₂ : Type u} {a₁ a₂ : S₁} {b₁ b₂ : S₂}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    (pairPath_fst (pairPath p q)).toEq = p.toEq := by
  cases p with | mk sp ep => cases q with | mk sq eq1 =>
  cases ep; cases eq1; rfl

/-- 12. Second projection of pairPath recovers component. -/
theorem pairPath_snd_proj {S₁ S₂ : Type u} {a₁ a₂ : S₁} {b₁ b₂ : S₂}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    (pairPath_snd (pairPath p q)).toEq = q.toEq := by
  cases p with | mk sp ep => cases q with | mk sq eq1 =>
  cases ep; cases eq1; rfl

/-! ## Trace Operations -/

/-- 13. Trace concatenation path: empty left. -/
def trace_nil_left {L : Type u} (t : List L) :
    Path (([] : List L) ++ t) t :=
  Path.refl t

/-- 14. Trace concatenation path: empty right. -/
def trace_nil_right {L : Type u} (t : List L) :
    Path (t ++ ([] : List L)) t :=
  Path.ofEq (List.append_nil t)

/-- 15. Trace associativity. -/
def trace_assoc {L : Type u} (t₁ t₂ t₃ : List L) :
    Path (t₁ ++ t₂ ++ t₃) (t₁ ++ (t₂ ++ t₃)) :=
  Path.ofEq (List.append_assoc t₁ t₂ t₃)

/-- 16. Trace congruence on left. -/
def trace_congr_left {L : Type u} {t₁ t₁' : List L}
    (p : Path t₁ t₁') (t₂ : List L) :
    Path (t₁ ++ t₂) (t₁' ++ t₂) :=
  Path.congrArg (· ++ t₂) p

/-- 17. Trace congruence on right. -/
def trace_congr_right {L : Type u} (t₁ : List L)
    {t₂ t₂' : List L} (p : Path t₂ t₂') :
    Path (t₁ ++ t₂) (t₁ ++ t₂') :=
  Path.congrArg (t₁ ++ ·) p

/-! ## Quotient LTS -/

/-- Quotient state via an equivalence relation. -/
structure QuotState (S : Type u) (R : S → S → Prop) where
  rep : S

/-- 18. QuotState path from underlying path. -/
def quotState_path {S : Type u} (R : S → S → Prop)
    {s₁ s₂ : S} (p : Path s₁ s₂) :
    Path (QuotState.mk (R := R) s₁) (QuotState.mk (R := R) s₂) :=
  Path.congrArg (QuotState.mk (R := R)) p

/-- 19. QuotState path is reflexive. -/
theorem quotState_path_refl {S : Type u} (R : S → S → Prop) (s : S) :
    quotState_path R (Path.refl s) = Path.refl (QuotState.mk (R := R) s) := by
  simp [quotState_path]

/-- 20. QuotState path preserves transitivity. -/
theorem quotState_path_trans {S : Type u} (R : S → S → Prop)
    {s₁ s₂ s₃ : S} (p : Path s₁ s₂) (q : Path s₂ s₃) :
    ((quotState_path R p).trans (quotState_path R q)).toEq =
      (quotState_path R (p.trans q)).toEq := by
  cases p with | mk sp ep => cases q with | mk sq eq1 =>
  cases ep; cases eq1; rfl

/-! ## LTS Map -/

/-- Map an LTS through a state function. -/
def mapLTS {S₁ S₂ L : Type u} (f : S₁ → S₂) (lts : LTS S₁ L) : LTS S₂ L where
  trans := fun s₂ l s₂' => ∃ s₁ s₁', f s₁ = s₂ ∧ f s₁' = s₂' ∧ lts.trans s₁ l s₁'

/-- 21. LTS map preserves paths between states. -/
def mapLTS_path {S₁ S₂ _L : Type u} (f : S₁ → S₂)
    {s₁ s₂ : S₁} (p : Path s₁ s₂) :
    Path (f s₁) (f s₂) :=
  Path.congrArg f p

/-- 22. LTS map path composition. -/
theorem mapLTS_path_trans {S₁ S₂ L : Type u} (f : S₁ → S₂)
    {s₁ s₂ s₃ : S₁} (p : Path s₁ s₂) (q : Path s₂ s₃) :
    ((mapLTS_path (_L := L) f p).trans (mapLTS_path (_L := L) f q)).toEq =
      (mapLTS_path (_L := L) f (p.trans q)).toEq := by
  cases p with | mk sp ep => cases q with | mk sq eq1 =>
  cases ep; cases eq1; rfl

/-- 23. Transport in LTS pair along path. -/
theorem pairPath_transport {S₁ S₂ : Type u} (D : LTSPair S₁ S₂ → Type u)
    {a₁ a₂ : S₁} {b₁ b₂ : S₂}
    (p : Path a₁ a₂) (q : Path b₁ b₂)
    (x : D (LTSPair.mk a₁ b₁)) :
    Path.transport (D := D) (pairPath p q) x =
      Path.transport (D := D)
        (Path.congrArg (fun b => LTSPair.mk a₂ b) q)
        (Path.transport (D := D)
          (Path.congrArg (fun a => LTSPair.mk a b₁) p) x) := by
  cases p with | mk sp ep => cases q with | mk sq eq1 =>
  cases ep; cases eq1; rfl

/-- 24. Congruence: LTSPair from both paths at once. -/
theorem pairPath_congrArg {S₁ S₂ : Type u}
    {a₁ a₂ : S₁} {b₁ b₂ : S₂}
    (ha : a₁ = a₂) (hb : b₁ = b₂) :
    (pairPath (Path.ofEq ha) (Path.ofEq hb)).toEq =
      (show LTSPair.mk a₁ b₁ = LTSPair.mk a₂ b₂ from by rw [ha, hb]) := by
  cases ha; cases hb; rfl

/-- 25. LTS pair path decomposition. -/
theorem pairPath_decompose {S₁ S₂ : Type u}
    {a₁ a₂ : S₁} {b₁ b₂ : S₂}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    (pairPath p q).toEq =
      ((Path.congrArg (fun a => LTSPair.mk a b₁) p).trans
        (Path.congrArg (fun b => LTSPair.mk a₂ b) q)).toEq := by
  cases p with | mk sp ep => cases q with | mk sq eq1 =>
  cases ep; cases eq1; rfl

end TransitionSystemPaths
end Computation
end Path
end ComputationalPaths

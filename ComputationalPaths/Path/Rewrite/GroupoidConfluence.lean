/-
# Confluence of the Completed Groupoid TRS

Proved via semantic interpretation into the free group on atoms.

No `Step.canon`, no `toEq`, no UIP.
-/

import ComputationalPaths.Path.Rewrite.GroupoidTRS
import ComputationalPaths.Path.Rewrite.NewmanLemma

namespace ComputationalPaths.Path.Rewrite.GroupoidConfluence

open GroupoidTRS

/-! ## CStep -/

inductive CStep : Expr → Expr → Prop where
  | symm_refl : CStep (.symm .refl) .refl
  | symm_symm (p : Expr) : CStep (.symm (.symm p)) p
  | trans_refl_left (p : Expr) : CStep (.trans .refl p) p
  | trans_refl_right (p : Expr) : CStep (.trans p .refl) p
  | trans_symm (p : Expr) : CStep (.trans p (.symm p)) .refl
  | symm_trans (p : Expr) : CStep (.trans (.symm p) p) .refl
  | symm_trans_congr (p q : Expr) :
      CStep (.symm (.trans p q)) (.trans (.symm q) (.symm p))
  | trans_assoc (p q r : Expr) :
      CStep (.trans (.trans p q) r) (.trans p (.trans q r))
  | trans_cancel_left (p q : Expr) :
      CStep (.trans p (.trans (.symm p) q)) q
  | trans_cancel_right (p q : Expr) :
      CStep (.trans (.symm p) (.trans p q)) q
  | symm_congr {p q : Expr} : CStep p q → CStep (.symm p) (.symm q)
  | trans_congr_left {p q : Expr} (r : Expr) :
      CStep p q → CStep (.trans p r) (.trans q r)
  | trans_congr_right (p : Expr) {q r : Expr} :
      CStep q r → CStep (.trans p q) (.trans p r)

/-! ## CRTC -/

abbrev CRTC := GroupoidTRS.RTC CStep

namespace CRTC
def single {a b : Expr} (h : CStep a b) : CRTC a b := RTC.single h

def symm_congr {p q : Expr} (h : CRTC p q) : CRTC (.symm p) (.symm q) := by
  induction h with
  | refl => exact .refl _
  | head s _ ih => exact .head (.symm_congr s) ih

def trans_congr_left (r : Expr) {p q : Expr} (h : CRTC p q) :
    CRTC (.trans p r) (.trans q r) := by
  induction h with
  | refl => exact .refl _
  | head s _ ih => exact .head (.trans_congr_left r s) ih

def trans_congr_right (p : Expr) {q r : Expr} (h : CRTC q r) :
    CRTC (.trans p q) (.trans p r) := by
  induction h with
  | refl => exact .refl _
  | head s _ ih => exact .head (.trans_congr_right p s) ih

def trans_congr {p p' q q' : Expr} (h₁ : CRTC p p') (h₂ : CRTC q q') :
    CRTC (.trans p q) (.trans p' q') :=
  (trans_congr_left q h₁).trans (trans_congr_right p' h₂)
end CRTC

/-! ## Termination -/

theorem cstep_weight_eq_imp_size_eq {p q : Expr} (h : CStep p q)
    (hw : q.weight = p.weight) : q.size = p.size := by
  induction h with
  | symm_refl => simp [Expr.weight] at hw
  | trans_refl_left _ => simp [Expr.weight] at hw; omega
  | trans_refl_right _ => simp [Expr.weight] at hw; omega
  | symm_symm p => simp [Expr.weight] at hw; have := Expr.weight_ge_four p; omega
  | trans_symm p => simp [Expr.weight] at hw; have := Expr.weight_ge_four p; omega
  | symm_trans p => simp [Expr.weight] at hw; have := Expr.weight_ge_four p; omega
  | symm_trans_congr _ _ => simp [Expr.weight] at hw; omega
  | trans_assoc _ _ _ => simp [Expr.size]; omega
  | trans_cancel_left p _ => simp [Expr.weight] at hw; have := Expr.weight_ge_four p; omega
  | trans_cancel_right p _ => simp [Expr.weight] at hw; have := Expr.weight_ge_four p; omega
  | symm_congr _ ih => simp [Expr.size, Expr.weight] at hw ⊢; exact ih (by omega)
  | trans_congr_left _ _ ih => simp [Expr.size, Expr.weight] at hw ⊢; exact ih (by omega)
  | trans_congr_right _ _ ih => simp [Expr.size, Expr.weight] at hw ⊢; exact ih (by omega)

theorem cstep_lex_decrease {p q : Expr} (h : CStep p q) :
    q.weight < p.weight ∨ (q.weight = p.weight ∧ q.leftWeight < p.leftWeight) := by
  induction h with
  | symm_refl => left; simp [Expr.weight]
  | symm_symm p => left; simp [Expr.weight]; have := Expr.weight_ge_four p; omega
  | trans_refl_left _ => left; simp [Expr.weight]; omega
  | trans_refl_right _ => left; simp [Expr.weight]; omega
  | trans_symm p => left; simp [Expr.weight]; have := Expr.weight_ge_four p; omega
  | symm_trans p => left; simp [Expr.weight]; have := Expr.weight_ge_four p; omega
  | symm_trans_congr _ _ => left; simp [Expr.weight]; omega
  | trans_assoc p _ _ =>
    right; exact ⟨by simp [Expr.weight]; omega,
      by simp [Expr.leftWeight]; have := Expr.size_pos p; omega⟩
  | trans_cancel_left p _ =>
    left; simp [Expr.weight]; have := Expr.weight_ge_four p; omega
  | trans_cancel_right p _ =>
    left; simp [Expr.weight]; have := Expr.weight_ge_four p; omega
  | symm_congr _ ih =>
    rcases ih with hw | ⟨hw, hl⟩
    · left; simp [Expr.weight]; omega
    · right; exact ⟨by simp [Expr.weight]; omega, by simp [Expr.leftWeight]; omega⟩
  | trans_congr_left r h ih =>
    rcases ih with hw | ⟨hw, hl⟩
    · left; simp [Expr.weight]; omega
    · right; exact ⟨by simp [Expr.weight]; omega,
        by simp [Expr.leftWeight]; have := cstep_weight_eq_imp_size_eq h hw; omega⟩
  | trans_congr_right p _ ih =>
    rcases ih with hw | ⟨hw, hl⟩
    · left; simp [Expr.weight]; omega
    · right; exact ⟨by simp [Expr.weight]; omega, by simp [Expr.leftWeight]; omega⟩

private theorem natLex_wf : WellFounded (fun (a b : Nat × Nat) =>
    a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)) := by
  constructor; intro ⟨w, l⟩; revert l
  induction w using Nat.strongRecOn with
  | _ w ihw => intro l; induction l using Nat.strongRecOn with
    | _ l ihl => exact ⟨_, fun ⟨w', l'⟩ h => by
        rcases h with hw | ⟨heq, hl⟩
        · exact ihw w' hw l'
        · cases heq; exact ihl l' hl⟩

theorem cstep_termination : WellFounded (fun q p : Expr => CStep p q) :=
  Subrelation.wf (fun h => cstep_lex_decrease h)
    (InvImage.wf (fun (e : Expr) => (e.weight, e.leftWeight)) natLex_wf)

/-! ## Free Group Word Algebra -/

inductive Gen where
  | pos : Nat → Gen
  | neg : Nat → Gen
  deriving DecidableEq

namespace Gen
def inv : Gen → Gen | .pos n => .neg n | .neg n => .pos n
@[simp] theorem inv_inv (g : Gen) : g.inv.inv = g := by cases g <;> rfl
theorem inv_ne (g : Gen) : g.inv ≠ g := by cases g <;> simp [inv]
def toExpr : Gen → Expr | .pos n => .atom n | .neg n => .symm (.atom n)
end Gen

/-- No adjacent inverse pair. -/
def Reduced : List Gen → Prop
  | [] | [_] => True
  | g :: h :: rest => g.inv ≠ h ∧ Reduced (h :: rest)

theorem reduced_tail {g : Gen} {w : List Gen} (h : Reduced (g :: w)) :
    Reduced w := by cases w with | nil => trivial | cons _ _ => exact h.2

/-- Prepend with cancellation. -/
def prepend (g : Gen) : List Gen → List Gen
  | [] => [g]
  | h :: rest => if g.inv = h then rest else g :: h :: rest

theorem prepend_cancel (g : Gen) (rest : List Gen) :
    prepend g (g.inv :: rest) = rest := by simp [prepend]

theorem prepend_no_cancel (g h : Gen) (rest : List Gen) (hne : g.inv ≠ h) :
    prepend g (h :: rest) = g :: h :: rest := by simp [prepend, hne]

theorem prepend_reduced (g : Gen) (w : List Gen) (hw : Reduced w) :
    Reduced (prepend g w) := by
  cases w with
  | nil => trivial
  | cons h rest =>
    simp only [prepend]
    split
    · exact reduced_tail hw
    · exact ⟨by assumption, hw⟩

theorem prepend_inv_cancel (g : Gen) (w : List Gen) (hw : Reduced w) :
    prepend g (prepend g.inv w) = w := by
  cases w with
  | nil =>
    simp [prepend]
  | cons k rest =>
    by_cases hk : g.inv.inv = k
    · -- g.inv.inv = k, i.e., g = k
      have hgk : g = k := by rw [← Gen.inv_inv g]; exact hk
      subst hgk
      -- prepend g.inv (g :: rest): need to check g.inv.inv = g
      -- Since g.inv.inv = g, the check succeeds → result is rest
      have h1 : prepend g.inv (g :: rest) = rest := by
        simp [prepend, Gen.inv_inv]
      rw [h1]
      -- Now need: prepend g rest = g :: rest
      cases rest with
      | nil => simp [prepend]
      | cons h' rest' =>
        exact prepend_no_cancel g h' rest' hw.1
    · -- g.inv.inv ≠ k, i.e., g ≠ k
      -- prepend is: prepend g' (h :: rest) checks g'.inv = h
      -- Here g' = g.inv, so checks g.inv.inv = k. Since hk says it's not equal, no cancel.
      have h1' : prepend g.inv (k :: rest) = g.inv :: k :: rest :=
        prepend_no_cancel g.inv k rest hk
      rw [h1', prepend_cancel g (k :: rest)]

/-- Concatenation with cancellation at junction. -/
def rwAppend : List Gen → List Gen → List Gen
  | [], w₂ => w₂
  | g :: rest, w₂ => prepend g (rwAppend rest w₂)

@[simp] theorem rwAppend_nil_l (w : List Gen) : rwAppend [] w = w := rfl
theorem rwAppend_nil_r (w : List Gen) (hw : Reduced w) : rwAppend w [] = w := by
  induction w with
  | nil => rfl
  | cons g rest ih =>
    simp only [rwAppend, ih (reduced_tail hw)]
    cases rest with
    | nil => simp [prepend]
    | cons h rest' =>
      exact prepend_no_cancel g h rest' hw.1

theorem rwAppend_cons (g : Gen) (rest w₂ : List Gen) :
    rwAppend (g :: rest) w₂ = prepend g (rwAppend rest w₂) := rfl

theorem rwAppend_reduced (w₁ w₂ : List Gen)
    (h₁ : Reduced w₁) (h₂ : Reduced w₂) :
    Reduced (rwAppend w₁ w₂) := by
  induction w₁ with
  | nil => exact h₂
  | cons g rest ih => exact prepend_reduced _ _ (ih (reduced_tail h₁))

theorem rwAppend_prepend (g : Gen) (w c : List Gen)
    (hw : Reduced w) (_hc : Reduced c) :
    rwAppend (prepend g w) c = prepend g (rwAppend w c) := by
  cases w with
  | nil => simp [prepend, rwAppend]
  | cons h rest =>
    by_cases heq : g.inv = h
    · subst heq
      rw [prepend_cancel]
      rw [rwAppend_cons]
      exact (prepend_inv_cancel g _ (rwAppend_reduced _ _ (reduced_tail hw) _hc)).symm
    · rw [prepend_no_cancel _ _ _ heq]
      rfl

theorem rwAppend_assoc (a b c : List Gen)
    (ha : Reduced a) (hb : Reduced b) (hc : Reduced c) :
    rwAppend (rwAppend a b) c = rwAppend a (rwAppend b c) := by
  induction a with
  | nil => rfl
  | cons g rest ih =>
    simp only [rwAppend]
    rw [rwAppend_prepend g _ c (rwAppend_reduced _ _ (reduced_tail ha) hb) hc,
        ih (reduced_tail ha)]

theorem rwAppend_single (g : Gen) (w : List Gen) :
    rwAppend [g] w = prepend g w := rfl

/-- Inversion. -/
def rwInv : List Gen → List Gen
  | [] => []
  | g :: rest => rwAppend (rwInv rest) [g.inv]

@[simp] theorem rwInv_nil : rwInv [] = [] := rfl
theorem rwInv_single (g : Gen) : rwInv [g] = [g.inv] := rfl

theorem rwInv_reduced (w : List Gen) (hw : Reduced w) :
    Reduced (rwInv w) := by
  induction w with
  | nil => trivial
  | cons g rest ih => exact rwAppend_reduced _ _ (ih (reduced_tail hw)) trivial

theorem rwInv_prepend (g : Gen) (w : List Gen) (hw : Reduced w) :
    rwInv (prepend g w) = rwAppend (rwInv w) [g.inv] := by
  cases w with
  | nil => simp [prepend, rwInv]
  | cons h rest =>
    by_cases heq : g.inv = h
    · subst heq
      rw [prepend_cancel]
      simp only [rwInv, Gen.inv_inv]
      rw [rwAppend_assoc (rwInv rest) [g] [g.inv]
            (rwInv_reduced _ (reduced_tail hw)) trivial trivial]
      have hc : rwAppend [g] [g.inv] = [] := by simp [rwAppend, prepend]
      rw [hc, rwAppend_nil_r _ (rwInv_reduced _ (reduced_tail hw))]
    · rw [prepend_no_cancel _ _ _ heq]
      rfl

theorem rwAppend_rwInv (w : List Gen) (hw : Reduced w) :
    rwAppend w (rwInv w) = [] := by
  induction w with
  | nil => rfl
  | cons g rest ih =>
    simp only [rwAppend, rwInv]
    rw [← rwAppend_assoc rest (rwInv rest) [g.inv]
          (reduced_tail hw) (rwInv_reduced _ (reduced_tail hw)) trivial]
    rw [ih (reduced_tail hw)]
    -- Goal: prepend g [g.inv] = []
    simp [prepend]

theorem rwInv_rwAppend_self (w : List Gen) (hw : Reduced w) :
    rwAppend (rwInv w) w = [] := by
  induction w with
  | nil => rfl
  | cons g rest ih =>
    simp only [rwInv]
    rw [rwAppend_assoc (rwInv rest) [g.inv] (g :: rest)
          (rwInv_reduced _ (reduced_tail hw)) trivial hw]
    simp only [rwAppend_single]
    -- Goal: rwAppend (rwInv rest) (prepend g.inv (g :: rest)) = []
    -- prepend g.inv (g :: rest) = rest since g.inv.inv = g
    have h1 : prepend g.inv (g :: rest) = rest := by simp [prepend, Gen.inv_inv]
    rw [h1]
    exact ih (reduced_tail hw)

theorem rwInv_dist (w₁ w₂ : List Gen)
    (h₁ : Reduced w₁) (h₂ : Reduced w₂) :
    rwInv (rwAppend w₁ w₂) = rwAppend (rwInv w₂) (rwInv w₁) := by
  induction w₁ with
  | nil => simp [rwAppend, rwInv]; exact (rwAppend_nil_r _ (rwInv_reduced _ h₂)).symm
  | cons g rest ih =>
    simp only [rwAppend]
    rw [rwInv_prepend g _ (rwAppend_reduced _ _ (reduced_tail h₁) h₂)]
    rw [ih (reduced_tail h₁)]
    rw [rwAppend_assoc (rwInv w₂) (rwInv rest) [g.inv]
          (rwInv_reduced _ h₂) (rwInv_reduced _ (reduced_tail h₁)) trivial]
    rfl

theorem rwInv_rwInv (w : List Gen) (hw : Reduced w) :
    rwInv (rwInv w) = w := by
  induction w with
  | nil => rfl
  | cons g rest ih =>
    simp only [rwInv]
    rw [rwInv_dist (rwInv rest) [g.inv]
          (rwInv_reduced _ (reduced_tail hw)) trivial]
    simp [rwInv, Gen.inv_inv, rwAppend]
    rw [ih (reduced_tail hw)]
    cases rest with
    | nil => simp [prepend]
    | cons h rest' =>
      have hne : g.inv ≠ h := hw.1
      simp [prepend, hne]

/-! ### Derived cancellation properties -/

theorem rwAppend_cancel_left (w₁ w₂ : List Gen)
    (h₁ : Reduced w₁) (h₂ : Reduced w₂) :
    rwAppend w₁ (rwAppend (rwInv w₁) w₂) = w₂ := by
  rw [← rwAppend_assoc w₁ (rwInv w₁) w₂ h₁ (rwInv_reduced _ h₁) h₂]
  rw [rwAppend_rwInv w₁ h₁]; rfl

theorem rwAppend_cancel_right (w₁ w₂ : List Gen)
    (h₁ : Reduced w₁) (h₂ : Reduced w₂) :
    rwAppend (rwInv w₁) (rwAppend w₁ w₂) = w₂ := by
  rw [← rwAppend_assoc (rwInv w₁) w₁ w₂ (rwInv_reduced _ h₁) h₁ h₂]
  rw [rwInv_rwAppend_self w₁ h₁]; rfl

/-! ## Interpretation: Expr → Reduced Word -/

def toRW : Expr → List Gen
  | .atom n => [.pos n]
  | .refl => []
  | .symm e => rwInv (toRW e)
  | .trans e₁ e₂ => rwAppend (toRW e₁) (toRW e₂)

theorem toRW_reduced : ∀ (e : Expr), Reduced (toRW e)
  | .atom _ => trivial
  | .refl => trivial
  | .symm e => rwInv_reduced _ (toRW_reduced e)
  | .trans e₁ e₂ => rwAppend_reduced _ _ (toRW_reduced e₁) (toRW_reduced e₂)

/-! ### Invariance: CStep preserves toRW -/

theorem toRW_invariant {e₁ e₂ : Expr} (h : CStep e₁ e₂) :
    toRW e₁ = toRW e₂ := by
  induction h with
  | symm_refl => rfl
  | symm_symm p => simp [toRW]; exact rwInv_rwInv _ (toRW_reduced p)
  | trans_refl_left p => simp [toRW]
  | trans_refl_right p => simp [toRW]; exact rwAppend_nil_r _ (toRW_reduced p)
  | trans_symm p => simp [toRW]; exact rwAppend_rwInv _ (toRW_reduced p)
  | symm_trans p => simp [toRW]; exact rwInv_rwAppend_self _ (toRW_reduced p)
  | symm_trans_congr p q =>
    simp [toRW]
    exact rwInv_dist (toRW p) (toRW q) (toRW_reduced p) (toRW_reduced q)
  | trans_assoc p q r =>
    simp [toRW]
    exact rwAppend_assoc _ _ _ (toRW_reduced p) (toRW_reduced q) (toRW_reduced r)
  | trans_cancel_left p q =>
    simp [toRW]
    exact rwAppend_cancel_left _ _ (toRW_reduced p) (toRW_reduced q)
  | trans_cancel_right p q =>
    simp [toRW]
    exact rwAppend_cancel_right _ _ (toRW_reduced p) (toRW_reduced q)
  | symm_congr _ ih => simp [toRW, ih]
  | trans_congr_left _ _ ih => simp [toRW, ih]
  | trans_congr_right _ _ ih => simp [toRW, ih]

theorem toRW_invariant_rtc {e₁ e₂ : Expr} (h : CRTC e₁ e₂) :
    toRW e₁ = toRW e₂ := by
  induction h with
  | refl => rfl
  | head s _ ih => rw [toRW_invariant s, ih]

/-! ## Reachability: every Expr CStep-reduces to its canonical form -/

/-- Convert a reduced word to an Expr. -/
def rwToExpr : List Gen → Expr
  | [] => .refl
  | [g] => g.toExpr
  | g :: h :: rest => .trans g.toExpr (rwToExpr (h :: rest))

/-- The canonical form. -/
def canon (e : Expr) : Expr := rwToExpr (toRW e)

/-- Cancel g with g.inv at the head. -/
theorem reach_cancel (g : Gen) (rest : List Gen) (_hr : Reduced rest) :
    CRTC (.trans g.toExpr (rwToExpr (g.inv :: rest))) (rwToExpr rest) := by
  cases rest with
  | nil =>
    -- trans g.toExpr (g.inv.toExpr) → refl
    cases g with
    | pos n => exact RTC.single (.trans_symm _)
    | neg n => exact RTC.single (.symm_trans _)
  | cons h rest' =>
    -- trans g.toExpr (trans g.inv.toExpr (rwToExpr ...))
    cases g with
    | pos n => exact RTC.single (.trans_cancel_left (.atom n) _)
    | neg n => exact RTC.single (.trans_cancel_right (.atom n) _)

/-- Prepend a generator to a canonical form. -/
theorem reach_prepend (g : Gen) (w : List Gen) (hw : Reduced w) :
    CRTC (.trans g.toExpr (rwToExpr w)) (rwToExpr (prepend g w)) := by
  cases w with
  | nil =>
    -- trans g.toExpr refl → g.toExpr = rwToExpr [g]
    exact RTC.single (.trans_refl_right _)
  | cons h rest =>
    by_cases heq : g.inv = h
    · subst heq
      -- prepend g (g.inv :: rest) = rest
      rw [prepend_cancel]
      exact reach_cancel g rest (reduced_tail hw)
    · rw [prepend_no_cancel _ _ _ heq]
      -- trans g.toExpr (rwToExpr (h :: rest)) = rwToExpr (g :: h :: rest)
      exact .refl _

/-- trans of two canonical forms reduces to the canonical form of the concatenation. -/
theorem reach_append (w₁ w₂ : List Gen) (hw₁ : Reduced w₁) (hw₂ : Reduced w₂) :
    CRTC (.trans (rwToExpr w₁) (rwToExpr w₂)) (rwToExpr (rwAppend w₁ w₂)) := by
  induction w₁ with
  | nil => exact RTC.single (.trans_refl_left _)
  | cons g rest ih =>
    cases rest with
    | nil =>
      -- w₁ = [g], so trans g.toExpr (rwToExpr w₂)
      exact reach_prepend g w₂ hw₂
    | cons h rest' =>
      -- w₁ = g :: h :: rest'
      -- trans (trans g.toExpr (rwToExpr (h :: rest'))) (rwToExpr w₂)
      -- → trans g.toExpr (trans (rwToExpr (h :: rest')) (rwToExpr w₂))  [trans_assoc]
      -- →* trans g.toExpr (rwToExpr (rwAppend (h :: rest') w₂))  [IH]
      -- →* rwToExpr (prepend g (rwAppend (h :: rest') w₂))  [reach_prepend]
      -- = rwToExpr (rwAppend (g :: h :: rest') w₂)  [by def]
      have hw₁' : Reduced (h :: rest') := reduced_tail hw₁
      have s1 : CStep (.trans (.trans g.toExpr (rwToExpr (h :: rest'))) (rwToExpr w₂))
                       (.trans g.toExpr (.trans (rwToExpr (h :: rest')) (rwToExpr w₂))) :=
        .trans_assoc _ _ _
      have s2 := CRTC.trans_congr_right g.toExpr (ih hw₁')
      have s3 := reach_prepend g (rwAppend (h :: rest') w₂)
                   (rwAppend_reduced _ _ hw₁' hw₂)
      exact (RTC.single s1).trans (s2.trans s3)

/-- symm of a canonical form reduces to the canonical form of the inverse. -/
theorem reach_symm (w : List Gen) (hw : Reduced w) :
    CRTC (.symm (rwToExpr w)) (rwToExpr (rwInv w)) := by
  induction w with
  | nil => exact RTC.single .symm_refl
  | cons g rest ih =>
    cases rest with
    | nil =>
      -- symm g.toExpr: need to reach rwToExpr [g.inv]
      cases g with
      | pos _ => exact .refl _  -- symm (atom n) is already the expr for neg n
      | neg n => exact RTC.single (.symm_symm _)  -- symm (symm (atom n)) → atom n
    | cons h rest' =>
      -- w = g :: h :: rest', so rwToExpr w = trans g.toExpr (rwToExpr (h :: rest'))
      -- rwInv w = rwAppend (rwInv (h :: rest')) [g.inv]
      -- symm (trans g.toExpr (rwToExpr (h :: rest')))
      -- → trans (symm (rwToExpr (h :: rest'))) (symm g.toExpr)  [symm_trans_congr]
      -- →* trans (rwToExpr (rwInv (h :: rest'))) (symm g.toExpr)  [IH on rest]
      -- → trans (rwToExpr (rwInv (h :: rest'))) (rwToExpr [g.inv])  [single symm step]
      -- →* rwToExpr (rwAppend (rwInv (h :: rest')) [g.inv])  [reach_append]
      -- = rwToExpr (rwInv w)  [by def]
      have hw' : Reduced (h :: rest') := reduced_tail hw
      have s1 : CStep (.symm (.trans g.toExpr (rwToExpr (h :: rest'))))
                       (.trans (.symm (rwToExpr (h :: rest'))) (.symm g.toExpr)) :=
        .symm_trans_congr _ _
      have ih_rest := ih hw'
      have ih_g : CRTC (.symm g.toExpr) (rwToExpr [g.inv]) := by
        cases g with
        | pos _ => exact .refl _
        | neg n => exact RTC.single (.symm_symm _)
      have s2 := CRTC.trans_congr ih_rest ih_g
      have s3 := reach_append (rwInv (h :: rest')) [g.inv]
                   (rwInv_reduced _ hw') trivial
      exact (RTC.single s1).trans (s2.trans s3)

/-- Every expression CStep-reduces to its canonical form. -/
theorem reach_canon (e : Expr) : CRTC e (canon e) := by
  induction e with
  | atom _ => exact .refl _
  | refl => exact .refl _
  | symm e ih =>
    exact (CRTC.symm_congr ih).trans (reach_symm (toRW e) (toRW_reduced e))
  | trans e₁ e₂ ih₁ ih₂ =>
    exact (CRTC.trans_congr ih₁ ih₂).trans
      (reach_append (toRW e₁) (toRW e₂) (toRW_reduced e₁) (toRW_reduced e₂))

/-! ## Main Confluence Theorem -/

/-- **Confluence of the completed groupoid TRS.**

For any expression `a` and CStep-reductions `a →* b` and `a →* c`,
there exists `d` with `b →* d` and `c →* d`.

Proof: `toRW` is invariant under CStep, so `toRW b = toRW a = toRW c`.
Both `b` and `c` reduce to `canon b = rwToExpr (toRW b) = rwToExpr (toRW c) = canon c`. -/
theorem confluence (a b c : Expr)
    (hab : CRTC a b) (hac : CRTC a c) :
    ∃ d, CRTC b d ∧ CRTC c d := by
  have hb : toRW a = toRW b := toRW_invariant_rtc hab
  have hc : toRW a = toRW c := toRW_invariant_rtc hac
  have heq : toRW b = toRW c := by rw [← hb, hc]
  have : canon b = canon c := by unfold canon; rw [heq]
  exact ⟨canon b, reach_canon b, this ▸ reach_canon c⟩

/-- Local confluence as a corollary. -/
theorem local_confluence (a b c : Expr)
    (hab : CStep a b) (hac : CStep a c) :
    ∃ d, CRTC b d ∧ CRTC c d :=
  confluence a b c (RTC.single hab) (RTC.single hac)

end ComputationalPaths.Path.Rewrite.GroupoidConfluence

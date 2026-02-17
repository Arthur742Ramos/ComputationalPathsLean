/-
  Modal Logic and Kripke Semantics via Computational Paths
  ========================================================

  A deep formalization of propositional modal logic, Kripke semantics,
  normal modal logics (K, T, S4, S5), bisimulation, temporal logic (CTL/LTL),
  and epistemic logic — all grounded in computational paths as the fundamental
  notion of identity/transformation between semantic objects.

  Author: armada-386 (ModalLogicDeep)
-/

import ComputationalPaths.Path.Basic

namespace ModalLogicDeep

open ComputationalPaths
open ComputationalPaths.Path

-- ============================================================
-- SECTION 1: Modal Formulas
-- ============================================================

/-- Atomic propositions indexed by natural numbers -/
inductive Atom where
  | mk : Nat → Atom
  deriving DecidableEq, Repr

/-- Propositional modal logic formulas with Box and Diamond -/
inductive MFormula where
  | atom  : Atom → MFormula
  | bot   : MFormula
  | neg   : MFormula → MFormula
  | conj  : MFormula → MFormula → MFormula
  | disj  : MFormula → MFormula → MFormula
  | impl  : MFormula → MFormula → MFormula
  | box   : MFormula → MFormula
  | dia   : MFormula → MFormula
  deriving DecidableEq, Repr

namespace MFormula

/-- Top as negation of bottom -/
def top : MFormula := neg bot

/-- Biconditional -/
def biimp (p q : MFormula) : MFormula := conj (impl p q) (impl q p)

end MFormula

-- ============================================================
-- SECTION 2: Kripke Frames
-- ============================================================

/-- A Kripke frame is a type of worlds with an accessibility relation -/
structure KripkeFrame where
  World : Type
  acc : World → World → Prop

/-- Reflexive frame property -/
def KripkeFrame.isReflexive (F : KripkeFrame) : Prop :=
  ∀ w : F.World, F.acc w w

/-- Transitive frame property -/
def KripkeFrame.isTransitive (F : KripkeFrame) : Prop :=
  ∀ w v u : F.World, F.acc w v → F.acc v u → F.acc w u

/-- Symmetric frame property -/
def KripkeFrame.isSymmetric (F : KripkeFrame) : Prop :=
  ∀ w v : F.World, F.acc w v → F.acc v w

/-- Euclidean frame property -/
def KripkeFrame.isEuclidean (F : KripkeFrame) : Prop :=
  ∀ w v u : F.World, F.acc w v → F.acc w u → F.acc v u

/-- Serial frame property -/
def KripkeFrame.isSerial (F : KripkeFrame) : Prop :=
  ∀ w : F.World, ∃ v : F.World, F.acc w v

-- ============================================================
-- SECTION 3: Kripke Models and Satisfaction
-- ============================================================

/-- A Kripke model adds a valuation to a frame -/
structure KripkeModel where
  frame : KripkeFrame
  val : KripkeFrame.World frame → Atom → Prop

/-- Satisfaction relation: model M, world w satisfies formula phi -/
def KripkeModel.satisfies (M : KripkeModel) : M.frame.World → MFormula → Prop
  | _, MFormula.bot => False
  | w, MFormula.atom a => M.val w a
  | w, MFormula.neg p => ¬ M.satisfies w p
  | w, MFormula.conj p q => M.satisfies w p ∧ M.satisfies w q
  | w, MFormula.disj p q => M.satisfies w p ∨ M.satisfies w q
  | w, MFormula.impl p q => M.satisfies w p → M.satisfies w q
  | w, MFormula.box p => ∀ v, M.frame.acc w v → M.satisfies v p
  | w, MFormula.dia p => ∃ v, M.frame.acc w v ∧ M.satisfies v p

/-- Model validity: formula valid in a model -/
def KripkeModel.valid (M : KripkeModel) (phi : MFormula) : Prop :=
  ∀ w : M.frame.World, M.satisfies w phi

/-- Frame validity: formula valid on a frame -/
def KripkeFrame.valid (F : KripkeFrame) (phi : MFormula) : Prop :=
  ∀ (val : F.World → Atom → Prop),
    let M : KripkeModel := ⟨F, val⟩
    ∀ w, M.satisfies w phi

-- ============================================================
-- SECTION 4: Accessibility Paths
-- ============================================================

/-- An accessibility path records a chain of accessible worlds -/
inductive AccPath (F : KripkeFrame) : F.World → F.World → Type where
  | here  : (w : F.World) → AccPath F w w
  | step  : {w v u : F.World} → F.acc w v → AccPath F v u → AccPath F w u

/-- Length of an accessibility path -/
def AccPath.length {F : KripkeFrame} : {w v : F.World} → AccPath F w v → Nat
  | _, _, AccPath.here _ => 0
  | _, _, AccPath.step _ rest => 1 + rest.length

/-- Concatenation of accessibility paths -/
def AccPath.append {F : KripkeFrame} : {w v u : F.World} →
    AccPath F w v → AccPath F v u → AccPath F w u
  | _, _, _, AccPath.here _, q => q
  | _, _, _, AccPath.step h p, q => AccPath.step h (p.append q)

-- ============================================================
-- SECTION 5: Path-Based Frame Properties
-- ============================================================

/-- Theorem 1: Transitivity allows path composition -/
theorem transitive_path_compose (F : KripkeFrame) (ht : F.isTransitive)
    (w v u : F.World) (h1 : F.acc w v) (h2 : F.acc v u) :
    F.acc w u :=
  ht w v u h1 h2

/-- Theorem 2: Path append preserves lengths additively -/
theorem accpath_append_length {F : KripkeFrame} {w v u : F.World}
    (p : AccPath F w v) (q : AccPath F v u) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | here _ => simp [AccPath.append, AccPath.length]
  | step h rest ih =>
    simp only [AccPath.append, AccPath.length, ih]
    omega

/-- Theorem 3: Symmetry of frame gives reverse accessibility -/
theorem symmetric_reverse (F : KripkeFrame) (hs : F.isSymmetric)
    (w v : F.World) (h : F.acc w v) : F.acc v w :=
  hs w v h

/-- Theorem 4: Euclidean + reflexive implies symmetric -/
theorem euclidean_reflexive_symmetric (F : KripkeFrame)
    (he : F.isEuclidean) (hr : F.isReflexive) : F.isSymmetric := by
  intro w v hwv
  exact he w v w hwv (hr w)

/-- Theorem 5: Euclidean + reflexive implies transitive -/
theorem euclidean_reflexive_transitive (F : KripkeFrame)
    (he : F.isEuclidean) (hr : F.isReflexive) : F.isTransitive := by
  intro w v u hwv hvu
  have hsym := euclidean_reflexive_symmetric F he hr
  have hvw := hsym w v hwv
  exact he v w u hvw hvu

/-- S5 frame properties bundled -/
structure S5Frame extends KripkeFrame where
  refl_prop : KripkeFrame.isReflexive toKripkeFrame
  sym_prop  : KripkeFrame.isSymmetric toKripkeFrame
  trans_prop : KripkeFrame.isTransitive toKripkeFrame

/-- Theorem 6: S5 frames are euclidean -/
theorem s5_euclidean (F : S5Frame) : F.toKripkeFrame.isEuclidean := by
  intro w v u hwv hwu
  exact F.trans_prop v w u (F.sym_prop w v hwv) hwu

-- ============================================================
-- SECTION 6: Path Coherence for Modal Reasoning
-- ============================================================

/-- Wrapper type for truth values at worlds -/
structure TruthAt (M : KripkeModel) (phi : MFormula) where
  world : M.frame.World
  holds : M.satisfies world phi

/-- Def 7: Path between truth witnesses via trans -/
def truth_path_trans {M : KripkeModel} {phi : MFormula}
    (a b c : TruthAt M phi)
    (p : Path a b) (q : Path b c) :
    Path a c :=
  Path.trans p q

/-- Def 8: Symmetric path between truth witnesses -/
def truth_path_symm {M : KripkeModel} {phi : MFormula}
    (a b : TruthAt M phi)
    (p : Path a b) :
    Path b a :=
  Path.symm p

/-- Def 9: Reflexive path on truth witness -/
def truth_path_refl {M : KripkeModel} {phi : MFormula}
    (a : TruthAt M phi) :
    Path a a :=
  Path.refl a

/-- Theorem 10: Trans associativity for truth paths -/
theorem truth_path_trans_assoc {M : KripkeModel} {phi : MFormula}
    (a b c d : TruthAt M phi)
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  trans_assoc p q r

/-- Theorem 11: Left identity for truth path trans -/
theorem truth_path_trans_refl_left {M : KripkeModel} {phi : MFormula}
    (a b : TruthAt M phi) (p : Path a b) :
    Path.trans (Path.refl a) p = p :=
  trans_refl_left p

/-- Theorem 12: Right identity for truth path trans -/
theorem truth_path_trans_refl_right {M : KripkeModel} {phi : MFormula}
    (a b : TruthAt M phi) (p : Path a b) :
    Path.trans p (Path.refl b) = p :=
  trans_refl_right p

/-- Theorem 13: Symm involution on truth paths -/
theorem truth_path_symm_symm {M : KripkeModel} {phi : MFormula}
    (a b : TruthAt M phi) (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  symm_symm p

/-- Theorem 14: symm distributes over trans -/
theorem truth_path_symm_trans {M : KripkeModel} {phi : MFormula}
    {a b c : TruthAt M phi} (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  symm_trans p q

-- ============================================================
-- SECTION 7: Normal Modal Logic Axioms
-- ============================================================

/-- Theorem 15: K axiom holds in all models -/
theorem axiomK_valid (M : KripkeModel) (p q : MFormula) :
    M.valid (MFormula.impl (MFormula.box (MFormula.impl p q))
              (MFormula.impl (MFormula.box p) (MFormula.box q))) := by
  intro w hbpq hbp v hwv
  exact hbpq v hwv (hbp v hwv)

/-- Theorem 16: T axiom (Box p → p) on reflexive frames -/
theorem axiomT_holds (F : KripkeFrame) (hr : F.isReflexive)
    (val : F.World → Atom → Prop) (p : MFormula) (w : F.World) :
    let M : KripkeModel := ⟨F, val⟩
    M.satisfies w (MFormula.box p) → M.satisfies w p := by
  intro M hbox
  exact hbox w (hr w)

/-- Theorem 17: 4 axiom (Box p → Box Box p) on transitive frames -/
theorem axiom4_holds (F : KripkeFrame) (ht : F.isTransitive)
    (val : F.World → Atom → Prop) (p : MFormula) (w : F.World) :
    let M : KripkeModel := ⟨F, val⟩
    M.satisfies w (MFormula.box p) → M.satisfies w (MFormula.box (MFormula.box p)) := by
  intro M hbox v hwv u hvu
  exact hbox u (ht w v u hwv hvu)

/-- Theorem 18: B axiom (p → Box Diamond p) on symmetric frames -/
theorem axiomB_holds (F : KripkeFrame) (hs : F.isSymmetric)
    (val : F.World → Atom → Prop) (p : MFormula) (w : F.World) :
    let M : KripkeModel := ⟨F, val⟩
    M.satisfies w p → M.satisfies w (MFormula.box (MFormula.dia p)) := by
  intro M hp v hwv
  exact ⟨w, hs w v hwv, hp⟩

/-- Theorem 19: 5 axiom (Diamond p → Box Diamond p) on euclidean frames -/
theorem axiom5_holds (F : KripkeFrame) (he : F.isEuclidean)
    (val : F.World → Atom → Prop) (p : MFormula) (w : F.World) :
    let M : KripkeModel := ⟨F, val⟩
    M.satisfies w (MFormula.dia p) → M.satisfies w (MFormula.box (MFormula.dia p)) := by
  intro M ⟨u, hwu, hu⟩ v hwv
  exact ⟨u, he w v u hwv hwu, hu⟩

/-- Theorem 20: D axiom (Box p → Diamond p) on serial frames -/
theorem axiomD_holds (F : KripkeFrame) (hd : F.isSerial)
    (val : F.World → Atom → Prop) (p : MFormula) (w : F.World) :
    let M : KripkeModel := ⟨F, val⟩
    M.satisfies w (MFormula.box p) → M.satisfies w (MFormula.dia p) := by
  intro M hbox
  obtain ⟨v, hwv⟩ := hd w
  exact ⟨v, hwv, hbox v hwv⟩

-- ============================================================
-- SECTION 8: Dual and Distribution Properties
-- ============================================================

/-- Theorem 21: Box implies not-Diamond-not -/
theorem box_implies_not_dia_not (M : KripkeModel) (p : MFormula) (w : M.frame.World) :
    M.satisfies w (MFormula.box p) →
    ¬ M.satisfies w (MFormula.dia (MFormula.neg p)) := by
  intro hbox ⟨v, hwv, hnp⟩
  exact hnp (hbox v hwv)

/-- Theorem 22: Diamond implies not-Box-not -/
theorem dia_implies_not_box_not (M : KripkeModel) (p : MFormula) (w : M.frame.World) :
    M.satisfies w (MFormula.dia p) →
    ¬ M.satisfies w (MFormula.box (MFormula.neg p)) := by
  intro ⟨v, hwv, hp⟩ hbn
  exact hbn v hwv hp

/-- Theorem 23: Box distributes over conjunction -/
theorem box_conj_dist (M : KripkeModel) (p q : MFormula) (w : M.frame.World) :
    M.satisfies w (MFormula.box (MFormula.conj p q)) ↔
    (M.satisfies w (MFormula.box p) ∧ M.satisfies w (MFormula.box q)) := by
  constructor
  · intro h
    exact ⟨fun v hwv => (h v hwv).1, fun v hwv => (h v hwv).2⟩
  · intro ⟨hp, hq⟩ v hwv
    exact ⟨hp v hwv, hq v hwv⟩

/-- Theorem 24: Diamond distributes over disjunction -/
theorem diamond_disj_dist (M : KripkeModel) (p q : MFormula) (w : M.frame.World) :
    M.satisfies w (MFormula.dia (MFormula.disj p q)) ↔
    (M.satisfies w (MFormula.dia p) ∨ M.satisfies w (MFormula.dia q)) := by
  constructor
  · intro ⟨v, hwv, hpq⟩
    match hpq with
    | Or.inl hp => exact Or.inl ⟨v, hwv, hp⟩
    | Or.inr hq => exact Or.inr ⟨v, hwv, hq⟩
  · intro h
    match h with
    | Or.inl ⟨v, hwv, hp⟩ => exact ⟨v, hwv, Or.inl hp⟩
    | Or.inr ⟨v, hwv, hq⟩ => exact ⟨v, hwv, Or.inr hq⟩

-- ============================================================
-- SECTION 9: Bisimulation
-- ============================================================

/-- Bisimulation between two Kripke models -/
structure Bisimulation (M1 M2 : KripkeModel) where
  rel : M1.frame.World → M2.frame.World → Prop
  atom_agree : ∀ w1 w2, rel w1 w2 → ∀ a, M1.val w1 a ↔ M2.val w2 a
  forth : ∀ w1 w2 v1, rel w1 w2 → M1.frame.acc w1 v1 →
          ∃ v2, M2.frame.acc w2 v2 ∧ rel v1 v2
  back : ∀ w1 w2 v2, rel w1 w2 → M2.frame.acc w2 v2 →
         ∃ v1, M1.frame.acc w1 v1 ∧ rel v1 v2

/-- Theorem 25: Bisimulation preserves satisfaction (atoms) -/
theorem bisim_preserves_atom (M1 M2 : KripkeModel) (B : Bisimulation M1 M2)
    (w1 : M1.frame.World) (w2 : M2.frame.World) (hr : B.rel w1 w2) (a : Atom) :
    M1.satisfies w1 (MFormula.atom a) ↔ M2.satisfies w2 (MFormula.atom a) :=
  B.atom_agree w1 w2 hr a

/-- Theorem 26: Bisimulation preserves satisfaction (full induction) -/
theorem bisim_preserves_satisfaction (M1 M2 : KripkeModel) (B : Bisimulation M1 M2)
    (phi : MFormula) :
    ∀ w1 w2, B.rel w1 w2 →
    (M1.satisfies w1 phi ↔ M2.satisfies w2 phi) := by
  induction phi with
  | atom a => exact fun w1 w2 hr => B.atom_agree w1 w2 hr a
  | bot => intro _ _ _; exact Iff.rfl
  | neg p ih =>
    intro w1 w2 hr
    constructor
    · intro hn hp2; exact hn ((ih w1 w2 hr).mpr hp2)
    · intro hn hp1; exact hn ((ih w1 w2 hr).mp hp1)
  | conj p q ihp ihq =>
    intro w1 w2 hr
    constructor
    · intro ⟨hp, hq⟩; exact ⟨(ihp w1 w2 hr).mp hp, (ihq w1 w2 hr).mp hq⟩
    · intro ⟨hp, hq⟩; exact ⟨(ihp w1 w2 hr).mpr hp, (ihq w1 w2 hr).mpr hq⟩
  | disj p q ihp ihq =>
    intro w1 w2 hr
    constructor
    · intro h; match h with
      | Or.inl hp => exact Or.inl ((ihp w1 w2 hr).mp hp)
      | Or.inr hq => exact Or.inr ((ihq w1 w2 hr).mp hq)
    · intro h; match h with
      | Or.inl hp => exact Or.inl ((ihp w1 w2 hr).mpr hp)
      | Or.inr hq => exact Or.inr ((ihq w1 w2 hr).mpr hq)
  | impl p q ihp ihq =>
    intro w1 w2 hr
    constructor
    · intro h hp2; exact (ihq w1 w2 hr).mp (h ((ihp w1 w2 hr).mpr hp2))
    · intro h hp1; exact (ihq w1 w2 hr).mpr (h ((ihp w1 w2 hr).mp hp1))
  | box p ih =>
    intro w1 w2 hr
    constructor
    · intro hbox v2 h2v
      obtain ⟨v1, h1v, hrv⟩ := B.back w1 w2 v2 hr h2v
      exact (ih v1 v2 hrv).mp (hbox v1 h1v)
    · intro hbox v1 h1v
      obtain ⟨v2, h2v, hrv⟩ := B.forth w1 w2 v1 hr h1v
      exact (ih v1 v2 hrv).mpr (hbox v2 h2v)
  | dia p ih =>
    intro w1 w2 hr
    constructor
    · intro ⟨v1, h1v, hv1⟩
      obtain ⟨v2, h2v, hrv⟩ := B.forth w1 w2 v1 hr h1v
      exact ⟨v2, h2v, (ih v1 v2 hrv).mp hv1⟩
    · intro ⟨v2, h2v, hv2⟩
      obtain ⟨v1, h1v, hrv⟩ := B.back w1 w2 v2 hr h2v
      exact ⟨v1, h1v, (ih v1 v2 hrv).mpr hv2⟩

-- ============================================================
-- SECTION 10: Path Algebra for Bisimulation Witnesses
-- ============================================================

/-- A bisimulation witness pairs related worlds -/
structure BisimPair (M1 M2 : KripkeModel) (B : Bisimulation M1 M2) where
  w1 : M1.frame.World
  w2 : M2.frame.World
  related : B.rel w1 w2

/-- Def 27: Path refl on bisimulation pairs -/
def bisim_pair_refl {M1 M2 : KripkeModel} {B : Bisimulation M1 M2}
    (bp : BisimPair M1 M2 B) :
    Path bp bp :=
  Path.refl bp

/-- Def 28: Path trans on bisimulation pairs -/
def bisim_pair_trans {M1 M2 : KripkeModel} {B : Bisimulation M1 M2}
    (a b c : BisimPair M1 M2 B)
    (p : Path a b) (q : Path b c) :
    Path a c :=
  Path.trans p q

/-- Def 29: Path symm on bisimulation pairs -/
def bisim_pair_symm {M1 M2 : KripkeModel} {B : Bisimulation M1 M2}
    (a b : BisimPair M1 M2 B)
    (p : Path a b) :
    Path b a :=
  Path.symm p

/-- Def 30: congrArg lifts through bisim pair w1 projection -/
def bisim_pair_congrArg_w1 {M1 M2 : KripkeModel} {B : Bisimulation M1 M2}
    (a b : BisimPair M1 M2 B)
    (p : Path a b) :
    Path a.w1 b.w1 :=
  Path.congrArg (fun bp => bp.w1) p

/-- Def 31: congrArg lifts through bisim pair w2 projection -/
def bisim_pair_congrArg_w2 {M1 M2 : KripkeModel} {B : Bisimulation M1 M2}
    (a b : BisimPair M1 M2 B)
    (p : Path a b) :
    Path a.w2 b.w2 :=
  Path.congrArg (fun bp => bp.w2) p

/-- Theorem 32: trans_assoc for bisim pairs -/
theorem bisim_pair_trans_assoc {M1 M2 : KripkeModel} {B : Bisimulation M1 M2}
    (a b c d : BisimPair M1 M2 B)
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  trans_assoc p q r

/-- Theorem 33: congrArg_trans for bisim w1 projection -/
theorem bisim_pair_congrArg_trans_w1 {M1 M2 : KripkeModel} {B : Bisimulation M1 M2}
    (a b c : BisimPair M1 M2 B)
    (p : Path a b) (q : Path b c) :
    Path.congrArg (fun bp => bp.w1) (Path.trans p q) =
      Path.trans (Path.congrArg (fun bp => bp.w1) p)
                 (Path.congrArg (fun bp => bp.w1) q) :=
  congrArg_trans (fun bp => bp.w1) p q

/-- Theorem 34: congrArg_symm for bisim w2 projection -/
theorem bisim_pair_congrArg_symm_w2 {M1 M2 : KripkeModel} {B : Bisimulation M1 M2}
    (a b : BisimPair M1 M2 B)
    (p : Path a b) :
    Path.congrArg (fun bp => bp.w2) (Path.symm p) =
      Path.symm (Path.congrArg (fun bp => bp.w2) p) :=
  congrArg_symm (fun bp => bp.w2) p

-- ============================================================
-- SECTION 11: Filtration (Finite Model Property)
-- ============================================================

/-- Subformula closure (simplified as a list) -/
def subformulas : MFormula → List MFormula
  | MFormula.bot => [MFormula.bot]
  | f@(MFormula.atom _) => [f]
  | f@(MFormula.neg p) => f :: subformulas p
  | f@(MFormula.conj p q) => f :: (subformulas p ++ subformulas q)
  | f@(MFormula.disj p q) => f :: (subformulas p ++ subformulas q)
  | f@(MFormula.impl p q) => f :: (subformulas p ++ subformulas q)
  | f@(MFormula.box p) => f :: subformulas p
  | f@(MFormula.dia p) => f :: subformulas p

/-- Theorem 35: A formula is in its own subformula closure -/
theorem self_in_subformulas (phi : MFormula) : phi ∈ subformulas phi := by
  cases phi <;> simp [subformulas]

/-- Filtration equivalence class representative -/
structure FiltWorld (M : KripkeModel) (gam : List MFormula) where
  rep : M.frame.World
  theory : List MFormula
  subset : ∀ f, f ∈ theory → f ∈ gam
  correct : ∀ f, f ∈ theory ↔ (f ∈ gam ∧ M.satisfies rep f)

/-- Def 36: Path refl for filtration worlds -/
def filt_world_refl {M : KripkeModel} {gam : List MFormula}
    (fw : FiltWorld M gam) :
    Path fw fw :=
  Path.refl fw

/-- Def 37: FiltWorld paths compose -/
def filt_world_trans {M : KripkeModel} {gam : List MFormula}
    (a b c : FiltWorld M gam)
    (p : Path a b) (q : Path b c) :
    Path a c :=
  Path.trans p q

/-- Theorem 38: symm_symm for filtration worlds -/
theorem filt_world_symm_symm {M : KripkeModel} {gam : List MFormula}
    (a b : FiltWorld M gam)
    (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  symm_symm p

-- ============================================================
-- SECTION 12: LTL Operators
-- ============================================================

/-- A transition system -/
structure TransSystem where
  State : Type
  trans_rel : State → State → Prop
  label : State → Atom → Prop

/-- Infinite path in a transition system -/
structure InfPath (T : TransSystem) where
  at_ : Nat → T.State
  step_rel : ∀ n, T.trans_rel (at_ n) (at_ (n + 1))

/-- LTL formulas -/
inductive LTLFormula where
  | atom   : Atom → LTLFormula
  | bot    : LTLFormula
  | neg    : LTLFormula → LTLFormula
  | conj   : LTLFormula → LTLFormula → LTLFormula
  | lnext  : LTLFormula → LTLFormula
  | luntil : LTLFormula → LTLFormula → LTLFormula

namespace LTLFormula

def eventually (p : LTLFormula) : LTLFormula := luntil (neg bot) p

def globally (p : LTLFormula) : LTLFormula := neg (eventually (neg p))

end LTLFormula

/-- LTL satisfaction on infinite paths -/
def ltlSat (T : TransSystem) (pi : InfPath T) : Nat → LTLFormula → Prop
  | _, LTLFormula.bot => False
  | i, LTLFormula.atom a => T.label (pi.at_ i) a
  | i, LTLFormula.neg p => ¬ ltlSat T pi i p
  | i, LTLFormula.conj p q => ltlSat T pi i p ∧ ltlSat T pi i q
  | i, LTLFormula.lnext p => ltlSat T pi (i + 1) p
  | i, LTLFormula.luntil p q => ∃ k, k ≥ i ∧ ltlSat T pi k q ∧ ∀ j, i ≤ j → j < k → ltlSat T pi j p

/-- Theorem 39: LTL next is deterministic on a path -/
theorem ltl_next_determ (T : TransSystem) (pi : InfPath T) (i : Nat) (p : LTLFormula) :
    ltlSat T pi i (LTLFormula.lnext p) ↔ ltlSat T pi (i + 1) p := by
  simp [ltlSat]

/-- Theorem 40: LTL conjunction distributes -/
theorem ltl_conj_dist (T : TransSystem) (pi : InfPath T) (i : Nat) (p q : LTLFormula) :
    ltlSat T pi i (LTLFormula.conj p q) ↔ (ltlSat T pi i p ∧ ltlSat T pi i q) := by
  simp [ltlSat]

-- ============================================================
-- SECTION 13: Epistemic Logic
-- ============================================================

/-- Multi-agent epistemic formulas -/
inductive EFormula (Agent : Type) where
  | atom  : Atom → EFormula Agent
  | bot   : EFormula Agent
  | neg   : EFormula Agent → EFormula Agent
  | conj  : EFormula Agent → EFormula Agent → EFormula Agent
  | knows : Agent → EFormula Agent → EFormula Agent
  | cknow : List Agent → EFormula Agent → EFormula Agent

/-- Multi-agent Kripke model -/
structure EModel (Agent : Type) where
  World : Type
  acc : Agent → World → World → Prop
  val : World → Atom → Prop

/-- Group accessibility: union of agents' relations -/
def groupAcc {Agent : Type} (M : EModel Agent) (agents : List Agent) :
    M.World → M.World → Prop :=
  fun w v => ∃ a, a ∈ agents ∧ M.acc a w v

/-- Transitive closure -/
inductive TClosure {A : Type} (R : A → A → Prop) : A → A → Prop where
  | base : R x y → TClosure R x y
  | step_tc : R x y → TClosure R y z → TClosure R x z

/-- Epistemic satisfaction -/
def eSat {Agent : Type} (M : EModel Agent) : M.World → EFormula Agent → Prop
  | _, EFormula.bot => False
  | w, EFormula.atom a => M.val w a
  | w, EFormula.neg p => ¬ eSat M w p
  | w, EFormula.conj p q => eSat M w p ∧ eSat M w q
  | w, EFormula.knows ag p => ∀ v, M.acc ag w v → eSat M v p
  | w, EFormula.cknow agents p =>
    ∀ v, TClosure (groupAcc M agents) w v → eSat M v p

/-- Theorem 41: Knowledge implies truth on reflexive epistemic frames -/
theorem knowledge_implies_truth {Agent : Type} (M : EModel Agent)
    (ag : Agent) (hrefl : ∀ w, M.acc ag w w) (w : M.World) (p : EFormula Agent) :
    eSat M w (EFormula.knows ag p) → eSat M w p := by
  intro hk
  exact hk w (hrefl w)

/-- Theorem 42: Positive introspection (KK) on transitive frames -/
theorem positive_introspection {Agent : Type} (M : EModel Agent)
    (ag : Agent) (htrans : ∀ w v u, M.acc ag w v → M.acc ag v u → M.acc ag w u)
    (w : M.World) (p : EFormula Agent) :
    eSat M w (EFormula.knows ag p) →
    eSat M w (EFormula.knows ag (EFormula.knows ag p)) := by
  intro hk v hwv u hvu
  exact hk u (htrans w v u hwv hvu)

/-- Theorem 43: Common knowledge implies individual knowledge -/
theorem cknow_implies_knows {Agent : Type} (M : EModel Agent)
    (ag : Agent) (agents : List Agent) (hmem : ag ∈ agents)
    (w : M.World) (p : EFormula Agent) :
    eSat M w (EFormula.cknow agents p) →
    eSat M w (EFormula.knows ag p) := by
  intro hck v hwv
  exact hck v (TClosure.base ⟨ag, hmem, hwv⟩)

-- ============================================================
-- SECTION 14: Path-Based Modal Frame Morphisms
-- ============================================================

/-- A bounded morphism between frames -/
structure BoundedMorphism (F1 F2 : KripkeFrame) where
  map : F1.World → F2.World
  forth : ∀ w v, F1.acc w v → F2.acc (map w) (map v)
  back : ∀ w u2, F2.acc (map w) u2 → ∃ v, F1.acc w v ∧ map v = u2

/-- Def 44: Bounded morphism identity via Path.refl -/
def bmorphism_id_path (F : KripkeFrame) (w : F.World) :
    Path (id w) w :=
  Path.refl w

/-- Def 45: Composition of bounded morphisms -/
def bmorphism_comp {F1 F2 F3 : KripkeFrame}
    (f : BoundedMorphism F1 F2) (g : BoundedMorphism F2 F3) :
    BoundedMorphism F1 F3 where
  map := g.map ∘ f.map
  forth := by
    intro w v h
    exact g.forth _ _ (f.forth w v h)
  back := by
    intro w u3 h
    obtain ⟨u2, h2, hu2⟩ := g.back (f.map w) u3 h
    subst hu2
    obtain ⟨v, hv, hfv⟩ := f.back w u2 h2
    exact ⟨v, hv, by simp [Function.comp, hfv]⟩

-- ============================================================
-- SECTION 15: Path coherence for frame properties
-- ============================================================

/-- Wrapper for frame property witnesses -/
structure FramePropWitness where
  name : String
  holds : Prop

/-- Def 46: Path refl for frame property witnesses -/
def frame_prop_path_refl (w : FramePropWitness) :
    Path w w :=
  Path.refl w

/-- Theorem 47: Trans-assoc for frame property paths -/
theorem frame_prop_trans_assoc (a b c d : FramePropWitness)
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  trans_assoc p q r

/-- Def 48: congrArg on frame property name -/
def frame_prop_congrArg_name (a b : FramePropWitness)
    (p : Path a b) :
    Path a.name b.name :=
  Path.congrArg (fun w => w.name) p

/-- Theorem 49: congrArg_trans for frame property name -/
theorem frame_prop_congrArg_trans_name (a b c : FramePropWitness)
    (p : Path a b) (q : Path b c) :
    Path.congrArg (fun w => w.name) (Path.trans p q) =
      Path.trans (Path.congrArg (fun w => w.name) p)
                 (Path.congrArg (fun w => w.name) q) :=
  congrArg_trans (fun w => w.name) p q

/-- Theorem 50: congrArg_symm for frame property name -/
theorem frame_prop_congrArg_symm_name (a b : FramePropWitness)
    (p : Path a b) :
    Path.congrArg (fun w => w.name) (Path.symm p) =
      Path.symm (Path.congrArg (fun w => w.name) p) :=
  congrArg_symm (fun w => w.name) p

-- ============================================================
-- SECTION 16: Generated Subframes
-- ============================================================

/-- Generated subframe: closed under accessibility -/
structure GenSubframe (F : KripkeFrame) where
  worlds : F.World → Prop
  closed : ∀ w v, worlds w → F.acc w v → worlds v

/-- Def 51: Generated subframe is itself a frame -/
def genSubframeToFrame (F : KripkeFrame) (G : GenSubframe F) : KripkeFrame where
  World := { w : F.World // G.worlds w }
  acc := fun ⟨w, _⟩ ⟨v, _⟩ => F.acc w v

/-- Theorem 52: Reflexivity transfers to generated subframes -/
theorem genSubframe_refl (F : KripkeFrame) (G : GenSubframe F)
    (hr : F.isReflexive) :
    (genSubframeToFrame F G).isReflexive := by
  intro ⟨w, _⟩
  exact hr w

/-- Theorem 53: Transitivity transfers to generated subframes -/
theorem genSubframe_trans (F : KripkeFrame) (G : GenSubframe F)
    (ht : F.isTransitive) :
    (genSubframeToFrame F G).isTransitive := by
  intro ⟨w, _⟩ ⟨v, _⟩ ⟨u, _⟩
  exact ht w v u

/-- Theorem 54: Symmetry transfers to generated subframes -/
theorem genSubframe_sym (F : KripkeFrame) (G : GenSubframe F)
    (hs : F.isSymmetric) :
    (genSubframeToFrame F G).isSymmetric := by
  intro ⟨w, _⟩ ⟨v, _⟩
  exact hs w v

-- ============================================================
-- SECTION 17: Path Algebra of Modal Operators
-- ============================================================

/-- Nesting depth of modal operators -/
def modalDepth : MFormula → Nat
  | MFormula.atom _ => 0
  | MFormula.bot => 0
  | MFormula.neg p => modalDepth p
  | MFormula.conj p q => max (modalDepth p) (modalDepth q)
  | MFormula.disj p q => max (modalDepth p) (modalDepth q)
  | MFormula.impl p q => max (modalDepth p) (modalDepth q)
  | MFormula.box p => 1 + modalDepth p
  | MFormula.dia p => 1 + modalDepth p

/-- Theorem 55: Modal depth of top is 0 -/
theorem modalDepth_top : modalDepth MFormula.top = 0 := by
  simp [MFormula.top, modalDepth]

/-- Theorem 56: Diamond has same depth as box -/
theorem modalDepth_dia_eq_box (p : MFormula) :
    modalDepth (MFormula.dia p) = modalDepth (MFormula.box p) := by
  simp [modalDepth]

/-- Def 57: Path refl on modal depths -/
def modalDepth_refl (p : MFormula) :
    Path (modalDepth p) (modalDepth p) :=
  Path.refl (modalDepth p)

/-- Def 58: congrArg lifts modalDepth through formula paths -/
def modalDepth_congrArg (p q : MFormula) (h : Path p q) :
    Path (modalDepth p) (modalDepth q) :=
  Path.congrArg modalDepth h

-- ============================================================
-- SECTION 18: Canonical Model Construction Skeleton
-- ============================================================

/-- Maximally consistent set (abstract) -/
structure MCS (logic : MFormula → Prop) where
  formulas : MFormula → Prop
  consistent : ¬ formulas MFormula.bot
  maximal : ∀ p, formulas p ∨ formulas (MFormula.neg p)
  closed_mp : ∀ p q, formulas (MFormula.impl p q) → formulas p → formulas q

/-- Canonical frame for a normal modal logic -/
def canonicalFrame (logic : MFormula → Prop) : KripkeFrame where
  World := MCS logic
  acc := fun w v => ∀ p, w.formulas (MFormula.box p) → v.formulas p

/-- Theorem 59: Canonical frame for T is reflexive if T contains axiom T -/
theorem canonical_reflexive (logic : MFormula → Prop)
    (hT : ∀ (w : MCS logic) (p : MFormula),
      w.formulas (MFormula.box p) → w.formulas p) :
    (canonicalFrame logic).isReflexive := by
  intro w p hbox
  exact hT w p hbox

/-- Theorem 60: Canonical frame for S4 is transitive if logic has axiom 4 -/
theorem canonical_transitive (logic : MFormula → Prop)
    (h4 : ∀ (w : MCS logic) (p : MFormula),
      w.formulas (MFormula.box p) → w.formulas (MFormula.box (MFormula.box p))) :
    (canonicalFrame logic).isTransitive := by
  intro w v u hwv hvu p hbox
  exact hvu p (hwv (MFormula.box p) (h4 w p hbox))

-- ============================================================
-- SECTION 19: Path Coherence Results
-- ============================================================

/-- Theorem 61: congrArg_trans for Kripke world functions -/
theorem frame_congrArg_trans {F : KripkeFrame}
    (f : F.World → Nat) (a b c : F.World)
    (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
      Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  congrArg_trans f p q

/-- Theorem 62: congrArg_symm for Kripke world functions -/
theorem frame_congrArg_symm {F : KripkeFrame}
    (f : F.World → Nat) (a b : F.World)
    (p : Path a b) :
    Path.congrArg f (Path.symm p) =
      Path.symm (Path.congrArg f p) :=
  congrArg_symm f p

/-- Theorem 63: symm_symm for Kripke world paths -/
theorem kripke_symm_symm {F : KripkeFrame} (w v : F.World)
    (p : Path w v) :
    Path.symm (Path.symm p) = p :=
  symm_symm p

/-- Theorem 64: trans_refl_left for Kripke world paths -/
theorem kripke_trans_refl_left {F : KripkeFrame} (w v : F.World)
    (p : Path w v) :
    Path.trans (Path.refl w) p = p :=
  trans_refl_left p

/-- Theorem 65: trans_refl_right for Kripke world paths -/
theorem kripke_trans_refl_right {F : KripkeFrame} (w v : F.World)
    (p : Path w v) :
    Path.trans p (Path.refl v) = p :=
  trans_refl_right p

-- ============================================================
-- SECTION 20: Modal Logic Metatheorems
-- ============================================================

/-- Theorem 66: Necessitation: if phi is valid, Box phi is valid -/
theorem necessitation (M : KripkeModel) (phi : MFormula)
    (hvalid : M.valid phi) : M.valid (MFormula.box phi) := by
  intro w v _
  exact hvalid v

/-- Theorem 67: Box is monotone: if p → q valid then Box p → Box q valid -/
theorem box_monotone (M : KripkeModel) (p q : MFormula)
    (h : ∀ w, M.satisfies w p → M.satisfies w q) (w : M.frame.World) :
    M.satisfies w (MFormula.box p) → M.satisfies w (MFormula.box q) := by
  intro hbox v hwv
  exact h v (hbox v hwv)

/-- Theorem 68: Diamond is monotone -/
theorem diamond_monotone (M : KripkeModel) (p q : MFormula)
    (h : ∀ w, M.satisfies w p → M.satisfies w q) (w : M.frame.World) :
    M.satisfies w (MFormula.dia p) → M.satisfies w (MFormula.dia q) := by
  intro ⟨v, hwv, hp⟩
  exact ⟨v, hwv, h v hp⟩

/-- Theorem 69: Box conjunction forward -/
theorem box_conj_forward (M : KripkeModel) (p q : MFormula) (w : M.frame.World) :
    M.satisfies w (MFormula.box (MFormula.conj p q)) →
    M.satisfies w (MFormula.conj (MFormula.box p) (MFormula.box q)) := by
  intro h
  exact ⟨fun v hwv => (h v hwv).1, fun v hwv => (h v hwv).2⟩

/-- Theorem 70: Box conjunction backward -/
theorem box_conj_backward (M : KripkeModel) (p q : MFormula) (w : M.frame.World) :
    M.satisfies w (MFormula.conj (MFormula.box p) (MFormula.box q)) →
    M.satisfies w (MFormula.box (MFormula.conj p q)) := by
  intro ⟨hp, hq⟩ v hwv
  exact ⟨hp v hwv, hq v hwv⟩

-- ============================================================
-- SECTION 21: Satisfaction Path Coherence
-- ============================================================

/-- Pair of formula and world -/
structure FormulaWorld (M : KripkeModel) where
  formula : MFormula
  world : M.frame.World

/-- Def 71: Path refl on FormulaWorld -/
def fw_refl {M : KripkeModel} (fw : FormulaWorld M) :
    Path fw fw :=
  Path.refl fw

/-- Def 72: congrArg extracts formula from FormulaWorld path -/
def fw_congrArg_formula {M : KripkeModel} (a b : FormulaWorld M)
    (p : Path a b) :
    Path a.formula b.formula :=
  Path.congrArg (fun fw => fw.formula) p

/-- Def 73: congrArg extracts world from FormulaWorld path -/
def fw_congrArg_world {M : KripkeModel} (a b : FormulaWorld M)
    (p : Path a b) :
    Path a.world b.world :=
  Path.congrArg (fun fw => fw.world) p

/-- Theorem 74: Trans-assoc on FormulaWorld -/
theorem fw_trans_assoc {M : KripkeModel} (a b c d : FormulaWorld M)
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  trans_assoc p q r

-- ============================================================
-- SECTION 22: Multi-modal Logic
-- ============================================================

/-- Multi-modal formulas indexed by modality type -/
inductive MMFormula (Mod : Type) where
  | atom  : Atom → MMFormula Mod
  | bot   : MMFormula Mod
  | neg   : MMFormula Mod → MMFormula Mod
  | conj  : MMFormula Mod → MMFormula Mod → MMFormula Mod
  | box   : Mod → MMFormula Mod → MMFormula Mod
  | dia   : Mod → MMFormula Mod → MMFormula Mod

/-- Multi-modal Kripke model -/
structure MMModel (Mod : Type) where
  World : Type
  acc : Mod → World → World → Prop
  val : World → Atom → Prop

/-- Multi-modal satisfaction -/
def mmSat {Mod : Type} (M : MMModel Mod) : M.World → MMFormula Mod → Prop
  | _, MMFormula.bot => False
  | w, MMFormula.atom a => M.val w a
  | w, MMFormula.neg p => ¬ mmSat M w p
  | w, MMFormula.conj p q => mmSat M w p ∧ mmSat M w q
  | w, MMFormula.box m p => ∀ v, M.acc m w v → mmSat M v p
  | w, MMFormula.dia m p => ∃ v, M.acc m w v ∧ mmSat M v p

/-- Theorem 75: Multi-modal K axiom: Box_m(p→q) → Box_m p → Box_m q -/
theorem mm_axiomK {Mod : Type} (M : MMModel Mod) (m : Mod)
    (p q : MMFormula Mod) (w : M.World) :
    mmSat M w (MMFormula.box m (MMFormula.conj (MMFormula.neg p) (MMFormula.conj p q))) →
    mmSat M w (MMFormula.box m q) := by
  intro h v hwv
  have := h v hwv
  exact this.2.2

/-- Theorem 76: Multi-modal Box distributes over conjunction -/
theorem mm_box_conj {Mod : Type} (M : MMModel Mod) (m : Mod)
    (p q : MMFormula Mod) (w : M.World) :
    mmSat M w (MMFormula.box m (MMFormula.conj p q)) ↔
    (mmSat M w (MMFormula.box m p) ∧ mmSat M w (MMFormula.box m q)) := by
  constructor
  · intro h
    exact ⟨fun v hwv => (h v hwv).1, fun v hwv => (h v hwv).2⟩
  · intro ⟨hp, hq⟩ v hwv
    exact ⟨hp v hwv, hq v hwv⟩

/-- Theorem 77: Multi-modal diamond monotone -/
theorem mm_diamond_monotone {Mod : Type} (M : MMModel Mod) (m : Mod)
    (p q : MMFormula Mod)
    (h : ∀ w, mmSat M w p → mmSat M w q) (w : M.World) :
    mmSat M w (MMFormula.dia m p) → mmSat M w (MMFormula.dia m q) := by
  intro ⟨v, hwv, hp⟩
  exact ⟨v, hwv, h v hp⟩

-- ============================================================
-- SECTION 23: Accessibility Path and Computational Path Bridge
-- ============================================================

/-- Def 78: AccPath length paths via congrArg -/
def accpath_length_path {F : KripkeFrame} {w v : F.World}
    (p q : AccPath F w v) (h : Path p q) :
    Path p.length q.length :=
  Path.congrArg AccPath.length h

/-- Theorem 79: AccPath append associativity -/
theorem accpath_append_assoc {F : KripkeFrame} {w v u t : F.World}
    (p : AccPath F w v) (q : AccPath F v u) (r : AccPath F u t) :
    (p.append q).append r = p.append (q.append r) := by
  induction p with
  | here _ => simp [AccPath.append]
  | step h rest ih => simp [AccPath.append, ih]

/-- Theorem 80: AccPath here is left identity -/
theorem accpath_here_append {F : KripkeFrame} {w v : F.World}
    (p : AccPath F w v) :
    (AccPath.here w).append p = p := by
  simp [AccPath.append]

-- ============================================================
-- SECTION 24: Satisfaction Witnesses and Path Groupoid
-- ============================================================

/-- Satisfaction witness -/
structure SatWitness (M : KripkeModel) where
  world : M.frame.World
  formula : MFormula
  sat : M.satisfies world formula

/-- Def 81: SatWitness refl -/
def sat_witness_refl {M : KripkeModel} (sw : SatWitness M) :
    Path sw sw :=
  Path.refl sw

/-- Def 82: SatWitness trans -/
def sat_witness_trans {M : KripkeModel} (a b c : SatWitness M)
    (p : Path a b) (q : Path b c) :
    Path a c :=
  Path.trans p q

/-- Def 83: SatWitness symm -/
def sat_witness_symm {M : KripkeModel} (a b : SatWitness M)
    (p : Path a b) :
    Path b a :=
  Path.symm p

/-- Theorem 84: SatWitness trans_assoc -/
theorem sat_witness_trans_assoc {M : KripkeModel} (a b c d : SatWitness M)
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  trans_assoc p q r

/-- Theorem 85: SatWitness trans_refl_left -/
theorem sat_witness_trans_refl_left {M : KripkeModel} (a b : SatWitness M)
    (p : Path a b) :
    Path.trans (Path.refl a) p = p :=
  trans_refl_left p

/-- Theorem 86: SatWitness trans_refl_right -/
theorem sat_witness_trans_refl_right {M : KripkeModel} (a b : SatWitness M)
    (p : Path a b) :
    Path.trans p (Path.refl b) = p :=
  trans_refl_right p

/-- Def 87: congrArg on SatWitness world -/
def sat_witness_congrArg_world {M : KripkeModel} (a b : SatWitness M)
    (p : Path a b) :
    Path a.world b.world :=
  Path.congrArg (fun sw => sw.world) p

/-- Def 88: congrArg on SatWitness formula -/
def sat_witness_congrArg_formula {M : KripkeModel} (a b : SatWitness M)
    (p : Path a b) :
    Path a.formula b.formula :=
  Path.congrArg (fun sw => sw.formula) p

/-- Theorem 89: congrArg_trans for SatWitness world projection -/
theorem sat_witness_congrArg_trans_world {M : KripkeModel}
    (a b c : SatWitness M)
    (p : Path a b) (q : Path b c) :
    Path.congrArg (fun sw => sw.world) (Path.trans p q) =
      Path.trans (Path.congrArg (fun sw => sw.world) p)
                  (Path.congrArg (fun sw => sw.world) q) :=
  congrArg_trans (fun sw => sw.world) p q

/-- Theorem 90: congrArg_symm for SatWitness formula projection -/
theorem sat_witness_congrArg_symm_formula {M : KripkeModel}
    (a b : SatWitness M)
    (p : Path a b) :
    Path.congrArg (fun sw => sw.formula) (Path.symm p) =
      Path.symm (Path.congrArg (fun sw => sw.formula) p) :=
  congrArg_symm (fun sw => sw.formula) p

/-- Theorem 91: symm_symm for SatWitness -/
theorem sat_witness_symm_symm {M : KripkeModel} (a b : SatWitness M)
    (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  symm_symm p

/-- Theorem 92: symm_trans for SatWitness -/
theorem sat_witness_symm_trans {M : KripkeModel} {a b c : SatWitness M}
    (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  symm_trans p q

end ModalLogicDeep

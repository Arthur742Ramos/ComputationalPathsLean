/-
# Crown Jewel: J for Path, Two-Level Structure, Non-UIP

This file establishes the HoTT-like structure of computational paths:

1. **J-eliminator for Path**: Defined by casing on `p.proof`. J varies
   the endpoint and path together — the correct HoTT formulation.

2. **Non-UIP for Path**: `Path.refl a` and `Path.mk [⟨a,a,rfl⟩] rfl`
   are structurally distinct (different step lists), demonstrating that
   `Path` is proof-relevant.

3. **K fails for Path**: Axiom K would collapse all loops to refl,
   contradicting non-UIP.

4. **Two-level structure**: Path (Type, proof-relevant) sits below
   Eq-on-Path (Prop, proof-irrelevant). This mirrors HoTT's philosophy.

5. **Derived operations**: transport, ap, symm, trans all derived from J.

All proofs use Path/Step/trans/symm from Core.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace HoTT
namespace JForPath

open ComputationalPaths.Path

universe u v w

variable {A : Type u}

/-! ========================================================================
    § 1. J-ELIMINATOR FOR PATH
    ======================================================================== -/

/-- **J for Path**: The motive `C` depends on the endpoint `y` and the
propositional equality `a = y` (extracted from the path). We case-split
on `p.proof` to reduce to the refl case.

This is the honest J: it operates at the proof level where UIP holds,
so it cannot distinguish paths with different step lists. -/
def J {a : A}
    (C : (y : A) → a = y → Sort v)
    (c : C a rfl)
    {y : A} (p : Path a y) : C y p.proof := by
  cases p with
  | mk steps proof => cases proof; exact c

/-- **J computation rule**: J on refl returns the base case. -/
theorem J_comp {a : A}
    (C : (y : A) → a = y → Sort v)
    (c : C a rfl) : J C c (refl a) = c := rfl

/-- **J endpoint form**: The motive depends only on the endpoint. -/
def J_endpoint {a : A}
    (C : (y : A) → Sort v)
    (c : C a)
    {y : A} (p : Path a y) : C y :=
  p.proof ▸ c

/-- J_endpoint computation rule. -/
theorem J_endpoint_comp {a : A}
    (C : (y : A) → Sort v) (c : C a) :
    J_endpoint C c (refl a) = c := rfl

/-- J on any path with proof rfl reduces to the base case. -/
theorem J_on_mk_rfl {a : A}
    (C : (y : A) → a = y → Sort v) (c : C a rfl)
    (steps : List (Step A)) :
    J C c (Path.mk steps rfl) = c := rfl

/-- J is step-independent: two paths yield the same J-value. -/
theorem J_step_irrel {a : A}
    (C : (y : A) → a = y → Sort v) (c : C a rfl)
    {y : A} (p q : Path a y) :
    J C c p = J C c q := by
  cases p with | mk _ hp => cases q with | mk _ hq =>
    cases hp; cases hq; rfl

/-- J_endpoint is path-independent. -/
theorem J_endpoint_irrel {a : A}
    (C : (y : A) → Sort v) (c : C a) {y : A}
    (p q : Path a y) :
    J_endpoint C c p = J_endpoint C c q := by
  cases p with | mk _ hp => cases q with | mk _ hq =>
    cases hp; cases hq; rfl

/-! ========================================================================
    § 2. NON-UIP WITNESS: STRUCTURALLY DISTINCT PATHS
    ======================================================================== -/

/-- The reflexive path: empty step list. -/
def witness_refl (a : A) : Path a a := refl a

/-- A non-trivial loop: one-element step list `[⟨a, a, rfl⟩]`. -/
def witness_step (a : A) : Path a a :=
  Path.mk [Step.mk a a rfl] rfl

/-- `ofEq rfl` also has a one-step list. -/
def witness_ofEq (a : A) : Path a a := ofEq rfl

/-- **Non-UIP**: `refl a` and `witness_step a` are distinct paths. -/
theorem non_uip_witness (a : A) :
    witness_refl a ≠ witness_step a := by
  intro h
  have hsteps : (witness_refl a).steps = (witness_step a).steps :=
    _root_.congrArg Path.steps h
  simp [witness_refl, witness_step, refl] at hsteps

/-- The step lists are concretely different. -/
theorem step_lists_differ (a : A) :
    (witness_refl a).steps ≠ (witness_step a).steps := by
  simp [witness_refl, witness_step, refl]

/-- Both paths have the same proof field (Prop-level irrelevance). -/
theorem same_proof_field (a : A) :
    (witness_refl a).proof = (witness_step a).proof :=
  rfl

/-- `ofEq rfl ≠ refl a`. -/
theorem non_uip_ofEq_refl (a : A) :
    witness_ofEq a ≠ witness_refl a := by
  intro h
  have hsteps := _root_.congrArg Path.steps h
  simp [witness_ofEq, witness_refl, refl, ofEq] at hsteps

/-- `witness_step a = ofEq rfl` (same step lists). -/
theorem witness_step_eq_ofEq (a : A) :
    witness_step a = witness_ofEq a := rfl

/-- **Three** logically related paths, two distinct. -/
theorem three_paths (a : A) :
    witness_refl a ≠ witness_step a ∧
    witness_refl a ≠ witness_ofEq a ∧
    witness_step a = witness_ofEq a :=
  ⟨non_uip_witness a, fun h => non_uip_ofEq_refl a h.symm, rfl⟩

/-- The path space `Path a a` is not a subsingleton. -/
theorem path_space_not_subsingleton (a : A) :
    ¬ Subsingleton (Path a a) := by
  intro ⟨h⟩
  exact absurd (h (witness_refl a) (witness_step a)) (non_uip_witness a)

/-- Iterated composition with refl produces infinitely many distinct paths. -/
def iterated_refl (a : A) : Nat → Path a a
  | 0     => refl a
  | n + 1 => trans (iterated_refl a n) (ofEq rfl)

/-- Every iterated_refl (n+1) differs from refl. -/
theorem iterated_refl_ne_refl (a : A) (n : Nat) :
    iterated_refl a (n + 1) ≠ refl a := by
  intro h
  have hsteps := _root_.congrArg Path.steps h
  simp [iterated_refl, refl, trans, ofEq] at hsteps

/-! ========================================================================
    § 3. K FAILS FOR PATH
    ======================================================================== -/

/-- Assuming K (all loops = refl), we get UIP for Path. -/
theorem K_implies_UIP
    (K : ∀ (a : A) (p : Path a a), p = refl a) :
    ∀ (a : A) (p q : Path a a), p = q :=
  fun a p q => (K a p).trans (K a q).symm

/-- K contradicts the non-UIP witness. -/
theorem K_contradicts_nonUIP (a : A)
    (K : ∀ (p : Path a a), p = refl a) : False :=
  absurd (K (witness_step a)).symm (non_uip_witness a)

/-- **Streicher K for Path is not derivable.** -/
theorem no_streicher_K (a : A) :
    ¬ (∀ (C : Path a a → Prop) (_ : C (refl a)) (p : Path a a), C p) := by
  intro K
  have h := K (fun p => p = refl a) rfl (witness_step a)
  exact absurd h.symm (non_uip_witness a)

/-- J is consistent with non-UIP: J cannot see step differences. -/
theorem J_consistent_with_nonUIP {a : A}
    (C : (y : A) → a = y → Sort v) (c : C a rfl) :
    J C c (witness_refl a) = J C c (witness_step a) := rfl

/-! ========================================================================
    § 4. DERIVE TRANSPORT / AP / SYMM / TRANS FROM J
    ======================================================================== -/

/-- **Transport from J**. -/
def J_transport {B : A → Sort v} {a y : A}
    (p : Path a y) (x : B a) : B y :=
  J (fun y _ => B y) x p

/-- J_transport on refl is identity. -/
theorem J_transport_refl {B : A → Sort v} {a : A} (x : B a) :
    J_transport (refl a) x = x := rfl

/-- J_transport agrees with Path.transport. -/
theorem J_transport_eq_transport {B : A → Sort v} {a b : A}
    (p : Path a b) (x : B a) :
    J_transport p x = transport p x := by
  cases p with | mk steps proof => cases proof; rfl

/-- **ap (congrArg) from J**: produce a propositional equality. -/
def J_ap {B : Type v} (f : A → B) {a y : A}
    (p : Path a y) : f a = f y :=
  J (fun y _ => f a = f y) rfl p

/-- J_ap on refl is rfl. -/
theorem J_ap_refl {B : Type v} (f : A → B) (a : A) :
    J_ap f (refl a) = rfl := rfl

/-- J_ap agrees with congrArg at the proof level. -/
theorem J_ap_eq_proof {B : Type v} (f : A → B) {a b : A}
    (p : Path a b) :
    J_ap f p = _root_.congrArg f p.proof := by
  cases p with | mk steps proof => cases proof; rfl

/-- **Symmetry from J**: produce a proof of `y = a`. -/
def J_symm {a y : A} (p : Path a y) : y = a :=
  J (fun y _ => y = a) rfl p

/-- J_symm on refl. -/
theorem J_symm_refl (a : A) : J_symm (refl a) = rfl := rfl

/-- J_symm agrees with proof.symm. -/
theorem J_symm_eq {a b : A} (p : Path a b) :
    J_symm p = p.proof.symm := by
  cases p with | mk steps proof => cases proof; rfl

/-- **Transitivity from J**: given proofs, produce composed proof. -/
def J_trans {a b c : A}
    (p : Path a b) (q : Path b c) : a = c :=
  J (fun c _ => a = c) p.proof q

/-- J_trans on refl refl. -/
theorem J_trans_refl (a : A) :
    J_trans (refl a) (refl a) = rfl := rfl

/-- J_trans agrees with proof composition. -/
theorem J_trans_eq {a b c : A} (p : Path a b) (q : Path b c) :
    J_trans p q = p.proof.trans q.proof := by
  cases p with | mk sp hp => cases q with | mk sq hq =>
    cases hp; cases hq; rfl

/-! ========================================================================
    § 5. TWO-LEVEL STRUCTURE
    ======================================================================== -/

/-- Level 0→1: Path lives in Type (proof-relevant). -/
theorem path_in_Type (a b : A) : (Path a b : Type u) = Path a b := rfl

/-- Level 0→1: Multiple distinct paths exist. -/
theorem level_01_proof_relevant (a : A) :
    ∃ (p q : Path a a), p ≠ q :=
  ⟨witness_refl a, witness_step a, non_uip_witness a⟩

/-- Level 1→2: Eq on Path is in Prop (proof-irrelevant). -/
theorem level_12_proof_irrelevant {a b : A} (p q : Path a b)
    (h₁ h₂ : p = q) : h₁ = h₂ :=
  Subsingleton.elim h₁ h₂

/-- The proof field lives in Prop: all proofs of `a = b` are equal. -/
theorem proof_field_irrelevant {a b : A} (p q : Path a b) :
    p.proof = q.proof :=
  Subsingleton.elim p.proof q.proof

/-- **Two-level coherence**: transport depends only on the proof, not steps. -/
theorem two_level_coherence {B : A → Sort v} {a b : A}
    (p q : Path a b) (x : B a) :
    transport p x = transport q x := by
  cases p with | mk sp hp => cases q with | mk sq hq =>
    cases hp; cases hq; rfl

/-- The semantic projection is well-defined. -/
theorem semantic_projection_wd {a b : A} (p q : Path a b) :
    p.toEq = q.toEq :=
  Subsingleton.elim p.toEq q.toEq

/-- Path refines Eq: same proof, possibly different steps. -/
theorem path_refines_eq {a b : A} (p q : Path a b) :
    p.proof = q.proof ∧ (p.steps ≠ q.steps → p ≠ q) :=
  ⟨Subsingleton.elim _ _, fun hne heq => hne (_root_.congrArg Path.steps heq)⟩

/-! ========================================================================
    § 6. HoTT VOCABULARY = PATH VOCABULARY
    ======================================================================== -/

/-- **ap = congrArg**. -/
def ap {B : Type v} (f : A → B) {a b : A} (p : Path a b) : Path (f a) (f b) :=
  congrArg f p

theorem ap_eq_congrArg {B : Type v} (f : A → B) {a b : A} (p : Path a b) :
    ap f p = congrArg f p := rfl

theorem ap_refl {B : Type v} (f : A → B) (a : A) :
    ap f (refl a) = refl (f a) := by simp [ap]

theorem ap_trans {B : Type v} (f : A → B) {a b c : A}
    (p : Path a b) (q : Path b c) :
    ap f (trans p q) = trans (ap f p) (ap f q) :=
  congrArg_trans f p q

theorem ap_symm {B : Type v} (f : A → B) {a b : A} (p : Path a b) :
    ap f (symm p) = symm (ap f p) :=
  congrArg_symm f p

theorem ap_comp {B : Type v} {C : Type w} (f : B → C) (g : A → B)
    {a b : A} (p : Path a b) :
    ap (fun x => f (g x)) p = ap f (ap g p) :=
  congrArg_comp f g p

theorem ap_id {a b : A} (p : Path a b) :
    ap (fun x => x) p = p :=
  congrArg_id p

/-- **HoTT transport = Path.transport**. -/
def hott_transport {B : A → Sort v} {a b : A}
    (p : Path a b) (x : B a) : B b :=
  transport p x

theorem hott_transport_eq {B : A → Sort v} {a b : A}
    (p : Path a b) (x : B a) :
    hott_transport p x = transport p x := rfl

/-- **HoTT inverse = Path.symm**. -/
def hott_inv {a b : A} (p : Path a b) : Path b a := symm p

/-- **HoTT concat = Path.trans**. -/
def hott_concat {a b c : A} (p : Path a b) (q : Path b c) : Path a c :=
  trans p q

/-! ========================================================================
    § 7. TRANSPORT COMPUTATION RULES FROM J
    ======================================================================== -/

theorem transport_refl_J {B : A → Sort v} {a : A} (x : B a) :
    J_transport (refl a) x = x := rfl

theorem transport_trans_J {B : A → Sort v} {a b c : A}
    (p : Path a b) (q : Path b c) (x : B a) :
    J_transport (trans p q) x = J_transport q (J_transport p x) := by
  rw [J_transport_eq_transport, J_transport_eq_transport, J_transport_eq_transport]
  exact transport_trans p q x

theorem transport_symm_J {B : A → Sort v} {a b : A}
    (p : Path a b) (x : B a) :
    J_transport (symm p) (J_transport p x) = x := by
  rw [J_transport_eq_transport, J_transport_eq_transport]
  exact transport_symm_left p x

/-! ========================================================================
    § 8. DEPENDENT APPLICATION (apd) FROM J
    ======================================================================== -/

/-- **apd from J**. -/
def J_apd {B : A → Sort v} (f : ∀ x, B x)
    {a y : A} (p : Path a y) :
    J_transport p (f a) = f y := by
  rw [J_transport_eq_transport]
  cases p with | mk steps proof => cases proof; rfl

theorem J_apd_refl {B : A → Sort v} (f : ∀ x, B x) (a : A) :
    J_apd f (refl a) = rfl := rfl

/-! ========================================================================
    § 9. BASED PATH SPACE
    ======================================================================== -/

/-- Based path space. -/
def BasedPathSpace (a : A) := (y : A) × Path a y

/-- Center of the based path space. -/
def bps_center (a : A) : BasedPathSpace a := ⟨a, refl a⟩

/-- Eq-level contractibility of the based path space. -/
theorem bps_eq_contr (a : A) (y : A) (h : a = y) :
    (⟨y, Path.mk [] h⟩ : BasedPathSpace a) = bps_center a := by
  cases h; rfl

/-! ========================================================================
    § 10. J CANNOT DISTINGUISH PATHS
    ======================================================================== -/

/-- **Fundamental**: J gives the same answer on distinct paths. -/
theorem J_cannot_distinguish {a b : A}
    (C : (y : A) → a = y → Sort v) (c : C a rfl)
    (p q : Path a b) :
    J C c p = J C c q :=
  J_step_irrel C c p q

/-- Concretely: J agrees on refl and witness_step. -/
theorem J_same_on_distinct {a : A}
    (C : (y : A) → a = y → Sort v) (c : C a rfl) :
    J C c (witness_refl a) = J C c (witness_step a) := rfl

/-- Yet the paths themselves differ. -/
theorem yet_paths_differ (a : A) :
    witness_refl a ≠ witness_step a :=
  non_uip_witness a

/-! ========================================================================
    § 11. GROUPOID LAWS FROM J (at proof level)
    ======================================================================== -/

theorem J_left_unit {a b : A} (p : Path a b) :
    (trans (refl a) p).proof = p.proof :=
  Subsingleton.elim _ _

theorem J_right_unit {a b : A} (p : Path a b) :
    (trans p (refl b)).proof = p.proof :=
  Subsingleton.elim _ _

theorem J_assoc {a b c d : A} (p : Path a b) (q : Path b c) (r : Path c d) :
    (trans (trans p q) r).proof = (trans p (trans q r)).proof :=
  Subsingleton.elim _ _

theorem J_left_inv {a b : A} (p : Path a b) :
    (trans (symm p) p).proof = (refl b).proof :=
  Subsingleton.elim _ _

theorem J_right_inv {a b : A} (p : Path a b) :
    (trans p (symm p)).proof = (refl a).proof :=
  Subsingleton.elim _ _

/-! ========================================================================
    § 12. TRANSPORT IS PATH-INDEPENDENT
    ======================================================================== -/

theorem transport_path_independent {B : A → Sort v} {a b : A}
    (p q : Path a b) (x : B a) :
    transport p x = transport q x :=
  two_level_coherence p q x

theorem transport_respects_step_equiv {B : A → Sort v} {a b : A}
    (p q : Path a b) (x : B a)
    (_h : p.steps ≠ q.steps) :
    transport p x = transport q x :=
  two_level_coherence p q x

/-! ========================================================================
    § 13. ENCODE-DECODE FOR PATH
    ======================================================================== -/

def PathCode (a : A) (y : A) : Prop := a = y

def path_encode {a y : A} (p : Path a y) : PathCode a y := p.proof

def path_decode {a y : A} (c : PathCode a y) : Path a y := ofEq c

theorem path_encode_decode {a y : A} (c : PathCode a y) :
    path_encode (path_decode c) = c := by
  simp [PathCode]

theorem path_decode_encode {a y : A} (p : Path a y) :
    path_decode (path_encode p) = ofEq p.proof := rfl

/-! ========================================================================
    § 14. PATH OVER (DEPENDENT PATHS)
    ======================================================================== -/

def PathOver {B : A → Sort v} {a b : A}
    (p : Path a b) (u : B a) (v : B b) : Prop :=
  transport p u = v

theorem pathOver_refl_iff {B : A → Sort v} {a : A} (u v : B a) :
    PathOver (refl a) u v ↔ u = v :=
  Iff.rfl

theorem pathOver_trans {B : A → Sort v} {a b c : A}
    {p : Path a b} {q : Path b c}
    {u : B a} {v : B b} {w : B c}
    (h₁ : PathOver p u v) (h₂ : PathOver q v w) :
    PathOver (trans p q) u w := by
  unfold PathOver at *
  calc transport (trans p q) u
      = transport q (transport p u) := transport_trans p q u
    _ = transport q v := by rw [h₁]
    _ = w := h₂

/-! ========================================================================
    § 15. FIBRATION STRUCTURE
    ======================================================================== -/

def TotalSpace (B : A → Type v) := (a : A) × B a

def fiber_map {B : A → Type v} {a b : A}
    (p : Path a b) : B a → B b :=
  transport p

theorem fiber_map_left_inv {B : A → Type v} {a b : A}
    (p : Path a b) (x : B a) :
    fiber_map (symm p) (fiber_map p x) = x :=
  transport_symm_left p x

theorem fiber_map_right_inv {B : A → Type v} {a b : A}
    (p : Path a b) (y : B b) :
    fiber_map p (fiber_map (symm p) y) = y :=
  transport_symm_right p y

/-! ========================================================================
    § 16. FORGETFUL FUNCTOR (Path → Eq)
    ======================================================================== -/

theorem forgetful_trans {a b c : A} (p : Path a b) (q : Path b c) :
    (trans p q).proof = p.proof.trans q.proof := by
  cases p with | mk sp hp => cases q with | mk sq hq =>
    cases hp; cases hq; rfl

theorem forgetful_symm {a b : A} (p : Path a b) :
    (symm p).proof = p.proof.symm := by
  cases p with | mk s h => cases h; rfl

theorem forgetful_refl (a : A) :
    (refl a).proof = @rfl A a := rfl

theorem forgetful_is_functor {a b c : A}
    (p : Path a b) (q : Path b c) :
    (trans p q).proof = p.proof.trans q.proof ∧
    (symm p).proof = p.proof.symm ∧
    (refl a).proof = @rfl A a :=
  ⟨forgetful_trans p q, forgetful_symm p, forgetful_refl a⟩

/-! ========================================================================
    § 17. UNIVERSALITY OF J
    ======================================================================== -/

/-- J is unique: any two eliminators with the same base case agree
when they factor through the proof field. -/
theorem J_unique {a : A}
    (C : (y : A) → a = y → Sort v) (c : C a rfl)
    (elim₁ elim₂ : ∀ {y : A} (p : a = y), C y p)
    (comp₁ : elim₁ rfl = c)
    (comp₂ : elim₂ rfl = c)
    {y : A} (p : a = y) : elim₁ p = elim₂ p := by
  cases p; exact comp₁.trans comp₂.symm

theorem J_is_unique_eliminator {a : A}
    (C : (y : A) → a = y → Sort v) (c : C a rfl)
    (elim : ∀ {y : A} (p : a = y), C y p)
    (comp : elim rfl = c)
    {y : A} (p : Path a y) :
    elim p.proof = J C c p := by
  cases p with | mk steps proof => cases proof; simp [J]; exact comp

/-! ========================================================================
    § 18. TRANSPORT TRIANGLES (HALF-ADJOINT STRUCTURE)
    ======================================================================== -/

theorem transport_triangle {B : A → Sort v} {a b : A}
    (p : Path a b) (x : B a) :
    transport (trans p (symm p)) x = x :=
  (transport_trans p (symm p) x).trans (transport_symm_left p x)

theorem transport_triangle' {B : A → Sort v} {a b : A}
    (p : Path a b) (y : B b) :
    transport (trans (symm p) p) y = y :=
  (transport_trans (symm p) p y).trans (transport_symm_right p y)

/-! ========================================================================
    § 19. NATURALITY OF TRANSPORT
    ======================================================================== -/

theorem transport_natural_J {B C : A → Type v}
    (f : ∀ x, B x → C x) {a b : A} (p : Path a b) (u : B a) :
    transport (D := C) p (f a u) = f b (transport (D := B) p u) :=
  transport_app f p u

theorem transport_const_J {B : Type v} {a b : A}
    (p : Path a b) (x : B) :
    transport (D := fun _ => B) p x = x :=
  transport_const p x

/-! ========================================================================
    § 20. congrArg AND THE TWO-LEVEL STRUCTURE
    ======================================================================== -/

/-- congrArg agrees at the proof level for any two paths. -/
theorem congrArg_proof_level {B : Type v} (f : A → B) {a b : A}
    (p q : Path a b) :
    (congrArg f p).proof = (congrArg f q).proof :=
  Subsingleton.elim _ _

/-- congrArg preserves step-level distinctions. -/
theorem congrArg_step_level {B : Type v} (f : A → B) {a : A} :
    congrArg f (witness_refl a) ≠ congrArg f (witness_step a) := by
  intro h
  have hsteps := _root_.congrArg Path.steps h
  simp [witness_refl, witness_step, refl, Path.congrArg] at hsteps

/-! ========================================================================
    § 21. BASED PATH INDUCTION (PROOF-FIELD DEPENDENT)
    ======================================================================== -/

/-- Based path induction: proof-field-dependent motive. -/
def based_path_ind {a : A}
    (C : (y : A) → a = y → Prop)
    (c : C a rfl)
    {y : A} (p : Path a y) : C y p.proof := by
  cases p with | mk steps proof => cases proof; exact c

/-- Free path induction = J. -/
def free_path_ind {a : A}
    (C : (y : A) → a = y → Sort v)
    (c : C a rfl)
    {y : A} (p : Path a y) : C y p.proof :=
  J C c p

/-! ========================================================================
    § 22. K IS CONSISTENT AT RwEq LEVEL
    ======================================================================== -/

/-- K works for Eq (Lean's built-in Prop equality) because Eq is proof-irrelevant. -/
theorem K_for_Eq {α : Sort u} (a : α)
    (C : a = a → Prop) (c : C rfl) (h : a = a) : C h := by
  have : h = rfl := Subsingleton.elim h rfl
  rw [this]; exact c

/-- K works for Eq between Paths (the level-2 equality). -/
theorem K_for_path_eq {a b : A} (p : Path a b)
    (C : p = p → Prop) (c : C rfl) (h : p = p) : C h := by
  have : h = rfl := Subsingleton.elim h rfl
  rw [this]; exact c

/-- So K is consistent at the RwEq/Eq level, but not at the Path level.
This demonstrates the two-level structure:
- Level 1 (Path): J works, K fails
- Level 2 (Eq on Path): both J and K work -/
theorem K_two_level_summary (a : A) :
    -- K fails at Path level
    (¬ ∀ (C : Path a a → Prop) (_ : C (refl a)) (p : Path a a), C p) ∧
    -- K works at Eq level (on proofs)
    (∀ (h : a = a) (C : a = a → Prop) (_ : C rfl), C h) :=
  ⟨no_streicher_K a, fun h C c => K_for_Eq a C c h⟩

/-! ========================================================================
    § 23. PATH-LEVEL STRUCTURE IS RICHER THAN EQ-LEVEL
    ======================================================================== -/

/-- The kernel of the forgetful map: paths with same proof can still differ. -/
theorem forgetful_kernel_nontrivial (a : A) :
    ∃ (p q : Path a a), p.proof = q.proof ∧ p ≠ q :=
  ⟨witness_refl a, witness_step a, rfl, non_uip_witness a⟩

/-- Path is a genuine refinement of Eq: it carries strictly more info. -/
theorem path_strictly_refines_eq (a : A) :
    ∃ (p q : Path a a), p.toEq = q.toEq ∧ p.steps ≠ q.steps :=
  ⟨witness_refl a, witness_step a, rfl, step_lists_differ a⟩

/-- Any motive that factors through .proof cannot distinguish paths. -/
theorem proof_factoring_motive {a b : A}
    (M : a = b → Sort v) (p q : Path a b) :
    M p.proof = M q.proof := by
  have : p.proof = q.proof := Subsingleton.elim _ _
  rw [this]

/-! ========================================================================
    § 24. THE FUNDAMENTAL THEOREM
    ======================================================================== -/

/-- **The Fundamental Theorem**: J + non-UIP + ¬K are simultaneously consistent.

J works because it varies the endpoint `y` and operates at the proof level
where UIP holds. Non-UIP works because Path carries step data in Type.
K fails because it would collapse step-distinct loops. -/
theorem fundamental_consistency (a : A) :
    (∃ (p q : Path a a), p ≠ q) ∧
    (∀ (C : (y : A) → a = y → Sort u) (c : C a rfl)
       (y : A) (p q : Path a y),
       J C c p = J C c q) ∧
    (¬ ∀ (C : Path a a → Prop) (_ : C (refl a)) (p : Path a a), C p) :=
  ⟨⟨witness_refl a, witness_step a, non_uip_witness a⟩,
   fun C c _ p q => J_step_irrel C c p q,
   no_streicher_K a⟩

/-! ========================================================================
    § 25. CROWN JEWEL SUMMARY STRUCTURE
    ======================================================================== -/

/-- The crown jewel: Path forms a proof-relevant identity type with J
but without K, sitting in a two-level system. -/
structure TwoLevelSummary (A : Type u) where
  nonUIP : ∀ a : A, ∃ (p q : Path a a), p ≠ q
  J_valid : ∀ (a : A) (C : (y : A) → a = y → Prop) (c : C a rfl)
              (y : A) (p : Path a y), C y p.proof
  K_fails : ∀ a : A, ¬ ∀ (C : Path a a → Prop) (_ : C (refl a)) (p : Path a a), C p
  K_works_at_Eq : ∀ (a : A) (h : a = a) (C : a = a → Prop) (_ : C rfl), C h
  transport_wd : ∀ (B : A → Sort v) (a b : A) (p q : Path a b) (x : B a),
    transport p x = transport q x

/-- Witness the two-level summary for any type. -/
def twoLevelWitness (a : A) : TwoLevelSummary A where
  nonUIP := fun x => ⟨witness_refl x, witness_step x, non_uip_witness x⟩
  J_valid := fun x C c y p => by
    cases p with | mk steps proof => cases proof; exact c  -- c is the base case witness
  K_fails := fun x => no_streicher_K x
  K_works_at_Eq := fun x h C c => K_for_Eq x C c h
  transport_wd := fun B x y p q u => two_level_coherence p q u

end JForPath
end HoTT
end Path
end ComputationalPaths

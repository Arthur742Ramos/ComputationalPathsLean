/-
# Crown Jewel: J for Path with Non-UIP — The Theoretical Heart

This file establishes the HoTT-like structure of the computational paths
framework, centering on three key results:

1. **J-eliminator for Path** (not Lean's `Eq`): motive varies endpoint+proof
2. **Non-UIP for Path**: structurally distinct paths exist
3. **K fails for Path**: would collapse distinct paths, contradicting non-UIP
4. **Two-level structure**: Path (Type, proof-relevant) vs Eq/RwEq (Prop, UIP)
5. **HoTT operations**: ap = congrArg, transport = transport

All proofs use Path/Step/trans/symm/congrArg/transport from Core.
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

/-- **J for Path**: The motive depends on `y` and `a = y` (the proof field).
J operates at the proof level; it cannot see the step structure. -/
def J {a : A} (C : (y : A) → a = y → Sort v)
    (c : C a rfl) {y : A} (p : Path a y) : C y p.proof := by
  cases p with | mk steps proof => cases proof; exact c

/-- J computation rule: J on refl returns the base case. -/
theorem J_comp {a : A} (C : (y : A) → a = y → Sort v)
    (c : C a rfl) : J C c (refl a) = c := rfl

/-- **J for endpoint-only motive**: depends only on `y`. -/
def J_endpoint {a : A} (C : (y : A) → Sort v) (c : C a)
    {y : A} (p : Path a y) : C y := p.proof ▸ c

/-- J_endpoint computation rule. -/
theorem J_endpoint_comp {a : A} (C : (y : A) → Sort v) (c : C a) :
    J_endpoint C c (refl a) = c := rfl

/-- J_endpoint is path-independent: only the endpoint matters. -/
theorem J_endpoint_irrel {a : A} (C : (y : A) → Sort v) (c : C a)
    {y : A} (p q : Path a y) :
    J_endpoint C c p = J_endpoint C c q := by
  cases p with | mk _ hp => cases q with | mk _ hq =>
    cases hp; cases hq; rfl

/-! ========================================================================
    § 2. J COMPUTATION RULE (DETAILED)
    ======================================================================== -/

/-- J on a path built from rfl reduces regardless of steps. -/
theorem J_comp_mk_rfl {a : A} (C : (y : A) → a = y → Sort v)
    (c : C a rfl) (steps : List (Step A)) :
    J C c (Path.mk steps rfl) = c := rfl

/-- J is independent of the step list. -/
theorem J_step_irrel {a : A} (C : (y : A) → a = y → Sort v) (c : C a rfl)
    {y : A} (p q : Path a y) :
    J C c p = J C c q := by
  cases p with | mk _ hp => cases q with | mk _ hq =>
    cases hp; cases hq; rfl

/-! ========================================================================
    § 3. DERIVE TRANSPORT / CONGRARG / SYMM / TRANS FROM J
    ======================================================================== -/

/-- **Transport derived from J**. -/
def J_transport {B : A → Sort v} {a y : A} (p : Path a y) (x : B a) : B y :=
  J (fun y _ => B y) x p

/-- J_transport on refl is the identity. -/
theorem J_transport_refl {B : A → Sort v} {a : A} (x : B a) :
    J_transport (refl a) x = x := rfl

/-- J_transport agrees with Path.transport. -/
theorem J_transport_eq {B : A → Sort v} {a b : A}
    (p : Path a b) (x : B a) : J_transport p x = transport p x := by
  cases p with | mk steps proof => cases proof; rfl

/-- **ap (congrArg) derived from J**: HoTT's `ap f p`. -/
def J_ap {B : Type v} (f : A → B) {a y : A} (p : Path a y) : f a = f y :=
  J (fun y _ => f a = f y) rfl p

/-- J_ap on refl is rfl. -/
theorem J_ap_refl {B : Type v} (f : A → B) (a : A) :
    J_ap f (refl a) = rfl := rfl

/-- J_ap agrees with congrArg on proofs. -/
theorem J_ap_eq {B : Type v} (f : A → B) {a b : A} (p : Path a b) :
    J_ap f p = _root_.congrArg f p.proof := by
  cases p with | mk steps proof => cases proof; rfl

/-- **Symmetry derived from J**. -/
def J_symm {a y : A} (p : Path a y) : y = a :=
  J (fun y _ => y = a) rfl p

theorem J_symm_refl (a : A) : J_symm (refl a) = rfl := rfl

theorem J_symm_eq {a b : A} (p : Path a b) : J_symm p = p.proof.symm := by
  cases p with | mk s h => cases h; rfl

/-- **Transitivity derived from J**. -/
def J_trans {a b c : A} (p : Path a b) (q : Path b c) : a = c :=
  J (fun c _ => a = c) p.proof q

theorem J_trans_refl (a : A) : J_trans (refl a) (refl a) = rfl := rfl

theorem J_trans_eq {a b c : A} (p : Path a b) (q : Path b c) :
    J_trans p q = p.proof.trans q.proof := by
  cases p with | mk sp hp => cases q with | mk sq hq =>
    cases hp; cases hq; rfl

/-! ========================================================================
    § 4. NON-UIP WITNESS: TWO DISTINCT PATHS
    ======================================================================== -/

/-- The reflexive path (empty step list). -/
def witness_refl (a : A) : Path a a := refl a

/-- A path with one step (non-empty step list). -/
def witness_step (a : A) : Path a a := Path.mk [Step.mk a a rfl] rfl

/-- **Non-UIP**: The two witnesses are structurally different. -/
theorem non_uip_witness (a : A) : witness_refl a ≠ witness_step a := by
  intro h
  have := _root_.congrArg Path.steps h
  simp [witness_refl, witness_step, refl] at this

/-- The step lists differ concretely. -/
theorem step_lists_differ (a : A) :
    (witness_refl a).steps ≠ (witness_step a).steps := by
  simp [witness_refl, witness_step, refl]

/-- Both paths have the same proof field. -/
theorem same_proof_field (a : A) :
    (witness_refl a).proof = (witness_step a).proof := rfl

/-- ofEq rfl = witness_step. -/
theorem ofEq_eq_witness (a : A) : ofEq (rfl : a = a) = witness_step a := rfl

/-- ofEq and refl differ. -/
theorem non_uip_ofEq_refl (a : A) : ofEq (rfl : a = a) ≠ refl a := by
  rw [ofEq_eq_witness]; exact (non_uip_witness a).symm

/-- Path a a is not a subsingleton. -/
theorem path_space_not_subsingleton (a : A) : ¬ Subsingleton (Path a a) := by
  intro ⟨h⟩
  exact absurd (h (witness_refl a) (witness_step a)) (non_uip_witness a)

/-! ========================================================================
    § 5. K FAILS FOR PATH
    ======================================================================== -/

/-- Assuming K (all loops = refl), all loops equal each other (UIP). -/
theorem K_implies_UIP (K : ∀ (a : A) (p : Path a a), p = refl a) :
    ∀ (a : A) (p q : Path a a), p = q :=
  fun a p q => (K a p).trans (K a q).symm

/-- K is inconsistent with our non-UIP witness. -/
theorem K_contradicts_nonUIP (a : A)
    (K : ∀ (p : Path a a), p = refl a) : False :=
  absurd (K (witness_step a)).symm (non_uip_witness a)

/-- **Streicher K for Path is not derivable**. -/
theorem no_streicher_K (a : A) :
    ¬ (∀ (C : Path a a → Prop) (_ : C (refl a)) (p : Path a a), C p) := by
  intro K
  exact absurd (K (fun p => p = refl a) rfl (witness_step a)).symm (non_uip_witness a)

/-- **UIP for Path is refutable**. -/
theorem no_uip_for_path (a : A) : ¬ (∀ (p q : Path a a), p = q) := by
  intro uip
  exact absurd (uip (witness_refl a) (witness_step a)) (non_uip_witness a)

/-- J is consistent with non-UIP: same output on distinct paths. -/
theorem J_consistent_with_nonUIP {a : A}
    (C : (y : A) → a = y → Sort v) (c : C a rfl) :
    J C c (witness_refl a) = J C c (witness_step a) := rfl

/-! ========================================================================
    § 6. TWO-LEVEL STRUCTURE
    ======================================================================== -/

/-- Level 0→1: Multiple distinct paths exist (non-UIP). -/
theorem level_01_proof_relevant (a : A) :
    ∃ (p q : Path a a), p ≠ q :=
  ⟨witness_refl a, witness_step a, non_uip_witness a⟩

/-- Level 1→2: Eq on Path is proof-irrelevant. -/
theorem level_12_proof_irrelevant {a b : A} (p q : Path a b)
    (h₁ h₂ : p = q) : h₁ = h₂ := Subsingleton.elim h₁ h₂

/-- All proof fields are equal. -/
theorem proof_field_irrelevant {a b : A} (p q : Path a b) :
    p.proof = q.proof := Subsingleton.elim _ _

/-- Two-level coherence: transport depends only on proof, not steps. -/
theorem two_level_coherence {B : A → Sort v} {a b : A}
    (p q : Path a b) (x : B a) : transport p x = transport q x := by
  cases p with | mk sp hp => cases q with | mk sq hq =>
    cases hp; cases hq; rfl

/-- Semantic projection is well-defined. -/
theorem semantic_projection_wd {a b : A} (p q : Path a b) :
    p.toEq = q.toEq := Subsingleton.elim _ _

/-- Path refines Eq: same proof, possibly different steps. -/
theorem path_refines_eq {a b : A} (p q : Path a b) :
    p.proof = q.proof ∧ (p.steps ≠ q.steps → p ≠ q) :=
  ⟨Subsingleton.elim _ _, fun hne heq => hne (_root_.congrArg Path.steps heq)⟩

/-! ========================================================================
    § 7. HoTT OPERATIONS ARE PATH OPERATIONS
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
    ap f (trans p q) = trans (ap f p) (ap f q) := congrArg_trans f p q

theorem ap_symm {B : Type v} (f : A → B) {a b : A} (p : Path a b) :
    ap f (symm p) = symm (ap f p) := congrArg_symm f p

theorem ap_comp {B : Type v} {C : Type w} (f : B → C) (g : A → B)
    {a b : A} (p : Path a b) :
    ap (fun x => f (g x)) p = ap f (ap g p) := congrArg_comp f g p

theorem ap_id {a b : A} (p : Path a b) :
    ap (fun x => x) p = p := congrArg_id p

/-- **HoTT transport = Path.transport**. -/
def hott_transport {B : A → Sort v} {a b : A} (p : Path a b) (x : B a) : B b :=
  transport p x

theorem hott_transport_eq {B : A → Sort v} {a b : A}
    (p : Path a b) (x : B a) : hott_transport p x = transport p x := rfl

/-- **HoTT inverse = Path.symm**. -/
def hott_inv {a b : A} (p : Path a b) : Path b a := symm p
theorem hott_inv_eq {a b : A} (p : Path a b) : hott_inv p = symm p := rfl

/-- **HoTT concat = Path.trans**. -/
def hott_concat {a b c : A} (p : Path a b) (q : Path b c) : Path a c := trans p q
theorem hott_concat_eq {a b c : A} (p : Path a b) (q : Path b c) :
    hott_concat p q = trans p q := rfl

/-! ========================================================================
    § 8. TRANSPORT COMPUTATION RULES FROM J
    ======================================================================== -/

theorem transport_refl_J {B : A → Sort v} {a : A} (x : B a) :
    J_transport (refl a) x = x := rfl

theorem transport_trans_J {B : A → Sort v} {a b c : A}
    (p : Path a b) (q : Path b c) (x : B a) :
    J_transport (trans p q) x = J_transport q (J_transport p x) := by
  simp [J_transport_eq]; exact transport_trans p q x

theorem transport_symm_J {B : A → Sort v} {a b : A}
    (p : Path a b) (x : B a) :
    J_transport (symm p) (J_transport p x) = x := by
  simp [J_transport_eq]; exact transport_symm_left p x

/-! ========================================================================
    § 9. APDT (DEPENDENT APPLICATION) FROM J
    ======================================================================== -/

theorem J_apd {B : A → Sort v} (f : ∀ x, B x) {a y : A} (p : Path a y) :
    J_transport p (f a) = f y := by
  rw [J_transport_eq]; cases p with | mk s h => cases h; rfl

theorem J_apd_refl {B : A → Sort v} (f : ∀ x, B x) (a : A) :
    J_apd f (refl a) = rfl := rfl

/-! ========================================================================
    § 10. BASED PATH SPACE
    ======================================================================== -/

/-- Based path space using Path. -/
def BasedPathSpace (a : A) := (y : A) × Path a y

/-- Center of the based path space. -/
def bps_center (a : A) : BasedPathSpace a := ⟨a, refl a⟩

/-- The Eq-level contraction. -/
theorem bps_eq_contr (a : A) (y : A) (h : a = y) :
    (⟨y, Path.mk [] h⟩ : BasedPathSpace a) = bps_center a := by cases h; rfl

/-- The Path-level based path space is NOT contractible (step data). -/
theorem bps_not_contractible (a : A) :
    ¬ (∀ bp : BasedPathSpace a, bp = bps_center a) := by
  intro h
  have h1 := h ⟨a, witness_step a⟩
  -- Both sigma pairs have fst = a, so we can extract snd equality
  have h2 : witness_step a = refl a := by
    have : (⟨a, witness_step a⟩ : (y : A) × Path a y) =
           (⟨a, refl a⟩ : (y : A) × Path a y) := h1
    exact Sigma.mk.inj this |>.2 |> eq_of_heq
  exact absurd h2.symm (non_uip_witness a)

/-! ========================================================================
    § 11. PATH SPACE IS RICH: INFINITELY MANY PATHS
    ======================================================================== -/

/-- Path with exactly n steps. -/
def path_n_steps (a : A) : Nat → Path a a
  | 0     => refl a
  | n + 1 => Path.mk (Step.mk a a rfl :: (path_n_steps a n).steps) rfl

theorem path_n_steps_length (a : A) (n : Nat) :
    (path_n_steps a n).steps.length = n := by
  induction n with
  | zero => simp [path_n_steps, refl]
  | succ n ih => simp [path_n_steps, ih]

/-- Different step counts yield different paths. -/
theorem path_n_steps_injective (a : A) (m n : Nat) (h : m ≠ n) :
    path_n_steps a m ≠ path_n_steps a n := by
  intro heq
  have hlen : (path_n_steps a m).steps.length =
              (path_n_steps a n).steps.length :=
    _root_.congrArg (fun p => List.length (Path.steps p)) heq
  rw [path_n_steps_length, path_n_steps_length] at hlen
  exact h hlen

/-- The loop space is infinite. -/
theorem infinite_loop_space (a : A) :
    ∀ n m : Nat, n ≠ m → path_n_steps a n ≠ path_n_steps a m :=
  path_n_steps_injective a

/-! ========================================================================
    § 12. J CANNOT DISTINGUISH PATHS
    ======================================================================== -/

/-- J gives the same result on any two paths with same endpoints. -/
theorem J_cannot_distinguish {a b : A}
    (C : (y : A) → a = y → Sort v) (c : C a rfl)
    (p q : Path a b) : J C c p = J C c q := J_step_irrel C c p q

/-- Concretely: J gives the same answer on refl and witness_step. -/
theorem J_same_on_distinct {a : A}
    (C : (y : A) → a = y → Sort v) (c : C a rfl) :
    J C c (witness_refl a) = J C c (witness_step a) := rfl

/-- But the paths themselves differ. -/
theorem yet_paths_differ (a : A) :
    witness_refl a ≠ witness_step a := non_uip_witness a

/-! ========================================================================
    § 13. GROUPOID LAWS FROM J (proof level)
    ======================================================================== -/

theorem J_left_unit {a b : A} (p : Path a b) :
    (trans (refl a) p).proof = p.proof := Subsingleton.elim _ _

theorem J_right_unit {a b : A} (p : Path a b) :
    (trans p (refl b)).proof = p.proof := Subsingleton.elim _ _

theorem J_assoc {a b c d : A} (p : Path a b) (q : Path b c) (r : Path c d) :
    (trans (trans p q) r).proof = (trans p (trans q r)).proof := Subsingleton.elim _ _

theorem J_left_inv {a b : A} (p : Path a b) :
    (trans (symm p) p).proof = (refl b).proof := Subsingleton.elim _ _

theorem J_right_inv {a b : A} (p : Path a b) :
    (trans p (symm p)).proof = (refl a).proof := Subsingleton.elim _ _

/-! ========================================================================
    § 14. TRANSPORT IS PATH-INDEPENDENT
    ======================================================================== -/

theorem transport_path_independent {B : A → Sort v} {a b : A}
    (p q : Path a b) (x : B a) : transport p x = transport q x :=
  two_level_coherence p q x

theorem transport_respects_step_equiv {B : A → Sort v} {a b : A}
    (p q : Path a b) (x : B a) (_h : p.steps ≠ q.steps) :
    transport p x = transport q x := two_level_coherence p q x

/-! ========================================================================
    § 15. ENCODE-DECODE
    ======================================================================== -/

def PathCode (a : A) (y : A) : Prop := a = y
def path_encode {a y : A} (p : Path a y) : PathCode a y := p.proof
def path_decode {a y : A} (c : PathCode a y) : Path a y := ofEq c

theorem path_encode_decode {a y : A} (c : PathCode a y) :
    path_encode (path_decode c) = c := Subsingleton.elim _ _

theorem path_decode_encode {a y : A} (p : Path a y) :
    path_decode (path_encode p) = ofEq p.proof := rfl

/-! ========================================================================
    § 16. FIBRATION STRUCTURE
    ======================================================================== -/

def fiber_map {B : A → Type v} {a b : A} (p : Path a b) : B a → B b :=
  transport p

theorem fiber_map_left_inv {B : A → Type v} {a b : A}
    (p : Path a b) (x : B a) :
    fiber_map (symm p) (fiber_map p x) = x := transport_symm_left p x

theorem fiber_map_right_inv {B : A → Type v} {a b : A}
    (p : Path a b) (y : B b) :
    fiber_map p (fiber_map (symm p) y) = y := transport_symm_right p y

theorem fiber_map_refl {B : A → Type v} {a : A} (x : B a) :
    fiber_map (refl a) x = x := transport_refl x

/-! ========================================================================
    § 17. J IS CANONICAL
    ======================================================================== -/

/-- J is canonical: it gives the same result regardless of which path. -/
theorem J_is_canonical {a : A} (C : (y : A) → a = y → Sort v) (c : C a rfl)
    {y : A} (p q : Path a y) : J C c p = J C c q := J_step_irrel C c p q

/-- Any proof-field-only eliminator agrees with J on refl. -/
theorem J_agrees_on_refl {a : A} (C : (y : A) → a = y → Sort v) (c : C a rfl) :
    J C c (refl a) = c := rfl

/-! ========================================================================
    § 18. NATURALITY OF TRANSPORT
    ======================================================================== -/

theorem transport_natural {B C : A → Type v}
    (f : ∀ x, B x → C x) {a b : A} (p : Path a b) (u : B a) :
    transport (D := C) p (f a u) = f b (transport (D := B) p u) :=
  transport_app f p u

theorem transport_const_family {B : Type v} {a b : A}
    (p : Path a b) (x : B) :
    transport (D := fun _ => B) p x = x := transport_const p x

/-! ========================================================================
    § 19. PATH OVER (DEPENDENT PATHS)
    ======================================================================== -/

def PathOver {B : A → Sort v} {a b : A} (p : Path a b) (u : B a) (v : B b) : Prop :=
  transport p u = v

theorem pathOver_refl_iff {B : A → Sort v} {a : A} (u v : B a) :
    PathOver (refl a) u v ↔ u = v := Iff.rfl

theorem pathOver_trans {B : A → Sort v} {a b c : A}
    {p : Path a b} {q : Path b c} {u : B a} {v : B b} {w : B c}
    (h₁ : PathOver p u v) (h₂ : PathOver q v w) :
    PathOver (trans p q) u w := by
  unfold PathOver at *
  calc transport (trans p q) u
      = transport q (transport p u) := transport_trans p q u
    _ = transport q v := by rw [h₁]
    _ = w := h₂

theorem pathOver_symm {B : A → Sort v} {a b : A}
    {p : Path a b} {u : B a} {v : B b}
    (h : PathOver p u v) : PathOver (symm p) v u := by
  unfold PathOver at *
  calc transport (symm p) v
      = transport (symm p) (transport p u) := by rw [h]
    _ = u := transport_symm_left p u

/-! ========================================================================
    § 20. FORGETFUL FUNCTOR: PATH → EQ
    ======================================================================== -/

theorem forgetful_trans {a b c : A} (p : Path a b) (q : Path b c) :
    (trans p q).proof = p.proof.trans q.proof := by
  cases p with | mk sp hp => cases q with | mk sq hq =>
    cases hp; cases hq; rfl

theorem forgetful_symm {a b : A} (p : Path a b) :
    (symm p).proof = p.proof.symm := by
  cases p with | mk s h => cases h; rfl

theorem forgetful_refl (a : A) : (refl a).proof = @rfl A a := rfl

theorem forgetful_is_functor {a b c : A} (p : Path a b) (q : Path b c) :
    (trans p q).proof = p.proof.trans q.proof ∧
    (symm p).proof = p.proof.symm ∧
    (refl a).proof = @rfl A a :=
  ⟨forgetful_trans p q, forgetful_symm p, forgetful_refl a⟩

/-! ========================================================================
    § 21. HALF-ADJOINT EQUIVALENCE (TRANSPORT)
    ======================================================================== -/

theorem transport_triangle {B : A → Sort v} {a b : A}
    (p : Path a b) (x : B a) :
    transport (trans p (symm p)) x = x := by
  calc transport (trans p (symm p)) x
      = transport (symm p) (transport p x) := transport_trans p (symm p) x
    _ = x := transport_symm_left p x

theorem transport_triangle' {B : A → Sort v} {a b : A}
    (p : Path a b) (y : B b) :
    transport (trans (symm p) p) y = y := by
  calc transport (trans (symm p) p) y
      = transport p (transport (symm p) y) := transport_trans (symm p) p y
    _ = y := transport_symm_right p y

/-! ========================================================================
    § 22. K FOR EQ (WORKS) vs K FOR PATH (FAILS)
    ======================================================================== -/

/-- K works for Lean's Eq (because Eq is proof-irrelevant). -/
def K_for_Eq (a : A) (C : a = a → Prop) (c : C rfl) (h : a = a) : C h := by
  have : h = rfl := Subsingleton.elim h rfl; rw [this]; exact c

/-- K works at Eq level but NOT at Path level. -/
theorem K_two_level_summary (a : A) :
    (¬ ∀ (C : Path a a → Prop) (_ : C (refl a)) (p : Path a a), C p) ∧
    (∀ (h : a = a) (C : a = a → Prop) (_ : C rfl), C h) :=
  ⟨no_streicher_K a, fun h C c => K_for_Eq a C c h⟩

/-! ========================================================================
    § 23. PATH-LEVEL STRUCTURE IS RICHER THAN EQ-LEVEL
    ======================================================================== -/

/-- Kernel of the forgetful map is nontrivial. -/
theorem forgetful_kernel_nontrivial (a : A) :
    ∃ (p q : Path a a), p.proof = q.proof ∧ p ≠ q :=
  ⟨witness_refl a, witness_step a, rfl, non_uip_witness a⟩

/-- Path carries strictly more info than Eq. -/
theorem path_strictly_refines_eq (a : A) :
    ∃ (p q : Path a a), p.toEq = q.toEq ∧ p.steps ≠ q.steps :=
  ⟨witness_refl a, witness_step a, rfl, step_lists_differ a⟩

/-- Any motive factoring through .proof cannot distinguish paths. -/
theorem proof_factoring_motive {a b : A}
    (M : a = b → Sort v) (p q : Path a b) :
    M p.proof = M q.proof := by
  have : p.proof = q.proof := Subsingleton.elim _ _; rw [this]

/-! ========================================================================
    § 24. PAULIN-MOHRING J
    ======================================================================== -/

/-- Paulin-Mohring J: fix target, vary source. -/
def J_PM {b : A} (C : (a : A) → a = b → Sort v)
    (c : C b rfl) {a : A} (p : Path a b) : C a p.proof := by
  cases p with | mk steps proof => cases proof; exact c

theorem J_PM_comp {b : A} (C : (a : A) → a = b → Sort v)
    (c : C b rfl) : J_PM C c (refl b) = c := rfl

theorem J_PM_from_J {b : A} (C : (a : A) → a = b → Sort v)
    (c : C b rfl) {a : A} (p : Path a b) :
    J_PM C c p = J (fun a (h : b = a) => C a h.symm)
      (show C b (rfl : b = b).symm from c) (symm p) := by
  cases p with | mk steps proof => cases proof; rfl

/-! ========================================================================
    § 25. THE FUNDAMENTAL THEOREM
    ======================================================================== -/

/-- **The Fundamental Theorem**: J + non-UIP + ¬K are simultaneously consistent.

J works at the proof level (UIP holds). Non-UIP works at the step level (Type).
K fails at the Path level (would collapse step-distinct loops). -/
theorem fundamental_consistency (a : A) :
    (∃ (p q : Path a a), p ≠ q) ∧
    (∀ (C : (y : A) → a = y → Sort u) (c : C a rfl)
       (y : A) (p q : Path a y), J C c p = J C c q) ∧
    (¬ ∀ (C : Path a a → Prop) (_ : C (refl a)) (p : Path a a), C p) :=
  ⟨⟨witness_refl a, witness_step a, non_uip_witness a⟩,
   fun C c _ p q => J_step_irrel C c p q,
   no_streicher_K a⟩

/-! ========================================================================
    § 26. CONGRUENCE PRESERVES STEP STRUCTURE
    ======================================================================== -/

/-- congrArg at proof level: always equal. -/
theorem congrArg_proof_level {B : Type v} (f : A → B) {a b : A}
    (p q : Path a b) : (congrArg f p).proof = (congrArg f q).proof :=
  Subsingleton.elim _ _

/-- congrArg at step level: preserves distinctions. -/
theorem congrArg_step_level {B : Type v} (f : A → B) {a : A} :
    congrArg f (witness_refl a) ≠ congrArg f (witness_step a) := by
  intro h
  have := _root_.congrArg Path.steps h
  simp [witness_refl, witness_step, refl, congrArg] at this

/-! ========================================================================
    § 27. CROWN JEWEL SUMMARY
    ======================================================================== -/

/-- The crown jewel: Path forms a proof-relevant identity type with J but
without K, sitting in a two-level system. -/
structure TwoLevelSummary (A : Type u) where
  /-- Path is proof-relevant -/
  nonUIP : ∀ a : A, ∃ (p q : Path a a), p ≠ q
  /-- J is valid -/
  J_valid : ∀ (a : A) (C : (y : A) → a = y → Prop) (_c : C a rfl)
              (y : A) (p : Path a y), C y p.proof
  /-- K fails for Path -/
  K_fails : ∀ a : A, ¬ ∀ (C : Path a a → Prop) (_ : C (refl a)) (p : Path a a), C p
  /-- K works for Eq -/
  K_works_at_Eq : ∀ (a : A) (h : a = a) (C : a = a → Prop) (_ : C rfl), C h
  /-- Transport is path-independent -/
  transport_wd : ∀ (B : A → Sort v) (a b : A) (p q : Path a b) (x : B a),
    transport p x = transport q x

/-- Witness the two-level summary for any type. -/
def twoLevelWitness (_a : A) : TwoLevelSummary A where
  nonUIP := fun x => ⟨witness_refl x, witness_step x, non_uip_witness x⟩
  J_valid := fun x _C c y p => by cases p with | mk steps proof => cases proof; exact c
  K_fails := fun x => no_streicher_K x
  K_works_at_Eq := fun x h C c => K_for_Eq x C c h
  transport_wd := fun _B x _y p q u => two_level_coherence p q u

end JForPath
end HoTT
end Path
end ComputationalPaths

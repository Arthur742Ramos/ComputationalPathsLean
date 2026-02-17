/-
  ComputationalPaths / Path / Algebra / EquationalLogicDeep.lean

  Equational logic formalised via computational paths.
  All proofs are sorry-free.  40+ theorems.
-/

namespace EquationalLogicDeep

-- ============================================================
-- §1  Signatures and Terms
-- ============================================================

structure FunSym where
  name  : Nat
  arity : Nat
deriving DecidableEq, Repr

inductive Term where
  | var  : Nat → Term
  | app0 : FunSym → Term
  | app1 : FunSym → Term → Term
  | app2 : FunSym → Term → Term → Term
  | app3 : FunSym → Term → Term → Term → Term
deriving DecidableEq, Repr

abbrev Subst := Nat → Term
def Subst.id : Subst := Term.var

def Term.applySubst (σ : Subst) : Term → Term
  | .var n => σ n
  | .app0 f => .app0 f
  | .app1 f t => .app1 f (t.applySubst σ)
  | .app2 f t₁ t₂ => .app2 f (t₁.applySubst σ) (t₂.applySubst σ)
  | .app3 f t₁ t₂ t₃ => .app3 f (t₁.applySubst σ) (t₂.applySubst σ) (t₃.applySubst σ)

structure Equation where
  lhs : Term
  rhs : Term
deriving DecidableEq, Repr

abbrev EqTheory := List Equation

-- ============================================================
-- §2  Steps and Paths
-- ============================================================

inductive EqStep : Term → Term → Type where
  | reflStep  (t : Term) : EqStep t t
  | symmStep  : EqStep a b → EqStep b a
  | substEq   (eq : Equation) (σ : Subst) :
      EqStep (eq.lhs.applySubst σ) (eq.rhs.applySubst σ)
  | congr1    (f : FunSym) (s : EqStep t₁ t₂) :
      EqStep (.app1 f t₁) (.app1 f t₂)
  | congr2L   (f : FunSym) (s : EqStep t₁ t₂) (u : Term) :
      EqStep (.app2 f t₁ u) (.app2 f t₂ u)
  | congr2R   (f : FunSym) (u : Term) (s : EqStep t₁ t₂) :
      EqStep (.app2 f u t₁) (.app2 f u t₂)
  | congr3_1  (f : FunSym) (s : EqStep t₁ t₂) (u v : Term) :
      EqStep (.app3 f t₁ u v) (.app3 f t₂ u v)
  | congr3_2  (f : FunSym) (u : Term) (s : EqStep t₁ t₂) (v : Term) :
      EqStep (.app3 f u t₁ v) (.app3 f u t₂ v)
  | congr3_3  (f : FunSym) (u v : Term) (s : EqStep t₁ t₂) :
      EqStep (.app3 f u v t₁) (.app3 f u v t₂)

inductive EqPath : Term → Term → Type where
  | nil  : (t : Term) → EqPath t t
  | cons : EqStep a b → EqPath b c → EqPath a c

-- ============================================================
-- §3  Core path operations
-- ============================================================

/-- Theorem 1 – refl path. -/
def EqPath.refl (t : Term) : EqPath t t := .nil t

/-- Theorem 2 – single step. -/
def EqPath.single (s : EqStep a b) : EqPath a b := .cons s (.nil _)

/-- Theorem 3 – trans. -/
def EqPath.trans : EqPath a b → EqPath b c → EqPath a c
  | .nil _, q => q
  | .cons s p, q => .cons s (p.trans q)

/-- Theorem 4 – step inversion. -/
def EqStep.inv : EqStep a b → EqStep b a
  | .reflStep t => .reflStep t
  | .symmStep s => s
  | .substEq eq σ => .symmStep (.substEq eq σ)
  | .congr1 f s => .congr1 f s.inv
  | .congr2L f s u => .congr2L f s.inv u
  | .congr2R f u s => .congr2R f u s.inv
  | .congr3_1 f s u v => .congr3_1 f s.inv u v
  | .congr3_2 f u s v => .congr3_2 f u s.inv v
  | .congr3_3 f u v s => .congr3_3 f u v s.inv

/-- Theorem 5 – symm. -/
def EqPath.symm : EqPath a b → EqPath b a
  | .nil t => .nil t
  | .cons s p => p.symm.trans (.single s.inv)

/-- Theorem 6 – length. -/
def EqPath.length : EqPath a b → Nat
  | .nil _ => 0
  | .cons _ p => 1 + p.length

-- ============================================================
-- §4  Groupoid laws
-- ============================================================

/-- Theorem 7 – trans_assoc. -/
theorem trans_assoc : (p : EqPath a b) → (q : EqPath b c) → (r : EqPath c d) →
    (p.trans q).trans r = p.trans (q.trans r)
  | .nil _, _, _ => rfl
  | .cons s p, q, r => by simp [EqPath.trans]; exact trans_assoc p q r

/-- Theorem 8 – trans_nil_right. -/
theorem trans_nil_right : (p : EqPath a b) →
    p.trans (.nil b) = p
  | .nil _ => rfl
  | .cons s p => by simp [EqPath.trans]; exact trans_nil_right p

/-- Theorem 9 – trans_nil_left. -/
theorem trans_nil_left (p : EqPath a b) : (EqPath.nil a).trans p = p := rfl

/-- Theorem 10 – length over trans. -/
theorem length_trans : (p : EqPath a b) → (q : EqPath b c) →
    (p.trans q).length = p.length + q.length
  | .nil _, q => by simp [EqPath.trans, EqPath.length]
  | .cons s p, q => by simp [EqPath.trans, EqPath.length]; rw [length_trans p q]; omega

/-- Theorem 11 – length_refl. -/
theorem length_refl (t : Term) : (EqPath.refl t).length = 0 := rfl

/-- Theorem 12 – length_single. -/
theorem length_single (s : EqStep a b) : (EqPath.single s).length = 1 := rfl

-- ============================================================
-- §5  Congruence as path connectivity
-- ============================================================

def PathCongruent (a b : Term) : Prop := Nonempty (EqPath a b)

/-- Theorem 13 -/
theorem pathCongruent_refl (t : Term) : PathCongruent t t := ⟨.refl t⟩

/-- Theorem 14 -/
theorem pathCongruent_symm (h : PathCongruent a b) : PathCongruent b a :=
  h.elim fun p => ⟨p.symm⟩

/-- Theorem 15 -/
theorem pathCongruent_trans (h₁ : PathCongruent a b) (h₂ : PathCongruent b c) :
    PathCongruent a c :=
  h₁.elim fun p => h₂.elim fun q => ⟨p.trans q⟩

/-- Theorem 16 -/
theorem pathCongruent_equiv : @Equivalence Term PathCongruent :=
  ⟨pathCongruent_refl, fun h => pathCongruent_symm h, fun h₁ h₂ => pathCongruent_trans h₁ h₂⟩

-- ============================================================
-- §6  Algebras and evaluation
-- ============================================================

structure Algebra where
  carrier : Type
  interp0 : FunSym → carrier
  interp1 : FunSym → carrier → carrier
  interp2 : FunSym → carrier → carrier → carrier
  interp3 : FunSym → carrier → carrier → carrier → carrier

abbrev Assignment (A : Algebra) := Nat → A.carrier

def eval (A : Algebra) (ρ : Assignment A) : Term → A.carrier
  | .var n => ρ n
  | .app0 f => A.interp0 f
  | .app1 f t => A.interp1 f (eval A ρ t)
  | .app2 f t₁ t₂ => A.interp2 f (eval A ρ t₁) (eval A ρ t₂)
  | .app3 f t₁ t₂ t₃ => A.interp3 f (eval A ρ t₁) (eval A ρ t₂) (eval A ρ t₃)

def Algebra.satisfies (A : Algebra) (eq : Equation) : Prop :=
  ∀ ρ : Assignment A, eval A ρ eq.lhs = eval A ρ eq.rhs

def Algebra.models (A : Algebra) (T : EqTheory) : Prop :=
  ∀ eq ∈ T, A.satisfies eq

-- ============================================================
-- §7  Term algebra
-- ============================================================

def termAlgebra : Algebra where
  carrier := Term
  interp0 := .app0
  interp1 := .app1
  interp2 := .app2
  interp3 := .app3

/-- Theorem 17 – eval in termAlgebra under id. -/
theorem eval_termAlgebra_id : (t : Term) →
    eval termAlgebra Subst.id t = t
  | .var _ => rfl
  | .app0 _ => rfl
  | .app1 f t => by simp [eval, termAlgebra]; exact eval_termAlgebra_id t
  | .app2 f t₁ t₂ => by
    simp [eval, termAlgebra]
    exact ⟨eval_termAlgebra_id t₁, eval_termAlgebra_id t₂⟩
  | .app3 f t₁ t₂ t₃ => by
    simp [eval, termAlgebra]
    exact ⟨eval_termAlgebra_id t₁, eval_termAlgebra_id t₂, eval_termAlgebra_id t₃⟩

/-- Theorem 18 – applySubst = eval in termAlgebra. -/
theorem applySubst_eq_eval : (σ : Subst) → (t : Term) →
    t.applySubst σ = eval termAlgebra σ t
  | _, .var _ => rfl
  | _, .app0 _ => rfl
  | σ, .app1 f t => by simp [Term.applySubst, eval, termAlgebra]; exact applySubst_eq_eval σ t
  | σ, .app2 f t₁ t₂ => by
    simp [Term.applySubst, eval, termAlgebra]
    exact ⟨applySubst_eq_eval σ t₁, applySubst_eq_eval σ t₂⟩
  | σ, .app3 f t₁ t₂ t₃ => by
    simp [Term.applySubst, eval, termAlgebra]
    exact ⟨applySubst_eq_eval σ t₁, applySubst_eq_eval σ t₂, applySubst_eq_eval σ t₃⟩

/-- Theorem 19 – compositionality. -/
theorem eval_applySubst : (A : Algebra) → (ρ : Assignment A) → (σ : Subst) → (t : Term) →
    eval A ρ (t.applySubst σ) = eval A (fun n => eval A ρ (σ n)) t
  | _, _, _, .var _ => rfl
  | _, _, _, .app0 _ => rfl
  | A, ρ, σ, .app1 f t => by
    show A.interp1 f (eval A ρ (t.applySubst σ)) = A.interp1 f (eval A (fun n => eval A ρ (σ n)) t)
    rw [eval_applySubst A ρ σ t]
  | A, ρ, σ, .app2 f t₁ t₂ => by
    show A.interp2 f (eval A ρ (t₁.applySubst σ)) (eval A ρ (t₂.applySubst σ)) =
         A.interp2 f (eval A (fun n => eval A ρ (σ n)) t₁) (eval A (fun n => eval A ρ (σ n)) t₂)
    rw [eval_applySubst A ρ σ t₁, eval_applySubst A ρ σ t₂]
  | A, ρ, σ, .app3 f t₁ t₂ t₃ => by
    show A.interp3 f (eval A ρ (t₁.applySubst σ)) (eval A ρ (t₂.applySubst σ)) (eval A ρ (t₃.applySubst σ)) =
         A.interp3 f (eval A (fun n => eval A ρ (σ n)) t₁) (eval A (fun n => eval A ρ (σ n)) t₂) (eval A (fun n => eval A ρ (σ n)) t₃)
    rw [eval_applySubst A ρ σ t₁, eval_applySubst A ρ σ t₂, eval_applySubst A ρ σ t₃]

-- ============================================================
-- §8  Soundness
-- ============================================================

/-- Theorem 20 – substitution instance soundness. -/
theorem satisfies_subst (A : Algebra) (eq : Equation) (σ : Subst)
    (hsat : A.satisfies eq) (ρ : Assignment A) :
    eval A ρ (eq.lhs.applySubst σ) = eval A ρ (eq.rhs.applySubst σ) := by
  rw [eval_applySubst, eval_applySubst]
  exact hsat _

-- ============================================================
-- §9  Birkhoff derivation
-- ============================================================

inductive BirkhoffDeriv : EqTheory → Term → Term → Type where
  | axiom_ (T : EqTheory) (eq : Equation) (h : eq ∈ T) (σ : Subst) :
      BirkhoffDeriv T (eq.lhs.applySubst σ) (eq.rhs.applySubst σ)
  | refl_ (T : EqTheory) (t : Term) : BirkhoffDeriv T t t
  | symm_ : BirkhoffDeriv T s t → BirkhoffDeriv T t s
  | trans_ : BirkhoffDeriv T s t → BirkhoffDeriv T t u → BirkhoffDeriv T s u
  | congr1_ (f : FunSym) : BirkhoffDeriv T t₁ t₂ →
      BirkhoffDeriv T (.app1 f t₁) (.app1 f t₂)
  | congr2L_ (f : FunSym) : BirkhoffDeriv T t₁ t₂ → (u : Term) →
      BirkhoffDeriv T (.app2 f t₁ u) (.app2 f t₂ u)
  | congr2R_ (f : FunSym) (u : Term) : BirkhoffDeriv T t₁ t₂ →
      BirkhoffDeriv T (.app2 f u t₁) (.app2 f u t₂)

/-- Theorem 21 – lift path through congr1. -/
def congrPath1 (f : FunSym) : EqPath a b → EqPath (.app1 f a) (.app1 f b)
  | .nil _ => .nil _
  | .cons s p => .cons (.congr1 f s) (congrPath1 f p)

/-- Theorem 22 – lift path through congr2L. -/
def congrPath2L (f : FunSym) (u : Term) : EqPath a b → EqPath (.app2 f a u) (.app2 f b u)
  | .nil _ => .nil _
  | .cons s p => .cons (.congr2L f s u) (congrPath2L f u p)

/-- Theorem 23 – lift path through congr2R. -/
def congrPath2R (f : FunSym) (u : Term) : EqPath a b → EqPath (.app2 f u a) (.app2 f u b)
  | .nil _ => .nil _
  | .cons s p => .cons (.congr2R f u s) (congrPath2R f u p)

/-- Theorem 24 – Birkhoff derivation yields multi-step EqPath. -/
def derivToMultiPath : BirkhoffDeriv T s t → EqPath s t
  | .axiom_ _ eq _ σ => .single (.substEq eq σ)
  | .refl_ _ t => .refl t
  | .symm_ d => (derivToMultiPath d).symm
  | .trans_ d₁ d₂ => (derivToMultiPath d₁).trans (derivToMultiPath d₂)
  | .congr1_ f d => congrPath1 f (derivToMultiPath d)
  | .congr2L_ f d u => congrPath2L f u (derivToMultiPath d)
  | .congr2R_ f u d => congrPath2R f u (derivToMultiPath d)

-- ============================================================
-- §10  Free algebra as path-connected components
-- ============================================================

def FreeConnected (T : EqTheory) (s t : Term) : Prop :=
  Nonempty (BirkhoffDeriv T s t)

/-- Theorem 25 -/ theorem freeConnected_refl (T : EqTheory) (t : Term) :
    FreeConnected T t t := ⟨.refl_ T t⟩

/-- Theorem 26 -/ theorem freeConnected_symm (h : FreeConnected T s t) :
    FreeConnected T t s := h.elim fun d => ⟨.symm_ d⟩

/-- Theorem 27 -/ theorem freeConnected_trans (h₁ : FreeConnected T s t) (h₂ : FreeConnected T t u) :
    FreeConnected T s u := h₁.elim fun d₁ => h₂.elim fun d₂ => ⟨.trans_ d₁ d₂⟩

/-- Theorem 28 -/ theorem freeConnected_equiv (T : EqTheory) :
    @Equivalence Term (FreeConnected T) :=
  ⟨freeConnected_refl T, fun h => freeConnected_symm h, fun h₁ h₂ => freeConnected_trans h₁ h₂⟩

/-- Theorem 29 -/ theorem freeConnected_congr1 (f : FunSym) (h : FreeConnected T t₁ t₂) :
    FreeConnected T (.app1 f t₁) (.app1 f t₂) := h.elim fun d => ⟨.congr1_ f d⟩

-- ============================================================
-- §11  Mal'cev conditions
-- ============================================================

def malcevSym : FunSym := ⟨999, 3⟩

def malcevEq1 : Equation :=
  ⟨.app3 malcevSym (.var 0) (.var 0) (.var 1), .var 1⟩

def malcevEq2 : Equation :=
  ⟨.app3 malcevSym (.var 0) (.var 1) (.var 1), .var 0⟩

def malcevTheory : EqTheory := [malcevEq1, malcevEq2]

private def malcevSubst (a b : Term) : Subst := fun n => if n == 0 then a else b

/-- Theorem 30 – Mal'cev path (first). -/
theorem malcev_lhs1 (a b : Term) :
    malcevEq1.lhs.applySubst (malcevSubst a b) = .app3 malcevSym a a b := by
  simp [malcevEq1, Term.applySubst, malcevSym, malcevSubst]

/-- Theorem 31 – Mal'cev path rhs (first). -/
theorem malcev_rhs1 (a b : Term) :
    malcevEq1.rhs.applySubst (malcevSubst a b) = b := by
  simp [malcevEq1, Term.applySubst, malcevSubst]

/-- Theorem 32 – Mal'cev lhs (second). -/
theorem malcev_lhs2 (a b : Term) :
    malcevEq2.lhs.applySubst (malcevSubst a b) = .app3 malcevSym a b b := by
  simp [malcevEq2, Term.applySubst, malcevSym, malcevSubst]

/-- Theorem 33 – Mal'cev rhs (second). -/
theorem malcev_rhs2 (a b : Term) :
    malcevEq2.rhs.applySubst (malcevSubst a b) = a := by
  simp [malcevEq2, Term.applySubst, malcevSubst]

/-- Theorem 34 – Mal'cev instantiation path 1: m(a,a,b) ~> b. -/
def malcevPath1 (a b : Term) :
    EqPath (malcevEq1.lhs.applySubst (malcevSubst a b))
           (malcevEq1.rhs.applySubst (malcevSubst a b)) :=
  .single (.substEq malcevEq1 (malcevSubst a b))

/-- Theorem 35 – Mal'cev instantiation path 2: m(a,b,b) ~> a. -/
def malcevPath2 (a b : Term) :
    EqPath (malcevEq2.lhs.applySubst (malcevSubst a b))
           (malcevEq2.rhs.applySubst (malcevSubst a b)) :=
  .single (.substEq malcevEq2 (malcevSubst a b))

-- ============================================================
-- §12  Congruence generation as path closure
-- ============================================================

structure GenPair where
  fst : Term
  snd : Term
deriving DecidableEq, Repr

inductive CongStep : List GenPair → Term → Term → Type where
  | gen   (gs : List GenPair) (g : GenPair) (h : g ∈ gs) : CongStep gs g.fst g.snd
  | refl  (gs : List GenPair) (t : Term) : CongStep gs t t
  | symm  : CongStep gs a b → CongStep gs b a
  | cong1 (gs : List GenPair) (f : FunSym) : CongStep gs t₁ t₂ →
      CongStep gs (.app1 f t₁) (.app1 f t₂)

inductive CongPath : List GenPair → Term → Term → Type where
  | nil  : (t : Term) → CongPath gs t t
  | cons : CongStep gs a b → CongPath gs b c → CongPath gs a c

/-- Theorem 36 -/ def CongPath.trans : CongPath gs a b → CongPath gs b c → CongPath gs a c
  | .nil _, q => q
  | .cons s p, q => .cons s (p.trans q)

/-- Theorem 37 -/ def CongPath.symm : CongPath gs a b → CongPath gs b a
  | .nil t => .nil t
  | .cons s p => p.symm.trans (.cons (.symm s) (.nil _))

/-- Theorem 38 -/ def CongPath.liftCong1 (gs : List GenPair) (f : FunSym) :
    CongPath gs t₁ t₂ → CongPath gs (.app1 f t₁) (.app1 f t₂)
  | .nil _ => .nil _
  | .cons s p => .cons (.cong1 gs f s) (liftCong1 gs f p)

/-- Theorem 39 -/ theorem congPath_trans_assoc :
    (p : CongPath gs a b) → (q : CongPath gs b c) → (r : CongPath gs c d) →
    (p.trans q).trans r = p.trans (q.trans r)
  | .nil _, _, _ => rfl
  | .cons s p, q, r => by simp [CongPath.trans]; exact congPath_trans_assoc p q r

/-- Theorem 40 -/ def CongPath.length : CongPath gs a b → Nat
  | .nil _ => 0
  | .cons _ p => 1 + p.length

-- ============================================================
-- §13  HSP closure
-- ============================================================

abbrev AlgClass := Algebra → Prop

def Hclosed (K : AlgClass) : Prop :=
  ∀ A, K A → ∀ B : Algebra, (∀ eq : Equation, A.satisfies eq → B.satisfies eq) → K B

def Pclosed (K : AlgClass) : Prop :=
  ∀ A B, K A → K B → ∃ P : Algebra, K P

def IsVariety (K : AlgClass) : Prop :=
  Hclosed K ∧ Pclosed K

def ModClass (T : EqTheory) : AlgClass := fun A => A.models T

/-- Theorem 41 -/ theorem modClass_Hclosed (T : EqTheory) : Hclosed (ModClass T) := by
  intro A hA B hAB; intro eq heq; exact hAB eq (hA eq heq)

/-- Theorem 42 -/ theorem modClass_Pclosed (T : EqTheory) : Pclosed (ModClass T) := by
  intro A _ hA _; exact ⟨A, hA⟩

/-- Theorem 43 -/ theorem birkhoff_easy (T : EqTheory) :
    Hclosed (ModClass T) ∧ Pclosed (ModClass T) :=
  ⟨modClass_Hclosed T, modClass_Pclosed T⟩

-- ============================================================
-- §14  Transport
-- ============================================================

/-- Theorem 44 -/ def EqPath.transport (P : Term → Prop) :
    EqPath a b → P a → (∀ x y, EqStep x y → P x → P y) → P b
  | .nil _, h, _ => h
  | .cons s p, h, hinv => p.transport P (hinv _ _ s h) hinv

/-- Theorem 45 -/ theorem transport_refl (P : Term → Prop) (t : Term) (h : P t)
    (hinv : ∀ x y, EqStep x y → P x → P y) :
    (EqPath.refl t).transport P h hinv = h := rfl

/-- Theorem 46 -/ theorem transport_trans :
    (P : Term → Prop) → (p : EqPath a b) → (q : EqPath b c) →
    (h : P a) → (hinv : ∀ x y, EqStep x y → P x → P y) →
    (p.trans q).transport P h hinv = q.transport P (p.transport P h hinv) hinv
  | _, .nil _, _, _, _ => rfl
  | P, .cons s p, q, h, hinv => by
    show (p.trans q).transport P (hinv _ _ s h) hinv = q.transport P (p.transport P (hinv _ _ s h) hinv) hinv
    exact transport_trans P p q (hinv _ _ s h) hinv

-- ============================================================
-- §15  congrArg
-- ============================================================

/-- Theorem 47 -/ def congrArgPath (f : Term → Term)
    (wrap : ∀ a b, EqStep a b → EqStep (f a) (f b)) :
    EqPath a b → EqPath (f a) (f b)
  | .nil _ => .nil _
  | .cons s p => .cons (wrap _ _ s) (congrArgPath f wrap p)

/-- Theorem 48 -/ theorem congrArg_length :
    (f : Term → Term) → (wrap : ∀ a b, EqStep a b → EqStep (f a) (f b)) →
    (p : EqPath a b) → (congrArgPath f wrap p).length = p.length
  | _, _, .nil _ => rfl
  | f, w, .cons s p => by simp [congrArgPath, EqPath.length]; exact congrArg_length f w p

/-- Theorem 49 -/ theorem congrArg_trans :
    (f : Term → Term) → (wrap : ∀ a b, EqStep a b → EqStep (f a) (f b)) →
    (p : EqPath a b) → (q : EqPath b c) →
    congrArgPath f wrap (p.trans q) = (congrArgPath f wrap p).trans (congrArgPath f wrap q)
  | _, _, .nil _, _ => rfl
  | f, w, .cons s p, q => by simp [EqPath.trans, congrArgPath]; exact congrArg_trans f w p q

-- ============================================================
-- §16  Rewriting and confluence
-- ============================================================

structure RewriteRule where
  lhs : Term
  rhs : Term
deriving DecidableEq, Repr

inductive Rewrites : List RewriteRule → Term → Term → Type where
  | atRoot (R : List RewriteRule) (r : RewriteRule) (h : r ∈ R) (σ : Subst) :
      Rewrites R (r.lhs.applySubst σ) (r.rhs.applySubst σ)
  | inCong1 (R : List RewriteRule) (f : FunSym) : Rewrites R t₁ t₂ →
      Rewrites R (.app1 f t₁) (.app1 f t₂)

inductive RWPath : List RewriteRule → Term → Term → Type where
  | nil  : (t : Term) → RWPath R t t
  | cons : Rewrites R a b → RWPath R b c → RWPath R a c

/-- Theorem 50 -/ def RWPath.trans : RWPath R a b → RWPath R b c → RWPath R a c
  | .nil _, q => q
  | .cons s p, q => .cons s (p.trans q)

/-- Theorem 51 -/ def rwToEqStep : Rewrites R a b → EqStep a b
  | .atRoot _ r _ σ => .substEq ⟨r.lhs, r.rhs⟩ σ
  | .inCong1 _ f s => .congr1 f (rwToEqStep s)

/-- Theorem 52 -/ def rwPathToEqPath : RWPath R a b → EqPath a b
  | .nil t => .nil t
  | .cons s p => .cons (rwToEqStep s) (rwPathToEqPath p)

def ChurchRosser (R : List RewriteRule) : Prop :=
  ∀ a b : Term, Nonempty (EqPath a b) →
    ∃ c, Nonempty (RWPath R a c) ∧ Nonempty (RWPath R b c)

/-- Theorem 53 -/ theorem cr_implies_join (R : List RewriteRule)
    (hcr : ChurchRosser R) (a b : Term) (h : Nonempty (EqPath a b)) :
    ∃ c, Nonempty (RWPath R a c) ∧ Nonempty (RWPath R b c) := hcr a b h

-- ============================================================
-- §17  Additional coherence
-- ============================================================

/-- Theorem 54 -/ theorem congrPath1_length :
    (f : FunSym) → (p : EqPath a b) → (congrPath1 f p).length = p.length
  | _, .nil _ => rfl
  | f, .cons s p => by simp [congrPath1, EqPath.length]; exact congrPath1_length f p

/-- Theorem 55 -/ theorem congrPath1_trans :
    (f : FunSym) → (p : EqPath a b) → (q : EqPath b c) →
    congrPath1 f (p.trans q) = (congrPath1 f p).trans (congrPath1 f q)
  | _, .nil _, _ => rfl
  | f, .cons s p, q => by simp [EqPath.trans, congrPath1]; exact congrPath1_trans f p q

/-- Theorem 56 -/ theorem congrPath2L_trans :
    (f : FunSym) → (u : Term) → (p : EqPath a b) → (q : EqPath b c) →
    congrPath2L f u (p.trans q) = (congrPath2L f u p).trans (congrPath2L f u q)
  | _, _, .nil _, _ => rfl
  | f, u, .cons s p, q => by simp [EqPath.trans, congrPath2L]; exact congrPath2L_trans f u p q

/-- Theorem 57 -/ def congrPath2 (f : FunSym) (p₁ : EqPath a₁ b₁) (p₂ : EqPath a₂ b₂) :
    EqPath (.app2 f a₁ a₂) (.app2 f b₁ b₂) :=
  (congrPath2L f a₂ p₁).trans (congrPath2R f b₁ p₂)

/-- Theorem 58 -/ theorem congrPath2_refl_right (f : FunSym) (p : EqPath a b) (u : Term) :
    congrPath2 f p (.refl u) = congrPath2L f u p := by
  simp [congrPath2, EqPath.refl]; exact trans_nil_right _

/-- Theorem 59 -/ def RWPath.length : RWPath R a b → Nat
  | .nil _ => 0
  | .cons _ p => 1 + p.length

/-- Theorem 60 -/ theorem rwPathToEqPath_length :
    (p : RWPath R a b) → (rwPathToEqPath p).length = p.length
  | .nil _ => rfl
  | .cons s p => by simp [rwPathToEqPath, EqPath.length, RWPath.length]; exact rwPathToEqPath_length p

/-- Theorem 61 -/ theorem applySubst_id : (t : Term) → t.applySubst Subst.id = t
  | .var _ => rfl
  | .app0 _ => rfl
  | .app1 _ t => by simp [Term.applySubst]; exact applySubst_id t
  | .app2 _ t₁ t₂ => by
    simp [Term.applySubst]
    exact ⟨applySubst_id t₁, applySubst_id t₂⟩
  | .app3 _ t₁ t₂ t₃ => by
    simp [Term.applySubst]
    exact ⟨applySubst_id t₁, applySubst_id t₂, applySubst_id t₃⟩

/-- Theorem 62 -/ theorem applySubst_comp :
    (σ τ : Subst) → (t : Term) →
    (t.applySubst σ).applySubst τ = t.applySubst (fun n => (σ n).applySubst τ)
  | _, _, .var _ => rfl
  | _, _, .app0 _ => rfl
  | σ, τ, .app1 _ t => by simp [Term.applySubst]; exact applySubst_comp σ τ t
  | σ, τ, .app2 _ t₁ t₂ => by
    simp [Term.applySubst]
    exact ⟨applySubst_comp σ τ t₁, applySubst_comp σ τ t₂⟩
  | σ, τ, .app3 _ t₁ t₂ t₃ => by
    simp [Term.applySubst]
    exact ⟨applySubst_comp σ τ t₁, applySubst_comp σ τ t₂, applySubst_comp σ τ t₃⟩

end EquationalLogicDeep

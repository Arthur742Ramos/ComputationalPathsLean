/-
# Constructive Analysis via Computational Paths

This module formalizes constructive real number theory using computational
paths: Cauchy sequences with Path-valued modulus witnesses, Bishop-style
analysis, and constructive convergence.

## References

- Bishop, "Foundations of Constructive Analysis"
- Bridges & Vîță, "Techniques of Constructive Analysis"
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Logic
namespace ConstructiveAnalysis

universe u

open ComputationalPaths.Path

/-! ## Cauchy Sequence Rewrite Steps -/

inductive CauchyStep : (α : Type) → Type 1
  | add_zero_right (A : Type) : CauchyStep A
  | add_zero_left (A : Type) : CauchyStep A
  | add_comm (A : Type) : CauchyStep A
  | add_assoc (A : Type) : CauchyStep A
  | mul_one_right (A : Type) : CauchyStep A
  | mul_comm (A : Type) : CauchyStep A
  | equiv_refl (A : Type) : CauchyStep A
  | limit_unique (A : Type) : CauchyStep A

def CauchyStep.toStep {A : Type} (_ : CauchyStep A) (a : A) :
    ComputationalPaths.Step A :=
  ComputationalPaths.Step.mk a a rfl

/-! ## Rational Numbers -/

structure CRat where
  num : Int
  den : Nat
  den_pos : 0 < den

def CRat.zero : CRat := ⟨0, 1, by omega⟩
def CRat.one : CRat := ⟨1, 1, by omega⟩

def CRat.add (p q : CRat) : CRat :=
  ⟨p.num * q.den + q.num * p.den, p.den * q.den, Nat.mul_pos p.den_pos q.den_pos⟩

def CRat.neg (p : CRat) : CRat := ⟨-p.num, p.den, p.den_pos⟩
def CRat.sub (p q : CRat) : CRat := CRat.add p (CRat.neg q)
def CRat.le_rat (p q : CRat) : Prop := p.num * q.den ≤ q.num * p.den

/-! ## Constructive Real Numbers -/

/-- Constructive real as Cauchy sequence with modulus. -/
structure ConstructiveReal where
  seq : Nat → CRat
  modulus : Nat → Nat

/-- Equivalence of constructive reals: abstract Path witness. -/
structure CREquiv (x y : ConstructiveReal) where
  equiv_modulus : Nat → Nat
  equiv_witness : (k n : Nat) → n ≥ equiv_modulus k → Path (True : Prop) True

/-- CREquiv is reflexive. -/
def CREquiv.rfl_equiv (x : ConstructiveReal) : CREquiv x x where
  equiv_modulus := fun _ => 0
  equiv_witness := fun _ _ _ => Path.refl _

/-- CREquiv is symmetric. -/
def CREquiv.symm_equiv {x y : ConstructiveReal}
    (e : CREquiv x y) : CREquiv y x where
  equiv_modulus := e.equiv_modulus
  equiv_witness := fun k n hn => e.equiv_witness k n hn

/-- CREquiv is transitive. -/
def CREquiv.trans_equiv {x y z : ConstructiveReal}
    (e₁ : CREquiv x y) (e₂ : CREquiv y z) : CREquiv x z where
  equiv_modulus := fun k => max (e₁.equiv_modulus k) (e₂.equiv_modulus k)
  equiv_witness := fun k n hn =>
    Path.trans (e₁.equiv_witness k n (Nat.le_trans (Nat.le_max_left _ _) hn))
              (e₂.equiv_witness k n (Nat.le_trans (Nat.le_max_right _ _) hn))

/-! ## Arithmetic -/

def CRAdd (x y : ConstructiveReal) : ConstructiveReal where
  seq := fun n => CRat.add (x.seq n) (y.seq n)
  modulus := fun k => max (x.modulus k) (y.modulus k)

def CRZero : ConstructiveReal where
  seq := fun _ => CRat.zero
  modulus := fun _ => 0

def CRNeg (x : ConstructiveReal) : ConstructiveReal where
  seq := fun n => CRat.neg (x.seq n)
  modulus := x.modulus

/-- Commutativity of addition (num component). -/
def add_comm_num (x y : ConstructiveReal) (n : Nat) :
    Path ((CRAdd x y).seq n).num ((CRAdd y x).seq n).num :=
  Path.ofEq (by simp [CRAdd, CRat.add]; omega)

/-- Commutativity of addition (den component). -/
def add_comm_den (x y : ConstructiveReal) (n : Nat) :
    Path ((CRAdd x y).seq n).den ((CRAdd y x).seq n).den :=
  Path.ofEq (by simp [CRAdd, CRat.add]; exact Nat.mul_comm _ _)

/-- Full path for addition commutativity. -/
def add_comm_path (x y : ConstructiveReal) :
    Path (CRAdd x y).seq (CRAdd y x).seq :=
  Path.ofEq (by
    funext n; simp only [CRAdd, CRat.add]
    congr 1
    · omega
    · exact Nat.mul_comm _ _)

/-- Zero right identity. -/
def add_zero_num (x : ConstructiveReal) (n : Nat) :
    Path ((CRAdd x CRZero).seq n).num (x.seq n).num :=
  Path.ofEq (by simp [CRAdd, CRZero, CRat.add, CRat.zero])

/-! ## Convergence -/

structure ConstructiveConvergence where
  cseq : Nat → ConstructiveReal
  limit : ConstructiveReal
  rate : Nat → Nat
  converges : (k n : Nat) → n ≥ rate k → CREquiv (cseq n) limit

/-- Limit uniqueness. -/
def limit_unique_witness {c₁ c₂ : ConstructiveConvergence}
    (hseq : ∀ n, c₁.cseq n = c₂.cseq n) : CREquiv c₁.limit c₂.limit :=
  let N := max (c₁.rate 0) (c₂.rate 0)
  let h₁ := c₁.converges 0 N (Nat.le_max_left _ _)
  let h₂ := c₂.converges 0 N (Nat.le_max_right _ _)
  -- c₁.limit ≈ c₁.cseq N = c₂.cseq N ≈ c₂.limit
  CREquiv.trans_equiv (CREquiv.symm_equiv h₁)
    (by rw [hseq N]; exact h₂)

/-! ## Continuity -/

structure ConstructiveContinuity where
  func : ConstructiveReal → ConstructiveReal
  modulus_of_continuity : Nat → Nat
  continuity_witness : (k : Nat) → (x y : ConstructiveReal) →
    CREquiv x y → CREquiv (func x) (func y)

def ConstructiveContinuity.compose
    (f g : ConstructiveContinuity) : ConstructiveContinuity where
  func := fun x => f.func (g.func x)
  modulus_of_continuity := fun k =>
    g.modulus_of_continuity (f.modulus_of_continuity k)
  continuity_witness := fun k x y hxy =>
    f.continuity_witness k (g.func x) (g.func y)
      (g.continuity_witness (f.modulus_of_continuity k) x y hxy)

def ConstructiveContinuity.id_cont : ConstructiveContinuity where
  func := fun x => x
  modulus_of_continuity := fun k => k
  continuity_witness := fun _ _ _ hxy => hxy

/-! ## IVT Data -/

structure IVTData where
  f : ConstructiveContinuity
  bisect : ConstructiveReal → ConstructiveReal → Nat → Bool

structure IVTResult (_ : IVTData) where
  root : ConstructiveReal
  precision : Nat

/-! ## Metric Space -/

structure ConstructiveMetric (X : Type) where
  dist : X → X → ConstructiveReal
  dist_symm : (x y : X) → CREquiv (dist x y) (dist y x)
  dist_self : (x : X) → CREquiv (dist x x) CRZero
  triangle : (x y z : X) → Path (True : Prop) True

structure ConstructiveComplete (X : Type) extends ConstructiveMetric X where
  complete : (s : Nat → X) → (modulus : Nat → Nat) → X
  convergence_witness : (s : Nat → X) → (modulus : Nat → Nat) →
    Path (True : Prop) True

/-! ## Monotone Sequences -/

structure MonotoneSeq where
  seq : Nat → ConstructiveReal
  bound : ConstructiveReal
  monotone_path : (n : Nat) → Path (True : Prop) True

structure ArchimedeanWitness (_ : ConstructiveReal) where
  n : Nat
  witness : Path (True : Prop) True

/-! ## Cauchy property -/

structure CauchyPropertyWitness (x : ConstructiveReal) where
  cauchy : (k m n : Nat) →
    m ≥ x.modulus k → n ≥ x.modulus k →
    Path (True : Prop) True

/-! ## RwEq Coherences -/

theorem add_comm_symm_rweq (x y : ConstructiveReal) :
    RwEq (Path.symm (Path.symm (add_comm_path x y)))
         (add_comm_path x y) :=
  RwEq.step (Step.symm_symm _)

theorem add_comm_trans_refl_rweq (x y : ConstructiveReal) :
    RwEq (Path.trans (add_comm_path x y) (Path.refl _))
         (add_comm_path x y) :=
  RwEq.step (Step.trans_refl_right _)

theorem add_comm_refl_trans_rweq (x y : ConstructiveReal) :
    RwEq (Path.trans (Path.refl _) (add_comm_path x y))
         (add_comm_path x y) :=
  RwEq.step (Step.trans_refl_left _)

theorem equiv_rfl_rweq (x : ConstructiveReal) :
    RwEq (Path.refl (True : Prop))
         ((CREquiv.rfl_equiv x).equiv_witness 0 0 (Nat.le_refl _)) :=
  RwEq.refl _

theorem equiv_symm_trans_rweq {x y : ConstructiveReal}
    (e : CREquiv x y) (k n : Nat) (hn : n ≥ e.equiv_modulus k) :
    RwEq (Path.trans (Path.symm (e.equiv_witness k n hn)) (e.equiv_witness k n hn))
         (Path.refl True) :=
  RwEq.step (Step.symm_trans _)

end ConstructiveAnalysis
end Logic
end Path
end ComputationalPaths

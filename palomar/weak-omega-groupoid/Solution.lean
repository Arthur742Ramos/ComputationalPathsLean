import Mathlib.Data.List.Basic

/-!
# Computational paths: a proof-relevant weak omega-groupoid boundary

This file is an independent kernel-checked solution to `Challenge.lean`.
It repeats the statement surface so that the Palomar comparator can check the
formalization without importing repository-local modules.  The boundary is
deliberately focused: it formalizes the proof-irrelevance contraction and the
explicit coherence routes highlighted in the accepted paper, rather than
claiming to reproduce every application in that paper.
-/

namespace ComputationalPaths.PalomarWeakOmegaGroupoid

universe u

noncomputable section

structure Path (A : Type u) (a b : A) where
  trace : List (A × A)
  proof : a = b

namespace Path

def refl (a : A) : Path A a a := ⟨[], rfl⟩

def ofEq {a b : A} (h : a = b) : Path A a b := ⟨[(a, b)], h⟩

def trans {a b c : A} (p : Path A a b) (q : Path A b c) : Path A a c :=
  ⟨p.trace ++ q.trace, p.proof.trans q.proof⟩

def symm {a b : A} (p : Path A a b) : Path A b a :=
  ⟨p.trace.reverse.map (fun x => (x.2, x.1)), p.proof.symm⟩

end Path

/-! The groupoid fragment of the path-rewrite system. -/

inductive Step {A : Type u} : {a b : A} →
    Path A a b → Path A a b → Type u where
  | trans_assoc {a b c d : A} (p : Path A a b) (q : Path A b c)
      (r : Path A c d) :
      Step (Path.trans (Path.trans p q) r)
        (Path.trans p (Path.trans q r))
  | trans_refl_left {a b : A} (p : Path A a b) :
      Step (Path.trans (Path.refl a) p) p
  | trans_refl_right {a b : A} (p : Path A a b) :
      Step (Path.trans p (Path.refl b)) p
  | trans_symm {a b : A} (p : Path A a b) :
      Step (Path.trans p (Path.symm p)) (Path.refl a)
  | symm_trans {a b : A} (p : Path A a b) :
      Step (Path.trans (Path.symm p) p) (Path.refl b)
  | trans_congr_left {a b c : A} {p p' : Path A a b}
      (q : Path A b c) (s : Step p p') :
      Step (Path.trans p q) (Path.trans p' q)
  | trans_congr_right {a b c : A} (p : Path A a b)
      {q q' : Path A b c} (s : Step q q') :
      Step (Path.trans p q) (Path.trans p q')

inductive RwEq {A : Type u} : {a b : A} →
    Path A a b → Path A a b → Type u where
  | refl (p : Path A a b) : RwEq p p
  | step {p q : Path A a b} : Step p q → RwEq p q
  | symm {p q : Path A a b} : RwEq p q → RwEq q p
  | trans {p q r : Path A a b} : RwEq p q → RwEq q r → RwEq p r

abbrev RwProp {A : Type u} {a b : A} (p q : Path A a b) : Prop :=
  Nonempty (RwEq p q)

def RwEq.stepCount {A : Type u} {a b : A} {p q : Path A a b} :
    RwEq p q → Nat
  | .refl _ => 0
  | .step _ => 1
  | .symm h => RwEq.stepCount h
  | .trans h₁ h₂ => RwEq.stepCount h₁ + RwEq.stepCount h₂

def whiskerRight {A : Type u} {a b c : A}
    {p p' : Path A a b} (h : RwEq p p') (q : Path A b c) :
    RwEq (Path.trans p q) (Path.trans p' q) := by
  induction h with
  | refl p => exact .refl _
  | step s => exact .step (.trans_congr_left q s)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

def whiskerLeft {A : Type u} {a b c : A}
    (p : Path A a b) {q q' : Path A b c} (h : RwEq q q') :
    RwEq (Path.trans p q) (Path.trans p q') := by
  induction h with
  | refl q => exact .refl _
  | step s => exact .step (.trans_congr_right p s)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

def vcomp {A : Type u} {a b : A} {p q r : Path A a b} :
    RwEq p q → RwEq q r → RwEq p r := RwEq.trans

def hcomp {A : Type u} {a b c : A}
    {p p' : Path A a b} {q q' : Path A b c} (h : RwEq p p')
    (k : RwEq q q') : RwEq (Path.trans p q) (Path.trans p' q') :=
  RwEq.trans (whiskerRight h q) (whiskerLeft p' k)

def hcompAlt {A : Type u} {a b c : A}
    {p p' : Path A a b} {q q' : Path A b c} (h : RwEq p p')
    (k : RwEq q q') : RwEq (Path.trans p q) (Path.trans p' q') :=
  RwEq.trans (whiskerLeft p k) (whiskerRight h q')

/-! The paper's proof-relevant 3-cells and the uniform higher tail. -/

inductive MetaStep3 {A : Type u} : {a b : A} → {p q : Path A a b} →
    RwEq p q → RwEq p q → Type u where
  | rweq_transport {d e : RwEq p q}
      (h : (⟨d⟩ : RwProp p q) = ⟨e⟩) : MetaStep3 d e
  | pentagon {a b c d e : A} (f : Path A a b) (g : Path A b c)
      (h : Path A c d) (k : Path A d e) :
      MetaStep3
        (vcomp
          (.step (.trans_assoc (Path.trans f g) h k))
          (.step (.trans_assoc f g (Path.trans h k))))
        (vcomp
          (vcomp
            (.step (.trans_congr_left k (.trans_assoc f g h)))
            (.step (.trans_assoc f (Path.trans g h) k)))
          (.step (.trans_congr_right f (.trans_assoc g h k))))
  | triangle {a b c : A} (f : Path A a b) (g : Path A b c) :
      MetaStep3
        (vcomp
          (.step (.trans_assoc f (Path.refl b) g))
          (.step (.trans_congr_right f (.trans_refl_left g))))
        (.step (.trans_congr_left g (.trans_refl_right f)))
  | interchange {a b c : A}
      {p p' : Path A a b} {q q' : Path A b c}
      (h : RwEq p p') (k : RwEq q q') :
      MetaStep3 (hcomp h k) (hcompAlt h k)

inductive Derivation3 {A : Type u} {a b : A} {p q : Path A a b} :
    RwEq p q → RwEq p q → Type u where
  | refl (d : RwEq p q) : Derivation3 d d
  | step {d e : RwEq p q} : MetaStep3 d e → Derivation3 d e
  | inv {d e : RwEq p q} : Derivation3 d e → Derivation3 e d
  | vcomp {d e f : RwEq p q} :
      Derivation3 d e → Derivation3 e f → Derivation3 d f

inductive HigherCell {T : Type u} : T → T → Type u where
  | refl (x : T) : HigherCell x x
  | step {x y : T}
      (h : (⟨x⟩ : Nonempty T) = ⟨y⟩) : HigherCell x y
  | inv {x y : T} : HigherCell x y → HigherCell y x
  | vcomp {x y z : T} : HigherCell x y → HigherCell y z → HigherCell x z

def pentagonRight {A : Type u} {a b c d e : A}
    (f : Path A a b) (g : Path A b c) (h : Path A c d) (k : Path A d e) :
    RwEq
      (Path.trans (Path.trans (Path.trans f g) h) k)
      (Path.trans f (Path.trans g (Path.trans h k))) :=
  .trans (.step (.trans_assoc (Path.trans f g) h k))
    (.step (.trans_assoc f g (Path.trans h k)))

def pentagonLeft {A : Type u} {a b c d e : A}
    (f : Path A a b) (g : Path A b c) (h : Path A c d) (k : Path A d e) :
    RwEq
      (Path.trans (Path.trans (Path.trans f g) h) k)
      (Path.trans f (Path.trans g (Path.trans h k))) :=
  .trans
    (.trans (.step (.trans_congr_left k (.trans_assoc f g h)))
      (.step (.trans_assoc f (Path.trans g h) k)))
    (.step (.trans_congr_right f (.trans_assoc g h k)))

def triangleLong {A : Type u} {a b c : A}
    (f : Path A a b) (g : Path A b c) :
    RwEq (Path.trans (Path.trans f (Path.refl b)) g)
      (Path.trans f g) :=
  .trans (.step (.trans_assoc f (Path.refl b) g))
    (.step (.trans_congr_right f (.trans_refl_left g)))

def triangleShort {A : Type u} {a b c : A}
    (f : Path A a b) (g : Path A b c) :
    RwEq (Path.trans (Path.trans f (Path.refl b)) g)
      (Path.trans f g) :=
  .step (.trans_congr_left g (.trans_refl_right f))

structure WeakOmegaGroupoidCertificate (A : Type u) where
  id₁ : (a : A) → Path A a a
  comp₁ : {a b c : A} → Path A a b → Path A b c → Path A a c
  inv₁ : {a b : A} → Path A a b → Path A b a
  associator : ∀ {a b c d : A} (p : Path A a b) (q : Path A b c)
    (r : Path A c d), RwEq (comp₁ (comp₁ p q) r) (comp₁ p (comp₁ q r))
  leftUnit : ∀ {a b : A} (p : Path A a b), RwEq (comp₁ (id₁ a) p) p
  rightUnit : ∀ {a b : A} (p : Path A a b), RwEq (comp₁ p (id₁ b)) p
  leftInverse : ∀ {a b : A} (p : Path A a b), RwEq (comp₁ (inv₁ p) p) (id₁ b)
  rightInverse : ∀ {a b : A} (p : Path A a b), RwEq (comp₁ p (inv₁ p)) (id₁ a)
  contract₃ : ∀ {a b : A} {p q : Path A a b} (d e : RwEq p q), Derivation3 d e
  contract₄ : ∀ {a b : A} {p q : Path A a b} {d e : RwEq p q}
    (m n : Derivation3 d e), HigherCell m n
  pentagon : ∀ {a b c d e : A} (f : Path A a b) (g : Path A b c)
    (h : Path A c d) (k : Path A d e),
    Derivation3 (pentagonRight f g h k) (pentagonLeft f g h k)
  triangle : ∀ {a b c : A} (f : Path A a b) (g : Path A b c),
    Derivation3 (triangleLong f g) (triangleShort f g)
  interchange : ∀ {a b c : A} {p p' : Path A a b}
    {q q' : Path A b c} (α : RwEq p p') (β : RwEq q q'),
    Derivation3 (hcomp α β) (hcompAlt α β)
  eckmannHilton : ∀ {a : A} (α β : RwEq (Path.refl a) (Path.refl a)),
    Derivation3 (vcomp α β) (vcomp β α)

theorem trace_is_observable {A : Type u} (a : A) :
    Path.ofEq (rfl : a = a) ≠ Path.refl a := by
  intro h
  have ht := congrArg (fun p => p.trace) h
  simp [Path.ofEq, Path.refl] at ht

theorem groupoid_laws {A : Type u} {a b : A} (p : Path A a b) :
    RwProp (Path.trans (Path.refl a) p) p ∧
    RwProp (Path.trans p (Path.refl b)) p ∧
    RwProp (Path.trans p (Path.symm p)) (Path.refl a) ∧
    RwProp (Path.trans (Path.symm p) p) (Path.refl b) := by
  constructor
  · exact ⟨.step (.trans_refl_left p)⟩
  constructor
  · exact ⟨.step (.trans_refl_right p)⟩
  constructor
  · exact ⟨.step (.trans_symm p)⟩
  · exact ⟨.step (.symm_trans p)⟩

def contractibility3 {A : Type u} {a b : A} {p q : Path A a b}
    (d e : RwEq p q) : Derivation3 d e :=
  .step (.rweq_transport (Subsingleton.elim _ _))

def contractibilityHigher {T : Type u} (x y : T) : HigherCell x y :=
  .step (Subsingleton.elim _ _)

theorem pentagon_route_counts {A : Type u} {a b c d e : A}
    (f : Path A a b) (g : Path A b c) (h : Path A c d) (k : Path A d e) :
    RwEq.stepCount (pentagonRight f g h k) = 2 ∧
      RwEq.stepCount (pentagonLeft f g h k) = 3 := by
  constructor <;> rfl

def pentagon_coherence {A : Type u} {a b c d e : A}
    (f : Path A a b) (g : Path A b c) (h : Path A c d) (k : Path A d e) :
    Derivation3 (pentagonRight f g h k) (pentagonLeft f g h k) := by
  simpa [pentagonRight, pentagonLeft, vcomp] using
    (Derivation3.step (.pentagon f g h k))

def triangle_coherence {A : Type u} {a b c : A}
    (f : Path A a b) (g : Path A b c) :
    Derivation3 (triangleLong f g) (triangleShort f g) := by
  simpa [triangleLong, triangleShort, vcomp] using
    (Derivation3.step (.triangle f g))

def interchange_coherence {A : Type u} {a b c : A}
    {p p' : Path A a b} {q q' : Path A b c}
    (α : RwEq p p') (β : RwEq q q') :
    Derivation3 (hcomp α β) (hcompAlt α β) :=
  .step (.interchange α β)

def eckmann_hilton_coherence {A : Type u} {a : A}
    (α β : RwEq (Path.refl a) (Path.refl a)) :
    Derivation3 (vcomp α β) (vcomp β α) :=
  contractibility3 _ _

theorem computational_paths_form_weak_omega_groupoid (A : Type u) :
    Nonempty (WeakOmegaGroupoidCertificate A) := by
  exact ⟨{
    id₁ := fun a => Path.refl a
    comp₁ := Path.trans
    inv₁ := Path.symm
    associator := fun p q r => .step (.trans_assoc p q r)
    leftUnit := fun p => .step (.trans_refl_left p)
    rightUnit := fun p => .step (.trans_refl_right p)
    leftInverse := fun p => .step (.symm_trans p)
    rightInverse := fun p => .step (.trans_symm p)
    contract₃ := contractibility3
    contract₄ := fun m n => contractibilityHigher m n
    pentagon := pentagon_coherence
    triangle := triangle_coherence
    interchange := interchange_coherence
    eckmannHilton := eckmann_hilton_coherence
  }⟩

end

end ComputationalPaths.PalomarWeakOmegaGroupoid

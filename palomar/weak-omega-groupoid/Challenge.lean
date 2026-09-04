import Mathlib.Data.List.Basic

/-!
# A proof-relevant weak omega-groupoid core for computational paths

This is the compact, independently auditable boundary selected from the
accepted paper *Computational Paths Form a Weak omega-Groupoid: A Constructive
Proof*.  It keeps the distinction that matters for the paper:

* `Path` is data carrying an equality proof and an observable trace;
* `RwEq` is the Type-valued symmetric-reflexive-transitive rewrite closure,
  serving as the proof-relevant 2-cell data;
* `RwProp` forgets that data to the mere proposition that a rewrite witness
  exists; and
* the only primitive 3-cell is transport along equality of those propositions.

Consequently, contractibility at level 3, the pentagon, triangle, full
four-2-cell interchange, and Eckmann--Hilton coherence are derived from the
same proof-irrelevance construction.  Level 4 and the uniform higher tail are
also represented by explicit derivation types.  This is a focused core
boundary, not a claim that this short Challenge reproduces every application,
confluence lemma, or source-level presentation in the 49-page manuscript.
-/

namespace ComputationalPaths.PalomarWeakOmegaGroupoid

universe u

noncomputable section

/-- A computational path is a finite observable trace carrying `a = b`. -/
structure Path (A : Type u) (a b : A) where
  trace : List (A × A)
  proof : a = b

namespace Path

/-- The empty computational path. -/
def refl (a : A) : Path A a a := ⟨[], rfl⟩

/-- A one-entry path carrying an ambient equality. -/
def ofEq {a b : A} (h : a = b) : Path A a b := ⟨[(a, b)], h⟩

/-- Concatenation of traces and endpoint proofs. -/
def trans {a b c : A} (p : Path A a b) (q : Path A b c) : Path A a c :=
  ⟨p.trace ++ q.trace, p.proof.trans q.proof⟩

/-- Reversal of both the trace and its endpoint equality. -/
def symm {a b : A} (p : Path A a b) : Path A b a :=
  ⟨p.trace.reverse.map (fun x => (x.2, x.1)), p.proof.symm⟩

end Path

/-! ## Proof-relevant rewrite cells -/

/-- Primitive rewrite rules on computational paths. -/
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

/-! `RwEq` is the concrete derivation data underlying the mere relation `RwProp`.
    The alias `Derivation2` makes the dimension of this cell explicit. -/

/-- Type-valued symmetric-reflexive-transitive closure of `Step`. -/
inductive RwEq {A : Type u} : {a b : A} →
    Path A a b → Path A a b → Type u where
  | refl (p : Path A a b) : RwEq p p
  | step {p q : Path A a b} : Step p q → RwEq p q
  | symm {p q : Path A a b} : RwEq p q → RwEq q p
  | trans {p q r : Path A a b} : RwEq p q → RwEq q r → RwEq p r

/-- A proof-relevant 2-cell: a concrete rewrite derivation between paths. -/
abbrev Derivation2 {A : Type u} {a b : A} (p q : Path A a b) := RwEq p q

/-- The mere proposition that a proof-relevant rewrite derivation exists. -/
abbrev RwProp {A : Type u} {a b : A} (p q : Path A a b) : Prop :=
  Nonempty (Derivation2 p q)

/-- Count generating rewrite steps, ignoring symmetry and composition nodes. -/
def RwEq.stepCount {A : Type u} {a b : A} {p q : Path A a b} :
    RwEq p q → Nat
  | .refl _ => 0
  | .step _ => 1
  | .symm h => RwEq.stepCount h
  | .trans h₁ h₂ => RwEq.stepCount h₁ + RwEq.stepCount h₂

/-- Transport a rewrite derivation by post-composition. -/
def whiskerRight {A : Type u} {a b c : A}
    {p p' : Path A a b} (h : Derivation2 p p') (q : Path A b c) :
    Derivation2 (Path.trans p q) (Path.trans p' q) := by
  induction h with
  | refl p => exact .refl _
  | step s => exact .step (.trans_congr_left q s)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- Transport a rewrite derivation by pre-composition. -/
def whiskerLeft {A : Type u} {a b c : A}
    (p : Path A a b) {q q' : Path A b c} (h : Derivation2 q q') :
    Derivation2 (Path.trans p q) (Path.trans p q') := by
  induction h with
  | refl q => exact .refl _
  | step s => exact .step (.trans_congr_right p s)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- Vertical composition of proof-relevant 2-cells. -/
def vcomp {A : Type u} {a b : A} {p q r : Path A a b} :
    Derivation2 p q → Derivation2 q r → Derivation2 p r := RwEq.trans

/-- Horizontal composition by whiskering and vertical composition. -/
def hcomp {A : Type u} {a b c : A}
    {p p' : Path A a b} {q q' : Path A b c} (α : Derivation2 p p')
    (β : Derivation2 q q') :
    Derivation2 (Path.trans p q) (Path.trans p' q') :=
  RwEq.trans (whiskerRight α q) (whiskerLeft p' β)

/-! ## Contractible higher cells -/

/-! The proof-irrelevance generator is the sole primitive 3-cell.  In
    particular, pentagon, triangle, and interchange are not constructors. -/

/-- The sole primitive 3-cell: transport across equality of `RwProp` values. -/
inductive MetaStep3 {A : Type u} : {a b : A} → {p q : Path A a b} →
    Derivation2 p q → Derivation2 p q → Type u where
  | rweq_transport {d e : Derivation2 p q}
      (h : (⟨d⟩ : RwProp p q) = ⟨e⟩) : MetaStep3 d e

/-- Explicit 3-cell derivations between parallel 2-cells. -/
inductive Derivation3 {A : Type u} {a b : A} {p q : Path A a b} :
    Derivation2 p q → Derivation2 p q → Type u where
  | refl (d : Derivation2 p q) : Derivation3 d d
  | step {d e : Derivation2 p q} : MetaStep3 d e → Derivation3 d e
  | inv {d e : Derivation2 p q} : Derivation3 d e → Derivation3 e d
  | vcomp {d e f : Derivation2 p q} :
      Derivation3 d e → Derivation3 e f → Derivation3 d f

/-! An explicit level-4 type is included so that the selected boundary is not
    merely a generic relation on an unnamed carrier. -/

/-- The level-4 truncation generator for parallel 3-cells. -/
inductive MetaStep4 {A : Type u} : {a b : A} → {p q : Path A a b} →
    {d e : Derivation2 p q} → Derivation3 d e → Derivation3 d e → Type u where
  | trunc_eq {m n : Derivation3 d e}
      (h : (⟨m⟩ : Nonempty (Derivation3 d e)) = ⟨n⟩) : MetaStep4 m n

/-- Explicit 4-cell derivations between parallel 3-cells. -/
inductive Derivation4 {A : Type u} {a b : A} {p q : Path A a b}
    {d e : Derivation2 p q} :
    Derivation3 d e → Derivation3 d e → Type u where
  | refl (m : Derivation3 d e) : Derivation4 m m
  | step {m n : Derivation3 d e} : MetaStep4 m n → Derivation4 m n
  | inv {m n : Derivation3 d e} : Derivation4 m n → Derivation4 n m
  | vcomp {m n k : Derivation3 d e} :
      Derivation4 m n → Derivation4 n k → Derivation4 m k

/-! The uniform tail is schematic in the carrier, but remains an explicit
    inductive derivation type at every level index. -/

/-- Indexed higher truncation generator for the schematic tail. -/
inductive MetaStepHigh (n : Nat) {T : Type u} : T → T → Type u where
  | trunc_eq {x y : T}
      (h : (⟨x⟩ : Nonempty T) = ⟨y⟩) : MetaStepHigh n x y

/-- Explicit derivations at each index of the higher tail. -/
inductive DerivationHigh (n : Nat) {T : Type u} : T → T → Type u where
  | refl (x : T) : DerivationHigh n x x
  | step {x y : T} : MetaStepHigh n x y → DerivationHigh n x y
  | inv {x y : T} : DerivationHigh n x y → DerivationHigh n y x
  | vcomp {x y z : T} :
      DerivationHigh n x y → DerivationHigh n y z → DerivationHigh n x z

/-! ## Explicit path-level routes -/

/-- The two-step left route around the associativity pentagon. -/
def pentagonLeft {A : Type u} {a b c d e : A}
    (f : Path A a b) (g : Path A b c) (h : Path A c d) (k : Path A d e) :
    Derivation2
      (Path.trans (Path.trans (Path.trans f g) h) k)
      (Path.trans f (Path.trans g (Path.trans h k))) :=
  .trans (.step (.trans_assoc (Path.trans f g) h k))
    (.step (.trans_assoc f g (Path.trans h k)))

/-- The three-step right route around the associativity pentagon. -/
def pentagonRight {A : Type u} {a b c d e : A}
    (f : Path A a b) (g : Path A b c) (h : Path A c d) (k : Path A d e) :
    Derivation2
      (Path.trans (Path.trans (Path.trans f g) h) k)
      (Path.trans f (Path.trans g (Path.trans h k))) :=
  .trans
    (.trans (.step (.trans_congr_left k (.trans_assoc f g h)))
      (.step (.trans_assoc f (Path.trans g h) k)))
    (.step (.trans_congr_right f (.trans_assoc g h k)))

/-- The associator-then-left-unitor route for the triangle. -/
def triangleLong {A : Type u} {a b c : A}
    (f : Path A a b) (g : Path A b c) :
    Derivation2 (Path.trans (Path.trans f (Path.refl b)) g)
      (Path.trans f g) :=
  .trans (.step (.trans_assoc f (Path.refl b) g))
    (.step (.trans_congr_right f (.trans_refl_left g)))

/-- The right-unitor route for the triangle. -/
def triangleShort {A : Type u} {a b c : A}
    (f : Path A a b) (g : Path A b c) :
    Derivation2 (Path.trans (Path.trans f (Path.refl b)) g)
      (Path.trans f g) :=
  .step (.trans_congr_left g (.trans_refl_right f))

/-! ## Selected mathematical statements -/

/-- A nonempty trace is distinguishable from the empty computational path. -/
theorem trace_is_observable {A : Type u} (a : A) :
    Path.ofEq (rfl : a = a) ≠ Path.refl a := by sorry

/-- Unit and inverse rewrite witnesses for every computational path. -/
theorem groupoid_laws {A : Type u} {a b : A} (p : Path A a b) :
    RwProp (Path.trans (Path.refl a) p) p ∧
    RwProp (Path.trans p (Path.refl b)) p ∧
    RwProp (Path.trans p (Path.symm p)) (Path.refl a) ∧
    RwProp (Path.trans (Path.symm p) p) (Path.refl b) := by sorry

/-- Contracts any two parallel proof-relevant 2-cells by equality of their
    `RwProp` projections.  This is the paper's central one-line construction,
    and no confluence or choice principle is used. -/
def contractibility3 {A : Type u} {a b : A} {p q : Path A a b}
    (d e : Derivation2 p q) : Derivation3 d e := by sorry

/-- Contracts any two parallel 3-cells with the explicit level-4 truncation
    generator. -/
def contractibility4 {A : Type u} {a b : A} {p q : Path A a b}
    {d e : Derivation2 p q} (m n : Derivation3 d e) : Derivation4 m n := by sorry

/-- Gives the uniform level-indexed higher contraction for the
    proof-irrelevant tail. -/
def contractibilityHigher (n : Nat) {T : Type u} (x y : T) :
    DerivationHigh n x y := by sorry

/-- Selected associativity, unit, and inverse laws for vertical 2-cell composition. -/
theorem derivation_groupoid_laws {A : Type u} {a b : A}
    {p q r s : Path A a b} (d₁ : Derivation2 p q) (d₂ : Derivation2 q r)
    (d₃ : Derivation2 r s) :
    Nonempty (Derivation3 (vcomp (vcomp d₁ d₂) d₃) (vcomp d₁ (vcomp d₂ d₃))) ∧
    Nonempty (Derivation3 (vcomp d₁ (.refl q)) d₁) ∧
    Nonempty (Derivation3 (vcomp (.symm d₁) d₁) (.refl q)) := by sorry

/-- The two selected pentagon routes have genuinely different derivation lengths. -/
theorem pentagon_route_counts {A : Type u} {a b c d e : A}
    (f : Path A a b) (g : Path A b c) (h : Path A c d) (k : Path A d e) :
    RwEq.stepCount (pentagonLeft f g h k) = 2 ∧
      RwEq.stepCount (pentagonRight f g h k) = 3 := by sorry

/-- These named coherences are derived witnesses, not primitive constructors:
    their two endpoints are parallel `Derivation2` values, so `contractibility3`
    supplies the 3-cell. -/

def pentagon_coherence {A : Type u} {a b c d e : A}
    (f : Path A a b) (g : Path A b c) (h : Path A c d) (k : Path A d e) :
    Derivation3 (pentagonLeft f g h k) (pentagonRight f g h k) := by sorry

def triangle_coherence {A : Type u} {a b c : A}
    (f : Path A a b) (g : Path A b c) :
    Derivation3 (triangleLong f g) (triangleShort f g) := by sorry

/-- Full interchange compares horizontal composition after vertical
    composition with vertical composition after horizontal composition. -/

def interchange_coherence {A : Type u} {a b c : A}
    {p p' p'' : Path A a b} {q q' q'' : Path A b c}
    (α : Derivation2 p p') (γ : Derivation2 p' p'')
    (β : Derivation2 q q') (δ : Derivation2 q' q'') :
    Derivation3 (hcomp (vcomp α γ) (vcomp β δ))
      (vcomp (hcomp α β) (hcomp γ δ)) := by sorry

/-- A derived Eckmann--Hilton witness for two endomorphism 2-cells. -/
def eckmann_hilton_coherence {A : Type u} {a : A}
    (α β : Derivation2 (Path.refl a) (Path.refl a)) :
    Derivation3 (vcomp α β) (vcomp β α) := by sorry

/-- The cell tower used by the paper's weak omega-groupoid construction.
    Dimensions 0--4 are named explicitly; the indexed tail records cells at
    every dimension at least 5. -/
def CellType (A : Type u) : Nat → Type u
  | 0 => A
  | 1 => Σ (a b : A), Path A a b
  | 2 => Σ (a b : A) (p q : Path A a b), Derivation2 p q
  | 3 => Σ (a b : A) (p q : Path A a b) (d e : Derivation2 p q),
      Derivation3 d e
  | 4 => Σ (a b : A) (p q : Path A a b) (d e : Derivation2 p q)
      (m n : Derivation3 d e), Derivation4 m n
  | k + 5 => Σ (a b : A) (p q : Path A a b) (d e : Derivation2 p q)
      (m₁ m₂ : Derivation3 d e) (c₁ c₂ : Derivation4 m₁ m₂),
      DerivationHigh k c₁ c₂

/-- The standard structural slice used here for the weak omega-groupoid
    theorem.  The path operations are the explicit definitions above; this
    record fixes the cell tower and the selected higher contractibility and
    coherence fields without claiming to encode every presentation of the
    Batanin--Leinster definition. -/
structure WeakOmegaGroupoidBoundary (A : Type u) where
  cells : (n : Nat) → Type u := CellType A
  contract₃ : ∀ {a b : A} {p q : Path A a b}
    (d e : Derivation2 p q), Derivation3 d e
  contract₄ : ∀ {a b : A} {p q : Path A a b} {d e : Derivation2 p q}
    (m n : Derivation3 d e), Derivation4 m n
  contractHigh : (n : Nat) → {T : Type u} → (x y : T) → DerivationHigh n x y
  pentagon : ∀ {a b c d e : A} (f : Path A a b) (g : Path A b c)
    (h : Path A c d) (k : Path A d e),
    Derivation3 (pentagonLeft f g h k) (pentagonRight f g h k)
  triangle : ∀ {a b c : A} (f : Path A a b) (g : Path A b c),
    Derivation3 (triangleLong f g) (triangleShort f g)
  interchange : ∀ {a b c : A} {p p' p'' : Path A a b}
    {q q' q'' : Path A b c} (α : Derivation2 p p') (γ : Derivation2 p' p'')
    (β : Derivation2 q q') (δ : Derivation2 q' q''),
    Derivation3 (hcomp (vcomp α γ) (vcomp β δ))
      (vcomp (hcomp α β) (hcomp γ δ))
  eckmannHilton : ∀ {a : A}
    (α β : Derivation2 (Path.refl a) (Path.refl a)),
    Derivation3 (vcomp α β) (vcomp β α)

/-- The canonical value of the selected weak omega-groupoid boundary. -/
def compPathOmegaGroupoidBoundary (A : Type u) : WeakOmegaGroupoidBoundary A := by sorry

theorem computational_paths_form_weak_omega_groupoid_boundary (A : Type u) :
    Nonempty (WeakOmegaGroupoidBoundary A) := ⟨compPathOmegaGroupoidBoundary A⟩

end

end ComputationalPaths.PalomarWeakOmegaGroupoid

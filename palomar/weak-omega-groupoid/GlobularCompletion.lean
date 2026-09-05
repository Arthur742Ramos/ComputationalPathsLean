import Solution

/-!
# Recursive globular completion of the computational-path 2-skeleton

This repairs the non-recursive indexed tail in the preliminary artifact.
The primitive universal filler is an explicit part of the chosen completion,
not a consequence of equality reflection or rewrite normalization. This file
does not assert an operadic weak omega-groupoid structure.
-/
namespace ComputationalPaths.PalomarWeakOmegaGroupoid.GlobularCompletion

universe u

/-- One level of a globular object, with its actual boundary carrier. -/
structure Layer where
  Obj : Type u
  Arr : Type u
  source : Arr → Obj
  target : Arr → Obj

/-- Parallel arrows have the same two endpoints. -/
def Parallel (L : Layer.{u}) (x y : L.Arr) : Prop :=
  L.source x = L.source y ∧ L.target x = L.target y

/-- A new cell includes its parallel boundary and explicit derivation data. -/
inductive CellDerivation (L : Layer.{u}) : L.Arr → L.Arr → Type u where
  | refl (x : L.Arr) : CellDerivation L x x
  | step {x y : L.Arr} (parallel : Parallel L x y)
      (irrelevance : (⟨x⟩ : Nonempty L.Arr) = ⟨y⟩) : CellDerivation L x y
  | inv {x y : L.Arr} : CellDerivation L x y → CellDerivation L y x
  | trans {x y z : L.Arr} :
      CellDerivation L x y → CellDerivation L y z → CellDerivation L x z

/-- Every intermediate derivation respects the fixed globular boundary. -/
theorem CellDerivation.parallel {L : Layer.{u}} {x y : L.Arr}
    (d : CellDerivation L x y) : Parallel L x y := by
  induction d with
  | refl _ => exact ⟨rfl, rfl⟩
  | step h _ => exact h
  | inv _ ih => exact ⟨ih.1.symm, ih.2.symm⟩
  | trans _ _ ih ih' => exact ⟨ih.1.trans ih'.1, ih.2.trans ih'.2⟩

structure Filler (L : Layer.{u}) where
  source : L.Arr
  target : L.Arr
  derivation : CellDerivation L source target

theorem Filler.parallel {L : Layer.{u}} (c : Filler L) :
    Parallel L c.source c.target := c.derivation.parallel

/-- Extend one layer; its arrows become the next layer's objects. -/
def extend (L : Layer.{u}) : Layer.{u} where
  Obj := L.Arr
  Arr := Filler L
  source := Filler.source
  target := Filler.target

/-- Total one-cells retain the submitted Path records. -/
abbrev One (A : Type u) := Σ (a b : A), Path A a b

/-- Total two-cells retain the submitted proof-relevant rewrite derivations. -/
abbrev Two (A : Type u) :=
  Σ (a b : A) (p q : Path A a b), Derivation2 p q

/-- The fixed 2-skeleton, with its actual path-valued boundaries. -/
def skeleton (A : Type u) : Layer.{u} where
  Obj := One A
  Arr := Two A
  source := fun x => ⟨x.1, x.2.1, x.2.2.1⟩
  target := fun x => ⟨x.1, x.2.1, x.2.2.2.1⟩

/-- Genuine iteration: every extension depends on the preceding layer. -/
def tower (A : Type u) : Nat → Layer.{u}
  | 0 => skeleton A
  | n + 1 => extend (tower A n)

/-- Cells at each dimension, preserving the original 0-, 1-, and 2-skeleton. -/
def Cell (A : Type u) : Nat → Type u
  | 0 => A
  | 1 => One A
  | n + 2 => (tower A n).Arr

/-- Source lowers the actual dimension by one. -/
def source {A : Type u} : (n : Nat) → Cell A (n + 1) → Cell A n
  | 0 => fun x => x.1
  | 1 => (skeleton A).source
  | n + 2 => (tower A (n + 1)).source

/-- Target lowers the actual dimension by one. -/
def target {A : Type u} : (n : Nat) → Cell A (n + 1) → Cell A n
  | 0 => fun x => x.2.1
  | 1 => (skeleton A).target
  | n + 2 => (tower A (n + 1)).target

theorem source_globular {A : Type u} (n : Nat) (c : Cell A (n + 2)) :
    source n (source (n + 1) c) = source n (target (n + 1) c) := by
  cases n with
  | zero => rfl
  | succ n => cases n <;> exact c.parallel.1

theorem target_globular {A : Type u} (n : Nat) (c : Cell A (n + 2)) :
    target n (source (n + 1) c) = target n (target (n + 1) c) := by
  cases n with
  | zero => rfl
  | succ n => cases n <;> exact c.parallel.2

/-- Chosen filler, only for a parallel boundary in the preceding layer. -/
def fill (L : Layer.{u}) (x y : L.Arr) (h : Parallel L x y) : Filler L :=
  ⟨x, y, .step h (Subsingleton.elim _ _)⟩

/-- Identity, inverse, and vertical composition preserve derivation syntax. -/
def identity (L : Layer.{u}) (x : L.Arr) : Filler L :=
  ⟨x, x, .refl x⟩

def inverse {L : Layer.{u}} (c : Filler L) : Filler L :=
  ⟨c.target, c.source, .inv c.derivation⟩

def compose {L : Layer.{u}} (c d : Filler L) (h : c.target = d.source) :
    Filler L where
  source := c.source
  target := d.target
  derivation := .trans c.derivation (h ▸ d.derivation)

theorem identity_boundary (L : Layer.{u}) (x : L.Arr) :
    (identity L x).source = x ∧ (identity L x).target = x := ⟨rfl, rfl⟩

theorem inverse_boundary {L : Layer.{u}} (c : Filler L) :
    (inverse c).source = c.target ∧ (inverse c).target = c.source := ⟨rfl, rfl⟩

theorem compose_boundary {L : Layer.{u}} (c d : Filler L)
    (h : c.target = d.source) :
    (compose c d h).source = c.source ∧
      (compose c d h).target = d.target := ⟨rfl, rfl⟩

/-- Identity cells at every dimension of the fixed tower. -/
def identityCell {A : Type u} : (n : Nat) → Cell A n → Cell A (n + 1)
  | 0 => fun a => ⟨a, a, Path.refl a⟩
  | 1 => fun x => ⟨x.1, x.2.1, x.2.2, x.2.2, .refl _⟩
  | n + 2 => identity (tower A n)

theorem identityCell_boundary {A : Type u} (n : Nat) (x : Cell A n) :
    source n (identityCell n x) = x ∧ target n (identityCell n x) = x := by
  cases n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n => cases n <;> exact ⟨rfl, rfl⟩

/-- Inversion at every positive dimension, retaining explicit inverse syntax. -/
def inverseCell {A : Type u} : (n : Nat) → Cell A (n + 1) → Cell A (n + 1)
  | 0 => fun x => ⟨x.2.1, x.1, Path.symm x.2.2⟩
  | 1 => fun x => ⟨x.1, x.2.1, x.2.2.2.1, x.2.2.1, .symm x.2.2.2.2⟩
  | _ + 2 => inverse

theorem inverseCell_boundary {A : Type u} (n : Nat) (x : Cell A (n + 1)) :
    source n (inverseCell n x) = target n x ∧
      target n (inverseCell n x) = source n x := by
  cases n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n => cases n <;> exact ⟨rfl, rfl⟩

/-- Fiberwise vertical composition of two-cells, using the actual RwEq data. -/
def composeTwo {A : Type u} {a b : A} {p q r : Path A a b}
    (d : Derivation2 p q) (e : Derivation2 q r) : Two A :=
  ⟨a, b, p, r, .trans d e⟩

/-- Parallel higher derivations have a chosen comparison one level above. -/
def compareDerivations {L : Layer.{u}} {x y : L.Arr}
    (d e : CellDerivation L x y) :
    CellDerivation (extend L) ⟨x, y, d⟩ ⟨x, y, e⟩ :=
  .step ⟨rfl, rfl⟩ (Subsingleton.elim _ _)

/-- Associativity of higher vertical composition, witnessed one dimension up. -/
def associativity {L : Layer.{u}} {w x y z : L.Arr}
    (a : CellDerivation L w x) (b : CellDerivation L x y)
    (c : CellDerivation L y z) :
    CellDerivation (extend L)
      ⟨w, z, .trans (.trans a b) c⟩ ⟨w, z, .trans a (.trans b c)⟩ :=
  compareDerivations _ _

/-- The two unit laws and inverse laws are comparisons, not raw equalities. -/
def unitLeft {L : Layer.{u}} {x y : L.Arr} (d : CellDerivation L x y) :
    CellDerivation (extend L) ⟨x, y, .trans (.refl x) d⟩ ⟨x, y, d⟩ :=
  compareDerivations _ _

def unitRight {L : Layer.{u}} {x y : L.Arr} (d : CellDerivation L x y) :
    CellDerivation (extend L) ⟨x, y, .trans d (.refl y)⟩ ⟨x, y, d⟩ :=
  compareDerivations _ _

def inverseLeft {L : Layer.{u}} {x y : L.Arr} (d : CellDerivation L x y) :
    CellDerivation (extend L) ⟨y, y, .trans (.inv d) d⟩ ⟨y, y, .refl y⟩ :=
  compareDerivations _ _

def inverseRight {L : Layer.{u}} {x y : L.Arr} (d : CellDerivation L x y) :
    CellDerivation (extend L) ⟨x, x, .trans d (.inv d)⟩ ⟨x, x, .refl x⟩ :=
  compareDerivations _ _

/-- Boundary-compatible cells at every higher level admit a chosen filler. -/
theorem higher_filling (A : Type u) (n : Nat) (x y : (tower A n).Arr)
    (h : Parallel (tower A n) x y) :
    ∃ c : Cell A (n + 3), source (n + 2) c = x ∧ target (n + 2) c = y :=
  ⟨fill (tower A n) x y h, rfl, rfl⟩

/-- Both pentagon routes embed as two-cells without erasing their syntax. -/
def pentagonFiller {A : Type u} {a b c d e : A}
    (f : Path A a b) (g : Path A b c) (h : Path A c d) (k : Path A d e) :
    Cell A 3 :=
  fill (skeleton A)
    ⟨a, e, _, _, pentagonLeft f g h k⟩
    ⟨a, e, _, _, pentagonRight f g h k⟩ ⟨rfl, rfl⟩

end ComputationalPaths.PalomarWeakOmegaGroupoid.GlobularCompletion

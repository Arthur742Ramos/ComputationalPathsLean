import Mathlib.Data.List.Basic

/-!
# Relative globular completion of computational rewrite data

A chosen parallel-cell completion, with a layerwise universal interpretation
property. The 0-, 1-, and 2-skeleton is fixed explicitly. The higher tower is
recursive and boundary-sensitive. No identification with identity types, no
normalization-derived coherence, and no operadic weak omega-groupoid theorem
is claimed. The paper's Theorem 10.2 is excluded.

Both Palomar modules contain the same complete checked development. This
intentional duplication keeps the statement independent of local imports and
avoids deliberate proof holes; it is not an independent second formalization.
-/

namespace ComputationalPaths.RelativeCompletion

universe u

noncomputable section

/-- A trace-decorated ambient equality. The list is observable metadata;
no adjacency or validity property of its entries is imposed. -/
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


end

end ComputationalPaths.RelativeCompletion


/-!
# Recursive globular completion of the computational-path 2-skeleton

This repairs the non-recursive indexed tail in the preliminary artifact.
The primitive universal filler is an explicit part of the chosen completion,
not a consequence of equality reflection or rewrite normalization. This file
does not assert an operadic weak omega-groupoid structure.
-/
namespace ComputationalPaths.RelativeCompletion.Globular

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

/-- Boundary-compatible cells at every higher level have a chosen filler. -/
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

end ComputationalPaths.RelativeCompletion.Globular


/-! The layerwise universal property of the chosen globular completion.
This is freeness of reversible composition syntax, NOT freeness as a groupoid:
associativity and inverse cancellation remain higher comparisons, not equations.
-/
namespace ComputationalPaths.RelativeCompletion.Globular

universe u v

/-- A target interpretation supplies typed operations and a chosen arrow for
each parallel pair. No associativity, cancellation, or uniqueness is assumed. -/
structure Interpretation (L : Layer.{u}) where
  Hom : L.Arr → L.Arr → Type v
  unit : (x : L.Arr) → Hom x x
  generator : {x y : L.Arr} → Parallel L x y → Hom x y
  inverse : {x y : L.Arr} → Hom x y → Hom y x
  compose : {x y z : L.Arr} → Hom x y → Hom y z → Hom x z

/-- Evaluation of the explicit higher derivation in a chosen target. -/
def interpret {L : Layer.{u}} (M : Interpretation.{u,v} L) :
    (x y : L.Arr) → CellDerivation L x y → M.Hom x y
  | _, _, .refl x => M.unit x
  | _, _, .step h _ => M.generator h
  | _, _, .inv d => M.inverse (interpret M _ _ d)
  | _, _, .trans d e => M.compose (interpret M _ _ d) (interpret M _ _ e)

/-- The exact preservation equations required of an interpretation. -/
def Preserves {L : Layer.{u}} (M : Interpretation.{u,v} L)
    (f : (x y : L.Arr) → CellDerivation L x y → M.Hom x y) : Prop :=
  (∀ x, f x x (.refl x) = M.unit x) ∧
  (∀ (x y) (h : Parallel L x y) (i : (⟨x⟩ : Nonempty L.Arr) = ⟨y⟩),
    f x y (.step h i) = M.generator h) ∧
  (∀ (x y) (d : CellDerivation L x y),
    f y x (.inv d) = M.inverse (f x y d)) ∧
  (∀ (x y z) (d : CellDerivation L x y) (e : CellDerivation L y z),
    f x z (.trans d e) = M.compose (f x y d) (f y z e))

/-- Every layer is free for precisely the displayed typed operations. -/
theorem unique_interpretation {L : Layer.{u}} (M : Interpretation.{u,v} L) :
    ∃! f : (x y : L.Arr) → CellDerivation L x y → M.Hom x y,
      Preserves M f := by
  refine ⟨interpret M, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x; rfl
  · intro x y h i; rfl
  · intro x y d; rfl
  · intro x y z d e; rfl
  · intro f hf
    funext x y d
    induction d with
    | refl x => exact hf.1 x
    | step h i => exact hf.2.1 _ _ h i
    | inv d ih =>
      change f _ _ (.inv d) = M.inverse (interpret M _ _ d)
      rw [hf.2.2.1, ih]
    | trans d e ih ih' =>
      change f _ _ (.trans d e) = M.compose (interpret M _ _ d) (interpret M _ _ e)
      rw [hf.2.2.2, ih, ih']

/-- A filler exists exactly for a parallel boundary, in every layer. -/
theorem inhabited_iff_parallel (L : Layer.{u}) (x y : L.Arr) :
    Nonempty (CellDerivation L x y) ↔ Parallel L x y :=
  ⟨fun ⟨d⟩ => d.parallel, fun h => ⟨.step h (Subsingleton.elim _ _)⟩⟩

/-- Count syntax constructors; no quotient identifies distinct expressions. -/
def nodeCount {L : Layer.{u}} {x y : L.Arr} : CellDerivation L x y → Nat
  | .refl _ => 0
  | .step _ _ => 1
  | .inv d => nodeCount d + 1
  | .trans d e => nodeCount d + nodeCount e + 1

/-- Chosen connectedness does not make higher derivations proof-irrelevant. -/
theorem higher_syntax_not_subsingleton (L : Layer.{u}) (x : L.Arr) :
    ¬ Subsingleton (CellDerivation L x x) := by
  intro h
  have eq := h.elim (.refl x) (.inv (.refl x))
  have count := congrArg nodeCount eq
  change 0 = 1 at count
  cases count

/-- Freeness holds uniformly at every layer, not only in low dimensions. -/
theorem tower_unique_interpretation (A : Type u) (n : Nat)
    (M : Interpretation.{u,v} (tower A n)) :
    ∃! f : (x y : (tower A n).Arr) → CellDerivation (tower A n) x y → M.Hom x y,
      Preserves M f := unique_interpretation M

/-- A map of layers preserves both of the actual boundary maps. -/
structure LayerMap (L K : Layer.{u}) where
  onObj : L.Obj → K.Obj
  onArr : L.Arr → K.Arr
  source_law : ∀ x, K.source (onArr x) = onObj (L.source x)
  target_law : ∀ x, K.target (onArr x) = onObj (L.target x)

def LayerMap.identity (L : Layer.{u}) : LayerMap L L :=
  ⟨id, id, fun _ => rfl, fun _ => rfl⟩

def LayerMap.comp {L K H : Layer.{u}} (f : LayerMap L K) (g : LayerMap K H) :
    LayerMap L H :=
  ⟨g.onObj ∘ f.onObj, g.onArr ∘ f.onArr,
    fun x => (g.source_law _).trans (congrArg g.onObj (f.source_law x)),
    fun x => (g.target_law _).trans (congrArg g.onObj (f.target_law x))⟩

theorem LayerMap.parallel {L K : Layer.{u}} (f : LayerMap L K)
    {x y : L.Arr} (h : Parallel L x y) : Parallel K (f.onArr x) (f.onArr y) :=
  ⟨(f.source_law x).trans ((congrArg f.onObj h.1).trans (f.source_law y).symm),
    (f.target_law x).trans ((congrArg f.onObj h.2).trans (f.target_law y).symm)⟩

/-- Boundary-preserving maps act on every derivation constructor. -/
def mapDerivation {L K : Layer.{u}} (f : LayerMap L K) :
    {x y : L.Arr} → CellDerivation L x y → CellDerivation K (f.onArr x) (f.onArr y)
  | _, _, .refl x => .refl (f.onArr x)
  | _, _, .step h _ => .step (f.parallel h) (Subsingleton.elim _ _)
  | _, _, .inv d => .inv (mapDerivation f d)
  | _, _, .trans d e => .trans (mapDerivation f d) (mapDerivation f e)

theorem map_identity {L : Layer.{u}} {x y : L.Arr} (d : CellDerivation L x y) :
    mapDerivation (LayerMap.identity L) d = d := by
  induction d with
  | refl _ => rfl
  | step _ _ => rfl
  | inv d ih => exact congrArg CellDerivation.inv ih
  | trans d e ih ih' => exact congrArg₂ CellDerivation.trans ih ih'

theorem map_comp {L K H : Layer.{u}} (f : LayerMap L K) (g : LayerMap K H)
    {x y : L.Arr} (d : CellDerivation L x y) :
    mapDerivation (f.comp g) d = mapDerivation g (mapDerivation f d) := by
  induction d with
  | refl _ => rfl
  | step _ _ => rfl
  | inv d ih => exact congrArg CellDerivation.inv ih
  | trans d e ih ih' => exact congrArg₂ CellDerivation.trans ih ih'

theorem map_preserves_nodes {L K : Layer.{u}} (f : LayerMap L K)
    {x y : L.Arr} (d : CellDerivation L x y) :
    nodeCount (mapDerivation f d) = nodeCount d := by
  induction d with
  | refl _ => rfl
  | step _ _ => rfl
  | inv d ih => exact congrArg (fun n => n + 1) ih
  | trans d e ih ih' => exact congrArg₂ (fun n m => n + m + 1) ih ih'

/-- Functorial extension from a layer map to a map of its completion. -/
def LayerMap.lift {L K : Layer.{u}} (f : LayerMap L K) :
    LayerMap (extend L) (extend K) :=
  ⟨f.onArr, fun c => ⟨f.onArr c.source, f.onArr c.target, mapDerivation f c.derivation⟩,
    fun _ => rfl, fun _ => rfl⟩

theorem LayerMap.ext {L K : Layer.{u}} (f g : LayerMap L K)
    (h₀ : f.onObj = g.onObj) (h₁ : f.onArr = g.onArr) : f = g := by
  cases f; cases g; cases h₀; cases h₁; rfl

theorem lift_identity (L : Layer.{u}) :
    (LayerMap.identity L).lift = LayerMap.identity (extend L) := by
  apply LayerMap.ext
  · rfl
  · funext c
    cases c with
    | mk x y d => exact congrArg (fun e => Filler.mk x y e) (map_identity d)

theorem lift_comp {L K H : Layer.{u}} (f : LayerMap L K) (g : LayerMap K H) :
    (f.comp g).lift = f.lift.comp g.lift := by
  apply LayerMap.ext
  · rfl
  · funext c
    cases c with
    | mk x y d => exact congrArg (fun e => Filler.mk _ _ e) (map_comp f g d)

/-- The original two-cell data are not identified by adding higher fillers:
the two explicit pentagon routes are distinct but joined by a three-cell. -/
theorem pentagon_distinct_connected {A : Type u} {a b c d e : A}
    (f : Path A a b) (g : Path A b c) (h : Path A c d) (k : Path A d e) :
    let l : Two A := ⟨a, e, _, _, pentagonLeft f g h k⟩
    let r : Two A := ⟨a, e, _, _, pentagonRight f g h k⟩
    l ≠ r ∧ ∃ cell : Cell A 3, source 2 cell = l ∧ target 2 cell = r := by
  constructor
  · intro eq
    have count := congrArg (fun x : Two A => RwEq.stepCount x.2.2.2.2) eq
    change 2 = 3 at count
    cases count
  · exact ⟨pentagonFiller f g h k, rfl, rfl⟩

end ComputationalPaths.RelativeCompletion.Globular

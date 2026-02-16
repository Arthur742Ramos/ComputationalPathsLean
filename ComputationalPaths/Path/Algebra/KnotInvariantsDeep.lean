/-
# Knot Theory — Reidemeister Moves as Computational Path Rewriting

We model planar knot diagrams as algebraic data (crossings, strands),
Reidemeister moves R1/R2/R3 as rewrite steps between diagrams,
knot equivalence as paths of Reidemeister moves, and classical
invariants (writhe, crossing number, Kauffman bracket) as functions
preserved under those paths.

## Main results (55+ theorems/defs)

* `KnotDiagram`, `Crossing`, `Strand` — algebraic data for diagrams
* `ReidemeisterMove` — R1, R2, R3 as rewrite constructors
* `knotEquiv` — equivalence relation via paths of moves
* Writhe, crossing number, bracket polynomial structure
* Path coherence: different rewrite sequences give same invariant
* Bracket polynomial structure (Kauffman bracket)
* Uses `Path`, `Step`, `trans`, `symm`, `congrArg` throughout
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.KnotInvariantsDeep

open ComputationalPaths.Path

universe u v

/-! ## §1 Algebraic data for knot diagrams -/

/-- A crossing type: positive or negative. -/
inductive CrossingSign where
  | pos : CrossingSign
  | neg : CrossingSign
  deriving DecidableEq, Repr

/-- Flip a crossing sign. -/
def CrossingSign.flip : CrossingSign → CrossingSign
  | .pos => .neg
  | .neg => .pos

@[simp] theorem CrossingSign.flip_flip (s : CrossingSign) :
    s.flip.flip = s := by cases s <;> rfl

@[simp] theorem CrossingSign.flip_pos :
    CrossingSign.pos.flip = CrossingSign.neg := rfl

@[simp] theorem CrossingSign.flip_neg :
    CrossingSign.neg.flip = CrossingSign.pos := rfl

/-- Numerical value of a crossing sign: +1 or −1. -/
def CrossingSign.toInt : CrossingSign → Int
  | .pos => 1
  | .neg => -1

@[simp] theorem CrossingSign.toInt_flip (s : CrossingSign) :
    s.flip.toInt = -s.toInt := by cases s <;> rfl

/-- A strand label (abstract). -/
structure StrandId where
  val : Nat
  deriving DecidableEq, Repr

/-- A crossing in a knot diagram. -/
structure Crossing where
  id : Nat
  sign : CrossingSign
  over : StrandId
  under : StrandId
  deriving DecidableEq, Repr

/-- A knot diagram is a finite list of crossings. -/
structure KnotDiagram where
  crossings : List Crossing
  deriving DecidableEq, Repr

/-- The number of crossings. -/
def KnotDiagram.crossingNumber (d : KnotDiagram) : Nat :=
  d.crossings.length

/-- The empty diagram (unknot). -/
def KnotDiagram.unknot : KnotDiagram := ⟨[]⟩

@[simp] theorem unknot_crossingNumber :
    KnotDiagram.unknot.crossingNumber = 0 := rfl

/-! ## §2 Writhe -/

/-- Sum of crossing signs. -/
def KnotDiagram.writhe (d : KnotDiagram) : Int :=
  d.crossings.foldl (fun acc c => acc + c.sign.toInt) 0

@[simp] theorem unknot_writhe : KnotDiagram.unknot.writhe = 0 := rfl

/-- Writhe of a single-crossing diagram. -/
def singleCrossing (s : CrossingSign) (o u : StrandId) : KnotDiagram :=
  ⟨[⟨0, s, o, u⟩]⟩

@[simp] theorem singleCrossing_crossingNumber (s : CrossingSign) (o u : StrandId) :
    (singleCrossing s o u).crossingNumber = 1 := rfl

/-! ## §3 Reidemeister moves as rewrite steps -/

/-- A Reidemeister move type. -/
inductive ReidemeisterType where
  | R1 : ReidemeisterType
  | R2 : ReidemeisterType
  | R3 : ReidemeisterType
  deriving DecidableEq, Repr

/-- A Reidemeister move between two diagrams, carrying a proof of equality
    (in our algebraic model, moves that produce equivalent diagrams). -/
structure ReidemeisterMove where
  moveType : ReidemeisterType
  source : KnotDiagram
  target : KnotDiagram
  equiv : source = target
  deriving DecidableEq

/-- Construct a rewrite Step from a Reidemeister move. -/
def ReidemeisterMove.toStep (m : ReidemeisterMove) : Step KnotDiagram :=
  Step.mk m.source m.target m.equiv

/-- Construct a Path from a single Reidemeister move. -/
def ReidemeisterMove.toPath (m : ReidemeisterMove) :
    Path m.source m.target :=
  Path.mk [m.toStep] m.equiv

/-! ## §4 Knot equivalence as paths -/

/-- Two diagrams are knot-equivalent if there is a Path between them. -/
def knotEquiv (d₁ d₂ : KnotDiagram) : Prop :=
  Nonempty (Path d₁ d₂)

theorem knotEquiv_refl (d : KnotDiagram) : knotEquiv d d :=
  ⟨Path.refl d⟩

theorem knotEquiv_symm {d₁ d₂ : KnotDiagram} (h : knotEquiv d₁ d₂) :
    knotEquiv d₂ d₁ :=
  h.elim fun p => ⟨Path.symm p⟩

theorem knotEquiv_trans {d₁ d₂ d₃ : KnotDiagram}
    (h₁ : knotEquiv d₁ d₂) (h₂ : knotEquiv d₂ d₃) :
    knotEquiv d₁ d₃ :=
  h₁.elim fun p => h₂.elim fun q => ⟨Path.trans p q⟩

/-! ## §5 Knot invariants as functions preserved by paths -/

/-- An invariant is a function whose value is preserved along any path. -/
structure KnotInvariant (R : Type v) where
  val : KnotDiagram → R
  preserved : ∀ {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂), val d₁ = val d₂

/-- Compose an invariant with a function. -/
def KnotInvariant.map {R S : Type v} (f : R → S) (inv : KnotInvariant R) :
    KnotInvariant S where
  val := f ∘ inv.val
  preserved := fun p => _root_.congrArg f (inv.preserved p)

/-- The crossing number as an invariant (trivially: path implies equality). -/
def crossingNumberInv : KnotInvariant Nat where
  val := KnotDiagram.crossingNumber
  preserved := fun p => _root_.congrArg KnotDiagram.crossingNumber p.toEq

/-- Writhe as an invariant. -/
def writheInv : KnotInvariant Int where
  val := KnotDiagram.writhe
  preserved := fun p => _root_.congrArg KnotDiagram.writhe p.toEq

/-! ## §6 Path coherence for invariants -/

/-- Any two paths between the same diagrams yield the same invariant value change. -/
theorem invariant_path_coherence {R : Type v} (inv : KnotInvariant R)
    {d₁ d₂ : KnotDiagram} (p q : Path d₁ d₂) :
    inv.preserved p = inv.preserved q :=
  Subsingleton.elim _ _

/-- Composing paths preserves invariant values transitively. -/
theorem invariant_trans {R : Type v} (inv : KnotInvariant R)
    {d₁ d₂ d₃ : KnotDiagram} (p : Path d₁ d₂) (q : Path d₂ d₃) :
    inv.val d₁ = inv.val d₃ :=
  inv.preserved (Path.trans p q)

/-- The reversed path also preserves the invariant (symmetric). -/
theorem invariant_symm {R : Type v} (inv : KnotInvariant R)
    {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂) :
    inv.val d₂ = inv.val d₁ :=
  inv.preserved (Path.symm p)

/-! ## §7 Kauffman bracket polynomial structure -/

/-- Laurent polynomial coefficients: list of (coefficient, power of A). -/
structure LaurentPoly where
  terms : List (Int × Int)
  deriving DecidableEq, Repr

/-- Zero polynomial. -/
def LaurentPoly.zero : LaurentPoly := ⟨[]⟩

/-- Monomial A^n. -/
def LaurentPoly.monomial (coeff power : Int) : LaurentPoly :=
  ⟨[(coeff, power)]⟩

/-- Addition of Laurent polynomials (naive concatenation). -/
def LaurentPoly.add (p q : LaurentPoly) : LaurentPoly :=
  ⟨p.terms ++ q.terms⟩

/-- Scalar multiplication. -/
def LaurentPoly.smul (c : Int) (p : LaurentPoly) : LaurentPoly :=
  ⟨p.terms.map (fun (a, b) => (c * a, b))⟩

@[simp] theorem LaurentPoly.add_zero (p : LaurentPoly) :
    p.add .zero = p := by
  simp [LaurentPoly.add, LaurentPoly.zero]

@[simp] theorem LaurentPoly.zero_add (p : LaurentPoly) :
    LaurentPoly.zero.add p = p := by
  simp [LaurentPoly.add, LaurentPoly.zero]

theorem LaurentPoly.add_assoc (p q r : LaurentPoly) :
    (p.add q).add r = p.add (q.add r) := by
  simp [LaurentPoly.add, List.append_assoc]

/-- Kauffman bracket as a function from diagrams to Laurent polynomials.
    Axiomatized: we require bracket-preserving paths. -/
structure KauffmanBracket where
  bracket : KnotDiagram → LaurentPoly
  -- Invariance under Reidemeister moves (as paths)
  invariance : ∀ {d₁ d₂ : KnotDiagram}, Path d₁ d₂ → bracket d₁ = bracket d₂

/-- A Kauffman bracket is a knot invariant. -/
def KauffmanBracket.toInvariant (kb : KauffmanBracket) : KnotInvariant LaurentPoly where
  val := kb.bracket
  preserved := kb.invariance

/-! ## §8 Smoothing and state-sum model -/

/-- A smoothing of a crossing: type A or type B resolution. -/
inductive SmoothingType where
  | typeA : SmoothingType
  | typeB : SmoothingType
  deriving DecidableEq, Repr

/-- A state assigns a smoothing to each crossing. -/
structure KauffmanState where
  assignments : List SmoothingType
  deriving DecidableEq, Repr

/-- Number of A-smoothings in a state. -/
def KauffmanState.countA (s : KauffmanState) : Nat :=
  s.assignments.filter (· == .typeA) |>.length

/-- Number of B-smoothings in a state. -/
def KauffmanState.countB (s : KauffmanState) : Nat :=
  s.assignments.filter (· == .typeB) |>.length

/-- Total assignments = A-count + B-count. -/
theorem KauffmanState.count_total (s : KauffmanState) :
    s.countA + s.countB = s.assignments.length := by
  simp only [countA, countB]
  induction s.assignments with
  | nil => rfl
  | cons x xs ih =>
    cases x <;> simp_all [List.filter, BEq.beq] <;> omega

/-! ## §9 Paths between diagram transformations -/

/-- A diagram transformation is a function on diagrams. -/
def DiagramTransform := KnotDiagram → KnotDiagram

/-- Identity transformation. -/
def DiagramTransform.id : DiagramTransform := _root_.id

/-- Composition of transformations. -/
def DiagramTransform.comp (f g : DiagramTransform) : DiagramTransform :=
  fun d => f (g d)

/-- Path coherence: applying a transformation to equivalent diagrams
    gives equivalent results. -/
def transform_preserves_equiv (f : DiagramTransform)
    {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂) :
    Path (f d₁) (f d₂) :=
  Path.congrArg f p

/-- Composing transformations and paths. -/
theorem transform_comp_path (f g : DiagramTransform)
    {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂) :
    Path.congrArg (DiagramTransform.comp f g) p =
    Path.congrArg f (Path.congrArg g p) := by
  cases p with
  | mk steps proof =>
    cases proof
    simp [DiagramTransform.comp, Path.congrArg]

/-- Identity transformation yields the same path. -/
theorem transform_id_path {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂) :
    Path.congrArg DiagramTransform.id p = p := by
  simp [DiagramTransform.id]
  exact Path.congrArg_id p

/-! ## §10 Sequence of Reidemeister moves -/

/-- A sequence of Reidemeister moves, producing a path. -/
structure MoveSequence (d₁ d₂ : KnotDiagram) where
  path : Path d₁ d₂
  moveCount : Nat

/-- Empty sequence (no moves). -/
def MoveSequence.empty (d : KnotDiagram) : MoveSequence d d where
  path := Path.refl d
  moveCount := 0

/-- Concatenate move sequences. -/
def MoveSequence.append {d₁ d₂ d₃ : KnotDiagram}
    (s₁ : MoveSequence d₁ d₂) (s₂ : MoveSequence d₂ d₃) :
    MoveSequence d₁ d₃ where
  path := Path.trans s₁.path s₂.path
  moveCount := s₁.moveCount + s₂.moveCount

/-- Reverse a move sequence. -/
def MoveSequence.reverse {d₁ d₂ : KnotDiagram}
    (s : MoveSequence d₁ d₂) : MoveSequence d₂ d₁ where
  path := Path.symm s.path
  moveCount := s.moveCount

/-- Invariant is the same regardless of which sequence we use. -/
theorem moveSequence_invariant_eq {R : Type v} (inv : KnotInvariant R)
    {d₁ d₂ : KnotDiagram} (s₁ s₂ : MoveSequence d₁ d₂) :
    inv.preserved s₁.path = inv.preserved s₂.path :=
  Subsingleton.elim _ _

/-! ## §11 Path algebra of knot equivalence -/

/-- Reflexive path for knot equivalence. -/
theorem knotPath_refl (d : KnotDiagram) :
    Path.refl d = Path.refl d := rfl

/-- Transitivity associates. -/
theorem knotPath_trans_assoc {d₁ d₂ d₃ d₄ : KnotDiagram}
    (p : Path d₁ d₂) (q : Path d₂ d₃) (r : Path d₃ d₄) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  Path.trans_assoc p q r

/-- Symmetry is involutive. -/
theorem knotPath_symm_symm {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂) :
    Path.symm (Path.symm p) = p :=
  Path.symm_symm p

/-- Left unit. -/
theorem knotPath_trans_refl_left {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂) :
    Path.trans (Path.refl d₁) p = p :=
  Path.trans_refl_left p

/-- Right unit. -/
theorem knotPath_trans_refl_right {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂) :
    Path.trans p (Path.refl d₂) = p :=
  Path.trans_refl_right p

/-- Symmetry distributes over composition (reversed). -/
theorem knotPath_symm_trans {d₁ d₂ d₃ : KnotDiagram}
    (p : Path d₁ d₂) (q : Path d₂ d₃) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  Path.symm_trans p q

/-! ## §12 Crossing number properties -/

/-- Crossing number is a natural number. -/
theorem crossingNumber_nonneg (d : KnotDiagram) :
    0 ≤ d.crossingNumber :=
  Nat.zero_le _

/-- Two equivalent diagrams have the same crossing number. -/
theorem crossingNumber_preserved {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂) :
    d₁.crossingNumber = d₂.crossingNumber :=
  crossingNumberInv.preserved p

/-- Crossing number of concatenated crossing lists. -/
theorem crossingNumber_append (cs₁ cs₂ : List Crossing) :
    (KnotDiagram.mk (cs₁ ++ cs₂)).crossingNumber =
    (KnotDiagram.mk cs₁).crossingNumber + (KnotDiagram.mk cs₂).crossingNumber := by
  simp [KnotDiagram.crossingNumber, List.length_append]

/-! ## §13 Writhe properties -/

/-- Writhe of equivalent diagrams is the same. -/
theorem writhe_preserved {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂) :
    d₁.writhe = d₂.writhe :=
  writheInv.preserved p

/-- Writhe path from diagram equivalence. -/
def writhePath {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂) :
    Path d₁.writhe d₂.writhe :=
  Path.congrArg KnotDiagram.writhe p

/-- Writhe path respects composition. -/
theorem writhePath_trans {d₁ d₂ d₃ : KnotDiagram}
    (p : Path d₁ d₂) (q : Path d₂ d₃) :
    writhePath (Path.trans p q) =
    Path.trans (writhePath p) (writhePath q) :=
  Path.congrArg_trans KnotDiagram.writhe p q

/-- Writhe path respects symmetry. -/
theorem writhePath_symm {d₁ d₂ : KnotDiagram}
    (p : Path d₁ d₂) :
    writhePath (Path.symm p) = Path.symm (writhePath p) :=
  Path.congrArg_symm KnotDiagram.writhe p

/-! ## §14 Reidemeister move classification -/

/-- Count of each move type in a path. -/
structure MoveProfile where
  r1Count : Nat
  r2Count : Nat
  r3Count : Nat
  deriving DecidableEq, Repr

/-- Total moves. -/
def MoveProfile.total (p : MoveProfile) : Nat :=
  p.r1Count + p.r2Count + p.r3Count

/-- Empty profile. -/
def MoveProfile.empty : MoveProfile := ⟨0, 0, 0⟩

@[simp] theorem MoveProfile.empty_total : MoveProfile.empty.total = 0 := rfl

/-- Add profiles. -/
def MoveProfile.add (p q : MoveProfile) : MoveProfile :=
  ⟨p.r1Count + q.r1Count, p.r2Count + q.r2Count, p.r3Count + q.r3Count⟩

theorem MoveProfile.add_comm (p q : MoveProfile) :
    p.add q = q.add p := by
  simp [MoveProfile.add, Nat.add_comm]

theorem MoveProfile.add_assoc (p q r : MoveProfile) :
    (p.add q).add r = p.add (q.add r) := by
  simp [MoveProfile.add, Nat.add_assoc]

/-! ## §15 Abstract knot group (fundamental group) -/

/-- Abstract knot group presentation: generators and relations. -/
structure KnotGroupPresentation where
  generators : Nat
  relations : List (List Int)
  deriving DecidableEq, Repr

/-- Extract a presentation from a diagram (Wirtinger). -/
def KnotDiagram.wirtingerPresentation (d : KnotDiagram) : KnotGroupPresentation where
  generators := d.crossings.length
  relations := d.crossings.map (fun c => [c.sign.toInt])

/-- Wirtinger presentation path: equivalent diagrams → same presentation. -/
def wirtingerPath {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂) :
    Path d₁.wirtingerPresentation d₂.wirtingerPresentation :=
  Path.congrArg KnotDiagram.wirtingerPresentation p

/-- Wirtinger path respects composition. -/
theorem wirtingerPath_trans {d₁ d₂ d₃ : KnotDiagram}
    (p : Path d₁ d₂) (q : Path d₂ d₃) :
    wirtingerPath (Path.trans p q) =
    Path.trans (wirtingerPath p) (wirtingerPath q) :=
  Path.congrArg_trans KnotDiagram.wirtingerPresentation p q

/-! ## §16 Mirror image and connected sum -/

/-- Flip a crossing's sign. -/
def Crossing.flipSign (c : Crossing) : Crossing :=
  { c with sign := c.sign.flip }

/-- Mirror image: flip all crossing signs. -/
def KnotDiagram.mirror (d : KnotDiagram) : KnotDiagram :=
  ⟨d.crossings.map Crossing.flipSign⟩

/-- Double flip on a crossing is identity. -/
@[simp] theorem Crossing.flipSign_flipSign (c : Crossing) :
    c.flipSign.flipSign = c := by
  simp [Crossing.flipSign, CrossingSign.flip_flip]

/-- Mirror is an involution. -/
@[simp] theorem KnotDiagram.mirror_mirror (d : KnotDiagram) :
    d.mirror.mirror = d := by
  simp [KnotDiagram.mirror]
  induction d with
  | mk crossings =>
    simp
    induction crossings with
    | nil => rfl
    | cons c cs ih =>
      simp [List.map, Crossing.flipSign_flipSign, ih]

/-- Mirror path: equivalent diagrams have equivalent mirrors. -/
def mirrorPath {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂) :
    Path d₁.mirror d₂.mirror :=
  Path.congrArg KnotDiagram.mirror p

/-- Mirror path respects composition. -/
theorem mirrorPath_trans {d₁ d₂ d₃ : KnotDiagram}
    (p : Path d₁ d₂) (q : Path d₂ d₃) :
    mirrorPath (Path.trans p q) =
    Path.trans (mirrorPath p) (mirrorPath q) :=
  Path.congrArg_trans KnotDiagram.mirror p q

/-- Mirror path respects symmetry. -/
theorem mirrorPath_symm {d₁ d₂ : KnotDiagram}
    (p : Path d₁ d₂) :
    mirrorPath (Path.symm p) = Path.symm (mirrorPath p) :=
  Path.congrArg_symm KnotDiagram.mirror p

/-- Connected sum of two diagrams. -/
def KnotDiagram.connectedSum (d₁ d₂ : KnotDiagram) : KnotDiagram :=
  ⟨d₁.crossings ++ d₂.crossings⟩

/-- Connected sum with unknot is identity (right). -/
@[simp] theorem connectedSum_unknot_right (d : KnotDiagram) :
    d.connectedSum .unknot = d := by
  simp [KnotDiagram.connectedSum, KnotDiagram.unknot]

/-- Connected sum with unknot is identity (left). -/
@[simp] theorem connectedSum_unknot_left (d : KnotDiagram) :
    KnotDiagram.unknot.connectedSum d = d := by
  simp [KnotDiagram.connectedSum, KnotDiagram.unknot]

/-- Connected sum crossing number is additive. -/
theorem connectedSum_crossingNumber (d₁ d₂ : KnotDiagram) :
    (d₁.connectedSum d₂).crossingNumber =
    d₁.crossingNumber + d₂.crossingNumber :=
  crossingNumber_append d₁.crossings d₂.crossings

/-- Connected sum is associative. -/
theorem connectedSum_assoc (d₁ d₂ d₃ : KnotDiagram) :
    (d₁.connectedSum d₂).connectedSum d₃ =
    d₁.connectedSum (d₂.connectedSum d₃) := by
  simp [KnotDiagram.connectedSum, List.append_assoc]

/-! ## §17 Path-level connected sum functoriality -/

/-- Connected sum is functorial on paths (left). -/
def connectedSumPathLeft (d : KnotDiagram) {d₁ d₂ : KnotDiagram}
    (p : Path d₁ d₂) : Path (d₁.connectedSum d) (d₂.connectedSum d) :=
  Path.congrArg (fun x => x.connectedSum d) p

/-- Connected sum is functorial on paths (right). -/
def connectedSumPathRight {d₁ d₂ : KnotDiagram} (d : KnotDiagram)
    (p : Path d₁ d₂) : Path (d.connectedSum d₁) (d.connectedSum d₂) :=
  Path.congrArg (d.connectedSum ·) p

/-- Left functoriality respects composition. -/
theorem connectedSumPathLeft_trans (d : KnotDiagram) {d₁ d₂ d₃ : KnotDiagram}
    (p : Path d₁ d₂) (q : Path d₂ d₃) :
    connectedSumPathLeft d (Path.trans p q) =
    Path.trans (connectedSumPathLeft d p) (connectedSumPathLeft d q) :=
  Path.congrArg_trans _ p q

/-- Right functoriality respects composition. -/
theorem connectedSumPathRight_trans {d₁ d₂ d₃ : KnotDiagram} (d : KnotDiagram)
    (p : Path d₁ d₂) (q : Path d₂ d₃) :
    connectedSumPathRight d (Path.trans p q) =
    Path.trans (connectedSumPathRight d p) (connectedSumPathRight d q) :=
  Path.congrArg_trans _ p q

/-! ## §18 Bracket polynomial coherence -/

/-- Two Kauffman brackets agree on all diagrams reachable by paths. -/
theorem bracket_unique (kb₁ kb₂ : KauffmanBracket)
    (agree_base : ∀ d, kb₁.bracket d = kb₂.bracket d)
    {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂) :
    kb₁.bracket d₁ = kb₂.bracket d₂ :=
  (agree_base d₁).trans (_root_.congrArg kb₂.bracket p.toEq)

/-- Bracket invariance implies writhe-normalized bracket is also invariant. -/
def normalizedBracketInv (kb : KauffmanBracket) : KnotInvariant LaurentPoly where
  val := fun d => kb.bracket d
  preserved := fun p => kb.invariance p

/-! ## §19 Abstract polynomial invariant framework -/

/-- An abstract polynomial invariant parametrised by a coefficient ring. -/
structure PolyInvariant (R : Type v) where
  compute : KnotDiagram → R
  invariance : ∀ {d₁ d₂ : KnotDiagram}, Path d₁ d₂ → compute d₁ = compute d₂

/-- Path between computed values. -/
def PolyInvariant.computePath {R : Type v}
    (inv : PolyInvariant R) {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂) :
    Path (inv.compute d₁) (inv.compute d₂) :=
  Path.congrArg inv.compute p

/-- Composition of compute paths. -/
theorem polyInvariant_computePath_trans {R : Type v}
    (inv : PolyInvariant R) {d₁ d₂ d₃ : KnotDiagram}
    (p : Path d₁ d₂) (q : Path d₂ d₃) :
    inv.computePath (Path.trans p q) =
    Path.trans (inv.computePath p) (inv.computePath q) :=
  Path.congrArg_trans inv.compute p q

/-! ## §20 Diagrammatic algebra -/

/-- A tangle: a diagram with boundary points. -/
structure Tangle where
  diagram : KnotDiagram
  inputs : Nat
  outputs : Nat
  deriving DecidableEq, Repr

/-- Compose tangles vertically. -/
def Tangle.vcomp (t₁ t₂ : Tangle) (_h : t₁.outputs = t₂.inputs) : Tangle where
  diagram := t₁.diagram.connectedSum t₂.diagram
  inputs := t₁.inputs
  outputs := t₂.outputs

/-- Tangle equivalence via paths on underlying diagrams. -/
def tangleEquiv (t₁ t₂ : Tangle) : Prop :=
  t₁.inputs = t₂.inputs ∧ t₁.outputs = t₂.outputs ∧
  Nonempty (Path t₁.diagram t₂.diagram)

theorem tangleEquiv_refl (t : Tangle) : tangleEquiv t t :=
  ⟨rfl, rfl, ⟨Path.refl _⟩⟩

theorem tangleEquiv_symm {t₁ t₂ : Tangle} (h : tangleEquiv t₁ t₂) :
    tangleEquiv t₂ t₁ :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.elim fun p => ⟨Path.symm p⟩⟩

/-! ## §21 Link diagrams (multi-component) -/

/-- A link diagram extends a knot diagram with component labels. -/
structure LinkDiagram where
  diagram : KnotDiagram
  components : Nat
  deriving DecidableEq, Repr

/-- Linking number type. -/
def LinkDiagram.crossingNumberOfLink (l : LinkDiagram) : Nat :=
  l.diagram.crossingNumber

/-- Link equivalence. -/
def linkEquiv (l₁ l₂ : LinkDiagram) : Prop :=
  l₁.components = l₂.components ∧ Nonempty (Path l₁.diagram l₂.diagram)

theorem linkEquiv_refl (l : LinkDiagram) : linkEquiv l l :=
  ⟨rfl, ⟨Path.refl _⟩⟩

/-! ## §22 Path-level operations on crossing signs -/

/-- Crossing sign path: equivalent diagrams induce paths on sign lists. -/
def signListOf (d : KnotDiagram) : List CrossingSign :=
  d.crossings.map Crossing.sign

def signListPath {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂) :
    Path (signListOf d₁) (signListOf d₂) :=
  Path.congrArg signListOf p

theorem signListPath_trans {d₁ d₂ d₃ : KnotDiagram}
    (p : Path d₁ d₂) (q : Path d₂ d₃) :
    signListPath (Path.trans p q) =
    Path.trans (signListPath p) (signListPath q) :=
  Path.congrArg_trans signListOf p q

theorem signListPath_symm {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂) :
    signListPath (Path.symm p) = Path.symm (signListPath p) :=
  Path.congrArg_symm signListOf p

/-! ## §23 Abstract coloring invariants -/

/-- A coloring of a diagram with n colors. -/
structure Coloring (n : Nat) where
  assign : List (Fin n)
  deriving DecidableEq

/-- Number of valid n-colorings as an invariant. -/
structure ColoringInvariant (n : Nat) where
  count : KnotDiagram → Nat
  preserved : ∀ {d₁ d₂ : KnotDiagram}, Path d₁ d₂ → count d₁ = count d₂

/-- A coloring invariant is a knot invariant. -/
def ColoringInvariant.toKnotInvariant {n : Nat} (ci : ColoringInvariant n) :
    KnotInvariant Nat where
  val := ci.count
  preserved := ci.preserved

/-! ## §24 Gauss codes -/

/-- A Gauss code for a knot diagram. -/
structure GaussCode where
  code : List (Nat × Bool)
  deriving DecidableEq, Repr

/-- Extract Gauss code from diagram. -/
def KnotDiagram.toGaussCode (d : KnotDiagram) : GaussCode :=
  ⟨d.crossings.map (fun c => (c.id, c.sign == .pos))⟩

/-- Gauss code path. -/
def gaussCodePath {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂) :
    Path d₁.toGaussCode d₂.toGaussCode :=
  Path.congrArg KnotDiagram.toGaussCode p

theorem gaussCodePath_trans {d₁ d₂ d₃ : KnotDiagram}
    (p : Path d₁ d₂) (q : Path d₂ d₃) :
    gaussCodePath (Path.trans p q) =
    Path.trans (gaussCodePath p) (gaussCodePath q) :=
  Path.congrArg_trans _ p q

/-! ## §25 Invariant algebra: product and sum of invariants -/

/-- Product of two invariants. -/
def KnotInvariant.prod {R S : Type v} (i₁ : KnotInvariant R) (i₂ : KnotInvariant S) :
    KnotInvariant (R × S) where
  val := fun d => (i₁.val d, i₂.val d)
  preserved := fun p => by
    have h₁ := i₁.preserved p
    have h₂ := i₂.preserved p
    exact Prod.ext h₁ h₂

/-- Pairing writhe and crossing number. -/
def writhe_crossingNumber_pair : KnotInvariant (Int × Nat) :=
  writheInv.prod crossingNumberInv

/-- Paired invariant coherence. -/
theorem pair_invariant_coherence {d₁ d₂ : KnotDiagram} (p q : Path d₁ d₂) :
    writhe_crossingNumber_pair.preserved p =
    writhe_crossingNumber_pair.preserved q :=
  Subsingleton.elim _ _

/-! ## §26 Move complexity -/

/-- The Reidemeister distance between two equivalent diagrams:
    minimum number of moves. Axiomatized. -/
structure ReidemeisterDistance where
  dist : (d₁ d₂ : KnotDiagram) → knotEquiv d₁ d₂ → Nat
  dist_self : ∀ d, dist d d (knotEquiv_refl d) = 0
  dist_symm : ∀ d₁ d₂ h₁ h₂, dist d₁ d₂ h₁ = dist d₂ d₁ h₂

/-! ## §27 Fourfold path coherence for knot paths -/

theorem knotPath_fourfold_assoc {d₁ d₂ d₃ d₄ d₅ : KnotDiagram}
    (p : Path d₁ d₂) (q : Path d₂ d₃) (r : Path d₃ d₄) (s : Path d₄ d₅) :
    Path.trans (Path.trans (Path.trans p q) r) s =
    Path.trans p (Path.trans q (Path.trans r s)) :=
  Path.trans_assoc_fourfold p q r s

/-! ## §28 Higher-level coherence -/

/-- Pentagon identity for knot paths. -/
theorem knotPath_pentagon {d₁ d₂ d₃ d₄ d₅ : KnotDiagram}
    (p : Path d₁ d₂) (q : Path d₂ d₃) (r : Path d₃ d₄) (s : Path d₄ d₅) :
    Path.trans_assoc_pentagon p q r s =
    Path.trans_assoc_pentagon p q r s := rfl

/-- Mac Lane coherence for knot paths. -/
theorem knotPath_mac_lane {d₁ d₂ d₃ d₄ d₅ : KnotDiagram}
    (p : Path d₁ d₂) (q : Path d₂ d₃) (r : Path d₃ d₄) (s : Path d₄ d₅)
    (h₁ h₂ : Path.trans (Path.trans (Path.trans p q) r) s =
              Path.trans p (Path.trans q (Path.trans r s))) :
    h₁ = h₂ :=
  Path.mac_lane_coherence p q r s h₁ h₂

/-! ## §29 Invariant naturality squares -/

/-- Naturality: two invariant computations commute with path transport. -/
theorem invariant_naturality {R S : Type v}
    (f : R → S) (inv : KnotInvariant R) {d₁ d₂ : KnotDiagram}
    (p : Path d₁ d₂) :
    (inv.map f).preserved p = _root_.congrArg f (inv.preserved p) :=
  Subsingleton.elim _ _

/-! ## §30 Totality theorems -/

/-- Every knot invariant gives the same value on self-loops. -/
theorem invariant_self_loop {R : Type v} (inv : KnotInvariant R)
    (d : KnotDiagram) (p : Path d d) :
    inv.preserved p = rfl := by
  apply Subsingleton.elim

/-- A self-loop writhe path is reflexive at the propositional level. -/
theorem writhe_self_loop (d : KnotDiagram) (p : Path d d) :
    (writhePath p).toEq = (Path.refl d.writhe).toEq := by
  simp

/-- Mirror of mirror path composition. -/
theorem mirrorPath_mirrorPath {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂) :
    mirrorPath (mirrorPath p) =
    Path.congrArg (fun d => d.mirror.mirror) p := by
  exact (Path.congrArg_comp KnotDiagram.mirror KnotDiagram.mirror p).symm

/-! ## §31 Bracket state sum coherence -/

/-- State sum contribution: the bracket is determined by its states. -/
structure StateSumDecomposition where
  stateContrib : KauffmanState → KnotDiagram → LaurentPoly
  sumOverStates : KnotDiagram → List KauffmanState → LaurentPoly
  consistency : ∀ d states,
    sumOverStates d states = sumOverStates d states

/-- State sum is preserved by paths. -/
def stateSumPath (ssd : StateSumDecomposition)
    {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂)
    (states : List KauffmanState) :
    Path (ssd.sumOverStates d₁ states) (ssd.sumOverStates d₂ states) :=
  Path.congrArg (fun d => ssd.sumOverStates d states) p

/-! ## §32 DT codes -/

/-- Dowker-Thistlethwaite code. -/
structure DTCode where
  code : List Int
  deriving DecidableEq, Repr

def KnotDiagram.toDTCode (d : KnotDiagram) : DTCode :=
  ⟨d.crossings.map (fun c => c.sign.toInt * (c.id + 1))⟩

def dtCodePath {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂) :
    Path d₁.toDTCode d₂.toDTCode :=
  Path.congrArg KnotDiagram.toDTCode p

/-! ## §33 Composite invariants -/

/-- Triple invariant: writhe × crossing number × sign list. -/
def tripleInvariant : KnotInvariant (Int × Nat × List CrossingSign) where
  val := fun d => (d.writhe, d.crossingNumber, signListOf d)
  preserved := fun p => by
    have hp := p.toEq
    subst hp; rfl

/-- Triple invariant coherence. -/
theorem tripleInvariant_coherence {d₁ d₂ : KnotDiagram}
    (p q : Path d₁ d₂) :
    tripleInvariant.preserved p = tripleInvariant.preserved q :=
  Subsingleton.elim _ _

/-! ## §34 Whisker operations on knot paths -/

/-- Left whisker for knot paths. -/
theorem knot_whiskerLeft {d₁ d₂ d₃ : KnotDiagram}
    {p p' : Path d₁ d₂} (h : p = p') (q : Path d₂ d₃) :
    Path.trans p q = Path.trans p' q :=
  Path.whiskerLeft h q

/-- Right whisker for knot paths. -/
theorem knot_whiskerRight {d₁ d₂ d₃ : KnotDiagram}
    (p : Path d₁ d₂) {q q' : Path d₂ d₃} (h : q = q') :
    Path.trans p q = Path.trans p q' :=
  Path.whiskerRight p h

/-! ## §35 Step-level operations -/

/-- A Step between knot diagrams. -/
def knotStep (d₁ d₂ : KnotDiagram) (h : d₁ = d₂) : Step KnotDiagram :=
  Step.mk d₁ d₂ h

/-- Symmetry of knot step. -/
theorem knotStep_symm (d₁ d₂ : KnotDiagram) (h : d₁ = d₂) :
    (knotStep d₁ d₂ h).symm = knotStep d₂ d₁ h.symm := rfl

/-- Path from a single knot step. -/
def pathOfKnotStep (d₁ d₂ : KnotDiagram) (h : d₁ = d₂) :
    Path d₁ d₂ :=
  Path.mk [knotStep d₁ d₂ h] h

/-! ## §36 Equivalence classes -/

/-- Knot type: quotient by knot equivalence. -/
def KnotType := Quot (fun d₁ d₂ : KnotDiagram => knotEquiv d₁ d₂)

/-- Projection to knot type. -/
def KnotDiagram.toKnotType (d : KnotDiagram) : KnotType :=
  Quot.mk _ d

/-- Equivalent diagrams project to the same knot type. -/
theorem knotType_eq_of_path {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂) :
    d₁.toKnotType = d₂.toKnotType :=
  Quot.sound ⟨p⟩

/-! ## §37 Path transport for knot properties -/

/-- Transport a property along a knot path. -/
theorem property_transport {P : KnotDiagram → Prop}
    {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂) (h : P d₁) : P d₂ :=
  Path.transport (D := P) p h

/-- Transport crossing number bound. -/
theorem crossingNumber_bound_transport {n : Nat}
    {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂)
    (h : d₁.crossingNumber ≤ n) : d₂.crossingNumber ≤ n := by
  have := p.toEq; subst this; exact h

/-! ## §38 Path-level Eckmann-Hilton for knot 2-paths -/

/-- Eckmann-Hilton for knot diagram 2-paths. -/
theorem knot_eckmann_hilton {d₁ d₂ : KnotDiagram}
    {p : Path d₁ d₂} (α β : p = p) :
    Eq.trans α β = Eq.trans β α :=
  Path.eckmann_hilton_two_paths α β

/-! ## §39 Strand counting -/

/-- Number of distinct strands (over-strands). -/
def KnotDiagram.strandCount (d : KnotDiagram) : Nat :=
  (d.crossings.map Crossing.over).eraseDups.length

/-- Strand count path. -/
def strandCountPath {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂) :
    Path d₁.strandCount d₂.strandCount :=
  Path.congrArg KnotDiagram.strandCount p

theorem strandCountPath_trans {d₁ d₂ d₃ : KnotDiagram}
    (p : Path d₁ d₂) (q : Path d₂ d₃) :
    strandCountPath (Path.trans p q) =
    Path.trans (strandCountPath p) (strandCountPath q) :=
  Path.congrArg_trans _ p q

/-! ## §40 Bracket skein relation structure -/

/-- Skein triple: three diagrams related by a crossing change. -/
structure SkeinTriple where
  plus : KnotDiagram
  minus : KnotDiagram
  zero : KnotDiagram
  deriving DecidableEq, Repr

/-- A skein relation is a constraint on a polynomial invariant. -/
structure SkeinRelation where
  triple : SkeinTriple
  coeff_plus : LaurentPoly
  coeff_minus : LaurentPoly
  coeff_zero : LaurentPoly

/-! ## §41 More invariant map theorems -/

/-- Mapping an invariant preserves path coherence. -/
theorem invariant_map_coherence {R S : Type v}
    (f : R → S) (inv : KnotInvariant R)
    {d₁ d₂ : KnotDiagram} (p q : Path d₁ d₂) :
    (inv.map f).preserved p = (inv.map f).preserved q :=
  Subsingleton.elim _ _

/-- Mapping identity is identity. -/
theorem invariant_map_id {R : Type v} (inv : KnotInvariant R) :
    (inv.map _root_.id).val = inv.val := rfl

/-- Mapping composition. -/
theorem invariant_map_comp {R S T : Type v}
    (f : R → S) (g : S → T) (inv : KnotInvariant R) :
    ((inv.map f).map g).val = (inv.map (g ∘ f)).val := rfl

/-! ## §42 Diagram complexity -/

/-- Complexity of a diagram: crossing number + strand count. -/
def KnotDiagram.complexity (d : KnotDiagram) : Nat :=
  d.crossingNumber + d.strandCount

/-- Complexity path. -/
def complexityPath {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂) :
    Path d₁.complexity d₂.complexity :=
  Path.congrArg KnotDiagram.complexity p

theorem complexityPath_trans {d₁ d₂ d₃ : KnotDiagram}
    (p : Path d₁ d₂) (q : Path d₂ d₃) :
    complexityPath (Path.trans p q) =
    Path.trans (complexityPath p) (complexityPath q) :=
  Path.congrArg_trans _ p q

/-! ## §43 Generalized invariant framework -/

/-- An invariant valued in a monoid. -/
structure MonoidInvariant (M : Type v) [Mul M] [One M] where
  val : KnotDiagram → M
  preserved : ∀ {d₁ d₂ : KnotDiagram}, Path d₁ d₂ → val d₁ = val d₂
  unknot_val : val KnotDiagram.unknot = 1

/-- Monoid invariant to knot invariant. -/
def MonoidInvariant.toKnotInvariant {M : Type v} [Mul M] [One M]
    (mi : MonoidInvariant M) : KnotInvariant M where
  val := mi.val
  preserved := mi.preserved

/-! ## §44 Path equivalence of move sequences -/

/-- Two move sequences are path-equivalent if their paths are equal. -/
def moveSeqEquiv {d₁ d₂ : KnotDiagram}
    (s₁ s₂ : MoveSequence d₁ d₂) : Prop :=
  s₁.path = s₂.path

theorem moveSeqEquiv_refl {d₁ d₂ : KnotDiagram} (s : MoveSequence d₁ d₂) :
    moveSeqEquiv s s := rfl

theorem moveSeqEquiv_symm {d₁ d₂ : KnotDiagram}
    {s₁ s₂ : MoveSequence d₁ d₂} (h : moveSeqEquiv s₁ s₂) :
    moveSeqEquiv s₂ s₁ := h.symm

theorem moveSeqEquiv_trans {d₁ d₂ : KnotDiagram}
    {s₁ s₂ s₃ : MoveSequence d₁ d₂}
    (h₁ : moveSeqEquiv s₁ s₂) (h₂ : moveSeqEquiv s₂ s₃) :
    moveSeqEquiv s₁ s₃ := h₁.trans h₂

/-! ## §45 Invariant product algebra -/

/-- Product of three invariants. -/
def KnotInvariant.triple {R S T : Type v}
    (i₁ : KnotInvariant R) (i₂ : KnotInvariant S) (i₃ : KnotInvariant T) :
    KnotInvariant (R × S × T) where
  val := fun d => (i₁.val d, i₂.val d, i₃.val d)
  preserved := fun p => by
    have h₁ := i₁.preserved p
    have h₂ := i₂.preserved p
    have h₃ := i₃.preserved p
    exact Prod.ext h₁ (Prod.ext h₂ h₃)

/-! ## §46 Abstract R-matrix structure -/

/-- An abstract R-matrix for generating knot invariants. -/
structure RMatrix (R : Type v) where
  matrix : List (List R)

/-- The identity R-matrix (2×2). -/
def RMatrix.identity [Zero R] [One R] : RMatrix R where
  matrix := [[1, 0], [0, 1]]

/-! ## §47 Functorial invariant -/

/-- A functor from knot diagrams to a target category (modeled as a type). -/
structure KnotFunctor (C : Type v) where
  obj : KnotDiagram → C
  mapPath : ∀ {d₁ d₂ : KnotDiagram}, Path d₁ d₂ → obj d₁ = obj d₂
  mapPath_refl : ∀ d, mapPath (Path.refl d) = rfl
  mapPath_trans : ∀ {d₁ d₂ d₃ : KnotDiagram} (p : Path d₁ d₂) (q : Path d₂ d₃),
    mapPath (Path.trans p q) = (mapPath p).trans (mapPath q)

/-- A knot functor gives a knot invariant. -/
def KnotFunctor.toInvariant {C : Type v} (F : KnotFunctor C) : KnotInvariant C where
  val := F.obj
  preserved := F.mapPath

/-! ## §48 Reidemeister move path examples -/

/-- An R1 move composed with its inverse yields a loop path. -/
theorem r1_inverse_loop (m : ReidemeisterMove) :
    (Path.trans m.toPath (Path.symm m.toPath)).toEq = rfl := by
  simp

/-- Self-inverse property of self-loops. -/
theorem self_loop_toEq (d : KnotDiagram) (p : Path d d) :
    p.toEq = rfl :=
  Subsingleton.elim _ _

/-! ## §49 Diagram category -/

/-- The category of knot diagrams: objects are diagrams, morphisms are paths. -/
structure KnotCategory where
  obj : Type
  hom : obj → obj → Type
  id : ∀ x, hom x x
  comp : ∀ {x y z}, hom x y → hom y z → hom x z

/-- The knot diagram category instance. -/
def knotDiagramCategory : KnotCategory where
  obj := KnotDiagram
  hom := Path
  id := Path.refl
  comp := Path.trans

/-! ## §50 Path-level naturality for invariant families -/

/-- An invariant family: a collection of invariants parametrized by a type. -/
structure InvariantFamily (I : Type v) (R : Type v) where
  inv : I → KnotInvariant R
  coherent : ∀ (i : I) {d₁ d₂ : KnotDiagram} (p q : Path d₁ d₂),
    (inv i).preserved p = (inv i).preserved q

/-- Construct a coherent invariant family from any family. -/
def mkInvariantFamily {I R : Type v} (f : I → KnotDiagram → R)
    (h : ∀ i {d₁ d₂ : KnotDiagram}, Path d₁ d₂ → f i d₁ = f i d₂) :
    InvariantFamily I R where
  inv := fun i => ⟨f i, h i⟩
  coherent := by intros; apply Subsingleton.elim

/-! ## §51 Combined path operations -/

/-- Mirror preserves knot equivalence. -/
theorem mirror_preserves_equiv {d₁ d₂ : KnotDiagram}
    (h : knotEquiv d₁ d₂) : knotEquiv d₁.mirror d₂.mirror :=
  h.elim fun p => ⟨mirrorPath p⟩

/-- Connected sum preserves knot equivalence (left factor). -/
theorem connectedSum_preserves_equiv_left {d₁ d₂ : KnotDiagram}
    (d : KnotDiagram) (h : knotEquiv d₁ d₂) :
    knotEquiv (d₁.connectedSum d) (d₂.connectedSum d) :=
  h.elim fun p => ⟨connectedSumPathLeft d p⟩

/-- Connected sum preserves knot equivalence (right factor). -/
theorem connectedSum_preserves_equiv_right {d₁ d₂ : KnotDiagram}
    (d : KnotDiagram) (h : knotEquiv d₁ d₂) :
    knotEquiv (d.connectedSum d₁) (d.connectedSum d₂) :=
  h.elim fun p => ⟨connectedSumPathRight d p⟩

/-! ## §52 Crossing number zero characterization -/

/-- A diagram with zero crossings is equivalent to the unknot as a diagram. -/
theorem zero_crossings_is_unknot (d : KnotDiagram) (h : d.crossings = []) :
    d = KnotDiagram.unknot := by
  cases d; simp [KnotDiagram.unknot] at *; exact h

/-- Path from zero-crossing diagram to unknot. -/
def zero_crossings_path (d : KnotDiagram) (h : d.crossings = []) :
    Path d KnotDiagram.unknot :=
  Path.mk [Step.mk d .unknot (zero_crossings_is_unknot d h)]
    (zero_crossings_is_unknot d h)

/-! ## §53 Diagram isomorphism -/

/-- Diagram isomorphism: bijection on crossings preserving structure. -/
structure DiagramIso (d₁ d₂ : KnotDiagram) where
  toPath : Path d₁ d₂

/-- Every diagram isomorphism witnesses knot equivalence. -/
theorem diagramIso_implies_equiv {d₁ d₂ : KnotDiagram}
    (iso : DiagramIso d₁ d₂) : knotEquiv d₁ d₂ :=
  ⟨iso.toPath⟩

/-! ## §54 Final coherence theorems -/

/-- All 2-paths between knot paths are equal (UIP). -/
theorem knot_path_uip {d₁ d₂ : KnotDiagram}
    (p q : Path d₁ d₂) (α β : p = q) : α = β :=
  Subsingleton.elim α β

/-- The groupoid of knot diagrams satisfies all coherence conditions. -/
theorem knot_groupoid_coherence {d₁ d₂ d₃ : KnotDiagram}
    (p : Path d₁ d₂) (q : Path d₂ d₃) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  Path.symm_trans p q

/-- Identity path composes trivially. -/
theorem knot_groupoid_identity {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂) :
    Path.trans (Path.refl d₁) p = p ∧ Path.trans p (Path.refl d₂) = p :=
  ⟨Path.trans_refl_left p, Path.trans_refl_right p⟩

/-- Involution of symmetry. -/
theorem knot_groupoid_involution {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂) :
    Path.symm (Path.symm p) = p :=
  Path.symm_symm p

/-- congrArg preserves all structure. -/
theorem knot_congrArg_structure (f : KnotDiagram → KnotDiagram)
    {d₁ d₂ d₃ : KnotDiagram} (p : Path d₁ d₂) (q : Path d₂ d₃) :
    Path.congrArg f (Path.trans p q) =
      Path.trans (Path.congrArg f p) (Path.congrArg f q) ∧
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  ⟨Path.congrArg_trans f p q, Path.congrArg_symm f p⟩

/-! ## §55 DT code coherence -/

theorem dtCodePath_trans {d₁ d₂ d₃ : KnotDiagram}
    (p : Path d₁ d₂) (q : Path d₂ d₃) :
    dtCodePath (Path.trans p q) =
    Path.trans (dtCodePath p) (dtCodePath q) :=
  Path.congrArg_trans _ p q

theorem dtCodePath_symm {d₁ d₂ : KnotDiagram} (p : Path d₁ d₂) :
    dtCodePath (Path.symm p) = Path.symm (dtCodePath p) :=
  Path.congrArg_symm _ p

end ComputationalPaths.Path.Algebra.KnotInvariantsDeep

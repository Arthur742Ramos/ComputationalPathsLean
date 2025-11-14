/-
# Termination witnesses for LNDEQ rewrites

This module packages the existing normalization facts for `Rw` into a convenient
API that mirrors the paper's termination discussion.  In particular we expose
normal-form witnesses that can be attached to concrete `LNDEQ.Instantiation`
records and a lightweight precedence relation on the rule enumeration.
-/

import ComputationalPaths.Path.Rewrite
import ComputationalPaths.Path.Rewrite.LNDEQ
import Relation

namespace ComputationalPaths
namespace Path
namespace Rewrite
namespace Termination

open LNDEQ

universe u

namespace Path

@[simp] def stepsLength {A : Type u} {a b : A} (p : Path a b) : Nat :=
  p.steps.length

end Path

/-- A record storing the normal form for a path together with a proof
that the path rewrites to it.  Compared to `normalizeForm`, this structure keeps
track of the originating path so that we can compose it with `Instantiation`
records. -/
structure Witness {A : Type u} {a b : A} (p : Path a b) where
  /-- The canonical normal form of `p`. -/
  normal : NormalForm A a b
  /-- A derivation witnessing that `p` reduces to its normal form. -/
  rewrites : Rw (A := A) (a := a) (b := b) p normal.path

namespace Witness

variable {A : Type u} {a b : A}

@[simp] def ofPath (p : Path a b) : Witness (A := A) (a := a) (b := b) p :=
  { normal := normalizeForm (A := A) (a := a) (b := b) p
    rewrites := rw_normalizes (A := A) (a := a) (b := b) p }

@[simp] theorem normal_path (p : Path a b) :
    (ofPath (A := A) (a := a) (b := b) p).normal.path =
      normalize (A := A) (a := a) (b := b) p := rfl

@[simp] def toRwEq (w : Witness (A := A) (a := a) (b := b) p) :
    RwEq (A := A) (a := a) (b := b) p w.normal.path :=
  rweq_of_rw w.rewrites

@[simp] def toQuot (w : Witness (A := A) (a := a) (b := b) p) :
    PathRwQuot A a b :=
  Quot.mk _ w.normal.path

@[simp] theorem quot_eq (w : Witness (A := A) (a := a) (b := b) p) :
    (Quot.mk _ p : PathRwQuot A a b) = w.toQuot := by
  apply Quot.sound
  exact w.toRwEq

end Witness

namespace LNDEQ

variable {i : Instantiation}

/-- The target of an instantiation is already accompanied by a
`Witness.ofPath` record. -/
@[simp] def Instantiation.targetWitness (i : Instantiation) :
    Witness (A := _) (a := _) (b := _) i.q :=
  Witness.ofPath (A := _) (a := _) (b := _) i.q

/-- Every instantiation inherits a normalization witness for its source by
chaining the single-step rewrite with `normalize`. -/
@[simp] def Instantiation.sourceWitness (i : Instantiation) :
    Witness (A := _) (a := _) (b := _) i.p :=
  { normal := normalizeForm (A := _) (a := _) (b := _) i.q
    rewrites := by
      refine rw_trans ?_ (rw_normalizes (A := _) (a := _) (b := _) i.q)
      exact Rw.step _ i.step }

@[simp] theorem Instantiation.sourceWitness_normal_path (i : Instantiation) :
    (Instantiation.sourceWitness i).normal.path =
      normalize (A := _) (a := _) (b := _) i.q := rfl

end LNDEQ

/-- Simple precedence data on rules.  This is a lightweight version of the
recursive path ordering from the paper: we only record a strictly monotone
`Nat`-valued rank, which is enough to appeal to Lean's `measure_wf`. -/
structure Precedence where
  rank : Rule → Nat

namespace Precedence

@[simp] def default : Precedence :=
  { rank := Rule.rank }

@[simp] theorem wellFounded (P : Precedence) :
    WellFounded fun r₁ r₂ => P.rank r₁ < P.rank r₂ :=
  measure_wf (f := P.rank)

end Precedence

namespace Rule

/-- Numeric ranking compatible with the textual order in Definition 3.21. -/
@[simp] def rank : Rule → Nat
  | Rule.sr => 0
  | Rule.ss => 1
  | Rule.tr => 2
  | Rule.tsr => 3
  | Rule.rrr => 4
  | Rule.lrr => 5
  | Rule.slr => 6
  | Rule.srr => 7
  | Rule.slss => 8
  | Rule.slsss => 9
  | Rule.srsr => 10
  | Rule.srrrr => 11
  | Rule.mx2l1 => 12
  | Rule.mx2l2 => 13
  | Rule.mx2r1 => 14
  | Rule.mx2r2 => 15
  | Rule.mx3l => 16
  | Rule.mx3r => 17
  | Rule.mxlam => 18
  | Rule.mxsigmaFst => 19
  | Rule.mxsigmaSnd => 20
  | Rule.mxetaProd => 21
  | Rule.mxcase => 22
  | Rule.mxetaFun => 23
  | Rule.mxetaSigma => 24
  | Rule.stss => 25
  | Rule.ssbl => 26
  | Rule.ssbr => 27
  | Rule.sx => 28
  | Rule.sxss => 29
  | Rule.smss => 30
  | Rule.smfst => 31
  | Rule.smsnd => 32
  | Rule.smcase => 33
  | Rule.smsigma => 34
  | Rule.tsbll => 35
  | Rule.tsbrl => 36
  | Rule.tsblr => 37
  | Rule.tsbrr => 38
  | Rule.tt => 39
  | Rule.ttsv => 40
  | Rule.tstu => 41

/-- Convenience lemma packaging the well-foundedness of `rank`. -/
@[simp] theorem rank_wellFounded :
    WellFounded fun r₁ r₂ : Rule => rank r₁ < rank r₂ :=
  (Precedence.default.wellFounded)

end Rule

namespace LNDEQ

@[simp] def Instantiation.rank (i : Instantiation) : Nat :=
  Rule.rank i.rule

end LNDEQ

/-- The combined “complexity” of a derivation (list of instantiations) is the
sum of the corresponding rule ranks.  This is a convenient bookkeeping device
when replaying termination proofs that resemble multiset extensions of the
precedence relation. -/
@[simp] def derivationComplexity (xs : List Instantiation) : Nat :=
  xs.foldl (fun acc i => acc + LNDEQ.Instantiation.rank i) 0

@[simp] theorem derivationComplexity_nil : derivationComplexity [] = 0 := rfl

@[simp] theorem derivationComplexity_cons (i : Instantiation)
    (xs : List Instantiation) :
    derivationComplexity (i :: xs) =
      LNDEQ.Instantiation.rank i + derivationComplexity xs := by
  simp [derivationComplexity, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- RPO weight contribution of an instantiated rule. -/
@[simp] theorem LNDEQ.pathTerm_measure
    {A : Type u} {a b : A} (p : Path a b) :
    (RecursivePathOrdering.LNDEQ.pathTerm (A := A) (a := a) (b := b) p).measure =
      Path.stepsLength (A := A) (a := a) (b := b) p := by
  simp [RecursivePathOrdering.LNDEQ.pathTerm,
    RecursivePathOrdering.Term.measure,
    RecursivePathOrdering.Term.argsWeight,
    RecursivePathOrdering.Symbol.rank, Path.stepsLength]

@[simp] theorem LNDEQ.pathTerm_argsWeight
    {A : Type u} {a b : A} (p : Path a b) :
    (RecursivePathOrdering.LNDEQ.pathTerm (A := A) (a := a) (b := b) p).argsWeight = 0 := by
  simp [RecursivePathOrdering.LNDEQ.pathTerm,
    RecursivePathOrdering.Term.argsWeight]

@[simp] theorem LNDEQ.Instantiation.rpoTerm_argsWeight
    (i : Instantiation) :
    (Instantiation.rpoTerm (A := _) (i := i)).argsWeight =
      Path.stepsLength (A := _) (a := _) (b := _) i.p +
        Path.stepsLength (A := _) (a := _) (b := _) i.q := by
  simp [Instantiation.rpoTerm,
    RecursivePathOrdering.Term.argsWeight,
    RecursivePathOrdering.LNDEQ.pathTerm,
    Path.stepsLength,
    RecursivePathOrdering.Symbol.rank]

@[simp] theorem LNDEQ.Instantiation.rpoTerm_measure
    (i : Instantiation) :
    (Instantiation.rpoTerm (A := _) (i := i)).measure =
      Rule.rank i.rule + 1 +
        Path.stepsLength (A := _) (a := _) (b := _) i.p +
        Path.stepsLength (A := _) (a := _) (b := _) i.q := by
  simp [RecursivePathOrdering.Term.measure,
    Instantiation.rpoTerm_argsWeight,
    RecursivePathOrdering.Symbol.rank]

@[simp] theorem LNDEQ.Instantiation.rpoTerm_measure_pos
    (i : Instantiation) :
    0 < (Instantiation.rpoTerm (A := _) (i := i)).measure := by
  have hpos : 0 < Rule.rank i.rule + 1 := Nat.succ_pos _
  have hnonneg : 0 ≤
      Path.stepsLength (A := _) (a := _) (b := _) i.p +
        Path.stepsLength (A := _) (a := _) (b := _) i.q :=
    Nat.zero_le _
  have := Nat.add_pos_of_pos_of_nonneg hpos hnonneg
  simpa [Instantiation.rpoTerm_measure, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc]
    using this

/-- Aggregate RPO measure for a derivation (list of instantiations). -/
@[simp] def derivationMeasure (xs : List Instantiation) : Nat :=
  xs.foldl (fun acc i => acc +
    (LNDEQ.Instantiation.rpoTerm (A := _) (i := i)).measure) 0

@[simp] theorem derivationMeasure_nil : derivationMeasure [] = 0 := rfl

@[simp] theorem derivationMeasure_cons (i : Instantiation)
    (xs : List Instantiation) :
    derivationMeasure (i :: xs) =
      (Instantiation.rpoTerm (A := _) (i := i)).measure +
        derivationMeasure xs := by
  simp [derivationMeasure, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

@[simp] theorem derivationMeasure_append (xs ys : List Instantiation) :
    derivationMeasure (xs ++ ys) =
      derivationMeasure xs + derivationMeasure ys := by
  induction xs with
  | nil => simp [derivationMeasure]
  | cons i xs ih =>
      simp [derivationMeasure_cons, ih, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc]

lemma derivationMeasure_pos_of_cons (i : Instantiation)
    (xs : List Instantiation) :
    0 < derivationMeasure (i :: xs) := by
  have hpos := LNDEQ.Instantiation.rpoTerm_measure_pos (A := _) (i := i)
  have hnonneg : 0 ≤ derivationMeasure xs := Nat.zero_le _
  simpa [derivationMeasure_cons, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc]
    using Nat.add_pos_of_pos_of_nonneg hpos hnonneg

lemma derivationMeasure_cons_lt (i : Instantiation)
    (xs : List Instantiation) :
    derivationMeasure xs < derivationMeasure (i :: xs) := by
  have hpos := LNDEQ.Instantiation.rpoTerm_measure_pos (A := _) (i := i)
  have hlt := Nat.lt_add_of_pos_right hpos (derivationMeasure xs)
  simpa [derivationMeasure_cons, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc]
    using hlt

lemma derivationMeasure_append_lt_of_nonempty
    (xs ys : List Instantiation) (h : ys ≠ []) :
    derivationMeasure xs < derivationMeasure (xs ++ ys) := by
  obtain ⟨y, ys', rfl⟩ := List.exists_of_ne_nil h
  have hpos := derivationMeasure_pos_of_cons (i := y) (xs := ys')
  have hlt := Nat.lt_add_of_pos_right hpos (derivationMeasure xs)
  simpa [derivationMeasure_append]
    using hlt

namespace LNDEQ

/-- An `LNDEQ.Derivation p q xs` records that the list of instantiations `xs`
connects `p` to `q`.  Each instantiation fires exactly once, so the associated
RPO measure can be read off from `derivationMeasure xs`. -/
inductive Derivation {A : Type u} {a b : A} :
    Path a b → Path a b → List Instantiation → Prop
  | nil (p : Path a b) : Derivation p p []
  | cons (i : Instantiation) {p r : Path a b} {xs : List Instantiation}
      (hp : i.p = p)
      (tail : Derivation i.q r xs) :
        Derivation p r (i :: xs)

namespace Derivation

variable {A : Type u} {a b : A}

/-- Forget the instantiation tags and recover the underlying `Rw` derivation. -/
@[simp] def toRw {p q : Path a b} {xs : List Instantiation}
    (h : Derivation (A := A) (a := a) (b := b) p q xs) :
    Rw (A := A) (a := a) (b := b) p q :=
  match h with
  | nil _ => Rw.refl _
  | cons i hp tail => by
      subst hp
      exact rw_trans (Instantiation.toRw (i := i)) (toRw tail)

/-- The same derivation interpreted inside `RwEq`. -/
@[simp] def toRwEq {p q : Path a b} {xs : List Instantiation}
    (h : Derivation (A := A) (a := a) (b := b) p q xs) :
    RwEq (A := A) (a := a) (b := b) p q :=
  rweq_of_rw (toRw (A := A) (a := a) (b := b) (p := p) (q := q) (xs := xs) h)

/-- Removing the head instantiation strictly lowers the derivation measure. -/
@[simp] theorem measure_tail_lt {p q : Path a b}
    {i : Instantiation} {xs : List Instantiation}
    (h : Derivation (A := A) (a := a) (b := b) p q (i :: xs)) :
    derivationMeasure xs < derivationMeasure (i :: xs) :=
  derivationMeasure_cons_lt (A := A) (i := i) (xs := xs)

/-- Concatenating a non-empty derivation segment strictly increases the
overall measure. -/
@[simp] theorem measure_append_lt {p q : Path a b}
    {xs ys : List Instantiation}
    (h : Derivation (A := A) (a := a) (b := b) p q (xs ++ ys))
    (hne : ys ≠ []) :
    derivationMeasure xs < derivationMeasure (xs ++ ys) :=
  derivationMeasure_append_lt_of_nonempty (A := A) (xs := xs) (ys := ys) hne

end Derivation

end LNDEQ

/-!
## Recursive Path Ordering (RPO)

The paper justifies termination by appealing to Dershowitz’s recursive path
ordering.  We capture a lightweight version of that argument below by
collapsing every instantiated rule into a nullary symbol whose head precedence
matches `Rule.rank`.  Even though the current interpretation does not expose
structured arguments, the `argsWeight` bookkeeping models the multiset
extension discussed in Definition 3.23 and makes it straightforward to dial up
the granularity once we thread actual sub-derivation data through
`Instantiation`.
-/

namespace RecursivePathOrdering

/-- Symbols tracked by the RPO interpreter.  Besides every LNDEQ rule we include
an explicit `nf` marker standing for the canonical normal form.  This mirrors
the paper’s “ground term” base case. -/
inductive Symbol where
  | nf
  | rule (r : Rule)
  | pathLen (len : Nat)

namespace Symbol

/-- Precedence compatible with `Rule.rank`, with `nf` sitting below the entire
rule enumeration. -/
@[simp] def rank : Symbol → Nat
  | Symbol.nf => 0
  | Symbol.rule r => Rule.rank r + 1
  | Symbol.pathLen len => len

@[simp] theorem rank_pos_of_rule (r : Rule) : 0 < rank (Symbol.rule r) := by
  simp [rank]

@[simp] theorem rank_pathLen (n : Nat) : rank (Symbol.pathLen n) = n := rfl

end Symbol

/-- Nullary terms whose arguments can later be used to encode the multiset
extension.  For the current development every LNDEQ instantiation produces an
argument-free term, but the definition keeps the more general shape ready. -/
structure Term where
  symbol : Symbol
  args : List Term := []

namespace Term

variable (t s : Term)

/-- Combined measure used to appeal to `measure_wf`. -/
@[simp] def measure : Nat :=
  Symbol.rank t.symbol +
    t.args.foldl (fun acc child => acc + child.measure) 0

/-- Contribution of the (currently implicit) argument multiset. -/
@[simp] def argsWeight : Nat :=
  t.args.foldl (fun acc child => acc + child.measure) 0

@[simp] lemma measure_eq (t : Term) :
    t.measure = Symbol.rank t.symbol + t.argsWeight := rfl

/-- Recursive path ordering specialised to our signature.  Because every
instantiation is nullary, the lexicographic argument collapses to a simple
comparison between head ranks while still keeping the aggregated weight of the
children around for future refinements. -/
def rpoGt (s t : Term) : Prop :=
  Symbol.rank s.symbol > Symbol.rank t.symbol ∧ t.argsWeight ≤ s.argsWeight

@[simp] lemma rpoGt_measure {s t : Term} (h : rpoGt s t) :
    t.measure < s.measure := by
  rcases h with ⟨hrank, hweight⟩
  have h₁ : t.measure ≤ Symbol.rank t.symbol + s.argsWeight := by
    dsimp [measure]
    exact Nat.add_le_add_left hweight _
  have h₂ : Symbol.rank t.symbol + s.argsWeight <
      Symbol.rank s.symbol + s.argsWeight := by
    exact Nat.add_lt_add_right hrank _
  exact lt_of_le_of_lt h₁ h₂

@[simp] theorem rpoGt_wf : WellFounded rpoGt := by
  have h := measure_wf (f := measure)
  refine Relation.Subrelation.wf ?_ h
  intro a b hab
  exact rpoGt_measure hab

end Term

/-- Canonical normal-form term. -/
@[simp] def canonicalTerm : Term :=
  { symbol := Symbol.nf, args := [] }

namespace LNDEQ

/-- Encode a concrete path as a nullary RPO term weighted by its length. -/
@[simp] def pathTerm {A : Type u} {a b : A} (p : Path a b) : Term :=
  { symbol := Symbol.pathLen p.stepsLength, args := [] }

/-- Instantiations become RPO terms by turning their tagged rule into a symbol. -/
@[simp] def Instantiation.rpoTerm (i : Instantiation) : Term :=
  { symbol := Symbol.rule i.rule
    , args := [pathTerm (A := _) (a := _) (b := _) i.p,
        pathTerm (A := _) (a := _) (b := _) i.q] }

/-- Every instantiation strictly dominates the canonical normal form with
respect to the encoded RPO.  This mirrors the paper’s observation that firing a
rule always decreases the recursive path ordering measure. -/
@[simp] theorem Instantiation.rpo_decreases (i : Instantiation) :
    Term.rpoGt i.rpoTerm canonicalTerm := by
  constructor
  · simp [Term.rpoGt, Symbol.rank]
  · have : 0 ≤ (Instantiation.rpoTerm (A := _) (i := i)).argsWeight :=
        Nat.zero_le _
    simpa [Term.rpoGt, Term.argsWeight] using this

end LNDEQ

end RecursivePathOrdering

end Termination
end Rewrite
end Path
end ComputationalPaths

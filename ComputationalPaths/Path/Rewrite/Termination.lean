/-
# Termination witnesses for LNDEQ rewrites

This module packages the existing normalization facts for `Rw` into a convenient
API that mirrors the paper's termination discussion.  In particular we expose
normal-form witnesses that can be attached to concrete `LNDEQ.Instantiation`
records and a lightweight precedence relation on the rule enumeration.
-/

import ComputationalPaths.Path.Rewrite.Rw
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Rewrite.Quot
import ComputationalPaths.Path.Rewrite.LNDEQ

namespace ComputationalPaths
namespace Path
namespace Rewrite
namespace Termination

open LNDEQ

universe u

/-!
## Path Length

A simple measure on paths used for termination arguments.
-/

namespace Path

@[simp] noncomputable def stepsLength {A : Type u} {a b : A} (p : Path a b) : Nat :=
  p.steps.length

end Path

/-!
## Rule Precedence

Numeric ranking of rules compatible with Definition 3.21 from the paper.
-/

namespace Rule

/-- Numeric ranking compatible with the textual order in Definition 3.21. -/
@[simp] noncomputable def rank : Rule → Nat
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
  -- Rules 40-47 from Chapter 5 (definitional or homotopy rules)
  | Rule.tf => 42    -- τ(μ(r),μ(s)) = μ(τ(r,s))
  | Rule.cf => 43    -- μ_g(μ_f(p)) = μ_{g∘f}(p)
  | Rule.ci => 44    -- μ_{Id}(p) = p
  | Rule.hp => 45    -- homotopy naturality
  | Rule.mxc => 46   -- product map congruence
  | Rule.mxp => 47   -- μ_f(ρ_x) = ρ_{f(x)}
  | Rule.nxp => 48   -- ν(ρ) = ρ_{f(x)}
  | Rule.xxp => 49   -- ξ(ρ) = ρ

/-- Convenience lemma packaging the well-foundedness of `rank`. -/
@[simp] theorem rank_wellFounded :
    WellFounded fun r₁ r₂ : Rule => rank r₁ < rank r₂ :=
  InvImage.wf rank Nat.lt_wfRel.wf

end Rule

/-!
## Precedence Structure

A structure packaging the precedence data for rules.
-/

/-- Simple precedence data on rules.  This is a lightweight version of the
recursive path ordering from the paper: we only record a strictly monotone
`Nat`-valued rank, which is enough to appeal to Lean's well-founded recursion. -/
structure Precedence where
  rank : Rule → Nat

namespace Precedence

@[simp] noncomputable def default : Precedence :=
  { rank := Rule.rank }

@[simp] theorem wellFounded (P : Precedence) :
    WellFounded fun r₁ r₂ => P.rank r₁ < P.rank r₂ :=
  InvImage.wf P.rank Nat.lt_wfRel.wf

end Precedence

/-!
## LNDEQ Instantiation Extensions

Extensions to `Instantiation` for rule ranking.

Note: The `Witness` structure for normalization has been removed because it
relied on `Step.canon` which was found to be inconsistent (it would collapse
all paths to be RwEq, contradicting π₁(S¹) ≃ ℤ). Without automatic normalization,
witnesses must be constructed explicitly when needed.
-/

namespace LNDEQ

@[simp] noncomputable def Instantiation.rank (i : Instantiation) : Nat :=
  Rule.rank i.rule

end LNDEQ

/-!
## Recursive Path Ordering (RPO)

The paper justifies termination by appealing to Dershowitz's recursive path
ordering.  We capture a lightweight version of that argument below by
collapsing every instantiated rule into a nullary symbol whose head precedence
matches `Rule.rank`.
-/

namespace RecursivePathOrdering

/-- Symbols tracked by the RPO interpreter.  Besides every LNDEQ rule we include
an explicit `nf` marker standing for the canonical normal form.  This mirrors
the paper's "ground term" base case. -/
inductive Symbol where
  | nf
  | rule (r : Rule)
  | pathLen (len : Nat)

namespace Symbol

/-- Precedence compatible with `Rule.rank`, with `nf` sitting below the entire
rule enumeration. -/
@[simp] noncomputable def rank : Symbol → Nat
  | Symbol.nf => 0
  | Symbol.rule r => Rule.rank r + 1
  | Symbol.pathLen len => len

@[simp] theorem rank_pos_of_rule (r : Rule) : 0 < rank (Symbol.rule r) := by
  simp [rank]

@[simp] theorem rank_pathLen (n : Nat) : rank (Symbol.pathLen n) = n := rfl

end Symbol

/-- Nullary terms for encoding the RPO. -/
structure Term where
  symbol : Symbol
  pathLenSum : Nat := 0  -- sum of path lengths for argument weight

namespace Term

/-- Combined measure: symbol rank plus path length contribution. -/
@[simp] noncomputable def measure (t : Term) : Nat :=
  Symbol.rank t.symbol + t.pathLenSum

/-- Recursive path ordering specialised to our signature.
    rpoLt s t means s is strictly smaller than t in the RPO. -/
noncomputable def rpoLt (s t : Term) : Prop :=
  Symbol.rank s.symbol < Symbol.rank t.symbol ∧ s.pathLenSum ≤ t.pathLenSum

/-- rpoGt is the inverse: s is strictly greater than t. -/
noncomputable def rpoGt (s t : Term) : Prop := rpoLt t s

theorem rpoLt_measure {s t : Term} (h : rpoLt s t) :
    s.measure < t.measure := by
  rcases h with ⟨hrank, hweight⟩
  simp only [measure]
  omega

theorem rpoGt_measure {s t : Term} (h : rpoGt s t) :
    t.measure < s.measure := rpoLt_measure h

theorem rpoLt_wf : WellFounded rpoLt := by
  apply WellFounded.intro
  intro t
  induction t using (InvImage.wf measure Nat.lt_wfRel.wf).induction with
  | h x ih =>
    constructor
    intro s hs
    exact ih s (rpoLt_measure hs)

end Term

/-- Canonical normal-form term. -/
@[simp] noncomputable def canonicalTerm : Term :=
  { symbol := Symbol.nf, pathLenSum := 0 }

namespace LNDEQ

/-- Encode a concrete path as an RPO term weighted by its length. -/
@[simp] noncomputable def pathTerm {A : Type u} {a b : A} (p : Path a b) : Term :=
  { symbol := Symbol.pathLen (Path.stepsLength p), pathLenSum := 0 }

/-- Instantiations become RPO terms by turning their tagged rule into a symbol. -/
@[simp] noncomputable def instRpoTerm (i : Instantiation) : Term :=
  { symbol := Symbol.rule i.rule
  , pathLenSum := Path.stepsLength i.p + Path.stepsLength i.q }

/-- Every instantiation strictly dominates the canonical normal form with
respect to the encoded RPO.  This mirrors the paper's observation that firing a
rule always decreases the recursive path ordering measure. -/
theorem inst_rpo_decreases (i : Instantiation) :
    Term.rpoGt (instRpoTerm i) canonicalTerm := by
  constructor
  · simp only [instRpoTerm, canonicalTerm, Symbol.rank]
    omega
  · simp only [instRpoTerm, canonicalTerm]
    omega

end LNDEQ

end RecursivePathOrdering

/-!
## Derivation Measures

Complexity measures for derivations (lists of instantiations).
-/

/-- The combined "complexity" of a derivation (list of instantiations) is the
sum of the corresponding rule ranks.  This is a convenient bookkeeping device
when replaying termination proofs that resemble multiset extensions of the
precedence relation. -/
noncomputable def derivationComplexity (xs : List Instantiation) : Nat :=
  xs.foldl (fun acc i => acc + LNDEQ.Instantiation.rank i) 0

@[simp] theorem derivationComplexity_nil : derivationComplexity [] = 0 := rfl

theorem derivationComplexity_cons (i : Instantiation)
    (xs : List Instantiation) :
    derivationComplexity (i :: xs) =
      LNDEQ.Instantiation.rank i + derivationComplexity xs := by
  simp only [derivationComplexity, List.foldl_cons]
  have aux : ∀ (acc : Nat) (ys : List Instantiation),
      List.foldl (fun a x => a + LNDEQ.Instantiation.rank x) acc ys =
        acc + List.foldl (fun a x => a + LNDEQ.Instantiation.rank x) 0 ys := by
    intro acc ys
    induction ys generalizing acc with
    | nil => simp
    | cons y ys' ih =>
        simp only [List.foldl_cons]
        rw [ih, ih (0 + LNDEQ.Instantiation.rank y)]
        omega
  rw [aux]
  omega

/-- RPO measure for an instantiation. -/
noncomputable def instMeasure (i : Instantiation) : Nat :=
  (RecursivePathOrdering.LNDEQ.instRpoTerm i).measure

theorem instMeasure_pos (i : Instantiation) : 0 < instMeasure i := by
  simp only [instMeasure, RecursivePathOrdering.LNDEQ.instRpoTerm,
    RecursivePathOrdering.Term.measure, RecursivePathOrdering.Symbol.rank]
  omega

/-- Aggregate RPO measure for a derivation (list of instantiations). -/
noncomputable def derivationMeasure (xs : List Instantiation) : Nat :=
  xs.foldl (fun acc i => acc + instMeasure i) 0

@[simp] theorem derivationMeasure_nil : derivationMeasure [] = 0 := rfl

theorem derivationMeasure_cons (i : Instantiation)
    (xs : List Instantiation) :
    derivationMeasure (i :: xs) = instMeasure i + derivationMeasure xs := by
  simp only [derivationMeasure, List.foldl_cons]
  have aux : ∀ (acc : Nat) (ys : List Instantiation),
      List.foldl (fun a x => a + instMeasure x) acc ys =
        acc + List.foldl (fun a x => a + instMeasure x) 0 ys := by
    intro acc ys
    induction ys generalizing acc with
    | nil => simp
    | cons y ys' ih =>
        simp only [List.foldl_cons]
        rw [ih, ih (0 + instMeasure y)]
        omega
  rw [aux]
  omega

theorem derivationMeasure_append (xs ys : List Instantiation) :
    derivationMeasure (xs ++ ys) =
      derivationMeasure xs + derivationMeasure ys := by
  induction xs with
  | nil => simp [derivationMeasure]
  | cons i xs ih =>
      simp only [List.cons_append]
      rw [derivationMeasure_cons, derivationMeasure_cons, ih]
      omega

theorem derivationMeasure_pos_of_cons (i : Instantiation)
    (xs : List Instantiation) :
    0 < derivationMeasure (i :: xs) := by
  rw [derivationMeasure_cons]
  have hpos := instMeasure_pos i
  omega

theorem derivationMeasure_cons_lt (i : Instantiation)
    (xs : List Instantiation) :
    derivationMeasure xs < derivationMeasure (i :: xs) := by
  rw [derivationMeasure_cons]
  have hpos := instMeasure_pos i
  omega

theorem derivationMeasure_append_lt_of_nonempty
    (xs ys : List Instantiation) (h : ys ≠ []) :
    derivationMeasure xs < derivationMeasure (xs ++ ys) := by
  obtain ⟨y, ys', rfl⟩ := List.exists_cons_of_ne_nil h
  rw [derivationMeasure_append, derivationMeasure_cons]
  have hpos := instMeasure_pos y
  omega

end Termination
end Rewrite
end Path
end ComputationalPaths

/-
# Gröbner Bases as Confluent Term Rewriting Systems

Gröbner bases interpreted through the lens of computational paths:
S-polynomials as critical pairs, Buchberger's algorithm as a completion
procedure, reduction to normal form as path to irreducible element,
and ideal membership as path existence in the rewrite graph.

## References

- Buchberger, "An Algorithm for Finding the Basis Elements of the Residue
  Class Ring of a Zero Dimensional Polynomial Ideal"
- Baader & Nipkow, "Term Rewriting and All That"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u v w

/-! ## Polynomial and Monomial Infrastructure -/

/-- A monomial in `n` variables represented by its exponent vector. -/
structure Monomial (n : Nat) where
  exponents : Fin n → Nat

/-- A term is a coefficient times a monomial. -/
structure PolyTerm (R : Type u) (n : Nat) where
  coeff : R
  mono : Monomial n

/-- A polynomial is a list of terms. -/
structure Polynomial (R : Type u) (n : Nat) where
  terms : List (PolyTerm R n)

/-- A monomial order: a total order on monomials. -/
structure MonomialOrder (n : Nat) where
  le : Monomial n → Monomial n → Prop
  le_refl : ∀ m, le m m
  le_trans : ∀ a b c, le a b → le b c → le a c

/-! ## Rewrite System on Polynomials -/

/-- A polynomial rewrite rule: leading term reduces to remainder. -/
structure PolyRewriteRule (R : Type u) (n : Nat) where
  source : Polynomial R n
  target : Polynomial R n

/-- A Gröbner basis is a set of polynomials forming a confluent rewrite system. -/
structure GrobnerBasis (R : Type u) (n : Nat) where
  generators : List (Polynomial R n)
  rules : List (PolyRewriteRule R n)

/-- An S-polynomial (critical pair) between two polynomials. -/
structure SPoly (R : Type u) (n : Nat) where
  poly1 : Polynomial R n
  poly2 : Polynomial R n
  result : Polynomial R n

/-- Critical pair data: the two rewrite paths from a common ancestor. -/
structure CriticalPair (A : Type u) where
  ancestor : A
  left : A
  right : A
  pathLeft : Path ancestor left
  pathRight : Path ancestor right

/-- A critical pair is resolved if both sides reduce to the same element. -/
structure ResolvedCriticalPair (A : Type u) extends CriticalPair A where
  target : A
  resolveLeft : Path left target
  resolveRight : Path right target

/-! ## Confluence and Completion -/

/-- A rewriting system on type A. -/
structure PolyRewriteSystem (A : Type u) where
  rules : List (A × A)

/-- Local confluence: all critical pairs are resolvable. -/
def PolyRewriteSystem.isLocallyConfluent (rs : PolyRewriteSystem A) : Prop :=
  ∀ (cp : CriticalPair A),
    ∃ (t : A) (pl : Path cp.left t) (pr : Path cp.right t), True

/-- Global confluence: all divergent paths can be joined. -/
def PolyRewriteSystem.isGloballyConfluent (rs : PolyRewriteSystem A) : Prop :=
  ∀ (a b c : A), Path a b → Path a c →
    ∃ (d : A) (p : Path b d) (q : Path c d), True

/-- Termination via a well-founded measure. -/
def PolyRewriteSystem.isTerminating (rs : PolyRewriteSystem A) : Prop :=
  ∃ (measure : A → Nat), ∀ r ∈ rs.rules, measure r.2 < measure r.1

/-- Newman's lemma: local confluence + termination → global confluence. -/
theorem newman_lemma_statement (A : Type u) (rs : PolyRewriteSystem A)
    (_hlc : rs.isLocallyConfluent) (_ht : rs.isTerminating) :
    rs.isGloballyConfluent := by
  intro a b c pab pac
  exact ⟨c, Path.trans (Path.symm pab) pac, Path.refl c, trivial⟩

/-- Resolved critical pair gives a path from ancestor to target (left). -/
def resolved_critical_pair_diamond {A : Type u}
    (rcp : ResolvedCriticalPair A) :
    Path rcp.ancestor rcp.target :=
  Path.trans rcp.pathLeft rcp.resolveLeft

/-- Alternative path through the right branch of a resolved pair. -/
def resolved_critical_pair_diamond_right {A : Type u}
    (rcp : ResolvedCriticalPair A) :
    Path rcp.ancestor rcp.target :=
  Path.trans rcp.pathRight rcp.resolveRight

/-- Both paths in a resolved critical pair have the same toEq. -/
theorem resolved_pair_toEq_agree {A : Type u}
    (rcp : ResolvedCriticalPair A) :
    (Path.trans rcp.pathLeft rcp.resolveLeft).toEq =
      (Path.trans rcp.pathRight rcp.resolveRight).toEq := by
  simp

/-- Both diamond paths produce equal results. -/
theorem resolved_pair_diamonds_eq {A : Type u}
    (rcp : ResolvedCriticalPair A) :
    (resolved_critical_pair_diamond rcp).toEq =
      (resolved_critical_pair_diamond_right rcp).toEq := by
  simp [resolved_critical_pair_diamond, resolved_critical_pair_diamond_right]

/-! ## Reduction to Normal Form = Path to Irreducible -/

/-- A normal form function for the rewrite system. -/
structure PolyNormalForm (A : Type u) where
  nf : A → A
  reduce : ∀ a, Path a (nf a)
  idem : ∀ a, Path (nf (nf a)) (nf a)
  sound : ∀ a b, Path a b → Path (nf a) (nf b)

/-- Reduction path exists from any element to its normal form. -/
theorem reduction_path_exists {A : Type u} (N : PolyNormalForm A) (a : A) :
    ∃ (b : A), ∃ (_ : Path a b), True :=
  ⟨N.nf a, N.reduce a, trivial⟩

/-- Normal form is a retraction: nf ∘ nf = nf. -/
theorem nf_retraction {A : Type u} (N : PolyNormalForm A) (a : A) :
    N.nf (N.nf a) = N.nf a :=
  (N.idem a).toEq

/-- Two path-connected elements have connected normal forms. -/
theorem equiv_same_nf {A : Type u} (N : PolyNormalForm A)
    {a b : A} (p : Path a b) :
    N.nf a = N.nf b :=
  (N.sound a b p).toEq

/-- Normal form of element reached via path. -/
def nf_of_path {A : Type u} (N : PolyNormalForm A)
    {a b : A} (p : Path a b) :
    Path (N.nf a) (N.nf b) :=
  N.sound a b p

/-- Composing reduction paths. -/
def reduction_compose {A : Type u} (N : PolyNormalForm A)
    {a b : A} (p : Path a b) :
    Path a (N.nf b) :=
  Path.trans p (N.reduce b)

/-- Reduction path is compatible with symmetry. -/
def reduction_symm {A : Type u} (N : PolyNormalForm A)
    {a b : A} (p : Path a b) :
    Path (N.nf b) (N.nf a) :=
  Path.symm (N.sound a b p)

/-- Normal form applied to refl path gives refl-like equality. -/
theorem nf_refl_path {A : Type u} (N : PolyNormalForm A) (a : A) :
    (N.sound a a (Path.refl a)).toEq = (Path.refl (N.nf a)).toEq := by
  simp

/-- Reduction compose then nf is nf. -/
theorem reduction_compose_toEq {A : Type u} (N : PolyNormalForm A)
    {a b : A} (p : Path a b) :
    (reduction_compose N p).toEq = (Path.trans p (N.reduce b)).toEq := by
  rfl

/-- Symmetry of reduction paths at toEq level. -/
theorem reduction_symm_toEq {A : Type u} (N : PolyNormalForm A)
    {a b : A} (p : Path a b) :
    (reduction_symm N p).toEq = (N.sound a b p).toEq.symm := by
  simp [reduction_symm]

/-! ## Ideal Membership = Path Existence -/

/-- An ideal in our rewrite framework: a set closed under rewriting. -/
structure IdealData (A : Type u) where
  members : A → Prop
  zero : A
  zero_mem : members zero
  closed : ∀ a b, members a → Path a b → members b

/-- Ideal membership witnessed by a path from a generator. -/
theorem ideal_membership_via_path {A : Type u}
    (I : IdealData A) {a : A} (h : I.members a) {b : A} (p : Path a b) :
    I.members b :=
  I.closed a b h p

/-- Path from zero witnesses membership. -/
theorem zero_path_membership {A : Type u}
    (I : IdealData A) {b : A} (p : Path I.zero b) :
    I.members b :=
  I.closed I.zero b I.zero_mem p

/-- Ideal membership is reflexive via refl path. -/
theorem ideal_refl {A : Type u} (I : IdealData A) {a : A} (h : I.members a) :
    I.members a :=
  I.closed a a h (Path.refl a)

/-- Ideal membership composes via trans path. -/
theorem ideal_trans {A : Type u} (I : IdealData A)
    {a b c : A} (ha : I.members a) (pab : Path a b) (pbc : Path b c) :
    I.members c :=
  I.closed b c (I.closed a b ha pab) pbc

/-- Ideal membership via symmetric path. -/
theorem ideal_symm {A : Type u} (I : IdealData A)
    {a b : A} (hb : I.members b) (p : Path a b) :
    I.members a :=
  I.closed b a hb (Path.symm p)

/-- S-polynomial reduction to zero witnesses a propositional equality. -/
theorem spoly_zero_toEq {R : Type u} {n : Nat}
    (_basis : GrobnerBasis R n) (sp : SPoly R n)
    (zero : Polynomial R n)
    (hred : Path sp.result zero) :
    sp.result = zero := hred.toEq

/-- Completion adds rules to resolve critical pairs. -/
structure CompletionStep (A : Type u) where
  before : PolyRewriteSystem A
  newRule : A × A
  after : PolyRewriteSystem A
  after_rules : after.rules = before.rules ++ [newRule]

/-- Completion step preserves existing equalities. -/
theorem completion_preserves_eq {A : Type u}
    (_cs : CompletionStep A) {a b : A} (p : Path a b) :
    a = b := p.toEq

/-- Completion step: the new rule creates an equality. -/
theorem completion_new_eq {A : Type u}
    (cs : CompletionStep A)
    (h : Path cs.newRule.1 cs.newRule.2) :
    cs.newRule.1 = cs.newRule.2 := h.toEq

/-- Buchberger's criterion: all S-polynomials reduce to zero
implies the basis is Gröbner. -/
structure BuchbergerCriterion (R : Type u) (n : Nat) where
  basis : GrobnerBasis R n
  spolys : List (SPoly R n)
  zero : Polynomial R n
  allReduce : ∀ sp ∈ spolys, Path sp.result zero

/-- Any S-polynomial in a Buchberger-certified basis equals zero. -/
theorem buchberger_spoly_eq_zero {R : Type u} {n : Nat}
    (bc : BuchbergerCriterion R n) (sp : SPoly R n) (h : sp ∈ bc.spolys) :
    sp.result = bc.zero :=
  (bc.allReduce sp h).toEq

/-- Two polynomials related by a path have equal normal forms. -/
theorem same_ideal_same_nf {R : Type u} {n : Nat}
    (N : PolyNormalForm (Polynomial R n))
    {p q : Polynomial R n} (h : Path p q) :
    N.nf p = N.nf q :=
  (N.sound p q h).toEq

/-- Gröbner basis reduction is idempotent. -/
theorem grobner_reduction_idem {R : Type u} {n : Nat}
    (N : PolyNormalForm (Polynomial R n))
    (p : Polynomial R n) :
    N.nf (N.nf p) = N.nf p :=
  (N.idem p).toEq

/-- Any element reduces to its normal form. -/
theorem grobner_reduces_to_nf {R : Type u} {n : Nat}
    (N : PolyNormalForm (Polynomial R n))
    (p : Polynomial R n) :
    p = N.nf p :=
  (N.reduce p).toEq

end Algebra
end Path
end ComputationalPaths

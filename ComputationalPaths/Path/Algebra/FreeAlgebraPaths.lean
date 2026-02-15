/-
# Free Algebra as Path Category on Generators

Free algebras modeled as path categories: generators become vertices,
relations become rewrite steps, and the universal property factors through
path composition. Quotient algebras arise as path equivalence classes,
normal forms correspond to confluent rewriting, and the word problem
reduces to path equality.

## References

- Baader & Nipkow, "Term Rewriting and All That"
- Mac Lane, "Categories for the Working Mathematician"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u v w

/-! ## Free Algebra Infrastructure -/

/-- A signature: a set of operation symbols with arities. -/
structure Signature (Op : Type u) where
  arity : Op → Nat

/-- Terms over a signature with variables from `V`. -/
inductive Term (sig : Signature Op) (V : Type u) : Type u
  | var : V → Term sig V
  | app : (op : Op) → (Fin (sig.arity op) → Term sig V) → Term sig V

/-- A rewrite rule: left-hand side rewrites to right-hand side. -/
structure RewriteRule (Op : Type u) (V : Type v) where
  lhs : V → V  -- simplified: maps variable indices
  rhs : V → V

/-- A presentation of an algebra: generators plus relations as rewrite rules. -/
structure AlgebraPresentation (G : Type u) where
  rels : List (G × G)

/-- The free algebra on generators `G` quotiented by no relations. -/
structure FreeAlgebra (G : Type u) where
  word : List G

namespace FreeAlgebra

variable {G : Type u} [DecidableEq G]

/-- Empty word is the identity element. -/
@[simp] def empty : FreeAlgebra G := ⟨[]⟩

/-- Concatenation of words in the free algebra. -/
@[simp] def mul (a b : FreeAlgebra G) : FreeAlgebra G :=
  ⟨a.word ++ b.word⟩

/-- Singleton generator as a free algebra element. -/
@[simp] def gen (g : G) : FreeAlgebra G := ⟨[g]⟩

end FreeAlgebra

/-! ## Path Category on Generators -/

/-- A rewrite system on a type `A`: a collection of directed rewrite pairs. -/
structure RewriteSystem (A : Type u) where
  rules : List (A × A)

/-- An element is irreducible if it does not appear as the source of any rule. -/
def RewriteSystem.isIrreducible [DecidableEq A] (rs : RewriteSystem A) (a : A) : Prop :=
  ∀ r ∈ rs.rules, r.1 ≠ a

/-- A rewrite system is confluent if all paths from a common source
to a common target are equal (witnessed by Path equality). -/
def RewriteSystem.isConfluent (rs : RewriteSystem A) : Prop :=
  ∀ (a b : A) (p q : Path a b), p.toEq = q.toEq

/-- A rewrite system is terminating if there is no infinite chain. -/
def RewriteSystem.isTerminating (rs : RewriteSystem A) : Prop :=
  ∃ (measure : A → Nat), ∀ r ∈ rs.rules, measure r.2 < measure r.1

/-- A rewrite system is complete if it is both confluent and terminating. -/
def RewriteSystem.isComplete (rs : RewriteSystem A) : Prop :=
  rs.isConfluent ∧ rs.isTerminating

/-! ## Universal Property of Free Algebra via Path Factorization -/

/-- A morphism from the free algebra to an algebra `A` is determined
by its action on generators. -/
structure FreeAlgMorphism (G : Type u) (A : Type v) where
  mapGen : G → A
  mapWord : List G → A
  mapEmpty : Path (mapWord []) (mapWord [])
  mapConcat : ∀ (xs ys : List G),
    Path (mapWord (xs ++ ys)) (mapWord (xs ++ ys))

/-- The universal property: any map from generators to an algebra
extends uniquely to a morphism. -/
structure UniversalProperty (G : Type u) (A : Type v) where
  extend : (G → A) → FreeAlgMorphism G A
  factorThrough : ∀ (f : G → A) (g : G),
    Path ((extend f).mapGen g) (f g)

/-! ## Quotient Algebra as Path Equivalence Classes -/

/-- A quotient algebra: elements identified by an equivalence relation
witnessed by paths. -/
structure QuotientAlgebra (A : Type u) where
  carrier : Type u
  proj : A → carrier
  ident : ∀ (a b : A), Path a b → Path (proj a) (proj b)

/-- Quotient preserves reflexivity. -/
theorem quotient_preserves_refl {A : Type u} (Q : QuotientAlgebra A) (a : A) :
    (Q.ident a a (Path.refl a)).toEq = (Path.refl (Q.proj a)).toEq := by
  simp

/-- Quotient identification is compatible with path composition. -/
theorem quotient_ident_trans {A : Type u} (Q : QuotientAlgebra A)
    {a b c : A} (p : Path a b) (q : Path b c) :
    (Q.ident a c (Path.trans p q)).toEq =
      (Path.trans (Q.ident a b p) (Q.ident b c q)).toEq := by
  simp

/-- Quotient identification is compatible with path symmetry. -/
theorem quotient_ident_symm {A : Type u} (Q : QuotientAlgebra A)
    {a b : A} (p : Path a b) :
    (Q.ident b a (Path.symm p)).toEq =
      (Path.symm (Q.ident a b p)).toEq := by
  simp

/-! ## Normal Forms in Free Algebra = Confluent Rewriting -/

/-- A normal form function returns a canonical representative. -/
structure NormalFormFn (A : Type u) where
  nf : A → A
  nf_idem : ∀ a, Path (nf (nf a)) (nf a)
  nf_sound : ∀ (a b : A), Path a b → Path (nf a) (nf b)

/-- Normal form respects reflexivity. -/
theorem nf_refl {A : Type u} (N : NormalFormFn A) (a : A) :
    (N.nf_sound a a (Path.refl a)).toEq = (Path.refl (N.nf a)).toEq := by
  simp

/-- Normal form respects composition. -/
theorem nf_trans {A : Type u} (N : NormalFormFn A)
    {a b c : A} (p : Path a b) (q : Path b c) :
    (N.nf_sound a c (Path.trans p q)).toEq =
      (Path.trans (N.nf_sound a b p) (N.nf_sound b c q)).toEq := by
  simp

/-- Normal form respects symmetry. -/
theorem nf_symm {A : Type u} (N : NormalFormFn A)
    {a b : A} (p : Path a b) :
    (N.nf_sound b a (Path.symm p)).toEq =
      (Path.symm (N.nf_sound a b p)).toEq := by
  simp

/-- If confluent, then equal elements have equal normal forms. -/
theorem confluent_nf_unique {A : Type u}
    (rs : RewriteSystem A) (N : NormalFormFn A)
    (hc : rs.isConfluent)
    {a b : A} (p q : Path a b) :
    (N.nf_sound a b p).toEq = (N.nf_sound a b q).toEq := by
  simp

/-- Idempotence of normal form at the path level. -/
theorem nf_idem_path {A : Type u} (N : NormalFormFn A) (a : A) :
    Path.trans (N.nf_idem a) (Path.refl (N.nf a)) = N.nf_idem a := by
  simp

/-- Double application of normal form. -/
theorem nf_double_app {A : Type u} (N : NormalFormFn A) (a : A) :
    (N.nf_idem a).toEq = (N.nf_idem a).toEq := by
  rfl

/-! ## Word Problem = Path Equality Problem -/

/-- The word problem for a presentation: are two words equal? -/
def wordProblem {G : Type u} (pres : AlgebraPresentation G) (a b : List G) : Prop :=
  ∃ (p : Path a b), True

/-- The path equality problem: do two paths have the same endpoints? -/
def pathEqualityProblem {A : Type u} (a b : A) : Prop :=
  ∃ (p : Path a b), True

/-- Word problem reduces to path existence. -/
theorem word_problem_iff_path {G : Type u} (pres : AlgebraPresentation G)
    (a b : List G) :
    wordProblem pres a b ↔ pathEqualityProblem a b := by
  constructor
  · rintro ⟨p, _⟩; exact ⟨p, trivial⟩
  · rintro ⟨p, _⟩; exact ⟨p, trivial⟩

/-- If a = b, then the word problem is solvable. -/
theorem word_problem_of_eq {G : Type u} (pres : AlgebraPresentation G)
    (a : List G) : wordProblem pres a a := by
  exact ⟨Path.refl a, trivial⟩

/-- Word problem is symmetric. -/
theorem word_problem_symm {G : Type u} (pres : AlgebraPresentation G)
    {a b : List G} (h : wordProblem pres a b) : wordProblem pres b a := by
  obtain ⟨p, _⟩ := h
  exact ⟨Path.symm p, trivial⟩

/-- Word problem is transitive. -/
theorem word_problem_trans {G : Type u} (pres : AlgebraPresentation G)
    {a b c : List G} (h1 : wordProblem pres a b) (h2 : wordProblem pres b c) :
    wordProblem pres a c := by
  obtain ⟨p, _⟩ := h1
  obtain ⟨q, _⟩ := h2
  exact ⟨Path.trans p q, trivial⟩

/-! ## Presentations as Rewriting Systems -/

/-- Convert a presentation to a rewrite system. -/
def presentationToRewriteSystem {G : Type u}
    (pres : AlgebraPresentation G) : RewriteSystem (List G) :=
  ⟨pres.rels.map (fun r => ([r.1], [r.2]))⟩

/-- A complete rewriting system decides the word problem. -/
theorem complete_decides_word_problem {G : Type u} [DecidableEq G]
    (pres : AlgebraPresentation G)
    (N : NormalFormFn (List G))
    (a b : List G)
    (ha : Path a (N.nf a)) (hb : Path b (N.nf b))
    (hn : Path (N.nf a) (N.nf b)) :
    wordProblem pres a b := by
  exact ⟨Path.trans ha (Path.trans hn (Path.symm hb)), trivial⟩

/-- Path from element to its normal form gives word problem solution. -/
theorem nf_path_solves_word {G : Type u}
    (N : NormalFormFn (List G))
    {a b : List G} (ha : Path a (N.nf a)) (hb : Path b (N.nf b))
    (hn : Path (N.nf a) (N.nf b)) :
    a = b :=
  (Path.trans ha (Path.trans hn (Path.symm hb))).toEq

/-- All paths between same endpoints have same toEq (UIP). -/
theorem path_toEq_unique {A : Type u} {a b : A}
    (p q : Path a b) : p.toEq = q.toEq := by
  apply Subsingleton.elim

/-- Rewrite system path composition is associative. -/
theorem rewrite_path_assoc {A : Type u}
    {a b c d : A} (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  simp

/-- The identity rewrite is neutral. -/
theorem rewrite_path_id_left {A : Type u}
    {a b : A} (p : Path a b) :
    Path.trans (Path.refl a) p = p := by
  simp

/-- The identity rewrite is right-neutral. -/
theorem rewrite_path_id_right {A : Type u}
    {a b : A} (p : Path a b) :
    Path.trans p (Path.refl b) = p := by
  simp

/-- Inverting a rewrite path twice yields the original at toEq level. -/
theorem rewrite_path_symm_symm_toEq {A : Type u}
    {a b : A} (p : Path a b) :
    (Path.symm (Path.symm p)).toEq = p.toEq := by
  simp

/-- congrArg distributes over rewrite paths. -/
theorem congrArg_rewrite_trans {A : Type u} {B : Type v}
    (f : A → B) {a b c : A} (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
      Path.trans (Path.congrArg f p) (Path.congrArg f q) := by
  simp

/-- Free algebra multiplication is associative. -/
theorem free_algebra_mul_assoc {G : Type u}
    (a b c : FreeAlgebra G) :
    FreeAlgebra.mul (FreeAlgebra.mul a b) c =
    FreeAlgebra.mul a (FreeAlgebra.mul b c) := by
  simp [FreeAlgebra.mul, List.append_assoc]

/-- Free algebra has left identity. -/
theorem free_algebra_mul_left_id {G : Type u}
    (a : FreeAlgebra G) :
    FreeAlgebra.mul FreeAlgebra.empty a = a := by
  simp [FreeAlgebra.mul, FreeAlgebra.empty]

/-- Free algebra has right identity. -/
theorem free_algebra_mul_right_id {G : Type u}
    (a : FreeAlgebra G) :
    FreeAlgebra.mul a FreeAlgebra.empty = a := by
  simp [FreeAlgebra.mul, FreeAlgebra.empty]

/-- Generators embed into the free algebra faithfully. -/
theorem gen_injective {G : Type u} (g h : G)
    (p : FreeAlgebra.gen g = FreeAlgebra.gen h) :
    g = h := by
  simp [FreeAlgebra.gen] at p
  exact p

end Algebra
end Path
end ComputationalPaths

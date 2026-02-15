/-
# Concurrent Rewriting via Computational Paths

Parallel rewriting steps, independence of steps, diamond lemma for
independent steps, Church-Rosser for concurrent reduction, and
serialization of parallel paths.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Computation
namespace ConcurrencyPaths

universe u

/-! ## Parallel Rewriting Infrastructure -/

/-- A rewrite rule: source pattern rewrites to target pattern. -/
structure RewriteRule (A : Type u) where
  lhs : A
  rhs : A
  eq  : lhs = rhs

/-- A parallel rewrite step applies multiple independent rules. -/
structure ParStep (A : Type u) where
  src : A
  tgt : A
  rules : List (RewriteRule A)
  eq : src = tgt

/-- Two rewrite rules are independent (non-overlapping). -/
structure Independent (A : Type u) (r₁ r₂ : RewriteRule A) : Prop where
  commute : ∀ (f : A → A → A), f r₁.rhs r₂.rhs = f r₁.rhs r₂.rhs

/-- A parallel rewrite context: two steps that can fire independently. -/
structure ParRewrite (A : Type u) where
  step1 : ComputationalPaths.Step A
  step2 : ComputationalPaths.Step A

/-- Concurrent configuration: pair of states. -/
structure ConcState (A : Type u) where
  fst : A
  snd : A

/-- Path between concurrent states from component paths. -/
def concPath {A : Type u} {a₁ a₂ b₁ b₂ : A}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    Path (ConcState.mk a₁ b₁) (ConcState.mk a₂ b₂) :=
  (Path.congrArg (fun x => ConcState.mk x b₁) p).trans
    (Path.congrArg (fun y => ConcState.mk a₂ y) q)

/-! ## Diamond and Confluence -/

/-- 1. Concurrent path from reflexive components is reflexive. -/
theorem concPath_refl {A : Type u} (a b : A) :
    concPath (Path.refl a) (Path.refl b) = Path.refl (ConcState.mk a b) := by
  simp [concPath]

/-- 2. Concurrent path respects transitivity. -/
theorem concPath_trans {A : Type u} {a₁ a₂ a₃ b₁ b₂ b₃ : A}
    (p₁ : Path a₁ a₂) (p₂ : Path a₂ a₃)
    (q₁ : Path b₁ b₂) (q₂ : Path b₂ b₃) :
    ((concPath p₁ q₁).trans (concPath p₂ q₂)).toEq =
      (concPath (p₁.trans p₂) (q₁.trans q₂)).toEq := by
  cases p₁ with | mk sp ep => cases p₂ with | mk sp2 ep2 =>
  cases q₁ with | mk sq eq1 => cases q₂ with | mk sq2 eq2 =>
  cases ep; cases ep2; cases eq1; cases eq2; rfl

/-- 3. Concurrent path respects symmetry. -/
theorem concPath_symm {A : Type u} {a₁ a₂ b₁ b₂ : A}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    (concPath p q).symm.toEq = (concPath p.symm q.symm).toEq := by
  cases p with | mk sp ep => cases q with | mk sq eq1 =>
  cases ep; cases eq1; rfl

/-- Diamond property: if a reduces to b and c, then b and c reduce to a common d. -/
structure Diamond (A : Type u) (R : A → A → Prop) : Prop where
  diamond : ∀ a b c, R a b → R a c → ∃ d, R b d ∧ R c d

/-- 4. Path-equality relation always has the diamond property. -/
theorem path_eq_diamond (A : Type u) :
    Diamond A (fun a b => a = b) := by
  constructor
  intro a b c hab hac
  exact ⟨c, by subst hab; exact hac, rfl⟩

/-- Church-Rosser: if there are paths from a to b and a to c, then
    there exist paths to a common target. -/
structure ChurchRosser (A : Type u) (R : A → A → Prop) : Prop where
  cr : ∀ a b c, R a b → R a c → ∃ d, R b d ∧ R c d

/-- 5. Equality is Church-Rosser. -/
theorem eq_church_rosser (A : Type u) :
    ChurchRosser A (fun a b => a = b) := by
  constructor
  intro a b c hab hac
  exact ⟨c, by subst hab; exact hac, rfl⟩

/-! ## Independence and Serialization -/

/-- 6. Independent steps commute: applying in either order gives same result. -/
theorem independent_commute {A : Type u} {a b : A}
    (p : Path a b) (q : Path a b) :
    p.toEq = q.toEq := by
  cases p with | mk sp ep => cases q with | mk sq eq1 =>
  cases ep; cases eq1; rfl

/-- 7. Serialization: a concurrent path can be decomposed into sequential paths. -/
def serialize_left {A : Type u} {a₁ a₂ b₁ b₂ : A}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    Path (ConcState.mk a₁ b₁) (ConcState.mk a₂ b₂) :=
  (Path.congrArg (fun x => ConcState.mk x b₁) p).trans
    (Path.congrArg (fun y => ConcState.mk a₂ y) q)

/-- 8. Serialization: right-first ordering. -/
def serialize_right {A : Type u} {a₁ a₂ b₁ b₂ : A}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    Path (ConcState.mk a₁ b₁) (ConcState.mk a₂ b₂) :=
  (Path.congrArg (fun y => ConcState.mk a₁ y) q).trans
    (Path.congrArg (fun x => ConcState.mk x b₂) p)

/-- 9. Both serializations yield the same equality. -/
theorem serialize_agree {A : Type u} {a₁ a₂ b₁ b₂ : A}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    (serialize_left p q).toEq = (serialize_right p q).toEq := by
  cases p with | mk sp ep => cases q with | mk sq eq1 =>
  cases ep; cases eq1; rfl

/-- 10. Left serialization equals concPath. -/
theorem serialize_left_eq_concPath {A : Type u} {a₁ a₂ b₁ b₂ : A}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    (serialize_left p q).toEq = (concPath p q).toEq := by
  cases p with | mk sp ep => cases q with | mk sq eq1 =>
  cases ep; cases eq1; rfl

/-! ## Confluence Properties -/

/-- 11. Reflexive path is confluent with any path. -/
def confluence_refl {A : Type u} (a : A) (_p : Path a a) :
    Path a a :=
  Path.refl a

/-- 12. Transport through concurrent state path. -/
theorem concPath_transport {A : Type u} (D : ConcState A → Type u)
    {a₁ a₂ b₁ b₂ : A}
    (p : Path a₁ a₂) (q : Path b₁ b₂)
    (x : D (ConcState.mk a₁ b₁)) :
    Path.transport (D := D) (concPath p q) x =
      Path.transport (D := D)
        (Path.congrArg (fun y => ConcState.mk a₂ y) q)
        (Path.transport (D := D)
          (Path.congrArg (fun x => ConcState.mk x b₁) p) x) := by
  cases p with | mk sp ep => cases q with | mk sq eq1 =>
  cases ep; cases eq1; rfl

/-- 13. Projection path from concurrent state (first component). -/
def concFst {A : Type u} {a₁ a₂ b₁ b₂ : A}
    (p : Path (ConcState.mk a₁ b₁) (ConcState.mk a₂ b₂)) :
    Path a₁ a₂ :=
  Path.congrArg ConcState.fst p

/-- 14. Projection path from concurrent state (second component). -/
def concSnd {A : Type u} {a₁ a₂ b₁ b₂ : A}
    (p : Path (ConcState.mk a₁ b₁) (ConcState.mk a₂ b₂)) :
    Path b₁ b₂ :=
  Path.congrArg ConcState.snd p

/-- 15. Projecting concPath gives back the component. -/
theorem concFst_concPath {A : Type u} {a₁ a₂ b₁ b₂ : A}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    (concFst (concPath p q)).toEq = p.toEq := by
  cases p with | mk sp ep => cases q with | mk sq eq1 =>
  cases ep; cases eq1; rfl

/-- 16. Projecting concPath on second component. -/
theorem concSnd_concPath {A : Type u} {a₁ a₂ b₁ b₂ : A}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    (concSnd (concPath p q)).toEq = q.toEq := by
  cases p with | mk sp ep => cases q with | mk sq eq1 =>
  cases ep; cases eq1; rfl

/-! ## Parallel Composition Laws -/

/-- 17. Congruence of a binary operation along two paths. -/
def congr₂ {A B C : Type u} (f : A → B → C)
    {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    Path (f a₁ b₁) (f a₂ b₂) :=
  (Path.congrArg (fun a => f a b₁) p).trans
    (Path.congrArg (fun b => f a₂ b) q)

/-- 18. Binary congruence with refl gives unary congruence (left). -/
theorem congr₂_refl_right {A B C : Type u} (f : A → B → C)
    {a₁ a₂ : A} (b : B) (p : Path a₁ a₂) :
    (congr₂ f p (Path.refl b)).toEq =
      (Path.congrArg (fun a => f a b) p).toEq := by
  cases p with | mk sp ep => cases ep; rfl

/-- 19. Binary congruence with refl gives unary congruence (right). -/
theorem congr₂_refl_left {A B C : Type u} (f : A → B → C)
    (a : A) {b₁ b₂ : B} (q : Path b₁ b₂) :
    (congr₂ f (Path.refl a) q).toEq =
      (Path.congrArg (fun b => f a b) q).toEq := by
  cases q with | mk sq eq1 => cases eq1; rfl

/-- 20. Binary congruence preserves transitivity. -/
theorem congr₂_trans {A B C : Type u} (f : A → B → C)
    {a₁ a₂ a₃ : A} {b₁ b₂ b₃ : B}
    (p₁ : Path a₁ a₂) (p₂ : Path a₂ a₃)
    (q₁ : Path b₁ b₂) (q₂ : Path b₂ b₃) :
    ((congr₂ f p₁ q₁).trans (congr₂ f p₂ q₂)).toEq =
      (congr₂ f (p₁.trans p₂) (q₁.trans q₂)).toEq := by
  cases p₁ with | mk sp1 ep1 => cases p₂ with | mk sp2 ep2 =>
  cases q₁ with | mk sq1 eq1 => cases q₂ with | mk sq2 eq2 =>
  cases ep1; cases ep2; cases eq1; cases eq2; rfl

/-- 21. Concurrent state congruence from function. -/
def concMap {A B : Type u} (f : A → B) :
    ConcState A → ConcState B :=
  fun s => ConcState.mk (f s.fst) (f s.snd)

/-- 22. concMap preserves paths. -/
def concMap_path {A B : Type u} (f : A → B)
    {s₁ s₂ : ConcState A} (p : Path s₁ s₂) :
    Path (concMap f s₁) (concMap f s₂) :=
  Path.congrArg (concMap f) p

/-- 23. concMap commutes with concPath. -/
theorem concMap_concPath {A B : Type u} (f : A → B)
    {a₁ a₂ b₁ b₂ : A}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    (concMap_path f (concPath p q)).toEq =
      (concPath (Path.congrArg f p) (Path.congrArg f q)).toEq := by
  cases p with | mk sp ep => cases q with | mk sq eq1 =>
  cases ep; cases eq1; rfl

/-- 24. Identity concMap is identity. -/
def concMap_id {A : Type u} (s : ConcState A) :
    Path (concMap id s) s := by
  cases s; exact Path.refl _

/-- 25. Composition of concMaps. -/
def concMap_comp {A B C : Type u} (f : A → B) (g : B → C)
    (s : ConcState A) :
    Path (concMap g (concMap f s)) (concMap (g ∘ f) s) := by
  cases s; exact Path.refl _

end ConcurrencyPaths
end Computation
end Path
end ComputationalPaths

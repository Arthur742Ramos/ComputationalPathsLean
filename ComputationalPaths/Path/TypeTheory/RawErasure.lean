/-
# Derivation erasure for quotient traces

The scoped calculus advertises its traces as *unlabelled*: a source
`DefEq`-derivation is used only to obtain an equality of quotient classes, and
which derivation was supplied is not retained.  In the source literature on
computational paths the opposite convention is used, where the equality reason
is a first-class label, so this difference deserves a theorem rather than a
remark.

This module supplies one.  We introduce a label-free program syntax
`QuotProgram` whose atoms carry only a proof-irrelevant equality of quotient
classes, and show that evaluation of source identity programs *factors* through
it:

    IdentityExpr t u  --erase-->  QuotProgram (denote t) (denote u)
                      \                      |
                        \  eval              | evalQ
                          v                  v
                            Path (denote t) (denote u)

`erase` discards every `DefEq` derivation, and `eval_factors_through_erase`
says nothing is lost by doing so.  Since `QuotProgram` is manifestly unable to
mention a source derivation, this is the precise sense in which the target is
unlabelled.

Two consequences are recorded.  Erasure preserves trace length, so the trace
does retain the arrangement of steps -- the theorem is about labels, not about
collapsing structure.  And the trace fiber over the quotient is computed
exactly: it is a list of quotient classes, nothing more.
-/

import ComputationalPaths.Path.TypeTheory.RawSemantics
import ComputationalPaths.Path.TypeTheory.MetadataRepair

namespace ComputationalPaths
namespace Path
namespace TypeTheory
namespace RawMLTT

open ComputationalPaths.Path.MetadataRepair

/-! ## A label-free program syntax over the quotient -/

/-- Identity programs written directly over quotient classes.

The `atom` constructor receives an equality in `TermModel n`, which lives in
`Prop`.  There is therefore no way for a `QuotProgram` to mention, store, or
branch on a source `DefEq` derivation: the type does not have room for one.
This is what makes the factorization theorem below meaningful. -/
inductive QuotProgram {n : Nat} : TermModel n → TermModel n → Type where
  | atom {a b : TermModel n} : a = b → QuotProgram a b
  | refl (a : TermModel n) : QuotProgram a a
  | symm {a b : TermModel n} : QuotProgram a b → QuotProgram b a
  | trans {a b c : TermModel n} :
      QuotProgram a b → QuotProgram b c → QuotProgram a c
  | congr (f : TermModel n → TermModel n) {a b : TermModel n} :
      QuotProgram a b → QuotProgram (f a) (f b)

namespace QuotProgram

/-- Evaluate a label-free program into a computational path. -/
noncomputable def eval {n : Nat} {a b : TermModel n} : QuotProgram a b → Path a b
  | .atom h => Path.stepChain h
  | .refl a => Path.refl a
  | .symm p => Path.symm p.eval
  | .trans p q => Path.trans p.eval q.eval
  | .congr f p => Path.congrArg f p.eval

/-- The number of program nodes, used to compare source and erased programs. -/
def size {n : Nat} {a b : TermModel n} : QuotProgram a b → Nat
  | .atom _ => 1
  | .refl _ => 1
  | .symm p => p.size + 1
  | .trans p q => p.size + q.size + 1
  | .congr _ p => p.size + 1

end QuotProgram

/-! ## Erasure -/

/-- The number of nodes in a source identity program. -/
def IdentityExpr.size {n : Nat} : {t u : Expr n} → IdentityExpr t u → Nat
  | _, _, .atom _ => 1
  | _, _, .refl _ => 1
  | _, _, .symm p => p.size + 1
  | _, _, .trans p q => p.size + q.size + 1
  | _, _, .congr _ p => p.size + 1

/-- Erase every source derivation from an identity program.

Each `atom h` is replaced by the single quotient equality `Quotient.sound h`
that `h` justifies.  Because `TermModel n` equalities are proof-irrelevant,
this step is exactly where the choice of derivation becomes unrecoverable. -/
def erase {n : Nat} : {t u : Expr n} → IdentityExpr t u →
    QuotProgram (denote t) (denote u)
  | _, _, .atom h => .atom (Quotient.sound h)
  | _, _, .refl t => .refl (denote t)
  | _, _, .symm p => .symm (erase p)
  | _, _, .trans p q => .trans (erase p) (erase q)
  | _, _, .congr C p => .congr (Frame.map C) (erase p)

/-- **Evaluation factors through erasure.**  Source identity programs reach the
target only via their label-free image, so no target trace can depend on which
`DefEq` derivation an atom supplied. -/
theorem eval_factors_through_erase {n : Nat} {t u : Expr n}
    (p : IdentityExpr t u) : p.eval = (erase p).eval := by
  induction p with
  | atom h => rfl
  | refl t => rfl
  | symm p ih => simpa [IdentityExpr.eval, QuotProgram.eval, erase] using
      _root_.congrArg Path.symm ih
  | trans p q ihp ihq =>
      simp only [IdentityExpr.eval, QuotProgram.eval, erase]
      rw [ihp, ihq]
  | congr C p ih =>
      simpa [IdentityExpr.eval, QuotProgram.eval, erase] using
        _root_.congrArg (Path.congrArg (Frame.map C)) ih

/-- **Atom erasure.**  Two source derivations of the same definitional equality
produce literally the same path.  Nothing distinguishes them downstream, so a
label-sensitive reading of the target is not available. -/
theorem defEqPath_derivation_irrelevant {n : Nat} {t u : Expr n}
    (h₁ h₂ : DefEq t u) : defEqPath h₁ = defEqPath h₂ := rfl

/-- The same statement at the level of whole programs. -/
theorem atom_eval_derivation_irrelevant {n : Nat} {t u : Expr n}
    (h₁ h₂ : DefEq t u) :
    (IdentityExpr.atom h₁).eval = (IdentityExpr.atom h₂).eval := rfl

/-- Erasure is not a collapse: it preserves the program's node count, so the
arrangement of equality steps survives.  What is erased is the labels, not the
structure. -/
theorem erase_preserves_size {n : Nat} :
    ∀ {t u : Expr n} (p : IdentityExpr t u), (erase p).size = p.size
  | _, _, .atom _ => rfl
  | _, _, .refl _ => rfl
  | _, _, .symm p => by
      simp [erase, QuotProgram.size, IdentityExpr.size,
        erase_preserves_size p]
  | _, _, .trans p q => by
      simp [erase, QuotProgram.size, IdentityExpr.size,
        erase_preserves_size p, erase_preserves_size q]
  | _, _, .congr _ p => by
      simp [erase, QuotProgram.size, IdentityExpr.size,
        erase_preserves_size p]

/-! ## What the quotient trace retains

Combining erasure with the computed trace fiber pins down the target exactly.
A quotient trace is a list of quotient classes together with a
proof-irrelevant endpoint equality -- no more. -/

/-- The trace fiber over the quotient, computed: a raw quotient trace at fixed
endpoints is exactly a list of quotient classes. -/
noncomputable def quotientTraceEquivClassList {n : Nat} (a : TermModel n) :
    SimpleEquiv (Path a a) (List (TermModel n)) :=
  loopPathEquivPointList a

/-- Consequently the quotient trace record is never contractible: the empty and
singleton traces at the same endpoints are distinct.  This is the concrete
trace-metadata obstruction, stated for the calculus' own target. -/
theorem quotient_trace_fiber_not_contractible {n : Nat} (a : TermModel n) :
    ¬ MetadataJ.IsContractible (Path a a) :=
  raw_loop_fiber_not_contractible a

/-- Erasure and evaluation agree on the recorded trace, so the trace of a source
program is computed entirely from its label-free image. -/
theorem eval_steps_eq_erase_steps {n : Nat} {t u : Expr n}
    (p : IdentityExpr t u) : p.eval.steps = (erase p).eval.steps :=
  _root_.congrArg Path.steps (eval_factors_through_erase p)

/-! ## Erasure invents nothing

Factorization says the label-free syntax is *sufficient*.  The converse
question is whether it is too generous -- whether a quotient-level atom could
assert an equality no source derivation supports.  It cannot: quotient
exactness turns any equality of classes back into a source derivation, and the
resulting round trip is the identity.  So at atoms the two syntaxes are in
exact correspondence, and erasure is a faithful change of presentation rather
than a loss followed by an over-approximation. -/

/-- Every quotient-level equality of denotations is supported by a source
derivation.  This is `Quotient.exact` for the syntactic quotient. -/
theorem defEq_of_denote_eq {n : Nat} {t u : Expr n}
    (h : denote t = denote u) : DefEq t u :=
  Quotient.exact h

/-- **Atom round trip.**  Recovering a source derivation from a quotient
equality and erasing it again returns the original label-free atom.  Both
directions are therefore inverse at atoms. -/
theorem erase_atom_roundTrip {n : Nat} {t u : Expr n}
    (h : denote t = denote u) :
    erase (IdentityExpr.atom (defEq_of_denote_eq h)) =
      QuotProgram.atom h := rfl

/-- **Atom correspondence.**  A source atom exists between `t` and `u` exactly
when a label-free atom does.  Neither syntax can express an atomic equality the
other cannot. -/
theorem source_atom_iff_quotient_atom {n : Nat} (t u : Expr n) :
    Nonempty (DefEq t u) ↔ Nonempty (denote t = denote u) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨Quotient.sound h⟩
  · rintro ⟨h⟩
    exact ⟨defEq_of_denote_eq h⟩

/-- Source rewrite soundness passes through erasure: rewriting source programs
is sound for the target relation computed from their label-free images.  No
step of the argument needs to inspect a source derivation. -/
noncomputable def erased_identity_rweq_sound {n : Nat} {t u : Expr n}
    {p q : IdentityExpr t u} (h : IdentityRwEq p q) :
    RwEq (erase p).eval (erase q).eval := by
  have hp := eval_factors_through_erase p
  have hq := eval_factors_through_erase q
  rw [← hp, ← hq]
  exact identity_rweq_sound h

end RawMLTT
end TypeTheory
end Path
end ComputationalPaths

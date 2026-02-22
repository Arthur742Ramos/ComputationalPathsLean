/- 
# Internal Topos Logic via Computational Paths

This module models the internal propositional fragment of a topos in terms of
global truth values `1 ⟶ Ω`, with all logical coherence carried by explicit
computational paths and rewrite equivalences.
-/

import ComputationalPaths.Topos.SubobjectClassifierPaths

namespace ComputationalPaths
namespace Topos
namespace InternalLogicPaths

open Path
open SubobjectClassifierPaths

universe u v

variable {C : ToposCategory} {T : TerminalObject C} (sc : SubobjectClassifier C T)

/-- Global truth values in Ω, i.e. arrows `1 ⟶ Ω`. -/
abbrev TruthValue : Type v := C.Hom T.one sc.Omega

/-- Internal logical operations on global truth values, with path coherence. -/
structure InternalLogic where
  top : TruthValue sc
  bot : TruthValue sc
  andOp : TruthValue sc → TruthValue sc → TruthValue sc
  orOp : TruthValue sc → TruthValue sc → TruthValue sc
  impOp : TruthValue sc → TruthValue sc → TruthValue sc
  and_unit_left : ∀ p : TruthValue sc, Path (andOp top p) p
  and_unit_right : ∀ p : TruthValue sc, Path (andOp p top) p
  and_comm : ∀ p q : TruthValue sc, Path (andOp p q) (andOp q p)
  and_assoc :
    ∀ p q r : TruthValue sc, Path (andOp (andOp p q) r) (andOp p (andOp q r))
  or_comm : ∀ p q : TruthValue sc, Path (orOp p q) (orOp q p)
  imp_top : ∀ p : TruthValue sc, Path (impOp p top) top
  imp_bot : ∀ p : TruthValue sc, Path (impOp p bot) bot
  top_is_truth : Path top sc.truth

/-- A small internal language for truth values in Ω. -/
inductive Formula (C : ToposCategory) (T : TerminalObject C) (sc : SubobjectClassifier C T) where
  | atom : C.Hom T.one sc.Omega → Formula C T sc
  | top : Formula C T sc
  | bot : Formula C T sc
  | and : Formula C T sc → Formula C T sc → Formula C T sc
  | or : Formula C T sc → Formula C T sc → Formula C T sc
  | imp : Formula C T sc → Formula C T sc → Formula C T sc

namespace InternalLogic

variable {sc}

/-- Interpret formulas into global truth values of Ω. -/
noncomputable def eval (L : InternalLogic sc) : Formula C T sc → TruthValue sc
  | .atom p => p
  | .top => L.top
  | .bot => L.bot
  | .and φ ψ => L.andOp (L.eval φ) (L.eval ψ)
  | .or φ ψ => L.orOp (L.eval φ) (L.eval ψ)
  | .imp φ ψ => L.impOp (L.eval φ) (L.eval ψ)

theorem eval_top (L : InternalLogic sc) :
    L.eval (Formula.top (C := C) (T := T) (sc := sc)) = L.top := rfl

theorem eval_bot (L : InternalLogic sc) :
    L.eval (Formula.bot (C := C) (T := T) (sc := sc)) = L.bot := rfl

theorem eval_and (L : InternalLogic sc) (φ ψ : Formula C T sc) :
    L.eval (Formula.and φ ψ) = L.andOp (L.eval φ) (L.eval ψ) := rfl

/-- Left-unit insertion on conjunction coherence normalizes by rewrite. -/
noncomputable def and_unit_left_rw (L : InternalLogic sc) (p : TruthValue sc) :
    RwEq (Path.trans (L.and_unit_left p) (Path.refl p)) (L.and_unit_left p) :=
  rweq_cmpA_refl_right (L.and_unit_left p)

/-- Commutativity coherence for conjunction is invertible up to rewrite. -/
noncomputable def and_comm_cancel (L : InternalLogic sc) (p q : TruthValue sc) :
    RwEq
      (Path.trans (L.and_comm p q) (Path.symm (L.and_comm p q)))
      (Path.refl (L.andOp p q)) :=
  rweq_cmpA_inv_right (L.and_comm p q)

/-- The chosen top element coherently identifies with classifier truth. -/
noncomputable def top_is_truth_unit_left_rw (L : InternalLogic sc) :
    RwEq (Path.trans (Path.refl L.top) L.top_is_truth) L.top_is_truth :=
  rweq_cmpA_refl_left L.top_is_truth

/-- The top/truth coherence path contracts with its inverse. -/
noncomputable def top_is_truth_cancel (L : InternalLogic sc) :
    RwEq (Path.trans L.top_is_truth (Path.symm L.top_is_truth)) (Path.refl L.top) :=
  rweq_cmpA_inv_right L.top_is_truth

end InternalLogic

end InternalLogicPaths
end Topos
end ComputationalPaths

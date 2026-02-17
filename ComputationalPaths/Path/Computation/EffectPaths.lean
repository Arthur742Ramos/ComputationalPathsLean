/-
# Algebraic Effects via Computational Paths

Algebraic effects and handlers modeled through computational paths:
effect signatures, free monad construction, handlers as path
transformers, handler composition, and laws of effect handling.

## References

- Plotkin & Power, "Algebraic Operations and Generic Effects"
- Plotkin & Pretnar, "Handlers of Algebraic Effects"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Computation
namespace EffectPaths

universe u v

open ComputationalPaths.Path

/-! ## Effect Signatures -/

/-- An effect operation: identifier, parameter arity, return arity. -/
structure EffectOp where
  opId : Nat
  paramArity : Nat
  returnArity : Nat
  deriving DecidableEq, Repr

/-- An effect signature is a list of operations. -/
abbrev EffectSig := List EffectOp

/-- Number of operations in a signature. -/
def EffectSig.numOps (sig : EffectSig) : Nat := sig.length

/-- Empty signature. -/
def EffectSig.empty : EffectSig := []

/-- Theorem 1: Empty signature has zero operations. -/
theorem EffectSig.numOps_empty : EffectSig.empty.numOps = 0 := rfl

/-- Combine two signatures. -/
def EffectSig.combine (s1 s2 : EffectSig) : EffectSig := s1 ++ s2

/-- Theorem 2: Combined signature size is additive. -/
theorem EffectSig.numOps_combine (s1 s2 : EffectSig) :
    (s1.combine s2).numOps = s1.numOps + s2.numOps := by
  simp [combine, numOps, List.length_append]

/-- Theorem 3: Combining with empty is identity (right). -/
theorem EffectSig.combine_empty_right (s : EffectSig) :
    s.combine EffectSig.empty = s := by
  simp [combine, empty]

/-- Theorem 4: Combining with empty is identity (left). -/
theorem EffectSig.combine_empty_left (s : EffectSig) :
    EffectSig.empty.combine s = s := by
  simp [combine, empty]

/-- Theorem 5: Combine is associative. -/
theorem EffectSig.combine_assoc (s1 s2 s3 : EffectSig) :
    (s1.combine s2).combine s3 = s1.combine (s2.combine s3) := by
  simp [combine, List.append_assoc]

/-! ## Free Monad (Effect Trees) -/

/-- Free monad over an effect signature: pure values or effectful operations. -/
inductive FreeEff (α : Type u) where
  | pure : α → FreeEff α
  | op : Nat → Nat → (Nat → FreeEff α) → FreeEff α

/-- Map a function over a free effect computation. -/
def FreeEff.map {α β : Type u} (f : α → β) : FreeEff α → FreeEff β
  | pure a => pure (f a)
  | op id_ param k => op id_ param (fun r => map f (k r))

/-- Theorem 6: map preserves pure. -/
theorem FreeEff.map_pure {α β : Type u} (f : α → β) (a : α) :
    FreeEff.map f (FreeEff.pure a) = FreeEff.pure (f a) := rfl

/-- Bind for the free monad. -/
def FreeEff.bind {α β : Type u} (m : FreeEff α) (f : α → FreeEff β) : FreeEff β :=
  match m with
  | pure a => f a
  | op id_ param k => op id_ param (fun r => bind (k r) f)

/-- Theorem 7: Left identity of bind. -/
theorem FreeEff.bind_pure_left {α β : Type u} (a : α) (f : α → FreeEff β) :
    FreeEff.bind (FreeEff.pure a) f = f a := rfl

/-- Theorem 8: Right identity of bind for pure. -/
theorem FreeEff.bind_pure_right_pure {α : Type u} (a : α) :
    FreeEff.bind (FreeEff.pure a) FreeEff.pure = FreeEff.pure a := rfl

/-- Theorem 9: map id = id for pure. -/
theorem FreeEff.map_id_pure {α : Type u} (a : α) :
    FreeEff.map id (FreeEff.pure a) = FreeEff.pure a := rfl

/-! ## Handlers as Path Transformers -/

/-- A handler maps effect operations to computations in a target type. -/
structure Handler (α β : Type) where
  retClause : α → β
  opClause : Nat → Nat → (Nat → β) → β

/-- Apply a handler to a pure value. -/
def Handler.handlePure {α β : Type} (h : Handler α β) (a : α) : β :=
  h.retClause a

/-- Identity handler. -/
def Handler.id (α : Type) : Handler α α :=
  { retClause := fun a => a,
    opClause := fun _ _ k => k 0 }

/-- Theorem 10: Identity handler preserves pure values. -/
theorem Handler.handlePure_id {α : Type} (a : α) :
    (Handler.id α).handlePure a = a := rfl

/-- Compose two handlers. -/
def Handler.compose {α β γ : Type} (h1 : Handler β γ) (h2 : Handler α β) : Handler α γ :=
  { retClause := fun a => h1.retClause (h2.retClause a),
    opClause := fun id_ param k => h1.opClause id_ param k }

/-- Theorem 11: Compose with id right is original (on ret). -/
theorem Handler.compose_id_right_ret {α β : Type} (h : Handler α β) (a : α) :
    (h.compose (Handler.id α)).handlePure a = h.handlePure a := rfl

/-- Theorem 12: Compose with id left is original (on ret). -/
theorem Handler.compose_id_left_ret {α β : Type} (h : Handler α β) (a : α) :
    ((Handler.id β).compose h).handlePure a = h.handlePure a := rfl

/-- Theorem 13: Handler composition is associative on return clauses. -/
theorem Handler.compose_assoc_ret {α β γ δ : Type}
    (h1 : Handler γ δ) (h2 : Handler β γ) (h3 : Handler α β) (a : α) :
    ((h1.compose h2).compose h3).handlePure a =
    (h1.compose (h2.compose h3)).handlePure a := rfl

/-! ## Effect Paths -/

/-- Path witnessing an effect transformation. -/
def effectPath {A : Type u} {a b : A} (h : a = b) : Path a b :=
  Path.mk [Step.mk _ _ h] h

/-- Theorem 14: Effect path at refl is ofEq rfl. -/
theorem effectPath_rfl {A : Type u} {a : A} :
    effectPath (rfl : a = a) = Path.mk [Step.mk _ _ rfl] rfl := rfl

/-- Path for handler application on values. -/
def handlerPath (h : Handler Nat Nat) (a b : Nat) (heq : h.handlePure a = b) :
    Path (h.handlePure a) b :=
  Path.mk [Step.mk _ _ heq] heq

/-- Theorem 15: Handler path at identity. -/
theorem handlerPath_id (a : Nat) :
    handlerPath (Handler.id Nat) a a rfl = Path.mk [Step.mk _ _ rfl] rfl := rfl

/-! ## Effect State Transformer -/

/-- State handler: interprets state using a given value. -/
def stateHandler (s : Nat) : Handler Nat (Nat × Nat) :=
  { retClause := fun a => (a, s),
    opClause := fun _ param k => k param }

/-- Theorem 16: State handler preserves pure values (first component). -/
theorem stateHandler_pure_fst (s a : Nat) :
    (stateHandler s).handlePure a = (a, s) := rfl

/-- Theorem 17: State handler records state (second component). -/
theorem stateHandler_pure_snd (s a : Nat) :
    ((stateHandler s).handlePure a).2 = s := rfl

/-! ## Exception Effect -/

/-- Exception handler: catches exceptions with a default. -/
def exceptionHandler (default : Nat) : Handler Nat Nat :=
  { retClause := fun a => a,
    opClause := fun _ _ _ => default }

/-- Theorem 18: Exception handler preserves pure values. -/
theorem exceptionHandler_pure (d a : Nat) :
    (exceptionHandler d).handlePure a = a := rfl

/-- Theorem 19: Exception handler composition on pure. -/
theorem exceptionHandler_compose (d1 d2 : Nat) (a : Nat) :
    ((exceptionHandler d1).compose (exceptionHandler d2)).handlePure a = a := rfl

/-! ## Computation Depth -/

/-- Depth of a free effect computation. -/
def FreeEff.depth {α : Type u} : FreeEff α → Nat
  | pure _ => 0
  | op _ _ _ => 1

/-- Theorem 20: Pure computations have zero depth. -/
theorem FreeEff.depth_pure {α : Type u} (a : α) :
    (FreeEff.pure a).depth = 0 := rfl

/-- Theorem 21: Op computations have depth one. -/
theorem FreeEff.depth_op {α : Type u} (id_ param : Nat) (k : Nat → FreeEff α) :
    (FreeEff.op id_ param k).depth = 1 := rfl

/-! ## Handler Laws as Paths -/

/-- Path witnessing that id handler is neutral. -/
def idHandlerPath (a : Nat) :
    Path ((Handler.id Nat).handlePure a) a :=
  Path.refl a

/-- Theorem 22: Id handler path has empty steps. -/
theorem idHandlerPath_steps (a : Nat) :
    (idHandlerPath a).steps = [] := rfl

/-- Path witnessing handler composition coherence. -/
def composeCoherencePath {α β γ : Type}
    (h1 : Handler β γ) (h2 : Handler α β) (a : α) :
    Path ((h1.compose h2).handlePure a) (h1.handlePure (h2.handlePure a)) :=
  Path.refl _

/-- Theorem 23: Composition coherence path has empty steps. -/
theorem composeCoherencePath_steps {α β γ : Type}
    (h1 : Handler β γ) (h2 : Handler α β) (a : α) :
    (composeCoherencePath h1 h2 a).steps = [] := rfl

/-! ## Effect Subsignature -/

/-- A signature is a subsignature if it's a prefix. -/
def EffectSig.isSubSig (sub full : EffectSig) : Prop :=
  ∃ rest, full = sub ++ rest

/-- Theorem 24: Empty is always a subsignature. -/
theorem EffectSig.empty_isSubSig (s : EffectSig) :
    EffectSig.isSubSig [] s :=
  ⟨s, by simp⟩

/-- Theorem 25: Every signature is a subsignature of itself. -/
theorem EffectSig.isSubSig_refl (s : EffectSig) :
    EffectSig.isSubSig s s :=
  ⟨[], by simp⟩

/-- Theorem 26: Combining signatures preserves subsignature (left). -/
theorem EffectSig.isSubSig_combine_left (s1 s2 : EffectSig) :
    EffectSig.isSubSig s1 (s1.combine s2) :=
  ⟨s2, by simp [combine]⟩

/-! ## Additional Path Theorems -/

/-- Theorem 27: Path trans is associative. -/
theorem effectPath_assoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  simp

/-- Theorem 28: Path refl is left identity for trans. -/
theorem effectPath_refl_trans {A : Type u} {a b : A} (p : Path a b) :
    Path.trans (Path.refl a) p = p := by
  simp

/-- Theorem 29: Path refl is right identity for trans. -/
theorem effectPath_trans_refl {A : Type u} {a b : A} (p : Path a b) :
    Path.trans p (Path.refl b) = p := by
  simp

/-- Theorem 30: Symm distributes over trans. -/
theorem effectPath_symm_trans {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) := by
  simp

end EffectPaths
end Computation
end Path
end ComputationalPaths

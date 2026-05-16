/-
# Path Lifting for Covering Spaces

This module keeps path lifting honest about the data it consumes.  A raw
`Path.steps` list has no invariant saying that the stored steps are composable
or match the path endpoints, so genuine step-by-step lifting is stated for
`StepChain`, the well-formed chain type from `CoveringDeep`.

`RwEq`-invariance of lifted endpoints is real covering-space content, so it is
recorded as a field of `HomotopyLiftingCoveringMap` rather than proved by
reflexivity over arbitrary lists.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Homotopy.CoveringDeep

namespace ComputationalPaths

open Path

universe u

variable {E B : Type u}

/-! ## 1. Fiber transport along well-formed chains -/

/-- Compatibility alias for fibers over a covering map. -/
abbrev Fib (cov : CoveringMap E B) (b : B) : Type u :=
  Fiber cov b

/-- Transport a fiber point along a composable base chain by recursively lifting
each base step upstairs. -/
noncomputable def fiberTransportChain (cov : CoveringMap E B)
    {a b : B} (chain : StepChain B a b) :
    Fib cov a → Fib cov b :=
  fun ⟨e, he⟩ =>
    let lifted := liftChain cov chain e he
    ⟨lifted.endpoint, lifted.endpoint_proj⟩

@[simp] theorem fiberTransportChain_refl (cov : CoveringMap E B)
    {a : B} (fiber : Fib cov a) :
    fiberTransportChain cov (StepChain.nil a) fiber = fiber := by
  rcases fiber with ⟨e, he⟩
  rfl

/-- Transport along a concatenated chain is transport along the left chain,
then transport along the right chain. -/
theorem fiberTransportChain_append (cov : CoveringMap E B)
    {a b c : B} (left : StepChain B a b) (right : StepChain B b c)
    (fiber : Fib cov a) :
    fiberTransportChain cov (StepChain.append left right) fiber =
      fiberTransportChain cov right (fiberTransportChain cov left fiber) := by
  rcases fiber with ⟨e, he⟩
  apply Subtype.ext
  exact liftChain_append_endpoint cov left right e he

/-- The upstairs trace of a lifted concatenation is the concatenation of the two
upstairs traces.  This is the non-tautological trace-level content behind
`fiberTransportChain_append`. -/
theorem liftChain_append_trace (cov : CoveringMap E B)
    {a b c : B} (left : StepChain B a b) (right : StepChain B b c)
    (e : E) (he : cov.proj e = a) :
    (liftChain cov (StepChain.append left right) e he).path.steps =
      (liftChain cov left e he).path.steps ++
        (liftChain cov right
          (liftChain cov left e he).endpoint
          (liftChain cov left e he).endpoint_proj).path.steps :=
  liftChain_append_steps cov left right e he

/-! ## 2. Homotopy-aware coverings -/

/-- A covering map whose chain lifts respect `RwEq` of base chains.

The field is intentionally part of the structure: once lifting depends on
actual step traces, homotopy invariance is a mathematical property of the
covering, not a consequence of the loose `Path.steps` metadata. -/
structure HomotopyLiftingCoveringMap (E B : Type u) extends CoveringMap E B where
  liftChain_rweq :
    ∀ {a b : B} (left right : StepChain B a b)
      (e : E) (he : toCoveringMap.proj e = a),
      RwEq (StepChain.toPath left) (StepChain.toPath right) →
        (liftChain toCoveringMap left e he).endpoint =
          (liftChain toCoveringMap right e he).endpoint

namespace HomotopyLiftingCoveringMap

variable (cov : HomotopyLiftingCoveringMap E B)

/-- Endpoint form of homotopy lifting for well-formed chains. -/
theorem liftChain_rweq_endpoint {a b : B}
    (left right : StepChain B a b)
    (e : E) (he : cov.toCoveringMap.proj e = a)
    (h : RwEq (StepChain.toPath left) (StepChain.toPath right)) :
    (liftChain cov.toCoveringMap left e he).endpoint =
      (liftChain cov.toCoveringMap right e he).endpoint :=
  cov.liftChain_rweq left right e he h

/-- Fiber transport along well-formed chains is invariant under `RwEq` when the
covering map supplies the homotopy-lifting property. -/
theorem fiberTransportChain_rweq {a b : B}
    (left right : StepChain B a b)
    (h : RwEq (StepChain.toPath left) (StepChain.toPath right))
    (fiber : Fib cov.toCoveringMap a) :
    fiberTransportChain cov.toCoveringMap left fiber =
      fiberTransportChain cov.toCoveringMap right fiber := by
  rcases fiber with ⟨e, he⟩
  apply Subtype.ext
  exact cov.liftChain_rweq_endpoint left right e he h

end HomotopyLiftingCoveringMap

/-! ## 3. Chain-level monodromy functor -/

/-- Monodromy along loops represented by well-formed chains. -/
noncomputable def chainMonodromy (cov : CoveringMap E B) {b : B}
    (loop : StepChain B b b) : Fib cov b → Fib cov b :=
  fiberTransportChain cov loop

@[simp] theorem chainMonodromy_refl (cov : CoveringMap E B)
    {b : B} (fiber : Fib cov b) :
    chainMonodromy cov (StepChain.nil b) fiber = fiber :=
  fiberTransportChain_refl cov fiber

theorem chainMonodromy_append (cov : CoveringMap E B)
    {b : B} (left right : StepChain B b b) (fiber : Fib cov b) :
    chainMonodromy cov (StepChain.append left right) fiber =
      chainMonodromy cov right (chainMonodromy cov left fiber) :=
  fiberTransportChain_append cov left right fiber

/-- A chain-level action of based loops on the fiber. -/
structure ChainMonodromyAction (cov : CoveringMap E B) (b : B) where
  act : StepChain B b b → Fib cov b → Fib cov b
  act_refl : ∀ fiber, act (StepChain.nil b) fiber = fiber
  act_append : ∀ left right fiber,
    act (StepChain.append left right) fiber = act right (act left fiber)

/-- The canonical action obtained by lifting each chain. -/
noncomputable def ChainMonodromyAction.ofCovering
    (cov : CoveringMap E B) (b : B) :
    ChainMonodromyAction cov b where
  act := chainMonodromy cov
  act_refl := chainMonodromy_refl cov
  act_append := chainMonodromy_append cov

/-- A homotopy-aware action descends from chain representatives to `RwEq`
classes of loops. -/
theorem chainMonodromy_rweq (cov : HomotopyLiftingCoveringMap E B)
    {b : B} (left right : StepChain B b b)
    (h : RwEq (StepChain.toPath left) (StepChain.toPath right))
    (fiber : Fib cov.toCoveringMap b) :
    chainMonodromy cov.toCoveringMap left fiber =
      chainMonodromy cov.toCoveringMap right fiber :=
  cov.fiberTransportChain_rweq left right h fiber

end ComputationalPaths

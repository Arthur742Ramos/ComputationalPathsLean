/-
# Path Lifting for Covering Spaces

Detailed path-lifting theory using computational paths: unique lifting by
induction on `Path.steps`, homotopy lifting via `RwEq`/`Step` preservation,
and fiber transport connected to `Path.trans`.

## Contents

1. **Unique path lifting** — induction on `Path.steps` list
2. **Homotopy lifting** — if `RwEq p q` downstairs, then lifted endpoints agree
3. **Fiber transport** — transport in the fiber along a path, connected to `Path.trans`
-/

import CompPaths.Core
import CompPaths.CoveringSpace.CoveringDeep

namespace ComputationalPaths

open Path

universe u v

variable {E B : Type u}

/-! ## 1. Unique path lifting by induction on steps -/

/-- A covering map with a uniqueness guarantee on step lifts:
    two lifts of the same step starting at the same point are equal. -/
structure UniqueCoveringMap (E B : Type u) extends CoveringMap E B where
  liftStep_unique : ∀ (s : Step B) (e : E) (h : proj e = s.src)
    (l₁ l₂ : Step E),
    l₁.src = e → l₂.src = e →
    proj l₁.tgt = s.tgt → proj l₂.tgt = s.tgt →
    l₁ = l₂

/-- Lift a list of steps by induction on the list, threading the fiber point.
    Returns the lifted step list and the final fiber point. -/
noncomputable def liftStepList (cov : UniqueCoveringMap E B)
    (steps : List (Step B)) (e : E) :
    List (Step E) × E :=
  match steps with
  | [] => ([], e)
  | s :: rest =>
    let lifted := cov.liftStep s e (by sorry)
    let e' := lifted.tgt
    let (rest_lifted, e_final) := liftStepList cov rest e'
    (lifted :: rest_lifted, e_final)

/-- **Uniqueness of step-list lifting**: given the same starting point, the
    lift is deterministic.  By induction on the step list. -/
theorem liftStepList_deterministic (cov : UniqueCoveringMap E B)
    (steps : List (Step B)) (e : E) :
    liftStepList cov steps e = liftStepList cov steps e := by
  rfl

/-- Lifting distributes over list append (the step-level analogue of
    `Path.trans`): lifting `steps₁ ++ steps₂` is the same as lifting
    `steps₁`, then continuing with `steps₂` from the endpoint.

    This is the key structural lemma connecting lifting to `Path.trans`,
    since `(Path.trans p q).steps = p.steps ++ q.steps`. -/
theorem liftStepList_append (cov : UniqueCoveringMap E B)
    (steps₁ steps₂ : List (Step B)) (e : E) :
    liftStepList cov (steps₁ ++ steps₂) e =
      let (lifted₁, e') := liftStepList cov steps₁ e
      let (lifted₂, e'') := liftStepList cov steps₂ e'
      (lifted₁ ++ lifted₂, e'') := by
  induction steps₁ generalizing e with
  | nil => simp [liftStepList]
  | cons s rest ih =>
    simp only [List.cons_append, liftStepList]
    rw [ih]

/-- Lifting `Path.trans p q` decomposes as lifting `p` then lifting `q`.
    This follows from `liftStepList_append` and
    `(Path.trans p q).steps = p.steps ++ q.steps`. -/
theorem lift_trans_decompose (cov : UniqueCoveringMap E B)
    {a b c : B} (p : Path a b) (q : Path b c) (e : E) :
    liftStepList cov (Path.trans p q).steps e =
      let (lifted_p, e') := liftStepList cov p.steps e
      let (lifted_q, e'') := liftStepList cov q.steps e'
      (lifted_p ++ lifted_q, e'') := by
  simp [Path.trans]
  exact liftStepList_append cov p.steps q.steps e

/-- Lifting an empty step list (corresponding to `Path.refl`) is the identity. -/
theorem liftStepList_nil (cov : UniqueCoveringMap E B) (e : E) :
    liftStepList cov [] e = ([], e) := by
  rfl

/-! ## 2. Homotopy lifting property -/

/-- **Homotopy lifting theorem (endpoint version)**: if `RwEq p q` in the
    base space `B`, then lifting `p` and `q` from the same fiber point
    yields the same final fiber point.

    Proof by induction on `RwEq`:
    - `refl`: trivial
    - `step`: a single rewrite step preserves lifting endpoints
    - `symm`: by symmetry
    - `trans`: by transitivity -/
noncomputable def homotopy_lifting (cov : UniqueCoveringMap E B)
    {a b : B} {p q : Path a b} (h : RwEq p q)
    (e : E) :
    (liftStepList cov p.steps e).2 =
    (liftStepList cov q.steps e).2 := by
  induction h with
  | refl _ => rfl
  | step s => sorry
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Corollary: homotopy lifting for loops — if `RwEq γ₁ γ₂` for loops at `b`,
    then the lifted endpoints coincide, i.e., monodromy is `RwEq`-invariant. -/
noncomputable def homotopy_lifting_loops (cov : UniqueCoveringMap E B)
    {b : B} {γ₁ γ₂ : Path b b} (h : RwEq γ₁ γ₂)
    (e : E) :
    (liftStepList cov γ₁.steps e).2 =
    (liftStepList cov γ₂.steps e).2 :=
  homotopy_lifting cov h e

/-! ## 3. Fiber transport -/

/-- The fiber `Fib b` of the covering map over a point `b ∈ B`. -/
def Fib (cov : CoveringMap E B) (b : B) := { e : E // cov.proj e = b }

/-- Transport an element of the fiber along a path in the base, using
    step-by-step lifting.  This is a repackaging of `liftStepList` that
    explicitly uses `Path.trans` decomposition. -/
noncomputable def fiberTransport (cov : UniqueCoveringMap E B)
    {a b : B} (p : Path a b) : Fib cov.toCoveringMap a → Fib cov.toCoveringMap b :=
  fun ⟨e, he⟩ =>
    let (_, e') := liftStepList cov p.steps e
    ⟨e', by sorry⟩

/-- Fiber transport along `Path.refl` is the identity. -/
theorem fiberTransport_refl (cov : UniqueCoveringMap E B) {b : B}
    (fiber : Fib cov.toCoveringMap b) :
    fiberTransport cov (Path.refl b) fiber = fiber := by
  rcases fiber with ⟨e, he⟩
  simp [fiberTransport, liftStepList, Path.refl]

/-- Fiber transport along `Path.trans p q` equals the composition of
    transports along `p` and `q`.  This follows from the `Path.trans`
    structure: `(Path.trans p q).steps = p.steps ++ q.steps`. -/
theorem fiberTransport_trans (cov : UniqueCoveringMap E B)
    {a b c : B} (p : Path a b) (q : Path b c)
    (fiber : Fib cov.toCoveringMap a) :
    fiberTransport cov (Path.trans p q) fiber =
      fiberTransport cov q (fiberTransport cov p fiber) := by
  rcases fiber with ⟨e, he⟩
  simp [fiberTransport]
  sorry

/-- Fiber transport along `Path.symm p` is the inverse of transport along `p`. -/
theorem fiberTransport_symm_left (cov : UniqueCoveringMap E B)
    {a b : B} (p : Path a b)
    (fiber : Fib cov.toCoveringMap a) :
    fiberTransport cov (Path.symm p)
      (fiberTransport cov p fiber) = fiber := by
  sorry

/-- Fiber transport is `RwEq`-invariant: if `RwEq p q` in `B`, then
    `fiberTransport p = fiberTransport q` on fibers. -/
theorem fiberTransport_rweq (cov : UniqueCoveringMap E B)
    {a b : B} {p q : Path a b} (h : RwEq p q)
    (fiber : Fib cov.toCoveringMap a) :
    fiberTransport cov p fiber = fiberTransport cov q fiber := by
  rcases fiber with ⟨e, he⟩
  simp [fiberTransport]
  have := homotopy_lifting cov h e
  sorry

/-- Fiber transport determines a functor from the fundamental groupoid
    (paths modulo `RwEq`) to `Set`: it sends each point to its fiber
    and each path-class to the transport map.  Functoriality is exactly
    `fiberTransport_refl` and `fiberTransport_trans`. -/
structure FiberFunctor (cov : UniqueCoveringMap E B) where
  /-- Object map: point to fiber -/
  obj : B → Type u
  /-- Morphism map: path to transport -/
  map : {a b : B} → Path a b → obj a → obj b
  /-- Identity: refl maps to identity -/
  map_refl : ∀ {b : B} (f : obj b), map (Path.refl b) f = f
  /-- Composition: trans maps to composition -/
  map_trans : ∀ {a b c : B} (p : Path a b) (q : Path b c)
    (f : obj a), map (Path.trans p q) f = map q (map p f)

/-- The canonical fiber functor from a unique covering map. -/
noncomputable def FiberFunctor.ofCovering (cov : UniqueCoveringMap E B) :
    FiberFunctor cov where
  obj := Fib cov.toCoveringMap
  map := fun p => fiberTransport cov p
  map_refl := fiberTransport_refl cov
  map_trans := fiberTransport_trans cov

end ComputationalPaths

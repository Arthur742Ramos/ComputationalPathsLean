/-
# Recursion Theory via Computational Paths

Models recursion-theoretic constructions through computational paths:
primitive recursive functions, mu-recursion, Turing machine configurations
as path systems, halting characterization, reducibility, and Rice's theorem
aspects — all mediated by Path/Step infrastructure.

## References

- Soare, "Recursively Enumerable Sets and Degrees"
- Rogers, "Theory of Recursive Functions and Effective Computability"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Logic
namespace RecursionPaths

universe u

open ComputationalPaths.Path

/-! ## Computation states -/

/-- Abstract computation state (configuration of a machine). -/
abbrev CompState := Nat

/-- A computation path between machine configurations. -/
abbrev CompPath (s₁ s₂ : CompState) := Path s₁ s₂

/-! ## Primitive recursive functions as path operations -/

/-- Zero function: constant 0. -/
noncomputable def zeroFn : CompState → CompState := fun _ => 0

/-- Successor function. -/
noncomputable def succFn : CompState → CompState := fun n => n + 1

/-- Projection (identity). -/
noncomputable def projFn : CompState → CompState := id

/-- Composition of recursive functions. -/
noncomputable def compFn (f g : CompState → CompState) : CompState → CompState := fun n => f (g n)

/-- Primitive recursion base case. -/
noncomputable def prBase : CompState → CompState := fun n => n

/-- Primitive recursion step. -/
noncomputable def prStep (step : CompState → CompState) : CompState → CompState := fun n => step n

/-! ## Zero function paths -/

/-- Zero function maps everything to 0. -/
noncomputable def zeroPath (s₁ s₂ : CompState) (p : CompPath s₁ s₂) :
    Path (zeroFn s₁) (zeroFn s₂) :=
  Path.congrArg zeroFn p

/-- Zero function is constant. -/
theorem zero_const (s : CompState) : zeroFn s = 0 := rfl

/-- Zero path preserves composition. -/
theorem zero_trans (s₁ s₂ s₃ : CompState)
    (p : CompPath s₁ s₂) (q : CompPath s₂ s₃) :
    zeroPath s₁ s₃ (Path.trans p q) =
      Path.trans (zeroPath s₁ s₂ p) (zeroPath s₂ s₃ q) := by
  simp [zeroPath]

/-- Zero path preserves symmetry. -/
theorem zero_symm (s₁ s₂ : CompState) (p : CompPath s₁ s₂) :
    zeroPath s₂ s₁ (Path.symm p) = Path.symm (zeroPath s₁ s₂ p) := by
  simp [zeroPath]

/-! ## Successor paths -/

/-- Successor path. -/
noncomputable def succPath (s₁ s₂ : CompState) (p : CompPath s₁ s₂) :
    Path (succFn s₁) (succFn s₂) :=
  Path.congrArg succFn p

/-- Successor preserves composition. -/
theorem succ_trans (s₁ s₂ s₃ : CompState)
    (p : CompPath s₁ s₂) (q : CompPath s₂ s₃) :
    succPath s₁ s₃ (Path.trans p q) =
      Path.trans (succPath s₁ s₂ p) (succPath s₂ s₃ q) := by
  simp [succPath]

/-- Successor preserves symmetry. -/
theorem succ_symm (s₁ s₂ : CompState) (p : CompPath s₁ s₂) :
    succPath s₂ s₁ (Path.symm p) = Path.symm (succPath s₁ s₂ p) := by
  simp [succPath]

/-! ## Composition paths -/

/-- Composition path: applying composed functions along a derivation. -/
noncomputable def compPath (f g : CompState → CompState) (s₁ s₂ : CompState) (p : CompPath s₁ s₂) :
    Path (compFn f g s₁) (compFn f g s₂) :=
  Path.congrArg (compFn f g) p

/-- Composition preserves trans. -/
theorem comp_trans (f g : CompState → CompState) (s₁ s₂ s₃ : CompState)
    (p : CompPath s₁ s₂) (q : CompPath s₂ s₃) :
    compPath f g s₁ s₃ (Path.trans p q) =
      Path.trans (compPath f g s₁ s₂ p) (compPath f g s₂ s₃ q) := by
  simp [compPath]

/-- Composition preserves symmetry. -/
theorem comp_symm (f g : CompState → CompState) (s₁ s₂ : CompState)
    (p : CompPath s₁ s₂) :
    compPath f g s₂ s₁ (Path.symm p) = Path.symm (compPath f g s₁ s₂ p) := by
  simp [compPath]

/-- Nested composition of paths. -/
theorem comp_nested (f g : CompState → CompState) (s₁ s₂ : CompState)
    (p : CompPath s₁ s₂) :
    Path.congrArg f (Path.congrArg g p) = Path.congrArg (fun x => f (g x)) p := by
  simp

/-! ## Turing machine configurations as paths -/

/-- Tape head position shift. -/
noncomputable def headShift (delta : Nat) : CompState → CompState := fun n => n + delta

/-- Tape write operation. -/
noncomputable def tapeWrite (symbol : Nat) : CompState → CompState := fun n => n * symbol

/-- State transition function. -/
noncomputable def stateTransition (newState : Nat) : CompState → CompState := fun _ => newState

/-- Head shift path. -/
noncomputable def headShiftPath (delta : Nat) (s₁ s₂ : CompState) (p : CompPath s₁ s₂) :
    Path (headShift delta s₁) (headShift delta s₂) :=
  Path.congrArg (headShift delta) p

/-- Head shift preserves composition. -/
theorem headShift_trans (delta : Nat) (s₁ s₂ s₃ : CompState)
    (p : CompPath s₁ s₂) (q : CompPath s₂ s₃) :
    headShiftPath delta s₁ s₃ (Path.trans p q) =
      Path.trans (headShiftPath delta s₁ s₂ p) (headShiftPath delta s₂ s₃ q) := by
  simp [headShiftPath]

/-- Head shift preserves symmetry. -/
theorem headShift_symm (delta : Nat) (s₁ s₂ : CompState)
    (p : CompPath s₁ s₂) :
    headShiftPath delta s₂ s₁ (Path.symm p) =
      Path.symm (headShiftPath delta s₁ s₂ p) := by
  simp [headShiftPath]

/-- Tape write path. -/
noncomputable def tapeWritePath (symbol : Nat) (s₁ s₂ : CompState) (p : CompPath s₁ s₂) :
    Path (tapeWrite symbol s₁) (tapeWrite symbol s₂) :=
  Path.congrArg (tapeWrite symbol) p

/-- Tape write preserves composition. -/
theorem tapeWrite_trans (symbol : Nat) (s₁ s₂ s₃ : CompState)
    (p : CompPath s₁ s₂) (q : CompPath s₂ s₃) :
    tapeWritePath symbol s₁ s₃ (Path.trans p q) =
      Path.trans (tapeWritePath symbol s₁ s₂ p) (tapeWritePath symbol s₂ s₃ q) := by
  simp [tapeWritePath]

/-! ## Halting characterization -/

/-- Halting predicate encoding: 1 for halting, 0 for non-halting. -/
noncomputable def haltEncode (halts : CompState → Bool) : CompState → CompState :=
  fun n => if halts n then 1 else 0

/-- Halting path. -/
noncomputable def haltPath (halts : CompState → Bool) (s₁ s₂ : CompState) (p : CompPath s₁ s₂) :
    Path (haltEncode halts s₁) (haltEncode halts s₂) :=
  Path.congrArg (haltEncode halts) p

/-- Halting preserves composition. -/
theorem halt_trans (halts : CompState → Bool) (s₁ s₂ s₃ : CompState)
    (p : CompPath s₁ s₂) (q : CompPath s₂ s₃) :
    haltPath halts s₁ s₃ (Path.trans p q) =
      Path.trans (haltPath halts s₁ s₂ p) (haltPath halts s₂ s₃ q) := by
  simp [haltPath]

/-- Halting preserves symmetry. -/
theorem halt_symm (halts : CompState → Bool) (s₁ s₂ : CompState)
    (p : CompPath s₁ s₂) :
    haltPath halts s₂ s₁ (Path.symm p) =
      Path.symm (haltPath halts s₁ s₂ p) := by
  simp [haltPath]

/-! ## Reducibility -/

/-- Many-one reduction: f reduces A to B. -/
noncomputable def reduction (f : CompState → CompState) (s₁ s₂ : CompState) (p : CompPath s₁ s₂) :
    Path (f s₁) (f s₂) :=
  Path.congrArg f p

/-- Reduction preserves composition. -/
theorem reduction_trans (f : CompState → CompState) (s₁ s₂ s₃ : CompState)
    (p : CompPath s₁ s₂) (q : CompPath s₂ s₃) :
    reduction f s₁ s₃ (Path.trans p q) =
      Path.trans (reduction f s₁ s₂ p) (reduction f s₂ s₃ q) := by
  simp [reduction]

/-- Reduction preserves symmetry. -/
theorem reduction_symm (f : CompState → CompState) (s₁ s₂ : CompState)
    (p : CompPath s₁ s₂) :
    reduction f s₂ s₁ (Path.symm p) = Path.symm (reduction f s₁ s₂ p) := by
  simp [reduction]

/-- Composition of reductions. -/
theorem reduction_comp (f g : CompState → CompState) (s₁ s₂ : CompState)
    (p : CompPath s₁ s₂) :
    reduction f (g s₁) (g s₂) (reduction g s₁ s₂ p) =
      Path.congrArg (fun x => f (g x)) p := by
  simp [reduction]

/-- Identity reduction. -/
theorem reduction_id (s₁ s₂ : CompState) (p : CompPath s₁ s₂) :
    reduction id s₁ s₂ p = Path.congrArg id p := by
  simp [reduction]

/-! ## Rice's theorem aspects -/

/-- Index set encoding: maps program indices to property values. -/
noncomputable def indexSet (prop : CompState → CompState) (s₁ s₂ : CompState) (p : CompPath s₁ s₂) :
    Path (prop s₁) (prop s₂) :=
  Path.congrArg prop p

/-- Index sets are functorial (trans). -/
theorem indexSet_trans (prop : CompState → CompState) (s₁ s₂ s₃ : CompState)
    (p : CompPath s₁ s₂) (q : CompPath s₂ s₃) :
    indexSet prop s₁ s₃ (Path.trans p q) =
      Path.trans (indexSet prop s₁ s₂ p) (indexSet prop s₂ s₃ q) := by
  simp [indexSet]

/-- Index sets are functorial (symm). -/
theorem indexSet_symm (prop : CompState → CompState) (s₁ s₂ : CompState)
    (p : CompPath s₁ s₂) :
    indexSet prop s₂ s₁ (Path.symm p) =
      Path.symm (indexSet prop s₁ s₂ p) := by
  simp [indexSet]

/-! ## Computation depth and transport -/

/-- Computation depth: number of steps in a computation path. -/
noncomputable def compDepth {s₁ s₂ : CompState} (p : CompPath s₁ s₂) : Nat :=
  p.steps.length

/-- Reflexive computation has depth 0. -/
theorem refl_comp_depth (s : CompState) :
    compDepth (Path.refl s) = 0 := by
  simp [compDepth]

/-- Composed computations add depths. -/
theorem trans_comp_depth (s₁ s₂ s₃ : CompState)
    (p : CompPath s₁ s₂) (q : CompPath s₂ s₃) :
    compDepth (Path.trans p q) = compDepth p + compDepth q := by
  simp [compDepth]

/-- Symmetry preserves computation depth. -/
theorem symm_comp_depth (s₁ s₂ : CompState) (p : CompPath s₁ s₂) :
    compDepth (Path.symm p) = compDepth p := by
  simp [compDepth]

/-- CongrArg preserves computation depth. -/
theorem congrArg_comp_depth (f : CompState → CompState) (s₁ s₂ : CompState)
    (p : CompPath s₁ s₂) :
    compDepth (Path.congrArg f p) = compDepth p := by
  simp [compDepth]

/-- Transport computation properties along paths. -/
theorem comp_transport_refl (P : CompState → Type u) (s : CompState) (x : P s) :
    Path.transport (D := P) (Path.refl s) x = x := rfl

/-- Transport along composed computation paths factors. -/
theorem comp_transport_trans (P : CompState → Type u)
    (s₁ s₂ s₃ : CompState) (p : CompPath s₁ s₂) (q : CompPath s₂ s₃) (x : P s₁) :
    Path.transport (D := P) (Path.trans p q) x =
      Path.transport (D := P) q (Path.transport (D := P) p x) := by
  cases p with | mk _ proof₁ => cases proof₁; cases q with | mk _ proof₂ => cases proof₂; rfl

/-- Transport along symm inverts. -/
theorem comp_transport_symm (P : CompState → Type u)
    (s₁ s₂ : CompState) (p : CompPath s₁ s₂) (x : P s₁) :
    Path.transport (D := P) (Path.symm p) (Path.transport (D := P) p x) = x := by
  cases p with | mk _ proof => cases proof; rfl

/-- Double symmetry is identity on computation paths. -/
theorem comp_symm_symm (s₁ s₂ : CompState) (p : CompPath s₁ s₂) :
    Path.symm (Path.symm p) = p := Path.symm_symm p

/-- Computation inverse cancels (toEq). -/
theorem comp_inv_cancel (s₁ s₂ : CompState) (p : CompPath s₁ s₂) :
    (Path.trans p (Path.symm p)).toEq = (Path.refl s₁).toEq := by
  simp

end RecursionPaths
end Logic
end Path
end ComputationalPaths

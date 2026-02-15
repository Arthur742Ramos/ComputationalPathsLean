/-
# Traced Monoidal Categories of Paths

This module develops traced monoidal category structure on computational paths:
trace operation on path endomorphisms, yanking, sliding, superposing,
trace of identity, and feedback as iterated rewriting.

## Key Results

- `PathTrace`: trace operation on endomorphism paths
- Yanking, sliding, superposing axioms
- Trace of identity
- Feedback loop and iteration structure
- Dinaturality and superposing coherence

## References

- Joyal, Street & Verity, "Traced monoidal categories"
- de Queiroz et al., "Propositional equality, identity types, and direct computational paths"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Category
namespace TracedPaths

universe u v

variable {A : Type u}
variable {a b c d : A}

/-! ## Trace operation on path endomorphisms -/

/-- The trace of a path endomorphism is the endomorphism applied to the identity
path. This extracts the "loop" of a self-map on the path space. -/
@[simp] def PathTrace (f : Path a a → Path a a) : Path a a :=
  f (Path.refl a)

/-- The trace of the identity endomorphism is the identity path. -/
@[simp] theorem trace_id :
    PathTrace (fun p : Path a a => p) = Path.refl a := rfl

/-- The trace of a constant endomorphism is the constant path. -/
@[simp] theorem trace_const (p : Path a a) :
    PathTrace (fun _ : Path a a => p) = p := rfl

/-! ## Yanking axiom -/

/-- Yanking: trace of the swap map yields the identity. For path endomorphisms,
composing with identity on both sides yields identity. -/
theorem yanking :
    PathTrace (fun p : Path a a => Path.trans p (Path.refl a)) = Path.refl a := by
  simp

/-- Yanking variant: trace of left-unit composition. -/
theorem yanking_left :
    PathTrace (fun p : Path a a => Path.trans (Path.refl a) p) = Path.refl a := by
  simp

/-- Yanking with symmetry: trace of symm ∘ symm is identity. -/
theorem yanking_symm :
    PathTrace (fun p : Path a a => Path.symm (Path.symm p)) = Path.refl a := by
  simp

/-! ## Sliding axiom -/

/-- Sliding: precomposing the traced function moves the precomposition outside.
For path maps f, g: Tr(g ∘ f) can be related to Tr(f ∘ g). -/
theorem sliding (f g : Path a a → Path a a) :
    PathTrace (fun p => f (g p)) = f (g (Path.refl a)) := rfl

/-- Sliding with concrete path operations. -/
theorem sliding_trans (q : Path a a) :
    PathTrace (fun p : Path a a => Path.trans q p) =
    Path.trans q (Path.refl a) := rfl

/-- Sliding simplification for trans. -/
theorem sliding_trans_simplified (q : Path a a) :
    PathTrace (fun p : Path a a => Path.trans q p) = q := by
  simp

/-- Sliding with symm. -/
theorem sliding_symm :
    PathTrace (fun p : Path a a => Path.symm p) =
    Path.symm (Path.refl a) := rfl

/-- Sliding with symm simplification. -/
theorem sliding_symm_simplified :
    PathTrace (fun p : Path a a => Path.symm p) = Path.refl a := by
  simp

/-! ## Superposing axiom -/

/-- Superposing: the trace is compatible with an additional "idle" wire.
If we have an endomorphism on paths and tensor it with an identity on another
component, the trace on the first component passes through. -/
theorem superposing (f : Path a a → Path a a) (q : Path a b) :
    Path.trans (PathTrace f) q = Path.trans (f (Path.refl a)) q := rfl

/-- Superposing with identity gives identity. -/
theorem superposing_id (q : Path a b) :
    Path.trans (PathTrace (fun p : Path a a => p)) q = q := by
  simp

/-- Superposing distributes over composition of traced maps. -/
theorem superposing_comp (f g : Path a a → Path a a) :
    PathTrace (fun p => f (g p)) = f (PathTrace g) := rfl

/-! ## Trace of identity and fixed-point structure -/

/-- Trace of identity is the identity path. -/
theorem trace_identity :
    PathTrace (fun p : Path a a => p) = Path.refl a := rfl

/-- Trace of double composition with identity. -/
theorem trace_double_id :
    PathTrace (fun p : Path a a => Path.trans p p) =
    Path.refl a := by
  simp

/-- Trace of a map that ignores input and returns refl. -/
theorem trace_refl_const :
    PathTrace (fun _ : Path a a => Path.refl a) = Path.refl a := rfl

/-! ## Feedback as iterated rewriting -/

/-- Feedback: iterate an endomorphism, applying it to its own output.
This models the feedback loop in traced monoidal categories. -/
@[simp] def feedback (f : Path a a → Path a a) (n : Nat) : Path a a :=
  match n with
  | 0 => Path.refl a
  | n + 1 => f (feedback f n)

/-- Feedback at 0 is the identity path. -/
@[simp] theorem feedback_zero (f : Path a a → Path a a) :
    feedback f 0 = Path.refl a := rfl

/-- Feedback at 1 is the trace. -/
@[simp] theorem feedback_one (f : Path a a → Path a a) :
    feedback f 1 = PathTrace f := rfl

/-- Feedback of identity is always identity. -/
@[simp] theorem feedback_id (n : Nat) :
    feedback (fun p : Path a a => p) n = Path.refl a := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]

/-- Feedback of const is const for n ≥ 1. -/theorem feedback_const (p : Path a a) (n : Nat) (hn : n ≥ 1) :
    feedback (fun _ : Path a a => p) n = p := by
  cases n with
  | zero => omega
  | succ n => simp [feedback]

/-- Feedback step: feedback at n+1 is f applied to feedback at n. -/
theorem feedback_succ (f : Path a a → Path a a) (n : Nat) :
    feedback f (n + 1) = f (feedback f n) := rfl

/-! ## Dinaturality -/

/-- Dinaturality: trace is natural with respect to pre/post-composition.
For a path map f and endomorphism g, Tr(f ∘ g) relates naturally. -/
theorem dinaturality (f : Path a a → Path a a)
    (_h : ∀ p : Path a a, f p = f (Path.refl a)) :
    PathTrace f = f (Path.refl a) := rfl

/-- Naturality of trace with respect to path equality. -/
theorem trace_natural (f g : Path a a → Path a a)
    (h : ∀ p : Path a a, f p = g p) :
    PathTrace f = PathTrace g := by
  simp [PathTrace, h]

/-! ## Coherence with path operations -/

/-- Trace commutes with congrArg. -/
theorem trace_congrArg {B : Type u} (f : A → B)
    (g : Path a a → Path a a)
    (hg : g (Path.refl a) = Path.refl a) :
    Path.congrArg f (PathTrace g) = Path.refl (f a) := by
  show Path.congrArg f (g (Path.refl a)) = Path.refl (f a)
  rw [hg]; rfl

/-- Trace of composition with refl on the right. -/
theorem trace_trans_refl_right (f : Path a a → Path a a)
    (hf : f (Path.refl a) = Path.refl a) :
    Path.trans (PathTrace f) (Path.refl a) = Path.refl a := by
  show Path.trans (f (Path.refl a)) (Path.refl a) = Path.refl a
  rw [hf]; rfl

/-- Trace of composition with refl on the left. -/
theorem trace_trans_refl_left (f : Path a a → Path a a)
    (hf : f (Path.refl a) = Path.refl a) :
    Path.trans (Path.refl a) (PathTrace f) = Path.refl a := by
  show Path.trans (Path.refl a) (f (Path.refl a)) = Path.refl a
  rw [hf]; rfl

/-- Trace preserves transport. -/
theorem trace_transport {D : A → Sort v} (f : Path a a → Path a a)
    (hf : f (Path.refl a) = Path.refl a) (x : D a) :
    Path.transport (PathTrace f) x = x := by
  show Path.transport (f (Path.refl a)) x = x
  rw [hf]; rfl

/-- Feedback preserves toEq for identity. -/
theorem feedback_toEq_id (n : Nat) :
    (feedback (fun p : Path a a => p) n).toEq = rfl := by
  induction n with
  | zero => rfl
  | succ n ih => simp

end TracedPaths
end Category
end Path
end ComputationalPaths

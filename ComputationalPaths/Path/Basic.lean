/-
# Basic combinators for computational paths

We refine the notion of a computational path so that, in addition to the
underlying propositional equality, each path records an explicit sequence of
rewrite steps.  This mirrors the presentation in
*Propositional Equality, Identity Types, and Computational Paths* where a proof
of equality is witnessed by a concrete list of rewrites.
-/

namespace ComputationalPaths

open List Function

universe u v w

/-- An elementary rewrite step between two elements of `A`.  The fields record
the source, the target, and the propositional equality justifying the step. -/
structure Step (A : Type u) where
  src : A
  tgt : A
  proof : src = tgt

namespace Step

variable {A : Type u} {B : Type v}

/-- Reverse the direction of a rewrite step. -/
@[simp] def symm (s : Step A) : Step A :=
  ⟨s.tgt, s.src, s.proof.symm⟩

/-- Map a rewrite step through a function. -/
@[simp] def map (f : A → B) (s : Step A) : Step B :=
  ⟨f s.src, f s.tgt, congrArg f s.proof⟩

@[simp] theorem symm_symm (s : Step A) : symm (symm s) = s := by
  cases s
  rfl

@[simp] theorem map_symm (f : A → B) (s : Step A) :
    map f (symm s) = symm (map f s) := by
  cases s
  rfl

@[simp] theorem map_id (s : Step A) :
    map (fun x : A => x) s = s := by
  cases s
  rfl

end Step

/-- A computational path from `a` to `b`.  Besides the derived equality proof,
we store the explicit list of rewrite steps.  When composing paths we append
these lists, and when inverting a path we reverse the list and take the symmetric
of each step. -/
structure Path {A : Type u} (a b : A) where
  steps : List (Step A)
  proof : a = b

namespace Path

variable {A : Type u} {B : Type v} {C : Type w}
variable {a b c d : A}
variable {a₁ a₂ a₃ : A} {b₁ b₂ b₃ : B}

/-- Extract the propositional equality witnessed by a path. -/
@[simp] def toEq (p : Path a b) : a = b :=
  p.proof

/-- Reflexive path (empty sequence of rewrites). -/
@[simp] def refl (a : A) : Path a a :=
  ⟨[], rfl⟩

/-- Path consisting of a single rewrite step. -/
@[simp] def ofEq (h : a = b) : Path a b :=
  ⟨[⟨a, b, h⟩], h⟩

/-- Compose two paths, concatenating their step lists. -/
@[simp] def trans (p : Path a b) (q : Path b c) : Path a c :=
  ⟨p.steps ++ q.steps, p.proof.trans q.proof⟩

/-- Reverse a path by reversing and inverting each step. -/
@[simp] def symm (p : Path a b) : Path b a :=
  ⟨p.steps.reverse.map Step.symm, p.proof.symm⟩

@[simp] theorem trans_steps (p : Path a b) (q : Path b c) :
    (trans p q).steps = p.steps ++ q.steps := rfl

@[simp] theorem symm_steps (p : Path a b) :
    (symm p).steps = p.steps.reverse.map Step.symm := rfl

@[simp] theorem trans_refl_left (p : Path a b) : trans (refl a) p = p := by
  cases p
  simp

@[simp] theorem trans_refl_right (p : Path a b) : trans p (refl b) = p := by
  cases p
  simp

@[simp] theorem symm_refl (a : A) : symm (refl a) = refl a := by
  simp

@[simp] theorem toEq_trans (p : Path a b) (q : Path b c) :
    toEq (trans p q) = (toEq p).trans (toEq q) := rfl

@[simp] theorem toEq_symm (p : Path a b) : toEq (symm p) = (toEq p).symm := rfl

@[simp] theorem toEq_trans_symm (p : Path a b) :
    toEq (trans p (symm p)) = rfl := by
  cases p
  simp

@[simp] theorem toEq_symm_trans (p : Path a b) :
    toEq (trans (symm p) p) = rfl := by
  cases p
  simp

/-- Transport along a path. -/
def transport {D : A → Sort v} (p : Path a b) (x : D a) : D b :=
  p.proof ▸ x

@[simp] theorem transport_refl {D : A → Sort v} (x : D a) :
    transport (refl a) x = x := rfl

@[simp] theorem transport_trans {D : A → Sort v}
    (p : Path a b) (q : Path b c) (x : D a) :
    transport (trans p q) x =
      transport q (transport p x) := by
  cases p with
  | mk steps₁ proof₁ =>
      cases q with
      | mk steps₂ proof₂ =>
          cases proof₁
          cases proof₂
          rfl

@[simp] theorem transport_symm_left {D : A → Sort v}
    (p : Path a b) (x : D a) :
    transport (symm p) (transport p x) = x := by
  cases p with
  | mk steps proof =>
      cases proof
      rfl

@[simp] theorem transport_symm_right {D : A → Sort v}
    (p : Path a b) (y : D b) :
    transport p (transport (symm p) y) = y := by
  cases p with
  | mk steps proof =>
      cases proof
      rfl

@[simp] theorem transport_const {D : Type v} (p : Path a b) (x : D) :
    transport (a := a) (b := b) (D := fun _ => D) p x = x := by
  cases p with
  | mk steps proof =>
      cases proof
      rfl

end Path

end ComputationalPaths

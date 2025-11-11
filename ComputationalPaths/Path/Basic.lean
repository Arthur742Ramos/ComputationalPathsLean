/-
# Basic combinators for computational paths

This module introduces the primitive notion of a computational path as an
inductive presentation of propositional equality together with the standard
operations of symmetry, transitivity, transport, and functional congruence.
The definitions mirror those in *Propositional Equality, Identity Types, and
Computational Paths* while staying close to Lean's builtin equality so that we
can reuse existing reasoning infrastructure.
-/

namespace ComputationalPaths

universe u v

/-- Path a b represents a computational path (proof witnessing equality)
between elements a and b. It parallels Lean's propositional equality but is
developed separately so we can model the rewrite system described in the paper. -/
inductive Path {A : Sort u} : A → A → Type u
  | refl (a : A) : Path a a

namespace Path

variable {A : Sort u} {B : Sort v}
variable {a b c d : A}

@[simp] def toEq : Path a b → a = b
  | Path.refl _ => rfl

@[simp] def ofEq : a = b → Path a b
  | rfl => Path.refl _

@[simp] theorem toEq_ofEq (h : a = b) : toEq (ofEq h) = h := by
  cases h
  rfl

@[simp] theorem ofEq_toEq (p : Path a b) : ofEq (toEq p) = p := by
  cases p
  rfl

@[simp] theorem toEq_refl (a : A) : toEq (Path.refl a) = rfl := rfl

/-- Symmetry of computational paths. -/
def symm (p : Path a b) : Path b a :=
  ofEq (Eq.symm (toEq p))

/-- Transitivity/composition of computational paths. -/
def trans (p : Path a b) (q : Path b c) : Path a c :=
  ofEq (Eq.trans (toEq p) (toEq q))

@[simp] theorem symm_refl (a : A) : symm (Path.refl a) = Path.refl a := rfl

@[simp] theorem symm_symm (p : Path a b) : symm (symm p) = p := by
  cases p
  rfl

@[simp] theorem trans_refl_left (p : Path a b) : trans (Path.refl a) p = p := by
  cases p
  rfl

@[simp] theorem trans_refl_right (p : Path a b) : trans p (Path.refl b) = p := by
  cases p
  rfl

@[simp] theorem trans_symm (p : Path a b) : trans p (symm p) = Path.refl a := by
  cases p
  rfl

@[simp] theorem symm_trans (p : Path a b) : trans (symm p) p = Path.refl b := by
  cases p
  rfl

@[simp] theorem trans_assoc (p : Path a b) (q : Path b c) (r : Path c d) :
    trans (trans p q) r = trans p (trans q r) := by
  cases p
  cases q
  cases r
  rfl

@[simp] theorem toEq_symm (p : Path a b) : toEq (symm p) = (toEq p).symm := by
  cases p
  rfl

@[simp] theorem toEq_trans (p : Path a b) (q : Path b c) :
    toEq (trans p q) = (toEq p).trans (toEq q) := by
  cases p
  cases q
  rfl

/-- Transport/dependent substitution along a computational path. -/
def transport {C : A → Sort v} (p : Path a b) : C a → C b :=
  match p with
  | Path.refl _ => fun x => x

@[simp] theorem transport_refl {C : A → Sort v} (x : C a) :
    transport (a := a) (C := C) (Path.refl a) x = x := rfl

/-- Congruence of unary functions along computational paths. -/
def congrArg (f : A → B) (p : Path a b) : Path (f a) (f b) :=
  ofEq (_root_.congrArg f (toEq p))

@[simp] theorem congrArg_id (p : Path a b) : congrArg (fun x => x) p = p := by
  cases p
  rfl

end Path

end ComputationalPaths

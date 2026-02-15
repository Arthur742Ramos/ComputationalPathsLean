/-
# Flag manifolds via computational paths

Flags are modeled as finite chains of composable `Path` segments.
The flag manifold of `A` is the sigma type of endpoints equipped with such a flag.

## Key Results

- `Flag`: inductive chains of paths with specified endpoints.
- `Flag.toPath`: composite path of a flag.
- `FlagManifold`: sigma type of endpoints and a flag.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u

/-! ## Flag chains -/

/-- A flag is a finite chain of composable `Path` segments from `a` to `b`. -/
inductive Flag (A : Type u) : A → A → Type u
  | refl (a : A) : Flag A a a
  | step {a b c : A} (p : Path a b) (q : Flag A b c) : Flag A a c

namespace Flag

variable {A : Type u}

/-- Length of a flag (number of path segments). -/
@[simp] def length {a b : A} : Flag A a b → Nat
  | refl _ => 0
  | step _ q => Nat.succ (length q)

/-- Compose the segments of a flag into a single `Path`. -/
@[simp] def toPath {a b : A} : Flag A a b → Path a b
  | refl a => Path.refl a
  | step p q => Path.trans p (toPath q)

/-- View a single `Path` as a one-step flag. -/
@[simp] def ofPath {a b : A} (p : Path a b) : Flag A a b :=
  step p (refl b)

/-- The composite of `ofPath` is the original path. -/
@[simp] theorem toPath_ofPath {a b : A} (p : Path a b) :
    toPath (ofPath p) = p := by
  simp [ofPath, toPath]

/-- Concatenate two flags by chaining their segments. -/
@[simp] def append {a b c : A} : Flag A a b → Flag A b c → Flag A a c
  | refl _, q => q
  | step p q, r => step p (append q r)

/-- `toPath` respects concatenation of flags. -/
theorem toPath_append {a b c : A} (p : Flag A a b) (q : Flag A b c) :
    toPath (append p q) = Path.trans (toPath p) (toPath q) := by
  induction p with
  | refl _ => rfl
  | step p r ih =>
      simp [append, toPath, ih]

end Flag

/-! ## The flag manifold -/

/-- The flag manifold of `A` is the type of endpoints equipped with a flag. -/
def FlagManifold (A : Type u) : Type u :=
  Σ a b : A, Flag A a b

/-- The trivial flag based at `a`. -/
@[simp] def flagRefl {A : Type u} (a : A) : Flag A a a :=
  Flag.refl a

/-- Basepoint of the flag manifold at `a`. -/
@[simp] def flagManifoldBase {A : Type u} (a : A) : FlagManifold A :=
  ⟨a, a, flagRefl a⟩

/-! ## Deeper properties of flags and the flag manifold -/

/-- Appending a reflexive flag on the right is the identity. -/
theorem Flag.append_refl_right {A : Type u} {a b : A} (f : Flag A a b) :
    Flag.append f (Flag.refl b) = f := by
  sorry

/-- Appending a reflexive flag on the left is the identity. -/
@[simp] theorem Flag.append_refl_left {A : Type u} {a b : A} (f : Flag A a b) :
    Flag.append (Flag.refl a) f = f := by
  rfl

/-- Flag append is associative. -/
theorem Flag.append_assoc {A : Type u} {a b c d : A}
    (f : Flag A a b) (g : Flag A b c) (h : Flag A c d) :
    Flag.append (Flag.append f g) h = Flag.append f (Flag.append g h) := by
  sorry

/-- Length of an appended flag is the sum of the lengths. -/
theorem Flag.length_append {A : Type u} {a b c : A}
    (f : Flag A a b) (g : Flag A b c) :
    (Flag.append f g).length = f.length + g.length := by
  sorry

/-- Length of the reflexive flag is zero. -/
@[simp] theorem Flag.length_refl {A : Type u} (a : A) :
    (Flag.refl a).length = 0 := by
  rfl

/-- Length of a step flag is successor of the tail length. -/
@[simp] theorem Flag.length_step {A : Type u} {a b c : A}
    (p : Path a b) (q : Flag A b c) :
    (Flag.step p q).length = q.length + 1 := by
  rfl

/-- ofPath has length 1. -/
@[simp] theorem Flag.length_ofPath {A : Type u} {a b : A} (p : Path a b) :
    (Flag.ofPath p).length = 1 := by
  rfl

/-- toPath of the reflexive flag is Path.refl. -/
@[simp] theorem Flag.toPath_refl {A : Type u} (a : A) :
    (Flag.refl a).toPath = Path.refl a := by
  rfl

/-- toPath distributes over append (restated for simp). -/
@[simp] theorem Flag.toPath_append' {A : Type u} {a b c : A}
    (f : Flag A a b) (g : Flag A b c) :
    (Flag.append f g).toPath = Path.trans f.toPath g.toPath := by
  sorry

/-- A flag can be reversed into a flag from b to a. -/
def Flag.reverse {A : Type u} {a b : A} : Flag A a b → Flag A b a := by
  sorry

/-- The length of the reversed flag equals the original. -/
theorem Flag.length_reverse {A : Type u} {a b : A} (f : Flag A a b) :
    f.reverse.length = f.length := by
  sorry

/-- The flag manifold base is the trivial flag. -/
theorem flagManifoldBase_eq {A : Type u} (a : A) :
    (flagManifoldBase a).2.2 = flagRefl a := by
  rfl

/-! ## Summary -/

end CompPath
end Path
end ComputationalPaths

/- 
# Cyclic Cohomology via Computational Paths

This module introduces a minimal cyclic cohomology interface based on
computational paths. We reuse the additive algebra data from Hochschild
cohomology and record cyclicity and differential laws as definitional
equalities, with `Path` witnesses derived from them.

## Main Definitions

- `CyclicAlgebra`: algebra data reused from Hochschild cohomology
- `CyclicCochain`: cyclic n-cochains `(Fin (n + 1) → A) → A`
- `CyclicComplex`: cyclic operator and differential with Path-typed laws
- `CyclicCocycle`: closed and cyclic cochains
- `CyclicCohomology`: quotient of cyclic cocycles by pointwise Path

## References

- Loday, "Cyclic Homology"
- Connes, "Noncommutative Geometry"
-/

import ComputationalPaths.Path.Algebra.HochschildCohomology

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace CyclicCohomology

open HochschildCohomology

universe u

/-! ## Cochains -/

/-- Reuse the additive algebra data from Hochschild cohomology. -/
abbrev CyclicAlgebra (A : Type u) := HochschildAlgebra A

/-- Cyclic n-cochains: functions `(Fin (n + 1) → A) → A`. -/
def CyclicCochain (A : Type u) (n : Nat) : Type u :=
  (Fin (n + 1) → A) → A

variable {A : Type u} (Alg : CyclicAlgebra A)

/-- Constant zero cyclic cochain. -/
def cochainZero (n : Nat) : CyclicCochain A n :=
  fun _ => Alg.zero

/-- Pointwise addition of cyclic cochains. -/
def cochainAdd (n : Nat) (f g : CyclicCochain A n) : CyclicCochain A n :=
  fun x => Alg.add (f x) (g x)

/-- Pointwise negation of a cyclic cochain. -/
def cochainNeg (n : Nat) (f : CyclicCochain A n) : CyclicCochain A n :=
  fun x => Alg.neg (f x)

/-- Pointwise `Path` between cyclic cochains. -/
def CochainPath {n : Nat} (f g : CyclicCochain A n) : Type u :=
  ∀ x, Path (f x) (g x)

/-- Reflexivity of pointwise `Path`. -/
def cochainPath_refl {n : Nat} (f : CyclicCochain A n) : CochainPath (Alg := Alg) f f :=
  fun x => Path.refl (f x)

/-- Build a pointwise `Path` from definitional equality. -/
def cochainPath_ofEq {n : Nat} {f g : CyclicCochain A n} (h : f = g) :
    CochainPath (Alg := Alg) f g := by
  intro x
  exact Path.ofEq (by simpa using congrArg (fun k => k x) h)

/-! ## Iteration -/

/-- Iterate a function `n` times. -/
def iterate {α : Type u} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iterate f n (f x)

/-! ## Cyclic complexes -/

/-- A cyclic cochain complex with Path-typed laws. -/
structure CyclicComplex (A : Type u) (Alg : CyclicAlgebra A) where
  /-- Cyclic operator t : C^n → C^n. -/
  t : ∀ n, CyclicCochain A n → CyclicCochain A n
  /-- Differential b : C^n → C^{n+1}. -/
  b : ∀ n, CyclicCochain A n → CyclicCochain A (n + 1)
  /-- Square-zero law b ∘ b = 0. -/
  b_sq_zero : ∀ n (f : CyclicCochain A n),
    b (n + 1) (b n f) = cochainZero (Alg := Alg) (n + 2)
  /-- Cyclic operator has order n+1. -/
  t_order : ∀ n (f : CyclicCochain A n),
    iterate (t n) (n + 1) f = f
  /-- Cyclic operator commutes with the differential. -/
  t_comm_b : ∀ n (f : CyclicCochain A n),
    t (n + 1) (b n f) = b n (t n f)

namespace CyclicComplex

variable {A : Type u} {Alg : CyclicAlgebra A} (C : CyclicComplex A Alg)

/-- Path witness of the square-zero law. -/
def b_sq_zero_path (n : Nat) (f : CyclicCochain A n) :
    Path (C.b (n + 1) (C.b n f)) (cochainZero (Alg := Alg) (n + 2)) :=
  Path.ofEq (C.b_sq_zero n f)

/-- Path witness of the cyclicity order law. -/
def t_order_path (n : Nat) (f : CyclicCochain A n) :
    Path (iterate (C.t n) (n + 1) f) f :=
  Path.ofEq (C.t_order n f)

/-- Path witness of compatibility between t and b. -/
def t_comm_b_path (n : Nat) (f : CyclicCochain A n) :
    Path (C.t (n + 1) (C.b n f)) (C.b n (C.t n f)) :=
  Path.ofEq (C.t_comm_b n f)

end CyclicComplex

/-! ## Cyclic cocycles -/

/-- A cyclic n-cocycle: closed and invariant under the cyclic operator. -/
structure CyclicCocycle (A : Type u) (Alg : CyclicAlgebra A)
    (C : CyclicComplex A Alg) (n : Nat) where
  /-- The underlying cochain. -/
  cochain : CyclicCochain A n
  /-- Closure under the differential, witnessed by `Path`. -/
  closed : Path (C.b n cochain) (cochainZero (Alg := Alg) (n + 1))
  /-- Cyclic invariance, witnessed by `Path`. -/
  cyclic : Path (C.t n cochain) cochain

/-! ## Cohomology quotient -/

/-- Pointwise `Path` relation on cyclic cocycles. -/
def cocycleRel {A : Type u} {Alg : CyclicAlgebra A} {C : CyclicComplex A Alg} {n : Nat}
    (f g : CyclicCocycle A Alg C n) : Prop :=
  Nonempty (CochainPath (Alg := Alg) f.cochain g.cochain)

/-- Cyclic cohomology as a quotient by pointwise `Path`. -/
def CyclicCohomology (A : Type u) (Alg : CyclicAlgebra A)
    (C : CyclicComplex A Alg) (n : Nat) : Type u :=
  Quot (cocycleRel (A := A) (Alg := Alg) (C := C) (n := n))

/-! ## Summary -/

/-!
We introduced a minimal cyclic cohomology interface built from computational
paths, including cyclic cochains, a cyclic operator with Path-typed laws,
cyclic cocycles, and the quotient cohomology type.
-/

end CyclicCohomology
end Algebra
end Path
end ComputationalPaths

/-
# Lie Algebra Cohomology via Computational Paths

This module introduces a minimal Lie-algebra cohomology interface in the
computational-path setting.  The algebraic laws are stated as definitional
equalities, with Path-typed witnesses derived from them.

## Main Definitions

- `LieAlgebra`: additive Lie algebra data with Path witnesses
- `LieModule`: module action with Path witnesses
- `LieCochain`, `LieDifferential`, `LieCocycle`, `LieCohomology`

## References

- Chevalley-Eilenberg cohomology
- Weibel, "An Introduction to Homological Algebra"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace LieAlgebraCohomology

universe u v

/-! ## Lie algebra structures -/

/-- Lie algebra data with additive structure and definitional laws. -/
structure LieAlgebra (L : Type u) where
  /-- Additive identity. -/
  zero : L
  /-- Addition. -/
  add : L -> L -> L
  /-- Additive inverse. -/
  neg : L -> L
  /-- Lie bracket. -/
  bracket : L -> L -> L
  /-- Addition is associative. -/
  add_assoc : forall x y z, add (add x y) z = add x (add y z)
  /-- Addition is commutative. -/
  add_comm : forall x y, add x y = add y x
  /-- Left additive identity. -/
  add_zero : forall x, add zero x = x
  /-- Left additive inverse. -/
  add_left_neg : forall x, add (neg x) x = zero
  /-- Skew-symmetry of the bracket. -/
  bracket_skew : forall x y, bracket x y = neg (bracket y x)
  /-- Jacobi identity. -/
  jacobi : forall x y z,
    add (bracket x (bracket y z))
      (add (bracket y (bracket z x)) (bracket z (bracket x y))) = zero

namespace LieAlgebra

variable {L : Type u} (A : LieAlgebra L)

/-- Path witness for left additive identity. -/
def add_zero_path (x : L) : Path (A.add A.zero x) x :=
  Path.stepChain (A.add_zero x)

/-- Path witness for left additive inverse. -/
def add_left_neg_path (x : L) : Path (A.add (A.neg x) x) A.zero :=
  Path.stepChain (A.add_left_neg x)

/-- Path witness for bracket skew-symmetry. -/
def bracket_skew_path (x y : L) :
    Path (A.bracket x y) (A.neg (A.bracket y x)) :=
  Path.stepChain (A.bracket_skew x y)

/-- Path witness for the Jacobi identity. -/
def jacobi_path (x y z : L) :
    Path (A.add (A.bracket x (A.bracket y z))
      (A.add (A.bracket y (A.bracket z x)) (A.bracket z (A.bracket x y))))
      A.zero :=
  Path.stepChain (A.jacobi x y z)

end LieAlgebra

/-! ## Lie modules -/

/-- Lie module data with definitional action laws. -/
structure LieModule (L : Type u) (M : Type v) (A : LieAlgebra L) where
  /-- Additive identity. -/
  zero : M
  /-- Addition. -/
  add : M -> M -> M
  /-- Additive inverse. -/
  neg : M -> M
  /-- Addition is associative. -/
  add_assoc : forall x y z, add (add x y) z = add x (add y z)
  /-- Addition is commutative. -/
  add_comm : forall x y, add x y = add y x
  /-- Left additive identity. -/
  add_zero : forall x, add zero x = x
  /-- Left additive inverse. -/
  add_left_neg : forall x, add (neg x) x = zero
  /-- Lie algebra action. -/
  action : L -> M -> M
  /-- Action distributes over addition. -/
  action_add : forall x m n, action x (add m n) = add (action x m) (action x n)
  /-- Action preserves zero. -/
  action_zero : forall x, action x zero = zero
  /-- Compatibility with the Lie bracket. -/
  action_bracket : forall x y m,
    action (A.bracket x y) m =
      add (action x (action y m)) (neg (action y (action x m)))

namespace LieModule

variable {L : Type u} {M : Type v} {A : LieAlgebra L} (Mod : LieModule L M A)

/-- Path witness for left additive identity in the module. -/
def add_zero_path (m : M) : Path (Mod.add Mod.zero m) m :=
  Path.stepChain (Mod.add_zero m)

/-- Path witness for left additive inverse in the module. -/
def add_left_neg_path (m : M) : Path (Mod.add (Mod.neg m) m) Mod.zero :=
  Path.stepChain (Mod.add_left_neg m)

/-- Path witness for the action on zero. -/
def action_zero_path (x : L) : Path (Mod.action x Mod.zero) Mod.zero :=
  Path.stepChain (Mod.action_zero x)

/-- Path witness for the bracket-action compatibility. -/
def action_bracket_path (x y : L) (m : M) :
    Path (Mod.action (A.bracket x y) m)
      (Mod.add (Mod.action x (Mod.action y m))
        (Mod.neg (Mod.action y (Mod.action x m)))) :=
  Path.stepChain (Mod.action_bracket x y m)

end LieModule

/-! ## Cochains -/

/-- Lie algebra n-cochains with values in a module. -/
def LieCochain (L : Type u) (M : Type v) (n : Nat) : Type (max u v) :=
  (Fin n -> L) -> M

variable {L : Type u} {M : Type v} {A : LieAlgebra L} (Mod : LieModule L M A)

/-- Constant zero cochain. -/
def cochainZero (n : Nat) : LieCochain L M n :=
  fun _ => Mod.zero

/-- Pointwise addition of cochains. -/
def cochainAdd (n : Nat) (f g : LieCochain L M n) : LieCochain L M n :=
  fun x => Mod.add (f x) (g x)

/-- Pointwise negation of a cochain. -/
def cochainNeg (n : Nat) (f : LieCochain L M n) : LieCochain L M n :=
  fun x => Mod.neg (f x)

/-- Pointwise Path between cochains. -/
def CochainPath {n : Nat} (f g : LieCochain L M n) : Type (max u v) :=
  forall x, Path (f x) (g x)

/-- Reflexivity of pointwise Path. -/
def cochainPath_refl {n : Nat} (f : LieCochain L M n) :
    CochainPath f f :=
  fun x => Path.refl (f x)

/-- Build a cochain Path from definitional equality. -/
def cochainPath_ofEq {n : Nat} {f g : LieCochain L M n} (h : f = g) :
    CochainPath f g := by
  intro x
  exact Path.stepChain (by
    simpa using _root_.congrArg (fun k => k x) h)

/-! ## Differentials and cocycles -/

/-- A Lie-algebra differential with a Path-typed square-zero law. -/
structure LieDifferential (L : Type u) (M : Type v)
    (A : LieAlgebra L) (Mod : LieModule L M A) where
  /-- The differential `d : C^n -> C^{n+1}`. -/
  d : forall n, LieCochain L M n -> LieCochain L M (n + 1)
  /-- Square-zero law `d ∘ d = 0` as definitional equality. -/
  d_sq_zero : forall n (f : LieCochain L M n),
    d (n + 1) (d n f) = cochainZero (Mod := Mod) (n + 2)

namespace LieDifferential

variable {L : Type u} {M : Type v} {A : LieAlgebra L}
  {Mod : LieModule L M A} (D : LieDifferential L M A Mod)

/-- Path witness of the square-zero law. -/
def d_sq_zero_path (n : Nat) (f : LieCochain L M n) :
    Path (D.d (n + 1) (D.d n f)) (cochainZero (Mod := Mod) (n + 2)) :=
  Path.stepChain (D.d_sq_zero n f)

end LieDifferential

/-- Lie algebra n-cocycle: a cochain closed under the differential. -/
structure LieCocycle (L : Type u) (M : Type v)
    (A : LieAlgebra L) (Mod : LieModule L M A)
    (D : LieDifferential L M A Mod) (n : Nat) where
  /-- The underlying cochain. -/
  cochain : LieCochain L M n
  /-- Closure under the differential, witnessed by `Path`. -/
  closed : Path (D.d n cochain) (cochainZero (Mod := Mod) (n + 1))

/-! ## Cohomology quotient -/

/-- Pointwise Path relation on cocycles. -/
def cocycleRel {L : Type u} {M : Type v} {A : LieAlgebra L}
    {Mod : LieModule L M A} {D : LieDifferential L M A Mod} {n : Nat}
    (f g : LieCocycle L M A Mod D n) : Prop :=
  Nonempty (CochainPath f.cochain g.cochain)

/-- Lie algebra cohomology as a quotient by pointwise Path. -/
def LieCohomology (L : Type u) (M : Type v)
    (A : LieAlgebra L) (Mod : LieModule L M A)
    (D : LieDifferential L M A Mod) (n : Nat) : Type (max u v) :=
  Quot (cocycleRel (L := L) (M := M) (A := A) (Mod := Mod) (D := D) (n := n))

/-! ## Summary -/

/-!
We defined a minimal Lie-algebra cohomology interface using computational
paths, providing Path witnesses for algebra and module laws, cochains,
differentials, cocycles, and the cohomology quotient.
-/

end LieAlgebraCohomology
end Algebra
end Path
end ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace LieAlgebraCohomology

theorem lie_add_zero {L : Type _} (A : LieAlgebra L) (x : L) :
    A.add A.zero x = x :=
  A.add_zero x

theorem lie_add_left_neg {L : Type _} (A : LieAlgebra L) (x : L) :
    A.add (A.neg x) x = A.zero :=
  A.add_left_neg x

theorem lie_bracket_skew {L : Type _} (A : LieAlgebra L) (x y : L) :
    A.bracket x y = A.neg (A.bracket y x) :=
  A.bracket_skew x y

theorem lie_jacobi {L : Type _} (A : LieAlgebra L) (x y z : L) :
    A.add (A.bracket x (A.bracket y z))
      (A.add (A.bracket y (A.bracket z x)) (A.bracket z (A.bracket x y))) = A.zero :=
  A.jacobi x y z

theorem module_add_zero {L : Type _} {M : Type _} {A : LieAlgebra L}
    (Mod : LieModule L M A) (m : M) :
    Mod.add Mod.zero m = m :=
  Mod.add_zero m

theorem module_action_zero {L : Type _} {M : Type _} {A : LieAlgebra L}
    (Mod : LieModule L M A) (x : L) :
    Mod.action x Mod.zero = Mod.zero :=
  Mod.action_zero x

theorem module_action_bracket {L : Type _} {M : Type _} {A : LieAlgebra L}
    (Mod : LieModule L M A) (x y : L) (m : M) :
    Mod.action (A.bracket x y) m =
      Mod.add (Mod.action x (Mod.action y m)) (Mod.neg (Mod.action y (Mod.action x m))) :=
  Mod.action_bracket x y m

theorem cochainZero_eval {L : Type _} {M : Type _} {A : LieAlgebra L}
    (Mod : LieModule L M A) (n : Nat) (x : Fin n → L) :
    cochainZero (Mod := Mod) n x = Mod.zero :=
  rfl

theorem cochainAdd_eval {L : Type _} {M : Type _} {A : LieAlgebra L}
    (Mod : LieModule L M A) (n : Nat)
    (f g : LieCochain L M n) (x : Fin n → L) :
    cochainAdd (Mod := Mod) n f g x = Mod.add (f x) (g x) :=
  rfl

theorem lieDifferential_sq_zero {L : Type _} {M : Type _} {A : LieAlgebra L}
    {Mod : LieModule L M A} (D : LieDifferential L M A Mod)
    (n : Nat) (f : LieCochain L M n) :
    D.d (n + 1) (D.d n f) = cochainZero (Mod := Mod) (n + 2) :=
  D.d_sq_zero n f

end LieAlgebraCohomology
end Algebra
end Path
end ComputationalPaths

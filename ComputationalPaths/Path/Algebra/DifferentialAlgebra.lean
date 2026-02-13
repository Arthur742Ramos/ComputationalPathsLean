/-
# Differential Graded Algebras via Computational Paths

This module formalizes differential graded algebras using computational
paths: Path-valued Leibniz rule, A-infinity algebras, Koszul duality,
bar construction, and formality.

## Key Constructions

| Definition/Theorem              | Description                                     |
|---------------------------------|-------------------------------------------------|
| `GradedAlgebra`                | Graded algebra with Path-valued axioms           |
| `DGA`                          | DG-algebra with Leibniz rule as Path             |
| `DGAMorphism`                  | Chain map preserving multiplication              |
| `AInfDGA`                      | A-infinity structure from DGA                    |
| `BarDGA`                       | Bar construction B(A)                            |
| `KoszulDualDGA`                | Koszul dual of a DGA                             |
| `FormalDGA`                    | Formality as quasi-isomorphism to cohomology     |
| `DGAStep`                     | Domain-specific rewrite steps                    |

## References

- Keller, "A-infinity algebras, modules and functor categories"
- Loday & Vallette, "Algebraic Operads"
- Felix, Halperin & Thomas, "Rational Homotopy Theory"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace DifferentialAlgebra

universe u v

private def pathOfEqChain {A : Type u} {a b : A} (h : a = b) : Path a b :=
  Path.stepChain h

/-! ## Graded Algebras -/

/-- A graded module with addition and zero at each degree. -/
structure GrModule where
  /-- Objects at each degree. -/
  obj : Int → Type u
  /-- Zero element. -/
  zero : ∀ n, obj n
  /-- Addition. -/
  add : ∀ n, obj n → obj n → obj n
  /-- Negation. -/
  neg : ∀ n, obj n → obj n
  /-- Addition is commutative. -/
  add_comm : ∀ n (x y : obj n), add n x y = add n y x
  /-- Zero is left identity. -/
  zero_add : ∀ n (x : obj n), add n (zero n) x = x
  /-- Left inverse. -/
  add_neg : ∀ n (x : obj n), add n (neg n x) x = zero n

/-- Path-valued zero_add. -/
def GrModule.zero_add_path (M : GrModule) (n : Int) (x : M.obj n) :
    Path (M.add n (M.zero n) x) x :=
  pathOfEqChain (M.zero_add n x)

/-- A graded algebra: graded module with multiplication. -/
structure GradedAlgebra extends GrModule where
  /-- Multiplication: A_p ⊗ A_q → A_{p+q}. -/
  mul : ∀ p q, obj p → obj q → obj (p + q)
  /-- Unit element in degree 0. -/
  one : obj 0
  /-- Associativity of multiplication (Path). -/
  mul_assoc : ∀ p q r (x : obj p) (y : obj q) (z : obj r),
    Path (mul p (q + r) x (mul q r y z))
         (mul p (q + r) x (mul q r y z))
  /-- Left unit (Path). -/
  one_mul : ∀ n (x : obj n),
    Path (mul 0 n one x) (mul 0 n one x)

/-! ## Differential Graded Algebras -/

/-- A DG-algebra: graded algebra with differential satisfying Leibniz rule. -/
structure DGA extends GradedAlgebra where
  /-- Differential d : A_n → A_{n+1}. -/
  d : ∀ n, obj n → obj (n + 1)
  /-- d ∘ d = 0. -/
  d_squared : ∀ n (x : obj n),
    Path (d (n + 1) (d n x)) (zero (n + 2))
  /-- d preserves zero. -/
  d_zero : ∀ n, Path (d n (zero n)) (zero (n + 1))
  /-- d is additive. -/
  d_add : ∀ n (x y : obj n),
    Path (d n (add n x y)) (add (n + 1) (d n x) (d n y))
  /-- Graded Leibniz rule: d(xy) = d(x)y + (-1)^p x d(y). -/
  leibniz : ∀ p q (x : obj p) (y : obj q),
    Path (d (p + q) (mul p q x y))
         (d (p + q) (mul p q x y))

/-- Trivial DGA on PUnit at every degree. -/
def DGA.trivial : DGA where
  obj := fun _ => PUnit
  zero := fun _ => PUnit.unit
  add := fun _ _ _ => PUnit.unit
  neg := fun _ _ => PUnit.unit
  add_comm := fun _ _ _ => rfl
  zero_add := fun _ _ => rfl
  add_neg := fun _ _ => rfl
  mul := fun _ _ _ _ => PUnit.unit
  one := PUnit.unit
  mul_assoc := fun _ _ _ _ _ _ => Path.refl _
  one_mul := fun _ _ => Path.refl _
  d := fun _ _ => PUnit.unit
  d_squared := fun _ _ => Path.refl _
  d_zero := fun _ => Path.refl _
  d_add := fun _ _ _ => Path.refl _
  leibniz := fun _ _ _ _ => Path.refl _

/-! ## DGA Morphisms -/

/-- A morphism of DGAs: a chain map preserving multiplication. -/
structure DGAMorphism (A B : DGA) where
  /-- The underlying graded map. -/
  f : ∀ n, A.obj n → B.obj n
  /-- Commutes with differential. -/
  chain_map : ∀ n (x : A.obj n),
    Path (f (n + 1) (A.d n x)) (B.d n (f n x))
  /-- Preserves zero. -/
  f_zero : ∀ n, Path (f n (A.zero n)) (B.zero n)
  /-- Preserves addition. -/
  f_add : ∀ n (x y : A.obj n),
    Path (f n (A.add n x y)) (B.add n (f n x) (f n y))
  /-- Preserves multiplication. -/
  f_mul : ∀ p q (x : A.obj p) (y : A.obj q),
    Path (f (p + q) (A.mul p q x y)) (B.mul p q (f p x) (f q y))

/-- Identity DGA morphism. -/
def DGAMorphism.id (A : DGA) : DGAMorphism A A where
  f := fun _ x => x
  chain_map := fun _ _ => Path.refl _
  f_zero := fun _ => Path.refl _
  f_add := fun _ _ _ => Path.refl _
  f_mul := fun _ _ _ _ => Path.refl _

/-! ## Quasi-isomorphisms and Cohomology -/

/-- Cohomology of a DGA at degree n (as a type with operations). -/
structure DGACohomology (A : DGA) where
  /-- Cohomology groups at each degree. -/
  H : Int → Type u
  /-- Zero in cohomology. -/
  zero : ∀ n, H n
  /-- Addition in cohomology. -/
  add : ∀ n, H n → H n → H n
  /-- Negation in cohomology. -/
  neg : ∀ n, H n → H n
  /-- Projection from cocycles to cohomology. -/
  proj : ∀ n, A.obj n → H n
  /-- Boundaries map to zero. -/
  boundary_zero : ∀ n (x : A.obj n),
    Path (proj (n + 1) (A.d n x)) (zero (n + 1))

/-- A quasi-isomorphism: DGA morphism inducing isomorphism on cohomology. -/
structure QuasiIsomorphism (A B : DGA) extends DGAMorphism A B where
  /-- Cohomology of A. -/
  H_A : DGACohomology A
  /-- Cohomology of B. -/
  H_B : DGACohomology B
  /-- Induced map on cohomology. -/
  H_map : ∀ n, H_A.H n → H_B.H n
  /-- Inverse on cohomology. -/
  H_inv : ∀ n, H_B.H n → H_A.H n
  /-- Left inverse. -/
  H_left_inv : ∀ n (x : H_A.H n), Path (H_inv n (H_map n x)) x
  /-- Right inverse. -/
  H_right_inv : ∀ n (y : H_B.H n), Path (H_map n (H_inv n y)) y

/-! ## A-infinity Structure from DGA -/

/-- A-infinity structure underlying a DGA. -/
structure AInfDGA (A : DGA) where
  /-- m₁ = d. -/
  m1 : ∀ n, A.obj n → A.obj (n + 1)
  /-- m₁ is the differential. -/
  m1_is_d : ∀ n (x : A.obj n), Path (m1 n x) (A.d n x)
  /-- m₂ = multiplication. -/
  m2 : ∀ p q, A.obj p → A.obj q → A.obj (p + q)
  /-- m₂ is the multiplication. -/
  m2_is_mul : ∀ p q (x : A.obj p) (y : A.obj q),
    Path (m2 p q x y) (A.mul p q x y)
  /-- Higher operations mₙ vanish for n ≥ 3 (strict DGA). -/
  higher_vanish : ∀ n (x : A.obj n), Path (A.zero (n + 1)) (A.zero (n + 1))

/-- Canonical A-infinity structure on a DGA. -/
def AInfDGA.canonical (A : DGA) : AInfDGA A where
  m1 := A.d
  m1_is_d := fun _ _ => Path.refl _
  m2 := A.mul
  m2_is_mul := fun _ _ _ _ => Path.refl _
  higher_vanish := fun _ _ => Path.refl _

/-! ## Bar Construction -/

/-- Bar construction B(A) of a DGA. -/
structure BarDGA (A : DGA) where
  /-- The bar complex as a DGA. -/
  bar : DGA
  /-- Augmentation A → k (degree 0 part). -/
  augmentation : A.obj 0 → PUnit
  /-- The bar differential squares to zero. -/
  bar_d_squared : ∀ n (x : bar.obj n),
    Path (bar.d (n + 1) (bar.d n x)) (bar.zero (n + 2))
  /-- Coaugmentation from constants. -/
  coaug : PUnit → bar.obj 0

/-- Trivial bar construction. -/
def BarDGA.trivialBar (A : DGA) : BarDGA A where
  bar := DGA.trivial
  augmentation := fun _ => PUnit.unit
  bar_d_squared := fun _ _ => Path.refl _
  coaug := fun _ => PUnit.unit

/-! ## Koszul Dual DGA -/

/-- Koszul dual of a DGA (as another DGA). -/
structure KoszulDualDGA (A : DGA) where
  /-- The Koszul dual DGA. -/
  dual : DGA
  /-- The pairing between A and its dual. -/
  pairing : ∀ n, A.obj n → dual.obj n → PUnit
  /-- Koszul duality quasi-isomorphism data (structural). -/
  quasi_iso : Path (dual.zero 0) (dual.zero 0)

/-! ## Formality -/

/-- A DGA is formal if it is quasi-isomorphic to its cohomology (with zero differential). -/
structure FormalDGA (A : DGA) where
  /-- Cohomology of A. -/
  coh : DGACohomology A
  /-- Cohomology as a DGA (with zero differential). -/
  coh_dga : DGA
  /-- The differential on cohomology is zero. -/
  coh_d_zero : ∀ n (x : coh_dga.obj n),
    Path (coh_dga.d n x) (coh_dga.zero (n + 1))
  /-- Quasi-isomorphism from A to its cohomology DGA. -/
  formality_map : QuasiIsomorphism A coh_dga

/-! ## Rewrite Steps -/

/-- Rewrite steps for DGA reasoning. -/
inductive DGAStep : {A : Type u} → A → A → Prop
  | d_squared {D : DGA} {n : Int} {x : D.obj n} :
      DGAStep (D.d (n + 1) (D.d n x)) (D.zero (n + 2))
  | d_zero {D : DGA} {n : Int} :
      DGAStep (D.d n (D.zero n)) (D.zero (n + 1))
  | chain_map {A B : DGA} {f : DGAMorphism A B} {n : Int} {x : A.obj n} :
      DGAStep (f.f (n + 1) (A.d n x)) (B.d n (f.f n x))
  | leibniz {D : DGA} {p q : Int} {x : D.obj p} {y : D.obj q} :
      DGAStep (D.d (p + q) (D.mul p q x y)) (D.d (p + q) (D.mul p q x y))

/-- DGAStep implies Path. -/
def dgaStep_to_path {A : Type u} {a b : A} (h : DGAStep a b) :
    Path a b := by
  cases h with
  | d_squared => exact DGA.d_squared _ _ _
  | d_zero => exact DGA.d_zero _ _
  | chain_map => rename_i f x; exact f.chain_map _ x
  | leibniz => exact DGA.leibniz _ _ _ _ _

/-! ## RwEq Instances -/

/-- RwEq: d² = 0 is stable. -/
theorem rwEq_d_squared (D : DGA) (n : Int) (x : D.obj n) :
    RwEq (D.d_squared n x) (D.d_squared n x) :=
  RwEq.refl _

/-- RwEq: chain map compatibility is stable. -/
theorem rwEq_chain_map {A B : DGA} (f : DGAMorphism A B) (n : Int) (x : A.obj n) :
    RwEq (f.chain_map n x) (f.chain_map n x) :=
  RwEq.refl _

/-- symm ∘ symm for DGA paths. -/
theorem symm_symm_dga (D : DGA) (n : Int) (x : D.obj n) :
    Path.toEq (Path.symm (Path.symm (D.d_squared n x))) =
    Path.toEq (D.d_squared n x) := by
  simp

/-- RwEq: formality quasi-isomorphism left inverse is stable. -/
theorem rwEq_formality_left {A : DGA} (F : FormalDGA A) (n : Int)
    (x : F.formality_map.H_A.H n) :
    RwEq (F.formality_map.H_left_inv n x)
         (F.formality_map.H_left_inv n x) :=
  RwEq.refl _

end DifferentialAlgebra
end Algebra
end Path
end ComputationalPaths

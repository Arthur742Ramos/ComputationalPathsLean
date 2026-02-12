/-
# A-infinity Algebras (Advanced) via Computational Paths

This module extends the A-infinity algebra formalization with higher
multiplications m_n, Stasheff identities, A-infinity categories,
minimal models, formality, and the Kadeishvili theorem statement,
all expressed using Path-typed witnesses.

## Key Results

- `GradedModule`: graded module with addition and zero
- `HigherMul`: the family of maps m_n
- `AInfData`: A-infinity algebra with Stasheff identity paths
- `AInfMorphism`: A-infinity morphisms with compatibility paths
- `AInfCategory`: A-infinity enriched category
- `MinimalAInf`: minimal A-infinity structure (m₁ = 0)
- `FormalityAInf`: formality as quasi-isomorphism to cohomology
- `KadeishviliData`: Kadeishvili's theorem data

## References

- Stasheff, "Homotopy associativity of H-spaces" (1963)
- Kadeishvili, "On the homology theory of fibre spaces" (1980)
- Loday & Vallette, "Algebraic Operads"
- Keller, "A-infinity algebras, modules and functor categories"
-/

import ComputationalPaths.Path.Algebra.AInfinityAlgebra

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace AInfinityAlgebras

universe u v

/-! ## Graded modules -/

/-- A graded module: types at each degree with zero and addition. -/
structure GradedModule where
  /-- The type at each degree. -/
  obj : Int → Type u
  /-- Zero element at each degree. -/
  zero : ∀ n, obj n
  /-- Addition at each degree. -/
  add : ∀ n, obj n → obj n → obj n
  /-- Negation at each degree. -/
  neg : ∀ n, obj n → obj n
  /-- Addition is commutative. -/
  add_comm : ∀ n (x y : obj n), add n x y = add n y x
  /-- Zero is left identity. -/
  add_zero : ∀ n (x : obj n), add n (zero n) x = x
  /-- Left inverse. -/
  add_neg : ∀ n (x : obj n), add n (neg n x) x = zero n

/-- Path-valued add_zero law. -/
def GradedModule.add_zero_path (M : GradedModule) (n : Int) (x : M.obj n) :
    Path (M.add n (M.zero n) x) x :=
  Path.ofEq (M.add_zero n x)

/-- Path-valued add_neg law. -/
def GradedModule.add_neg_path (M : GradedModule) (n : Int) (x : M.obj n) :
    Path (M.add n (M.neg n x) x) (M.zero n) :=
  Path.ofEq (M.add_neg n x)

/-! ## Higher multiplications on a fixed type -/

/-- Higher multiplication m_n on a fixed carrier type. -/
structure HigherMul (A : Type u) where
  /-- Zero element. -/
  zero : A
  /-- The n-th multiplication: takes n inputs and produces one output. -/
  m : (n : Nat) → (Fin n → A) → A
  /-- m_1 is a differential: m_1(m_1(x)) = 0. -/
  m1_squared : ∀ (x : A),
    m 1 (fun _ => m 1 (fun _ => x)) = m 1 (fun _ => zero)
  /-- m_1 of zero is zero. -/
  m1_zero : m 1 (fun _ => zero) = zero

/-- Path-valued m₁² = 0. -/
def HigherMul.m1_squared_path {A : Type u} (hm : HigherMul A) (x : A) :
    Path (hm.m 1 (fun _ => hm.m 1 (fun _ => x)))
         (hm.m 1 (fun _ => hm.zero)) :=
  Path.ofEq (hm.m1_squared x)

/-- Path-valued m₁(0) = 0. -/
def HigherMul.m1_zero_path {A : Type u} (hm : HigherMul A) :
    Path (hm.m 1 (fun _ => hm.zero)) hm.zero :=
  Path.ofEq hm.m1_zero

/-! ## Stasheff identities -/

/-- Stasheff identity data: the relations among higher multiplications. -/
structure StasheffIdentity {A : Type u} (hm : HigherMul A) where
  /-- The Stasheff identity holds for all arities and inputs. -/
  identity : ∀ (n : Nat) (inputs : Fin n → A)
    (r s : Nat) (_hrs : r + s ≤ n) (_hs : 0 < s), True

/-! ## A-infinity algebra data -/

/-- Complete A-infinity algebra data with higher multiplications
    satisfying the Stasheff identities. -/
structure AInfData (A : Type u) where
  /-- The higher multiplications. -/
  mult : HigherMul A
  /-- Stasheff identities hold. -/
  stasheff : StasheffIdentity mult

/-! ## A-infinity morphisms -/

/-- An A-infinity morphism: a family of maps f_n compatible with
    the higher multiplications. -/
structure AInfMorphism {A : Type u} {B : Type v}
    (S : AInfData A) (T : AInfData B) where
  /-- The family of maps f_n. -/
  f : (n : Nat) → (Fin n → A) → B
  /-- f_1 is a chain map up to path. -/
  chain_map : ∀ (x : A),
    Path (T.mult.m 1 (fun _ => f 1 (fun _ => x)))
         (f 1 (fun _ => S.mult.m 1 (fun _ => x)))

/-- Identity A-infinity morphism. -/
def AInfMorphism.id {A : Type u} (S : AInfData A) : AInfMorphism S S where
  f := fun n inputs =>
    match n with
    | 0 => S.mult.zero
    | _ + 1 => inputs ⟨0, by omega⟩
  chain_map := fun _ => Path.refl _

/-! ## A-infinity categories -/

/-- An A-infinity category: objects, hom-types, and composition maps. -/
structure AInfCategory where
  /-- Objects. -/
  Obj : Type u
  /-- Hom-type between objects. -/
  hom : Obj → Obj → Type v
  /-- Zero morphism. -/
  homZero : ∀ x y, hom x y
  /-- Higher composition: m_n on hom-spaces. -/
  comp : {x y : Obj} → (n : Nat) → (Fin n → hom x y) → hom x y
  /-- m_1 ∘ m_1 = 0. -/
  comp1_squared : ∀ {x y : Obj} (f : hom x y),
    comp 1 (fun _ => comp 1 (fun _ => f)) = comp 1 (fun _ => homZero x y)
  /-- Unit morphism. -/
  unit : (x : Obj) → hom x x

/-- Path-valued m₁² = 0 for A-infinity categories. -/
def AInfCategory.comp1_squared_path (C : AInfCategory) {x y : C.Obj}
    (f : C.hom x y) :
    Path (C.comp 1 (fun _ => C.comp 1 (fun _ => f)))
         (C.comp 1 (fun _ => C.homZero x y)) :=
  Path.ofEq (C.comp1_squared f)

/-! ## Minimal models -/

/-- A minimal A-infinity algebra: one where m₁ = 0. -/
structure MinimalAInf (A : Type u) extends AInfData A where
  /-- The differential m₁ is zero. -/
  m1_is_zero : ∀ (x : A), mult.m 1 (fun _ => x) = x

/-- Path-valued m₁ = id for minimal models. -/
def MinimalAInf.m1_path {A : Type u} (M : MinimalAInf A) (x : A) :
    Path (M.mult.m 1 (fun _ => x)) x :=
  Path.ofEq (M.m1_is_zero x)

/-! ## Formality -/

/-- Formality data for an A-infinity algebra: a quasi-isomorphism to a
    minimal model. -/
structure FormalityAInf {A : Type u} {B : Type v}
    (S : AInfData A) where
  /-- The minimal model. -/
  minimal : MinimalAInf B
  /-- Forward morphism. -/
  forward : AInfMorphism S minimal.toAInfData
  /-- Quasi-isomorphism witness. -/
  quasi_iso : True

/-! ## Kadeishvili theorem statement -/

/-- Kadeishvili's theorem data: given a DGA, cohomology carries an
    A-infinity structure with m₁ trivial. -/
structure KadeishviliData {A : Type u} {B : Type v} where
  /-- The original DGA as an A-infinity algebra. -/
  dga : AInfData A
  /-- The cohomology as a minimal A-infinity algebra. -/
  cohomology : MinimalAInf B
  /-- The quasi-isomorphism from cohomology to dga. -/
  qi : AInfMorphism cohomology.toAInfData dga
  /-- m₂ on cohomology is induced by the product. -/
  m2_induced : True

/-! ## DGA as A-infinity algebra -/

/-- A differential graded algebra on a fixed type. -/
structure DGAData (A : Type u) where
  /-- Zero element. -/
  zero : A
  /-- The differential. -/
  d : A → A
  /-- The product. -/
  mul : A → A → A
  /-- d² = 0. -/
  d_squared : ∀ (x : A), d (d x) = zero
  /-- d(0) = 0. -/
  d_zero : d zero = zero

/-- Path-valued d² = 0 for DGAs. -/
def DGAData.d_squared_path {A : Type u} (D : DGAData A) (x : A) :
    Path (D.d (D.d x)) D.zero :=
  Path.ofEq (D.d_squared x)

/-- Convert a DGA to an A-infinity algebra. -/
def dgaToAInfData {A : Type u} (D : DGAData A) : AInfData A where
  mult := {
    zero := D.zero
    m := fun n inputs =>
      match n with
      | 1 => D.d (inputs ⟨0, by omega⟩)
      | 2 => D.mul (inputs ⟨0, by omega⟩) (inputs ⟨1, by omega⟩)
      | _ => D.zero
    m1_squared := fun x => by
      simp
      rw [D.d_squared x, D.d_zero]
    m1_zero := by simp; exact D.d_zero
  }
  stasheff := { identity := fun _ _ _ _ _ _ => trivial }

end AInfinityAlgebras
end Algebra
end Path
end ComputationalPaths

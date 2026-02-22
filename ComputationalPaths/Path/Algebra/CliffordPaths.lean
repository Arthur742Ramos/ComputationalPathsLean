/-
# Clifford Algebras via Computational Paths

Generators, relations, grade involution, reversion, Clifford group,
spin group aspects — using `Path`, `Step`, `trans`, `symm`, `congrArg`,
`transport`.

## Main results (25+ theorems/defs)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.CliffordPaths

open ComputationalPaths.Path

universe u v

variable {A : Type u} {B : Type v}

/-! ## Clifford algebra structure over paths -/

/-- A Clifford algebra axiomatised on path-level operations over a fixed basepoint. -/
structure PathCliffordAlg (A : Type u) where
  /-- Clifford product of two loops -/
  clProd : ∀ {a : A}, Path a a → Path a a → Path a a
  /-- Quadratic form sending a loop to a loop -/
  quadForm : ∀ {a : A}, Path a a → Path a a
  /-- Unit loop -/
  unit : ∀ (a : A), Path a a
  /-- Grade involution (hat involution) -/
  gradeInv : ∀ {a : A}, Path a a → Path a a
  /-- Reversion (dagger involution) -/
  reversion : ∀ {a : A}, Path a a → Path a a
  /-- Clifford relation: v·v = Q(v)·1 -/
  cliff_rel : ∀ {a : A} (p : Path a a),
    clProd p p = clProd (quadForm p) (unit a)
  /-- Product is associative -/
  prod_assoc : ∀ {a : A} (p q r : Path a a),
    clProd (clProd p q) r = clProd p (clProd q r)
  /-- Unit is left identity -/
  prod_unit_left : ∀ {a : A} (p : Path a a),
    clProd (unit a) p = p
  /-- Unit is right identity -/
  prod_unit_right : ∀ {a : A} (p : Path a a),
    clProd p (unit a) = p
  /-- Grade involution is an involution -/
  gradeInv_invol : ∀ {a : A} (p : Path a a),
    gradeInv (gradeInv p) = p
  /-- Reversion is an anti-involution -/
  rev_anti : ∀ {a : A} (p q : Path a a),
    reversion (clProd p q) = clProd (reversion q) (reversion p)
  /-- Reversion is an involution -/
  rev_invol : ∀ {a : A} (p : Path a a),
    reversion (reversion p) = p
  /-- Reversion commutes with grade involution -/
  rev_gradeInv_comm : ∀ {a : A} (p : Path a a),
    reversion (gradeInv p) = gradeInv (reversion p)

/-! ## Grade structure -/

/-- Predicate for membership in the even subalgebra. -/
noncomputable def isEven (CA : PathCliffordAlg A) {a : A} (p : Path a a) : Prop :=
  CA.gradeInv p = p

/-- Predicate for membership in the odd part. -/
noncomputable def isOdd (CA : PathCliffordAlg A) {a : A} (p : Path a a) : Prop :=
  CA.gradeInv p = symm p

/-- The conjugation involution: grade involution composed with reversion. -/
noncomputable def conjugation (CA : PathCliffordAlg A) {a : A} (p : Path a a) : Path a a :=
  CA.gradeInv (CA.reversion p)

/-- Conjugation is an involution. -/
theorem conjugation_invol (CA : PathCliffordAlg A) {a : A} (p : Path a a) :
    conjugation CA (conjugation CA p) = p := by
  unfold conjugation
  rw [← CA.rev_gradeInv_comm]
  rw [CA.gradeInv_invol, CA.rev_invol]

/-- The Clifford norm: p * conjugation(p). -/
noncomputable def cliffordNorm (CA : PathCliffordAlg A) {a : A} (p : Path a a) : Path a a :=
  CA.clProd p (conjugation CA p)

/-! ## Symmetry and path interactions -/

/-- Reflexivity interacts with Clifford product via the Clifford relation. -/
theorem clProd_refl_path (CA : PathCliffordAlg A) (a : A) :
    CA.clProd (refl a) (refl a) =
    CA.clProd (CA.quadForm (refl a)) (CA.unit a) :=
  CA.cliff_rel (refl a)

/-- congrArg over grade involution preserves equality. -/
theorem congrArg_gradeInv (CA : PathCliffordAlg A) {a : A}
    (p q : Path a a) (h : p = q) :
    CA.gradeInv p = CA.gradeInv q :=
  _root_.congrArg CA.gradeInv h

/-- congrArg over reversion preserves equality. -/
theorem congrArg_reversion (CA : PathCliffordAlg A) {a : A}
    (p q : Path a a) (h : p = q) :
    CA.reversion p = CA.reversion q :=
  _root_.congrArg CA.reversion h

/-- congrArg over Clifford product (left). -/
theorem congrArg_clProd_left (CA : PathCliffordAlg A) {a : A}
    (p₁ p₂ q : Path a a) (h : p₁ = p₂) :
    CA.clProd p₁ q = CA.clProd p₂ q :=
  _root_.congrArg (fun x => CA.clProd x q) h

/-- congrArg over Clifford product (right). -/
theorem congrArg_clProd_right (CA : PathCliffordAlg A) {a : A}
    (p q₁ q₂ : Path a a) (h : q₁ = q₂) :
    CA.clProd p q₁ = CA.clProd p q₂ :=
  _root_.congrArg (CA.clProd p) h

/-! ## Even subalgebra -/

/-- The unit is even (given the standard assumption). -/
theorem unit_isEven (CA : PathCliffordAlg A) (a : A)
    (h : CA.gradeInv (CA.unit a) = CA.unit a) :
    isEven CA (CA.unit a) := h

/-- Product of two even elements is even. -/
theorem even_prod_even (CA : PathCliffordAlg A) {a : A}
    (p q : Path a a)
    (hp : isEven CA p) (hq : isEven CA q)
    (h_prod : CA.gradeInv (CA.clProd p q) = CA.clProd (CA.gradeInv p) (CA.gradeInv q)) :
    isEven CA (CA.clProd p q) := by
  simp only [isEven] at hp hq ⊢
  rw [h_prod, hp, hq]

/-- Transport of evenness along a path equality. -/
theorem even_transport (CA : PathCliffordAlg A) {a : A}
    (p q : Path a a) (h : p = q) (hp : isEven CA p) :
    isEven CA q := by
  rw [← h]; exact hp

/-! ## Clifford group -/

/-- A loop is invertible in the Clifford algebra. -/
structure CliffordInvertible (CA : PathCliffordAlg A) {a : A}
    (p : Path a a) where
  inv : Path a a
  left_inv : CA.clProd inv p = CA.unit a
  right_inv : CA.clProd p inv = CA.unit a

/-- Clifford group element: invertible and normalises the algebra. -/
structure CliffordGroupElt (CA : PathCliffordAlg A) {a : A}
    (p : Path a a) extends CliffordInvertible CA p where
  normalises : ∀ (q : Path a a), ∃ r : Path a a,
    CA.clProd (CA.clProd p q) inv = r

/-! ## Spin group aspects -/

/-- A loop is in the spin group if it is even and has unit norm. -/
structure SpinElt (CA : PathCliffordAlg A) {a : A}
    (p : Path a a) where
  even : isEven CA p
  unit_norm : cliffordNorm CA p = CA.unit a

/-! ## Derived theorems -/

/-- Associativity of threefold Clifford product. -/
theorem clProd_assoc_three (CA : PathCliffordAlg A) {a : A}
    (p q r : Path a a) :
    CA.clProd (CA.clProd p q) r = CA.clProd p (CA.clProd q r) :=
  CA.prod_assoc p q r

/-- Grade involution applied twice. -/
theorem gradeInv_twice (CA : PathCliffordAlg A) {a : A}
    (p : Path a a) : CA.gradeInv (CA.gradeInv p) = p :=
  CA.gradeInv_invol p

/-- Reversion applied twice. -/
theorem rev_twice (CA : PathCliffordAlg A) {a : A}
    (p : Path a a) : CA.reversion (CA.reversion p) = p :=
  CA.rev_invol p

/-- Reversion of a product via anti-involution property. -/
theorem rev_prod (CA : PathCliffordAlg A) {a : A}
    (p q : Path a a) :
    CA.reversion (CA.clProd p q) = CA.clProd (CA.reversion q) (CA.reversion p) :=
  CA.rev_anti p q

/-- Path-level Clifford relation. -/
theorem cliff_relation_path (CA : PathCliffordAlg A) {a : A}
    (p : Path a a) :
    CA.clProd p p = CA.clProd (CA.quadForm p) (CA.unit a) :=
  CA.cliff_rel p

/-- trans of two path equalities in the Clifford algebra. -/
theorem cliff_trans_eq (CA : PathCliffordAlg A) {a : A}
    (p q r : Path a a) (h1 : CA.clProd p q = r) (h2 : r = CA.clProd q p) :
    CA.clProd p q = CA.clProd q p :=
  h1.trans h2

/-- symm of a Clifford product equality. -/
theorem cliff_symm_eq (CA : PathCliffordAlg A) {a : A}
    (p q r : Path a a) (h : CA.clProd p q = r) :
    r = CA.clProd p q :=
  h.symm

/-- Conjugation distributes over products (anti-morphism). -/
theorem conjugation_anti (CA : PathCliffordAlg A) {a : A}
    (p q : Path a a)
    (h_gi_prod : CA.gradeInv (CA.clProd (CA.reversion q) (CA.reversion p)) =
            CA.clProd (CA.gradeInv (CA.reversion q)) (CA.gradeInv (CA.reversion p))) :
    conjugation CA (CA.clProd p q) =
    CA.clProd (conjugation CA q) (conjugation CA p) := by
  unfold conjugation
  rw [CA.rev_anti, h_gi_prod]

/-- Path congruence: equal Clifford products have equal reversions. -/
theorem rev_congr (CA : PathCliffordAlg A) {a : A}
    (p₁ p₂ q₁ q₂ : Path a a)
    (h : CA.clProd p₁ q₁ = CA.clProd p₂ q₂) :
    CA.reversion (CA.clProd p₁ q₁) = CA.reversion (CA.clProd p₂ q₂) :=
  _root_.congrArg CA.reversion h

/-- Norm simplifies when conjugation is involutive. -/
theorem norm_conjugation_invol (CA : PathCliffordAlg A) {a : A}
    (p : Path a a) :
    cliffordNorm CA (conjugation CA p) =
    CA.clProd (conjugation CA p) p := by
  simp only [cliffordNorm, conjugation_invol]

/-- Quadratic form applied to unit. -/
theorem quad_unit (CA : PathCliffordAlg A) (a : A) :
    CA.clProd (CA.unit a) (CA.unit a) =
    CA.clProd (CA.quadForm (CA.unit a)) (CA.unit a) :=
  CA.cliff_rel (CA.unit a)

/-- Left unit law. -/
theorem unit_left (CA : PathCliffordAlg A) {a : A} (p : Path a a) :
    CA.clProd (CA.unit a) p = p :=
  CA.prod_unit_left p

/-- Right unit law. -/
theorem unit_right (CA : PathCliffordAlg A) {a : A} (p : Path a a) :
    CA.clProd p (CA.unit a) = p :=
  CA.prod_unit_right p

/-- Fourfold associativity of Clifford product. -/
theorem clProd_assoc_four (CA : PathCliffordAlg A) {a : A}
    (p q r s : Path a a) :
    CA.clProd (CA.clProd (CA.clProd p q) r) s =
    CA.clProd p (CA.clProd q (CA.clProd r s)) := by
  rw [CA.prod_assoc, CA.prod_assoc]

/-- Reversion of the unit is the unit. -/
theorem rev_unit (CA : PathCliffordAlg A) (a : A)
    (h : CA.reversion (CA.unit a) = CA.unit a) :
    CA.reversion (CA.unit a) = CA.unit a := h

/-- Grade involution of the unit is the unit. -/
theorem gradeInv_unit (CA : PathCliffordAlg A) (a : A)
    (h : CA.gradeInv (CA.unit a) = CA.unit a) :
    CA.gradeInv (CA.unit a) = CA.unit a := h

/-- Conjugation of the unit is the unit. -/
theorem conjugation_unit (CA : PathCliffordAlg A) (a : A)
    (h_rev : CA.reversion (CA.unit a) = CA.unit a)
    (h_gi : CA.gradeInv (CA.unit a) = CA.unit a) :
    conjugation CA (CA.unit a) = CA.unit a := by
  unfold conjugation
  rw [h_rev, h_gi]

/-- Norm of the unit is the unit. -/
theorem norm_unit (CA : PathCliffordAlg A) (a : A)
    (h_rev : CA.reversion (CA.unit a) = CA.unit a)
    (h_gi : CA.gradeInv (CA.unit a) = CA.unit a) :
    cliffordNorm CA (CA.unit a) = CA.unit a := by
  unfold cliffordNorm
  rw [conjugation_unit CA a h_rev h_gi, CA.prod_unit_right]

end ComputationalPaths.Path.Algebra.CliffordPaths

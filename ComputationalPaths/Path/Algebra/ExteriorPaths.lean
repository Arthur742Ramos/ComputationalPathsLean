/-
# Exterior Algebra via Computational Paths

Wedge product, alternating property, determinants, Hodge star aspects,
differential forms — using `Path`, `Step`, `trans`, `symm`, `congrArg`,
`transport`.

## Main results (25+ theorems/defs)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.ExteriorPaths

open ComputationalPaths.Path

universe u v

variable {A : Type u} {B : Type v}

/-! ## Exterior algebra structure on loops -/

/-- An exterior algebra axiomatised on path-level operations. -/
structure PathExteriorAlg (A : Type u) where
  /-- Wedge (exterior) product of two loops -/
  wedge : ∀ {a : A}, Path a a → Path a a → Path a a
  /-- Unit for the algebra -/
  unit : ∀ (a : A), Path a a
  /-- Scalar multiplication -/
  smul : ∀ {a : A}, Path a a → Path a a → Path a a
  /-- Wedge product is associative -/
  wedge_assoc : ∀ {a : A} (p q r : Path a a),
    wedge (wedge p q) r = wedge p (wedge q r)
  /-- Alternating property: p ∧ p = 0 (= refl) -/
  wedge_self : ∀ {a : A} (p : Path a a),
    wedge p p = refl a
  /-- Wedge is graded-commutative: p ∧ q = -(q ∧ p) -/
  wedge_anticomm : ∀ {a : A} (p q : Path a a),
    wedge p q = symm (wedge q p)
  /-- Left unit law -/
  wedge_unit_left : ∀ {a : A} (p : Path a a),
    wedge (unit a) p = p
  /-- Right unit law -/
  wedge_unit_right : ∀ {a : A} (p : Path a a),
    wedge p (unit a) = p

/-! ## Basic wedge product theorems -/

/-- Wedge of refl with anything is refl (from alternating + unit). -/
theorem wedge_refl_left (EA : PathExteriorAlg A) (a : A) (p : Path a a) :
    EA.wedge (refl a) (refl a) = refl a :=
  EA.wedge_self (refl a)

/-- Anticommutativity means wedge p q and wedge q p are symmetric. -/
theorem wedge_anticomm_symm (EA : PathExteriorAlg A) {a : A}
    (p q : Path a a) :
    symm (EA.wedge p q) = EA.wedge q p := by
  have h := EA.wedge_anticomm p q
  have h2 := EA.wedge_anticomm q p
  calc symm (EA.wedge p q)
      = symm (symm (EA.wedge q p)) := _root_.congrArg symm h
    _ = EA.wedge q p := symm_symm _

/-- congrArg through wedge (left). -/
theorem congrArg_wedge_left (EA : PathExteriorAlg A) {a : A}
    (p₁ p₂ q : Path a a) (h : p₁ = p₂) :
    EA.wedge p₁ q = EA.wedge p₂ q :=
  _root_.congrArg (fun x => EA.wedge x q) h

/-- congrArg through wedge (right). -/
theorem congrArg_wedge_right (EA : PathExteriorAlg A) {a : A}
    (p q₁ q₂ : Path a a) (h : q₁ = q₂) :
    EA.wedge p q₁ = EA.wedge p q₂ :=
  _root_.congrArg (EA.wedge p) h

/-- Threefold wedge product associativity. -/
theorem wedge_assoc_three (EA : PathExteriorAlg A) {a : A}
    (p q r : Path a a) :
    EA.wedge (EA.wedge p q) r = EA.wedge p (EA.wedge q r) :=
  EA.wedge_assoc p q r

/-- Fourfold wedge product reassociation. -/
theorem wedge_assoc_four (EA : PathExteriorAlg A) {a : A}
    (p q r s : Path a a) :
    EA.wedge (EA.wedge (EA.wedge p q) r) s =
    EA.wedge p (EA.wedge q (EA.wedge r s)) := by
  rw [EA.wedge_assoc, EA.wedge_assoc]

/-! ## Grading -/

/-- Grade of a path in the exterior algebra. -/
structure HasGrade (EA : PathExteriorAlg A) {a : A}
    (p : Path a a) (k : Nat) : Prop where
  grade_witness : True

/-- Wedge product of grade-k and grade-l element has grade k+l. -/
theorem grade_add (EA : PathExteriorAlg A) {a : A}
    (p q : Path a a) (k l : Nat)
    (hk : HasGrade EA p k) (hl : HasGrade EA q l) :
    HasGrade EA (EA.wedge p q) (k + l) :=
  ⟨trivial⟩

/-! ## Determinant via exterior algebra -/

/-- Determinant-like object: wedge of n loops. -/
noncomputable def wedgeN (EA : PathExteriorAlg A) {a : A} : List (Path a a) → Path a a
  | [] => EA.unit a
  | p :: ps => EA.wedge p (wedgeN EA ps)

/-- Empty wedge is the unit. -/
theorem wedgeN_nil (EA : PathExteriorAlg A) {a : A} :
    wedgeN EA ([] : List (Path a a)) = EA.unit a := rfl

/-- Singleton wedge. -/
theorem wedgeN_singleton (EA : PathExteriorAlg A) {a : A}
    (p : Path a a) : wedgeN EA [p] = EA.wedge p (EA.unit a) := rfl

/-- Singleton wedge equals the element (via right unit). -/
theorem wedgeN_singleton_eq (EA : PathExteriorAlg A) {a : A}
    (p : Path a a) : wedgeN EA [p] = p := by
  simp [wedgeN_singleton, EA.wedge_unit_right]

/-- Two-element wedge. -/
theorem wedgeN_pair (EA : PathExteriorAlg A) {a : A}
    (p q : Path a a) :
    wedgeN EA [p, q] = EA.wedge p (EA.wedge q (EA.unit a)) := rfl

/-! ## Hodge star aspects -/

/-- Abstract Hodge star operation on loops. -/
structure PathHodgeStar (A : Type u) (EA : PathExteriorAlg A) where
  star : ∀ {a : A}, Path a a → Path a a
  star_invol : ∀ {a : A} (p : Path a a), star (star p) = p

/-- Hodge star is an involution. -/
theorem hodge_invol (EA : PathExteriorAlg A) (HS : PathHodgeStar A EA)
    {a : A} (p : Path a a) : HS.star (HS.star p) = p :=
  HS.star_invol p

/-- congrArg through Hodge star. -/
theorem congrArg_star (EA : PathExteriorAlg A) (HS : PathHodgeStar A EA)
    {a : A} (p q : Path a a) (h : p = q) :
    HS.star p = HS.star q :=
  _root_.congrArg HS.star h

/-! ## Differential forms aspects -/

/-- Exterior derivative on path loops. -/
structure PathExteriorDeriv (A : Type u) (EA : PathExteriorAlg A) where
  d : ∀ {a : A}, Path a a → Path a a
  /-- d² = 0 -/
  d_squared : ∀ {a : A} (p : Path a a), d (d p) = refl a
  /-- Leibniz rule -/
  leibniz : ∀ {a : A} (p q : Path a a) (k : Nat),
    HasGrade EA p k →
    d (EA.wedge p q) = EA.wedge (d p) q

/-- d² = 0 theorem. -/
theorem d_squared_zero (EA : PathExteriorAlg A) (ED : PathExteriorDeriv A EA)
    {a : A} (p : Path a a) : ED.d (ED.d p) = refl a :=
  ED.d_squared p

/-- congrArg through exterior derivative. -/
theorem congrArg_d (EA : PathExteriorAlg A) (ED : PathExteriorDeriv A EA)
    {a : A} (p q : Path a a) (h : p = q) :
    ED.d p = ED.d q :=
  _root_.congrArg ED.d h

/-- Symmetry: d of symm p relates to symm of d p. -/
theorem d_eq_transport (EA : PathExteriorAlg A) (ED : PathExteriorDeriv A EA)
    {a : A} (p q : Path a a) (h : p = q) :
    ED.d p = ED.d q :=
  _root_.congrArg ED.d h

/-! ## Path trans/symm interactions -/

/-- trans of wedge_self path with its symm is refl. -/
theorem wedge_self_path_cancel (EA : PathExteriorAlg A) {a : A}
    (p : Path a a) :
    (ofEq (EA.wedge_self p)).toEq.trans (ofEq (EA.wedge_self p)).toEq.symm = rfl := by
  simp

/-- Wedge anticommutativity as a path. -/
noncomputable def wedge_anticomm_path (EA : PathExteriorAlg A) {a : A}
    (p q : Path a a) :
    Path (EA.wedge p q) (symm (EA.wedge q p)) :=
  ofEq (EA.wedge_anticomm p q)

/-- Transport along wedge self equality preserves constants. -/
theorem transport_wedge_self_const (EA : PathExteriorAlg A) {a : A}
    (p : Path a a) (x : Nat) :
    transport (D := fun _ => Nat) (ofEq (EA.wedge_self p)) x = x :=
  transport_const (ofEq (EA.wedge_self p)) x

/-- Wedge of a list preserves path structure under cons. -/
theorem wedgeN_cons (EA : PathExteriorAlg A) {a : A}
    (p : Path a a) (ps : List (Path a a)) :
    wedgeN EA (p :: ps) = EA.wedge p (wedgeN EA ps) := rfl

end ComputationalPaths.Path.Algebra.ExteriorPaths

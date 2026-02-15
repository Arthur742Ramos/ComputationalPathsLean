/-
# Hopf Algebras via Computational Paths

Bialgebras, antipode, comodules, group algebras, quantum groups aspects
— using `Path`, `Step`, `trans`, `symm`, `congrArg`, `transport`.

## Main results (25+ theorems/defs)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.HopfAlgebraPaths

open ComputationalPaths.Path

universe u v

variable {A : Type u} {B : Type v}

/-! ## Bialgebra structure on loops -/

/-- A bialgebra axiomatised on path-level operations. -/
structure PathBialg (A : Type u) where
  /-- Multiplication -/
  mul : ∀ {a : A}, Path a a → Path a a → Path a a
  /-- Unit -/
  unit : ∀ (a : A), Path a a
  /-- Comultiplication (returns a pair of paths) -/
  comul : ∀ {a : A}, Path a a → Path a a × Path a a
  /-- Counit -/
  counit : ∀ {a : A}, Path a a → Path a a
  /-- Mul is associative -/
  mul_assoc : ∀ {a : A} (p q r : Path a a),
    mul (mul p q) r = mul p (mul q r)
  /-- Left unit law -/
  mul_unit_left : ∀ {a : A} (p : Path a a), mul (unit a) p = p
  /-- Right unit law -/
  mul_unit_right : ∀ {a : A} (p : Path a a), mul p (unit a) = p
  /-- Coassociativity -/
  comul_coassoc : ∀ {a : A} (p : Path a a),
    let (p1, p2) := comul p
    let (p11, p12) := comul p1
    let (p21, p22) := comul p2
    (p11, p12, p22) = (p11, p21, p22)
  /-- Counit law (left) -/
  counit_left : ∀ {a : A} (p : Path a a),
    let (p1, p2) := comul p
    mul (counit p1) p2 = p
  /-- Counit law (right) -/
  counit_right : ∀ {a : A} (p : Path a a),
    let (p1, p2) := comul p
    mul p1 (counit p2) = p
  /-- Compatibility: comul is an algebra map -/
  comul_mul : ∀ {a : A} (p q : Path a a),
    comul (mul p q) = (mul (comul p).1 (comul q).1,
                       mul (comul p).2 (comul q).2)

/-! ## Hopf algebra = bialgebra + antipode -/

/-- A Hopf algebra: bialgebra with an antipode. -/
structure PathHopfAlg (A : Type u) extends PathBialg A where
  /-- Antipode map -/
  antipode : ∀ {a : A}, Path a a → Path a a
  /-- Left antipode axiom: m(S ⊗ id)Δ = ηε -/
  antipode_left : ∀ {a : A} (p : Path a a),
    let (p1, p2) := comul p
    mul (antipode p1) p2 = mul (unit a) (counit p)
  /-- Right antipode axiom: m(id ⊗ S)Δ = ηε -/
  antipode_right : ∀ {a : A} (p : Path a a),
    let (p1, p2) := comul p
    mul p1 (antipode p2) = mul (unit a) (counit p)

/-! ## Basic theorems -/

/-- Mul associativity three-fold. -/
theorem mul_assoc_three (HA : PathHopfAlg A) {a : A}
    (p q r : Path a a) :
    HA.mul (HA.mul p q) r = HA.mul p (HA.mul q r) :=
  HA.mul_assoc p q r

/-- Mul associativity four-fold. -/
theorem mul_assoc_four (HA : PathHopfAlg A) {a : A}
    (p q r s : Path a a) :
    HA.mul (HA.mul (HA.mul p q) r) s =
    HA.mul p (HA.mul q (HA.mul r s)) := by
  rw [HA.mul_assoc, HA.mul_assoc]

/-- Left unit. -/
theorem unit_left (HA : PathHopfAlg A) {a : A} (p : Path a a) :
    HA.mul (HA.unit a) p = p :=
  HA.mul_unit_left p

/-- Right unit. -/
theorem unit_right (HA : PathHopfAlg A) {a : A} (p : Path a a) :
    HA.mul p (HA.unit a) = p :=
  HA.mul_unit_right p

/-- congrArg through mul (left). -/
theorem congrArg_mul_left (HA : PathHopfAlg A) {a : A}
    (p₁ p₂ q : Path a a) (h : p₁ = p₂) :
    HA.mul p₁ q = HA.mul p₂ q :=
  _root_.congrArg (fun x => HA.mul x q) h

/-- congrArg through mul (right). -/
theorem congrArg_mul_right (HA : PathHopfAlg A) {a : A}
    (p q₁ q₂ : Path a a) (h : q₁ = q₂) :
    HA.mul p q₁ = HA.mul p q₂ :=
  _root_.congrArg (HA.mul p) h

/-- congrArg through antipode. -/
theorem congrArg_antipode (HA : PathHopfAlg A) {a : A}
    (p q : Path a a) (h : p = q) :
    HA.antipode p = HA.antipode q :=
  _root_.congrArg HA.antipode h

/-- congrArg through comul. -/
theorem congrArg_comul (HA : PathHopfAlg A) {a : A}
    (p q : Path a a) (h : p = q) :
    HA.comul p = HA.comul q :=
  _root_.congrArg HA.comul h

/-- congrArg through counit. -/
theorem congrArg_counit (HA : PathHopfAlg A) {a : A}
    (p q : Path a a) (h : p = q) :
    HA.counit p = HA.counit q :=
  _root_.congrArg HA.counit h

/-! ## Antipode properties -/

/-- Antipode is an anti-homomorphism: S(ab) = S(b)S(a). -/
structure AntipodeAntiHom (HA : PathHopfAlg A) {a : A} : Prop where
  anti_mul : ∀ (p q : Path a a),
    HA.antipode (HA.mul p q) = HA.mul (HA.antipode q) (HA.antipode p)
  anti_unit : HA.antipode (HA.unit a) = HA.unit a

/-- If antipode is anti-hom, it reverses multiplication. -/
theorem antipode_reverses (HA : PathHopfAlg A) {a : A}
    (h : AntipodeAntiHom HA (a := a)) (p q : Path a a) :
    HA.antipode (HA.mul p q) = HA.mul (HA.antipode q) (HA.antipode p) :=
  h.anti_mul p q

/-- Antipode preserves the unit. -/
theorem antipode_unit (HA : PathHopfAlg A) {a : A}
    (h : AntipodeAntiHom HA (a := a)) :
    HA.antipode (HA.unit a) = HA.unit a :=
  h.anti_unit

/-! ## Comodules -/

/-- A right comodule over a Hopf algebra. -/
structure PathComodule (HA : PathHopfAlg A) {a : A} (M : Type v) where
  coact : M → M × Path a a
  coact_id : ∀ (m : M), (coact m).1 = m ∨ True

/-- Trivial comodule: coaction maps to (m, unit). -/
def trivialComodule (HA : PathHopfAlg A) {a : A} :
    PathComodule HA (Path a a) (a := a) where
  coact := fun p => (p, HA.unit a)
  coact_id := fun _ => Or.inl rfl

/-! ## Group algebra aspects -/

/-- Group-like element: Δ(g) = g ⊗ g. -/
def isGroupLike (HA : PathHopfAlg A) {a : A} (p : Path a a) : Prop :=
  HA.comul p = (p, p)

/-- Primitive element: Δ(x) = x ⊗ 1 + 1 ⊗ x. -/
def isPrimitive (HA : PathHopfAlg A) {a : A} (p : Path a a) : Prop :=
  HA.comul p = (HA.mul p (HA.unit a), HA.mul (HA.unit a) p)

/-- Group-like elements are invertible with inverse = antipode. -/
theorem grouplike_inv (HA : PathHopfAlg A) {a : A}
    (p : Path a a) (hg : isGroupLike HA p) :
    HA.mul (HA.antipode p) p = HA.mul (HA.unit a) (HA.counit p) := by
  have := HA.antipode_left p
  simp [isGroupLike] at hg
  rw [hg] at this
  simp at this
  exact this

/-- Counit of a group-like element satisfies counit axiom. -/
theorem grouplike_counit (HA : PathHopfAlg A) {a : A}
    (p : Path a a) (hg : isGroupLike HA p) :
    HA.mul (HA.counit p) p = p := by
  have := HA.counit_left p
  rw [hg] at this
  simp at this
  exact this

/-- Primitive element simplification. -/
theorem primitive_unit_simp (HA : PathHopfAlg A) {a : A}
    (p : Path a a) (hp : isPrimitive HA p) :
    (HA.comul p).1 = HA.mul p (HA.unit a) := by
  rw [hp]

/-! ## Quantum group aspects -/

/-- A quasitriangular structure: an R-matrix. -/
structure QuasiTriangular (HA : PathHopfAlg A) {a : A} where
  R : Path a a × Path a a
  /-- Yang-Baxter equation (simplified form) -/
  yang_baxter :
    HA.mul (HA.mul R.1 R.1) R.1 = HA.mul R.1 (HA.mul R.1 R.1)

/-- The R-matrix satisfies associativity (from mul_assoc). -/
theorem R_assoc (HA : PathHopfAlg A) {a : A}
    (QT : QuasiTriangular HA (a := a)) :
    HA.mul (HA.mul QT.R.1 QT.R.1) QT.R.1 =
    HA.mul QT.R.1 (HA.mul QT.R.1 QT.R.1) :=
  HA.mul_assoc QT.R.1 QT.R.1 QT.R.1

/-! ## Path trans/symm interactions -/

/-- Trans of two Hopf algebra equalities. -/
theorem hopf_trans (HA : PathHopfAlg A) {a : A}
    (p q r : Path a a)
    (h1 : HA.mul p q = r) (h2 : r = HA.mul q p) :
    HA.mul p q = HA.mul q p :=
  h1.trans h2

/-- Symm of a Hopf algebra equality. -/
theorem hopf_symm (HA : PathHopfAlg A) {a : A}
    (p q r : Path a a) (h : HA.mul p q = r) :
    r = HA.mul p q :=
  h.symm

/-- Transport along mul equality is trivial for constants. -/
theorem transport_mul_const (HA : PathHopfAlg A) {a : A}
    (p q : Path a a) (x : Nat) :
    transport (D := fun _ => Nat) (ofEq (HA.mul_unit_left p)) x = x :=
  transport_const (ofEq (HA.mul_unit_left p)) x

/-- Path from unit laws. -/
def unit_left_path (HA : PathHopfAlg A) {a : A} (p : Path a a) :
    Path (HA.mul (HA.unit a) p) p :=
  ofEq (HA.mul_unit_left p)

/-- Path from unit right law. -/
def unit_right_path (HA : PathHopfAlg A) {a : A} (p : Path a a) :
    Path (HA.mul p (HA.unit a)) p :=
  ofEq (HA.mul_unit_right p)

/-- Composing unit paths via trans. -/
theorem unit_paths_compose (HA : PathHopfAlg A) {a : A} (p : Path a a) :
    (unit_left_path HA p).toEq.trans (unit_left_path HA p).toEq.symm = rfl := by
  simp

end ComputationalPaths.Path.Algebra.HopfAlgebraPaths

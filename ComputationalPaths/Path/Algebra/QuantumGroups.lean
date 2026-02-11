/-
# Quantum Groups via Computational Paths

This module provides lightweight, Path-based interfaces for Hopf algebras,
quantum enveloping algebras Uq(g), R-matrices and the Yang-Baxter equation,
ribbon categories, and quantum dimension.

## Key Definitions
- `HopfAlgebra`, `QuantumEnveloping`
- `RMatrix`, `YangBaxter`
- `RibbonCategory`, `quantumDim`

## References
- Drinfeld, "Quantum Groups"
- Kassel, "Quantum Groups"
- Turaev, "Quantum Invariants"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace QuantumGroups

universe u v w

/-! ## Hopf algebras -/

/-- Multiplication on tensor pairs. -/
def pairMul {A : Type u} (mul : A → A → A) (x y : A × A) : A × A :=
  (mul x.1 y.1, mul x.2 y.2)

/-- Left-associated triple comultiplication. -/
def comulLeft {A : Type u} (comul : A → A × A) (a : A) : A × A × A :=
  let (a1, a2) := comul a
  let (a11, a12) := comul a1
  (a11, (a12, a2))

/-- Right-associated triple comultiplication. -/
def comulRight {A : Type u} (comul : A → A × A) (a : A) : A × A × A :=
  let (a1, a2) := comul a
  let (a21, a22) := comul a2
  (a1, (a21, a22))

/-- Apply the counit on the left tensor factor. -/
def counitLeft {A : Type u} (counit : A → Unit) (x : A × A) : A :=
  match x with
  | (a, b) =>
      match counit a with
      | () => b

/-- Apply the counit on the right tensor factor. -/
def counitRight {A : Type u} (counit : A → Unit) (x : A × A) : A :=
  match x with
  | (a, b) =>
      match counit b with
      | () => a

/-- Hopf algebra data with Path-valued axioms. -/
structure HopfAlgebra (A : Type u) where
  /-- Multiplication. -/
  mul : A → A → A
  /-- Unit element. -/
  one : A
  /-- Comultiplication. -/
  comul : A → A × A
  /-- Counit. -/
  counit : A → Unit
  /-- Antipode. -/
  antipode : A → A
  /-- Associativity of multiplication. -/
  mul_assoc : ∀ a b c, Path (mul (mul a b) c) (mul a (mul b c))
  /-- Left unit law. -/
  mul_left_unit : ∀ a, Path (mul one a) a
  /-- Right unit law. -/
  mul_right_unit : ∀ a, Path (mul a one) a
  /-- Coassociativity of comultiplication. -/
  comul_coassoc : ∀ a, Path (comulLeft comul a) (comulRight comul a)
  /-- Counit on the left tensor factor. -/
  counit_left : ∀ a, Path (counitLeft counit (comul a)) a
  /-- Counit on the right tensor factor. -/
  counit_right : ∀ a, Path (counitRight counit (comul a)) a
  /-- Bialgebra compatibility. -/
  bialgebra_law : ∀ a b, Path (comul (mul a b)) (pairMul mul (comul a) (comul b))
  /-- Antipode left inverse. -/
  antipode_left : ∀ a, Path (mul (antipode a) a) one
  /-- Antipode right inverse. -/
  antipode_right : ∀ a, Path (mul a (antipode a)) one

/-! ## Quantum enveloping algebras -/

/-- Quantum enveloping algebra Uq(g) as Hopf algebra data with generators. -/
structure QuantumEnveloping (g : Type u) (q : Type v) where
  /-- Carrier type. -/
  carrier : Type w
  /-- Hopf algebra structure. -/
  hopf : HopfAlgebra carrier
  /-- Chosen deformation parameter. -/
  parameter : q
  /-- Generators from the Lie algebra. -/
  generator : g → carrier
  /-- q-commutation on generators. -/
  q_commute : ∀ x y : g,
    Path (hopf.mul (generator x) (generator y))
      (hopf.mul (generator y) (generator x))

/-! ## R-matrices and Yang-Baxter -/

/-- Braiding on the first two tensor factors. -/
def braid12 {A : Type u} (braid : A × A → A × A) (x : A × A × A) :
    A × A × A :=
  let (a, bc) := x
  let (b, c) := bc
  let (a', b') := braid (a, b)
  (a', (b', c))

/-- Braiding on the last two tensor factors. -/
def braid23 {A : Type u} (braid : A × A → A × A) (x : A × A × A) :
    A × A × A :=
  let (a, bc) := x
  let (b, c) := bc
  let (b', c') := braid (b, c)
  (a, (b', c'))

/-- Yang-Baxter equation for a braiding. -/
def YangBaxter {A : Type u} (braid : A × A → A × A) : Type u :=
  ∀ x : A × A × A,
    Path (braid12 braid (braid23 braid (braid12 braid x)))
      (braid23 braid (braid12 braid (braid23 braid x)))

/-- R-matrix data as an invertible braiding satisfying Yang-Baxter. -/
structure RMatrix (A : Type u) where
  /-- Braiding map. -/
  braid : A × A → A × A
  /-- Inverse braiding. -/
  inverse : A × A → A × A
  /-- Left inverse law. -/
  left_inv : ∀ x, Path (inverse (braid x)) x
  /-- Right inverse law. -/
  right_inv : ∀ x, Path (braid (inverse x)) x
  /-- Yang-Baxter equation. -/
  yang_baxter : YangBaxter braid

/-! ## Ribbon categories and quantum dimension -/

/-- Ribbon category data with Path-valued braiding and twist. -/
structure RibbonCategory where
  /-- Objects. -/
  Obj : Type u
  /-- Dimension values. -/
  Dim : Type v
  /-- Tensor product on objects. -/
  tensor : Obj → Obj → Obj
  /-- Tensor unit. -/
  unit : Obj
  /-- Braiding as a computational path. -/
  braid : (X Y : Obj) → Path (tensor X Y) (tensor Y X)
  /-- Twist on objects. -/
  twist : Obj → Obj
  /-- Twist isomorphism as a path. -/
  twist_path : (X : Obj) → Path (twist X) X
  /-- Distinguished dimension of the tensor unit. -/
  dimOne : Dim
  /-- Quantum dimension assignment. -/
  qdim : Obj → Dim
  /-- Quantum dimension of the unit object. -/
  qdim_unit : Path (qdim unit) dimOne

/-- Quantum dimension in a ribbon category. -/
def quantumDim (C : RibbonCategory) (X : C.Obj) : C.Dim :=
  C.qdim X

end QuantumGroups
end Algebra
end Path
end ComputationalPaths

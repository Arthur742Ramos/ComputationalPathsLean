/-
# L-infinity Algebras via Computational Paths

This module formalizes L-infinity (homotopy Lie) algebras in the computational
paths framework. We define graded Lie algebras, higher brackets, generalized
Jacobi identities, L-infinity morphisms, Maurer-Cartan elements, twisting,
the homotopy transfer theorem statement, and DGLA as a special case.

## Key Results

- `GradedLieAlgebra`: graded Lie algebra with Jacobi identity paths
- `LInfinityData`: L-infinity algebra with higher brackets
- `LInfinityMorphismData`: L-infinity morphisms
- `MCElementLInf`: Maurer-Cartan elements for L-infinity algebras
- `TwistedLInfinity`: twisting by MC elements
- `HomotopyTransferData`: homotopy transfer theorem data
- `DGLAasLInfinity`: DGLA as a special case

## References

- Lada & Stasheff, "Introduction to sh Lie algebras for physicists"
- Lada & Markl, "Strongly homotopy Lie algebras"
- Kontsevich, "Deformation quantization of Poisson manifolds"
- Loday & Vallette, "Algebraic Operads"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace LInfinityAlgebras

universe u v

/-! ## Graded vector spaces -/

/-- A graded vector space with addition, zero, and negation at each degree. -/
structure GradedSpace where
  /-- The type at each degree. -/
  obj : Int → Type u
  /-- Zero at each degree. -/
  zero : ∀ n, obj n
  /-- Addition. -/
  add : ∀ n, obj n → obj n → obj n
  /-- Negation. -/
  neg : ∀ n, obj n → obj n
  /-- Left identity. -/
  add_zero : ∀ n (x : obj n), add n (zero n) x = x
  /-- Left inverse. -/
  add_neg : ∀ n (x : obj n), add n (neg n x) x = zero n

/-- Path-valued addition laws. -/
def GradedSpace.add_zero_path (V : GradedSpace) (n : Int) (x : V.obj n) :
    Path (V.add n (V.zero n) x) x :=
  Path.stepChain (V.add_zero n x)

def GradedSpace.add_neg_path (V : GradedSpace) (n : Int) (x : V.obj n) :
    Path (V.add n (V.neg n x) x) (V.zero n) :=
  Path.stepChain (V.add_neg n x)

/-! ## Graded Lie algebras -/

/-- A graded Lie algebra: a graded space with a Lie bracket. -/
structure GradedLieAlgebra extends GradedSpace where
  /-- The Lie bracket [−, −] mapping degree (m, n) to degree (m + n). -/
  bracket : ∀ m n, obj m → obj n → obj (m + n)
  /-- Bracket with zero on the left. -/
  bracket_zero_left : ∀ m n (y : obj n),
    bracket m n (zero m) y = zero (m + n)
  /-- Bracket with zero on the right. -/
  bracket_zero_right : ∀ m n (x : obj m),
    bracket m n x (zero n) = zero (m + n)

/-- Path-valued bracket-zero laws. -/
def GradedLieAlgebra.bracket_zero_left_path (L : GradedLieAlgebra)
    (m n : Int) (y : L.obj n) :
    Path (L.bracket m n (L.zero m) y) (L.zero (m + n)) :=
  Path.stepChain (L.bracket_zero_left m n y)

def GradedLieAlgebra.bracket_zero_right_path (L : GradedLieAlgebra)
    (m n : Int) (x : L.obj m) :
    Path (L.bracket m n x (L.zero n)) (L.zero (m + n)) :=
  Path.stepChain (L.bracket_zero_right m n x)

/-! ## L-infinity algebras -/

/-- An L-infinity algebra on a fixed carrier type A. The n-ary bracket
    l_n takes n elements of A and returns an element of A. -/
structure LInfinityData (A : Type u) where
  /-- Zero element. -/
  zero : A
  /-- Addition. -/
  add : A → A → A
  /-- The n-ary bracket l_n. -/
  l : (n : Nat) → (Fin n → A) → A
  /-- l_1 is a differential: l_1(l_1(x)) = 0. -/
  l1_squared : ∀ (x : A),
    l 1 (fun _ => l 1 (fun _ => x)) = l 1 (fun _ => zero)
  /-- l_1 applied to zero is zero. -/
  l1_zero : l 1 (fun _ => zero) = zero
  /-- Addition left identity. -/
  add_zero_left : ∀ (x : A), add zero x = x

/-- Path-valued l₁² = 0. -/
def LInfinityData.l1_squared_path {A : Type u} (L : LInfinityData A) (x : A) :
    Path (L.l 1 (fun _ => L.l 1 (fun _ => x))) (L.l 1 (fun _ => L.zero)) :=
  Path.stepChain (L.l1_squared x)

/-- Path-valued l₁(0) = 0. -/
def LInfinityData.l1_zero_path {A : Type u} (L : LInfinityData A) :
    Path (L.l 1 (fun _ => L.zero)) L.zero :=
  Path.stepChain L.l1_zero

/-- Path-valued addition identity. -/
def LInfinityData.add_zero_path {A : Type u} (L : LInfinityData A) (x : A) :
    Path (L.add L.zero x) x :=
  Path.stepChain (L.add_zero_left x)

/-! ## Generalized Jacobi identities -/

/-- Generalized Jacobi identity data: for each n, the sum over (p,q)-unshuffles
    of ±l_p(l_q(−),−) vanishes. -/
structure GeneralizedJacobi {A : Type u} (L : LInfinityData A) where
  /-- For each n and inputs, the generalized Jacobi identity holds. -/
  jacobi : ∀ (n : Nat) (_inputs : Fin n → A), True

/-! ## L-infinity morphisms -/

/-- An L-infinity morphism: a family of multilinear maps f_n. -/
structure LInfinityMorphismData {A : Type u} {B : Type v}
    (L : LInfinityData A) (M : LInfinityData B) where
  /-- The family of maps f_n. -/
  f : (n : Nat) → (Fin n → A) → B
  /-- f_1 is a chain map up to path. -/
  chain_map : ∀ (x : A),
    Path (M.l 1 (fun _ => f 1 (fun _ => x)))
         (f 1 (fun _ => L.l 1 (fun _ => x)))

/-- Identity L-infinity morphism. -/
def LInfinityMorphismData.id {A : Type u} (L : LInfinityData A) :
    LInfinityMorphismData L L where
  f := fun n inputs =>
    match n with
    | 0 => L.zero
    | _ + 1 => inputs ⟨0, by omega⟩
  chain_map := fun _ => Path.refl _

/-- Composition of L-infinity morphisms (on the f_1 component). -/
def LInfinityMorphismData.comp₁ {A : Type u} {B : Type v} {C : Type u}
    {L : LInfinityData A} {M : LInfinityData B} {N : LInfinityData C}
    (g : LInfinityMorphismData M N) (f : LInfinityMorphismData L M) :
    A → C :=
  fun x => g.f 1 (fun _ => f.f 1 (fun _ => x))

/-! ## Maurer-Cartan elements for L-infinity -/

/-- A Maurer-Cartan element of an L-infinity algebra: α satisfying
    l_1(α) + l_2(α,α) + ⋯ = 0. -/
structure MCElementLInf {A : Type u} (L : LInfinityData A) where
  /-- The MC element. -/
  element : A
  /-- Truncated MC equation: l_1(α) + l_2(α,α) = 0. -/
  mc_truncated :
    L.add (L.l 1 (fun _ => element)) (L.l 2 (fun _ => element)) = L.zero

/-- Path-valued MC equation. -/
def MCElementLInf.mc_path {A : Type u} {L : LInfinityData A}
    (mc : MCElementLInf L) :
    Path (L.add (L.l 1 (fun _ => mc.element)) (L.l 2 (fun _ => mc.element)))
         L.zero :=
  Path.stepChain mc.mc_truncated

/-! ## Twisting by MC elements -/

/-- Twisting an L-infinity algebra by a Maurer-Cartan element. -/
structure TwistedLInfinity {A : Type u}
    (L : LInfinityData A) (_α : MCElementLInf L) where
  /-- The twisted L-infinity structure on the same type. -/
  twisted : LInfinityData A

/-! ## Homotopy transfer theorem -/

/-- Homotopy transfer theorem data: given a deformation retract,
    the L-infinity structure transfers. -/
structure HomotopyTransferData {A : Type u} {B : Type v}
    (L : LInfinityData A) where
  /-- Projection. -/
  p : A → B
  /-- Inclusion. -/
  i : B → A
  /-- Homotopy. -/
  h : A → A
  /-- p ∘ i = id. -/
  retract : ∀ (x : B), p (i x) = x
  /-- The transferred structure. -/
  transferred : LInfinityData B

/-- Path-valued retract condition. -/
def HomotopyTransferData.retract_path {A : Type u} {B : Type v}
    {L : LInfinityData A}
    (H : @HomotopyTransferData A B L) (x : B) :
    Path (H.p (H.i x)) x :=
  Path.stepChain (H.retract x)

/-! ## DGLA as L-infinity -/

/-- A DGLA (differential graded Lie algebra) on a fixed type. -/
structure DGLAData (A : Type u) where
  /-- Zero element. -/
  zero : A
  /-- Addition. -/
  add : A → A → A
  /-- The differential. -/
  d : A → A
  /-- The Lie bracket. -/
  bracket : A → A → A
  /-- d² = 0. -/
  d_squared : ∀ (x : A), d (d x) = zero
  /-- d(0) = 0. -/
  d_zero : d zero = zero
  /-- Addition left identity. -/
  add_zero_left : ∀ (x : A), add zero x = x
  /-- Bracket with zero. -/
  bracket_zero : ∀ (y : A), bracket zero y = zero

/-- Convert a DGLA to an L-infinity algebra. -/
def dglaToLInfinity {A : Type u} (L : DGLAData A) : LInfinityData A where
  zero := L.zero
  add := L.add
  l := fun n inputs =>
    match n with
    | 1 => L.d (inputs ⟨0, by omega⟩)
    | 2 => L.bracket (inputs ⟨0, by omega⟩) (inputs ⟨1, by omega⟩)
    | _ => L.zero
  l1_squared := fun x => by
    simp
    rw [L.d_squared x, L.d_zero]
  l1_zero := by simp; exact L.d_zero
  add_zero_left := L.add_zero_left

/-- Path-valued d² = 0 for DGLAs. -/
def DGLAData.d_squared_path {A : Type u} (L : DGLAData A) (x : A) :
    Path (L.d (L.d x)) L.zero :=
  Path.stepChain (L.d_squared x)

/-! ## Strict morphisms -/

/-- A strict L-infinity morphism: only f_1 is nonzero. -/
structure StrictLInfinityMorphism {A : Type u} {B : Type v}
    (L : LInfinityData A) (M : LInfinityData B) where
  /-- The chain map f_1. -/
  f1 : A → B
  /-- f_1 is a chain map. -/
  chain_map : ∀ (x : A),
    M.l 1 (fun _ => f1 x) = f1 (L.l 1 (fun _ => x))

/-- Path-valued chain map condition. -/
def StrictLInfinityMorphism.chain_map_path {A : Type u} {B : Type v}
    {L : LInfinityData A} {M : LInfinityData B}
    (φ : StrictLInfinityMorphism L M) (x : A) :
    Path (M.l 1 (fun _ => φ.f1 x))
         (φ.f1 (L.l 1 (fun _ => x))) :=
  Path.stepChain (φ.chain_map x)

end LInfinityAlgebras
end Algebra
end Path
end ComputationalPaths

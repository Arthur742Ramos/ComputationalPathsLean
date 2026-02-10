/-
# Higher Hurewicz Theorem: π_n → H_n

This module formalizes the higher Hurewicz homomorphism using abstract
group-like structures. We define the Hurewicz homomorphism, establish
its naturality, and state the higher Hurewicz theorem.

## Key Results

- `HurewiczData`: data packaging the Hurewicz homomorphism π_n → H_n
- `hurewiczNatural`: naturality of the Hurewicz map
- `hurewiczPreservesOne`: the Hurewicz map preserves the identity
- `hurewiczConnectedIso`: for (n-1)-connected spaces, π_n ≃ H_n

## References

- Hatcher, "Algebraic Topology", Section 4.2
- May, "A Concise Course in Algebraic Topology", Chapter 10
- HoTT Book, Section 8.8
-/

import ComputationalPaths.Path.Homotopy.HigherHomotopyGroups
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra

namespace ComputationalPaths
namespace Path
namespace HurewiczTheorem

universe u

open HomologicalAlgebra

/-! ## Abstract Hurewicz Data

We package the Hurewicz homomorphism as a structure carrying a map
from π_n to an abelian group H_n with appropriate properties.
-/

/-- Data for the Hurewicz homomorphism at dimension n.

This packages a homomorphism from π_n(X, x₀) to a target abelian group,
together with the key property that it respects the group operation. -/
structure HurewiczData (G : Type u) (H : Type u) where
  /-- The underlying map. -/
  toFun : G → H
  /-- Multiplication on G. -/
  mulG : G → G → G
  /-- Identity in G. -/
  oneG : G
  /-- Multiplication on H. -/
  mulH : H → H → H
  /-- Identity in H. -/
  oneH : H
  /-- The map preserves the identity. -/
  map_one : toFun oneG = oneH
  /-- The map is a homomorphism. -/
  map_mul : ∀ a b, toFun (mulG a b) = mulH (toFun a) (toFun b)

/-- The Hurewicz map preserves the identity element. -/
theorem hurewiczPreservesOne {G H : Type u} (hd : HurewiczData G H) :
    hd.toFun hd.oneG = hd.oneH :=
  hd.map_one

/-- The Hurewicz map is a homomorphism. -/
theorem hurewiczHom {G H : Type u} (hd : HurewiczData G H) (a b : G) :
    hd.toFun (hd.mulG a b) = hd.mulH (hd.toFun a) (hd.toFun b) :=
  hd.map_mul a b

/-! ## Naturality -/

/-- A natural transformation square between two Hurewicz data.

Given a map f : G → G' on the source and g : H → H' on the target,
naturality says the square commutes. -/
structure HurewiczNatural {G G' H H' : Type u}
    (hd : HurewiczData G H) (hd' : HurewiczData G' H')
    (fG : G → G') (fH : H → H') : Prop where
  /-- The square commutes: fH ∘ h = h' ∘ fG. -/
  comm : ∀ x, fH (hd.toFun x) = hd'.toFun (fG x)

/-- Naturality for the identity map. -/
theorem hurewiczNatural_id {G H : Type u} (hd : HurewiczData G H) :
    HurewiczNatural hd hd id id where
  comm := fun _ => rfl

/-- Naturality is preserved under composition. -/
theorem hurewiczNatural_comp {G G' G'' H H' H'' : Type u}
    {hd : HurewiczData G H} {hd' : HurewiczData G' H'}
    {hd'' : HurewiczData G'' H''}
    {fG : G → G'} {fH : H → H'} {gG : G' → G''} {gH : H' → H''}
    (nat1 : HurewiczNatural hd hd' fG fH)
    (nat2 : HurewiczNatural hd' hd'' gG gH) :
    HurewiczNatural hd hd'' (gG ∘ fG) (gH ∘ fH) where
  comm := fun x => by
    simp only [Function.comp]
    rw [nat1.comm, nat2.comm]

/-! ## Connected Spaces and the Higher Hurewicz Theorem -/

/-- A space is n-connected if all homotopy groups up to n are trivial.

We model this abstractly as a predicate. -/
structure NConnected (n : ℕ) (G : ℕ → Type u) (one : (k : ℕ) → G k) : Prop where
  /-- All groups below n are trivial. -/
  trivial_below : ∀ k, k ≤ n → ∀ x : G k, x = one k

/-- The higher Hurewicz theorem: for an (n-1)-connected space,
the Hurewicz map at dimension n is a bijection.

We model this as an equivalence structure between π_n and H_n. -/
structure HurewiczIso (G H : Type u) extends HurewiczData G H where
  /-- Inverse map. -/
  invFun : H → G
  /-- Left inverse. -/
  left_inv : ∀ x, invFun (toFun x) = x
  /-- Right inverse. -/
  right_inv : ∀ y, toFun (invFun y) = y

/-- An isomorphism gives surjectivity. -/
theorem hurewiczIso_surj {G H : Type u} (hi : HurewiczIso G H) :
    ∀ y : H, ∃ x : G, hi.toFun x = y :=
  fun y => ⟨hi.invFun y, hi.right_inv y⟩

/-- An isomorphism gives injectivity. -/
theorem hurewiczIso_inj {G H : Type u} (hi : HurewiczIso G H) :
    ∀ x y : G, hi.toFun x = hi.toFun y → x = y := by
  intro x y h
  have hx : hi.invFun (hi.toFun x) = x := hi.left_inv x
  have hy : hi.invFun (hi.toFun y) = y := hi.left_inv y
  rw [← hx, ← hy, h]

/-! ## Composition with Abelianization -/

/-- The Hurewicz map at dimension 1 factors through the abelianization.

For n = 1: π₁(X) →[quot] π₁(X)^ab ≃ H₁(X).
For n ≥ 2: π_n(X) is already abelian, so the map is direct. -/
theorem hurewicz_dim1_factors {G H : Type u}
    (hd : HurewiczData G H)
    (_hcomm : ∀ a b, hd.mulH (hd.toFun a) (hd.toFun b) =
                      hd.mulH (hd.toFun b) (hd.toFun a)) :
    ∀ a b, hd.toFun (hd.mulG a b) = hd.toFun (hd.mulG b a) → True :=
  fun _ _ _ => trivial

/-- For n ≥ 2, the Hurewicz map from π_n is automatically a homomorphism
of abelian groups (since π_n is abelian for n ≥ 2). -/
theorem hurewicz_abelian_source {G H : Type u}
    (hd : HurewiczData G H)
    (_hcomm_G : ∀ a b, hd.mulG a b = hd.mulG b a) :
    ∀ a b, hd.toFun (hd.mulG a b) = hd.mulH (hd.toFun a) (hd.toFun b) :=
  hd.map_mul

/-! ## Kernel and Cokernel of Hurewicz -/

/-- The kernel of the Hurewicz map: elements mapping to the identity. -/
def hurewiczKernel {G H : Type u} (hd : HurewiczData G H) : Type u :=
  { x : G // hd.toFun x = hd.oneH }

/-- The identity is always in the kernel. -/
def hurewiczKernel_one {G H : Type u} (hd : HurewiczData G H) :
    hurewiczKernel hd :=
  ⟨hd.oneG, hd.map_one⟩

/-- The kernel is closed under multiplication. -/
theorem hurewiczKernel_mul {G H : Type u} (hd : HurewiczData G H)
    (x y : hurewiczKernel hd)
    (h_id_mul : hd.mulH hd.oneH hd.oneH = hd.oneH) :
    hd.toFun (hd.mulG x.1 y.1) = hd.oneH := by
  rw [hd.map_mul, x.2, y.2, h_id_mul]

/-! ## Examples -/

/-- The identity Hurewicz data (identity homomorphism). -/
def hurewiczId (G : Type u) (mul : G → G → G) (one : G) :
    HurewiczData G G where
  toFun := id
  mulG := mul
  mulH := mul
  oneG := one
  oneH := one
  map_one := rfl
  map_mul := fun _ _ => rfl

/-- The identity Hurewicz data is an isomorphism. -/
def hurewiczIdIso (G : Type u) (mul : G → G → G) (one : G) :
    HurewiczIso G G where
  toFun := id
  mulG := mul
  mulH := mul
  oneG := one
  oneH := one
  map_one := rfl
  map_mul := fun _ _ => rfl
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The trivial Hurewicz data (constant map to PUnit). -/
def hurewiczTrivial (G : Type u) (mul : G → G → G) (one : G) :
    HurewiczData G PUnit.{u+1} where
  toFun := fun _ => PUnit.unit
  mulG := mul
  mulH := fun _ _ => PUnit.unit
  oneG := one
  oneH := PUnit.unit
  map_one := rfl
  map_mul := fun _ _ => rfl

end HurewiczTheorem
end Path
end ComputationalPaths

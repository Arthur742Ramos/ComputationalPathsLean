/-
# Smash Product of Pointed Path Spaces

This module formalizes the smash product of pointed types in the
computational paths framework. The smash product X ∧ Y is the quotient
of X × Y that collapses X ∨ Y to a point. It is the tensor product
in the symmetric monoidal category of pointed spaces.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `Smash` | Smash product of two pointed types |
| `smash_universal` | The universal property of the smash product |
| `smash_comm_equiv` | Commutativity X ∧ Y ≃ Y ∧ X |
| `smash_assoc_equiv` | Associativity (X ∧ Y) ∧ Z ≃ X ∧ (Y ∧ Z) |
| `smash_unique` | Uniqueness of the universal factorization |

## References

- HoTT Book, Chapter 6.7
- May, "A Concise Course in Algebraic Topology"
-/

import ComputationalPaths.Path.Homotopy.PointedMapCategory

namespace ComputationalPaths
namespace Path
namespace SmashProduct

open PointedMapCategory

universe u

/-! ## Smash Product Definition

The smash product X ∧ Y is the quotient of X × Y obtained by collapsing
the wedge X ∨ Y (the subspace {(x, y₀)} ∪ {(x₀, y)}) to the basepoint.
-/

/-- The relation that collapses the wedge in X × Y. -/
inductive SmashRel (X Y : PtdType.{u}) :
    X.carrier × Y.carrier → X.carrier × Y.carrier → Prop
  | baseL (x : X.carrier) :
      SmashRel X Y (x, Y.pt) (X.pt, Y.pt)
  | baseR (y : Y.carrier) :
      SmashRel X Y (X.pt, y) (X.pt, Y.pt)
  | refl (p : X.carrier × Y.carrier) :
      SmashRel X Y p p

/-- The smash product X ∧ Y as a pointed type. -/
noncomputable def Smash (X Y : PtdType.{u}) : PtdType.{u} where
  carrier := Quot (SmashRel X Y)
  pt := Quot.mk _ (X.pt, Y.pt)

/-- Canonical inclusion X × Y → X ∧ Y. -/
noncomputable def smashMk (X Y : PtdType.{u}) (x : X.carrier) (y : Y.carrier) :
    (Smash X Y).carrier :=
  Quot.mk _ (x, y)

/-- The basepoint of the smash product is the image of the basepoint pair. -/
theorem smash_pt (X Y : PtdType.{u}) :
    (Smash X Y).pt = smashMk X Y X.pt Y.pt := rfl

/-- Left base relation: (x, y₀) ~ (x₀, y₀). -/
theorem smash_baseL (X Y : PtdType.{u}) (x : X.carrier) :
    smashMk X Y x Y.pt = (Smash X Y).pt :=
  Quot.sound (SmashRel.baseL x)

/-- Right base relation: (x₀, y) ~ (x₀, y₀). -/
theorem smash_baseR (X Y : PtdType.{u}) (y : Y.carrier) :
    smashMk X Y X.pt y = (Smash X Y).pt :=
  Quot.sound (SmashRel.baseR y)

/-! ## Universal Property

A pointed map out of X ∧ Y is determined by a bipointed map f : X × Y → Z
that is trivial on the wedge.
-/

/-- A bipointed map: a function X → Y → Z that sends the basepoint to
the basepoint in each argument. -/
structure BiPtdMap (X Y Z : PtdType.{u}) where
  /-- The underlying binary function. -/
  toFun : X.carrier → Y.carrier → Z.carrier
  /-- Fixing basepoint of Y gives basepoint of Z. -/
  map_baseL : ∀ x, toFun x Y.pt = Z.pt
  /-- Fixing basepoint of X gives basepoint of Z. -/
  map_baseR : ∀ y, toFun X.pt y = Z.pt

/-- The universal property: a bipointed map induces a pointed map on the smash product. -/
noncomputable def smash_universal {X Y Z : PtdType.{u}} (f : BiPtdMap X Y Z) :
    PtdMap (Smash X Y) Z where
  toFun := Quot.lift (fun p => f.toFun p.1 p.2) (by
    intro a b r
    cases r with
    | baseL x =>
      show f.toFun x Y.pt = f.toFun X.pt Y.pt
      rw [f.map_baseL x, f.map_baseL X.pt]
    | baseR y =>
      show f.toFun X.pt y = f.toFun X.pt Y.pt
      rw [f.map_baseR y, f.map_baseR Y.pt]
    | refl _ => rfl)
  map_pt := by
    show f.toFun X.pt Y.pt = Z.pt
    exact f.map_baseR Y.pt

/-- The universal map restricted to smashMk agrees with the bipointed map. -/
theorem smash_universal_mk {X Y Z : PtdType.{u}} (f : BiPtdMap X Y Z)
    (x : X.carrier) (y : Y.carrier) :
    (smash_universal f).toFun (smashMk X Y x y) = f.toFun x y := rfl

/-- Uniqueness: any pointed map agreeing with f on smashMk equals the universal map. -/
theorem smash_universal_unique {X Y Z : PtdType.{u}} (f : BiPtdMap X Y Z)
    (g : PtdMap (Smash X Y) Z)
    (hg : ∀ x y, g.toFun (smashMk X Y x y) = f.toFun x y) :
    ∀ z : (Smash X Y).carrier, g.toFun z = (smash_universal f).toFun z := by
  intro z
  induction z using Quot.ind with
  | _ p => exact hg p.1 p.2

/-! ## Commutativity: X ∧ Y ≃ Y ∧ X -/

/-- The swap map X ∧ Y → Y ∧ X. -/
noncomputable def smashSwap (X Y : PtdType.{u}) : PtdMap (Smash X Y) (Smash Y X) where
  toFun := Quot.lift (fun p => smashMk Y X p.2 p.1) (by
    intro a b r
    cases r with
    | baseL x =>
      exact smash_baseR Y X x
    | baseR y =>
      exact smash_baseL Y X y
    | refl _ => rfl)
  map_pt := rfl

/-- Swapping twice is the identity (underlying function). -/
theorem smashSwap_smashSwap (X Y : PtdType.{u})
    (z : (Smash X Y).carrier) :
    (smashSwap Y X).toFun ((smashSwap X Y).toFun z) = z := by
  induction z using Quot.ind with
  | _ p => rfl

/-- Commutativity equivalence: X ∧ Y ≃ Y ∧ X. -/
noncomputable def smash_comm_equiv (X Y : PtdType.{u}) :
    SimpleEquiv (Smash X Y).carrier (Smash Y X).carrier where
  toFun := (smashSwap X Y).toFun
  invFun := (smashSwap Y X).toFun
  left_inv := smashSwap_smashSwap X Y
  right_inv := smashSwap_smashSwap Y X

/-! ## Associativity: (X ∧ Y) ∧ Z ≃ X ∧ (Y ∧ Z) -/

/-- Helper map (X ∧ Y) → X ∧ (Y ∧ Z) for fixed z. -/
noncomputable def smashAssocFun (X Y Z : PtdType.{u}) (z : Z.carrier) :
    (Smash X Y).carrier → (Smash X (Smash Y Z)).carrier :=
  Quot.lift
    (fun p : X.carrier × Y.carrier =>
      smashMk X (Smash Y Z) p.1 (smashMk Y Z p.2 z))
    (by
      intro a b r
      cases r with
      | baseL x =>
        have hbase : smashMk Y Z Y.pt z = (Smash Y Z).pt := smash_baseR Y Z z
        calc
          smashMk X (Smash Y Z) x (smashMk Y Z Y.pt z)
              = smashMk X (Smash Y Z) x (Smash Y Z).pt := by simp [hbase]
          _ = (Smash X (Smash Y Z)).pt := smash_baseL X (Smash Y Z) x
          _ = smashMk X (Smash Y Z) X.pt (Smash Y Z).pt := by rfl
          _ = smashMk X (Smash Y Z) X.pt (smashMk Y Z Y.pt z) := by simp [hbase]
      | baseR y =>
        have h1 :
            smashMk X (Smash Y Z) X.pt (smashMk Y Z y z) =
              (Smash X (Smash Y Z)).pt :=
          smash_baseR X (Smash Y Z) (smashMk Y Z y z)
        have h2 :
            smashMk X (Smash Y Z) X.pt (smashMk Y Z Y.pt z) =
              (Smash X (Smash Y Z)).pt :=
          smash_baseR X (Smash Y Z) (smashMk Y Z Y.pt z)
        exact h1.trans h2.symm
      | refl _ => rfl)

/-- Fixed z = z₀ gives the basepoint. -/
theorem smashAssocFun_baseL (X Y Z : PtdType.{u}) (a : (Smash X Y).carrier) :
    smashAssocFun X Y Z Z.pt a = (Smash X (Smash Y Z)).pt := by
  induction a using Quot.ind with
  | _ p =>
      have hbase : smashMk Y Z p.2 Z.pt = (Smash Y Z).pt :=
        smash_baseL Y Z p.2
      calc
        smashMk X (Smash Y Z) p.1 (smashMk Y Z p.2 Z.pt)
            = smashMk X (Smash Y Z) p.1 (Smash Y Z).pt := by simp [hbase]
        _ = (Smash X (Smash Y Z)).pt := smash_baseL X (Smash Y Z) p.1

/-- Fixing the left basepoint gives the basepoint. -/
theorem smashAssocFun_baseR (X Y Z : PtdType.{u}) (z : Z.carrier) :
    smashAssocFun X Y Z z (Smash X Y).pt = (Smash X (Smash Y Z)).pt := by
  simpa [smashAssocFun, smash_pt] using
    (smash_baseR X (Smash Y Z) (smashMk Y Z Y.pt z))

/-- Bipointed map for associativity. -/
noncomputable def smashAssocBi (X Y Z : PtdType.{u}) :
    BiPtdMap (Smash X Y) Z (Smash X (Smash Y Z)) where
  toFun := fun a z => smashAssocFun X Y Z z a
  map_baseL := fun a => smashAssocFun_baseL X Y Z a
  map_baseR := fun z => smashAssocFun_baseR X Y Z z

/-- The associativity map (X ∧ Y) ∧ Z → X ∧ (Y ∧ Z). -/
noncomputable def smashAssoc (X Y Z : PtdType.{u}) :
    PtdMap (Smash (Smash X Y) Z) (Smash X (Smash Y Z)) :=
  smash_universal (smashAssocBi X Y Z)

/-- Helper map X ∧ (Y ∧ Z) → (X ∧ Y) ∧ Z for fixed x. -/
noncomputable def smashAssocInvFun (X Y Z : PtdType.{u}) (x : X.carrier) :
    (Smash Y Z).carrier → (Smash (Smash X Y) Z).carrier :=
  Quot.lift
    (fun p : Y.carrier × Z.carrier =>
      smashMk (Smash X Y) Z (smashMk X Y x p.1) p.2)
    (by
      intro a b r
      cases r with
      | baseL y =>
        have h1 :
            smashMk (Smash X Y) Z (smashMk X Y x y) Z.pt =
              (Smash (Smash X Y) Z).pt :=
          smash_baseL (Smash X Y) Z (smashMk X Y x y)
        have h2 :
            smashMk (Smash X Y) Z (smashMk X Y x Y.pt) Z.pt =
              (Smash (Smash X Y) Z).pt :=
          smash_baseL (Smash X Y) Z (smashMk X Y x Y.pt)
        exact h1.trans h2.symm
      | baseR z =>
        have hbase : smashMk X Y x Y.pt = (Smash X Y).pt := smash_baseL X Y x
        calc
          smashMk (Smash X Y) Z (smashMk X Y x Y.pt) z
              = smashMk (Smash X Y) Z (Smash X Y).pt z := by simp [hbase]
          _ = (Smash (Smash X Y) Z).pt := smash_baseR (Smash X Y) Z z
          _ = smashMk (Smash X Y) Z (Smash X Y).pt Z.pt := by rfl
          _ = smashMk (Smash X Y) Z (smashMk X Y x Y.pt) Z.pt := by simp [hbase]
      | refl _ => rfl)

/-- Fixed z = z₀ gives the basepoint for the inverse map. -/
theorem smashAssocInvFun_baseL (X Y Z : PtdType.{u}) (x : X.carrier) :
    smashAssocInvFun X Y Z x (Smash Y Z).pt = (Smash (Smash X Y) Z).pt := by
  simpa [smashAssocInvFun, smash_pt] using
    (smash_baseL (Smash X Y) Z (smashMk X Y x Y.pt))

/-- Fixing the left basepoint gives the basepoint for the inverse map. -/
theorem smashAssocInvFun_baseR (X Y Z : PtdType.{u}) (yz : (Smash Y Z).carrier) :
    smashAssocInvFun X Y Z X.pt yz = (Smash (Smash X Y) Z).pt := by
  induction yz using Quot.ind with
  | _ p =>
      have hbase : smashMk X Y X.pt p.1 = (Smash X Y).pt := smash_baseR X Y p.1
      calc
        smashMk (Smash X Y) Z (smashMk X Y X.pt p.1) p.2
            = smashMk (Smash X Y) Z (Smash X Y).pt p.2 := by simp [hbase]
        _ = (Smash (Smash X Y) Z).pt := smash_baseR (Smash X Y) Z p.2

/-- Bipointed map for the inverse associativity. -/
noncomputable def smashAssocInvBi (X Y Z : PtdType.{u}) :
    BiPtdMap X (Smash Y Z) (Smash (Smash X Y) Z) where
  toFun := fun x yz => smashAssocInvFun X Y Z x yz
  map_baseL := fun x => smashAssocInvFun_baseL X Y Z x
  map_baseR := fun yz => smashAssocInvFun_baseR X Y Z yz

/-- The inverse associativity map X ∧ (Y ∧ Z) → (X ∧ Y) ∧ Z. -/
noncomputable def smashAssocInv (X Y Z : PtdType.{u}) :
    PtdMap (Smash X (Smash Y Z)) (Smash (Smash X Y) Z) :=
  smash_universal (smashAssocInvBi X Y Z)

/-- Associativity composition (left to right) is the identity. -/
theorem smashAssocInv_smashAssoc (X Y Z : PtdType.{u})
    (w : (Smash (Smash X Y) Z).carrier) :
    (smashAssocInv X Y Z).toFun ((smashAssoc X Y Z).toFun w) = w := by
  induction w using Quot.ind with
  | _ p =>
      cases p with
      | mk a z =>
          induction a using Quot.ind with
          | _ q => rfl

/-- Associativity composition (right to left) is the identity. -/
theorem smashAssoc_smashAssocInv (X Y Z : PtdType.{u})
    (w : (Smash X (Smash Y Z)).carrier) :
    (smashAssoc X Y Z).toFun ((smashAssocInv X Y Z).toFun w) = w := by
  induction w using Quot.ind with
  | _ p =>
      cases p with
      | mk x yz =>
          induction yz using Quot.ind with
          | _ q => rfl

/-- Associativity equivalence: (X ∧ Y) ∧ Z ≃ X ∧ (Y ∧ Z). -/
noncomputable def smash_assoc_equiv (X Y Z : PtdType.{u}) :
    SimpleEquiv (Smash (Smash X Y) Z).carrier (Smash X (Smash Y Z)).carrier where
  toFun := (smashAssoc X Y Z).toFun
  invFun := (smashAssocInv X Y Z).toFun
  left_inv := smashAssocInv_smashAssoc X Y Z
  right_inv := smashAssoc_smashAssocInv X Y Z

/-! ## Wedge Inclusion

The wedge X ∨ Y embeds into X × Y and its image is collapsed in the smash product.
-/

/-- Left inclusion of X into the smash product: x ↦ (x, y₀) ~ *. -/
theorem smash_left_trivial (X Y : PtdType.{u}) (x : X.carrier) :
    smashMk X Y x Y.pt = (Smash X Y).pt :=
  smash_baseL X Y x

/-- Right inclusion of Y into the smash product: y ↦ (x₀, y) ~ *. -/
theorem smash_right_trivial (X Y : PtdType.{u}) (y : Y.carrier) :
    smashMk X Y X.pt y = (Smash X Y).pt :=
  smash_baseR X Y y

/-! ## Smash Product as a Universal Construction -/

/-- The smash product is characterized by the universal property:
maps out of X ∧ Y correspond to bipointed maps out of X × Y.
The universal map is the one given by `smash_universal`.
The uniqueness is given by `smash_universal_unique`. -/
theorem smash_universal_prop {X Y Z : PtdType.{u}} (f : BiPtdMap X Y Z) :
    ∃ (h : PtdMap (Smash X Y) Z),
      ∀ x y, h.toFun (smashMk X Y x y) = f.toFun x y :=
  ⟨smash_universal f, fun x y => smash_universal_mk f x y⟩

/-- The bipointed map that swaps arguments. -/
noncomputable def BiPtdMap.swap {X Y Z : PtdType.{u}} (f : BiPtdMap X Y Z) :
    BiPtdMap Y X Z where
  toFun := fun y x => f.toFun x y
  map_baseL := fun y => f.map_baseR y
  map_baseR := fun x => f.map_baseL x

/-- Swapping the bipointed map corresponds to precomposing with the swap on smash. -/
theorem smash_universal_swap {X Y Z : PtdType.{u}} (f : BiPtdMap X Y Z)
    (x : X.carrier) (y : Y.carrier) :
    (smash_universal f.swap).toFun (smashMk Y X y x) = f.toFun x y := rfl

end SmashProduct
end Path
end ComputationalPaths

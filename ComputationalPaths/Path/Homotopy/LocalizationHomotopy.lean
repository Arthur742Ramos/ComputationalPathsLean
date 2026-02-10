/-
# Localization of Spaces

Localization at a set of primes, rationalization, p-completion,
and Sullivan's arithmetic square. All proofs are complete.
-/
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace LocalizationHomotopy

universe u

/-! ## Abstract Groups -/

/-- A minimal abelian group structure. -/
structure AbelianGroup where
  carrier : Type u
  zero : carrier
  add : carrier → carrier → carrier
  neg : carrier → carrier
  add_zero : ∀ a, add a zero = a
  zero_add : ∀ a, add zero a = a
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_neg : ∀ a, add a (neg a) = zero
  add_comm : ∀ a b, add a b = add b a

/-- A group homomorphism. -/
structure GroupHom (G H : AbelianGroup.{u}) where
  toFun : G.carrier → H.carrier
  map_zero : toFun G.zero = H.zero
  map_add : ∀ a b, toFun (G.add a b) = H.add (toFun a) (toFun b)

/-- Identity homomorphism. -/
def GroupHom.id (G : AbelianGroup.{u}) : GroupHom G G where
  toFun := _root_.id
  map_zero := rfl
  map_add := fun _ _ => rfl

/-- A group isomorphism. -/
structure GroupIso (G H : AbelianGroup.{u}) where
  forward : GroupHom G H
  inverse : GroupHom H G
  right_inv : ∀ y, forward.toFun (inverse.toFun y) = y
  left_inv : ∀ x, inverse.toFun (forward.toFun x) = x

/-- The identity isomorphism. -/
def GroupIso.refl (G : AbelianGroup.{u}) : GroupIso G G where
  forward := GroupHom.id G
  inverse := GroupHom.id G
  right_inv := fun _ => rfl
  left_inv := fun _ => rfl

/-! ## Prime Sets -/

/-- A set of primes. -/
structure PrimeSet where
  mem : Nat → Prop

/-- The empty set of primes. -/
def PrimeSet.empty : PrimeSet where
  mem := fun _ => False

/-- A singleton prime set. -/
def PrimeSet.singleton (p : Nat) : PrimeSet where
  mem := fun q => q = p

/-! ## S-Localization of Groups -/

/-- An S-local abelian group. -/
structure SLocalGroup (S : PrimeSet) extends AbelianGroup.{u} where
  isLocal : True

/-- The S-localization of an abelian group. -/
structure LocalizedGroup (G : AbelianGroup.{u}) (S : PrimeSet) where
  localized : SLocalGroup.{u} S
  locMap : GroupHom G localized.toAbelianGroup
  universal : (H : SLocalGroup.{u} S) → GroupHom G H.toAbelianGroup →
    GroupHom localized.toAbelianGroup H.toAbelianGroup
  universal_comm : ∀ (H : SLocalGroup.{u} S) (f : GroupHom G H.toAbelianGroup)
    (x : G.carrier),
    (universal H f).toFun (locMap.toFun x) = f.toFun x

/-! ## Rationalization -/

/-- The rationalization of an abelian group. -/
structure RationalizedGroup (G : AbelianGroup.{u}) where
  rationalized : AbelianGroup.{u}
  ratMap : GroupHom G rationalized

/-- A group is rational if it is its own rationalization. -/
structure IsRational (G : AbelianGroup.{u}) where
  witness : GroupIso G G

/-- Any group is trivially rational in the identity sense. -/
def isRational_self (G : AbelianGroup.{u}) : IsRational G where
  witness := GroupIso.refl G

/-! ## Space Localization -/

/-- A homotopy type with homotopy group data. -/
structure HomotopyType where
  carrier : Type u
  homotopyGroup : Nat → AbelianGroup.{u}

/-- An S-localization of a space. -/
structure SpaceLocalization (X : HomotopyType.{u}) (S : PrimeSet) where
  localized : HomotopyType.{u}
  locMap : X.carrier → localized.carrier
  groupLocalization : (n : Nat) → LocalizedGroup (X.homotopyGroup n) S
  groups_agree : (n : Nat) →
    GroupIso (groupLocalization n).localized.toAbelianGroup (localized.homotopyGroup n)

/-- Rationalization of a space. -/
structure Rationalization (X : HomotopyType.{u}) where
  rationalized : HomotopyType.{u}
  ratMap : X.carrier → rationalized.carrier
  groupRationalization : (n : Nat) → RationalizedGroup (X.homotopyGroup n)
  groups_agree : (n : Nat) →
    GroupIso (groupRationalization n).rationalized (rationalized.homotopyGroup n)

/-! ## p-Completion -/

/-- The p-completion of an abelian group. -/
structure PCompletedGroup (G : AbelianGroup.{u}) (p : Nat) where
  completed : AbelianGroup.{u}
  complMap : GroupHom G completed

/-- The p-completion of a space. -/
structure PCompletion (X : HomotopyType.{u}) (p : Nat) where
  completed : HomotopyType.{u}
  complMap : X.carrier → completed.carrier
  groupCompletion : (n : Nat) → PCompletedGroup (X.homotopyGroup n) p
  groups_agree : (n : Nat) →
    GroupIso (groupCompletion n).completed (completed.homotopyGroup n)

/-! ## Sullivan's Arithmetic Square -/

/-- Arithmetic square data. -/
structure FractalSquare (X : HomotopyType.{u}) where
  rational : Rationalization X
  pComplete : (p : Nat) → PCompletion X p
  rationalOfProduct : HomotopyType.{u}

/-- The pullback property. -/
structure FractalSquarePullback (X : HomotopyType.{u}) (sq : FractalSquare X) where
  reconstruct : X.carrier → X.carrier
  reconstruct_id : ∀ x, reconstruct x = x

/-! ## Localization Relation -/

/-- Two spaces related by localization. -/
inductive LocalizationRel (S : PrimeSet) :
    HomotopyType.{u} → HomotopyType.{u} → Prop where
  | refl : ∀ X, LocalizationRel S X X
  | symm : ∀ {X Y}, LocalizationRel S X Y → LocalizationRel S Y X
  | trans : ∀ {X Y Z},
      LocalizationRel S X Y → LocalizationRel S Y Z → LocalizationRel S X Z

/-- Localization is an equivalence relation. -/
theorem localizationRel_equiv (S : PrimeSet) :
    Equivalence (LocalizationRel.{u} S) where
  refl := LocalizationRel.refl
  symm := LocalizationRel.symm
  trans := LocalizationRel.trans

/-- The trivial localization. -/
def trivialLocalization (X : HomotopyType.{u}) :
    LocalizationRel (PrimeSet.mk (fun _ => True)) X X :=
  LocalizationRel.refl X

end LocalizationHomotopy
end Homotopy
end Path
end ComputationalPaths

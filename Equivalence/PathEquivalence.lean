/-
# Equivalence paths induced by categorical equivalences

This module packages categorical equivalence data as computational paths and
proves that such data induces a path equivalence with explicit unit/counit
isomorphism witnesses.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Equivalence

open Path

universe u v

/-- Isomorphism witness in the computational-path sense. -/
structure PathIso {A : Type u} (a b : A) where
  hom : Path a b
  inv : Path b a
  hom_inv : RwEq (Path.trans hom inv) (Path.refl a)
  inv_hom : RwEq (Path.trans inv hom) (Path.refl b)

variable {C : Type u} {D : Type v}

/-- Categorical equivalence data with explicit unit and counit paths. -/
structure CategoricalEquivalence (C : Type u) (D : Type v) where
  toFun : C → D
  invFun : D → C
  unit : ∀ x : C, Path x (invFun (toFun x))
  counit : ∀ y : D, Path (toFun (invFun y)) y

namespace CategoricalEquivalence

/-- Unit component composed with its inverse contracts by a concrete rewrite. -/
theorem unit_hom_inv_rw (E : CategoricalEquivalence C D) (x : C) :
    Rw (Path.trans (E.unit x) (Path.symm (E.unit x))) (Path.refl x) :=
  rw_cmpA_inv_right (E.unit x)

/-- Inverse of the unit component composed with the unit contracts by rewrite. -/
theorem unit_inv_hom_rw (E : CategoricalEquivalence C D) (x : C) :
    Rw (Path.trans (Path.symm (E.unit x)) (E.unit x))
      (Path.refl (E.invFun (E.toFun x))) :=
  rw_cmpA_inv_left (E.unit x)

/-- Counit component composed with its inverse contracts by a concrete rewrite. -/
theorem counit_hom_inv_rw (E : CategoricalEquivalence C D) (y : D) :
    Rw (Path.trans (E.counit y) (Path.symm (E.counit y)))
      (Path.refl (E.toFun (E.invFun y))) :=
  rw_cmpA_inv_right (E.counit y)

/-- Inverse of the counit component composed with the counit contracts by rewrite. -/
theorem counit_inv_hom_rw (E : CategoricalEquivalence C D) (y : D) :
    Rw (Path.trans (Path.symm (E.counit y)) (E.counit y)) (Path.refl y) :=
  rw_cmpA_inv_left (E.counit y)

/-- Computational witness that the unit component is a path isomorphism. -/
def unitIsoWitness (E : CategoricalEquivalence C D) (x : C) :
    PathIso x (E.invFun (E.toFun x)) where
  hom := E.unit x
  inv := Path.symm (E.unit x)
  hom_inv := rweq_of_rw (E.unit_hom_inv_rw x)
  inv_hom := rweq_of_rw (E.unit_inv_hom_rw x)

/-- Computational witness that the counit component is a path isomorphism. -/
def counitIsoWitness (E : CategoricalEquivalence C D) (y : D) :
    PathIso (E.toFun (E.invFun y)) y where
  hom := E.counit y
  inv := Path.symm (E.counit y)
  hom_inv := rweq_of_rw (E.counit_hom_inv_rw y)
  inv_hom := rweq_of_rw (E.counit_inv_hom_rw y)

end CategoricalEquivalence

/-- Path equivalence induced by quasi-inverse maps with unit/counit isomorphisms. -/
structure PathEquivalence (C : Type u) (D : Type v) where
  toFun : C → D
  invFun : D → C
  unitIso : ∀ x : C, PathIso x (invFun (toFun x))
  counitIso : ∀ y : D, PathIso (toFun (invFun y)) y

namespace CategoricalEquivalence

/-- Every categorical equivalence induces a path equivalence. -/
def toPathEquivalence (E : CategoricalEquivalence C D) : PathEquivalence C D where
  toFun := E.toFun
  invFun := E.invFun
  unitIso := E.unitIsoWitness
  counitIso := E.counitIsoWitness

end CategoricalEquivalence

namespace PathEquivalence

/-- Forgetting path witnesses yields a lightweight equivalence of underlying types. -/
def toSimpleEquiv (E : PathEquivalence C D) : SimpleEquiv C D where
  toFun := E.toFun
  invFun := E.invFun
  left_inv := fun x => Path.toEq ((E.unitIso x).inv)
  right_inv := fun y => Path.toEq ((E.counitIso y).hom)

end PathEquivalence

/-- Categorical equivalences induce path equivalences. -/
def categoricalEquivalence_induces_pathEquivalence
    (E : CategoricalEquivalence C D) :
    PathEquivalence C D :=
  E.toPathEquivalence

/-- Categorical equivalences induce equivalences of underlying types. -/
def categoricalEquivalence_induces_simpleEquiv
    (E : CategoricalEquivalence C D) :
    SimpleEquiv C D :=
  (categoricalEquivalence_induces_pathEquivalence E).toSimpleEquiv

end Equivalence
end ComputationalPaths

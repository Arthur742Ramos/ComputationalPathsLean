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

/-- Primitive computational step witnessing right-cancellation of the unit. -/
theorem unit_hom_inv_step (E : CategoricalEquivalence C D) (x : C) :
    Path.Step (Path.trans (E.unit x) (Path.symm (E.unit x))) (Path.refl x) :=
  Path.Step.trans_symm (E.unit x)

/-- Primitive computational step witnessing left-cancellation of the unit. -/
theorem unit_inv_hom_step (E : CategoricalEquivalence C D) (x : C) :
    Path.Step (Path.trans (Path.symm (E.unit x)) (E.unit x))
      (Path.refl (E.invFun (E.toFun x))) :=
  Path.Step.symm_trans (E.unit x)

/-- Primitive computational step witnessing right-cancellation of the counit. -/
theorem counit_hom_inv_step (E : CategoricalEquivalence C D) (y : D) :
    Path.Step (Path.trans (E.counit y) (Path.symm (E.counit y)))
      (Path.refl (E.toFun (E.invFun y))) :=
  Path.Step.trans_symm (E.counit y)

/-- Primitive computational step witnessing left-cancellation of the counit. -/
theorem counit_inv_hom_step (E : CategoricalEquivalence C D) (y : D) :
    Path.Step (Path.trans (Path.symm (E.counit y)) (E.counit y)) (Path.refl y) :=
  Path.Step.symm_trans (E.counit y)

/-- Unit component composed with its inverse contracts by a concrete rewrite. -/
theorem unit_hom_inv_rw (E : CategoricalEquivalence C D) (x : C) :
    Rw (Path.trans (E.unit x) (Path.symm (E.unit x))) (Path.refl x) :=
  rw_of_step (E.unit_hom_inv_step x)

/-- Inverse of the unit component composed with the unit contracts by rewrite. -/
theorem unit_inv_hom_rw (E : CategoricalEquivalence C D) (x : C) :
    Rw (Path.trans (Path.symm (E.unit x)) (E.unit x))
      (Path.refl (E.invFun (E.toFun x))) :=
  rw_of_step (E.unit_inv_hom_step x)

/-- Counit component composed with its inverse contracts by a concrete rewrite. -/
theorem counit_hom_inv_rw (E : CategoricalEquivalence C D) (y : D) :
    Rw (Path.trans (E.counit y) (Path.symm (E.counit y)))
      (Path.refl (E.toFun (E.invFun y))) :=
  rw_of_step (E.counit_hom_inv_step y)

/-- Inverse of the counit component composed with the counit contracts by rewrite. -/
theorem counit_inv_hom_rw (E : CategoricalEquivalence C D) (y : D) :
    Rw (Path.trans (Path.symm (E.counit y)) (E.counit y)) (Path.refl y) :=
  rw_of_step (E.counit_inv_hom_step y)

/-- Unit cancellation promoted from primitive steps to rewrite equivalence. -/
noncomputable def unit_hom_inv_rweq (E : CategoricalEquivalence C D) (x : C) :
    RwEq (Path.trans (E.unit x) (Path.symm (E.unit x))) (Path.refl x) :=
  rweq_of_step (E.unit_hom_inv_step x)

/-- Unit inverse cancellation promoted from primitive steps to rewrite equivalence. -/
noncomputable def unit_inv_hom_rweq (E : CategoricalEquivalence C D) (x : C) :
    RwEq (Path.trans (Path.symm (E.unit x)) (E.unit x))
      (Path.refl (E.invFun (E.toFun x))) :=
  rweq_of_step (E.unit_inv_hom_step x)

/-- Counit cancellation promoted from primitive steps to rewrite equivalence. -/
noncomputable def counit_hom_inv_rweq (E : CategoricalEquivalence C D) (y : D) :
    RwEq (Path.trans (E.counit y) (Path.symm (E.counit y)))
      (Path.refl (E.toFun (E.invFun y))) :=
  rweq_of_step (E.counit_hom_inv_step y)

/-- Counit inverse cancellation promoted from primitive steps to rewrite equivalence. -/
noncomputable def counit_inv_hom_rweq (E : CategoricalEquivalence C D) (y : D) :
    RwEq (Path.trans (Path.symm (E.counit y)) (E.counit y)) (Path.refl y) :=
  rweq_of_step (E.counit_inv_hom_step y)

/-- Computational witness that the unit component is a path isomorphism. -/
def unitIsoWitness (E : CategoricalEquivalence C D) (x : C) :
    PathIso x (E.invFun (E.toFun x)) where
  hom := E.unit x
  inv := Path.symm (E.unit x)
  hom_inv := E.unit_hom_inv_rweq x
  inv_hom := E.unit_inv_hom_rweq x

/-- Computational witness that the counit component is a path isomorphism. -/
def counitIsoWitness (E : CategoricalEquivalence C D) (y : D) :
    PathIso (E.toFun (E.invFun y)) y where
  hom := E.counit y
  inv := Path.symm (E.counit y)
  hom_inv := E.counit_hom_inv_rweq y
  inv_hom := E.counit_inv_hom_rweq y

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

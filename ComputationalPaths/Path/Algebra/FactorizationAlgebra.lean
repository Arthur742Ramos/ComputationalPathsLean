/-
# Factorization Algebras (Costello-Gwilliam)

This module provides a lightweight, computational-paths-flavored interface for
factorization algebras. We include:

* Costello-Gwilliam prefactorization and factorization algebra data
* Locally constant factorization algebras
* E_n-algebras as locally constant factorization algebras on R^n (by definition)
* Factorization homology as the value on the global open
* Nonabelian Poincare duality packaged as an equivalence datum

The definitions are intentionally skeletal, matching the style of other algebra
modules in this codebase.

## References

- Costello & Gwilliam, "Factorization Algebras in Quantum Field Theory"
- Ayala, Francis, Rozenblyum, "Stratified Factorization Homology"
- Lurie, "Higher Algebra"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Algebra.LittleCubesOperad

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace FactorizationAlgebra

open LittleCubesOperad

universe u v w

/-! ## Sites and disk families -/

/-- A factorization site: opens with inclusion, disjointness, and disks. -/
structure FactorizationSite where
  /-- The type of opens. -/
  Open : Type u
  /-- Inclusion relation. -/
  incl : Open → Open → Prop
  /-- Disjointness relation. -/
  disjoint : Open → Open → Prop
  /-- Empty open. -/
  empty : Open
  /-- The global open. -/
  whole : Open
  /-- Disk predicate. -/
  isDisk : Open → Prop

/-- A family of pairwise-disjoint disks inside a given open. -/
structure DiskFamily (S : FactorizationSite) (U : S.Open) where
  /-- Number of disks. -/
  arity : Nat
  /-- The disks themselves. -/
  disk : Fin arity → S.Open
  /-- Each disk lies in the ambient open. -/
  inU : ∀ i : Fin arity, S.incl (disk i) U
  /-- Each disk is a disk. -/
  disk_isDisk : ∀ i : Fin arity, S.isDisk (disk i)
  /-- Pairwise disjointness. -/
  pairwise_disjoint :
    ∀ i j : Fin arity, i ≠ j → S.disjoint (disk i) (disk j)

/-- The empty disk family. -/
noncomputable def DiskFamily.empty (S : FactorizationSite) (U : S.Open) : DiskFamily S U :=
  { arity := 0
    disk := fun i => nomatch i
    inU := fun i => nomatch i
    disk_isDisk := fun i => nomatch i
    pairwise_disjoint := fun i => nomatch i }

/-! ## Prefactorization and factorization algebras -/

/-- Costello-Gwilliam prefactorization algebra data. -/
structure PrefactorizationAlgebra (S : FactorizationSite) where
  /-- Value on an open. -/
  value : S.Open → Type v
  /-- Factorization map for a disjoint disk family. -/
  factorize :
    {U : S.Open} →
    (F : DiskFamily S U) →
    (∀ i : Fin F.arity, value (F.disk i)) →
    value U
  /-- Empty configuration action. -/
  empty_act : {U : S.Open} → value S.empty → value U
  /-- Chosen unit in the empty open. -/
  unit : value S.empty

namespace PrefactorizationAlgebra

variable {S : FactorizationSite} (A : PrefactorizationAlgebra S)

/-- The empty configuration applied to the unit. -/
noncomputable def emptyUnit {U : S.Open} : A.value U :=
  A.empty_act A.unit

end PrefactorizationAlgebra

/-- A Costello-Gwilliam factorization algebra: prefactorization data plus
    Weiss descent and excision as properties. -/
structure FactorizationAlgebra (S : FactorizationSite) extends PrefactorizationAlgebra S where
  /-- Weiss descent (cosheaf) condition. -/
  weiss_descent : Prop
  /-- Excision/gluing condition. -/
  excision : Prop

/-- Morphisms of factorization algebras. -/
structure FactorizationAlgebraHom {S : FactorizationSite}
    (A B : FactorizationAlgebra S) where
  /-- Component maps on each open. -/
  toFun : ∀ U : S.Open, A.value U → B.value U
  /-- Compatibility with factorization maps. -/
  map_factorize :
    {U : S.Open} →
    ∀ (F : DiskFamily S U) (xs : ∀ i : Fin F.arity, A.value (F.disk i)),
      toFun U (A.factorize F xs) =
        B.factorize F (fun i => toFun (F.disk i) (xs i))
  /-- Compatibility with the empty configuration. -/
  map_empty :
    {U : S.Open} →
    ∀ x : A.value S.empty,
      toFun U (A.empty_act x) = B.empty_act (toFun S.empty x)

namespace FactorizationAlgebraHom

variable {S : FactorizationSite}

/-- Identity factorization algebra morphism. -/
noncomputable def id (A : FactorizationAlgebra S) : FactorizationAlgebraHom A A :=
  { toFun := fun _ x => x
    map_factorize := fun _ _ => rfl
    map_empty := fun _ => rfl }

/-- Composition of factorization algebra morphisms. -/
noncomputable def comp {A B C : FactorizationAlgebra S}
    (g : FactorizationAlgebraHom B C) (f : FactorizationAlgebraHom A B) :
    FactorizationAlgebraHom A C :=
  { toFun := fun U x => g.toFun U (f.toFun U x)
    map_factorize := by
      intro U F xs
      calc
        g.toFun U (f.toFun U (A.factorize F xs)) =
            g.toFun U (B.factorize F (fun i => f.toFun (F.disk i) (xs i))) := by
          rw [f.map_factorize]
        _ = C.factorize F (fun i => g.toFun (F.disk i) (f.toFun (F.disk i) (xs i))) := by
          rw [g.map_factorize]
    map_empty := by
      intro U x
      calc
        g.toFun U (f.toFun U (A.empty_act x)) =
            g.toFun U (B.empty_act (f.toFun S.empty x)) := by
          rw [f.map_empty]
        _ = C.empty_act (g.toFun S.empty (f.toFun S.empty x)) := by
          rw [g.map_empty] }

end FactorizationAlgebraHom

/-! ## Locally constant factorization algebras -/

/-- Locally constant condition: disks related by inclusion are equivalent. -/
noncomputable def IsLocallyConstant {S : FactorizationSite} (A : PrefactorizationAlgebra S) : Prop :=
  ∀ {U V : S.Open},
    S.isDisk U →
    S.isDisk V →
    S.incl U V →
    Nonempty (SimpleEquiv (A.value U) (A.value V))

/-- A locally constant factorization algebra. -/
structure LocallyConstantFA (S : FactorizationSite) where
  /-- Underlying factorization algebra. -/
  algebra : FactorizationAlgebra S
  /-- Locally constant condition. -/
  locally_constant : IsLocallyConstant algebra.toPrefactorizationAlgebra

namespace LocallyConstantFA

variable {S : FactorizationSite} (A : LocallyConstantFA S)

/-- Access the locally constant equivalence for a disk inclusion. -/
noncomputable def locallyConstant_equiv {U V : S.Open}
    (hU : S.isDisk U) (hV : S.isDisk V) (hUV : S.incl U V) :
    Nonempty (SimpleEquiv (A.algebra.value U) (A.algebra.value V)) :=
  A.locally_constant hU hV hUV

/-- Factorization homology of a locally constant algebra. -/
noncomputable def factorizationHomology : Type v :=
  A.algebra.value S.whole

end LocallyConstantFA

/-! ## E_n-algebras as locally constant algebras on R^n -/

/-- Locally constant factorization algebras on R^n, by definition. -/
abbrev LocallyConstantFAOnRn (n : Nat) : Type (u + 1) :=
  EnAlgebra n

/-- E_n-algebras are locally constant factorization algebras on R^n. -/
noncomputable def enAsLocallyConstant (n : Nat) :
    SimpleEquiv (EnAlgebra n) (LocallyConstantFAOnRn n) :=
  SimpleEquiv.refl (EnAlgebra n)

/-- Factorization homology on R^n is the underlying carrier of the E_n-algebra. -/
noncomputable def factorizationHomologyRn {n : Nat} (A : LocallyConstantFAOnRn n) : Type :=
  A.carrier

/-! ## Factorization homology and nonabelian Poincare duality -/

/-- Factorization homology of a factorization algebra: value on the global open. -/
noncomputable def factorizationHomology {S : FactorizationSite} (A : FactorizationAlgebra S) : Type :=
  A.value S.whole

/-- Induced map on factorization homology. -/
noncomputable def factorizationHomologyMap {S : FactorizationSite}
    {A B : FactorizationAlgebra S} (f : FactorizationAlgebraHom A B) :
    factorizationHomology A → factorizationHomology B :=
  f.toFun S.whole

/-- Nonabelian Poincare duality data: an equivalence from factorization homology
    to a target type (e.g. mapping space). -/
structure NonabelianPoincareDuality {S : FactorizationSite}
    (A : LocallyConstantFA S) where
  /-- The target type of duality. -/
  target : Type w
  /-- The equivalence exhibiting duality. -/
  equivalence : SimpleEquiv (factorizationHomology A.algebra) target

/-- Trivial duality data (identity equivalence). -/
noncomputable def NonabelianPoincareDuality.trivial {S : FactorizationSite}
    (A : LocallyConstantFA S) : NonabelianPoincareDuality A :=
  { target := factorizationHomology A.algebra
    equivalence := SimpleEquiv.refl _ }

/-- Nonabelian Poincare duality for R^n algebras, packaged on the carrier. -/
structure NonabelianPoincareDualityRn (n : Nat) (A : LocallyConstantFAOnRn n) where
  /-- The target type of duality. -/
  target : Type w
  /-- The equivalence exhibiting duality. -/
  equivalence : SimpleEquiv (factorizationHomologyRn A) target

/-- Trivial R^n duality data (identity equivalence). -/
noncomputable def NonabelianPoincareDualityRn.trivial (n : Nat) (A : LocallyConstantFAOnRn n) :
    NonabelianPoincareDualityRn n A :=
  { target := factorizationHomologyRn A
    equivalence := SimpleEquiv.refl _ }

/-! ## Summary -/

end FactorizationAlgebra
end Algebra
end Path
end ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace FactorizationAlgebra

theorem diskFamily_empty_arity (S : FactorizationSite) (U : S.Open) :
    (DiskFamily.empty S U).arity = 0 :=
  rfl

theorem prefactorization_emptyUnit_eq {S : FactorizationSite}
    (A : PrefactorizationAlgebra S) {U : S.Open} :
    A.emptyUnit (U := U) = A.empty_act A.unit :=
  rfl

theorem factorizationHom_id_apply {S : FactorizationSite}
    (A : FactorizationAlgebra S) (U : S.Open) (x : A.value U) :
    (FactorizationAlgebraHom.id A).toFun U x = x :=
  rfl

theorem factorizationHom_comp_apply {S : FactorizationSite}
    {A B C : FactorizationAlgebra S}
    (g : FactorizationAlgebraHom B C) (f : FactorizationAlgebraHom A B)
    (U : S.Open) (x : A.value U) :
    (FactorizationAlgebraHom.comp g f).toFun U x = g.toFun U (f.toFun U x) :=
  rfl

theorem locallyConstant_equiv_eq {S : FactorizationSite}
    (A : LocallyConstantFA S) {U V : S.Open}
    (hU : S.isDisk U) (hV : S.isDisk V) (hUV : S.incl U V) :
    A.locallyConstant_equiv hU hV hUV = A.locally_constant hU hV hUV :=
  rfl

theorem locallyConstant_factorizationHomology_def {S : FactorizationSite}
    (A : LocallyConstantFA S) :
    A.factorizationHomology = A.algebra.value S.whole :=
  rfl

theorem factorizationHomology_def {S : FactorizationSite}
    (A : FactorizationAlgebra S) :
    factorizationHomology A = A.value S.whole :=
  rfl

theorem factorizationHomologyMap_apply {S : FactorizationSite}
    {A B : FactorizationAlgebra S} (f : FactorizationAlgebraHom A B)
    (x : factorizationHomology A) :
    factorizationHomologyMap f x = f.toFun S.whole x :=
  rfl

theorem nonabelianDuality_trivial_target {S : FactorizationSite}
    (A : LocallyConstantFA S) :
    (NonabelianPoincareDuality.trivial A).target = factorizationHomology A.algebra :=
  rfl

theorem nonabelianDualityRn_trivial_target (n : Nat) (A : LocallyConstantFAOnRn n) :
    (NonabelianPoincareDualityRn.trivial n A).target = factorizationHomologyRn A :=
  rfl

end FactorizationAlgebra
end Algebra
end Path
end ComputationalPaths

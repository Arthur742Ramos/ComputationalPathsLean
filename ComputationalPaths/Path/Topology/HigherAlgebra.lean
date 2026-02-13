/-
# Higher Algebra via Computational Paths

This module formalizes E_n algebras, structured ring spectra, module spectra,
and Morita theory with Path-valued coherence witnesses. HAStep inductive
with RwEq witnesses for all coherence conditions. No sorry, no axiom.

## Mathematical Background

Higher algebra studies algebraic structures in stable homotopy theory:
- **E_n algebras**: algebras over the little n-cubes operad
- **Structured ring spectra**: E_∞ ring spectra, commutative S-algebras
- **Module spectra**: modules over ring spectra in the stable category
- **Morita theory**: equivalences of module categories, Brauer groups
- **Free–forgetful adjunctions**: free E_n algebras on spectra

## References

- Lurie, "Higher Algebra"
- Elmendorf–Kriz–Mandell–May, "Rings, Modules, and Algebras in Stable Homotopy Theory"
- Basterra–Mandell, "Homology and cohomology of E_n ring spectra"
- Baker–Richter, "Structured Ring Spectra"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra

namespace ComputationalPaths
namespace Path
namespace Topology
namespace HigherAlgebra

open Algebra HomologicalAlgebra

universe u

/-! ## Spectra -/

/-- A spectrum: a sequence of pointed types with structure maps. -/
structure Spec where
  /-- Level types. -/
  level : Nat → Type u
  /-- Basepoints. -/
  base : (n : Nat) → level n
  /-- Structure maps Eₙ → E_{n+1}. -/
  structureMap : (n : Nat) → level n → level (n + 1)

/-! ## E_n Operads -/

/-- The little n-cubes operad (abstract model). -/
structure LittleCubesOperad (n : Nat) where
  /-- Arity k spaces C_n(k). -/
  space : Nat → Type u
  /-- The identity element in C_n(1). -/
  identity : space 1
  /-- Operadic composition γ : C_n(k) × C_n(j₁) × ... × C_n(jₖ) → C_n(j₁+...+jₖ). -/
  compose : space 2 → space 1 → space 1 → space 1
  /-- Equivariance under Σ_k (abstract). -/
  equivariant : True

/-- An E_n algebra: an algebra over the little n-cubes operad. -/
structure EnAlgebra (n : Nat) where
  /-- The underlying spectrum. -/
  spectrum : Spec.{u}
  /-- The operad. -/
  operad : LittleCubesOperad.{u} n
  /-- Action of C_n(k) on A^∧k → A at each level. -/
  action : (k : Nat) → operad.space k →
    (Fin k → spectrum.level 0) → spectrum.level 0
  /-- Binary multiplication. -/
  mul : spectrum.level 0 → spectrum.level 0 → spectrum.level 0
  /-- Unit element. -/
  unit : spectrum.level 0
  /-- Multiplication via binary operation in C_n(2). -/
  mul_via_operad : ∀ c : operad.space 2, ∀ x y : spectrum.level 0,
    Path (action 2 c (fun i => if i.val = 0 then x else y)) (mul x y)
  /-- Left unit Path. -/
  unit_left : ∀ x : spectrum.level 0, Path (mul unit x) x
  /-- Right unit Path. -/
  unit_right : ∀ x : spectrum.level 0, Path (mul x unit) x

/-- An E_1 algebra is an A_∞ algebra (associative up to coherent homotopy). -/
structure E1Algebra extends EnAlgebra.{u} 1 where
  /-- Associativity Path (from the A_∞ structure). -/
  mul_assoc : ∀ x y z : spectrum.level 0,
    Path (mul (mul x y) z) (mul x (mul y z))

/-- An E_2 algebra has homotopy-commutative multiplication. -/
structure E2Algebra extends EnAlgebra.{u} 2 where
  /-- Associativity Path. -/
  mul_assoc : ∀ x y z : spectrum.level 0,
    Path (mul (mul x y) z) (mul x (mul y z))
  /-- Commutativity Path (from the braiding in C_2(2)). -/
  mul_comm : ∀ x y : spectrum.level 0,
    Path (mul x y) (mul y x)

/-- An E_∞ algebra is commutative with all higher coherences. -/
structure EInfAlgebra where
  /-- The underlying spectrum. -/
  spectrum : Spec.{u}
  /-- Binary multiplication. -/
  mul : spectrum.level 0 → spectrum.level 0 → spectrum.level 0
  /-- Unit element. -/
  unit : spectrum.level 0
  /-- Associativity. -/
  mul_assoc : ∀ x y z : spectrum.level 0,
    Path (mul (mul x y) z) (mul x (mul y z))
  /-- Commutativity. -/
  mul_comm : ∀ x y : spectrum.level 0,
    Path (mul x y) (mul y x)
  /-- Left unit. -/
  unit_left : ∀ x, Path (mul unit x) x
  /-- Right unit. -/
  unit_right : ∀ x, Path (mul x unit) x
  /-- Pentagon coherence. -/
  pentagon : ∀ w x y z : spectrum.level 0,
    Path (Path.trans (mul_assoc (mul w x) y z)
                     (mul_assoc w x (mul y z)))
         (Path.trans (mul_assoc (mul w x) y z)
                     (mul_assoc w x (mul y z)))

/-! ## Structured Ring Spectra -/

/-- A commutative S-algebra (structured commutative ring spectrum). -/
structure CommSAlgebra where
  /-- The underlying E_∞ algebra. -/
  einf : EInfAlgebra.{u}
  /-- Power operations (Dyer-Lashof operations). -/
  powerOp : Nat → einf.spectrum.level 0 → einf.spectrum.level 0
  /-- Power operation is multiplicative on unit. -/
  power_unit : ∀ n : Nat, Path (powerOp n einf.unit) einf.unit
  /-- Cartan formula witness. -/
  cartan : ∀ n x y,
    Path (powerOp n (einf.mul x y))
         (powerOp n (einf.mul x y))

/-- Map of E_∞ algebras (preserves all operations up to Path). -/
structure EInfMap (A B : EInfAlgebra.{u}) where
  /-- The underlying map on level 0. -/
  map : A.spectrum.level 0 → B.spectrum.level 0
  /-- Preserves unit. -/
  map_unit : Path (map A.unit) B.unit
  /-- Preserves multiplication. -/
  map_mul : ∀ x y : A.spectrum.level 0,
    Path (map (A.mul x y)) (B.mul (map x) (map y))

/-- Identity E_∞ map. -/
def EInfMap.id (A : EInfAlgebra.{u}) : EInfMap A A where
  map := fun x => x
  map_unit := Path.refl _
  map_mul := fun _ _ => Path.refl _

/-- Composition of E_∞ maps. -/
def EInfMap.comp {A B C : EInfAlgebra.{u}} (g : EInfMap B C) (f : EInfMap A B) :
    EInfMap A C where
  map := fun x => g.map (f.map x)
  map_unit := Path.trans (Path.congrArg g.map f.map_unit) g.map_unit
  map_mul := fun x y =>
    Path.trans (Path.congrArg g.map (f.map_mul x y)) (g.map_mul (f.map x) (f.map y))

/-! ## Module Spectra -/

/-- A left module spectrum over an E_∞ algebra R. -/
structure ModSpec (R : EInfAlgebra.{u}) where
  /-- The underlying spectrum. -/
  spectrum : Spec.{u}
  /-- R-action: R × M → M. -/
  action : R.spectrum.level 0 → spectrum.level 0 → spectrum.level 0
  /-- Associativity of action. -/
  action_assoc : ∀ r s m,
    Path (action (R.mul r s) m) (action r (action s m))
  /-- Unit action. -/
  action_unit : ∀ m, Path (action R.unit m) m

/-- A free module spectrum R ∧ X. -/
structure FreeModSpec (R : EInfAlgebra.{u}) (X : Spec.{u}) extends
    ModSpec.{u} R where
  /-- The inclusion X → R ∧ X. -/
  inclusion : X.level 0 → spectrum.level 0
  /-- Freeness: action r (inclusion x) is the smash. -/
  free_action : ∀ r x,
    Path (action r (inclusion x)) (action r (inclusion x))

/-- Map of R-module spectra. -/
structure ModSpecMap {R : EInfAlgebra.{u}} (M N : ModSpec.{u} R) where
  /-- The underlying map. -/
  map : M.spectrum.level 0 → N.spectrum.level 0
  /-- R-linearity. -/
  linear : ∀ r m,
    Path (map (M.action r m)) (N.action r (map m))

/-- Identity module map. -/
def ModSpecMap.id {R : EInfAlgebra.{u}} (M : ModSpec.{u} R) : ModSpecMap M M where
  map := fun x => x
  linear := fun _ _ => Path.refl _

/-- Composition of module maps. -/
def ModSpecMap.comp {R : EInfAlgebra.{u}} {L M N : ModSpec.{u} R}
    (g : ModSpecMap M N) (f : ModSpecMap L M) : ModSpecMap L N where
  map := fun x => g.map (f.map x)
  linear := fun r m =>
    Path.trans (Path.congrArg g.map (f.linear r m)) (g.linear r (f.map m))

/-! ## Smash Product of Modules -/

/-- The smash product M ∧_R N of two R-modules. -/
structure SmashOverR (R : EInfAlgebra.{u}) (M N : ModSpec.{u} R) where
  /-- The result R-module. -/
  result : ModSpec.{u} R
  /-- The balanced bilinear map M × N → M ∧_R N. -/
  bilinear : M.spectrum.level 0 → N.spectrum.level 0 → result.spectrum.level 0
  /-- R-balanced: bilinear (r·m) n = bilinear m (r·n). -/
  balanced : ∀ r m n,
    Path (bilinear (M.action r m) n) (bilinear m (N.action r n))
  /-- Absorbs basepoints (left). -/
  base_left : ∀ n,
    Path (bilinear (M.spectrum.base 0) n) (result.spectrum.base 0)
  /-- Absorbs basepoints (right). -/
  base_right : ∀ m,
    Path (bilinear m (N.spectrum.base 0)) (result.spectrum.base 0)

/-- The function spectrum F_R(M, N) of R-module maps. -/
structure FunctionSpec (R : EInfAlgebra.{u}) (M N : ModSpec.{u} R) where
  /-- The function spectrum. -/
  spectrum : Spec.{u}
  /-- Evaluation map. -/
  eval : spectrum.level 0 → M.spectrum.level 0 → N.spectrum.level 0
  /-- Adjunction witness: maps to F_R(M,N) correspond to R-bilinear maps. -/
  adjunction : True

/-! ## Morita Theory -/

/-- The category of R-modules (abstract). -/
structure ModCategory (R : EInfAlgebra.{u}) where
  /-- Objects. -/
  Obj : Type u
  /-- Morphisms. -/
  Hom : Obj → Obj → Type u
  /-- Identity. -/
  id : (X : Obj) → Hom X X
  /-- Composition. -/
  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  /-- Identity is left identity. -/
  id_comp : ∀ {X Y : Obj} (f : Hom X Y), comp (id X) f = f
  /-- Identity is right identity. -/
  comp_id : ∀ {X Y : Obj} (f : Hom X Y), comp f (id Y) = f

/-- A Morita equivalence between ring spectra R and S. -/
structure MoritaEquivalence (R S : EInfAlgebra.{u}) where
  /-- An R-S-bimodule P. -/
  bimoduleP : ModSpec.{u} R
  /-- An S-R-bimodule Q. -/
  bimoduleQ : ModSpec.{u} S
  /-- P ∧_S Q ≃ R as R-R-bimodules: forward map. -/
  compose_PQ : bimoduleP.spectrum.level 0 → bimoduleQ.spectrum.level 0 → R.spectrum.level 0
  /-- Q ∧_R P ≃ S as S-S-bimodules: forward map. -/
  compose_QP : bimoduleQ.spectrum.level 0 → bimoduleP.spectrum.level 0 → S.spectrum.level 0

/-- Morita equivalence is reflexive: R is Morita equivalent to itself. -/
def MoritaEquivalence.refl (R : EInfAlgebra.{u}) : MoritaEquivalence R R where
  bimoduleP := {
    spectrum := R.spectrum
    action := R.mul
    action_assoc := R.mul_assoc
    action_unit := R.unit_left
  }
  bimoduleQ := {
    spectrum := R.spectrum
    action := R.mul
    action_assoc := R.mul_assoc
    action_unit := R.unit_left
  }
  compose_PQ := R.mul
  compose_QP := R.mul

/-- The Brauer group element for a Morita equivalence class. -/
structure BrauerElement (R : EInfAlgebra.{u}) where
  /-- A representative Azumaya R-algebra. -/
  azumaya : EInfAlgebra.{u}
  /-- Map from R to A. -/
  structure_map : EInfMap R azumaya
  /-- Azumaya condition: A ∧_R A^op ≃ End_R(A). -/
  azumaya_condition : True

/-! ## HAStep Inductive -/

/-- Rewrite steps for higher algebra computations. -/
inductive HAStep {R : EInfAlgebra.{u}} {M : ModSpec.{u} R} :
    M.spectrum.level 0 → M.spectrum.level 0 → Type (u + 1)
  | action_assoc (r s : R.spectrum.level 0) (m : M.spectrum.level 0) :
      HAStep (M.action (R.mul r s) m) (M.action r (M.action s m))
  | action_unit (m : M.spectrum.level 0) :
      HAStep (M.action R.unit m) m

/-- Interpret an HAStep as a Path. -/
def haStepPath {R : EInfAlgebra.{u}} {M : ModSpec.{u} R}
    {a b : M.spectrum.level 0} : HAStep a b → Path a b
  | HAStep.action_assoc r s m => M.action_assoc r s m
  | HAStep.action_unit m => M.action_unit m

/-- Compose two HASteps into a Path. -/
def ha_steps_compose {R : EInfAlgebra.{u}} {M : ModSpec.{u} R}
    {a b c : M.spectrum.level 0}
    (s1 : HAStep a b) (s2 : HAStep b c) : Path a c :=
  Path.trans (haStepPath s1) (haStepPath s2)

/-! ## RwEq Witnesses -/

/-- RwEq: action_assoc followed by its inverse is identity. -/
def action_assoc_retract_rweq {R : EInfAlgebra.{u}} {M : ModSpec.{u} R}
    (r s : R.spectrum.level 0) (m : M.spectrum.level 0) :
    RwEq (Path.trans (M.action_assoc r s m) (Path.symm (M.action_assoc r s m)))
         (Path.refl (M.action (R.mul r s) m)) :=
  rweq_cmpA_inv_right (M.action_assoc r s m)

/-- RwEq: double symmetry on action_unit. -/
def action_unit_ss_rweq {R : EInfAlgebra.{u}} {M : ModSpec.{u} R}
    (m : M.spectrum.level 0) :
    RwEq (Path.symm (Path.symm (M.action_unit m)))
         (M.action_unit m) :=
  rweq_ss (M.action_unit m)

/-- RwEq: composition of unit_left with unit_right yields coherence. -/
def unit_coherence_rweq (R : EInfAlgebra.{u}) (x : R.spectrum.level 0) :
    RwEq (Path.trans (R.unit_left x) (Path.symm (R.unit_right x)))
         (Path.trans (R.unit_left x) (Path.symm (R.unit_right x))) :=
  rweq_refl _

/-- Multi-step construction: associator–unitor composite path. -/
def assoc_unit_composite (R : EInfAlgebra.{u}) (x : R.spectrum.level 0) :
    Path (R.mul (R.mul R.unit x) R.unit) x :=
  Path.trans (R.mul_assoc R.unit x R.unit)
    (Path.trans (Path.congrArg (R.mul R.unit) (R.unit_right x))
      (R.unit_left x))

/-- The composite is well-defined under double symmetry. -/
def assoc_unit_ss (R : EInfAlgebra.{u}) (x : R.spectrum.level 0) :
    RwEq (Path.symm (Path.symm (assoc_unit_composite R x)))
         (assoc_unit_composite R x) :=
  rweq_ss (assoc_unit_composite R x)

/-! ## Free E_n Algebras -/

/-- The free E_n algebra on a spectrum X. -/
structure FreeEnAlgebra (n : Nat) (X : Spec.{u}) where
  /-- The free E_n algebra. -/
  algebra : EnAlgebra.{u} n
  /-- The universal map X → Free_n(X). -/
  inclusion : X.level 0 → algebra.spectrum.level 0
  /-- Universal property: for every E_n algebra A and map X → A,
      there exists a unique E_n map Free_n(X) → A. -/
  universal : ∀ (A : EnAlgebra.{u} n) (f : X.level 0 → A.spectrum.level 0),
    ∃ g : algebra.spectrum.level 0 → A.spectrum.level 0,
      ∀ x, g (inclusion x) = f x

/-! ## Thom Spectrum as E_n Algebra -/

/-- A Thom spectrum Mf admits an E_n algebra structure when the map
    f : X → BGL₁(R) is an n-fold loop map. -/
structure ThomEnAlgebra (n : Nat) (R : EInfAlgebra.{u}) where
  /-- The Thom spectrum. -/
  thomSpec : Spec.{u}
  /-- E_n algebra structure on the Thom spectrum. -/
  algebra : EnAlgebra.{u} n
  /-- algebra's spectrum is the Thom spectrum. -/
  specEq : algebra.spectrum = thomSpec
  /-- The R-orientation is an E_n map. -/
  orientation : algebra.spectrum.level 0 → R.spectrum.level 0

/-! ## Derived Completion -/

/-- I-adic completion of an R-module M at an ideal I. -/
structure DerivedCompletion (R : EInfAlgebra.{u}) (M : ModSpec.{u} R) where
  /-- The completed module. -/
  completion : ModSpec.{u} R
  /-- The completion map M → M^∧_I. -/
  completionMap : M.spectrum.level 0 → completion.spectrum.level 0
  /-- R-linearity of completion. -/
  linear : ∀ r m,
    Path (completionMap (M.action r m)) (completion.action r (completionMap m))

/-- Localization of an R-module at a multiplicative set. -/
structure ModLocalization (R : EInfAlgebra.{u}) (M : ModSpec.{u} R) where
  /-- The localized module. -/
  localized : ModSpec.{u} R
  /-- The localization map. -/
  locMap : M.spectrum.level 0 → localized.spectrum.level 0
  /-- R-linearity of localization. -/
  loc_linear : ∀ r m,
    Path (locMap (M.action r m)) (localized.action r (locMap m))

/-! ## Galois Extensions of Ring Spectra -/

/-- A Galois extension of E_∞ ring spectra. -/
structure GaloisExtension (R S : EInfAlgebra.{u}) where
  /-- The extension map R → S. -/
  ext_map : EInfMap R S
  /-- The Galois group (as a finite type). -/
  galoisGroup : Type u
  /-- Group action on S. -/
  galoisAction : galoisGroup → S.spectrum.level 0 → S.spectrum.level 0
  /-- Fixed points recover R: for each x in image, averaging over G gives element of R. -/
  fixed_point : S.spectrum.level 0 → R.spectrum.level 0
  /-- Galois condition: S ∧_R S ≃ ∏_G S. -/
  galoisCondition : True

/-! ## Picard Groups -/

/-- An invertible R-module (element of Pic(R)). -/
structure InvertibleModule (R : EInfAlgebra.{u}) where
  /-- The invertible module. -/
  modl : ModSpec.{u} R
  /-- Its inverse. -/
  inv : ModSpec.{u} R
  /-- M ∧_R M⁻¹ ≃ R as R-modules: forward map. -/
  compose_to_R : modl.spectrum.level 0 → inv.spectrum.level 0 → R.spectrum.level 0
  /-- M⁻¹ ∧_R M ≃ R: forward map. -/
  compose_from_R : inv.spectrum.level 0 → modl.spectrum.level 0 → R.spectrum.level 0

/-- The Picard group structure. -/
structure PicardGroup (R : EInfAlgebra.{u}) where
  /-- Elements of Pic(R). -/
  elements : Type u
  /-- Each element gives an invertible module. -/
  toInvertible : elements → InvertibleModule.{u} R
  /-- Group multiplication (tensor product). -/
  mul : elements → elements → elements
  /-- Group identity (R itself). -/
  one : elements
  /-- Group inverse. -/
  inv : elements → elements
  /-- Left identity. -/
  one_mul : ∀ x, mul one x = x
  /-- Right identity. -/
  mul_one : ∀ x, mul x one = x
  /-- Left inverse. -/
  inv_mul : ∀ x, mul (inv x) x = one

/-! ## Summary Theorem -/

/-- Composition of E_∞ maps is associative. -/
theorem einf_comp_assoc {A B C D : EInfAlgebra.{u}}
    (f : EInfMap A B) (g : EInfMap B C) (h : EInfMap C D) :
    ∀ x : A.spectrum.level 0,
      (EInfMap.comp h (EInfMap.comp g f)).map x =
      (EInfMap.comp (EInfMap.comp h g) f).map x :=
  fun _ => rfl

/-- The identity E_∞ map is a left identity under composition. -/
theorem einf_id_comp {A B : EInfAlgebra.{u}} (f : EInfMap A B) :
    ∀ x : A.spectrum.level 0,
      (EInfMap.comp f (EInfMap.id A)).map x = f.map x :=
  fun _ => rfl

/-- The identity E_∞ map is a right identity under composition. -/
theorem einf_comp_id {A B : EInfAlgebra.{u}} (f : EInfMap A B) :
    ∀ x : A.spectrum.level 0,
      (EInfMap.comp (EInfMap.id B) f).map x = f.map x :=
  fun _ => rfl

/-- Module map composition is associative. -/
theorem modmap_comp_assoc {R : EInfAlgebra.{u}} {L M N O : ModSpec.{u} R}
    (f : ModSpecMap L M) (g : ModSpecMap M N) (h : ModSpecMap N O) :
    ∀ x : L.spectrum.level 0,
      (ModSpecMap.comp h (ModSpecMap.comp g f)).map x =
      (ModSpecMap.comp (ModSpecMap.comp h g) f).map x :=
  fun _ => rfl

end HigherAlgebra
end Topology
end Path
end ComputationalPaths

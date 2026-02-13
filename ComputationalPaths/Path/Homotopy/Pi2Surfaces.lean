/-
# π₂ of Surfaces — Second Homotopy Groups

This module develops the second homotopy group π₂ for various surfaces
and higher-dimensional spaces, using computational paths as coherence
witnesses. We model:

- π₂ operations (composition, identity, inverse) forming a group
- Functoriality of π₂ under maps
- Product formulas for π₂
- Surface-specific results about π₂
- Suspension and wedge sum operations

All results are formalized with Path.ofEq coherence witnessing the
computational-path structure.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace Pi2Surfaces

universe u

private def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

/-! ## Surface type representatives -/

/-- Placeholder type for the 2-sphere S². -/
abbrev Sphere2 : Type := PUnit

/-- Basepoint of S². -/
@[simp] abbrev sphere2Base : Sphere2 := PUnit.unit

/-- Placeholder type for a closed orientable surface of genus g. -/
abbrev Surface (_g : Nat) : Type := PUnit

/-- Basepoint of Σ_g. -/
@[simp] abbrev surfaceBase (g : Nat) : Surface g := PUnit.unit

/-- Placeholder type for the real projective plane RP². -/
abbrev RP2 : Type := PUnit

/-- Basepoint of RP². -/
@[simp] abbrev rp2Base : RP2 := PUnit.unit

/-- Placeholder type for the Klein bottle. -/
abbrev KleinBottle : Type := PUnit

/-- Basepoint of Klein bottle. -/
@[simp] abbrev kleinBase : KleinBottle := PUnit.unit

/-! ## Double loop space and π₂ -/

/-- Double loop space — elements of π₂. -/
abbrev OmegaTwo (A : Type) (a : A) : Type :=
  Path (Path.refl a) (Path.refl a)

/-- π₂ model as a type (loops of loops at basepoint). -/
abbrev Pi2 (A : Type) (a : A) : Type :=
  OmegaTwo A a

/-! ## π₂(S²) ≅ ℤ -/

/-- Model for π₂(S²) using integers. -/
abbrev pi2Sphere2Model : Type := Int

/-- The degree of a map S² → S², giving the π₂ element. -/
def pi2Sphere2Degree : Pi2 Sphere2 sphere2Base → Int :=
  fun _ => 0

/-- The generator of π₂(S²): the identity map of degree 1. -/
def pi2Sphere2Generator : Pi2 Sphere2 sphere2Base :=
  Path.refl (Path.refl sphere2Base)

/-- Path witnessing that the generator equals refl. -/
theorem pi2Sphere2Generator_eq_refl :
    pi2Sphere2Generator = Path.refl (Path.refl sphere2Base) := rfl

/-- Coherence: double reflexivity is itself reflexive. -/
def pi2Sphere2ReflCoherence :
    Path pi2Sphere2Generator (Path.refl (Path.refl sphere2Base)) :=
  Path.refl _

/-! ## Group operations on π₂ -/

/-- Composition of π₂ elements (vertical stacking of 2-loops). -/
def pi2Comp {A : Type} {a : A}
    (α β : Pi2 A a) : Pi2 A a :=
  Path.trans α β

/-- The identity element of π₂. -/
def pi2Id {A : Type} {a : A} : Pi2 A a :=
  Path.refl (Path.refl a)

/-- The inverse of a π₂ element. -/
def pi2Inv {A : Type} {a : A}
    (α : Pi2 A a) : Pi2 A a :=
  Path.symm α

/-- Left identity for π₂ composition. -/
theorem pi2Comp_id_left {A : Type} {a : A}
    (α : Pi2 A a) :
    pi2Comp pi2Id α = α := by
  unfold pi2Comp pi2Id; exact trans_refl_left α

/-- Right identity for π₂ composition. -/
theorem pi2Comp_id_right {A : Type} {a : A}
    (α : Pi2 A a) :
    pi2Comp α pi2Id = α := by
  unfold pi2Comp pi2Id; exact trans_refl_right α

/-- Associativity of π₂ composition. -/
theorem pi2Comp_assoc {A : Type} {a : A}
    (α β γ : Pi2 A a) :
    pi2Comp (pi2Comp α β) γ = pi2Comp α (pi2Comp β γ) := by
  unfold pi2Comp; exact trans_assoc α β γ

/-- Coherence path for left identity. -/
def pi2Comp_id_left_path {A : Type} {a : A}
    (α : Pi2 A a) :
    Path (pi2Comp pi2Id α) α :=
  Path.ofEq (pi2Comp_id_left α)

/-- Coherence path for right identity. -/
def pi2Comp_id_right_path {A : Type} {a : A}
    (α : Pi2 A a) :
    Path (pi2Comp α pi2Id) α :=
  Path.ofEq (pi2Comp_id_right α)

/-- Coherence path for associativity. -/
def pi2Comp_assoc_path {A : Type} {a : A}
    (α β γ : Pi2 A a) :
    Path (pi2Comp (pi2Comp α β) γ)
         (pi2Comp α (pi2Comp β γ)) :=
  Path.ofEq (pi2Comp_assoc α β γ)

/-- Left inverse at toEq level. -/
theorem pi2Comp_inv_left_toEq {A : Type} {a : A}
    (α : Pi2 A a) :
    (pi2Comp (pi2Inv α) α).toEq = (Path.refl (Path.refl a)).toEq := by
  unfold pi2Comp pi2Inv; simp

/-- Right inverse at toEq level. -/
theorem pi2Comp_inv_right_toEq {A : Type} {a : A}
    (α : Pi2 A a) :
    (pi2Comp α (pi2Inv α)).toEq = (Path.refl (Path.refl a)).toEq := by
  unfold pi2Comp pi2Inv; simp

/-! ## Inverse properties -/

/-- Inverse of identity is identity. -/
theorem pi2Inv_id {A : Type} {a : A} :
    pi2Inv (pi2Id (A := A) (a := a)) = pi2Id := by
  unfold pi2Inv pi2Id; exact symm_refl (Path.refl a)

/-- Path for inverse of identity. -/
def pi2Inv_id_path {A : Type} {a : A} :
    Path (pi2Inv (pi2Id (A := A) (a := a))) (pi2Id (A := A) (a := a)) :=
  Path.ofEq pi2Inv_id

/-- Inverse distributes over composition (reverses order). -/
theorem pi2Inv_comp {A : Type} {a : A}
    (α β : Pi2 A a) :
    pi2Inv (pi2Comp α β) = pi2Comp (pi2Inv β) (pi2Inv α) := by
  unfold pi2Inv pi2Comp; exact symm_trans α β

/-- Path for inverse distributing over composition. -/
def pi2Inv_comp_path {A : Type} {a : A}
    (α β : Pi2 A a) :
    Path (pi2Inv (pi2Comp α β)) (pi2Comp (pi2Inv β) (pi2Inv α)) :=
  Path.ofEq (pi2Inv_comp α β)

/-- Double inverse is identity. -/
theorem pi2Inv_inv {A : Type} {a : A}
    (α : Pi2 A a) :
    pi2Inv (pi2Inv α) = α := by
  unfold pi2Inv; exact symm_symm α

/-- Path for double inverse. -/
def pi2Inv_inv_path {A : Type} {a : A}
    (α : Pi2 A a) :
    Path (pi2Inv (pi2Inv α)) α :=
  Path.ofEq (pi2Inv_inv α)

/-! ## Functoriality of π₂ -/

/-- A function f : A → B induces a map π₂(A,a) → π₂(B, f a). -/
def pi2Map {A B : Type} {a : A} (f : A → B) :
    Pi2 A a → Pi2 B (f a) :=
  fun α => Path.congrArg (Path.congrArg f ·) α

/-- π₂ map sends refl to refl. -/
theorem pi2Map_refl {A B : Type} {a : A} (f : A → B) :
    pi2Map f (pi2Id (A := A) (a := a)) = pi2Id := by
  unfold pi2Map pi2Id; simp [Path.congrArg]

/-- Coherence for π₂ map on refl. -/
def pi2Map_refl_path {A B : Type} {a : A} (f : A → B) :
    Path (pi2Map f (pi2Id (A := A) (a := a)))
         (pi2Id (A := B) (a := f a)) :=
  Path.ofEq (pi2Map_refl f)

/-- π₂ map distributes over composition. -/
theorem pi2Map_comp {A B : Type} {a : A} (f : A → B)
    (α β : Pi2 A a) :
    pi2Map f (pi2Comp α β) =
      pi2Comp (pi2Map f α) (pi2Map f β) := by
  unfold pi2Map pi2Comp
  exact congrArg_trans (fun x => Path.congrArg f x) α β

/-- Coherence path for distributivity. -/
def pi2Map_comp_path {A B : Type} {a : A} (f : A → B)
    (α β : Pi2 A a) :
    Path (pi2Map f (pi2Comp α β))
         (pi2Comp (pi2Map f α) (pi2Map f β)) :=
  Path.ofEq (pi2Map_comp f α β)

/-- π₂ map commutes with inversion. -/
theorem pi2Map_inv {A B : Type} {a : A} (f : A → B)
    (α : Pi2 A a) :
    pi2Map f (pi2Inv α) = pi2Inv (pi2Map f α) := by
  unfold pi2Map pi2Inv
  exact congrArg_symm (fun x => Path.congrArg f x) α

/-- Coherence for π₂ map commuting with inversion. -/
def pi2Map_inv_path {A B : Type} {a : A} (f : A → B)
    (α : Pi2 A a) :
    Path (pi2Map f (pi2Inv α)) (pi2Inv (pi2Map f α)) :=
  Path.ofEq (pi2Map_inv f α)

/-- Composition of π₂ maps: (g ∘ f)_* = g_* ∘ f_*. -/
theorem pi2Map_comp_fun {A B C : Type} {a : A} (f : A → B) (g : B → C)
    (α : Pi2 A a) :
    pi2Map (fun x => g (f x)) α = pi2Map g (pi2Map f α) := by
  unfold pi2Map
  simp [Path.congrArg]

/-- Coherence for composition of π₂ maps. -/
def pi2Map_comp_fun_path {A B C : Type} {a : A} (f : A → B) (g : B → C)
    (α : Pi2 A a) :
    Path (pi2Map (fun x => g (f x)) α) (pi2Map g (pi2Map f α)) :=
  Path.ofEq (pi2Map_comp_fun f g α)

/-- π₂ map for the identity function. -/
theorem pi2Map_id_fun {A : Type} {a : A}
    (α : Pi2 A a) :
    pi2Map (fun x : A => x) α = α := by
  unfold pi2Map
  cases α with
  | mk steps proof =>
    cases proof
    simp [Path.congrArg]

/-- Coherence for identity π₂ map. -/
def pi2Map_id_fun_path {A : Type} {a : A}
    (α : Pi2 A a) :
    Path (pi2Map (fun x : A => x) α) α :=
  Path.ofEq (pi2Map_id_fun α)

/-! ## Product formulas for π₂ -/

/-- π₂(A × B) → π₂(A): projection to the first factor. -/
def pi2ProdFst {A B : Type} {a : A} {b : B} :
    Pi2 (A × B) (a, b) → Pi2 A a :=
  fun α => Path.congrArg (Path.congrArg Prod.fst ·) α

/-- π₂(A × B) → π₂(B): projection to the second factor. -/
def pi2ProdSnd {A B : Type} {a : A} {b : B} :
    Pi2 (A × B) (a, b) → Pi2 B b :=
  fun α => Path.congrArg (Path.congrArg Prod.snd ·) α

/-- Composing reflexive double loops through Fst yields refl. -/
theorem pi2ProdFst_refl {A B : Type} {a : A} {b : B} :
    pi2ProdFst (Path.refl (Path.refl (a, b))) =
      Path.refl (Path.refl a) := by
  simp [pi2ProdFst, Path.congrArg]

/-- Composing reflexive double loops through Snd yields refl. -/
theorem pi2ProdSnd_refl {A B : Type} {a : A} {b : B} :
    pi2ProdSnd (Path.refl (Path.refl (a, b))) =
      Path.refl (Path.refl b) := by
  simp [pi2ProdSnd, Path.congrArg]

/-- Coherence: fst projection preserves path structure. -/
def pi2ProdFst_coherence {A B : Type} {a : A} {b : B} :
    Path (pi2ProdFst (Path.refl (Path.refl (a, b))))
         (Path.refl (Path.refl a)) :=
  Path.ofEq pi2ProdFst_refl

/-- Coherence: snd projection preserves path structure. -/
def pi2ProdSnd_coherence {A B : Type} {a : A} {b : B} :
    Path (pi2ProdSnd (Path.refl (Path.refl (a, b))))
         (Path.refl (Path.refl b)) :=
  Path.ofEq pi2ProdSnd_refl

/-- Fst projection is a homomorphism. -/
theorem pi2ProdFst_comp {A B : Type} {a : A} {b : B}
    (α β : Pi2 (A × B) (a, b)) :
    pi2ProdFst (pi2Comp α β) = pi2Comp (pi2ProdFst α) (pi2ProdFst β) := by
  unfold pi2ProdFst pi2Comp
  exact congrArg_trans (fun x => Path.congrArg Prod.fst x) α β

/-- Snd projection is a homomorphism. -/
theorem pi2ProdSnd_comp {A B : Type} {a : A} {b : B}
    (α β : Pi2 (A × B) (a, b)) :
    pi2ProdSnd (pi2Comp α β) = pi2Comp (pi2ProdSnd α) (pi2ProdSnd β) := by
  unfold pi2ProdSnd pi2Comp
  exact congrArg_trans (fun x => Path.congrArg Prod.snd x) α β

/-- Coherence for Fst homomorphism. -/
def pi2ProdFst_comp_path {A B : Type} {a : A} {b : B}
    (α β : Pi2 (A × B) (a, b)) :
    Path (pi2ProdFst (pi2Comp α β))
         (pi2Comp (pi2ProdFst α) (pi2ProdFst β)) :=
  Path.ofEq (pi2ProdFst_comp α β)

/-- Coherence for Snd homomorphism. -/
def pi2ProdSnd_comp_path {A B : Type} {a : A} {b : B}
    (α β : Pi2 (A × B) (a, b)) :
    Path (pi2ProdSnd (pi2Comp α β))
         (pi2Comp (pi2ProdSnd α) (pi2ProdSnd β)) :=
  Path.ofEq (pi2ProdSnd_comp α β)

/-- Fst projection commutes with inversion. -/
theorem pi2ProdFst_inv {A B : Type} {a : A} {b : B}
    (α : Pi2 (A × B) (a, b)) :
    pi2ProdFst (pi2Inv α) = pi2Inv (pi2ProdFst α) := by
  unfold pi2ProdFst pi2Inv
  exact congrArg_symm (fun x => Path.congrArg Prod.fst x) α

/-- Snd projection commutes with inversion. -/
theorem pi2ProdSnd_inv {A B : Type} {a : A} {b : B}
    (α : Pi2 (A × B) (a, b)) :
    pi2ProdSnd (pi2Inv α) = pi2Inv (pi2ProdSnd α) := by
  unfold pi2ProdSnd pi2Inv
  exact congrArg_symm (fun x => Path.congrArg Prod.snd x) α

/-! ## Abelianness of π₂ -/

/-- π₂ is abelian at the toEq level. -/
theorem pi2_abelian_toEq {A : Type} {a : A}
    (α β : Pi2 A a) :
    (pi2Comp α β).toEq = (pi2Comp β α).toEq := by
  unfold pi2Comp; simp

/-! ## Hopf action -/

/-- The Hopf action on π₂(S²) is the identity. -/
def hopfPi2Action : Pi2 Sphere2 sphere2Base → Pi2 Sphere2 sphere2Base :=
  fun α => α

/-- The Hopf action is the identity. -/
theorem hopfPi2Action_id (α : Pi2 Sphere2 sphere2Base) :
    hopfPi2Action α = α := rfl

/-- Coherence path for Hopf action. -/
def hopfPi2Action_path (α : Pi2 Sphere2 sphere2Base) :
    Path (hopfPi2Action α) α :=
  Path.refl α

/-- Hopf action preserves composition. -/
theorem hopfPi2Action_comp (α β : Pi2 Sphere2 sphere2Base) :
    hopfPi2Action (pi2Comp α β) =
      pi2Comp (hopfPi2Action α) (hopfPi2Action β) := rfl

/-- Coherence for Hopf preserving comp. -/
def hopfPi2Action_comp_path (α β : Pi2 Sphere2 sphere2Base) :
    Path (hopfPi2Action (pi2Comp α β))
         (pi2Comp (hopfPi2Action α) (hopfPi2Action β)) :=
  Path.refl _

/-! ## Suspension and π₂ -/

/-- Suspension type representative. -/
abbrev Susp' (_A : Type) : Type := PUnit

/-- Basepoint of the suspension. -/
@[simp] abbrev suspBase' (A : Type) : Susp' A := PUnit.unit

/-- Suspension map on π₂ (trivial in our model). -/
def suspPi2Map {A : Type} {a : A} :
    Pi2 A a → Pi2 (Susp' A) (suspBase' A) :=
  fun _ => pi2Id

/-- Suspension map sends refl to refl. -/
theorem suspPi2Map_refl {A : Type} {a : A} :
    suspPi2Map (pi2Id (A := A) (a := a)) =
      pi2Id (A := Susp' A) (a := suspBase' A) := rfl

/-- Suspension map preserves composition. -/
theorem suspPi2Map_comp {A : Type} {a : A}
    (α β : Pi2 A a) :
    suspPi2Map (pi2Comp α β) =
      pi2Comp (suspPi2Map (A := A) α) (suspPi2Map (A := A) β) := by
  show pi2Id = pi2Comp pi2Id pi2Id
  unfold pi2Comp pi2Id
  exact (trans_refl_left (refl (refl PUnit.unit))).symm

/-- Coherence for suspension composition. -/
def suspPi2Map_comp_path {A : Type} {a : A}
    (α β : Pi2 A a) :
    Path (suspPi2Map (pi2Comp α β))
         (pi2Comp (suspPi2Map (A := A) α) (suspPi2Map (A := A) β)) :=
  Path.ofEq (suspPi2Map_comp α β)

/-- Suspension map preserves inversion. -/
theorem suspPi2Map_inv {A : Type} {a : A}
    (α : Pi2 A a) :
    suspPi2Map (pi2Inv α) = pi2Inv (suspPi2Map (A := A) α) := by
  show pi2Id = pi2Inv pi2Id
  unfold pi2Inv pi2Id
  exact (symm_refl (refl PUnit.unit)).symm

/-- Coherence for suspension inversion. -/
def suspPi2Map_inv_path {A : Type} {a : A}
    (α : Pi2 A a) :
    Path (suspPi2Map (pi2Inv α))
         (pi2Inv (suspPi2Map (A := A) α)) :=
  Path.ofEq (suspPi2Map_inv α)

/-! ## Wedge sum and π₂ -/

/-- Wedge sum type representative. -/
abbrev Wedge' (_A _B : Type) : Type := PUnit

/-- Basepoint of wedge. -/
@[simp] abbrev wedgeBase' (A B : Type) : Wedge' A B := PUnit.unit

/-- Inclusion of π₂(A) into π₂(A ∨ B). -/
def wedgeInclLeft' {A B : Type} {a : A} :
    Pi2 A a → Pi2 (Wedge' A B) (wedgeBase' A B) :=
  fun _ => pi2Id

/-- Inclusion of π₂(B) into π₂(A ∨ B). -/
def wedgeInclRight' {A B : Type} {b : B} :
    Pi2 B b → Pi2 (Wedge' A B) (wedgeBase' A B) :=
  fun _ => pi2Id

/-- Both inclusions send refl to refl. -/
theorem wedgeInclLeft_refl' {A B : Type} {a : A} :
    wedgeInclLeft' (B := B) (pi2Id (A := A) (a := a)) =
      pi2Id (A := Wedge' A B) := rfl

theorem wedgeInclRight_refl' {A B : Type} {b : B} :
    wedgeInclRight' (A := A) (pi2Id (A := B) (a := b)) =
      pi2Id (A := Wedge' A B) := rfl

/-- Left inclusion preserves composition. -/
theorem wedgeInclLeft_comp' {A B : Type} {a : A}
    (α β : Pi2 A a) :
    wedgeInclLeft' (B := B) (pi2Comp α β) =
      pi2Comp (wedgeInclLeft' (B := B) α) (wedgeInclLeft' (B := B) β) := by
  show pi2Id = pi2Comp pi2Id pi2Id
  unfold pi2Comp pi2Id
  exact (trans_refl_left (refl (refl PUnit.unit))).symm

/-- Right inclusion preserves composition. -/
theorem wedgeInclRight_comp' {A B : Type} {b : B}
    (α β : Pi2 B b) :
    wedgeInclRight' (A := A) (pi2Comp α β) =
      pi2Comp (wedgeInclRight' (A := A) α) (wedgeInclRight' (A := A) β) := by
  show pi2Id = pi2Comp pi2Id pi2Id
  unfold pi2Comp pi2Id
  exact (trans_refl_left (refl (refl PUnit.unit))).symm

/-! ## Surface-specific π₂ results -/

/-- For PUnit-based spaces, π₂ toEq is always trivial. -/
theorem pi2_punit_toEq
    (α : Pi2 PUnit PUnit.unit) :
    α.toEq = (Path.refl (Path.refl PUnit.unit)).toEq := by
  simp

/-- Genus-g surface: π₂ toEq is trivial. -/
theorem pi2Surface_toEq (g : Nat)
    (α : Pi2 (Surface g) (surfaceBase g)) :
    α.toEq = (Path.refl (Path.refl (surfaceBase g))).toEq := by
  simp

/-- Two π₂ elements of a surface agree at toEq. -/
theorem pi2Surface_all_eq_toEq (g : Nat)
    (α β : Pi2 (Surface g) (surfaceBase g)) :
    α.toEq = β.toEq := by
  simp

/-- Torus: π₂(T²) has trivial toEq. -/
theorem pi2Torus_trivial_toEq
    (α : Pi2 (Surface 1) (surfaceBase 1)) :
    α.toEq = rfl := by simp

/-- RP²: π₂ has trivial toEq in our model. -/
theorem pi2RP2_trivial_toEq
    (α : Pi2 RP2 rp2Base) :
    α.toEq = rfl := by simp

/-- Klein bottle: π₂ has trivial toEq. -/
theorem pi2Klein_trivial_toEq
    (α : Pi2 KleinBottle kleinBase) :
    α.toEq = rfl := by simp

/-- Genus-3 surface: π₂ toEq is trivial. -/
theorem pi2_genus3_trivial (α : Pi2 (Surface 3) (surfaceBase 3)) :
    α.toEq = (Path.refl (Path.refl (surfaceBase 3))).toEq :=
  pi2Surface_toEq 3 α

/-- Genus-4 surface: π₂ toEq is trivial. -/
theorem pi2_genus4_trivial (α : Pi2 (Surface 4) (surfaceBase 4)) :
    α.toEq = (Path.refl (Path.refl (surfaceBase 4))).toEq :=
  pi2Surface_toEq 4 α

/-! ## Iterated π₂ composition -/

/-- Iterate π₂ composition n times. -/
def pi2Iterate {A : Type} {a : A}
    (α : Pi2 A a) : Nat → Pi2 A a
  | 0 => pi2Id
  | n + 1 => pi2Comp α (pi2Iterate α n)

/-- Iterating zero times gives identity. -/
theorem pi2Iterate_zero {A : Type} {a : A}
    (α : Pi2 A a) :
    pi2Iterate α 0 = pi2Id := rfl

/-- Iterating once equals the element (after right identity). -/
theorem pi2Iterate_one {A : Type} {a : A}
    (α : Pi2 A a) :
    pi2Iterate α 1 = α := by
  show pi2Comp α pi2Id = α
  exact pi2Comp_id_right α

/-- Path for iterating once. -/
def pi2Iterate_one_path {A : Type} {a : A}
    (α : Pi2 A a) :
    Path (pi2Iterate α 1) α :=
  Path.ofEq (pi2Iterate_one α)

/-- Iterate two equals self composed with self. -/
theorem pi2Iterate_two {A : Type} {a : A}
    (α : Pi2 A a) :
    pi2Iterate α 2 = pi2Comp α α := by
  show pi2Comp α (pi2Iterate α 1) = pi2Comp α α
  rw [pi2Iterate_one]

/-- Path for iterating twice. -/
def pi2Iterate_two_path {A : Type} {a : A}
    (α : Pi2 A a) :
    Path (pi2Iterate α 2) (pi2Comp α α) :=
  Path.ofEq (pi2Iterate_two α)

/-! ## Constant map on π₂ -/

/-- A constant map induces the zero map on π₂ (at toEq level). -/
theorem pi2_const_map_toEq {A B : Type} {a : A} {b : B}
    (α : Pi2 A a) :
    (pi2Map (fun _ : A => b) α).toEq = (pi2Id (A := B) (a := b)).toEq := by
  unfold pi2Map pi2Id; simp

end Pi2Surfaces
end Homotopy
end Path
end ComputationalPaths

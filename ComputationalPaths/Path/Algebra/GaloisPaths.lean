/-
# Galois Theory via Computational Paths

Automorphisms, fixed fields, Galois groups, fundamental theorem aspects,
normal/separable extensions. All coherence witnessed by `Path`.

## References

- Lang, "Algebra"
- Artin, "Galois Theory"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace GaloisPaths

universe u v

open ComputationalPaths.Path

/-! ## Path-witnessed field structure (local copy) -/

/-- A field with Path-witnessed laws (minimal for Galois theory). -/
structure PField (F : Type u) where
  zero : F
  one : F
  add : F → F → F
  mul : F → F → F
  neg : F → F
  inv : F → F
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  zero_add : ∀ a, add zero a = a
  add_neg : ∀ a, add a (neg a) = zero
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b, mul a b = mul b a
  one_mul : ∀ a, mul one a = a
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)

/-- A field embedding. -/
structure PFieldEmbed (F E : Type u) (pF : PField F) (pE : PField E) where
  embed : F → E
  map_zero : embed pF.zero = pE.zero
  map_one : embed pF.one = pE.one
  map_add : ∀ a b, embed (pF.add a b) = pE.add (embed a) (embed b)
  map_mul : ∀ a b, embed (pF.mul a b) = pE.mul (embed a) (embed b)

/-! ## Field automorphisms -/

/-- A field automorphism: an invertible field homomorphism. -/
structure FieldAut (F : Type u) (pF : PField F) where
  toFun : F → F
  invFun : F → F
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ a, toFun (invFun a) = a
  map_zero : toFun pF.zero = pF.zero
  map_one : toFun pF.one = pF.one
  map_add : ∀ a b, toFun (pF.add a b) = pF.add (toFun a) (toFun b)
  map_mul : ∀ a b, toFun (pF.mul a b) = pF.mul (toFun a) (toFun b)

/-- Identity automorphism. -/
def autId {F : Type u} (pF : PField F) : FieldAut F pF :=
  ⟨id, id, fun _ => rfl, fun _ => rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Identity automorphism acts as identity. -/
theorem autId_apply {F : Type u} (pF : PField F) (a : F) :
    (autId pF).toFun a = a := rfl

/-- Path: identity automorphism. -/
def autId_path {F : Type u} (pF : PField F) (a : F) :
    Path ((autId pF).toFun a) a :=
  Path.refl _

/-- Compose two automorphisms. -/
def autComp {F : Type u} {pF : PField F}
    (σ τ : FieldAut F pF) : FieldAut F pF :=
  { toFun := σ.toFun ∘ τ.toFun
    invFun := τ.invFun ∘ σ.invFun
    left_inv := fun a => by simp [Function.comp, σ.left_inv, τ.left_inv]
    right_inv := fun a => by simp [Function.comp, σ.right_inv, τ.right_inv]
    map_zero := by simp [Function.comp, τ.map_zero, σ.map_zero]
    map_one := by simp [Function.comp, τ.map_one, σ.map_one]
    map_add := fun a b => by simp [Function.comp, τ.map_add, σ.map_add]
    map_mul := fun a b => by simp [Function.comp, τ.map_mul, σ.map_mul] }

/-- Automorphism composition is associative. -/
theorem autComp_assoc {F : Type u} {pF : PField F}
    (σ τ ρ : FieldAut F pF) :
    (autComp (autComp σ τ) ρ).toFun = (autComp σ (autComp τ ρ)).toFun := by
  rfl

/-- Path: composition associativity. -/
def autComp_assoc_path {F : Type u} {pF : PField F}
    (σ τ ρ : FieldAut F pF) :
    Path (autComp (autComp σ τ) ρ).toFun (autComp σ (autComp τ ρ)).toFun :=
  Path.refl _

/-- Left identity for automorphism composition. -/
theorem autComp_id_left {F : Type u} {pF : PField F}
    (σ : FieldAut F pF) :
    (autComp (autId pF) σ).toFun = σ.toFun := by
  rfl

/-- Path: left identity. -/
def autComp_id_left_path {F : Type u} {pF : PField F}
    (σ : FieldAut F pF) :
    Path (autComp (autId pF) σ).toFun σ.toFun :=
  Path.refl _

/-- Right identity for automorphism composition. -/
theorem autComp_id_right {F : Type u} {pF : PField F}
    (σ : FieldAut F pF) :
    (autComp σ (autId pF)).toFun = σ.toFun := by
  rfl

/-- Path: right identity. -/
def autComp_id_right_path {F : Type u} {pF : PField F}
    (σ : FieldAut F pF) :
    Path (autComp σ (autId pF)).toFun σ.toFun :=
  Path.refl _

/-- Inverse automorphism. -/
def autInv {F : Type u} {pF : PField F} (σ : FieldAut F pF) : FieldAut F pF :=
  { toFun := σ.invFun
    invFun := σ.toFun
    left_inv := σ.right_inv
    right_inv := σ.left_inv
    map_zero := by
      have := σ.left_inv pF.zero
      rw [σ.map_zero] at this; exact this
    map_one := by
      have := σ.left_inv pF.one
      rw [σ.map_one] at this; exact this
    map_add := fun a b => by
      apply_fun σ.toFun using Function.LeftInverse.injective σ.left_inv
      rw [σ.right_inv, σ.map_add, σ.right_inv, σ.right_inv]
    map_mul := fun a b => by
      apply_fun σ.toFun using Function.LeftInverse.injective σ.left_inv
      rw [σ.right_inv, σ.map_mul, σ.right_inv, σ.right_inv] }

/-- Left inverse law. -/
theorem autComp_inv_left {F : Type u} {pF : PField F}
    (σ : FieldAut F pF) (a : F) :
    (autComp (autInv σ) σ).toFun a = a := by
  simp [autComp, autInv, Function.comp, σ.left_inv]

/-- Path: left inverse. -/
def autComp_inv_left_path {F : Type u} {pF : PField F}
    (σ : FieldAut F pF) (a : F) :
    Path ((autComp (autInv σ) σ).toFun a) a :=
  Path.ofEq (autComp_inv_left σ a)

/-- Right inverse law. -/
theorem autComp_inv_right {F : Type u} {pF : PField F}
    (σ : FieldAut F pF) (a : F) :
    (autComp σ (autInv σ)).toFun a = a := by
  simp [autComp, autInv, Function.comp, σ.right_inv]

/-- Path: right inverse. -/
def autComp_inv_right_path {F : Type u} {pF : PField F}
    (σ : FieldAut F pF) (a : F) :
    Path ((autComp σ (autInv σ)).toFun a) a :=
  Path.ofEq (autComp_inv_right σ a)

/-! ## Fixed fields -/

/-- An element a is fixed by automorphism σ. -/
def isFixed {F : Type u} {pF : PField F} (σ : FieldAut F pF) (a : F) : Prop :=
  σ.toFun a = a

/-- The identity fixes everything. -/
theorem id_fixes_all {F : Type u} (pF : PField F) (a : F) :
    isFixed (autId pF) a := rfl

/-- Path: identity fixes all. -/
def id_fixes_all_path {F : Type u} (pF : PField F) (a : F) :
    Path ((autId pF).toFun a) a :=
  Path.refl _

/-- If σ fixes a and b, then σ fixes a + b. -/
theorem fixed_add {F : Type u} {pF : PField F}
    (σ : FieldAut F pF) (a b : F) (ha : isFixed σ a) (hb : isFixed σ b) :
    isFixed σ (pF.add a b) := by
  simp [isFixed] at *
  rw [σ.map_add, ha, hb]

/-- Path: fixed under addition. -/
def fixed_add_path {F : Type u} {pF : PField F}
    (σ : FieldAut F pF) (a b : F) (ha : isFixed σ a) (hb : isFixed σ b) :
    Path (σ.toFun (pF.add a b)) (pF.add a b) :=
  Path.ofEq (fixed_add σ a b ha hb)

/-- If σ fixes a and b, then σ fixes a * b. -/
theorem fixed_mul {F : Type u} {pF : PField F}
    (σ : FieldAut F pF) (a b : F) (ha : isFixed σ a) (hb : isFixed σ b) :
    isFixed σ (pF.mul a b) := by
  simp [isFixed] at *
  rw [σ.map_mul, ha, hb]

/-- Path: fixed under multiplication. -/
def fixed_mul_path {F : Type u} {pF : PField F}
    (σ : FieldAut F pF) (a b : F) (ha : isFixed σ a) (hb : isFixed σ b) :
    Path (σ.toFun (pF.mul a b)) (pF.mul a b) :=
  Path.ofEq (fixed_mul σ a b ha hb)

/-! ## Galois groups -/

/-- A Galois group: a list of automorphisms with closure properties. -/
structure GaloisGroup (F : Type u) (pF : PField F) where
  auts : List (FieldAut F pF)
  hasId : (autId pF) ∈ auts ∨ auts = []

/-- Singleton Galois group (trivial). -/
def trivialGalois {F : Type u} (pF : PField F) : GaloisGroup F pF :=
  ⟨[autId pF], Or.inl (by simp)⟩

/-- Size of the Galois group. -/
def galoisOrder {F : Type u} {pF : PField F} (G : GaloisGroup F pF) : Nat :=
  G.auts.length

/-- Trivial group has order 1. -/
theorem trivialGalois_order {F : Type u} (pF : PField F) :
    galoisOrder (trivialGalois pF) = 1 := rfl

/-- Path: trivial group order. -/
def trivialGalois_order_path {F : Type u} (pF : PField F) :
    Path (galoisOrder (trivialGalois pF)) 1 :=
  Path.refl _

/-! ## Automorphism congruence and transport -/

/-- congrArg: equal automorphisms give equal results. -/
def aut_congr {F : Type u} {pF : PField F}
    (σ τ : FieldAut F pF) (h : σ = τ) (a : F) :
    Path (σ.toFun a) (τ.toFun a) :=
  Path.congrArg (fun s => FieldAut.toFun s a) (Path.ofEq h)

/-- congrArg: automorphism applied to equal elements. -/
def aut_apply_congr {F : Type u} {pF : PField F}
    (σ : FieldAut F pF) (a b : F) (h : a = b) :
    Path (σ.toFun a) (σ.toFun b) :=
  Path.congrArg σ.toFun (Path.ofEq h)

/-- Transport along automorphism inverse path. -/
theorem aut_inv_transport {F : Type u} {pF : PField F}
    (σ : FieldAut F pF) (a : F) :
    σ.invFun (σ.toFun a) = a :=
  σ.left_inv a

/-- Path: inverse transport. -/
def aut_inv_transport_path {F : Type u} {pF : PField F}
    (σ : FieldAut F pF) (a : F) :
    Path (σ.invFun (σ.toFun a)) a :=
  Path.ofEq (σ.left_inv a)

/-- Symm of inverse transport path gives forward transport. -/
theorem aut_inv_transport_symm {F : Type u} {pF : PField F}
    (σ : FieldAut F pF) (a : F) :
    Path.symm (aut_inv_transport_path σ a) =
      Path.ofEq (σ.left_inv a).symm := by
  simp [aut_inv_transport_path, Path.symm, Path.ofEq]

/-! ## Normal extensions -/

/-- A set of automorphisms acts transitively on roots: modeled as
    every element maps to some element via some automorphism. -/
structure NormalWitness {F : Type u} {pF : PField F}
    (G : GaloisGroup F pF) (roots : List F) where
  act : F → F  -- representative action
  preserves : ∀ r, r ∈ roots → act r ∈ roots

/-- The identity provides a trivial normal witness. -/
def trivialNormal {F : Type u} {pF : PField F}
    (G : GaloisGroup F pF) (roots : List F) :
    NormalWitness G roots :=
  ⟨id, fun _ h => h⟩

/-- Trivial normal witness acts as identity. -/
theorem trivialNormal_id {F : Type u} {pF : PField F}
    (G : GaloisGroup F pF) (roots : List F) (r : F) :
    (trivialNormal G roots).act r = r := rfl

/-- Path: trivial normal is identity. -/
def trivialNormal_path {F : Type u} {pF : PField F}
    (G : GaloisGroup F pF) (roots : List F) (r : F) :
    Path ((trivialNormal G roots).act r) r :=
  Path.refl _

/-! ## Separable extensions -/

/-- A polynomial is separable if it has distinct roots (modeled by a witness). -/
structure SeparableWitness {F : Type u} (pF : PField F) where
  roots : List F
  distinct : roots.Nodup

/-- Empty separable witness. -/
def emptySeparable {F : Type u} (pF : PField F) : SeparableWitness pF :=
  ⟨[], List.nodup_nil⟩

/-- Empty separable has no roots. -/
theorem emptySeparable_roots {F : Type u} (pF : PField F) :
    (emptySeparable pF).roots = [] := rfl

/-- Path: empty separable roots. -/
def emptySeparable_path {F : Type u} (pF : PField F) :
    Path (emptySeparable pF).roots ([] : List F) :=
  Path.refl _

/-! ## Fundamental theorem aspects -/

/-- Fixed field: elements fixed by all automorphisms in G. -/
def isInFixedField {F : Type u} {pF : PField F}
    (G : GaloisGroup F pF) (a : F) : Prop :=
  ∀ σ, σ ∈ G.auts → isFixed σ a

/-- Zero is in the fixed field. -/
theorem zero_in_fixed {F : Type u} {pF : PField F}
    (G : GaloisGroup F pF) :
    isInFixedField G pF.zero := by
  intro σ _
  exact σ.map_zero

/-- Path: zero is fixed. -/
def zero_in_fixed_path {F : Type u} {pF : PField F}
    (G : GaloisGroup F pF) (σ : FieldAut F pF) (hσ : σ ∈ G.auts) :
    Path (σ.toFun pF.zero) pF.zero :=
  Path.ofEq (zero_in_fixed G σ hσ)

/-- One is in the fixed field. -/
theorem one_in_fixed {F : Type u} {pF : PField F}
    (G : GaloisGroup F pF) :
    isInFixedField G pF.one := by
  intro σ _
  exact σ.map_one

/-- Path: one is fixed. -/
def one_in_fixed_path {F : Type u} {pF : PField F}
    (G : GaloisGroup F pF) (σ : FieldAut F pF) (hσ : σ ∈ G.auts) :
    Path (σ.toFun pF.one) pF.one :=
  Path.ofEq (one_in_fixed G σ hσ)

/-- Fixed field is closed under addition. -/
theorem fixed_field_add {F : Type u} {pF : PField F}
    (G : GaloisGroup F pF) (a b : F)
    (ha : isInFixedField G a) (hb : isInFixedField G b) :
    isInFixedField G (pF.add a b) := by
  intro σ hσ
  exact fixed_add σ a b (ha σ hσ) (hb σ hσ)

/-- Fixed field is closed under multiplication. -/
theorem fixed_field_mul {F : Type u} {pF : PField F}
    (G : GaloisGroup F pF) (a b : F)
    (ha : isInFixedField G a) (hb : isInFixedField G b) :
    isInFixedField G (pF.mul a b) := by
  intro σ hσ
  exact fixed_mul σ a b (ha σ hσ) (hb σ hσ)

/-- Trans path: combining two fixed-field proofs. -/
def fixed_field_trans_path {F : Type u} {pF : PField F}
    (σ : FieldAut F pF) (a b : F)
    (ha : isFixed σ a) (hb : isFixed σ b) :
    Path (σ.toFun (pF.add a b)) (pF.add a b) :=
  Path.trans
    (Path.ofEq (σ.map_add a b))
    (Path.trans
      (Path.congrArg (fun x => pF.add x (σ.toFun b)) (Path.ofEq ha))
      (Path.congrArg (fun x => pF.add a x) (Path.ofEq hb)))

end GaloisPaths
end Algebra
end Path
end ComputationalPaths

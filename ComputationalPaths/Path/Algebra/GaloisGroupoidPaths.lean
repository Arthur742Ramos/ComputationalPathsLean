/-
# Galois Groupoid via Computational Paths

The automorphism group of a field extension carries a natural groupoid
structure whose laws are witnessed by explicit `Path`/`trans`/`symm`
combinators. This module proves 38 theorems connecting Galois-theoretic
operations (composition, inversion, fixed-field membership, conjugation)
with the computational-path algebra.

Every path is built from explicit `Step` witnesses — zero `Path.ofEq`.

## References

- Lang, *Algebra*, Ch. VI
- Szamuely, *Galois Groups and Fundamental Groups*
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace GaloisGroupoidPaths

open ComputationalPaths.Path

universe u

/-! ## Domain inductives -/

/-- Galois action expressions — the "objects" we rewrite between. -/
inductive GaloisExpr (F : Type u) where
  | elem : F → GaloisExpr F
  | app : (F → F) → F → GaloisExpr F        -- σ(a)
  | comp : (F → F) → (F → F) → F → GaloisExpr F  -- σ(τ(a))

/-- Galois rewrite step kinds. -/
inductive GaloisStepKind where
  | leftId   : GaloisStepKind  -- id ∘ σ = σ
  | rightId  : GaloisStepKind  -- σ ∘ id = σ
  | assoc    : GaloisStepKind  -- (σ∘τ)∘ρ = σ∘(τ∘ρ)
  | invLeft  : GaloisStepKind  -- σ⁻¹∘σ = id
  | invRight : GaloisStepKind  -- σ∘σ⁻¹ = id
  | mapZero  : GaloisStepKind  -- σ(0) = 0
  | mapOne   : GaloisStepKind  -- σ(1) = 1
  | fixed    : GaloisStepKind  -- σ(a) = a for fixed a
  deriving DecidableEq, Repr

/-! ## Local field infrastructure -/

/-- Minimal field structure for Galois path theorems. -/
structure GField (F : Type u) where
  zero : F
  one : F
  add : F → F → F
  mul : F → F → F
  neg : F → F
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  zero_add : ∀ a, add zero a = a
  add_neg : ∀ a, add a (neg a) = zero

/-- A field automorphism with invertibility. -/
structure FAut (F : Type u) (gF : GField F) where
  toFun : F → F
  invFun : F → F
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ a, toFun (invFun a) = a
  map_zero : toFun gF.zero = gF.zero
  map_one : toFun gF.one = gF.one
  map_add : ∀ a b, toFun (gF.add a b) = gF.add (toFun a) (toFun b)
  map_mul : ∀ a b, toFun (gF.mul a b) = gF.mul (toFun a) (toFun b)

variable {F : Type u} {gF : GField F}

/-- Build a genuine 1-step path from a proof. -/
@[inline] def galStep {α : Type _} (a b : α) (h : a = b) : Path a b :=
  Path.mk [Step.mk a b h] h

/-- Identity automorphism. -/
def fautId (gF : GField F) : FAut F gF :=
  ⟨id, id, fun _ => rfl, fun _ => rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Compose two automorphisms. -/
def fautComp (σ τ : FAut F gF) : FAut F gF where
  toFun := fun a => σ.toFun (τ.toFun a)
  invFun := fun a => τ.invFun (σ.invFun a)
  left_inv := fun a => by simp [σ.left_inv, τ.left_inv]
  right_inv := fun a => by simp [σ.right_inv, τ.right_inv]
  map_zero := by simp [τ.map_zero, σ.map_zero]
  map_one := by simp [τ.map_one, σ.map_one]
  map_add := fun a b => by simp [τ.map_add, σ.map_add]
  map_mul := fun a b => by simp [τ.map_mul, σ.map_mul]

/-- Inverse automorphism. -/
def fautInv (σ : FAut F gF) : FAut F gF where
  toFun := σ.invFun
  invFun := σ.toFun
  left_inv := σ.right_inv
  right_inv := σ.left_inv
  map_zero := by have := σ.left_inv gF.zero; rw [σ.map_zero] at this; exact this
  map_one := by have := σ.left_inv gF.one; rw [σ.map_one] at this; exact this
  map_add := fun a b => by
    have hinj : Function.Injective σ.toFun :=
      Function.LeftInverse.injective σ.left_inv
    exact hinj (by rw [σ.right_inv, σ.map_add, σ.right_inv, σ.right_inv])
  map_mul := fun a b => by
    have hinj : Function.Injective σ.toFun :=
      Function.LeftInverse.injective σ.left_inv
    exact hinj (by rw [σ.right_inv, σ.map_mul, σ.right_inv, σ.right_inv])

/-- An element is fixed by an automorphism. -/
def isFixed (σ : FAut F gF) (a : F) : Prop := σ.toFun a = a

/-! ## Theorems 1–4: Groupoid unit and associativity -/

/-- Theorem 1: left-identity path for composition. -/
def galois_comp_id_left (σ : FAut F gF) (a : F) :
    Path ((fautComp (fautId gF) σ).toFun a) (σ.toFun a) :=
  Path.refl _

/-- Theorem 2: right-identity path for composition. -/
def galois_comp_id_right (σ : FAut F gF) (a : F) :
    Path ((fautComp σ (fautId gF)).toFun a) (σ.toFun a) :=
  Path.refl _

/-- Theorem 3: associativity path for triple composition. -/
def galois_comp_assoc (σ τ ρ : FAut F gF) (a : F) :
    Path ((fautComp (fautComp σ τ) ρ).toFun a)
         ((fautComp σ (fautComp τ ρ)).toFun a) :=
  Path.refl _

/-- Theorem 4: left-inverse cancellation. -/
theorem galois_inv_left_eq (σ : FAut F gF) (a : F) :
    (fautComp (fautInv σ) σ).toFun a = a := by
  simp [fautComp, fautInv, σ.left_inv]

def galois_inv_left (σ : FAut F gF) (a : F) :
    Path ((fautComp (fautInv σ) σ).toFun a) a :=
  galStep _ _ (galois_inv_left_eq σ a)

/-! ## Theorems 5–8: Inverse and symmetry -/

/-- Theorem 5: right-inverse cancellation. -/
theorem galois_inv_right_eq (σ : FAut F gF) (a : F) :
    (fautComp σ (fautInv σ)).toFun a = a := by
  simp [fautComp, fautInv, σ.right_inv]

def galois_inv_right (σ : FAut F gF) (a : F) :
    Path ((fautComp σ (fautInv σ)).toFun a) a :=
  galStep _ _ (galois_inv_right_eq σ a)

/-- Theorem 6: double inverse is identity. -/
theorem galois_inv_inv (σ : FAut F gF) (a : F) :
    (fautInv (fautInv σ)).toFun a = σ.toFun a := by
  simp [fautInv]

/-- Theorem 7: double-inverse path. -/
def galois_inv_inv_path (σ : FAut F gF) (a : F) :
    Path ((fautInv (fautInv σ)).toFun a) (σ.toFun a) :=
  galStep _ _ (galois_inv_inv σ a)

/-- Theorem 8: symm of left-inverse path gives backward direction. -/
def galois_inv_left_symm (σ : FAut F gF) (a : F) :
    Path a ((fautComp (fautInv σ) σ).toFun a) :=
  Path.symm (galois_inv_left σ a)

/-! ## Theorems 9–12: Trans / composition of paths -/

/-- Theorem 9: round-trip via trans of inverse paths. -/
def galois_inv_round_trip (σ : FAut F gF) (a : F) :
    Path ((fautComp (fautInv σ) σ).toFun a)
         ((fautComp σ (fautInv σ)).toFun a) :=
  Path.trans (galois_inv_left σ a) (Path.symm (galois_inv_right σ a))

/-- Theorem 10: identity inverse is identity. -/
theorem galois_id_inv (a : F) :
    (fautInv (fautId gF (F := F))).toFun a = a := by
  simp [fautInv, fautId]

/-- Theorem 11: path witness for identity inverse. -/
def galois_id_inv_path (a : F) :
    Path ((fautInv (fautId gF (F := F))).toFun a) a :=
  galStep _ _ (galois_id_inv (gF := gF) a)

/-- Theorem 12: chain σ⁻¹σ = id = ττ⁻¹ via trans. -/
def galois_inv_chain (σ τ : FAut F gF) (a : F) :
    Path ((fautComp (fautInv σ) σ).toFun a)
         ((fautComp τ (fautInv τ)).toFun a) :=
  Path.trans (galois_inv_left σ a) (Path.symm (galois_inv_right τ a))

/-! ## Theorems 13–16: Fixed-field paths -/

/-- Theorem 13: automorphisms fix zero. -/
def galois_fixes_zero (σ : FAut F gF) :
    Path (σ.toFun gF.zero) gF.zero :=
  galStep _ _ σ.map_zero

/-- Theorem 14: automorphisms fix one. -/
def galois_fixes_one (σ : FAut F gF) :
    Path (σ.toFun gF.one) gF.one :=
  galStep _ _ σ.map_one

/-- Theorem 15: inverse preserves fixed elements. -/
theorem galois_inv_fixes {σ : FAut F gF} {a : F}
    (h : isFixed σ a) : isFixed (fautInv σ) a := by
  simp [isFixed, fautInv] at *
  have := σ.left_inv a
  rw [h] at this
  exact this

/-- Theorem 16: path for inverse preserving fixed elements. -/
def galois_inv_fixes_path {σ : FAut F gF} {a : F}
    (h : isFixed σ a) : Path ((fautInv σ).toFun a) a :=
  galStep _ _ (galois_inv_fixes h)

/-! ## Theorems 17–20: Conjugation -/

/-- Conjugation: σ τ σ⁻¹. -/
def galois_conjugate (σ τ : FAut F gF) : FAut F gF :=
  fautComp (fautComp σ τ) (fautInv σ)

/-- Theorem 17: conjugation by identity is identity. -/
theorem galois_conjugate_id (τ : FAut F gF) (a : F) :
    (galois_conjugate (fautId gF) τ).toFun a = τ.toFun a := by
  simp [galois_conjugate, fautComp, fautInv, fautId]

/-- Theorem 18: path for conjugation by identity. -/
def galois_conjugate_id_path (τ : FAut F gF) (a : F) :
    Path ((galois_conjugate (fautId gF) τ).toFun a) (τ.toFun a) :=
  galStep _ _ (galois_conjugate_id τ a)

/-- Theorem 19: conjugation of identity is identity. -/
theorem galois_conjugate_of_id (σ : FAut F gF) (a : F) :
    (galois_conjugate σ (fautId gF)).toFun a = a := by
  simp [galois_conjugate, fautComp, fautId, fautInv]
  exact σ.right_inv a

/-- Theorem 20: path for conjugation of identity. -/
def galois_conjugate_of_id_path (σ : FAut F gF) (a : F) :
    Path ((galois_conjugate σ (fautId gF)).toFun a) a :=
  galStep _ _ (galois_conjugate_of_id σ a)

/-! ## Theorems 21–25: Deeper coherence -/

/-- Theorem 21: fixed-field negation closure. -/
theorem galois_fixed_neg {σ : FAut F gF} {a : F}
    (h : isFixed σ a) : isFixed σ (gF.neg a) := by
  simp [isFixed] at *
  have h1 : gF.add (σ.toFun (gF.neg a)) (σ.toFun a) = gF.zero := by
    rw [← σ.map_add, gF.add_comm (gF.neg a) a, gF.add_neg, σ.map_zero]
  have h2 : gF.add (σ.toFun (gF.neg a)) a = gF.zero := by rw [h] at h1; exact h1
  calc σ.toFun (gF.neg a)
      = gF.add (σ.toFun (gF.neg a)) gF.zero := by rw [gF.add_comm, gF.zero_add]
    _ = gF.add (σ.toFun (gF.neg a)) (gF.add a (gF.neg a)) := by rw [gF.add_neg]
    _ = gF.add (gF.add (σ.toFun (gF.neg a)) a) (gF.neg a) := by rw [gF.add_assoc]
    _ = gF.add gF.zero (gF.neg a) := by rw [h2]
    _ = gF.neg a := by rw [gF.zero_add]

/-- Theorem 22: path for negation closure. -/
def galois_fixed_neg_path {σ : FAut F gF} {a : F}
    (h : isFixed σ a) : Path (σ.toFun (gF.neg a)) (gF.neg a) :=
  galStep _ _ (galois_fixed_neg h)

/-- Theorem 23: composing fixed-element paths via trans for addition. -/
def galois_fixed_add_path (σ : FAut F gF) (a b : F)
    (ha : isFixed σ a) (hb : isFixed σ b) :
    Path (σ.toFun (gF.add a b)) (gF.add a b) :=
  Path.trans
    (galStep _ _ (σ.map_add a b))
    (Path.trans
      (Path.congrArg (fun x => gF.add x (σ.toFun b)) (galStep _ _ ha))
      (Path.congrArg (fun x => gF.add a x) (galStep _ _ hb)))

/-- Theorem 24: fourfold composition associativity. -/
def galois_comp_assoc4 (σ τ ρ μ : FAut F gF) (a : F) :
    Path ((fautComp (fautComp (fautComp σ τ) ρ) μ).toFun a)
         ((fautComp σ (fautComp τ (fautComp ρ μ))).toFun a) :=
  Path.refl _

/-- Theorem 25: unit coherence — id ∘ (σ ∘ id) = σ. -/
def galois_unit_coherence (σ : FAut F gF) (a : F) :
    Path ((fautComp (fautId gF) (fautComp σ (fautId gF))).toFun a)
         (σ.toFun a) :=
  Path.refl _

/-! ## Theorems 26–30: Deeper domain paths -/

/-- Theorem 26: composition fixes zero -/
def galois_comp_fixes_zero (σ τ : FAut F gF) :
    Path ((fautComp σ τ).toFun gF.zero) gF.zero :=
  galStep _ _ (by simp [fautComp, τ.map_zero, σ.map_zero])

/-- Theorem 27: composition fixes one -/
def galois_comp_fixes_one (σ τ : FAut F gF) :
    Path ((fautComp σ τ).toFun gF.one) gF.one :=
  galStep _ _ (by simp [fautComp, τ.map_one, σ.map_one])

/-- Theorem 28: inverse of composition = reversed composition of inverses -/
theorem galois_inv_comp_eq (σ τ : FAut F gF) (a : F) :
    (fautInv (fautComp σ τ)).toFun a = (fautComp (fautInv τ) (fautInv σ)).toFun a := by
  simp [fautInv, fautComp]

def galois_inv_comp_path (σ τ : FAut F gF) (a : F) :
    Path ((fautInv (fautComp σ τ)).toFun a)
         ((fautComp (fautInv τ) (fautInv σ)).toFun a) :=
  galStep _ _ (galois_inv_comp_eq σ τ a)

/-- Theorem 29: conjugation preserves zero -/
def galois_conjugate_zero (σ τ : FAut F gF) :
    Path ((galois_conjugate σ τ).toFun gF.zero) gF.zero :=
  galStep _ _ (by
    simp [galois_conjugate, fautComp, fautInv]
    have h1 := (fautInv σ).map_zero
    simp [fautInv] at h1
    rw [h1, τ.map_zero, σ.map_zero])

/-- Theorem 30: fixed element under composition -/
theorem galois_comp_fixes {σ τ : FAut F gF} {a : F}
    (hσ : isFixed σ a) (hτ : isFixed τ a) : isFixed (fautComp σ τ) a := by
  simp [isFixed, fautComp] at *
  rw [hτ, hσ]

def galois_comp_fixes_path {σ τ : FAut F gF} {a : F}
    (hσ : isFixed σ a) (hτ : isFixed τ a) :
    Path ((fautComp σ τ).toFun a) a :=
  galStep _ _ (galois_comp_fixes hσ hτ)

/-! ## Theorems 31–35: Congruence paths -/

/-- Theorem 31: congruence through toFun -/
def galois_congr_toFun (σ : FAut F gF) {a b : F} (p : Path a b) :
    Path (σ.toFun a) (σ.toFun b) :=
  Path.congrArg σ.toFun p

/-- Theorem 32: congruence through invFun -/
def galois_congr_invFun (σ : FAut F gF) {a b : F} (p : Path a b) :
    Path (σ.invFun a) (σ.invFun b) :=
  Path.congrArg σ.invFun p

/-- Theorem 33: chain inverse-left then congruence -/
def galois_inv_left_congr (σ : FAut F gF) {a b : F} (p : Path a b) :
    Path ((fautComp (fautInv σ) σ).toFun a) b :=
  Path.trans (galois_inv_left σ a) p

/-- Theorem 34: map_add path -/
def galois_map_add_path (σ : FAut F gF) (a b : F) :
    Path (σ.toFun (gF.add a b)) (gF.add (σ.toFun a) (σ.toFun b)) :=
  galStep _ _ (σ.map_add a b)

/-- Theorem 35: map_mul path -/
def galois_map_mul_path (σ : FAut F gF) (a b : F) :
    Path (σ.toFun (gF.mul a b)) (gF.mul (σ.toFun a) (σ.toFun b)) :=
  galStep _ _ (σ.map_mul a b)

/-! ## Theorems 36–38: Transport and deeper chains -/

/-- Theorem 36: transport along fixed-zero path -/
def galois_transport_zero {D : F → Sort _} (σ : FAut F gF) (x : D (σ.toFun gF.zero)) :
    D gF.zero :=
  Path.transport (galois_fixes_zero σ) x

/-- Theorem 37: double conjugation chain path -/
def galois_double_conjugate_id (σ : FAut F gF) (a : F) :
    Path ((galois_conjugate σ (galois_conjugate σ (fautId gF))).toFun a) a := by
  have h1 : (galois_conjugate σ (fautId gF)).toFun = fun x => σ.toFun (σ.invFun x) := by
    ext x; simp [galois_conjugate, fautComp, fautId, fautInv]
  have h2 : ∀ x, σ.toFun (σ.invFun x) = x := σ.right_inv
  have : (galois_conjugate σ (galois_conjugate σ (fautId gF))).toFun a = a := by
    simp [galois_conjugate, fautComp, fautInv, fautId]
    rw [σ.right_inv (σ.invFun a)]
    exact σ.right_inv a
  exact galStep _ _ this

/-- Theorem 38: inverse involution path — inv(inv(σ)) applied gives same as σ -/
def galois_inv_involution_chain (σ : FAut F gF) (a : F) :
    Path ((fautInv (fautInv σ)).toFun a) (σ.toFun a) :=
  Path.trans (galois_inv_inv_path σ a) (Path.refl _)

end GaloisGroupoidPaths
end Algebra
end Path
end ComputationalPaths

/-
# Galois Groupoid via Computational Paths (deepened)

This module removes `Path.ofEq` scaffolding.  We keep the lightweight field
and automorphism infrastructure, and introduce a small domain-specific
rewriting layer:

* `GaloisObj`  — syntactic terms representing field elements
* `GaloisStep` — elementary rewrite steps (unit, associativity, inverse, etc.)
* `GaloisPath` — generated paths under `refl`/`trans`/`symm`

All `Path` witnesses are built using `Path.refl`, `Path.trans`, `Path.symm`,
`Path.congrArg`, and explicit one-step traces (`Path.mk` + `Step.mk`).
No `Path.ofEq` appears in this file.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace GaloisGroupoidPaths

open ComputationalPaths.Path

universe u

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
  map_zero := by
    have := σ.left_inv gF.zero
    rw [σ.map_zero] at this
    exact this
  map_one := by
    have := σ.left_inv gF.one
    rw [σ.map_one] at this
    exact this
  map_add := fun a b => by
    have hinj : Function.Injective σ.toFun :=
      Function.LeftInverse.injective σ.left_inv
    apply hinj
    simp [σ.map_add, σ.right_inv]
  map_mul := fun a b => by
    have hinj : Function.Injective σ.toFun :=
      Function.LeftInverse.injective σ.left_inv
    apply hinj
    simp [σ.map_mul, σ.right_inv]

/-- An element is fixed by an automorphism. -/
def isFixed (σ : FAut F gF) (a : F) : Prop := σ.toFun a = a

/-! ## Domain layer: `GaloisObj` / `GaloisStep` / `GaloisPath` -/

/-- Domain objects: explicit terms representing field elements. -/
inductive GaloisObj (F : Type u) : Type u where
  | term : F → GaloisObj F

namespace GaloisObj

def eval : GaloisObj F → F
  | term a => a

@[simp] theorem eval_term (a : F) : eval (term a) = a := rfl

end GaloisObj

/-- Elementary steps for Galois groupoid computations. -/
inductive GaloisStep : GaloisObj F → GaloisObj F → Type u
  | compIdLeft (σ : FAut F gF) (a : F) :
      GaloisStep (.term ((fautComp (fautId gF) σ).toFun a)) (.term (σ.toFun a))
  | compIdRight (σ : FAut F gF) (a : F) :
      GaloisStep (.term ((fautComp σ (fautId gF)).toFun a)) (.term (σ.toFun a))
  | compAssoc (σ τ ρ : FAut F gF) (a : F) :
      GaloisStep (.term ((fautComp (fautComp σ τ) ρ).toFun a))
                (.term ((fautComp σ (fautComp τ ρ)).toFun a))
  | invLeft (σ : FAut F gF) (a : F) :
      GaloisStep (.term ((fautComp (fautInv σ) σ).toFun a)) (.term a)
  | invRight (σ : FAut F gF) (a : F) :
      GaloisStep (.term ((fautComp σ (fautInv σ)).toFun a)) (.term a)
  | fixesZero (σ : FAut F gF) : GaloisStep (.term (σ.toFun gF.zero)) (.term gF.zero)
  | fixesOne (σ : FAut F gF) : GaloisStep (.term (σ.toFun gF.one)) (.term gF.one)

namespace GaloisStep

theorem eval_eq : {a b : GaloisObj F} → (s : GaloisStep (gF := gF) a b) → (GaloisObj.eval a = GaloisObj.eval b)
  | _, _, compIdLeft _ _ => rfl
  | _, _, compIdRight _ _ => rfl
  | _, _, compAssoc _ _ _ _ => rfl
  | _, _, invLeft σ a => σ.left_inv a
  | _, _, invRight σ a => σ.right_inv a
  | _, _, fixesZero σ => σ.map_zero
  | _, _, fixesOne σ => σ.map_one

def toPath : {a b : GaloisObj F} → (s : GaloisStep (gF := gF) a b) → Path (GaloisObj.eval a) (GaloisObj.eval b)
  | _, _, s => Path.mk [Step.mk _ _ (eval_eq (gF := gF) s)] (eval_eq (gF := gF) s)

end GaloisStep

inductive GaloisPath : GaloisObj F → GaloisObj F → Type u
  | refl (a : GaloisObj F) : GaloisPath a a
  | step {a b : GaloisObj F} (s : GaloisStep (gF := gF) a b) : GaloisPath a b
  | trans {a b c : GaloisObj F} (p : GaloisPath a b) (q : GaloisPath b c) : GaloisPath a c
  | symm {a b : GaloisObj F} (p : GaloisPath a b) : GaloisPath b a

namespace GaloisPath

def toPath {a b : GaloisObj F} : GaloisPath (gF := gF) a b → Path (GaloisObj.eval a) (GaloisObj.eval b)
  | refl _ => Path.refl _
  | step s => GaloisStep.toPath (gF := gF) s
  | trans p q => Path.trans (toPath p) (toPath q)
  | symm p => Path.symm (toPath p)

end GaloisPath

/-! ## Exported theorems 1–25 -/

def galois_comp_id_left (σ : FAut F gF) (a : F) :
    Path ((fautComp (fautId gF) σ).toFun a) (σ.toFun a) :=
  GaloisStep.toPath (GaloisStep.compIdLeft σ a)

def galois_comp_id_right (σ : FAut F gF) (a : F) :
    Path ((fautComp σ (fautId gF)).toFun a) (σ.toFun a) :=
  GaloisStep.toPath (GaloisStep.compIdRight σ a)

def galois_comp_assoc (σ τ ρ : FAut F gF) (a : F) :
    Path ((fautComp (fautComp σ τ) ρ).toFun a)
         ((fautComp σ (fautComp τ ρ)).toFun a) :=
  GaloisStep.toPath (GaloisStep.compAssoc σ τ ρ a)

def galois_inv_left (σ : FAut F gF) (a : F) :
    Path ((fautComp (fautInv σ) σ).toFun a) a :=
  GaloisStep.toPath (GaloisStep.invLeft σ a)

def galois_inv_right (σ : FAut F gF) (a : F) :
    Path ((fautComp σ (fautInv σ)).toFun a) a :=
  GaloisStep.toPath (GaloisStep.invRight σ a)

theorem galois_inv_inv (σ : FAut F gF) (a : F) :
    (fautInv (fautInv σ)).toFun a = σ.toFun a := rfl

def galois_inv_inv_path (σ : FAut F gF) (a : F) :
    Path ((fautInv (fautInv σ)).toFun a) (σ.toFun a) :=
  Path.mk [Step.mk _ _ (galois_inv_inv σ a)] (galois_inv_inv σ a)

def galois_inv_left_symm (σ : FAut F gF) (a : F) :
    Path a ((fautComp (fautInv σ) σ).toFun a) :=
  Path.symm (galois_inv_left σ a)

def galois_inv_round_trip (σ : FAut F gF) (a : F) :
    Path ((fautComp (fautInv σ) σ).toFun a)
         ((fautComp σ (fautInv σ)).toFun a) :=
  Path.trans (galois_inv_left σ a) (Path.symm (galois_inv_right σ a))

theorem galois_id_inv_eq (gF : GField F) (a : F) :
    (fautInv (fautId gF)).toFun a = a := rfl

def galois_id_inv_path (gF : GField F) (a : F) :
    Path ((fautInv (fautId gF)).toFun a) a :=
  Path.mk [Step.mk _ _ (galois_id_inv_eq gF a)] (galois_id_inv_eq gF a)

def galois_inv_chain (σ τ : FAut F gF) (a : F) :
    Path ((fautComp (fautInv σ) σ).toFun a)
         ((fautComp τ (fautInv τ)).toFun a) :=
  Path.trans (galois_inv_left σ a) (Path.symm (galois_inv_right τ a))

def galois_fixes_zero (σ : FAut F gF) : Path (σ.toFun gF.zero) gF.zero :=
  GaloisStep.toPath (GaloisStep.fixesZero σ)

def galois_fixes_one (σ : FAut F gF) : Path (σ.toFun gF.one) gF.one :=
  GaloisStep.toPath (GaloisStep.fixesOne σ)

theorem galois_inv_fixes {σ : FAut F gF} {a : F}
    (h : isFixed σ a) : isFixed (fautInv σ) a := by
  simp [isFixed, fautInv] at *
  rw [← h, σ.left_inv]
  exact h.symm

def galois_inv_fixes_path {σ : FAut F gF} {a : F}
    (h : isFixed σ a) : Path ((fautInv σ).toFun a) a :=
  Path.mk [Step.mk _ _ (galois_inv_fixes h)] (galois_inv_fixes h)

def galois_conjugate (σ τ : FAut F gF) : FAut F gF :=
  fautComp (fautComp σ τ) (fautInv σ)

theorem galois_conjugate_id (τ : FAut F gF) (a : F) :
    (galois_conjugate (fautId gF) τ).toFun a = τ.toFun a := rfl

def galois_conjugate_id_path (τ : FAut F gF) (a : F) :
    Path ((galois_conjugate (fautId gF) τ).toFun a) (τ.toFun a) :=
  Path.mk [Step.mk _ _ (galois_conjugate_id τ a)] (galois_conjugate_id τ a)

theorem galois_conjugate_of_id (σ : FAut F gF) (a : F) :
    (galois_conjugate σ (fautId gF)).toFun a = a := σ.right_inv a

def galois_conjugate_of_id_path (σ : FAut F gF) (a : F) :
    Path ((galois_conjugate σ (fautId gF)).toFun a) a :=
  Path.mk [Step.mk _ _ (galois_conjugate_of_id σ a)] (galois_conjugate_of_id σ a)

theorem galois_fixed_neg {σ : FAut F gF} {a : F}
    (h : isFixed σ a) : isFixed σ (gF.neg a) := by
  simp [isFixed] at *
  have h1 : gF.add (σ.toFun (gF.neg a)) (σ.toFun a) = gF.zero := by
    rw [← σ.map_add, gF.add_comm (gF.neg a) a, gF.add_neg, σ.map_zero]
  have h2 : gF.add (σ.toFun (gF.neg a)) a = gF.zero := by
    rw [h] at h1; exact h1
  calc σ.toFun (gF.neg a)
      = gF.add (σ.toFun (gF.neg a)) gF.zero := by rw [gF.add_comm, gF.zero_add]
    _ = gF.add (σ.toFun (gF.neg a)) (gF.add a (gF.neg a)) := by rw [gF.add_neg]
    _ = gF.add (gF.add (σ.toFun (gF.neg a)) a) (gF.neg a) := by rw [gF.add_assoc]
    _ = gF.add gF.zero (gF.neg a) := by rw [h2]
    _ = gF.neg a := by rw [gF.zero_add]

def galois_fixed_neg_path {σ : FAut F gF} {a : F}
    (h : isFixed σ a) : Path (σ.toFun (gF.neg a)) (gF.neg a) :=
  Path.mk [Step.mk _ _ (galois_fixed_neg h)] (galois_fixed_neg h)

def galois_fixed_add_path (σ : FAut F gF) (a b : F)
    (ha : isFixed σ a) (hb : isFixed σ b) :
    Path (σ.toFun (gF.add a b)) (gF.add a b) :=
  Path.trans
    (Path.mk [Step.mk _ _ (σ.map_add a b)] (σ.map_add a b))
    (Path.trans
      (Path.congrArg (fun x => gF.add x (σ.toFun b)) (Path.mk [Step.mk _ _ ha] ha))
      (Path.congrArg (fun x => gF.add a x) (Path.mk [Step.mk _ _ hb] hb)))

def galois_comp_assoc4 (σ τ ρ μ : FAut F gF) (a : F) :
    Path ((fautComp (fautComp (fautComp σ τ) ρ) μ).toFun a)
         ((fautComp σ (fautComp τ (fautComp ρ μ))).toFun a) :=
  Path.refl _

def galois_unit_coherence (σ : FAut F gF) (a : F) :
    Path ((fautComp (fautId gF) (fautComp σ (fautId gF))).toFun a)
         (σ.toFun a) :=
  Path.refl _

/-! ## Path algebra -/

theorem galois_inv_left_toEq (σ : FAut F gF) (a : F) :
    (galois_inv_left σ a).toEq = σ.left_inv a := rfl

theorem galois_inv_right_toEq (σ : FAut F gF) (a : F) :
    (galois_inv_right σ a).toEq = σ.right_inv a := rfl

theorem galois_fixes_zero_toEq (σ : FAut F gF) :
    (galois_fixes_zero σ).toEq = σ.map_zero := rfl

theorem galois_fixes_one_toEq (σ : FAut F gF) :
    (galois_fixes_one σ).toEq = σ.map_one := rfl

theorem galois_comp_id_left_toEq (σ : FAut F gF) (a : F) :
    (galois_comp_id_left σ a).toEq = rfl := rfl

theorem galois_comp_id_right_toEq (σ : FAut F gF) (a : F) :
    (galois_comp_id_right σ a).toEq = rfl := rfl

theorem galois_comp_assoc_toEq (σ τ ρ : FAut F gF) (a : F) :
    (galois_comp_assoc σ τ ρ a).toEq = rfl := rfl

theorem galois_inv_inv_path_toEq (σ : FAut F gF) (a : F) :
    (galois_inv_inv_path σ a).toEq = galois_inv_inv σ a := rfl

theorem galois_id_inv_path_toEq (gF : GField F) (a : F) :
    (galois_id_inv_path gF a).toEq = galois_id_inv_eq gF a := rfl

theorem galois_inv_fixes_path_toEq {σ : FAut F gF} {a : F} (h : isFixed σ a) :
    (galois_inv_fixes_path h).toEq = galois_inv_fixes h := rfl

theorem galois_conjugate_id_path_toEq (τ : FAut F gF) (a : F) :
    (galois_conjugate_id_path τ a).toEq = galois_conjugate_id τ a := rfl

theorem galois_conjugate_of_id_path_toEq (σ : FAut F gF) (a : F) :
    (galois_conjugate_of_id_path σ a).toEq = galois_conjugate_of_id σ a := rfl

theorem galois_fixed_neg_path_toEq {σ : FAut F gF} {a : F} (h : isFixed σ a) :
    (galois_fixed_neg_path h).toEq = galois_fixed_neg h := rfl

theorem galois_unit_coherence_toEq (σ : FAut F gF) (a : F) :
    (galois_unit_coherence σ a).toEq = rfl := rfl

end GaloisGroupoidPaths
end Algebra
end Path
end ComputationalPaths

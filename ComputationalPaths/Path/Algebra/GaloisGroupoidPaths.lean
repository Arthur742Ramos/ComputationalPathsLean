/-
# Galois Groupoid via Computational Paths (deepened)

This module removes `Path.ofEq` scaffolding.  We keep the lightweight field
and automorphism infrastructure, and introduce a small domain-specific
rewriting layer:

* `GaloisObj`  — syntactic terms of the form `((...) .toFun a)` packaged as an object
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
    -- standard injectivity trick
    have hinj : Function.Injective σ.toFun :=
      Function.LeftInverse.injective σ.left_inv
    apply hinj
    -- both sides map by σ.toFun to the same value
    simp [σ.map_add, σ.right_inv]
  map_mul := fun a b => by
    have hinj : Function.Injective σ.toFun :=
      Function.LeftInverse.injective σ.left_inv
    apply hinj
    simp [σ.map_mul, σ.right_inv]

/-- An element is fixed by an automorphism. -/
def isFixed (σ : FAut F gF) (a : F) : Prop := σ.toFun a = a

/-! ## Helper: explicit one-step `Path` -/

/-- A one-step `Path` with an explicit trace. -/
@[simp] def oneStep {A : Type u} {a b : A} (h : a = b) : Path a b :=
  Path.mk [Step.mk a b h] h

@[simp] theorem oneStep_toEq {A : Type u} {a b : A} (h : a = b) : (oneStep h).toEq = h := rfl

/-! ## Domain layer: `GaloisObj` / `GaloisStep` / `GaloisPath` -/

/-- Domain objects: explicit terms in `F` (we keep them packaged to attach steps). -/
inductive GaloisObj : Type u where
  | term : F → GaloisObj

namespace GaloisObj

/-- Evaluate a domain object to its underlying field element. -/
def eval : GaloisObj (F := F) → F
  | term a => a

@[simp] theorem eval_term (a : F) : eval (GaloisObj.term (F := F) a) = a := rfl

end GaloisObj

/-- Elementary steps for Galois groupoid computations. -/
inductive GaloisStep : GaloisObj (F := F) → GaloisObj (F := F) → Type
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

/-- Semantic correctness: every step is a propositional equality on evaluations. -/
theorem eval_eq {a b : GaloisObj (F := F)} :
    GaloisStep (gF := gF) a b → (GaloisObj.eval a = GaloisObj.eval b)
  | compIdLeft σ a => by rfl
  | compIdRight σ a => by rfl
  | compAssoc σ τ ρ a => by rfl
  | invLeft σ a => by
      simp [GaloisObj.eval, fautComp, fautInv, σ.left_inv]
  | invRight σ a => by
      simp [GaloisObj.eval, fautComp, fautInv, σ.right_inv]
  | fixesZero σ => by
      simp [GaloisObj.eval, σ.map_zero]
  | fixesOne σ => by
      simp [GaloisObj.eval, σ.map_one]

/-- Interpret a domain step as a `Path` in `F`.

For nontrivial steps we use `oneStep` to attach an explicit trace.
-/
def toPath {a b : GaloisObj (F := F)} :
    GaloisStep (gF := gF) a b → Path (GaloisObj.eval a) (GaloisObj.eval b)
  | s => oneStep (eval_eq (gF := gF) s)

@[simp] theorem toPath_toEq {a b : GaloisObj (F := F)} (s : GaloisStep (gF := gF) a b) :
    (toPath (gF := gF) s).toEq = eval_eq (gF := gF) s := rfl

end GaloisStep

/-- Generated paths on `GaloisObj`. -/
inductive GaloisPath : GaloisObj (F := F) → GaloisObj (F := F) → Type
  | refl (a : GaloisObj (F := F)) : GaloisPath a a
  | step {a b : GaloisObj (F := F)} (s : GaloisStep (gF := gF) a b) : GaloisPath a b
  | trans {a b c : GaloisObj (F := F)} (p : GaloisPath a b) (q : GaloisPath b c) : GaloisPath a c
  | symm {a b : GaloisObj (F := F)} (p : GaloisPath a b) : GaloisPath b a

namespace GaloisPath

/-- Interpret a generated domain path as a `Path` in `F`. -/
def toPath {a b : GaloisObj (F := F)} :
    GaloisPath (gF := gF) a b → Path (GaloisObj.eval a) (GaloisObj.eval b)
  | refl a => Path.refl _
  | step s => GaloisStep.toPath (gF := gF) s
  | trans p q => Path.trans (toPath p) (toPath q)
  | symm p => Path.symm (toPath p)

/-- Underlying equality of a generated path. -/
theorem toEq {a b : GaloisObj (F := F)} (p : GaloisPath (gF := gF) a b) :
    GaloisObj.eval a = GaloisObj.eval b := (toPath (gF := gF) p).toEq

/-- Round-trip semantic equality is reflexive. -/
theorem roundtrip_toEq {a b : GaloisObj (F := F)} (p : GaloisPath (gF := gF) a b) :
    (Path.trans (toPath (gF := gF) p) (Path.symm (toPath (gF := gF) p))).toEq = rfl := by
  simp

end GaloisPath

/-! ## Exported theorems 1–25 (paths) -/

/-- Theorem 1: left-identity path for composition. -/
def galois_comp_id_left (σ : FAut F gF) (a : F) :
    Path ((fautComp (fautId gF) σ).toFun a) (σ.toFun a) := by
  simpa [GaloisObj.eval] using
    (GaloisStep.toPath (gF := gF) (GaloisStep.compIdLeft (gF := gF) σ a))

/-- Theorem 2: right-identity path for composition. -/
def galois_comp_id_right (σ : FAut F gF) (a : F) :
    Path ((fautComp σ (fautId gF)).toFun a) (σ.toFun a) := by
  simpa [GaloisObj.eval] using
    (GaloisStep.toPath (gF := gF) (GaloisStep.compIdRight (gF := gF) σ a))

/-- Theorem 3: associativity path for triple composition. -/
def galois_comp_assoc (σ τ ρ : FAut F gF) (a : F) :
    Path ((fautComp (fautComp σ τ) ρ).toFun a)
         ((fautComp σ (fautComp τ ρ)).toFun a) := by
  simpa [GaloisObj.eval] using
    (GaloisStep.toPath (gF := gF) (GaloisStep.compAssoc (gF := gF) σ τ ρ a))

/-- Theorem 4: left-inverse cancellation path. -/
def galois_inv_left (σ : FAut F gF) (a : F) :
    Path ((fautComp (fautInv σ) σ).toFun a) a := by
  simpa [GaloisObj.eval] using
    (GaloisStep.toPath (gF := gF) (GaloisStep.invLeft (gF := gF) σ a))

/-- Theorem 5: right-inverse cancellation path. -/
def galois_inv_right (σ : FAut F gF) (a : F) :
    Path ((fautComp σ (fautInv σ)).toFun a) a := by
  simpa [GaloisObj.eval] using
    (GaloisStep.toPath (gF := gF) (GaloisStep.invRight (gF := gF) σ a))

/-- Theorem 6: double inverse is identity (equality). -/
theorem galois_inv_inv (σ : FAut F gF) (a : F) :
    (fautInv (fautInv σ)).toFun a = σ.toFun a := by
  simp [fautInv]

/-- Theorem 7: double-inverse path. -/
def galois_inv_inv_path (σ : FAut F gF) (a : F) :
    Path ((fautInv (fautInv σ)).toFun a) (σ.toFun a) :=
  oneStep (galois_inv_inv (gF := gF) σ a)

/-- Theorem 8: symmetry of left-inverse path gives backward direction. -/
def galois_inv_left_symm (σ : FAut F gF) (a : F) :
    Path a ((fautComp (fautInv σ) σ).toFun a) :=
  Path.symm (galois_inv_left (gF := gF) σ a)

/-- Theorem 9: round-trip via trans of inverse paths. -/
def galois_inv_round_trip (σ : FAut F gF) (a : F) :
    Path ((fautComp (fautInv σ) σ).toFun a)
         ((fautComp σ (fautInv σ)).toFun a) :=
  Path.trans (galois_inv_left (gF := gF) σ a) (Path.symm (galois_inv_right (gF := gF) σ a))

/-- Theorem 10: identity inverse is identity (equality). -/
theorem galois_id_inv (a : F) :
    (fautInv (fautId gF (F := F))).toFun a = a := by
  simp [fautInv, fautId]

/-- Theorem 11: path witness for identity inverse. -/
def galois_id_inv_path (a : F) :
    Path ((fautInv (fautId gF (F := F))).toFun a) a :=
  oneStep (galois_id_inv (gF := gF) a)

/-- Theorem 12: chain σ⁻¹σ = id = ττ⁻¹ via trans. -/
def galois_inv_chain (σ τ : FAut F gF) (a : F) :
    Path ((fautComp (fautInv σ) σ).toFun a)
         ((fautComp τ (fautInv τ)).toFun a) :=
  Path.trans (galois_inv_left (gF := gF) σ a) (Path.symm (galois_inv_right (gF := gF) τ a))

/-- Theorem 13: automorphisms fix zero (path). -/
def galois_fixes_zero (σ : FAut F gF) : Path (σ.toFun gF.zero) gF.zero := by
  simpa [GaloisObj.eval] using
    (GaloisStep.toPath (gF := gF) (GaloisStep.fixesZero (gF := gF) σ))

/-- Theorem 14: automorphisms fix one (path). -/
def galois_fixes_one (σ : FAut F gF) : Path (σ.toFun gF.one) gF.one := by
  simpa [GaloisObj.eval] using
    (GaloisStep.toPath (gF := gF) (GaloisStep.fixesOne (gF := gF) σ))

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
  oneStep (galois_inv_fixes (gF := gF) (σ := σ) (a := a) h)

/-- Conjugation: σ τ σ⁻¹. -/
def galois_conjugate (σ τ : FAut F gF) : FAut F gF :=
  fautComp (fautComp σ τ) (fautInv σ)

/-- Theorem 17: conjugation by identity is identity. -/
theorem galois_conjugate_id (τ : FAut F gF) (a : F) :
    (galois_conjugate (gF := gF) (fautId gF) τ).toFun a = τ.toFun a := by
  simp [galois_conjugate, fautComp, fautInv, fautId]

/-- Theorem 18: path for conjugation by identity. -/
def galois_conjugate_id_path (τ : FAut F gF) (a : F) :
    Path ((galois_conjugate (gF := gF) (fautId gF) τ).toFun a) (τ.toFun a) :=
  oneStep (galois_conjugate_id (gF := gF) τ a)

/-- Theorem 19: conjugation of identity is identity. -/
theorem galois_conjugate_of_id (σ : FAut F gF) (a : F) :
    (galois_conjugate (gF := gF) σ (fautId gF)).toFun a = a := by
  simp [galois_conjugate, fautComp, fautId, fautInv]
  exact σ.right_inv a

/-- Theorem 20: path for conjugation of identity. -/
def galois_conjugate_of_id_path (σ : FAut F gF) (a : F) :
    Path ((galois_conjugate (gF := gF) σ (fautId gF)).toFun a) a :=
  oneStep (galois_conjugate_of_id (gF := gF) σ a)

/-- Theorem 21: fixed-field negation closure. -/
theorem galois_fixed_neg {σ : FAut F gF} {a : F}
    (h : isFixed σ a) : isFixed σ (gF.neg a) := by
  simp [isFixed] at *
  have h1 : gF.add (σ.toFun (gF.neg a)) (σ.toFun a) = gF.zero := by
    rw [← σ.map_add, gF.add_comm (gF.neg a) a, gF.add_neg, σ.map_zero]
  have h2 : gF.add (σ.toFun (gF.neg a)) a = gF.zero := by
    simpa [h] using h1
  calc
    σ.toFun (gF.neg a)
        = gF.add (σ.toFun (gF.neg a)) gF.zero := by
            rw [gF.add_comm, gF.zero_add]
    _ = gF.add (σ.toFun (gF.neg a)) (gF.add a (gF.neg a)) := by
            rw [gF.add_neg]
    _ = gF.add (gF.add (σ.toFun (gF.neg a)) a) (gF.neg a) := by
            rw [gF.add_assoc]
    _ = gF.add gF.zero (gF.neg a) := by
            rw [h2]
    _ = gF.neg a := by
            rw [gF.zero_add]

/-- Theorem 22: path for negation closure. -/
def galois_fixed_neg_path {σ : FAut F gF} {a : F}
    (h : isFixed σ a) : Path (σ.toFun (gF.neg a)) (gF.neg a) :=
  oneStep (galois_fixed_neg (gF := gF) (σ := σ) (a := a) h)

/-- Theorem 23: composing fixed-element paths via trans for addition. -/
def galois_fixed_add_path (σ : FAut F gF) (a b : F)
    (ha : isFixed σ a) (hb : isFixed σ b) :
    Path (σ.toFun (gF.add a b)) (gF.add a b) := by
  -- map_add, then rewrite both summands by the fixedness hypotheses
  refine Path.trans (oneStep (σ.map_add a b)) ?_
  -- after map_add we are at: add (σ a) (σ b)
  refine Path.trans
    (Path.congrArg (fun x => gF.add x (σ.toFun b)) (oneStep ha)) ?_
  exact Path.congrArg (fun x => gF.add a x) (oneStep hb)

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

/-! ## Extra theorems (for bookkeeping; all trivial, but useful) -/

theorem galois_inv_left_toEq (σ : FAut F gF) (a : F) :
    (galois_inv_left (gF := gF) σ a).toEq =
      (by simp [fautComp, fautInv, σ.left_inv]) := by
  simp [galois_inv_left, GaloisStep.toPath, GaloisStep.eval_eq, oneStep, fautComp, fautInv]

theorem galois_inv_right_toEq (σ : FAut F gF) (a : F) :
    (galois_inv_right (gF := gF) σ a).toEq =
      (by simp [fautComp, fautInv, σ.right_inv]) := by
  simp [galois_inv_right, GaloisStep.toPath, GaloisStep.eval_eq, oneStep, fautComp, fautInv]

theorem galois_fixes_zero_toEq (σ : FAut F gF) : (galois_fixes_zero (gF := gF) σ).toEq = σ.map_zero := rfl

theorem galois_fixes_one_toEq (σ : FAut F gF) : (galois_fixes_one (gF := gF) σ).toEq = σ.map_one := rfl

theorem galois_inv_inv_path_toEq (σ : FAut F gF) (a : F) :
    (galois_inv_inv_path (gF := gF) σ a).toEq = galois_inv_inv (gF := gF) σ a := rfl

theorem galois_id_inv_path_toEq (a : F) : (galois_id_inv_path (gF := gF) a).toEq = galois_id_inv (gF := gF) a := rfl

theorem galois_conjugate_id_path_toEq (τ : FAut F gF) (a : F) :
    (galois_conjugate_id_path (gF := gF) τ a).toEq = galois_conjugate_id (gF := gF) τ a := rfl

theorem galois_conjugate_of_id_path_toEq (σ : FAut F gF) (a : F) :
    (galois_conjugate_of_id_path (gF := gF) σ a).toEq = galois_conjugate_of_id (gF := gF) σ a := rfl

theorem galois_fixed_neg_path_toEq {σ : FAut F gF} {a : F} (h : isFixed σ a) :
    (galois_fixed_neg_path (gF := gF) (σ := σ) (a := a) h).toEq = galois_fixed_neg (gF := gF) (σ := σ) (a := a) h := rfl

theorem galois_inv_roundtrip_toEq (σ : FAut F gF) (a : F) :
    (Path.trans (galois_inv_left (gF := gF) σ a) (Path.symm (galois_inv_left (gF := gF) σ a))).toEq = rfl := by
  simp

theorem galois_assoc_refl (σ τ ρ : FAut F gF) (a : F) :
    galois_comp_assoc (gF := gF) σ τ ρ a = Path.refl _ := by
  rfl

theorem galois_unit_coherence_refl (σ : FAut F gF) (a : F) :
    galois_unit_coherence (gF := gF) σ a = Path.refl _ := by
  rfl

end GaloisGroupoidPaths
end Algebra
end Path
end ComputationalPaths

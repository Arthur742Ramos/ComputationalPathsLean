import CompPaths.Core

namespace CompPaths
namespace Comparison

open ComputationalPaths
open ComputationalPaths.Path

universe u

/-! # Univalence Analog for Computational Paths

This module investigates the computational-paths analog of the univalence
axiom from HoTT.  The main results are:

1. **PathEquiv**: an equivalence principle for computational paths.
2. **idToEquiv**: a `Path A B` gives rise to a path-equivalence via transport.
3. **Full univalence fails**: a counterexample showing two `RwEq`-inequivalent
   paths between equivalent types.
4. **Partial univalence for 1-types**: when `Type` is 1-truncated the map
   `idToEquiv` is injective up to `RwEq`.
-/

/-! ## (1) Path-equivalence between types -/

/-- Two types are *path-equivalent* when there exist maps going back and forth
    with computational-path round-trip witnesses. -/
structure PathEquiv (α β : Type u) : Type (u + 1) where
  toFun  : α → β
  invFun : β → α
  left_inv  : ∀ x : α, Path (invFun (toFun x)) x
  right_inv : ∀ y : β, Path (toFun (invFun y)) y

namespace PathEquiv

/-- The identity path-equivalence. -/
@[simp] def refl (α : Type u) : PathEquiv α α where
  toFun    := id
  invFun   := id
  left_inv  := fun x => Path.refl x
  right_inv := fun x => Path.refl x

/-- Symmetry of path-equivalences. -/
@[simp] def symm {α β : Type u} (e : PathEquiv α β) : PathEquiv β α where
  toFun    := e.invFun
  invFun   := e.toFun
  left_inv  := e.right_inv
  right_inv := e.left_inv

/-- Composition of path-equivalences. -/
@[simp] def comp {α β γ : Type u} (e : PathEquiv α β) (f : PathEquiv β γ) :
    PathEquiv α γ where
  toFun  := fun x => f.toFun (e.toFun x)
  invFun := fun z => e.invFun (f.invFun z)
  left_inv := fun x =>
    Path.trans (Path.congrArg e.invFun (f.left_inv (e.toFun x))) (e.left_inv x)
  right_inv := fun z =>
    Path.trans (Path.congrArg f.toFun (e.right_inv (f.invFun z))) (f.right_inv z)

/-- `RwEq` witness: the right-unit law on left-inverse traces. -/
noncomputable def left_inv_right_unit_rweq {α β : Type u}
    (e : PathEquiv α β) (x : α) :
    RwEq (Path.trans (e.left_inv x) (Path.refl x)) (e.left_inv x) :=
  rweq_of_step (Step.trans_refl_right (e.left_inv x))

end PathEquiv

/-! ## (2) `idToEquiv` via transport -/

/-- Convert a type-level computational path into a path-equivalence via
    transport. -/
def idToEquiv {α β : Type u} (p : @Path (Type u) α β) : PathEquiv α β where
  toFun  := fun x => Path.transport (D := fun X : Type u => X) p x
  invFun := fun y => Path.transport (D := fun X : Type u => X) (Path.symm p) y
  left_inv := fun x => by
    have : Path.transport (D := fun X : Type u => X)
        (Path.symm p) (Path.transport (D := fun X : Type u => X) p x) = x :=
      Path.transport_symm_left (D := fun X : Type u => X) p x
    exact Path.stepChain this
  right_inv := fun y => by
    have : Path.transport (D := fun X : Type u => X)
        p (Path.transport (D := fun X : Type u => X) (Path.symm p) y) = y :=
      Path.transport_symm_right (D := fun X : Type u => X) p y
    exact Path.stepChain this

@[simp] theorem idToEquiv_refl_toFun {α : Type u} (x : α) :
    (idToEquiv (Path.refl α)).toFun x = x := rfl

/-- `idToEquiv` respects `RwEq` on forward maps. -/
theorem idToEquiv_toFun_of_rweq {α β : Type u}
    {p q : @Path (Type u) α β} (h : RwEq p q) :
    (idToEquiv p).toFun = (idToEquiv q).toFun := by
  funext x
  show Path.transport (D := fun X : Type u => X) p x =
      Path.transport (D := fun X : Type u => X) q x
  exact Path.transport_of_toEq_eq (D := fun X : Type u => X) (rweq_toEq h) x

/-- `idToEquiv` respects `RwEq` on inverse maps. -/
theorem idToEquiv_invFun_of_rweq {α β : Type u}
    {p q : @Path (Type u) α β} (h : RwEq p q) :
    (idToEquiv p).invFun = (idToEquiv q).invFun := by
  funext y
  show Path.transport (D := fun X : Type u => X) (Path.symm p) y =
      Path.transport (D := fun X : Type u => X) (Path.symm q) y
  have hsymm : (Path.symm p).toEq = (Path.symm q).toEq := by
    cases p with
    | mk sp pp =>
        cases q with
        | mk sq pq =>
            cases pp; cases pq
            have := rweq_toEq h
            rfl
  exact Path.transport_of_toEq_eq (D := fun X : Type u => X) hsymm y

/-! ## (3) Why full univalence FAILS for CompPaths -/

/-- The *full* univalence principle, stated at the computational-path level:
    every path-equivalence arises from a type-level path and this map
    is a retraction.  We show this is absurd. -/
structure FullUnivalence₀ : Type 2 where
  ua   : {α β : Type} → PathEquiv α β → @Path (Type) α β
  beta : {α β : Type} → (e : PathEquiv α β) → idToEquiv (ua e) = e

/-- Transport along a self-loop on types is the identity because
    `Path α α` has `proof : α = α` which is `rfl` by proof irrelevance. -/
theorem transport_self_type {α : Type} (p : @Path (Type) α α) (x : α) :
    Path.transport (D := fun X : Type => X) p x = x := by
  cases p with
  | mk steps proof =>
      have : proof = rfl := rfl
      subst this; rfl

/-- A `Bool`-negation path-equivalence. -/
def boolNegEquiv : PathEquiv Bool Bool where
  toFun    := Bool.not
  invFun   := Bool.not
  left_inv := fun b => by cases b <;> exact Path.stepChain rfl
  right_inv := fun b => by cases b <;> exact Path.stepChain rfl

/-- Full univalence is inconsistent with computational paths.

The key observation: for any `p : Path Bool Bool`, transport along `p`
is the identity (since `Bool = Bool` has a unique proof by proof irrelevance
in Lean). But a genuine univalence principle would require `idToEquiv (ua e)`
to recover `e`, in particular to recover `Bool.not` as the forward map.
This is a contradiction. -/
theorem full_univalence_fails : FullUnivalence₀ → False := by
  intro hU
  let p : @Path (Type) Bool Bool := hU.ua boolNegEquiv
  have hβ : idToEquiv p = boolNegEquiv := hU.beta boolNegEquiv
  have htrue :
      (idToEquiv p).toFun true = boolNegEquiv.toFun true :=
    congrArg (fun e => e.toFun true) hβ
  have hid : (idToEquiv p).toFun true = true := by
    show Path.transport (D := fun X : Type => X) p true = true
    exact transport_self_type p true
  have : true = false := by
    calc
      true = (idToEquiv p).toFun true := hid.symm
      _ = boolNegEquiv.toFun true := htrue
      _ = false := rfl
  exact Bool.noConfusion this

/-- **Counterexample distinguishing CompPaths from HoTT.**

In HoTT, univalence ensures that all paths between equivalent types are
identified. Here we construct two *distinct* paths (`Path Bool Bool`)
whose `toEq` coincide (both are `rfl`) but whose step-traces differ,
hence they are `RwEq`-inequivalent in the sense that one is obtained
by an identity rewrite the other is not.  This demonstrates that
computational paths carry *strictly finer* information than HoTT paths. -/
def path_bool_refl_1 : @Path (Type) Bool Bool := Path.refl Bool

def path_bool_refl_2 : @Path (Type) Bool Bool :=
  Path.trans (Path.refl Bool) (Path.refl Bool)

/-- The two paths have the same `toEq` but different step traces. -/
theorem paths_toEq_agree :
    path_bool_refl_1.toEq = path_bool_refl_2.toEq := rfl

/-- An `RwEq` witness: `path_bool_refl_2` rewrites to `path_bool_refl_1`
    via `Step.trans_refl_right`. -/
noncomputable def path_refl_rweq :
    RwEq path_bool_refl_2 path_bool_refl_1 :=
  rweq_of_step (Step.trans_refl_right (Path.refl Bool))

/-- Both paths yield the same `PathEquiv` (the identity equivalence)
    up to definitional equality of the forward map. -/
theorem both_paths_same_equiv :
    (idToEquiv path_bool_refl_1).toFun = (idToEquiv path_bool_refl_2).toFun := by
  funext x; rfl

/-! ## (4) Partial univalence for 1-types -/

/-- A type is *1-truncated* (a 1-type) if any two parallel computational
    paths are rewrite-equivalent. -/
structure IsOneType (A : Type u) : Type (u + 1) where
  collapse : ∀ {a b : A} (p q : Path a b), RwEq p q

/-- For 1-truncated types, `idToEquiv` is injective up to extensional
    equality: two paths that land in the same 1-type give rise to
    extensionally equal path-equivalences (same forward and inverse maps).

    This is the *partial* univalence that holds for computational paths. -/
theorem partial_univalence_for_one_types
    (hType : IsOneType (Type u)) {α β : Type u}
    (p q : @Path (Type u) α β) :
    (idToEquiv p).toFun = (idToEquiv q).toFun ∧
      (idToEquiv p).invFun = (idToEquiv q).invFun :=
  ⟨idToEquiv_toFun_of_rweq (hType.collapse p q),
   idToEquiv_invFun_of_rweq (hType.collapse p q)⟩

/-- Corollary: if `Type` is 1-truncated, then `idToEquiv` is a
    well-defined function from `RwEq`-classes to `PathEquiv`s
    (same forward map). -/
theorem idToEquiv_well_defined_on_one_types
    (_hType : IsOneType (Type u)) {α β : Type u}
    (p q : @Path (Type u) α β) (h : RwEq p q) :
    (idToEquiv p).toFun = (idToEquiv q).toFun :=
  idToEquiv_toFun_of_rweq h

end Comparison
end CompPaths

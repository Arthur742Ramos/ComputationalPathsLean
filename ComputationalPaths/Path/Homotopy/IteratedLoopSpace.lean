/-
# Iterated Loop Spaces

This module formalizes iterated loop spaces Ω^n in the computational paths
framework. We define n-fold loop spaces, iterated delooping, recognition for
En spaces, and group completion.

## Key Results

- `OmegaN`: iterated loop space Ω^n(X)
- `IteratedDelooping`: n-fold delooping data
- `EnSpaceData`: recognition data for En spaces
- `GroupCompletion`: group completion of a monoid-like space

## References

- May, "The Geometry of Iterated Loop Spaces"
- Boardman & Vogt, "Homotopy Invariant Algebraic Structures"
- Segal, "Categories and cohomology theories"
-/

import ComputationalPaths.Path.Homotopy.LoopSpaceAlgebra
import ComputationalPaths.Path.Homotopy.SuspensionLoop
import ComputationalPaths.Path.Homotopy.Loops

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace IteratedLoopSpace

open SuspensionLoop

universe u

/-! ## Iterated loop spaces -/

/-- The n-fold iterated loop space Ω^n(X) as a pointed type. -/
noncomputable def OmegaN (n : Nat) (X : Pointed) : Pointed :=
  Nat.recOn n X (fun _ acc => loopPointed acc)

/-- Ω^0(X) = X. -/
theorem omegaN_zero (X : Pointed) : OmegaN 0 X = X := rfl

/-- Ω^{n+1}(X) = Ω(Ω^n(X)). -/
theorem omegaN_succ (n : Nat) (X : Pointed) :
    OmegaN (n + 1) X = loopPointed (OmegaN n X) := rfl

/-! ## Operations on iterated loop spaces -/

/-- Composition in Ω^{n+1}(X), defined by loop composition. -/
noncomputable def omegaNComp (n : Nat) {X : Pointed}
    (p q : (OmegaN (n + 1) X).carrier) : (OmegaN (n + 1) X).carrier :=
  LoopSpace.comp p q

/-- Identity in Ω^{n+1}(X). -/
noncomputable def omegaNId (n : Nat) (X : Pointed) : (OmegaN (n + 1) X).carrier :=
  LoopSpace.id

/-- Inversion in Ω^{n+1}(X). -/
noncomputable def omegaNInv (n : Nat) {X : Pointed}
    (p : (OmegaN (n + 1) X).carrier) : (OmegaN (n + 1) X).carrier :=
  LoopSpace.inv p

noncomputable def omegaN_comp_assoc_rweq (n : Nat) {X : Pointed}
    (p q r : (OmegaN (n + 1) X).carrier) :
    RwEq (omegaNComp n (omegaNComp n p q) r)
      (omegaNComp n p (omegaNComp n q r)) := by
  simpa [omegaNComp, LoopSpace.comp] using LoopSpace.comp_assoc_rweq p q r

noncomputable def omegaN_id_comp_rweq (n : Nat) {X : Pointed}
    (p : (OmegaN (n + 1) X).carrier) :
    RwEq (omegaNComp n (omegaNId n X) p) p := by
  simpa [omegaNComp, omegaNId, LoopSpace.comp, LoopSpace.id] using LoopSpace.loop_refl_trans p

noncomputable def omegaN_comp_id_rweq (n : Nat) {X : Pointed}
    (p : (OmegaN (n + 1) X).carrier) :
    RwEq (omegaNComp n p (omegaNId n X)) p := by
  simpa [omegaNComp, omegaNId, LoopSpace.comp, LoopSpace.id] using LoopSpace.loop_trans_refl p

/-! ## Associativity and unit laws -/

/-- Associativity of composition in Ω^{n+1}(X). -/
noncomputable def omegaN_comp_assoc (n : Nat) {X : Pointed}
    (p q r : (OmegaN (n + 1) X).carrier) :
    RwEq (omegaNComp n (omegaNComp n p q) r)
      (omegaNComp n p (omegaNComp n q r)) :=
  omegaN_comp_assoc_rweq n p q r

/-- Left unit law in Ω^{n+1}(X). -/
noncomputable def omegaN_id_comp (n : Nat) {X : Pointed}
    (p : (OmegaN (n + 1) X).carrier) :
    RwEq (omegaNComp n (omegaNId n X) p) p :=
  omegaN_id_comp_rweq n p

/-- Right unit law in Ω^{n+1}(X). -/
noncomputable def omegaN_comp_id (n : Nat) {X : Pointed}
    (p : (OmegaN (n + 1) X).carrier) :
    RwEq (omegaNComp n p (omegaNId n X)) p :=
  omegaN_comp_id_rweq n p

/-! ## Iterated delooping -/

/-- Data for an n-fold delooping: a sequence of pointed types
    where each is the loop space of the next. -/
structure IteratedDelooping (X : Pointed) (n : Nat) where
  /-- The delooping levels. B 0 = X, B k is the k-th delooping. -/
  level : Fin (n + 1) → Pointed
  /-- Level 0 is X. -/
  level_zero : level ⟨0, Nat.zero_lt_succ n⟩ = X
  /-- Structure maps: level k → Ω(level (k+1)). -/
  structureMap : (k : Fin n) →
    PointedMap (level ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩)
      (loopPointed (level ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩))

/-- Trivial 0-fold delooping: just the space itself. -/
noncomputable def IteratedDelooping.zero (X : Pointed) : IteratedDelooping X 0 where
  level := fun _ => X
  level_zero := rfl
  structureMap := fun k => Fin.elim0 k

/-! ## En space recognition -/

/-- Recognition data for an En space: a type with an n-fold delooping
    where all structure maps are equivalences. -/
structure EnSpaceData (X : Pointed) (n : Nat) where
  /-- The n-fold delooping. -/
  delooping : IteratedDelooping X n
  /-- The structure maps are equivalences (modeled as having inverses). -/
  inverse : (k : Fin n) →
    PointedMap
      (loopPointed (delooping.level ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩))
      (delooping.level ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩)
  /-- Left inverse law. -/
  left_inv : ∀ (k : Fin n) (x : (delooping.level ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩).carrier),
    (inverse k).toFun ((delooping.structureMap k).toFun x) = x
  /-- Right inverse law. -/
  right_inv : ∀ (k : Fin n)
    (l : (loopPointed (delooping.level ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩)).carrier),
    (delooping.structureMap k).toFun ((inverse k).toFun l) = l

namespace EnSpaceData

variable {X : Pointed} {n : Nat} (E : EnSpaceData X n)

/-- `Path` witness for the left inverse law of an En-space structure map. -/
noncomputable def left_inv_path (k : Fin n)
    (x : (E.delooping.level ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩).carrier) :
    Path ((E.inverse k).toFun ((E.delooping.structureMap k).toFun x)) x :=
  Path.stepChain (E.left_inv k x)

/-- `Path` witness for the right inverse law of an En-space structure map. -/
noncomputable def right_inv_path (k : Fin n)
    (l : (loopPointed (E.delooping.level ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩)).carrier) :
    Path ((E.delooping.structureMap k).toFun ((E.inverse k).toFun l)) l :=
  Path.stepChain (E.right_inv k l)

end EnSpaceData

/-- An E1 space has a 1-fold delooping: it is a loop space. -/
noncomputable def E1SpaceData (X : Pointed) := EnSpaceData X 1

/-! ## Group completion -/

/-- Monoid data on a pointed type. -/
structure PointedMonoidData (X : Pointed) where
  /-- Multiplication. -/
  mul : X.carrier → X.carrier → X.carrier
  /-- Left unit. -/
  mul_pt_left : ∀ x, mul X.pt x = x
  /-- Right unit. -/
  mul_pt_right : ∀ x, mul x X.pt = x
  /-- Associativity. -/
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)

namespace PointedMonoidData

variable {X : Pointed} (M : PointedMonoidData X)

/-- `Path` witness for the left unit law. -/
noncomputable def mul_pt_left_path (x : X.carrier) :
    Path (M.mul X.pt x) x :=
  Path.stepChain (M.mul_pt_left x)

/-- `Path` witness for the right unit law. -/
noncomputable def mul_pt_right_path (x : X.carrier) :
    Path (M.mul x X.pt) x :=
  Path.stepChain (M.mul_pt_right x)

/-- `Path` witness for associativity. -/
noncomputable def mul_assoc_path (x y z : X.carrier) :
    Path (M.mul (M.mul x y) z) (M.mul x (M.mul y z)) :=
  Path.stepChain (M.mul_assoc x y z)

end PointedMonoidData

/-- Group completion data: a monoid together with its group completion. -/
structure GroupCompletion (X : Pointed) where
  /-- Monoid structure on X. -/
  monoid : PointedMonoidData X
  /-- The group completion as a pointed type. -/
  completion : Pointed
  /-- The completion map. -/
  map : PointedMap X completion
  /-- Multiplication on the completion. -/
  completionMul : completion.carrier → completion.carrier → completion.carrier
  /-- Inversion in the completion. -/
  inv : completion.carrier → completion.carrier
  /-- Left inverse in the completion. -/
  inv_left : ∀ y : completion.carrier,
    completionMul (inv y) y = completion.pt
  /-- Right inverse in the completion. -/
  inv_right : ∀ y : completion.carrier,
    completionMul y (inv y) = completion.pt

/-- Path-valued left inverse. -/
noncomputable def GroupCompletion.inv_left_path {X : Pointed} (G : GroupCompletion X)
    (y : G.completion.carrier) :
    Path (G.completionMul (G.inv y) y) G.completion.pt :=
  Path.stepChain (G.inv_left y)

/-- Path-valued right inverse. -/
noncomputable def GroupCompletion.inv_right_path {X : Pointed} (G : GroupCompletion X)
    (y : G.completion.carrier) :
    Path (G.completionMul y (G.inv y)) G.completion.pt :=
  Path.stepChain (G.inv_right y)

/-- The trivial group completion of a single point. -/
noncomputable def GroupCompletion.trivial : GroupCompletion { carrier := Unit, pt := () } where
  monoid :=
    { mul := fun _ _ => ()
      mul_pt_left := fun _ => rfl
      mul_pt_right := fun _ => rfl
      mul_assoc := fun _ _ _ => rfl }
  completion := { carrier := Unit, pt := () }
  map := { toFun := fun _ => (), map_pt := rfl }
  completionMul := fun _ _ => ()
  inv := fun _ => ()
  inv_left := fun _ => rfl
  inv_right := fun _ => rfl

/-- `Path` witness for the left inverse law in the trivial group completion. -/
noncomputable def GroupCompletion.trivial_inv_left_path
    (y : GroupCompletion.trivial.completion.carrier) :
    Path
      (GroupCompletion.trivial.completionMul (GroupCompletion.trivial.inv y) y)
      GroupCompletion.trivial.completion.pt :=
  GroupCompletion.inv_left_path GroupCompletion.trivial y

/-- `Path` witness for the right inverse law in the trivial group completion. -/
noncomputable def GroupCompletion.trivial_inv_right_path
    (y : GroupCompletion.trivial.completion.carrier) :
    Path
      (GroupCompletion.trivial.completionMul y (GroupCompletion.trivial.inv y))
      GroupCompletion.trivial.completion.pt :=
  GroupCompletion.inv_right_path GroupCompletion.trivial y

/-! ## Summary -/

end IteratedLoopSpace
end Homotopy
end Path
end ComputationalPaths

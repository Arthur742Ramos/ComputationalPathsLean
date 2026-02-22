/-
# Little Cubes Operad

This module formalizes the little n-cubes operad in the computational paths
framework. We define the little n-cube embeddings, the En operad, composition
of cubes, and connect to the recognition principle.

## Key Results

- `SubInterval`: sub-intervals of [0,1]
- `RectEmbed`: rectilinear embeddings
- `LittleCubeConfig`: configurations of disjoint little cubes
- `EnOperad`: the En operad as a clean operad
- `EnAlgebra`: algebras over the En operad

## References

- Boardman & Vogt, "Homotopy Invariant Algebraic Structures"
- May, "The Geometry of Iterated Loop Spaces"
- Fresse, "Homotopy of Operads and Grothendieck–Teichmüller Groups"
-/

import ComputationalPaths.Path.Algebra.OperadTheory
import ComputationalPaths.Path.Homotopy.SuspensionLoop

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace LittleCubesOperad

open OperadTheory
open SuspensionLoop

universe u

/-! ## Intervals and cubes -/

/-- A sub-interval of [0, 1], represented by rational-like endpoints
    (natural numbers standing in for coordinates). -/
structure SubInterval where
  /-- Left endpoint. -/
  lo : Nat
  /-- Right endpoint. -/
  hi : Nat
  /-- Non-degeneracy: lo < hi. -/
  valid : lo < hi

/-- A rectilinear embedding of [0,1]^n into [0,1]^n, given by n sub-intervals. -/
structure RectEmbed (n : Nat) where
  /-- The sub-interval in each coordinate direction. -/
  intervals : Fin n → SubInterval

/-- Two rectilinear embeddings have disjoint images if their intervals are
    disjoint in at least one coordinate. -/
noncomputable def disjointImages {n : Nat} (e₁ e₂ : RectEmbed n) : Prop :=
  ∃ i : Fin n,
    (e₁.intervals i).hi ≤ (e₂.intervals i).lo ∨
    (e₂.intervals i).hi ≤ (e₁.intervals i).lo

/-! ## Little n-cubes -/

/-- A little n-cube configuration: k pairwise-disjoint rectilinear embeddings
    of [0,1]^n into [0,1]^n. -/
structure LittleCubeConfig (n : Nat) (k : Nat) where
  /-- The k embeddings. -/
  cubes : Fin k → RectEmbed n
  /-- All pairs are disjoint. -/
  pairwise_disjoint : ∀ i j : Fin k, i ≠ j → disjointImages (cubes i) (cubes j)

/-- The identity little cube: a single cube filling the whole space. -/
noncomputable def identityCube (n : Nat) : LittleCubeConfig n 1 where
  cubes := fun _ =>
    { intervals := fun _ => { lo := 0, hi := 1, valid := Nat.zero_lt_one } }
  pairwise_disjoint := fun i j h => absurd (Fin.ext (by omega)) h

/-! ## En operad -/

/-- The space of little n-cube configurations of arity k. -/
noncomputable def EnSpace (n : Nat) (k : Nat) : Type :=
  LittleCubeConfig n k

/-- The symmetric group acts on little cube configurations by
    permuting the labels. -/
noncomputable def enAction (n : Nat) {k : Nat} (σ : Perm k) (c : EnSpace n k) :
    EnSpace n k where
  cubes := c.cubes ∘ σ.invFun
  pairwise_disjoint := fun i j h => by
    apply c.pairwise_disjoint (σ.invFun i) (σ.invFun j)
    intro heq
    apply h
    have h1 : σ.toFun (σ.invFun i) = σ.toFun (σ.invFun j) := by rw [heq]
    rw [σ.right_inv, σ.right_inv] at h1
    exact h1

/-- The En operad as a clean operad. -/
noncomputable def enOperad (n : Nat) : CleanOperad where
  ops := fun k => EnSpace n k
  unit := identityCube n
  action := fun σ c => enAction n σ c
  action_id := fun _ => rfl
  action_comp := fun _ _ _ => rfl

/-! ## Composition of little cubes -/

/-- Rescale a sub-interval: place inner inside outer. -/
noncomputable def rescaleInterval (outer inner : SubInterval) : SubInterval where
  lo := outer.lo + inner.lo
  hi := outer.lo + inner.hi
  valid := Nat.add_lt_add_left inner.valid outer.lo

/-- Compose two rectilinear embeddings: place inner inside outer. -/
noncomputable def composeEmbed {n : Nat} (outer inner : RectEmbed n) : RectEmbed n where
  intervals := fun i => rescaleInterval (outer.intervals i) (inner.intervals i)

/-! ## En-algebras -/

/-- An En-algebra structure on a type: data connecting the En operad
    action to the algebraic structure. -/
structure EnAlgebra (n : Nat) where
  /-- The carrier type. -/
  carrier : Type u
  /-- Structure map: a little cube configuration acts on tuples. -/
  act : {k : Nat} → EnSpace n k → (Fin k → carrier) → carrier
  /-- Equivariance under permutations. -/
  equivariant : {k : Nat} → ∀ (σ : Perm k) (c : EnSpace n k) (xs : Fin k → carrier),
    act (enAction n σ c) xs = act c (xs ∘ σ.invFun)
  /-- Unit: acting by the identity cube on a single element returns it. -/
  unit_act : ∀ x : carrier,
    act (identityCube n) (fun _ => x) = x

/-- The trivial En-algebra on Unit. -/
noncomputable def EnAlgebra.trivial (n : Nat) : EnAlgebra n where
  carrier := Unit
  act := fun _ _ => ()
  equivariant := fun _ _ _ => rfl
  unit_act := fun _ => rfl

/-- Path-valued unit law. -/
noncomputable def EnAlgebra.unit_act_path {n : Nat} (A : EnAlgebra n) (x : A.carrier) :
    Path (A.act (identityCube n) (fun _ => x)) x :=
  Path.stepChain (A.unit_act x)

/-- Path-valued equivariance. -/
noncomputable def EnAlgebra.equivariant_path {n : Nat} (A : EnAlgebra n)
    {k : Nat} (σ : Perm k) (c : EnSpace n k) (xs : Fin k → A.carrier) :
    Path (A.act (enAction n σ c) xs) (A.act c (xs ∘ σ.invFun)) :=
  Path.stepChain (A.equivariant σ c xs)

/-! ## Connection to recognition principle -/

/-- An En-algebra with a group-like structure admits delooping data.
    This packages the recognition principle connection. -/
structure EnRecognitionData (n : Nat) where
  /-- The En-algebra. -/
  algebra : EnAlgebra n
  /-- The target pointed type. -/
  target : Pointed
  /-- Map from the algebra carrier to the target. -/
  toTarget : algebra.carrier → target.carrier
  /-- Map back from the target. -/
  fromTarget : target.carrier → algebra.carrier
  /-- Left inverse. -/
  left_inv : ∀ x, fromTarget (toTarget x) = x
  /-- Right inverse. -/
  right_inv : ∀ y, toTarget (fromTarget y) = y

/-- Path-valued left inverse. -/
noncomputable def EnRecognitionData.left_inv_path {n : Nat} (d : EnRecognitionData n) (x : d.algebra.carrier) :
    Path (d.fromTarget (d.toTarget x)) x :=
  Path.stepChain (d.left_inv x)

/-! ## Morphisms of En-algebras -/

/-- Morphism between En-algebras. -/
structure EnAlgebraHom {n : Nat} (A B : EnAlgebra n) where
  /-- The underlying function. -/
  toFun : A.carrier → B.carrier
  /-- Compatibility with the operad action. -/
  map_act : {k : Nat} → ∀ (c : EnSpace n k) (xs : Fin k → A.carrier),
    toFun (A.act c xs) = B.act c (toFun ∘ xs)

/-- Identity En-algebra morphism. -/
noncomputable def EnAlgebraHom.id {n : Nat} (A : EnAlgebra n) : EnAlgebraHom A A where
  toFun := _root_.id
  map_act := fun _ _ => rfl

/-- Composition of En-algebra morphisms. -/
noncomputable def EnAlgebraHom.comp {n : Nat} {A B C : EnAlgebra n}
    (g : EnAlgebraHom B C) (f : EnAlgebraHom A B) : EnAlgebraHom A C where
  toFun := g.toFun ∘ f.toFun
  map_act := fun c xs => by
    simp only [Function.comp]
    rw [f.map_act, g.map_act]
    rfl

/-! ## Summary -/

end LittleCubesOperad
end Algebra
end Path
end ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace LittleCubesOperad

theorem identityCube_interval_lo (n : Nat) (i : Fin 1) (j : Fin n) :
    (((identityCube n).cubes i).intervals j).lo = 0 :=
  rfl

theorem identityCube_interval_hi (n : Nat) (i : Fin 1) (j : Fin n) :
    (((identityCube n).cubes i).intervals j).hi = 1 :=
  rfl

theorem enSpace_def (n k : Nat) :
    EnSpace n k = LittleCubeConfig n k :=
  rfl

theorem rescaleInterval_lo (outer inner : SubInterval) :
    (rescaleInterval outer inner).lo = outer.lo + inner.lo :=
  rfl

theorem rescaleInterval_hi (outer inner : SubInterval) :
    (rescaleInterval outer inner).hi = outer.lo + inner.hi :=
  rfl

theorem composeEmbed_intervals {n : Nat} (outer inner : RectEmbed n) (i : Fin n) :
    (composeEmbed outer inner).intervals i =
      rescaleInterval (outer.intervals i) (inner.intervals i) :=
  rfl

theorem enAlgebra_trivial_carrier (n : Nat) :
    (EnAlgebra.trivial n).carrier = Unit :=
  rfl

theorem enAlgebra_unit_act_eq {n : Nat} (A : EnAlgebra n) (x : A.carrier) :
    A.act (identityCube n) (fun _ => x) = x :=
  A.unit_act x

theorem enRecognition_left_inv_eq {n : Nat}
    (d : EnRecognitionData n) (x : d.algebra.carrier) :
    d.fromTarget (d.toTarget x) = x :=
  d.left_inv x

theorem enAlgebraHom_id_apply {n : Nat} (A : EnAlgebra n) (x : A.carrier) :
    (EnAlgebraHom.id A).toFun x = x :=
  rfl

end LittleCubesOperad
end Algebra
end Path
end ComputationalPaths

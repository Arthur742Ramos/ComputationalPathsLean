/-
# Group Actions for Computational Paths

This module develops algebraic structure for `GroupAction` from
`Algebra/GroupStructures.lean`.  We define stabilizers, orbits, and action
homomorphisms, and we establish the standard action identities.

## Key results

- Orbit/stabilizer definitions
- Action homomorphisms (action as a group homomorphism)
- Product and conjugation actions
- Orbit invariance under action
-/

import ComputationalPaths.Path.Algebra.GroupStructures

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u v w

/-! ## Action lemmas -/

namespace GroupAction

variable {G : Type u} {X : Type v} {S : StrictGroup G}

/-- Action composition rewritten to the right. -/
theorem act_mul_right (A : GroupAction G S X) (g h : G) (x : X) :
    A.act g (A.act h x) = A.act (S.mul g h) x :=
  (A.act_mul g h x).symm

/-- Action by the identity is the identity function. -/
theorem act_id (A : GroupAction G S X) :
    A.act S.one = id := by
  funext x
  exact A.act_one x

end GroupAction

/-! ## Orbit and Stabilizer -/

namespace GroupAction

variable {G : Type u} {X : Type v} {S : StrictGroup G}

/-- Orbit of a point under a group action. -/
def Orbit (A : GroupAction G S X) (x : X) : X → Prop :=
  fun y => ∃ g : G, A.act g x = y

/-- Stabilizer of a point: elements fixing it. -/
def Stabilizer (A : GroupAction G S X) (x : X) : Subgroup G S where
  carrier := fun g => A.act g x = x
  one_mem := by
    simp [GroupAction.act_one']
  mul_mem := by
    intro g h hg hh
    simp [GroupAction.act_mul', hg, hh]
  inv_mem := by
    intro g hg
    calc
      A.act (S.inv g) x = A.act (S.inv g) (A.act g x) := by simp [hg]
      _ = A.act (S.mul (S.inv g) g) x := (A.act_mul _ _ _).symm
      _ = x := by simp [S.mul_left_inv, A.act_one]

/-- Membership in the orbit via identity. -/
theorem orbit_self (A : GroupAction G S X) (x : X) :
    A.Orbit x x := by
  refine ⟨S.one, ?_⟩
  simp [GroupAction.act_one']

/-- Orbit is closed under action. -/
theorem orbit_closed (A : GroupAction G S X) {x y : X} (g : G)
    (hy : A.Orbit x y) : A.Orbit x (A.act g y) := by
  rcases hy with ⟨h, rfl⟩
  refine ⟨S.mul g h, ?_⟩
  simp [GroupAction.act_mul']

/-- Two points in the same orbit are related by some group element. -/
theorem orbit_symm (A : GroupAction G S X) {x y : X}
    (hy : A.Orbit x y) : A.Orbit y x := by
  rcases hy with ⟨g, rfl⟩
  refine ⟨S.inv g, ?_⟩
  calc
    A.act (S.inv g) (A.act g x) = A.act (S.mul (S.inv g) g) x := (A.act_mul _ _ _).symm
    _ = x := by simp [S.mul_left_inv, A.act_one]

/-- Orbits are transitive under the action. -/
theorem orbit_trans (A : GroupAction G S X) {x y z : X}
    (hy : A.Orbit x y) (hz : A.Orbit y z) : A.Orbit x z := by
  rcases hy with ⟨g, rfl⟩
  rcases hz with ⟨h, rfl⟩
  refine ⟨S.mul h g, ?_⟩
  simp [GroupAction.act_mul']

end GroupAction

/-! ## Action homomorphisms -/

namespace GroupAction

variable {G : Type u} {X : Type v} {S : StrictGroup G}

/-- Action by a fixed element as a function. -/
@[simp] def actFun (A : GroupAction G S X) (g : G) : X → X :=
  fun x => A.act g x

/-- Action by a fixed element is invertible with inverse action. -/
@[simp] theorem actFun_inv (A : GroupAction G S X) (g : G) :
    actFun A (S.inv g) ∘ actFun A g = id := by
  funext x
  calc
    A.act (S.inv g) (A.act g x) = A.act (S.mul (S.inv g) g) x := (A.act_mul _ _ _).symm
    _ = x := by simp [S.mul_left_inv, A.act_one]

/-- Action defines a monoid homomorphism into endomorphisms. -/
@[simp] def actionHom (A : GroupAction G S X) :
    MonoidHom G (X → X) S.toStrictMonoid
      { mul := fun f g => fun x => f (g x)
        one := fun x => x
        mul_assoc := by intro f g h; rfl
        one_mul := by intro f; rfl
        mul_one := by intro f; rfl } where
  toFun := fun g => actFun A g
  map_mul := by
    intro g h
    funext x
    simp [actFun, GroupAction.act_mul']
  map_one := by
    funext x
    simp [actFun, GroupAction.act_one']

/-- Conjugation action of a strict group on itself. -/
@[simp] def conjugationAction (S : StrictGroup G) : GroupAction G S G where
  act := fun g x => S.mul (S.mul g x) (S.inv g)
  act_one := by
    intro x
    simp [S.one_mul, S.mul_one, StrictGroup.inv_one]
  act_mul := by
    intro g h x
    simp [S.mul_assoc, StrictGroup.inv_mul_eq]

/-- Product action on X × Y. -/
@[simp] def productAction {X : Type v} {Y : Type w}
    (A : GroupAction G S X) (B : GroupAction G S Y) : GroupAction G S (X × Y) where
  act := fun g xy => (A.act g xy.1, B.act g xy.2)
  act_one := by
    intro xy
    simp [GroupAction.act_one']
  act_mul := by
    intro g h xy
    simp [GroupAction.act_mul']

end GroupAction

end Algebra
end Path
end ComputationalPaths

/-
# Galois descent and torsor coherence via computational paths

This module packages Galois descent data and torsor trivialization
with explicit computational-path witnesses. The descent datum for a
Galois extension encodes the action of the Galois group on fiber data,
and the cocycle condition is tracked by `Path`, `Step`, and `RwEq`.
-/

import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Descent.PathCoherence

namespace ComputationalPaths
namespace Descent
namespace GaloisDescent

open Path

universe u v

/-- Group action data with path-level coherence for identity and
multiplicativity laws. -/
structure GroupActionData (G : Type u) (X : Type v) where
  mul : G → G → G
  one : G
  act : G → X → X
  mul_assoc : (g h k : G) → Path (mul (mul g h) k) (mul g (mul h k))
  one_mul : (g : G) → Path (mul one g) g
  mul_one : (g : G) → Path (mul g one) g
  act_one : (x : X) → Path (act one x) x
  act_mul : (g h : G) → (x : X) → Path (act (mul g h) x) (act g (act h x))

namespace GroupActionData

variable {G : Type u} {X : Type v} (A : GroupActionData G X)

/-- act_one right-cancels. -/
noncomputable def act_one_cancel_right (x : X) :
    RwEq (Path.trans (A.act_one x) (Path.symm (A.act_one x)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (A.act_one x)

/-- act_one left-cancels. -/
noncomputable def act_one_cancel_left (x : X) :
    RwEq (Path.trans (Path.symm (A.act_one x)) (A.act_one x))
         (Path.refl _) :=
  rweq_cmpA_inv_left (A.act_one x)

/-- act_mul right-cancels. -/
noncomputable def act_mul_cancel_right (g h : G) (x : X) :
    RwEq (Path.trans (A.act_mul g h x) (Path.symm (A.act_mul g h x)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (A.act_mul g h x)

/-- act_mul left-cancels. -/
noncomputable def act_mul_cancel_left (g h : G) (x : X) :
    RwEq (Path.trans (Path.symm (A.act_mul g h x)) (A.act_mul g h x))
         (Path.refl _) :=
  rweq_cmpA_inv_left (A.act_mul g h x)

/-- mul_assoc right-cancels. -/
noncomputable def mul_assoc_cancel_right (g h k : G) :
    RwEq (Path.trans (A.mul_assoc g h k) (Path.symm (A.mul_assoc g h k)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (A.mul_assoc g h k)

/-- one_mul right-unit. -/
noncomputable def one_mul_refl_right (g : G) :
    RwEq (Path.trans (A.one_mul g) (Path.refl _))
         (A.one_mul g) :=
  rweq_cmpA_refl_right (A.one_mul g)

/-- mul_one right-unit. -/
noncomputable def mul_one_refl_right (g : G) :
    RwEq (Path.trans (A.mul_one g) (Path.refl _))
         (A.mul_one g) :=
  rweq_cmpA_refl_right (A.mul_one g)

/-- act_one symm-symm. -/
noncomputable def act_one_symm_symm (x : X) :
    RwEq (Path.symm (Path.symm (A.act_one x)))
         (A.act_one x) :=
  rweq_symm_symm (A.act_one x)

/-- act_mul symm-symm. -/
noncomputable def act_mul_symm_symm (g h : G) (x : X) :
    RwEq (Path.symm (Path.symm (A.act_mul g h x)))
         (A.act_mul g h x) :=
  rweq_symm_symm (A.act_mul g h x)

/-- mul_assoc symm-symm. -/
noncomputable def mul_assoc_symm_symm (g h k : G) :
    RwEq (Path.symm (Path.symm (A.mul_assoc g h k)))
         (A.mul_assoc g h k) :=
  rweq_symm_symm (A.mul_assoc g h k)

/-- one_mul left-unit. -/
noncomputable def one_mul_refl_left (g : G) :
    RwEq (Path.trans (Path.refl _) (A.one_mul g))
         (A.one_mul g) :=
  rweq_cmpA_refl_left (A.one_mul g)

/-- act_one left-unit. -/
noncomputable def act_one_refl_left (x : X) :
    RwEq (Path.trans (Path.refl _) (A.act_one x))
         (A.act_one x) :=
  rweq_cmpA_refl_left (A.act_one x)

/-- act_mul left-unit. -/
noncomputable def act_mul_refl_left (g h : G) (x : X) :
    RwEq (Path.trans (Path.refl _) (A.act_mul g h x))
         (A.act_mul g h x) :=
  rweq_cmpA_refl_left (A.act_mul g h x)

end GroupActionData

/-- Galois descent datum with cocycle coherence via paths. -/
structure GaloisDescentDatum (G : Type u) (Fiber : Type v) where
  action : GroupActionData G Fiber
  /-- Descent isomorphism φ_g : F → F for each group element. -/
  phi : G → Fiber → Fiber
  /-- φ respects the group action. -/
  phi_act : (g : G) → (x : Fiber) → Path (phi g x) (action.act g x)
  /-- Cocycle condition: φ_{gh} = φ_g ∘ φ_h. -/
  cocycle : (g h : G) → (x : Fiber) →
    Path (phi (action.mul g h) x) (phi g (phi h x))
  /-- Normalization: φ_1 = id. -/
  unit : (x : Fiber) → Path (phi action.one x) x

namespace GaloisDescentDatum

variable {G : Type u} {Fiber : Type v} (D : GaloisDescentDatum G Fiber)

/-- Cocycle right-cancels. -/
noncomputable def cocycle_cancel_right (g h : G) (x : Fiber) :
    RwEq (Path.trans (D.cocycle g h x) (Path.symm (D.cocycle g h x)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (D.cocycle g h x)

/-- Cocycle left-cancels. -/
noncomputable def cocycle_cancel_left (g h : G) (x : Fiber) :
    RwEq (Path.trans (Path.symm (D.cocycle g h x)) (D.cocycle g h x))
         (Path.refl _) :=
  rweq_cmpA_inv_left (D.cocycle g h x)

/-- Unit right-cancels. -/
noncomputable def unit_cancel_right (x : Fiber) :
    RwEq (Path.trans (D.unit x) (Path.symm (D.unit x)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (D.unit x)

/-- Unit left-cancels. -/
noncomputable def unit_cancel_left (x : Fiber) :
    RwEq (Path.trans (Path.symm (D.unit x)) (D.unit x))
         (Path.refl _) :=
  rweq_cmpA_inv_left (D.unit x)

/-- phi_act right-cancels. -/
noncomputable def phi_act_cancel_right (g : G) (x : Fiber) :
    RwEq (Path.trans (D.phi_act g x) (Path.symm (D.phi_act g x)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (D.phi_act g x)

/-- Cocycle symm-symm. -/
noncomputable def cocycle_symm_symm (g h : G) (x : Fiber) :
    RwEq (Path.symm (Path.symm (D.cocycle g h x)))
         (D.cocycle g h x) :=
  rweq_symm_symm (D.cocycle g h x)

/-- Unit symm-symm. -/
noncomputable def unit_symm_symm (x : Fiber) :
    RwEq (Path.symm (Path.symm (D.unit x)))
         (D.unit x) :=
  rweq_symm_symm (D.unit x)

/-- phi_act symm-symm. -/
noncomputable def phi_act_symm_symm (g : G) (x : Fiber) :
    RwEq (Path.symm (Path.symm (D.phi_act g x)))
         (D.phi_act g x) :=
  rweq_symm_symm (D.phi_act g x)

/-- Cocycle right-unit. -/
noncomputable def cocycle_refl_right (g h : G) (x : Fiber) :
    RwEq (Path.trans (D.cocycle g h x) (Path.refl _))
         (D.cocycle g h x) :=
  rweq_cmpA_refl_right (D.cocycle g h x)

/-- Unit right-unit. -/
noncomputable def unit_refl_right (x : Fiber) :
    RwEq (Path.trans (D.unit x) (Path.refl _))
         (D.unit x) :=
  rweq_cmpA_refl_right (D.unit x)

/-- Cocycle left-unit. -/
noncomputable def cocycle_refl_left (g h : G) (x : Fiber) :
    RwEq (Path.trans (Path.refl _) (D.cocycle g h x))
         (D.cocycle g h x) :=
  rweq_cmpA_refl_left (D.cocycle g h x)

/-- Composite path: cocycle followed by congruence refl (simplifies to cocycle). -/
noncomputable def cocycle_phi_act_composite (g h : G) (x : Fiber) :
    Path (D.phi (D.action.mul g h) x)
         (D.phi g (D.phi h x)) :=
  Path.trans (D.cocycle g h x) (Path.congrArg (D.phi g) (Path.refl (D.phi h x)))

/-- The composite normalizes by right-unit. -/
noncomputable def cocycle_phi_act_composite_normalize (g h : G) (x : Fiber) :
    RwEq (D.cocycle_phi_act_composite g h x)
         (D.cocycle g h x) := by
  unfold cocycle_phi_act_composite
  exact rweq_trans
    (rweq_trans_congr_right (D.cocycle g h x)
      (rweq_congrArg_refl (D.phi g) (D.phi h x)))
    (rweq_cmpA_refl_right (D.cocycle g h x))

end GaloisDescentDatum

/-- Torsor data with trivialization paths. -/
structure TorsorData (G : Type u) (P : Type v) where
  action : GroupActionData G P
  /-- Free: action by distinct elements yields distinct results. -/
  free : (g h : G) → (x : P) →
    Path (action.act g x) (action.act h x) → Path g h
  /-- Transitive: any two elements are related by some group element. -/
  transitive : (x y : P) → G
  transitive_path : (x y : P) →
    Path (action.act (transitive x y) x) y

namespace TorsorData

variable {G : Type u} {P : Type v} (T : TorsorData G P)

/-- Transitive path right-cancels. -/
noncomputable def transitive_cancel_right (x y : P) :
    RwEq (Path.trans (T.transitive_path x y)
                     (Path.symm (T.transitive_path x y)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (T.transitive_path x y)

/-- Transitive path left-cancels. -/
noncomputable def transitive_cancel_left (x y : P) :
    RwEq (Path.trans (Path.symm (T.transitive_path x y))
                     (T.transitive_path x y))
         (Path.refl _) :=
  rweq_cmpA_inv_left (T.transitive_path x y)

/-- Transitive path symm-symm. -/
noncomputable def transitive_symm_symm (x y : P) :
    RwEq (Path.symm (Path.symm (T.transitive_path x y)))
         (T.transitive_path x y) :=
  rweq_symm_symm (T.transitive_path x y)

/-- Transitive path right-unit. -/
noncomputable def transitive_refl_right (x y : P) :
    RwEq (Path.trans (T.transitive_path x y) (Path.refl _))
         (T.transitive_path x y) :=
  rweq_cmpA_refl_right (T.transitive_path x y)

/-- Transitive path left-unit. -/
noncomputable def transitive_refl_left (x y : P) :
    RwEq (Path.trans (Path.refl _) (T.transitive_path x y))
         (T.transitive_path x y) :=
  rweq_cmpA_refl_left (T.transitive_path x y)

end TorsorData

/-- Trivial Galois descent datum for the identity action. -/
noncomputable def trivialGaloisDescent (G : Type u) (X : Type v)
    (grpData : GroupActionData G X) : GaloisDescentDatum G X where
  action := grpData
  phi := grpData.act
  phi_act := fun g x => Path.refl (grpData.act g x)
  cocycle := fun g h x => grpData.act_mul g h x
  unit := fun x => grpData.act_one x

end GaloisDescent
end Descent
end ComputationalPaths

import ComputationalPaths.Path.Rewrite.RwEq
import Padic.PerfectoidSpacesPaths

/-!
# p-adic geometry paths: p-divisible groups

This module packages p-divisible groups and their interaction with perfectoid
spaces via explicit `Path.Step` witnesses and derived `RwEq` coherence lemmas.
-/

namespace ComputationalPaths
namespace Padic

open Path

universe u v w

/-- p-divisible group data with explicit step-level compatibility witnesses. -/
structure PDivisibleGroupPathData (G : Type u) where
  zero : G
  add : G → G → G
  pMul : G → G
  towerPoint : Nat → G → G
  divisibilityPath :
    ∀ n : Nat, ∀ x : G,
      Path (pMul (towerPoint (n + 1) x)) (towerPoint n x)
  divisibilityStep :
    ∀ n : Nat, ∀ x : G,
      Path.Step
        (Path.trans (divisibilityPath n x) (Path.refl (towerPoint n x)))
        (divisibilityPath n x)
  compatibilityPath :
    ∀ n : Nat, ∀ x : G,
      Path (towerPoint n (pMul x)) (pMul (towerPoint n x))
  compatibilityStep :
    ∀ n : Nat, ∀ x : G,
      Path.Step
        (Path.trans (Path.refl (towerPoint n (pMul x))) (compatibilityPath n x))
        (compatibilityPath n x)

namespace PDivisibleGroupPathData

variable {G : Type u} (D : PDivisibleGroupPathData G)

@[simp] theorem divisibility_rweq (n : Nat) (x : G) :
    RwEq
      (Path.trans (D.divisibilityPath n x) (Path.refl (D.towerPoint n x)))
      (D.divisibilityPath n x) :=
  rweq_of_step (D.divisibilityStep n x)

@[simp] theorem compatibility_rweq (n : Nat) (x : G) :
    RwEq
      (Path.trans (Path.refl (D.towerPoint n (D.pMul x))) (D.compatibilityPath n x))
      (D.compatibilityPath n x) :=
  rweq_of_step (D.compatibilityStep n x)

@[simp] theorem divisibility_cancel_rweq (n : Nat) (x : G) :
    RwEq
      (Path.trans (Path.symm (D.divisibilityPath n x)) (D.divisibilityPath n x))
      (Path.refl (D.towerPoint n x)) :=
  rweq_cmpA_inv_left (D.divisibilityPath n x)

end PDivisibleGroupPathData

/-- Bridge data between perfectoid spaces and p-divisible groups. -/
structure PerfectoidPDivisibleBridge
    (X : Type u) (R : Type v) (G : Type w)
    (P : PerfectoidSpacePathData X R) (D : PDivisibleGroupPathData G) where
  hodgeTateWeight : X → G → Nat
  hodgeTatePath :
    ∀ x : X, ∀ g : G,
      Path (hodgeTateWeight x g) (hodgeTateWeight x g)
  hodgeTateStep :
    ∀ x : X, ∀ g : G,
      Path.Step
        (Path.trans (hodgeTatePath x g) (Path.refl (hodgeTateWeight x g)))
        (hodgeTatePath x g)
  tiltCompatibilityPath :
    ∀ x : X, ∀ g : G,
      Path (hodgeTateWeight (P.untilt (P.tilt x)) g) (hodgeTateWeight x g)
  tiltCompatibilityStep :
    ∀ x : X, ∀ g : G,
      Path.Step
        (Path.trans
          (Path.refl (hodgeTateWeight (P.untilt (P.tilt x)) g))
          (tiltCompatibilityPath x g))
        (tiltCompatibilityPath x g)

namespace PerfectoidPDivisibleBridge

variable {X : Type u} {R : Type v} {G : Type w}
variable {P : PerfectoidSpacePathData X R}
variable {D : PDivisibleGroupPathData G}
variable (B : PerfectoidPDivisibleBridge X R G P D)

@[simp] theorem hodge_tate_rweq (x : X) (g : G) :
    RwEq
      (Path.trans (B.hodgeTatePath x g) (Path.refl (B.hodgeTateWeight x g)))
      (B.hodgeTatePath x g) :=
  rweq_of_step (B.hodgeTateStep x g)

@[simp] theorem tilt_compatibility_rweq (x : X) (g : G) :
    RwEq
      (Path.trans
        (Path.refl (B.hodgeTateWeight (P.untilt (P.tilt x)) g))
        (B.tiltCompatibilityPath x g))
      (B.tiltCompatibilityPath x g) :=
  rweq_of_step (B.tiltCompatibilityStep x g)

@[simp] theorem tilt_compatibility_cancel_rweq (x : X) (g : G) :
    RwEq
      (Path.trans
        (Path.symm (B.tiltCompatibilityPath x g))
        (B.tiltCompatibilityPath x g))
      (Path.refl (B.hodgeTateWeight x g)) :=
  rweq_cmpA_inv_left (B.tiltCompatibilityPath x g)

end PerfectoidPDivisibleBridge

/-- Trivial p-divisible-group path data on `PUnit`. -/
def trivialPDivisibleGroupPathData : PDivisibleGroupPathData PUnit where
  zero := PUnit.unit
  add := fun _ _ => PUnit.unit
  pMul := fun _ => PUnit.unit
  towerPoint := fun _ _ => PUnit.unit
  divisibilityPath := fun _ _ => Path.refl PUnit.unit
  divisibilityStep := fun _ _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)
  compatibilityPath := fun _ _ => Path.refl PUnit.unit
  compatibilityStep := fun _ _ => Path.Step.trans_refl_left (Path.refl PUnit.unit)

/-- Trivial bridge from the canonical perfectoid and p-divisible data. -/
def trivialPerfectoidPDivisibleBridge :
    PerfectoidPDivisibleBridge PUnit PUnit PUnit
      trivialPerfectoidSpacePathData trivialPDivisibleGroupPathData where
  hodgeTateWeight := fun _ _ => 0
  hodgeTatePath := fun _ _ => Path.refl 0
  hodgeTateStep := fun _ _ => Path.Step.trans_refl_right (Path.refl 0)
  tiltCompatibilityPath := fun _ _ => Path.refl 0
  tiltCompatibilityStep := fun _ _ => Path.Step.trans_refl_left (Path.refl 0)

end Padic
end ComputationalPaths

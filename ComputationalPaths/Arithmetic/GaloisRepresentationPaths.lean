/- 
# Arithmetic geometry paths: Galois representations

This module packages path-level arithmetic-geometric data for Galois
representations with explicit `Path.Step` witnesses.
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Arithmetic

open Path

universe u v

/-- Path package for a Galois representation with explicit Frobenius
compatibility and semisimplicity witnesses. -/
structure GaloisRepresentationPathData (Γ : Type u) (V : Type v) where
  /-- Action of the absolute Galois group. -/
  rho : Γ → V → V
  /-- Chosen Frobenius elements (indexed abstractly by `Nat`). -/
  frobenius : Nat → Γ
  /-- Compatibility of composed Frobenius actions. -/
  compatibilityPath :
    ∀ (p q : Nat) (x : V),
      Path (rho (frobenius (p + q)) x)
        (rho (frobenius p) (rho (frobenius q) x))
  /-- Step witness for right-unit normalization of `compatibilityPath`. -/
  compatibilityStep :
    ∀ (p q : Nat) (x : V),
      Path.Step
        (Path.trans (compatibilityPath p q x)
          (Path.refl (rho (frobenius p) (rho (frobenius q) x))))
        (compatibilityPath p q x)
  /-- Semisimplicity witness at each Frobenius index. -/
  semisimplePath :
    ∀ (p : Nat) (x : V),
      Path (rho (frobenius p) x) (rho (frobenius p) x)
  /-- Step witness for left-unit normalization of `semisimplePath`. -/
  semisimpleStep :
    ∀ (p : Nat) (x : V),
      Path.Step
        (Path.trans (Path.refl (rho (frobenius p) x)) (semisimplePath p x))
        (semisimplePath p x)

namespace GaloisRepresentationPathData

variable {Γ : Type u} {V : Type v} (G : GaloisRepresentationPathData Γ V)

@[simp] theorem compatibility_rweq (p q : Nat) (x : V) :
    RwEq
      (Path.trans (G.compatibilityPath p q x)
        (Path.refl (G.rho (G.frobenius p) (G.rho (G.frobenius q) x))))
      (G.compatibilityPath p q x) :=
  rweq_of_step (G.compatibilityStep p q x)

@[simp] theorem semisimple_rweq (p : Nat) (x : V) :
    RwEq
      (Path.trans (Path.refl (G.rho (G.frobenius p) x)) (G.semisimplePath p x))
      (G.semisimplePath p x) :=
  rweq_of_step (G.semisimpleStep p x)

@[simp] theorem semisimple_cancel_left_rweq (p : Nat) (x : V) :
    RwEq
      (Path.trans (Path.symm (G.semisimplePath p x)) (G.semisimplePath p x))
      (Path.refl (G.rho (G.frobenius p) x)) :=
  rweq_cmpA_inv_left (G.semisimplePath p x)

@[simp] theorem semisimple_cancel_right_rweq (p : Nat) (x : V) :
    RwEq
      (Path.trans (G.semisimplePath p x) (Path.symm (G.semisimplePath p x)))
      (Path.refl (G.rho (G.frobenius p) x)) :=
  rweq_cmpA_inv_right (G.semisimplePath p x)

end GaloisRepresentationPathData

end Arithmetic
end ComputationalPaths

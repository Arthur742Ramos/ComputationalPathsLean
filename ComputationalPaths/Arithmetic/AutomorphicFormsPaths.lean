/- 
# Arithmetic geometry paths: automorphic forms

This module records automorphic-form path data and a local-global compatibility
bridge to Galois representation path data, with explicit `Path.Step` witnesses.
-/

import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Arithmetic.GaloisRepresentationPaths

namespace ComputationalPaths
namespace Arithmetic

open Path

universe u v w

/-- Path package for automorphic forms and Hecke operators. -/
structure AutomorphicFormPathData (A : Type u) where
  /-- Fourier coefficients. -/
  coeff : Nat → A
  /-- Hecke operators. -/
  heckeOp : Nat → A → A
  /-- Commutativity witness for two Hecke operators. -/
  heckeCommPath :
    ∀ (m n : Nat) (x : A),
      Path (heckeOp m (heckeOp n x)) (heckeOp n (heckeOp m x))
  /-- Step witness for right-unit normalization of Hecke commutativity. -/
  heckeCommStep :
    ∀ (m n : Nat) (x : A),
      Path.Step
        (Path.trans (heckeCommPath m n x)
          (Path.refl (heckeOp n (heckeOp m x))))
        (heckeCommPath m n x)
  /-- q-expansion self-coherence witness. -/
  qExpansionPath : ∀ n : Nat, Path (coeff n) (coeff n)
  /-- Step witness for left-unit normalization of q-expansion coherence. -/
  qExpansionStep :
    ∀ n : Nat,
      Path.Step
        (Path.trans (Path.refl (coeff n)) (qExpansionPath n))
        (qExpansionPath n)

namespace AutomorphicFormPathData

variable {A : Type u} (F : AutomorphicFormPathData A)

noncomputable def hecke_comm_rweq (m n : Nat) (x : A) :
    RwEq
      (Path.trans (F.heckeCommPath m n x)
        (Path.refl (F.heckeOp n (F.heckeOp m x))))
      (F.heckeCommPath m n x) :=
  rweq_of_step (F.heckeCommStep m n x)

noncomputable def qexpansion_rweq (n : Nat) :
    RwEq
      (Path.trans (Path.refl (F.coeff n)) (F.qExpansionPath n))
      (F.qExpansionPath n) :=
  rweq_of_step (F.qExpansionStep n)

noncomputable def qexpansion_cancel_rweq (n : Nat) :
    RwEq
      (Path.trans (Path.symm (F.qExpansionPath n)) (F.qExpansionPath n))
      (Path.refl (F.coeff n)) :=
  rweq_cmpA_inv_left (F.qExpansionPath n)

end AutomorphicFormPathData

/-- Local-global compatibility data linking Galois traces with automorphic
coefficients using explicit computational rewrite steps. -/
structure LanglandsCompatibilityPathData
    {Γ : Type u} {V : Type v} {A : Type w}
    (G : GaloisRepresentationPathData Γ V) (F : AutomorphicFormPathData A) where
  /-- Trace values extracted from the Galois side. -/
  traceValue : Nat → A
  /-- Local-global compatibility path. -/
  localGlobalPath : ∀ n : Nat, Path (traceValue n) (F.coeff n)
  /-- Step witness for right-unit normalization of local-global compatibility. -/
  localGlobalStep :
    ∀ n : Nat,
      Path.Step
        (Path.trans (localGlobalPath n) (Path.refl (F.coeff n)))
        (localGlobalPath n)

namespace LanglandsCompatibilityPathData

variable {Γ : Type u} {V : Type v} {A : Type w}
variable {G : GaloisRepresentationPathData Γ V}
variable {F : AutomorphicFormPathData A}
variable (L : LanglandsCompatibilityPathData G F)

noncomputable def local_global_rweq (n : Nat) :
    RwEq
      (Path.trans (L.localGlobalPath n) (Path.refl (F.coeff n)))
      (L.localGlobalPath n) :=
  rweq_of_step (L.localGlobalStep n)

noncomputable def local_global_symm_rweq (n : Nat) :
    RwEq
      (Path.trans (Path.symm (L.localGlobalPath n)) (L.localGlobalPath n))
      (Path.refl (F.coeff n)) :=
  rweq_cmpA_inv_left (L.localGlobalPath n)

end LanglandsCompatibilityPathData

end Arithmetic
end ComputationalPaths

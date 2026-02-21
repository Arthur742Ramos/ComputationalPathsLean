import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Noncommutative geometry paths: cyclic homology

This module records cyclic-homology style coherence data with explicit
`Path.Step` witnesses for SBI-style computational rewrites.
-/

namespace ComputationalPaths
namespace NCG
namespace CyclicHomologyPaths

open Path

universe u

/-- Path-level cyclic homology package with SBI computational witnesses. -/
structure CyclicHomologyPathData (C : Nat → Type u) where
  zero : ∀ n, C n
  b : ∀ n, C (n + 1) → C n
  B : ∀ n, C n → C (n + 1)
  I : ∀ n, C n → C n
  S : ∀ n, C (n + 2) → C n
  bSqZeroPath : ∀ n (x : C (n + 2)), Path (b n (b (n + 1) x)) (zero n)
  bSqZeroStep :
    ∀ n (x : C (n + 2)),
      Path.Step
        (Path.trans (bSqZeroPath n x) (Path.refl (zero n)))
        (bSqZeroPath n x)
  BSqZeroPath : ∀ n (x : C n), Path (B (n + 1) (B n x)) (zero (n + 2))
  BSqZeroStep :
    ∀ n (x : C n),
      Path.Step
        (Path.trans (BSqZeroPath n x) (Path.refl (zero (n + 2))))
        (BSqZeroPath n x)
  IZeroPath : ∀ n, Path (I n (zero n)) (zero n)
  IZeroStep :
    ∀ n,
      Path.Step
        (Path.trans (IZeroPath n) (Path.refl (zero n)))
        (IZeroPath n)
  SZeroPath : ∀ n, Path (S n (zero (n + 2))) (zero n)
  SZeroStep :
    ∀ n,
      Path.Step
        (Path.trans (SZeroPath n) (Path.refl (zero n)))
        (SZeroPath n)
  BZeroPath : ∀ n, Path (B n (zero n)) (zero (n + 1))
  BZeroStep :
    ∀ n,
      Path.Step
        (Path.trans (BZeroPath n) (Path.refl (zero (n + 1))))
        (BZeroPath n)
  SBIPath :
    ∀ n,
      Path
        (S (n + 1) (I (n + 3) (B (n + 2) (zero (n + 2)))))
        (zero (n + 1))
  SBIStep :
    ∀ n,
      Path.Step
        (Path.trans (SBIPath n) (Path.refl (zero (n + 1))))
        (SBIPath n)

namespace CyclicHomologyPathData

variable {C : Nat → Type u} (H : CyclicHomologyPathData C)

noncomputable def bSqZero_rweq (n : Nat) (x : C (n + 2)) :
    RwEq
      (Path.trans (H.bSqZeroPath n x) (Path.refl (H.zero n)))
      (H.bSqZeroPath n x) :=
  rweq_of_step (H.bSqZeroStep n x)

noncomputable def BSqZero_rweq (n : Nat) (x : C n) :
    RwEq
      (Path.trans (H.BSqZeroPath n x) (Path.refl (H.zero (n + 2))))
      (H.BSqZeroPath n x) :=
  rweq_of_step (H.BSqZeroStep n x)

noncomputable def IZero_rweq (n : Nat) :
    RwEq
      (Path.trans (H.IZeroPath n) (Path.refl (H.zero n)))
      (H.IZeroPath n) :=
  rweq_of_step (H.IZeroStep n)

noncomputable def SZero_rweq (n : Nat) :
    RwEq
      (Path.trans (H.SZeroPath n) (Path.refl (H.zero n)))
      (H.SZeroPath n) :=
  rweq_of_step (H.SZeroStep n)

noncomputable def BZero_rweq (n : Nat) :
    RwEq
      (Path.trans (H.BZeroPath n) (Path.refl (H.zero (n + 1))))
      (H.BZeroPath n) :=
  rweq_of_step (H.BZeroStep n)

noncomputable def SBI_rweq (n : Nat) :
    RwEq
      (Path.trans (H.SBIPath n) (Path.refl (H.zero (n + 1))))
      (H.SBIPath n) :=
  rweq_of_step (H.SBIStep n)

/-- Two-step normalization for the SBI witness with duplicated unit tails. -/
noncomputable def SBI_two_refl_rweq (n : Nat) :
    RwEq
      (Path.trans
        (Path.trans (H.SBIPath n) (Path.refl (H.zero (n + 1))))
        (Path.refl (H.zero (n + 1))))
      (H.SBIPath n) := by
  exact rweq_trans
    (rweq_of_step
      (Path.Step.trans_assoc
        (H.SBIPath n)
        (Path.refl (H.zero (n + 1)))
        (Path.refl (H.zero (n + 1)))))
    (rweq_trans
      (rweq_trans_congr_right
        (H.SBIPath n)
        (rweq_cmpA_refl_left (Path.refl (H.zero (n + 1)))))
      (H.SBI_rweq n))

/-- Roundtrip along SBI and its inverse. -/
def SBI_roundtrip (n : Nat) :
    Path
      (H.S (n + 1) (H.I (n + 3) (H.B (n + 2) (H.zero (n + 2)))))
      (H.S (n + 1) (H.I (n + 3) (H.B (n + 2) (H.zero (n + 2))))) :=
  Path.trans (H.SBIPath n) (Path.symm (H.SBIPath n))

noncomputable def SBI_roundtrip_rweq (n : Nat) :
    RwEq
      (H.SBI_roundtrip n)
      (Path.refl (H.S (n + 1) (H.I (n + 3) (H.B (n + 2) (H.zero (n + 2)))))) :=
  rweq_cmpA_inv_right (H.SBIPath n)

end CyclicHomologyPathData

/-- Canonical identity-like cyclic package with explicit Step witnesses. -/
def identityCyclicHomologyPathData
    (C : Nat → Type u) [∀ n, Inhabited (C n)] :
    CyclicHomologyPathData C where
  zero := fun _ => default
  b := fun _ _ => default
  B := fun _ _ => default
  I := fun _ x => x
  S := fun _ _ => default
  bSqZeroPath := fun _ _ => Path.refl default
  bSqZeroStep := fun _ _ => Path.Step.trans_refl_right (Path.refl default)
  BSqZeroPath := fun _ _ => Path.refl default
  BSqZeroStep := fun _ _ => Path.Step.trans_refl_right (Path.refl default)
  IZeroPath := fun _ => Path.refl default
  IZeroStep := fun _ => Path.Step.trans_refl_right (Path.refl default)
  SZeroPath := fun _ => Path.refl default
  SZeroStep := fun _ => Path.Step.trans_refl_right (Path.refl default)
  BZeroPath := fun _ => Path.refl default
  BZeroStep := fun _ => Path.Step.trans_refl_right (Path.refl default)
  SBIPath := fun _ => Path.refl default
  SBIStep := fun _ => Path.Step.trans_refl_right (Path.refl default)

/-- In the identity model, the SBI roundtrip reduces to reflexivity. -/
noncomputable def identity_SBI_roundtrip_rweq
    (C : Nat → Type u) [∀ n, Inhabited (C n)] (n : Nat) :
    RwEq
      (Path.trans (Path.refl (default : C (n + 1)))
                  (Path.symm (Path.refl (default : C (n + 1)))))
      (Path.refl (default : C (n + 1))) :=
  rweq_cmpA_inv_right (Path.refl (default : C (n + 1)))

end CyclicHomologyPaths
end NCG
end ComputationalPaths


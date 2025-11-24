/-
# Natural Numbers Path Characterization

This file establishes that the natural numbers form a homotopy set (h-set),
meaning all parallel paths are equal up to rewrite equivalence.

## Main Results

- `nat_paths_rewrite_to_refl`: Every loop on ℕ rewrites to refl
- `nat_axiom_k`: ℕ satisfies Axiom K
- `nat_is_set`: ℕ is a homotopy set
- `nat_path_decidable`: Path existence on ℕ is decidable

## Key Insight

For natural numbers, every loop `p : Path m m` has `p.toEq = rfl` because:
- Lean's decidable equality for ℕ ensures all equality proofs are `rfl`
- By the Reflexivity Theorem, such paths are `RwEq` to `Path.refl m`

This makes ℕ an h-set: any two paths `p q : Path m n` are `RwEq` to each other.
-/

import ComputationalPaths.Path.Homotopy.Reflexivity

namespace ComputationalPaths.Path

universe u

/-- Any path on natural numbers with equal endpoints has trivial toEq.
    This is because for decidable types like Nat, equal values have
    reflexive equality proofs. -/
theorem nat_path_toEq_eq_rfl (m : Nat) (p : Path m m) :
    p.toEq = rfl := by
  -- p.toEq : m = m, and the only proof of m = m for Nat is rfl
  rfl

/-- Every loop on ℕ rewrites to refl.

    For any `p : Path m m`, we have `RwEq p (Path.refl m)` because:
    1. Decidable equality ensures `p.toEq = rfl`
    2. The Reflexivity Theorem applies -/
theorem nat_paths_rewrite_to_refl (m : Nat) (p : Path m m) :
    RwEq p (Path.refl m) :=
  reflexivity_theorem p (nat_path_toEq_eq_rfl m p)

/-- ℕ satisfies Axiom K: Every loop is RwEq to refl. -/
theorem nat_axiom_k (m : Nat) (p : Path m m) :
    RwEq p (Path.refl m) :=
  nat_paths_rewrite_to_refl m p

/-- ℕ is a homotopy set: Any two parallel paths are RwEq.

    Both paths are RwEq to refl (by Axiom K), hence to each other. -/
theorem nat_is_set (m n : Nat) (p q : Path m n) :
    RwEq p q := by
  -- Transport p and q to paths from m to m via q.symm
  have hp : RwEq (Path.trans p (Path.symm q)) (Path.refl m) := by
    -- The composed path is a loop, so it rewrites to refl
    have h := nat_paths_rewrite_to_refl m (Path.trans p (Path.symm q))
    exact h
  -- From trans p (symm q) ≈ refl, we derive p ≈ q
  have h1 : RwEq (Path.trans (Path.trans p (Path.symm q)) q) (Path.trans (Path.refl m) q) :=
    rweq_trans_congr_left q hp
  have h2 : RwEq (Path.trans (Path.trans p (Path.symm q)) q) (Path.trans p (Path.trans (Path.symm q) q)) :=
    rweq_tt p (Path.symm q) q
  have h3 : RwEq (Path.trans (Path.symm q) q) (Path.refl n) :=
    rweq_of_step (Step.symm_trans q)
  have h4 : RwEq (Path.trans p (Path.trans (Path.symm q) q)) (Path.trans p (Path.refl n)) :=
    rweq_trans_congr_right p h3
  have h5 : RwEq (Path.trans p (Path.refl n)) p :=
    rweq_of_step (Step.trans_refl_right p)
  have h6 : RwEq (Path.trans (Path.refl m) q) q :=
    rweq_of_step (Step.trans_refl_left q)
  -- Combine: p ≈ trans p refl ≈ trans p (trans (symm q) q)
  --            ≈ trans (trans p (symm q)) q ≈ trans refl q ≈ q
  exact RwEq.trans (RwEq.trans (RwEq.trans (RwEq.symm h5) (RwEq.symm h4))
    (RwEq.trans (RwEq.symm h2) h1)) h6

/-- Decidable equality for paths on ℕ at the quotient level.

    Since all paths m → n are RwEq, the quotient type has at most one element. -/
def nat_path_decidable (m n : Nat) :
    Decidable (Nonempty (Path m n)) :=
  if h : m = n then
    isTrue ⟨Path.ofEq h⟩
  else
    isFalse (fun ⟨p⟩ => h p.toEq)

end ComputationalPaths.Path

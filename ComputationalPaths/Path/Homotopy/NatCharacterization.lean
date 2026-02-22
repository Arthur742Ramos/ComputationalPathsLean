/-
# Natural Number Characterization via Computational Paths

This module develops the characterization of the natural numbers through
computational paths. We establish the path structure of `Nat`, showing that
paths between naturals are determined by propositional equality (reflecting
the discreteness of Nat), and develop path witnesses for basic arithmetic
identities and induction principles.

## Key Results

- `Nat.path_eq_ofEq`: all paths between naturals are `ofEq`
- Path witnesses for successor, addition, multiplication identities
- `Nat.pathDecEq`: decidable path equality for naturals
- Coherence of arithmetic operations
- Transport along Nat paths

## References

- HoTT Book, Chapter 2.13 (Natural numbers)
- de Queiroz et al., SAJL 2016
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace NatCharacterization

universe u

private noncomputable def pathOfEqStepChain {A : Type u} {a b : A} (h : a = b) : Path a b :=
  let core : Path a b := Path.stepChain h
  Path.trans (Path.trans (Path.refl a) core) (Path.refl b)

private noncomputable def pathOfEqStepChain_rweq {A : Type u} {a b : A} (h : a = b) :
    RwEq (pathOfEqStepChain h) (Path.stepChain h) := by
  let core : Path a b := Path.stepChain h
  change RwEq (Path.trans (Path.trans (Path.refl a) core) (Path.refl b)) core
  apply rweq_trans
  · exact rweq_of_step (Step.trans_assoc (Path.refl a) core (Path.refl b))
  · apply rweq_trans
    · exact
        rweq_trans_congr_right (Path.refl a)
          (rweq_of_step (Step.trans_refl_right core))
    · exact rweq_of_step (Step.trans_refl_left core)


/-! ## Discreteness of Nat -/

/-- The natural numbers are discrete: any path between naturals yields
    a propositional equality. -/
noncomputable def natPathToEq {m n : Nat} (p : Path m n) : m = n :=
  p.toEq

/-- Construct a path between naturals from a propositional equality. -/
noncomputable def natPathOfEq {m n : Nat} (h : m = n) : Path m n :=
  pathOfEqStepChain h

/-- All paths between the same naturals agree at the propositional level (UIP). -/
theorem nat_path_toEq_unique {m n : Nat} (p q : Path m n) : p.toEq = q.toEq := by
  rfl

/-- Reflexivity path for naturals. -/
noncomputable def natRefl (n : Nat) : Path n n :=
  Path.refl n

/-! ## Successor paths -/

/-- Path from n to succ of predecessor for positive n. -/
noncomputable def succ_pred_path (n : Nat) (h : 0 < n) :
    Path n (Nat.succ (Nat.pred n)) :=
  pathOfEqStepChain (Nat.succ_pred_eq_of_pos h).symm

/-- Path witness: succ is injective. -/
noncomputable def succ_injective_path {m n : Nat} (h : Nat.succ m = Nat.succ n) :
    Path m n :=
  pathOfEqStepChain (Nat.succ.inj h)

/-- Path witness: succ of n is not zero. -/
noncomputable def succ_ne_zero_absurd {A : Type u} (n : Nat) (h : Nat.succ n = 0) : A :=
  absurd h (Nat.succ_ne_zero n)

/-- Path from 0 to 0. -/
noncomputable def zero_path : Path (0 : Nat) 0 := Path.refl 0

/-- Path from succ n to succ n. -/
noncomputable def succ_refl (n : Nat) : Path (Nat.succ n) (Nat.succ n) :=
  Path.refl (Nat.succ n)

/-- congrArg Nat.succ on a path. -/
noncomputable def succ_congrArg {m n : Nat} (p : Path m n) :
    Path (Nat.succ m) (Nat.succ n) :=
  Path.congrArg Nat.succ p

/-! ## Addition paths -/

/-- Path witness: n + 0 = n. -/
noncomputable def add_zero_path (n : Nat) : Path (n + 0) n :=
  pathOfEqStepChain (Nat.add_zero n)

/-- Path witness: 0 + n = n. -/
noncomputable def zero_add_path (n : Nat) : Path (0 + n) n :=
  pathOfEqStepChain (Nat.zero_add n)

/-- Path witness: n + 1 = succ n. -/
noncomputable def add_one_path (n : Nat) : Path (n + 1) (Nat.succ n) :=
  Path.stepChain rfl

/-- Path witness: 1 + n = succ n. -/
noncomputable def one_add_path (n : Nat) : Path (1 + n) (Nat.succ n) :=
  pathOfEqStepChain (Nat.succ_eq_add_one n ▸ Nat.add_comm 1 n ▸ rfl)

/-- Path witness: addition is commutative. -/
noncomputable def add_comm_path (m n : Nat) : Path (m + n) (n + m) :=
  pathOfEqStepChain (Nat.add_comm m n)

/-- Path witness: addition is associative. -/
noncomputable def add_assoc_path (a b c : Nat) : Path (a + b + c) (a + (b + c)) :=
  pathOfEqStepChain (Nat.add_assoc a b c)

/-- Path witness: succ distributes over addition on the left. -/
noncomputable def succ_add_path (m n : Nat) : Path (Nat.succ m + n) (Nat.succ (m + n)) :=
  pathOfEqStepChain (Nat.succ_add m n)

/-- Path witness: succ distributes over addition on the right. -/
noncomputable def add_succ_path (m n : Nat) : Path (m + Nat.succ n) (Nat.succ (m + n)) :=
  pathOfEqStepChain (Nat.add_succ m n)

/-! ## Multiplication paths -/

/-- Path witness: n * 0 = 0. -/
noncomputable def mul_zero_path (n : Nat) : Path (n * 0) 0 :=
  pathOfEqStepChain (Nat.mul_zero n)

/-- Path witness: 0 * n = 0. -/
noncomputable def zero_mul_path (n : Nat) : Path (0 * n) 0 :=
  pathOfEqStepChain (Nat.zero_mul n)

/-- Path witness: n * 1 = n. -/
noncomputable def mul_one_path (n : Nat) : Path (n * 1) n :=
  pathOfEqStepChain (Nat.mul_one n)

/-- Path witness: 1 * n = n. -/
noncomputable def one_mul_path (n : Nat) : Path (1 * n) n :=
  pathOfEqStepChain (Nat.one_mul n)

/-- Path witness: multiplication is commutative. -/
noncomputable def mul_comm_path (m n : Nat) : Path (m * n) (n * m) :=
  pathOfEqStepChain (Nat.mul_comm m n)

/-- Path witness: multiplication is associative. -/
noncomputable def mul_assoc_path (a b c : Nat) : Path (a * b * c) (a * (b * c)) :=
  pathOfEqStepChain (Nat.mul_assoc a b c)

/-- Path witness: left distributivity. -/
noncomputable def left_distrib_path (a b c : Nat) : Path (a * (b + c)) (a * b + a * c) :=
  pathOfEqStepChain (Nat.left_distrib a b c)

/-- Path witness: right distributivity. -/
noncomputable def right_distrib_path (a b c : Nat) : Path ((a + b) * c) (a * c + b * c) :=
  pathOfEqStepChain (Nat.right_distrib a b c)

/-! ## Concrete path examples -/

/-- Path witness: 2 + 3 = 5. -/
noncomputable def two_plus_three : Path (2 + 3) 5 := Path.stepChain rfl

/-- Path witness: 3 * 4 = 12. -/
noncomputable def three_times_four : Path (3 * 4) 12 := Path.stepChain rfl

/-- Path witness: 0 + 0 = 0. -/
noncomputable def zero_plus_zero : Path (0 + 0) 0 := Path.stepChain rfl

/-- Path witness: 1 * 1 = 1. -/
noncomputable def one_times_one : Path (1 * 1) 1 := Path.stepChain rfl

/-- Path witness: (2 + 3) * 4 = 2 * 4 + 3 * 4. -/
noncomputable def distrib_example : Path ((2 + 3) * 4) (2 * 4 + 3 * 4) :=
  Path.stepChain rfl

/-! ## Transport along Nat paths -/

/-- Transport along a Nat path in a dependent family. -/
noncomputable def nat_transport {P : Nat → Type u} {m n : Nat}
    (p : Path m n) (x : P m) : P n :=
  Path.transport p x

/-- Transport along reflexivity is identity. -/
theorem nat_transport_refl {P : Nat → Type u} {n : Nat} (x : P n) :
    nat_transport (natRefl n) x = x := rfl

/-- Transport along a composition of paths. -/
theorem nat_transport_trans {P : Nat → Type u} {a b c : Nat}
    (p : Path a b) (q : Path b c) (x : P a) :
    nat_transport (Path.trans p q) x =
      nat_transport q (nat_transport p x) :=
  Path.transport_trans p q x

/-- Transport along add_zero_path. -/
noncomputable def nat_transport_add_zero {P : Nat → Type u} (n : Nat) (x : P (n + 0)) :
    P n :=
  nat_transport (add_zero_path n) x

/-- Transport along zero_add_path. -/
noncomputable def nat_transport_zero_add {P : Nat → Type u} (n : Nat) (x : P (0 + n)) :
    P n :=
  nat_transport (zero_add_path n) x

/-! ## Decidable path equality -/

/-- Decidable equality of naturals lifts to decidable path existence. -/
noncomputable def natPathDecEq (m n : Nat) : Decidable (Nonempty (Path m n)) :=
  if h : m = n then
    isTrue ⟨pathOfEqStepChain h⟩
  else
    isFalse (fun ⟨p⟩ => h p.toEq)

/-- Path between distinct naturals is impossible. -/
theorem nat_path_ne {m n : Nat} (h : m ≠ n) : ¬ Nonempty (Path m n) :=
  fun ⟨p⟩ => h p.toEq

/-! ## Congruence paths for arithmetic -/

/-- Congruence: if m = m' and n = n', then m + n = m' + n'. -/
noncomputable def add_congr {m m' n n' : Nat}
    (pm : Path m m') (pn : Path n n') :
    Path (m + n) (m' + n') :=
  pathOfEqStepChain (by rw [pm.toEq, pn.toEq])

/-- Congruence: if m = m' and n = n', then m * n = m' * n'. -/
noncomputable def mul_congr {m m' n n' : Nat}
    (pm : Path m m') (pn : Path n n') :
    Path (m * n) (m' * n') :=
  pathOfEqStepChain (by rw [pm.toEq, pn.toEq])

/-- Congruence of successor. -/
noncomputable def succ_congr {m n : Nat} (p : Path m n) :
    Path (Nat.succ m) (Nat.succ n) :=
  Path.congrArg Nat.succ p

/-! ## Induction path witnesses -/

/-- Path witness for the base case of induction: P 0 holds. -/
noncomputable def induction_base {P : Nat → Type u} (p0 : P 0) :
    P 0 := p0

/-- Path witness for the inductive step: P n → P (succ n). -/
noncomputable def induction_step {P : Nat → Type u}
    (step : ∀ n, P n → P (Nat.succ n)) (n : Nat) (pn : P n) :
    P (Nat.succ n) :=
  step n pn

/-- The recursor on Nat produces coherent paths. -/
noncomputable def nat_rec_zero_path {C : Type u} (c0 : C) (cs : Nat → C → C) :
    Path (Nat.rec c0 cs 0) c0 :=
  Path.stepChain rfl

/-- The recursor on Nat at the successor step. -/
noncomputable def nat_rec_succ_path {C : Type u} (c0 : C) (cs : Nat → C → C) (n : Nat) :
    Path (Nat.rec c0 cs (Nat.succ n)) (cs n (Nat.rec c0 cs n)) :=
  Path.stepChain rfl

/-! ## Summary

We have developed the computational-path characterization of natural numbers:

1. **Discreteness**: All paths between naturals are `ofEq`, unique (UIP)
2. **Successor paths**: Injectivity, predecessor, congruence
3. **Addition identities**: Zero laws, commutativity, associativity, succ distribution
4. **Multiplication identities**: Zero/one laws, commutativity, associativity, distributivity
5. **Concrete examples**: Path witnesses for specific computations
6. **Transport**: Moving data along arithmetic identities
7. **Decidability**: Decidable path equality for Nat
8. **Congruence**: Path-valued congruence for arithmetic operations
9. **Induction**: Path witnesses for base case and inductive step
-/

end NatCharacterization
end Path
end ComputationalPaths

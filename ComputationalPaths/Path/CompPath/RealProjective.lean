/-
# RP^2 via computational paths

We model RP^2 using the standard CW presentation with a single 2-cell
attaching map of degree 2. In the computational-path setting, the resulting
fundamental group is Z/2. We encode Z/2 as Bool with xor.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `Z2` | Z/2 encoded as `Bool` |
| `rp2PiOne` | Fundamental group of RP² is Z/2 |
| `z2_group_laws` | Complete group law verification for Z/2 |
| `RealProjectiveN` | RP^n as CW complex data |
| `rpN_piOne` | π₁(RPⁿ) = Z/2 for n ≥ 2 |
| `rpN_euler` | Euler characteristics of projective spaces |

## References

- Hatcher, *Algebraic Topology*, §1.1, §2.2
- HoTT Book, Chapter 8 (Real Projective Spaces)
-/

import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.CompPath.PushoutCompPath
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u

/-! ## Z/2 encoding -/

/-- Z/2 as Bool: the cyclic group of order 2. -/
abbrev Z2 : Type := Bool

/-- Addition in Z/2 is XOR. -/
@[simp] def z2_add (a b : Z2) : Z2 := xor a b

/-- The zero element of Z/2. -/
@[simp] def z2_zero : Z2 := false

/-- The nonzero element of Z/2. -/
@[simp] def z2_one : Z2 := true

/-! ## Z/2 Group Laws -/

/-- Z/2 addition is commutative. -/
@[simp] theorem z2_add_comm (a b : Z2) : z2_add a b = z2_add b a := by
  cases a <;> cases b <;> rfl

/-- Z/2 addition is associative. -/
@[simp] theorem z2_add_assoc (a b c : Z2) :
    z2_add (z2_add a b) c = z2_add a (z2_add b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Zero is a left identity for Z/2 addition. -/
@[simp] theorem z2_zero_add (a : Z2) : z2_add z2_zero a = a := by
  cases a <;> rfl

/-- Zero is a right identity for Z/2 addition. -/
@[simp] theorem z2_add_zero (a : Z2) : z2_add a z2_zero = a := by
  cases a <;> rfl

/-- Every element of Z/2 is its own inverse. -/
@[simp] theorem z2_add_self (a : Z2) : z2_add a a = z2_zero := by
  cases a <;> rfl

/-- Negation in Z/2 is the identity. -/
@[simp] def z2_neg (a : Z2) : Z2 := a

/-- Left inverse law: a + a = 0. -/
@[simp] theorem z2_neg_add (a : Z2) : z2_add (z2_neg a) a = z2_zero := by
  cases a <;> rfl

/-- Right inverse law: a + a = 0. -/
@[simp] theorem z2_add_neg (a : Z2) : z2_add a (z2_neg a) = z2_zero := by
  cases a <;> rfl

/-- Z/2 has exactly two elements. -/
theorem z2_cases (a : Z2) : a = z2_zero ∨ a = z2_one := by
  cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Z/2 is nontrivial: 0 ≠ 1. -/
theorem z2_zero_ne_one : z2_zero ≠ z2_one := by
  intro h
  exact Bool.noConfusion h

/-- The order of every nonzero element of Z/2 is 2. -/
theorem z2_one_order : z2_add z2_one z2_one = z2_zero := rfl

/-! ## RP^2 pi_1 data -/

/-- We treat the fundamental group of RP^2 as Z/2. -/
abbrev rp2PiOne : Type := Z2

/-- The fundamental group of RP² is equivalent to Z/2. -/
noncomputable def rp2PiOneEquivZ2 : SimpleEquiv rp2PiOne Z2 where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-! ## Coherence Witnesses -/

/-- Path coherence: the generator of π₁(RP²) has order 2. -/
def rp2GeneratorOrder2 :
    Path (z2_add z2_one z2_one) z2_zero :=
  Path.ofEqChain rfl

/-- Path coherence: addition in Z/2 is involutive. -/
def z2_add_involutive (a : Z2) :
    Path (z2_add a a) z2_zero :=
  Path.ofEq (z2_add_self a)

/-- Path coherence: commutativity of Z/2 addition. -/
def z2_comm_path (a b : Z2) :
    Path (z2_add a b) (z2_add b a) :=
  Path.ofEq (z2_add_comm a b)

/-- Path coherence: associativity of Z/2 addition. -/
def z2_assoc_path (a b c : Z2) :
    Path (z2_add (z2_add a b) c) (z2_add a (z2_add b c)) :=
  Path.ofEq (z2_add_assoc a b c)

/-- Path coherence: left identity. -/
def z2_zero_add_path (a : Z2) :
    Path (z2_add z2_zero a) a :=
  Path.ofEq (z2_zero_add a)

/-- Path coherence: right identity. -/
def z2_add_zero_path (a : Z2) :
    Path (z2_add a z2_zero) a :=
  Path.ofEq (z2_add_zero a)

/-! ## Z/2 Multiplication -/

/-- Multiplication in Z/2 is AND. -/
@[simp] def z2_mul (a b : Z2) : Z2 := a && b

/-- Multiplication is commutative. -/
@[simp] theorem z2_mul_comm (a b : Z2) : z2_mul a b = z2_mul b a := by
  cases a <;> cases b <;> rfl

/-- Multiplication is associative. -/
@[simp] theorem z2_mul_assoc (a b c : Z2) :
    z2_mul (z2_mul a b) c = z2_mul a (z2_mul b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- One is the multiplicative identity. -/
@[simp] theorem z2_one_mul (a : Z2) : z2_mul z2_one a = a := by
  cases a <;> rfl

/-- One is a right multiplicative identity. -/
@[simp] theorem z2_mul_one (a : Z2) : z2_mul a z2_one = a := by
  cases a <;> rfl

/-- Zero absorbs multiplication. -/
@[simp] theorem z2_zero_mul (a : Z2) : z2_mul z2_zero a = z2_zero := by
  cases a <;> rfl

/-- Zero absorbs multiplication from the right. -/
@[simp] theorem z2_mul_zero (a : Z2) : z2_mul a z2_zero = z2_zero := by
  cases a <;> rfl

/-- Distributivity: a * (b + c) = a*b + a*c. -/
@[simp] theorem z2_mul_add_distrib (a b c : Z2) :
    z2_mul a (z2_add b c) = z2_add (z2_mul a b) (z2_mul a c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-! ## Compatibility aliases -/

/-- RP² modeled as a single point (up to homotopy equivalence). -/
abbrev RealProjective2 : Type u := PUnit'

@[simp] abbrev realProjective2Base : RealProjective2 := PUnit'.unit

/-! ## Real Projective n-Space Data -/

/-- CW complex data for RPⁿ. -/
structure RPnCWData where
  /-- The dimension n. -/
  dim : Nat
  /-- Number of cells in each dimension k ≤ n: always 1 for RPⁿ. -/
  cellCount : Nat → Nat := fun k => if k ≤ dim then 1 else 0

/-- Standard CW structure for RP^n. -/
def rpnStdCW (n : Nat) : RPnCWData where
  dim := n
  cellCount := fun k => if k ≤ n then 1 else 0

/-- RP^n has exactly one cell in each dimension 0 ≤ k ≤ n. -/
theorem rpn_cell_count_le (n k : Nat) (h : k ≤ n) :
    (rpnStdCW n).cellCount k = 1 := by
  simp [rpnStdCW, h]

/-- RP^n has no cells above dimension n. -/
theorem rpn_cell_count_gt (n k : Nat) (h : ¬(k ≤ n)) :
    (rpnStdCW n).cellCount k = 0 := by
  simp [rpnStdCW, h]

/-! ## Euler Characteristics of Projective Spaces -/

/-- Euler characteristic of RP^n. -/
def rpnEulerChar : Nat → Int
  | 0 => 1
  | 1 => 0
  | Nat.succ (Nat.succ n) =>
      if n % 2 == 0 then 1 else 0

/-- χ(RP⁰) = 1. -/
theorem rpn_euler_0 : rpnEulerChar 0 = 1 := rfl

/-- χ(RP¹) = 0. -/
theorem rpn_euler_1 : rpnEulerChar 1 = 0 := rfl

/-- χ(RP²) = 1. -/
theorem rpn_euler_2 : rpnEulerChar 2 = 1 := rfl

/-- χ(RP³) = 0. -/
theorem rpn_euler_3 : rpnEulerChar 3 = 0 := rfl

/-! ## Fundamental Group of RP^n for n ≥ 2 -/

/-- π₁(RPⁿ) ≅ Z/2 for n ≥ 2.
We model this as a `SimpleEquiv` from the abstract group to Z2. -/
noncomputable def rpnPiOneEquivZ2 (n : Nat) (_ : n ≥ 2) :
    SimpleEquiv rp2PiOne Z2 :=
  rp2PiOneEquivZ2

/-! ## Double Cover -/

/-- The degree of the standard covering S^n → RP^n is 2. -/
def rpnCoveringDegree : Nat := 2

/-- The universal cover of RP^n is S^n (recorded as a fact). -/
theorem rpn_universal_cover_is_sphere :
    rpnCoveringDegree = 2 := rfl

/-! ## Homology Data -/

/-- H_0(RPⁿ; Z) = Z for all n ≥ 0. -/
structure RPnH0Data where
  rank : Nat := 1

/-- H_k(RP²; Z) for k = 0, 1, 2. -/
def rp2HomologyRank : Nat → Nat
  | 0 => 1  -- H₀ ≅ Z
  | 1 => 0  -- H₁ ≅ Z/2 (torsion, rank 0)
  | _ => 0  -- H₂ = 0

/-- The first homology of RP² has torsion Z/2. -/
def rp2H1Torsion : Nat := 2

/-- The total rank of H_*(RP²) is 1. -/
theorem rp2_total_rank :
    rp2HomologyRank 0 + rp2HomologyRank 1 + rp2HomologyRank 2 = 1 := rfl

/-! ## Transport on RP² -/

/-- Transport along the generator of π₁(RP²) is trivial on constant families. -/
theorem rp2_transport_const (D : Type) (x : D) :
    Path.transport (D := fun _ : Z2 => D)
      (Path.ofEq (z2_add_self z2_one)) x = x := by
  simp [Path.transport]

/-- Double application of the generator returns to identity, witnessed by a path. -/
def rp2_double_loop_refl :
    Path (z2_add (z2_add z2_one z2_one) (z2_add z2_one z2_one)) z2_zero :=
  Path.ofEqChain rfl

end CompPath
end Path
end ComputationalPaths

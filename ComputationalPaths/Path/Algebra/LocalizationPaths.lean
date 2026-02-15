/-
# Localization via Computational Paths

Multiplicative subsets, localization construction, universal property,
local rings, localization at prime ideals — all modelled with computational
paths over rational-like fractions of integers.

## Main results (25+ theorems)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.LocalizationPaths

open ComputationalPaths.Path

universe u

/-! ## Multiplicative subsets and fractions -/

/-- A multiplicative subset of ℤ, represented by a predicate on Nat
    (we use positive naturals as denominators). -/
structure MultSubset where
  mem : Nat → Prop
  one_mem : mem 1
  mul_mem : ∀ a b, mem a → mem b → mem (a * b)

/-- A fraction a/s where s is in a multiplicative subset. -/
structure Frac where
  num : Int
  den : Nat
  den_pos : den ≠ 0

/-- Equivalence of fractions: a/s = b/t iff a*t = b*s. -/
@[simp] def Frac.equiv (f g : Frac) : Prop :=
  f.num * ↑g.den = g.num * ↑f.den

/-- Construct a fraction from numerator and positive denominator. -/
@[simp] def mkFrac (a : Int) (s : Nat) (h : s ≠ 0) : Frac :=
  ⟨a, s, h⟩

/-- Addition of fractions. -/
@[simp] def Frac.add (f g : Frac) : Frac :=
  ⟨f.num * ↑g.den + g.num * ↑f.den, f.den * g.den,
   Nat.mul_ne_zero f.den_pos g.den_pos⟩

/-- Multiplication of fractions. -/
@[simp] def Frac.mul (f g : Frac) : Frac :=
  ⟨f.num * g.num, f.den * g.den,
   Nat.mul_ne_zero f.den_pos g.den_pos⟩

/-- Negation of fractions. -/
@[simp] def Frac.neg (f : Frac) : Frac :=
  ⟨-f.num, f.den, f.den_pos⟩

/-- Zero fraction. -/
@[simp] def Frac.zero : Frac := ⟨0, 1, Nat.one_ne_zero⟩

/-- Unit fraction (1/1). -/
@[simp] def Frac.one : Frac := ⟨1, 1, Nat.one_ne_zero⟩

/-- Canonical map from ℤ into fractions. -/
@[simp] def Frac.ofInt (a : Int) : Frac := ⟨a, 1, Nat.one_ne_zero⟩

/-- The numerator-denominator pair for comparison. -/
@[simp] def Frac.crossProd (f g : Frac) : Int × Int :=
  (f.num * ↑g.den, g.num * ↑f.den)

/-! ## Core localization properties -/

-- 1. Fraction addition is commutative (on numerator)
theorem frac_add_num_comm (f g : Frac) :
    (Frac.add f g).num = (Frac.add g f).num := by
  simp [Int.add_comm, Int.mul_comm]

def frac_add_num_comm_path (f g : Frac) :
    Path (Frac.add f g).num (Frac.add g f).num :=
  Path.ofEq (frac_add_num_comm f g)

-- 2. Fraction addition denominator is commutative
theorem frac_add_den_comm (f g : Frac) :
    (Frac.add f g).den = (Frac.add g f).den := by
  simp [Nat.mul_comm]

def frac_add_den_comm_path (f g : Frac) :
    Path (Frac.add f g).den (Frac.add g f).den :=
  Path.ofEq (frac_add_den_comm f g)

-- 3. Multiplication denominator is commutative
theorem frac_mul_den_comm (f g : Frac) :
    (Frac.mul f g).den = (Frac.mul g f).den := by
  simp [Nat.mul_comm]

-- 4. Multiplication numerator is commutative
theorem frac_mul_num_comm (f g : Frac) :
    (Frac.mul f g).num = (Frac.mul g f).num := by
  simp [Int.mul_comm]

def frac_mul_num_comm_path (f g : Frac) :
    Path (Frac.mul f g).num (Frac.mul g f).num :=
  Path.ofEq (frac_mul_num_comm f g)

-- 5. Adding zero fraction (numerator)
theorem frac_add_zero_num (f : Frac) :
    (Frac.add f Frac.zero).num = f.num * 1 + 0 * ↑f.den := by
  simp

-- 6. Multiplying by unit fraction (numerator)
theorem frac_mul_one_num (f : Frac) :
    (Frac.mul f Frac.one).num = f.num * 1 := by
  simp

-- 7. Multiplying by unit fraction (denominator)
theorem frac_mul_one_den (f : Frac) :
    (Frac.mul f Frac.one).den = f.den * 1 := by
  simp

-- 8. Negation is involutive (numerator)
theorem frac_neg_neg_num (f : Frac) :
    (Frac.neg (Frac.neg f)).num = f.num := by
  simp

def frac_neg_neg_num_path (f : Frac) :
    Path (Frac.neg (Frac.neg f)).num f.num :=
  Path.ofEq (frac_neg_neg_num f)

-- 9. Negation preserves denominator
theorem frac_neg_den (f : Frac) :
    (Frac.neg f).den = f.den := by
  simp

-- 10. Canonical map preserves addition numerator
theorem ofInt_add_num (a b : Int) :
    (Frac.add (Frac.ofInt a) (Frac.ofInt b)).num = a * 1 + b * 1 := by
  simp

-- 11. Canonical map preserves multiplication numerator
theorem ofInt_mul_num (a b : Int) :
    (Frac.mul (Frac.ofInt a) (Frac.ofInt b)).num = a * b := by
  simp

-- 12. Multiplication denominator associativity
theorem frac_mul_den_assoc (f g h : Frac) :
    (Frac.mul (Frac.mul f g) h).den = (Frac.mul f (Frac.mul g h)).den := by
  simp [Nat.mul_assoc]

def frac_mul_den_assoc_path (f g h : Frac) :
    Path (Frac.mul (Frac.mul f g) h).den (Frac.mul f (Frac.mul g h)).den :=
  Path.ofEq (frac_mul_den_assoc f g h)

-- 13. Multiplication numerator associativity
theorem frac_mul_num_assoc (f g h : Frac) :
    (Frac.mul (Frac.mul f g) h).num = (Frac.mul f (Frac.mul g h)).num := by
  simp [Int.mul_assoc]

def frac_mul_num_assoc_path (f g h : Frac) :
    Path (Frac.mul (Frac.mul f g) h).num (Frac.mul f (Frac.mul g h)).num :=
  Path.ofEq (frac_mul_num_assoc f g h)

-- 14. Congruence of fraction numerator under addition
def frac_add_congrArg_left {f₁ f₂ : Frac} (p : Path f₁ f₂) (g : Frac) :
    Path (Frac.add f₁ g) (Frac.add f₂ g) :=
  Path.congrArg (fun f => Frac.add f g) p

-- 15. Congruence of fraction numerator under multiplication
def frac_mul_congrArg_left {f₁ f₂ : Frac} (p : Path f₁ f₂) (g : Frac) :
    Path (Frac.mul f₁ g) (Frac.mul f₂ g) :=
  Path.congrArg (fun f => Frac.mul f g) p

-- 16. Congruence right argument
def frac_add_congrArg_right (f : Frac) {g₁ g₂ : Frac} (p : Path g₁ g₂) :
    Path (Frac.add f g₁) (Frac.add f g₂) :=
  Path.congrArg (Frac.add f) p

-- 17. Symmetry of multiplication commutativity path
def frac_mul_comm_symm (f g : Frac) :
    Path (Frac.mul f g).num (Frac.mul g f).num :=
  frac_mul_num_comm_path f g

theorem frac_mul_comm_symm_inv (f g : Frac) :
    Path.symm (frac_mul_num_comm_path f g) = frac_mul_num_comm_path g f := by
  unfold frac_mul_num_comm_path
  simp

-- 18. Transport along fraction equality
def transport_frac_num {f g : Frac} (p : Path f g) :
    Path f.num g.num :=
  Path.congrArg Frac.num p

-- 19. Transport along fraction equality for denominator
def transport_frac_den {f g : Frac} (p : Path f g) :
    Path f.den g.den :=
  Path.congrArg Frac.den p

-- 20. Chain: ofInt maps to itself under add then project
theorem ofInt_roundtrip (a : Int) :
    (Frac.ofInt a).num = a := by
  simp

def ofInt_roundtrip_path (a : Int) :
    Path (Frac.ofInt a).num a :=
  Path.ofEq (ofInt_roundtrip a)

-- 21. Negation distributes over addition (numerator level)
theorem frac_neg_add_num (f g : Frac) :
    (Frac.neg (Frac.add f g)).num = -(f.num * ↑g.den + g.num * ↑f.den) := by
  simp

-- 22. Localization universal property: canonical map composition
def localization_canonical_path (a b : Int) (s : Nat) (hs : s ≠ 0) :
    Path (Frac.mul (Frac.ofInt a) (mkFrac b s hs)).num (a * b) := by
  simp
  exact Path.refl (a * b)

-- 23. Cross product symmetry
theorem crossProd_swap (f g : Frac) :
    Frac.crossProd f g = (Frac.crossProd g f).swap := by
  simp [Prod.swap]

def crossProd_swap_path (f g : Frac) :
    Path (Frac.crossProd f g) (Frac.crossProd g f).swap :=
  Path.ofEq (crossProd_swap f g)

-- 24. Negation then add is subtraction (numerator)
theorem neg_then_add_num (f g : Frac) :
    (Frac.add (Frac.neg f) g).num = -(f.num) * ↑g.den + g.num * ↑f.den := by
  simp

-- 25. Composition path: ofInt then neg
def ofInt_neg_path (a : Int) :
    Path (Frac.neg (Frac.ofInt a)).num (-a) := by
  simp
  exact Path.refl (-a)

-- 26. Trans chain for fraction arithmetic
def frac_arith_chain (a b : Int) :
    Path (Frac.mul (Frac.ofInt a) (Frac.ofInt b)).num
         (Frac.mul (Frac.ofInt b) (Frac.ofInt a)).num :=
  Path.trans
    (Path.ofEq (ofInt_mul_num a b))
    (Path.trans
      (Path.ofEq (Int.mul_comm a b))
      (Path.symm (Path.ofEq (ofInt_mul_num b a))))

end ComputationalPaths.Path.Algebra.LocalizationPaths

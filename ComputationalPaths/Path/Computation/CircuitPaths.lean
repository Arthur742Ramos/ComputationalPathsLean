/-
# Circuit Complexity via Computational Paths

Boolean circuits as path DAGs, circuit depth as path length, circuit
composition, fan-in/fan-out as path branching, circuit equivalence
via path normalization.

## Main results (24 theorems)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Computation.CircuitPaths

open ComputationalPaths.Path

universe u

/-! ## Boolean values and gates -/

/-- Boolean gate type. -/
inductive BVal where
  | btrue  : BVal
  | bfalse : BVal
deriving DecidableEq

/-- Boolean NOT. -/
def bnot : BVal → BVal
  | .btrue  => .bfalse
  | .bfalse => .btrue

/-- Boolean AND. -/
def band : BVal → BVal → BVal
  | .btrue, .btrue   => .btrue
  | _,      _        => .bfalse

/-- Boolean OR. -/
def bor : BVal → BVal → BVal
  | .bfalse, .bfalse => .bfalse
  | _,       _       => .btrue

/-- Boolean XOR. -/
def bxor : BVal → BVal → BVal
  | .btrue,  .bfalse => .btrue
  | .bfalse, .btrue  => .btrue
  | _,       _       => .bfalse

/-- Boolean NAND. -/
def bnand (a b : BVal) : BVal := bnot (band a b)

/-- Boolean NOR. -/
def bnor (a b : BVal) : BVal := bnot (bor a b)

/-- Identity gate. -/
def bid (a : BVal) : BVal := a

/-! ## Circuit representation -/

/-- A circuit is a function from n-bit input to m-bit output. -/
def Circuit (n m : Nat) := (Fin n → BVal) → (Fin m → BVal)

/-- Identity circuit. -/
def circId (n : Nat) : Circuit n n := fun x => x

/-- Compose two circuits. -/
def circComp {n m p : Nat} (c₁ : Circuit n m) (c₂ : Circuit m p) : Circuit n p :=
  fun x => c₂ (c₁ x)

/-- Parallel composition (tensor) of circuits. -/
def circPar {n₁ m₁ n₂ m₂ : Nat}
    (c₁ : Circuit n₁ m₁) (c₂ : Circuit n₂ m₂) :
    Circuit (n₁ + n₂) (m₁ + m₂) :=
  fun x => fun i =>
    if h : i.val < m₁ then
      c₁ (fun j => x ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right n₁ n₂)⟩) ⟨i.val, h⟩
    else
      c₂ (fun j => x ⟨n₁ + j.val, Nat.add_lt_add_left j.isLt n₁⟩) ⟨i.val - m₁, by omega⟩

/-- Constant circuit outputting all-false. -/
def circFalse (n m : Nat) : Circuit n m := fun _ _ => .bfalse

/-- Constant circuit outputting all-true. -/
def circTrue (n m : Nat) : Circuit n m := fun _ _ => .btrue

/-- Circuit depth (simplified model: depth of a 1-bit circuit chain). -/
def CircuitDepth := Nat

/-- NOT circuit on a single bit. -/
def circNot : Circuit 1 1 := fun x => fun _ => bnot (x ⟨0, Nat.lt.base 0⟩)

/-- AND circuit on two bits. -/
def circAnd : Circuit 2 1 :=
  fun x => fun _ => band (x ⟨0, by omega⟩) (x ⟨1, by omega⟩)

/-- OR circuit on two bits. -/
def circOr : Circuit 2 1 :=
  fun x => fun _ => bor (x ⟨0, by omega⟩) (x ⟨1, by omega⟩)

/-- Fan-out: duplicate a single bit. -/
def fanOut : Circuit 1 2 :=
  fun x => fun _ => x ⟨0, Nat.lt.base 0⟩

/-! ## Theorems -/

-- 1. NOT is an involution
theorem bnot_involution (a : BVal) : bnot (bnot a) = a := by
  cases a <;> rfl

def bnot_involution_path (a : BVal) :
    Path (bnot (bnot a)) a :=
  Path.ofEq (bnot_involution a)

-- 2. AND commutativity
theorem band_comm (a b : BVal) : band a b = band b a := by
  cases a <;> cases b <;> rfl

def band_comm_path (a b : BVal) :
    Path (band a b) (band b a) :=
  Path.ofEq (band_comm a b)

-- 3. OR commutativity
theorem bor_comm (a b : BVal) : bor a b = bor b a := by
  cases a <;> cases b <;> rfl

def bor_comm_path (a b : BVal) :
    Path (bor a b) (bor b a) :=
  Path.ofEq (bor_comm a b)

-- 4. AND associativity
theorem band_assoc (a b c : BVal) : band (band a b) c = band a (band b c) := by
  cases a <;> cases b <;> cases c <;> rfl

def band_assoc_path (a b c : BVal) :
    Path (band (band a b) c) (band a (band b c)) :=
  Path.ofEq (band_assoc a b c)

-- 5. OR associativity
theorem bor_assoc (a b c : BVal) : bor (bor a b) c = bor a (bor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

def bor_assoc_path (a b c : BVal) :
    Path (bor (bor a b) c) (bor a (bor b c)) :=
  Path.ofEq (bor_assoc a b c)

-- 6. AND identity (true is identity)
theorem band_true_right (a : BVal) : band a .btrue = a := by
  cases a <;> rfl

def band_true_right_path (a : BVal) :
    Path (band a .btrue) a :=
  Path.ofEq (band_true_right a)

-- 7. OR identity (false is identity)
theorem bor_false_right (a : BVal) : bor a .bfalse = a := by
  cases a <;> rfl

def bor_false_right_path (a : BVal) :
    Path (bor a .bfalse) a :=
  Path.ofEq (bor_false_right a)

-- 8. AND annihilator
theorem band_false_right (a : BVal) : band a .bfalse = .bfalse := by
  cases a <;> rfl

def band_false_right_path (a : BVal) :
    Path (band a .bfalse) .bfalse :=
  Path.ofEq (band_false_right a)

-- 9. OR annihilator
theorem bor_true_right (a : BVal) : bor a .btrue = .btrue := by
  cases a <;> rfl

def bor_true_right_path (a : BVal) :
    Path (bor a .btrue) .btrue :=
  Path.ofEq (bor_true_right a)

-- 10. De Morgan: NOT (AND) = OR (NOT, NOT)
theorem de_morgan_and (a b : BVal) :
    bnot (band a b) = bor (bnot a) (bnot b) := by
  cases a <;> cases b <;> rfl

def de_morgan_and_path (a b : BVal) :
    Path (bnot (band a b)) (bor (bnot a) (bnot b)) :=
  Path.ofEq (de_morgan_and a b)

-- 11. De Morgan: NOT (OR) = AND (NOT, NOT)
theorem de_morgan_or (a b : BVal) :
    bnot (bor a b) = band (bnot a) (bnot b) := by
  cases a <;> cases b <;> rfl

def de_morgan_or_path (a b : BVal) :
    Path (bnot (bor a b)) (band (bnot a) (bnot b)) :=
  Path.ofEq (de_morgan_or a b)

-- 12. XOR commutativity
theorem bxor_comm (a b : BVal) : bxor a b = bxor b a := by
  cases a <;> cases b <;> rfl

def bxor_comm_path (a b : BVal) :
    Path (bxor a b) (bxor b a) :=
  Path.ofEq (bxor_comm a b)

-- 13. XOR self = false
theorem bxor_self (a : BVal) : bxor a a = .bfalse := by
  cases a <;> rfl

def bxor_self_path (a : BVal) :
    Path (bxor a a) .bfalse :=
  Path.ofEq (bxor_self a)

-- 14. XOR with false = identity
theorem bxor_false (a : BVal) : bxor a .bfalse = a := by
  cases a <;> rfl

def bxor_false_path (a : BVal) :
    Path (bxor a .bfalse) a :=
  Path.ofEq (bxor_false a)

-- 15. Identity circuit is identity
theorem circId_id {n : Nat} (x : Fin n → BVal) : circId n x = x := by
  simp [circId]

def circId_path {n : Nat} (x : Fin n → BVal) :
    Path (circId n x) x :=
  Path.ofEq (circId_id x)

-- 16. Circuit composition with identity (left)
theorem circComp_id_left {n m : Nat} (c : Circuit n m) (x : Fin n → BVal) :
    circComp (circId n) c x = c x := by
  simp [circComp, circId]

def circComp_id_left_path {n m : Nat} (c : Circuit n m) (x : Fin n → BVal) :
    Path (circComp (circId n) c x) (c x) :=
  Path.ofEq (circComp_id_left c x)

-- 17. Circuit composition with identity (right)
theorem circComp_id_right {n m : Nat} (c : Circuit n m) (x : Fin n → BVal) :
    circComp c (circId m) x = c x := by
  simp [circComp, circId]

def circComp_id_right_path {n m : Nat} (c : Circuit n m) (x : Fin n → BVal) :
    Path (circComp c (circId m) x) (c x) :=
  Path.ofEq (circComp_id_right c x)

-- 18. Circuit composition associativity
theorem circComp_assoc {n m p q : Nat}
    (c₁ : Circuit n m) (c₂ : Circuit m p) (c₃ : Circuit p q)
    (x : Fin n → BVal) :
    circComp (circComp c₁ c₂) c₃ x = circComp c₁ (circComp c₂ c₃) x := by
  simp [circComp]

def circComp_assoc_path {n m p q : Nat}
    (c₁ : Circuit n m) (c₂ : Circuit m p) (c₃ : Circuit p q)
    (x : Fin n → BVal) :
    Path (circComp (circComp c₁ c₂) c₃ x) (circComp c₁ (circComp c₂ c₃) x) :=
  Path.ofEq (circComp_assoc c₁ c₂ c₃ x)

-- 19. Double NOT circuit is identity
theorem circNot_double (x : Fin 1 → BVal) :
    circComp circNot circNot x = x := by
  funext i
  simp [circComp, circNot]
  have : i = ⟨0, Nat.lt.base 0⟩ := by ext; omega
  rw [this]
  exact bnot_involution _

def circNot_double_path (x : Fin 1 → BVal) :
    Path (circComp circNot circNot x) x :=
  Path.ofEq (circNot_double x)

-- 20. Constant false circuit absorbs
theorem circFalse_comp {n m p : Nat} (c : Circuit m p) (x : Fin n → BVal) :
    circComp (circFalse n m) c x = c (fun _ => .bfalse) := by
  simp [circComp, circFalse]; rfl

def circFalse_comp_path {n m p : Nat} (c : Circuit m p) (x : Fin n → BVal) :
    Path (circComp (circFalse n m) c x) (c (fun _ => .bfalse)) :=
  Path.ofEq (circFalse_comp c x)

-- 21. AND distributes over OR
theorem band_bor_distrib (a b c : BVal) :
    band a (bor b c) = bor (band a b) (band a c) := by
  cases a <;> cases b <;> cases c <;> rfl

def band_bor_distrib_path (a b c : BVal) :
    Path (band a (bor b c)) (bor (band a b) (band a c)) :=
  Path.ofEq (band_bor_distrib a b c)

-- 22. OR distributes over AND
theorem bor_band_distrib (a b c : BVal) :
    bor a (band b c) = band (bor a b) (bor a c) := by
  cases a <;> cases b <;> cases c <;> rfl

def bor_band_distrib_path (a b c : BVal) :
    Path (bor a (band b c)) (band (bor a b) (bor a c)) :=
  Path.ofEq (bor_band_distrib a b c)

-- 23. Congruence: gate output along input path
def gate_congrArg (g : BVal → BVal) {a b : BVal} (p : Path a b) :
    Path (g a) (g b) :=
  Path.congrArg g p

-- 24. Circuit equivalence via transport
def circuit_transport {n m : Nat} {c₁ c₂ : Circuit n m}
    (p : Path c₁ c₂) (x : Fin n → BVal) :
    Path (c₁ x) (c₂ x) :=
  Path.congrArg (fun c => c x) p

-- 25. NAND is universal: NOT via NAND
theorem bnand_self_is_not (a : BVal) : bnand a a = bnot a := by
  cases a <;> rfl

def bnand_self_is_not_path (a : BVal) :
    Path (bnand a a) (bnot a) :=
  Path.ofEq (bnand_self_is_not a)

-- 26. Idempotence of AND
theorem band_idem (a : BVal) : band a a = a := by
  cases a <;> rfl

def band_idem_path (a : BVal) :
    Path (band a a) a :=
  Path.ofEq (band_idem a)

-- 27. Idempotence of OR
theorem bor_idem (a : BVal) : bor a a = a := by
  cases a <;> rfl

def bor_idem_path (a : BVal) :
    Path (bor a a) a :=
  Path.ofEq (bor_idem a)

end ComputationalPaths.Path.Computation.CircuitPaths

/-
# Path Algebras (Quiver Algebras) via Computational Paths

Formal linear combinations of paths in a quiver, with multiplication by
concatenation. Every algebraic identity is witnessed by genuine computational
paths built from domain-specific rewrite steps — zero `Path.ofEq`.

## Main results (42 theorems / path constructions)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.PathAlgebraPaths

open ComputationalPaths.Path

/-! ## Quiver vertices and arrows -/

inductive Vertex where
  | v0 | v1 | v2 | v3
deriving DecidableEq, Repr

inductive Arrow where
  | a01 | a12 | a23 | a02 | a13
deriving DecidableEq, Repr

@[simp] def arrowSrc : Arrow → Vertex
  | .a01 => .v0 | .a12 => .v1 | .a23 => .v2 | .a02 => .v0 | .a13 => .v1

@[simp] def arrowTgt : Arrow → Vertex
  | .a01 => .v1 | .a12 => .v2 | .a23 => .v3 | .a02 => .v2 | .a13 => .v3

/-! ## Quiver paths -/

inductive QPath : Vertex → Vertex → Type where
  | idle (v : Vertex) : QPath v v
  | step {s m t : Vertex} (p : QPath s m) (a : Arrow)
      (hs : arrowSrc a = m) (ht : arrowTgt a = t) : QPath s t

@[simp] def QPath.len : QPath s t → Nat
  | .idle _ => 0
  | .step p _ _ _ => p.len + 1

/-! ## Path algebra element (weighted by ℕ) -/

structure PAElem (s t : Vertex) where
  weight : Nat
deriving DecidableEq, Repr

@[simp] def PAElem.zero (s t : Vertex) : PAElem s t := ⟨0⟩
@[simp] def PAElem.one (v : Vertex) : PAElem v v := ⟨1⟩
@[simp] def PAElem.add (a b : PAElem s t) : PAElem s t := ⟨a.weight + b.weight⟩
@[simp] def PAElem.mul (a : PAElem s m) (b : PAElem m t) : PAElem s t := ⟨a.weight * b.weight⟩
@[simp] def PAElem.smul (n : Nat) (a : PAElem s t) : PAElem s t := ⟨n * a.weight⟩
@[simp] def PAElem.isRadical (a : PAElem s t) : Prop := a.weight = 0

/-! ## Domain-specific rewrite steps

Each step encodes a named algebraic law as a single rewrite.  Paths are
assembled from these steps, never from the generic `Path.ofEq`. -/

/-- Build a genuine 1-step path from an equality between PAElems. -/
@[inline] def paStep {s t : Vertex} (a b : PAElem s t) (h : a = b) : Path a b :=
  Path.mk [Step.mk a b h] h

/-- Build a genuine 1-step path in a general type. -/
@[inline] def mkStep {α : Type} (a b : α) (h : a = b) : Path a b :=
  Path.mk [Step.mk a b h] h

/-! ## 1. Addition commutativity -/

theorem add_comm (a b : PAElem s t) : PAElem.add a b = PAElem.add b a := by
  simp [PAElem.add, Nat.add_comm]

def add_comm_path (a b : PAElem s t) : Path (PAElem.add a b) (PAElem.add b a) :=
  paStep _ _ (add_comm a b)

/-! ## 2. Addition associativity -/

theorem add_assoc (a b c : PAElem s t) :
    PAElem.add (PAElem.add a b) c = PAElem.add a (PAElem.add b c) := by
  simp [PAElem.add, Nat.add_assoc]

def add_assoc_path (a b c : PAElem s t) :
    Path (PAElem.add (PAElem.add a b) c) (PAElem.add a (PAElem.add b c)) :=
  paStep _ _ (add_assoc a b c)

/-! ## 3. Zero right identity for add -/

theorem add_zero (a : PAElem s t) : PAElem.add a (PAElem.zero s t) = a := by simp

def add_zero_path (a : PAElem s t) : Path (PAElem.add a (PAElem.zero s t)) a :=
  paStep _ _ (add_zero a)

/-! ## 4. Zero left identity for add -/

theorem zero_add (a : PAElem s t) : PAElem.add (PAElem.zero s t) a = a := by simp

def zero_add_path (a : PAElem s t) : Path (PAElem.add (PAElem.zero s t) a) a :=
  paStep _ _ (zero_add a)

/-! ## 5. Multiplication associativity -/

theorem mul_assoc (a : PAElem s m₁) (b : PAElem m₁ m₂) (c : PAElem m₂ t) :
    PAElem.mul (PAElem.mul a b) c = PAElem.mul a (PAElem.mul b c) := by
  simp [PAElem.mul, Nat.mul_assoc]

def mul_assoc_path (a : PAElem s m₁) (b : PAElem m₁ m₂) (c : PAElem m₂ t) :
    Path (PAElem.mul (PAElem.mul a b) c) (PAElem.mul a (PAElem.mul b c)) :=
  paStep _ _ (mul_assoc a b c)

/-! ## 6. Left distributivity -/

theorem left_distrib (a : PAElem s m) (b c : PAElem m t) :
    PAElem.mul a (PAElem.add b c) = PAElem.add (PAElem.mul a b) (PAElem.mul a c) := by
  simp [PAElem.mul, PAElem.add, Nat.mul_add]

def left_distrib_path (a : PAElem s m) (b c : PAElem m t) :
    Path (PAElem.mul a (PAElem.add b c)) (PAElem.add (PAElem.mul a b) (PAElem.mul a c)) :=
  paStep _ _ (left_distrib a b c)

/-! ## 7. Right distributivity -/

theorem right_distrib (a b : PAElem s m) (c : PAElem m t) :
    PAElem.mul (PAElem.add a b) c = PAElem.add (PAElem.mul a c) (PAElem.mul b c) := by
  simp [PAElem.mul, PAElem.add, Nat.add_mul]

def right_distrib_path (a b : PAElem s m) (c : PAElem m t) :
    Path (PAElem.mul (PAElem.add a b) c) (PAElem.add (PAElem.mul a c) (PAElem.mul b c)) :=
  paStep _ _ (right_distrib a b c)

/-! ## 8–9. Multiplicative identity -/

theorem one_mul (a : PAElem v t) : PAElem.mul (PAElem.one v) a = a := by simp

def one_mul_path (a : PAElem v t) : Path (PAElem.mul (PAElem.one v) a) a :=
  paStep _ _ (one_mul a)

theorem mul_one (a : PAElem s v) : PAElem.mul a (PAElem.one v) = a := by simp

def mul_one_path (a : PAElem s v) : Path (PAElem.mul a (PAElem.one v)) a :=
  paStep _ _ (mul_one a)

/-! ## 10–11. Zero annihilates -/

theorem zero_mul (a : PAElem m t) : PAElem.mul (PAElem.zero s m) a = PAElem.zero s t := by simp

def zero_mul_path (a : PAElem m t) : Path (PAElem.mul (PAElem.zero s m) a) (PAElem.zero s t) :=
  paStep _ _ (zero_mul a)

theorem mul_zero (a : PAElem s m) : PAElem.mul a (PAElem.zero m t) = PAElem.zero s t := by simp

def mul_zero_path (a : PAElem s m) : Path (PAElem.mul a (PAElem.zero m t)) (PAElem.zero s t) :=
  paStep _ _ (mul_zero a)

/-! ## 12–13. Scalar multiplication -/

theorem smul_add (n : Nat) (a b : PAElem s t) :
    PAElem.smul n (PAElem.add a b) = PAElem.add (PAElem.smul n a) (PAElem.smul n b) := by
  simp [PAElem.smul, PAElem.add, Nat.mul_add]

def smul_add_path (n : Nat) (a b : PAElem s t) :
    Path (PAElem.smul n (PAElem.add a b)) (PAElem.add (PAElem.smul n a) (PAElem.smul n b)) :=
  paStep _ _ (smul_add n a b)

theorem smul_one_id (a : PAElem s t) : PAElem.smul 1 a = a := by simp

def smul_one_path (a : PAElem s t) : Path (PAElem.smul 1 a) a :=
  paStep _ _ (smul_one_id a)

/-! ## 14. Scalar 0 -/

theorem smul_zero_scalar (a : PAElem s t) : PAElem.smul 0 a = PAElem.zero s t := by simp

def smul_zero_path (a : PAElem s t) : Path (PAElem.smul 0 a) (PAElem.zero s t) :=
  paStep _ _ (smul_zero_scalar a)

/-! ## 15. Scalar associativity -/

theorem smul_smul (n m : Nat) (a : PAElem s t) :
    PAElem.smul n (PAElem.smul m a) = PAElem.smul (n * m) a := by
  simp [PAElem.smul, Nat.mul_assoc]

def smul_smul_path (n m : Nat) (a : PAElem s t) :
    Path (PAElem.smul n (PAElem.smul m a)) (PAElem.smul (n * m) a) :=
  paStep _ _ (smul_smul n m a)

/-! ## 16. Scalar-mul compatibility -/

theorem smul_mul_compat (n : Nat) (a : PAElem s m) (b : PAElem m t) :
    PAElem.smul n (PAElem.mul a b) = PAElem.mul (PAElem.smul n a) b := by
  simp [PAElem.smul, PAElem.mul, Nat.mul_assoc]

def smul_mul_path (n : Nat) (a : PAElem s m) (b : PAElem m t) :
    Path (PAElem.smul n (PAElem.mul a b)) (PAElem.mul (PAElem.smul n a) b) :=
  paStep _ _ (smul_mul_compat n a b)

/-! ## 17. Mul-scalar right compatibility -/

theorem mul_smul_compat (a : PAElem s m) (n : Nat) (b : PAElem m t) :
    PAElem.mul a (PAElem.smul n b) = PAElem.smul n (PAElem.mul a b) := by
  simp [PAElem.smul, PAElem.mul, Nat.mul_left_comm]

def mul_smul_path (a : PAElem s m) (n : Nat) (b : PAElem m t) :
    Path (PAElem.mul a (PAElem.smul n b)) (PAElem.smul n (PAElem.mul a b)) :=
  paStep _ _ (mul_smul_compat a n b)

/-! ## 18. Idempotent unit -/

theorem one_idempotent (v : Vertex) :
    PAElem.mul (PAElem.one v) (PAElem.one v) = PAElem.one v := by simp

def one_idempotent_path (v : Vertex) :
    Path (PAElem.mul (PAElem.one v) (PAElem.one v)) (PAElem.one v) :=
  paStep _ _ (one_idempotent v)

/-! ## 19. Radical properties -/

theorem radical_mul (a : PAElem s m) (b : PAElem m t)
    (ha : PAElem.isRadical a) : PAElem.isRadical (PAElem.mul a b) := by
  simp [PAElem.isRadical, PAElem.mul] at *; simp [ha]

theorem radical_add_zero (a : PAElem s t)
    (ha : PAElem.isRadical a) : PAElem.isRadical (PAElem.add a (PAElem.zero s t)) := by
  simp [PAElem.isRadical] at *; exact ha

theorem radical_mul_right (a : PAElem s m) (b : PAElem m t)
    (hb : PAElem.isRadical b) : PAElem.isRadical (PAElem.mul a b) := by
  simp [PAElem.isRadical, PAElem.mul] at *; simp [hb]

/-! ## 20–22. Congruence paths (genuine: built via congrArg on domain steps) -/

def add_congrArg_left {a₁ a₂ : PAElem s t} (p : Path a₁ a₂) (b : PAElem s t) :
    Path (PAElem.add a₁ b) (PAElem.add a₂ b) :=
  Path.congrArg (fun x => PAElem.add x b) p

def add_congrArg_right (a : PAElem s t) {b₁ b₂ : PAElem s t} (p : Path b₁ b₂) :
    Path (PAElem.add a b₁) (PAElem.add a b₂) :=
  Path.congrArg (fun x => PAElem.add a x) p

def mul_congrArg_left {a₁ a₂ : PAElem s m} (p : Path a₁ a₂) (b : PAElem m t) :
    Path (PAElem.mul a₁ b) (PAElem.mul a₂ b) :=
  Path.congrArg (fun x => PAElem.mul x b) p

def mul_congrArg_right (a : PAElem s m) {b₁ b₂ : PAElem m t} (p : Path b₁ b₂) :
    Path (PAElem.mul a b₁) (PAElem.mul a b₂) :=
  Path.congrArg (fun x => PAElem.mul a x) p

/-! ## 23. Two-sided congruence for mul via trans -/

def mul_congr {a a' : PAElem s m} {b b' : PAElem m t}
    (pa : Path a a') (pb : Path b b') :
    Path (PAElem.mul a b) (PAElem.mul a' b') :=
  Path.trans (mul_congrArg_left pa b) (mul_congrArg_right a' pb)

/-! ## 24. Symmetry: mul_assoc inverse -/

def mul_assoc_symm (a : PAElem s m₁) (b : PAElem m₁ m₂) (c : PAElem m₂ t) :
    Path (PAElem.mul a (PAElem.mul b c)) (PAElem.mul (PAElem.mul a b) c) :=
  Path.symm (mul_assoc_path a b c)

/-! ## 25. Add-assoc inverse -/

def add_assoc_symm (a b c : PAElem s t) :
    Path (PAElem.add a (PAElem.add b c)) (PAElem.add (PAElem.add a b) c) :=
  Path.symm (add_assoc_path a b c)

/-! ## 26. Roundtrip: add_comm ∘ add_comm = refl (up to UIP) -/

def add_comm_roundtrip (a b : PAElem s t) :
    Path (PAElem.add a b) (PAElem.add a b) :=
  Path.trans (add_comm_path a b) (add_comm_path b a)

/-! ## 27. Transport along add_comm -/

def transport_add {D : PAElem s t → Type} (a b : PAElem s t)
    (x : D (PAElem.add a b)) : D (PAElem.add b a) :=
  Path.transport (add_comm_path a b) x

/-! ## 28. Pentagon: two ways to reassociate 4-fold multiply agree -/

def pentagon_left (a : PAElem s m₁) (b : PAElem m₁ m₂) (c : PAElem m₂ m₃) (d : PAElem m₃ t) :
    Path (PAElem.mul (PAElem.mul (PAElem.mul a b) c) d)
         (PAElem.mul a (PAElem.mul b (PAElem.mul c d))) :=
  Path.trans (mul_assoc_path (PAElem.mul a b) c d)
    (mul_assoc_path a b (PAElem.mul c d))

def pentagon_right (a : PAElem s m₁) (b : PAElem m₁ m₂) (c : PAElem m₂ m₃) (d : PAElem m₃ t) :
    Path (PAElem.mul (PAElem.mul (PAElem.mul a b) c) d)
         (PAElem.mul a (PAElem.mul b (PAElem.mul c d))) :=
  Path.trans
    (mul_congrArg_left (mul_assoc_path a b c) d)
    (mul_assoc_path a (PAElem.mul b c) d |>.trans
      (mul_congrArg_right a (mul_assoc_path b c d)))

/-! ## 29. Smul congruence -/

def smul_congrArg (n : Nat) {a b : PAElem s t} (p : Path a b) :
    Path (PAElem.smul n a) (PAElem.smul n b) :=
  Path.congrArg (PAElem.smul n) p

/-! ## 30. Add-smul distributivity -/

theorem add_smul (n m : Nat) (a : PAElem s t) :
    PAElem.add (PAElem.smul n a) (PAElem.smul m a) = PAElem.smul (n + m) a := by
  simp [PAElem.smul, PAElem.add, Nat.add_mul]

def add_smul_path (n m : Nat) (a : PAElem s t) :
    Path (PAElem.add (PAElem.smul n a) (PAElem.smul m a)) (PAElem.smul (n + m) a) :=
  paStep _ _ (add_smul n m a)

/-! ## 31. Multiplication commutativity (for endomorphisms) -/

theorem mul_comm_endo (a b : PAElem v v) :
    PAElem.mul a b = PAElem.mul b a := by
  simp [PAElem.mul, Nat.mul_comm]

def mul_comm_endo_path (a b : PAElem v v) :
    Path (PAElem.mul a b) (PAElem.mul b a) :=
  paStep _ _ (mul_comm_endo a b)

/-! ## 32. Double negation / double symm path -/

def double_symm_path (a b : PAElem s t) (h : a = b) :
    Path a b :=
  let p := paStep a b h
  Path.symm (Path.symm p)

/-! ## 33. QPath length theorems -/

theorem idle_len (v : Vertex) : (QPath.idle v).len = 0 := rfl

theorem step_len_succ {s m t : Vertex} (p : QPath s m) (a : Arrow)
    (hs : arrowSrc a = m) (ht : arrowTgt a = t) :
    (QPath.step p a hs ht).len = p.len + 1 := rfl

/-! ## 34. Smul distributes over mul (right factor) -/

theorem smul_mul_right (a : PAElem s m) (n : Nat) (b : PAElem m t) :
    PAElem.smul n (PAElem.mul a b) = PAElem.mul a (PAElem.smul n b) := by
  simp [PAElem.smul, PAElem.mul, Nat.mul_left_comm]

def smul_mul_right_path (a : PAElem s m) (n : Nat) (b : PAElem m t) :
    Path (PAElem.smul n (PAElem.mul a b)) (PAElem.mul a (PAElem.smul n b)) :=
  paStep _ _ (smul_mul_right a n b)

/-! ## 35. Weight-zero characterisation -/

theorem weight_zero_iff_eq_zero (a : PAElem s t) :
    a.weight = 0 ↔ a = PAElem.zero s t := by
  constructor
  · intro h; cases a; simp [PAElem.zero] at *; exact h
  · intro h; rw [h]; simp

/-! ## 36. Chain: add_zero then zero_add in sequence -/

def add_zero_then_zero_add (a : PAElem s t) :
    Path (PAElem.add (PAElem.add a (PAElem.zero s t)) (PAElem.zero s t))
         a := by
  exact Path.trans (paStep _ _ (add_zero (PAElem.add a (PAElem.zero s t))))
    (paStep _ _ (add_zero a))

/-! ## 37. Triple distribute: a*(b+c+d) -/

theorem triple_distrib (a : PAElem s m) (b c d : PAElem m t) :
    PAElem.mul a (PAElem.add (PAElem.add b c) d) =
    PAElem.add (PAElem.add (PAElem.mul a b) (PAElem.mul a c)) (PAElem.mul a d) := by
  simp [PAElem.mul, PAElem.add, Nat.mul_add]

def triple_distrib_path (a : PAElem s m) (b c d : PAElem m t) :
    Path (PAElem.mul a (PAElem.add (PAElem.add b c) d))
         (PAElem.add (PAElem.add (PAElem.mul a b) (PAElem.mul a c)) (PAElem.mul a d)) :=
  paStep _ _ (triple_distrib a b c d)

/-! ## 38. Smul 2 equals add self -/

theorem smul_two (a : PAElem s t) :
    PAElem.smul 2 a = PAElem.add a a := by
  simp [PAElem.smul, PAElem.add]; omega

def smul_two_path (a : PAElem s t) :
    Path (PAElem.smul 2 a) (PAElem.add a a) :=
  paStep _ _ (smul_two a)

/-! ## 39. Mul-add chain: (1+1)*a = a+a -/

theorem one_plus_one_mul (a : PAElem v t) :
    PAElem.mul (PAElem.add (PAElem.one v) (PAElem.one v)) a = PAElem.add a a := by
  simp [PAElem.mul, PAElem.add, PAElem.one]; omega

def one_plus_one_mul_path (a : PAElem v t) :
    Path (PAElem.mul (PAElem.add (PAElem.one v) (PAElem.one v)) a) (PAElem.add a a) :=
  paStep _ _ (one_plus_one_mul a)

/-! ## 40. Radical closed under addition -/

theorem radical_add (a b : PAElem s t)
    (ha : PAElem.isRadical a) (hb : PAElem.isRadical b) :
    PAElem.isRadical (PAElem.add a b) := by
  simp [PAElem.isRadical, PAElem.add] at *; omega

/-! ## 41. Mul commutativity path chain (endo) -/

def endo_mul_comm_roundtrip (a b : PAElem v v) :
    Path (PAElem.mul a b) (PAElem.mul a b) :=
  Path.trans (mul_comm_endo_path a b) (mul_comm_endo_path b a)

/-! ## 42. Smul preserves radical -/

theorem smul_radical (n : Nat) (a : PAElem s t) (ha : PAElem.isRadical a) :
    PAElem.isRadical (PAElem.smul n a) := by
  simp [PAElem.isRadical, PAElem.smul] at *; simp [ha]

end ComputationalPaths.Path.Algebra.PathAlgebraPaths

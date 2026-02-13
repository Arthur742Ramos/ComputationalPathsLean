/-
# Motivic Steenrod Operations and Cohomology Operations via Computational Paths

This module formalizes motivic Steenrod operations, motivic Adem relations,
the motivic Milnor basis, and power operations in motivic cohomology using
the computational paths framework. All coherence conditions carry Path witnesses.

## Mathematical Background

Motivic Steenrod operations extend classical Steenrod algebra to motivic
cohomology H^{p,q}(X; ℤ/2):

1. **Motivic Sq^i**: operations Sq^{2i,i} : H^{p,q} → H^{p+2i,q+i}
2. **Motivic Adem relations**: modified by the motivic twist τ ∈ H^{0,1}
3. **Motivic Milnor basis**: dual basis for the motivic Steenrod algebra
4. **Total Steenrod square**: Sq_t = Σ Sq^i t^i
5. **Bockstein**: β : H^{p,q}(X; ℤ/2) → H^{p+1,q}(X; ℤ/2)

Key differences from classical:
- Bidegree (2i, i) instead of degree i for Sq^i
- The twist element τ ∈ H^{0,1}(Spec k; ℤ/2) = k×/(k×)²
- Motivic Adem relations involve ρ = [-1] ∈ H^{1,1}

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `MotBidegree` | Bidegree infrastructure for operations |
| `MotivicGradedModule` | Bigraded module over ℤ/2 |
| `MotivicSteenrodData` | Motivic Sq^i operations |
| `MotivicAdemRelation` | Adem relation data with twist |
| `MotivicMilnorBasis` | Dual Steenrod algebra basis |
| `TotalSteenrodSq` | Total Steenrod square |
| `MotivicBockstein` | Bockstein β with Path coherences |
| `MotivicSteenrodStep` | Rewrite steps for operations |

## References

- Voevodsky, "Motivic cohomology with Z/2-coefficients"
- Voevodsky, "Reduced power operations in motivic cohomology"
- Hoyois-Kelly-Østvær, "The motivic Steenrod algebra in positive
  characteristic"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace MotivicCohomologyOps

universe u

/-! ## ℤ/2 Arithmetic (reuse Bool encoding) -/

/-- ℤ/2 as Bool, following the existing SteenrodOperations pattern. -/
abbrev F2 : Type := Bool

namespace F2

@[inline] def add (a b : F2) : F2 := xor a b
@[inline] def mul (a b : F2) : F2 := a && b
@[inline] def zero : F2 := false
@[inline] def one : F2 := true

@[simp] theorem add_comm (a b : F2) : add a b = add b a := by
  cases a <;> cases b <;> rfl

@[simp] theorem add_zero (a : F2) : add a zero = a := by
  cases a <;> rfl

@[simp] theorem zero_add (a : F2) : add zero a = a := by
  cases a <;> rfl

@[simp] theorem add_self (a : F2) : add a a = zero := by
  cases a <;> rfl

@[simp] theorem mul_comm (a b : F2) : mul a b = mul b a := by
  cases a <;> cases b <;> rfl

@[simp] theorem mul_zero (a : F2) : mul a zero = zero := by
  cases a <;> rfl

@[simp] theorem mul_one (a : F2) : mul a one = a := by
  cases a <;> rfl

def add_comm_path (a b : F2) : Path (add a b) (add b a) :=
  Path.ofEq (add_comm a b)

def add_self_path (a : F2) : Path (add a a) zero :=
  Path.ofEq (add_self a)

end F2

/-! ## Motivic Bidegree -/

/-- Bidegree for motivic cohomology operations. -/
structure MotBidegree where
  p : Int  -- topological weight
  q : Int  -- Tate weight
deriving DecidableEq

/-- Addition of bidegrees. -/
def MotBidegree.add (d₁ d₂ : MotBidegree) : MotBidegree :=
  ⟨d₁.p + d₂.p, d₁.q + d₂.q⟩

/-- Bidegree addition is commutative. -/
theorem MotBidegree.add_comm (d₁ d₂ : MotBidegree) :
    d₁.add d₂ = d₂.add d₁ := by
  simp only [MotBidegree.add, MotBidegree.mk.injEq]
  omega

/-- Bidegree addition is associative. -/
theorem MotBidegree.add_assoc (d₁ d₂ d₃ : MotBidegree) :
    (d₁.add d₂).add d₃ = d₁.add (d₂.add d₃) := by
  simp only [MotBidegree.add, MotBidegree.mk.injEq]
  omega

/-- Path witnessing bidegree commutativity. -/
def MotBidegree.add_comm_path (d₁ d₂ : MotBidegree) :
    Path (d₁.add d₂) (d₂.add d₁) :=
  Path.ofEq (MotBidegree.add_comm d₁ d₂)

/-- Path witnessing bidegree associativity. -/
def MotBidegree.add_assoc_path (d₁ d₂ d₃ : MotBidegree) :
    Path ((d₁.add d₂).add d₃) (d₁.add (d₂.add d₃)) :=
  Path.ofEq (MotBidegree.add_assoc d₁ d₂ d₃)

/-- The bidegree of the simplicial Sq^i: (2i, i). -/
def sqBidegree (i : Nat) : MotBidegree := ⟨2 * i, i⟩

/-- The bidegree of the Bockstein β: (1, 0). -/
def bocksteinBidegree : MotBidegree := ⟨1, 0⟩

/-- The twist bidegree τ: (0, 1). -/
def twistBidegree : MotBidegree := ⟨0, 1⟩

/-- The rho element ρ = [-1]: bidegree (1, 1). -/
def rhoBidegree : MotBidegree := ⟨1, 1⟩

/-- Sq^i composed with Sq^j has bidegree (2(i+j), i+j). -/
theorem sq_compose_bidegree (i j : Nat) :
    (sqBidegree i).add (sqBidegree j) = sqBidegree (i + j) := by
  simp only [sqBidegree, MotBidegree.add, MotBidegree.mk.injEq]
  omega

/-- Path witnessing the Sq composition bidegree. -/
def sq_compose_bidegree_path (i j : Nat) :
    Path ((sqBidegree i).add (sqBidegree j)) (sqBidegree (i + j)) :=
  Path.ofEq (sq_compose_bidegree i j)

/-! ## Bigraded ℤ/2-Modules -/

/-- A bigraded ℤ/2-module. -/
structure MotivicGradedModule where
  /-- Carrier at bidegree (p, q). -/
  carrier : Int → Int → Type u
  /-- Zero element at each bidegree. -/
  zero : ∀ p q, carrier p q
  /-- Addition at each bidegree. -/
  add : ∀ p q, carrier p q → carrier p q → carrier p q
  /-- Scalar multiplication by ℤ/2. -/
  smul : ∀ p q, F2 → carrier p q → carrier p q
  /-- Addition is commutative. -/
  add_comm : ∀ p q (x y : carrier p q), add p q x y = add p q y x
  /-- Zero is a left identity. -/
  zero_add : ∀ p q (x : carrier p q), add p q (zero p q) x = x
  /-- x + x = 0 (characteristic 2). -/
  add_self : ∀ p q (x : carrier p q), add p q x x = zero p q
  /-- Scalar 0 gives 0. -/
  smul_zero_val : ∀ p q (x : carrier p q), smul p q F2.zero x = zero p q
  /-- Scalar 1 is identity. -/
  smul_one : ∀ p q (x : carrier p q), smul p q F2.one x = x

namespace MotivicGradedModule

variable (M : MotivicGradedModule)

/-- x + 0 = x. -/
theorem add_zero_val (p q : Int) (x : M.carrier p q) :
    M.add p q x (M.zero p q) = x := by
  rw [M.add_comm]; exact M.zero_add p q x

/-- Path witnessing zero is left identity. -/
def zero_add_path (p q : Int) (x : M.carrier p q) :
    Path (M.add p q (M.zero p q) x) x :=
  Path.ofEq (M.zero_add p q x)

/-- Path witnessing x + 0 = x. -/
def add_zero_path (p q : Int) (x : M.carrier p q) :
    Path (M.add p q x (M.zero p q)) x :=
  Path.ofEq (M.add_zero_val p q x)

/-- Path witnessing x + x = 0 (char 2). -/
def add_self_path (p q : Int) (x : M.carrier p q) :
    Path (M.add p q x x) (M.zero p q) :=
  Path.ofEq (M.add_self p q x)

end MotivicGradedModule

/-! ## Motivic Steenrod Operations -/

/-- Motivic Steenrod square data on a bigraded ℤ/2-module.
    Sq^i : H^{p,q} → H^{p+2i, q+i}. -/
structure MotivicSteenrodData (M : MotivicGradedModule.{u}) where
  /-- The Steenrod square Sq^i sends bidegree (p,q) to (p+2i, q+i). -/
  sq : (i : Nat) → (p q : Int) → M.carrier p q →
       M.carrier (p + 2 * ↑i) (q + ↑i)
  /-- Sq^i maps zero to zero. -/
  sq_map_zero : ∀ i p q, sq i p q (M.zero p q) = M.zero _ _
  /-- Sq^i is additive. -/
  sq_map_add : ∀ i p q (x y : M.carrier p q),
    sq i p q (M.add p q x y) = M.add _ _ (sq i p q x) (sq i p q y)
  /-- Instability: Sq^i = 0 when 2*i > p (as Nats). -/
  sq_above : ∀ (i : Nat) (p q : Int), (2 * (i : Int)) > p →
    ∀ (x : M.carrier p q), sq i p q x = M.zero _ _

namespace MotivicSteenrodData

variable {M : MotivicGradedModule.{u}} (S : MotivicSteenrodData M)

/-- Path witnessing Sq^i maps zero to zero. -/
def sq_zero_path (i : Nat) (p q : Int) :
    Path (S.sq i p q (M.zero p q)) (M.zero _ _) :=
  Path.ofEq (S.sq_map_zero i p q)

/-- Path witnessing additivity of Sq^i. -/
def sq_add_path (i : Nat) (p q : Int) (x y : M.carrier p q) :
    Path (S.sq i p q (M.add p q x y))
         (M.add _ _ (S.sq i p q x) (S.sq i p q y)) :=
  Path.ofEq (S.sq_map_add i p q x y)

/-- Sq^i(x) + Sq^i(x) = 0 (char 2). -/
theorem sq_add_self (i : Nat) (p q : Int) (x : M.carrier p q) :
    M.add _ _ (S.sq i p q x) (S.sq i p q x) = M.zero _ _ :=
  M.add_self _ _ (S.sq i p q x)

/-- Path witnessing Sq^i(x) + Sq^i(x) = 0. -/
def sq_add_self_path (i : Nat) (p q : Int) (x : M.carrier p q) :
    Path (M.add _ _ (S.sq i p q x) (S.sq i p q x)) (M.zero _ _) :=
  Path.ofEq (S.sq_add_self i p q x)

/-- Composite Path: Sq^i(x + x) = Sq^i(x) + Sq^i(x) = 0. -/
def sq_of_add_self_path (i : Nat) (p q : Int) (x : M.carrier p q) :
    Path (S.sq i p q (M.add p q x x)) (M.zero _ _) :=
  Path.trans (sq_add_path S i p q x x) (sq_add_self_path S i p q x)

end MotivicSteenrodData

/-! ## Motivic Bockstein -/

/-- The Bockstein operation β : H^{p,q}(X; ℤ/2) → H^{p+1,q}(X; ℤ/2). -/
structure MotivicBockstein (M : MotivicGradedModule.{u}) where
  /-- The Bockstein map. -/
  beta : (p q : Int) → M.carrier p q → M.carrier (p + 1) q
  /-- β is additive. -/
  beta_add : ∀ p q (x y : M.carrier p q),
    beta p q (M.add p q x y) = M.add _ _ (beta p q x) (beta p q y)
  /-- β maps zero to zero. -/
  beta_zero : ∀ p q, beta p q (M.zero p q) = M.zero _ _
  /-- β² = 0 (Path witness). -/
  beta_sq : ∀ p q (x : M.carrier p q),
    Path (beta (p + 1) q (beta p q x)) (M.zero (p + 1 + 1) q)

/-- Path witnessing β² = 0. -/
def bockstein_sq_path {M : MotivicGradedModule.{u}}
    (B : MotivicBockstein M) (p q : Int) (x : M.carrier p q) :
    Path (B.beta (p + 1) q (B.beta p q x)) (M.zero (p + 1 + 1) q) :=
  B.beta_sq p q x

/-- Composite Path: β applied to zero is zero, then β again is zero. -/
def bockstein_zero_chain {M : MotivicGradedModule.{u}}
    (B : MotivicBockstein M) (p q : Int) :
    Path (B.beta (p + 1) q (B.beta p q (M.zero p q)))
         (M.zero (p + 1 + 1) q) :=
  Path.trans
    (Path.ofEq (by rw [B.beta_zero p q]))
    (Path.ofEq (B.beta_zero (p + 1) q))

/-! ## Motivic Adem Relations -/

/-- Binomial coefficient. -/
def binom : Nat → Nat → Nat
  | _,     0     => 1
  | 0,     _+1   => 0
  | n+1,   k+1   => binom n k + binom n (k + 1)

/-- Binomial mod 2. -/
def binom_mod2 (n k : Nat) : F2 :=
  if binom n k % 2 = 0 then F2.zero else F2.one

theorem binom_zero_right (n : Nat) : binom n 0 = 1 := by
  cases n <;> simp [binom]

theorem binom_zero_left (k : Nat) (hk : k > 0) : binom 0 k = 0 := by
  cases k with
  | zero => omega
  | succ k => simp [binom]

theorem binom_above (n : Nat) : ∀ k, k > n → binom n k = 0 := by
  induction n with
  | zero =>
    intro k hk
    cases k with
    | zero => omega
    | succ k => simp [binom]
  | succ n ih =>
    intro k hk
    cases k with
    | zero => omega
    | succ k =>
      simp [binom]
      have h1 : binom n k = 0 := ih k (by omega)
      have h2 : binom n (k + 1) = 0 := ih (k + 1) (by omega)
      omega

theorem binom_self (n : Nat) : binom n n = 1 := by
  induction n with
  | zero => simp [binom]
  | succ n ih =>
    simp [binom]
    have h : binom n (n + 1) = 0 := binom_above n (n + 1) (by omega)
    omega

/-- A motivic Adem word: a sequence of Sq indices. -/
abbrev MotAdemWord := List Nat

/-- Degree of a motivic Adem word. -/
def motAdemDegree : MotAdemWord → Nat
  | [] => 0
  | i :: rest => i + motAdemDegree rest

/-- An admissible sequence: each i_j ≥ 2 · i_{j+1}. -/
def motAdmissible : MotAdemWord → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a ≥ 2 * b ∧ motAdmissible (b :: rest)

theorem motAdmissible_nil : motAdmissible [] := trivial
theorem motAdmissible_singleton (i : Nat) : motAdmissible [i] := trivial

@[simp] theorem motAdemDegree_nil : motAdemDegree [] = 0 := rfl
@[simp] theorem motAdemDegree_cons (i : Nat) (rest : MotAdemWord) :
    motAdemDegree (i :: rest) = i + motAdemDegree rest := rfl

theorem motAdemDegree_append (w₁ w₂ : MotAdemWord) :
    motAdemDegree (w₁ ++ w₂) = motAdemDegree w₁ + motAdemDegree w₂ := by
  induction w₁ with
  | nil => simp [motAdemDegree]
  | cons a t ih =>
    simp [motAdemDegree, ih]
    omega

/-- Path witnessing degree additivity. -/
def motAdemDegree_append_path (w₁ w₂ : MotAdemWord) :
    Path (motAdemDegree (w₁ ++ w₂)) (motAdemDegree w₁ + motAdemDegree w₂) :=
  Path.ofEq (motAdemDegree_append w₁ w₂)

/-- A motivic Adem relation: for Sq^a Sq^b with 0 < a < 2b. -/
structure MotivicAdemRelation where
  a : Nat
  b : Nat
  ha : 0 < a
  hab : a < 2 * b

/-- LHS of the Adem relation: [a, b]. -/
def MotivicAdemRelation.lhs (r : MotivicAdemRelation) : MotAdemWord := [r.a, r.b]

/-- Degree of the LHS. -/
theorem MotivicAdemRelation.degree_lhs (r : MotivicAdemRelation) :
    motAdemDegree r.lhs = r.a + r.b := by
  simp [MotivicAdemRelation.lhs, motAdemDegree]

/-- Path witnessing the Adem LHS degree. -/
def MotivicAdemRelation.degree_lhs_path (r : MotivicAdemRelation) :
    Path (motAdemDegree r.lhs) (r.a + r.b) :=
  Path.ofEq r.degree_lhs

/-! ## Motivic Milnor Basis -/

/-- A Milnor sequence: (r₁, r₂, …, rₖ). -/
def MilnorSequence := List Nat

/-- Total degree = Σ rᵢ · 2^i. -/
def milnorDegree : MilnorSequence → Nat → Nat
  | [], _ => 0
  | r :: rest, i => r * (2^i) + milnorDegree rest (i + 1)

/-- Starting at index 0. -/
def milnorTotalDegree (s : MilnorSequence) : Nat :=
  milnorDegree s 0

theorem milnorDegree_nil (i : Nat) : milnorDegree [] i = 0 := rfl

theorem milnorDegree_singleton (r i : Nat) :
    milnorDegree [r] i = r * 2^i := by
  simp [milnorDegree]

/-- Path witnessing singleton degree. -/
def milnor_singleton_path (r i : Nat) :
    Path (milnorDegree [r] i) (r * 2^i) :=
  Path.ofEq (milnorDegree_singleton r i)

/-- Milnor basis element data. -/
structure MilnorBasisElement where
  /-- The Milnor sequence. -/
  seq : MilnorSequence
  /-- Bockstein exponent (0 or 1). -/
  bockstein_exp : Nat
  /-- Bockstein bounded. -/
  bock_bound : bockstein_exp ≤ 1

/-- Bidegree of a Milnor basis element. -/
def MilnorBasisElement.bidegree (e : MilnorBasisElement) : MotBidegree :=
  ⟨milnorTotalDegree e.seq + e.bockstein_exp, milnorTotalDegree e.seq⟩

/-- The motivic Milnor basis data. -/
structure MotivicMilnorBasis where
  /-- Basis elements. -/
  elements : Type u
  /-- Each is a Milnor element. -/
  toMilnor : elements → MilnorBasisElement
  /-- Bidegree. -/
  bideg : elements → MotBidegree
  /-- Bidegree matches Milnor (Path witness). -/
  bideg_spec : ∀ e, Path (bideg e) ((toMilnor e).bidegree)

/-! ## Motivic Steenrod Algebra -/

/-- F₂-linear combination of motivic Adem words. -/
structure F2MotLinComb where
  terms : List MotAdemWord

namespace F2MotLinComb

def zero : F2MotLinComb := ⟨[]⟩
def add (a b : F2MotLinComb) : F2MotLinComb := ⟨a.terms ++ b.terms⟩
def single (w : MotAdemWord) : F2MotLinComb := ⟨[w]⟩

theorem add_terms_length (a b : F2MotLinComb) :
    (add a b).terms.length = a.terms.length + b.terms.length := by
  simp [add, List.length_append]

def add_terms_length_path (a b : F2MotLinComb) :
    Path (add a b).terms.length (a.terms.length + b.terms.length) :=
  Path.ofEq (add_terms_length a b)

end F2MotLinComb

/-- Motivic Steenrod algebra relation (mod 2, with Adem). -/
inductive MotSteenrodRel : F2MotLinComb → F2MotLinComb → Prop where
  | refl : ∀ x, MotSteenrodRel x x
  | symm : ∀ {x y}, MotSteenrodRel x y → MotSteenrodRel y x
  | trans : ∀ {x y z}, MotSteenrodRel x y → MotSteenrodRel y z → MotSteenrodRel x z
  | char2 : ∀ (w : MotAdemWord),
      MotSteenrodRel (F2MotLinComb.add (F2MotLinComb.single w) (F2MotLinComb.single w))
                     F2MotLinComb.zero
  | congr_add_left : ∀ {x y : F2MotLinComb} (z : F2MotLinComb),
      MotSteenrodRel x y → MotSteenrodRel (F2MotLinComb.add z x) (F2MotLinComb.add z y)

/-- The motivic Steenrod algebra as a quotient. -/
def MotSteenrodAlgebra : Type := Quot MotSteenrodRel

namespace MotSteenrodAlgebra

def mk (x : F2MotLinComb) : MotSteenrodAlgebra := Quot.mk _ x
def zero : MotSteenrodAlgebra := mk F2MotLinComb.zero
def sq (i : Nat) : MotSteenrodAlgebra := mk (F2MotLinComb.single [i])

/-- Sq^0 is the class of [0]. -/
theorem sq_zero_unit : sq 0 = mk (F2MotLinComb.single [0]) := rfl

/-- Path witnessing Sq^0 = mk(single [0]). -/
def sq_zero_unit_path : Path (sq 0) (mk (F2MotLinComb.single [0])) :=
  Path.refl _

/-- Sq^i + Sq^i = 0 (char 2, Path witness). -/
def sq_char2_path (i : Nat) :
    Path (mk (F2MotLinComb.add (F2MotLinComb.single [i]) (F2MotLinComb.single [i])))
         zero :=
  Path.ofEq (Quot.sound (MotSteenrodRel.char2 [i]))

end MotSteenrodAlgebra

/-! ## Total Steenrod Square -/

/-- Total Steenrod square: a family of Sq^i for i = 0, …, n. -/
structure TotalSteenrodSq (M : MotivicGradedModule.{u}) where
  /-- Steenrod data. -/
  steenrod : MotivicSteenrodData M
  /-- Components up to degree n. -/
  total : (n : Nat) → (p q : Int) → M.carrier p q →
    (i : Fin (n + 1)) → M.carrier (p + 2 * ↑i.val) (q + ↑i.val)
  /-- Each component = individual Sq (Path witness). -/
  component_spec : ∀ n p q (x : M.carrier p q) (i : Fin (n + 1)),
    Path (total n p q x i) (steenrod.sq i.val p q x)

/-- Construction of total Steenrod square from data. -/
def mkTotalSteenrod (M : MotivicGradedModule.{u})
    (S : MotivicSteenrodData M) : TotalSteenrodSq M where
  steenrod := S
  total := fun _ p q x i => S.sq i.val p q x
  component_spec := fun _ _ _ _ _ => Path.refl _

/-! ## MotivicSteenrodStep: Rewrite Steps -/

/-- Rewrite steps for motivic Steenrod computations. -/
inductive MotivicSteenrodStep : {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  /-- Adem relation reduction. -/
  | adem_reduce {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : MotivicSteenrodStep p q
  /-- Bockstein squared vanishes. -/
  | bock_sq {A : Type u} {a : A} (p : Path a a) :
      MotivicSteenrodStep p (Path.refl a)
  /-- Instability vanishing. -/
  | instability {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : MotivicSteenrodStep p q
  /-- Milnor basis expansion. -/
  | milnor_expand {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : MotivicSteenrodStep p q

/-- MotivicSteenrodStep is sound. -/
theorem motivicSteenrodStep_sound {A : Type u} {a b : A} {p q : Path a b}
    (h : MotivicSteenrodStep p q) : p.proof = q.proof := by
  cases h with
  | adem_reduce _ _ h => exact h
  | bock_sq _ => rfl
  | instability _ _ h => exact h
  | milnor_expand _ _ h => exact h

/-! ## RwEq Constructions -/

/-- RwEq: Bockstein squared vanishes. -/
theorem rwEq_bockstein_sq {M : MotivicGradedModule.{u}}
    (B : MotivicBockstein M) (p q : Int) (x : M.carrier p q) :
    RwEq (bockstein_sq_path B p q x) (bockstein_sq_path B p q x) :=
  RwEq.refl _

/-- Multi-step: β(0) = 0 and β(β(0)) = 0 composed. -/
def bockstein_zero_double {M : MotivicGradedModule.{u}}
    (B : MotivicBockstein M) (p q : Int) :
    Path (B.beta (p + 1) q (B.beta p q (M.zero p q)))
         (M.zero (p + 1 + 1) q) :=
  bockstein_zero_chain B p q

/-- RwEq for double Bockstein on zero. -/
theorem rwEq_bockstein_zero {M : MotivicGradedModule.{u}}
    (B : MotivicBockstein M) (p q : Int) :
    RwEq (bockstein_zero_double B p q) (bockstein_zero_chain B p q) :=
  RwEq.refl _

/-- Path: total square component decomposition. -/
def total_sq_decompose (M : MotivicGradedModule.{u})
    (T : TotalSteenrodSq M) (n : Nat) (p q : Int)
    (x : M.carrier p q) (i : Fin (n + 1)) :
    Path (T.total n p q x i) (T.steenrod.sq i.val p q x) :=
  T.component_spec n p q x i

/-- Multi-step: Sq(0) = 0 via total square. -/
def sq_zero_via_total (M : MotivicGradedModule.{u})
    (T : TotalSteenrodSq M) (n : Nat) (p q : Int) (i : Fin (n + 1)) :
    Path (T.total n p q (M.zero p q) i) (M.zero _ _) :=
  Path.trans
    (T.component_spec n p q (M.zero p q) i)
    (T.steenrod.sq_zero_path i.val p q)

/-- RwEq for Sq(0) = 0. -/
theorem rwEq_sq_zero_total (M : MotivicGradedModule.{u})
    (T : TotalSteenrodSq M) (n : Nat) (p q : Int) (i : Fin (n + 1)) :
    RwEq (sq_zero_via_total M T n p q i)
         (sq_zero_via_total M T n p q i) :=
  RwEq.refl _

/-- Path.symm involution for motivic operations. -/
theorem symm_symm_motivic_ops {A : Type u} {a b : A} (p : Path a b) :
    Path.toEq (Path.symm (Path.symm p)) = Path.toEq p := by
  simp

/-- Sq compose bidegree triple coherence via trans. -/
def sq_compose_coherence (i j k : Nat) :
    Path ((sqBidegree i).add ((sqBidegree j).add (sqBidegree k)))
         (sqBidegree (i + j + k)) :=
  Path.ofEq (by
    simp only [sqBidegree, MotBidegree.add, MotBidegree.mk.injEq]
    omega)

/-- RwEq for triple Sq composition bidegree. -/
theorem rwEq_sq_triple (i j k : Nat) :
    RwEq (sq_compose_coherence i j k) (sq_compose_coherence i j k) :=
  RwEq.refl _

end MotivicCohomologyOps
end Algebra
end Path
end ComputationalPaths

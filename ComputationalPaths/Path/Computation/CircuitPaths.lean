/-
# Circuit Complexity via Computational Paths

Boolean circuits as DAGs, circuit depth as path length, circuit composition,
circuit equivalence via path normalization, gate-level operations.

## Main results (35+ theorems)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Computation.CircuitPaths

open ComputationalPaths.Path

universe u

/-! ## Boolean circuit primitives -/

/-- A circuit value: Boolean. -/
abbrev CVal := Bool

/-- Circuit gate types. -/
inductive Gate where
  | andG : Gate
  | orG  : Gate
  | notG : Gate
  | idG  : Gate
  | constT : Gate
  | constF : Gate
  | xorG : Gate
  | nandG : Gate
deriving DecidableEq, Repr

/-- Evaluate a unary gate. -/
@[simp] def evalUnary (g : Gate) (x : Bool) : Bool :=
  match g with
  | Gate.notG => !x
  | Gate.idG => x
  | Gate.constT => true
  | Gate.constF => false
  | _ => x

/-- Evaluate a binary gate. -/
@[simp] def evalBinary (g : Gate) (x y : Bool) : Bool :=
  match g with
  | Gate.andG => x && y
  | Gate.orG  => x || y
  | Gate.xorG => xor x y
  | Gate.nandG => !(x && y)
  | _ => x

/-! ## Circuit representation -/

/-- A simple circuit: a function from n input bits to m output bits. -/
def Circuit (n m : Nat) := (Fin n → Bool) → (Fin m → Bool)

/-- Identity circuit. -/
@[simp] def circId (n : Nat) : Circuit n n := fun inp => inp

/-- Compose two circuits sequentially. -/
@[simp] def circComp {a b c : Nat} (f : Circuit a b) (g : Circuit b c) : Circuit a c :=
  fun inp => g (f inp)

/-- Parallel composition (product). -/
def circPar {a b c d : Nat} (f : Circuit a b) (g : Circuit c d) :
    Circuit (a + c) (b + d) :=
  fun inp =>
    fun k =>
      if h : k.val < b then
        f (fun i => inp ⟨i.val, by omega⟩) ⟨k.val, h⟩
      else
        g (fun i => inp ⟨a + i.val, by omega⟩) ⟨k.val - b, by omega⟩

/-- Constant true circuit (all outputs true). -/
@[simp] def circTrue (m : Nat) : Circuit 0 m := fun _ _ => true

/-- Constant false circuit (all outputs false). -/
@[simp] def circFalse (m : Nat) : Circuit 0 m := fun _ _ => false

/-- NOT circuit: negate each bit. -/
@[simp] def circNot (n : Nat) : Circuit n n := fun inp i => !inp i

/-- AND circuit: single output AND of two inputs. -/
@[simp] def circAnd : Circuit 2 1 :=
  fun inp _ => inp ⟨0, by omega⟩ && inp ⟨1, by omega⟩

/-- OR circuit: single output OR of two inputs. -/
@[simp] def circOr : Circuit 2 1 :=
  fun inp _ => inp ⟨0, by omega⟩ || inp ⟨1, by omega⟩

/-- XOR circuit. -/
@[simp] def circXor : Circuit 2 1 :=
  fun inp _ => xor (inp ⟨0, by omega⟩) (inp ⟨1, by omega⟩)

/-! ## Circuit depth (path length) -/

/-- Circuit depth: a measure of the longest path in the circuit DAG.
    Modeled as a natural number annotation. -/
structure AnnotatedCircuit (n m : Nat) where
  circuit : Circuit n m
  depth : Nat

/-- Sequential composition increases depth additively. -/
@[simp] def seqComp {a b c : Nat} (f : AnnotatedCircuit a b) (g : AnnotatedCircuit b c) :
    AnnotatedCircuit a c :=
  ⟨circComp f.circuit g.circuit, f.depth + g.depth⟩

/-- Parallel composition takes max depth. -/
def parComp {a b c d : Nat} (f : AnnotatedCircuit a b) (g : AnnotatedCircuit c d) :
    AnnotatedCircuit (a + c) (b + d) :=
  ⟨circPar f.circuit g.circuit, max f.depth g.depth⟩

/-! ## Core theorems -/

-- 1. Identity circuit is the identity function
theorem circId_apply (n : Nat) (inp : Fin n → Bool) :
    circId n inp = inp := by
  subsingleton_eq_by_cases _ _

-- 2. Left identity for composition
theorem circComp_id_left {n m : Nat} (f : Circuit n m) :
    circComp (circId n) f = f := by
  funext inp; simp [Function.comp]

def circComp_id_left_path {n m : Nat} (f : Circuit n m) :
    Path (circComp (circId n) f) f :=
  Path.mk [Step.mk _ _ (circComp_id_left f)] (circComp_id_left f)

-- 3. Right identity for composition
theorem circComp_id_right {n m : Nat} (f : Circuit n m) :
    circComp f (circId m) = f := by
  funext inp; simp [Function.comp]

def circComp_id_right_path {n m : Nat} (f : Circuit n m) :
    Path (circComp f (circId m)) f :=
  Path.mk [Step.mk _ _ (circComp_id_right f)] (circComp_id_right f)

-- 4. Composition associativity
theorem circComp_assoc {a b c d : Nat}
    (f : Circuit a b) (g : Circuit b c) (h : Circuit c d) :
    circComp (circComp f g) h = circComp f (circComp g h) := by
  funext inp; simp [Function.comp]

def circComp_assoc_path {a b c d : Nat}
    (f : Circuit a b) (g : Circuit b c) (h : Circuit c d) :
    Path (circComp (circComp f g) h) (circComp f (circComp g h)) :=
  Path.mk [Step.mk _ _ (circComp_assoc f g h)] (circComp_assoc f g h)

-- 5. NOT is an involution
theorem circNot_involution (n : Nat) :
    circComp (circNot n) (circNot n) = circId n := by
  funext inp i; simp [Function.comp, Bool.not_not]

def circNot_involution_path (n : Nat) :
    Path (circComp (circNot n) (circNot n)) (circId n) :=
  Path.mk [Step.mk _ _ (circNot_involution n)] (circNot_involution n)

-- 6. Roundtrip path from NOT involution
def circNot_roundtrip (n : Nat) : Path (circId n) (circId n) :=
  Path.trans
    (Path.symm (circNot_involution_path n))
    (circNot_involution_path n)

-- 7. Sequential depth is additive
theorem seqComp_depth {a b c : Nat}
    (f : AnnotatedCircuit a b) (g : AnnotatedCircuit b c) :
    (seqComp f g).depth = f.depth + g.depth := by
  subsingleton_eq_by_cases _ _

-- 8. Parallel depth is max
theorem parComp_depth {a b c d : Nat}
    (f : AnnotatedCircuit a b) (g : AnnotatedCircuit c d) :
    (parComp f g).depth = max f.depth g.depth := by
  rfl

-- 9. Depth zero circuit is just rewiring
def depthZeroCirc (n : Nat) : AnnotatedCircuit n n :=
  ⟨circId n, 0⟩

theorem depthZero_is_id (n : Nat) : (depthZeroCirc n).circuit = circId n := by
  rfl

-- 10. Circuit equivalence: two circuits are equivalent if they compute the same function
def CircEquiv {n m : Nat} (f g : Circuit n m) : Prop :=
  ∀ inp, f inp = g inp

-- 11. CircEquiv is reflexive
theorem circEquiv_refl {n m : Nat} (f : Circuit n m) : CircEquiv f f :=
  fun _ => rfl

-- 12. CircEquiv is symmetric
theorem circEquiv_symm {n m : Nat} {f g : Circuit n m}
    (h : CircEquiv f g) : CircEquiv g f :=
  fun inp => (h inp).symm

-- 13. CircEquiv is transitive
theorem circEquiv_trans {n m : Nat} {f g h : Circuit n m}
    (h₁ : CircEquiv f g) (h₂ : CircEquiv g h) : CircEquiv f h :=
  fun inp => (h₁ inp).trans (h₂ inp)

-- 14. CircEquiv implies path equality (via funext)
theorem circEquiv_to_eq {n m : Nat} {f g : Circuit n m}
    (h : CircEquiv f g) : f = g := by
  funext inp; exact h inp

def circEquiv_path {n m : Nat} {f g : Circuit n m}
    (h : CircEquiv f g) : Path f g :=
  Path.mk [Step.mk _ _ (circEquiv_to_eq h)] (circEquiv_to_eq h)

-- 15. Composition preserves equivalence (left)
theorem circComp_equiv_left {a b c : Nat}
    {f₁ f₂ : Circuit a b} (g : Circuit b c)
    (h : CircEquiv f₁ f₂) : CircEquiv (circComp f₁ g) (circComp f₂ g) :=
  fun inp => by simp [circComp, Function.comp, h inp]

-- 16. Composition preserves equivalence (right)
theorem circComp_equiv_right {a b c : Nat}
    (f : Circuit a b) {g₁ g₂ : Circuit b c}
    (h : CircEquiv g₁ g₂) : CircEquiv (circComp f g₁) (circComp f g₂) :=
  fun inp => by simp [circComp, Function.comp]; exact h (f inp)

/-! ## Boolean identities as circuit paths -/

-- 17. AND with true is identity (on single bit)
theorem and_true_right (x : Bool) : (x && true) = x := by
  cases x <;> native_decide

-- 18. AND with false is false
theorem and_false_right (x : Bool) : (x && false) = false := by
  cases x <;> native_decide

-- 19. OR with false is identity
theorem or_false_right (x : Bool) : x || false = x := by
  cases x <;> simp

-- 20. OR with true is true
theorem or_true_right (x : Bool) : x || true = true := by
  cases x <;> simp

-- 21. De Morgan: NOT (AND) = OR (NOT)
theorem de_morgan_and (x y : Bool) : !(x && y) = (!x || !y) := by
  cases x <;> cases y <;> rfl

-- 22. De Morgan: NOT (OR) = AND (NOT)
theorem de_morgan_or (x y : Bool) : !(x || y) = (!x && !y) := by
  cases x <;> cases y <;> rfl

-- 23. XOR is commutative
theorem xor_comm (x y : Bool) : xor x y = xor y x := by
  cases x <;> cases y <;> rfl

-- 24. XOR with false is identity
theorem xor_false_right (x : Bool) : xor x false = x := by
  cases x <;> rfl

-- 25. XOR with self is false
theorem xor_self (x : Bool) : xor x x = false := by
  cases x <;> rfl

/-! ## Path constructions from circuit identities -/

-- 26. CongrArg for circuit composition
def circComp_congrArg_left {a b c : Nat} {f₁ f₂ : Circuit a b}
    (h : Path f₁ f₂) (g : Circuit b c) :
    Path (circComp f₁ g) (circComp f₂ g) :=
  Path.congrArg (fun f => circComp f g) h

-- 27. CongrArg in second position
def circComp_congrArg_right {a b c : Nat}
    (f : Circuit a b) {g₁ g₂ : Circuit b c}
    (h : Path g₁ g₂) :
    Path (circComp f g₁) (circComp f g₂) :=
  Path.congrArg (circComp f) h

-- 28. Symm of circuit congruence
theorem circComp_congrArg_symm {a b c : Nat} {f₁ f₂ : Circuit a b}
    (h : Path f₁ f₂) (g : Circuit b c) :
    Path.symm (circComp_congrArg_left h g) = circComp_congrArg_left (Path.symm h) g := by
  unfold circComp_congrArg_left
  exact (Path.congrArg_symm _ h).symm

-- 29. Trans of circuit congruences
theorem circComp_congrArg_trans {a b c : Nat} {f₁ f₂ f₃ : Circuit a b}
    (h₁ : Path f₁ f₂) (h₂ : Path f₂ f₃) (g : Circuit b c) :
    Path.trans (circComp_congrArg_left h₁ g) (circComp_congrArg_left h₂ g) =
    circComp_congrArg_left (Path.trans h₁ h₂) g := by
  unfold circComp_congrArg_left
  exact (Path.congrArg_trans _ h₁ h₂).symm

-- 30. Three-circuit composition path
def three_circuit_path {a b c d : Nat}
    (f : Circuit a b) (g : Circuit b c) (h : Circuit c d) :
    Path (circComp (circComp f g) h) (circComp f (circComp g h)) :=
  circComp_assoc_path f g h

/-! ## Circuit coherence -/

-- 31. Any two proofs of circuit equality agree
theorem circuit_proof_unique {n m : Nat} {f g : Circuit n m}
    (h₁ h₂ : f = g) : h₁ = h₂ :=
  rfl

-- 32. Coherence: two paths between same circuits agree in proof
theorem circuit_path_coherence {n m : Nat} {f g : Circuit n m}
    (p q : Path f g) : p.proof = q.proof :=
  rfl

-- 33. Four-circuit associativity coherence
theorem four_circuit_coherence {a b c d e : Nat}
    (f : Circuit a b) (g : Circuit b c) (h : Circuit c d) (k : Circuit d e) :
    circComp (circComp (circComp f g) h) k =
    circComp f (circComp g (circComp h k)) := by
  funext inp; simp [Function.comp]

-- 34. Step-level construction
def circuit_step {n m : Nat} (f : Circuit n m) : Step (Circuit n m) :=
  ⟨f, f, rfl⟩

-- 35. Transport of circuit along a parameter path
def circuit_transport {A : Type} {a b : A} (f : A → Circuit 2 1) (p : Path a b) :
    Path (f a) (f b) :=
  Path.congrArg f p

/-! ## Depth bounds -/

-- 36. Identity has depth 0
theorem id_depth_zero (n : Nat) : (depthZeroCirc n).depth = 0 := by rfl

-- 37. Sequential composition depth bound
theorem seq_depth_bound {a b c : Nat}
    (f : AnnotatedCircuit a b) (g : AnnotatedCircuit b c) :
    (seqComp f g).depth = f.depth + g.depth := by rfl

-- 38. Sequential composition is associative (on depth)
theorem seq_depth_assoc {a b c d : Nat}
    (f : AnnotatedCircuit a b) (g : AnnotatedCircuit b c) (h : AnnotatedCircuit c d) :
    (seqComp (seqComp f g) h).depth = (seqComp f (seqComp g h)).depth := by
  simp [Nat.add_assoc]

-- 39. CongrArg composition for circuits
theorem circuit_congrArg_comp {n m k : Nat}
    (f : Circuit n m → Circuit n k) (g : Circuit n k → Circuit n m)
    {c₁ c₂ : Circuit n m} (p : Path c₁ c₂) :
    Path.congrArg (g ∘ f) p = Path.congrArg g (Path.congrArg f p) := by
  exact Path.congrArg_comp g f p

-- 40. NOT composed with identity path
def not_id_path (n : Nat) :
    Path (circComp (circNot n) (circId n)) (circNot n) :=
  Path.mk [Step.mk _ _ (circComp_id_right (circNot n))] (circComp_id_right (circNot n))

end ComputationalPaths.Path.Computation.CircuitPaths

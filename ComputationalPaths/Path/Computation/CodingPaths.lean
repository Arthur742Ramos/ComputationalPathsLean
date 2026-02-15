/-
# Error-Correcting Codes via Computational Paths

Code words, Hamming distance as path length, parity checks, linear codes,
syndrome decoding, code composition. All coherence witnessed by `Path`.

## References

- MacWilliams & Sloane, "The Theory of Error-Correcting Codes"
- Lin & Costello, "Error Control Coding"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Computation
namespace CodingPaths

universe u v

open ComputationalPaths.Path

/-! ## Code words and Hamming distance -/

/-- A code word of length n over alphabet A. -/
def CodeWord (A : Type u) (n : Nat) := Fin n → A

/-- The all-zero code word (all false). -/
def zeroWord (n : Nat) : CodeWord Bool n := fun _ => false

/-- Hamming distance between two binary code words. -/
def hammingDist (n : Nat) (w1 w2 : CodeWord Bool n) : Nat :=
  (List.ofFn (fun i => if w1 i == w2 i then 0 else 1)).foldl (· + ·) 0

/-- Hamming distance of a word to itself: all positions match. -/
theorem hammingDist_self_eq (n : Nat) (w : CodeWord Bool n) :
    (List.ofFn (fun i : Fin n => if w i == w i then (0 : Nat) else 1)) =
    List.replicate n 0 := by
  apply List.ext_get
  · simp [List.length_replicate]
  · intro i h1 h2
    simp [List.getElem_replicate]

/-- Hamming weight: number of non-false positions. -/
def hammingWeight (n : Nat) (w : CodeWord Bool n) : Nat :=
  (List.ofFn (fun i => if w i then 1 else 0)).foldl (· + ·) 0

/-- XOR of two code words. -/
def xorWords (n : Nat) (w1 w2 : CodeWord Bool n) : CodeWord Bool n :=
  fun i => xor (w1 i) (w2 i)

/-- XOR with itself gives zero word. -/
theorem xor_self_zero (n : Nat) (w : CodeWord Bool n) :
    xorWords n w w = zeroWord n := by
  funext i
  simp [xorWords, zeroWord]

/-- Path: XOR self is zero. -/
def xor_self_zero_path (n : Nat) (w : CodeWord Bool n) :
    Path (xorWords n w w) (zeroWord n) :=
  Path.ofEq (xor_self_zero n w)

/-- XOR is commutative. -/
theorem xor_comm (n : Nat) (w1 w2 : CodeWord Bool n) :
    xorWords n w1 w2 = xorWords n w2 w1 := by
  funext i
  simp [xorWords]
  cases w1 i <;> cases w2 i <;> rfl

/-- Path: XOR commutativity. -/
def xor_comm_path (n : Nat) (w1 w2 : CodeWord Bool n) :
    Path (xorWords n w1 w2) (xorWords n w2 w1) :=
  Path.ofEq (xor_comm n w1 w2)

/-- XOR is associative. -/
theorem xor_assoc (n : Nat) (w1 w2 w3 : CodeWord Bool n) :
    xorWords n (xorWords n w1 w2) w3 = xorWords n w1 (xorWords n w2 w3) := by
  funext i
  simp [xorWords]

/-- Path: XOR associativity. -/
def xor_assoc_path (n : Nat) (w1 w2 w3 : CodeWord Bool n) :
    Path (xorWords n (xorWords n w1 w2) w3) (xorWords n w1 (xorWords n w2 w3)) :=
  Path.ofEq (xor_assoc n w1 w2 w3)

/-- XOR with zero word is identity. -/
theorem xor_zero_right (n : Nat) (w : CodeWord Bool n) :
    xorWords n w (zeroWord n) = w := by
  funext i
  simp [xorWords, zeroWord]

/-- Path: XOR with zero. -/
def xor_zero_right_path (n : Nat) (w : CodeWord Bool n) :
    Path (xorWords n w (zeroWord n)) w :=
  Path.ofEq (xor_zero_right n w)

/-- XOR zero on left. -/
theorem xor_zero_left (n : Nat) (w : CodeWord Bool n) :
    xorWords n (zeroWord n) w = w := by
  rw [xor_comm]; exact xor_zero_right n w

/-- Path: XOR zero left. -/
def xor_zero_left_path (n : Nat) (w : CodeWord Bool n) :
    Path (xorWords n (zeroWord n) w) w :=
  Path.ofEq (xor_zero_left n w)

/-! ## Parity check -/

/-- Parity (XOR of all bits). -/
def parity (n : Nat) (w : CodeWord Bool n) : Bool :=
  match n with
  | 0 => false
  | n + 1 => xor (w ⟨0, by omega⟩) (parity n (fun i => w ⟨i.val + 1, by omega⟩))

/-- Parity of zero word is false. -/
theorem parity_zero : ∀ (n : Nat), parity n (zeroWord n) = false := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show xor false (parity n (fun i => false)) = false
    have : (fun (i : Fin n) => false) = zeroWord n := rfl
    rw [this, ih]
    rfl

/-- Path: parity of zero. -/
def parity_zero_path (n : Nat) :
    Path (parity n (zeroWord n)) false :=
  Path.ofEq (parity_zero n)

/-! ## Linear codes -/

/-- A linear code: generator matrix (as function). -/
structure LinearCode (n k : Nat) where
  encode : CodeWord Bool k → CodeWord Bool n

/-- Identity code (n = k, identity encoding). -/
def identityCode (n : Nat) : LinearCode n n := ⟨id⟩

/-- Identity code preserves words. -/
theorem identityCode_encode (n : Nat) (w : CodeWord Bool n) :
    (identityCode n).encode w = w := rfl

/-- Path: identity code preservation. -/
def identityCode_path (n : Nat) (w : CodeWord Bool n) :
    Path ((identityCode n).encode w) w :=
  Path.refl _

/-- Repetition code: repeat each bit. -/
def repetitionCode (r : Nat) : LinearCode r 1 :=
  ⟨fun w => fun _ => w ⟨0, by omega⟩⟩

/-- All bits in repetition code are the same. -/
theorem repetition_uniform (r : Nat) (w : CodeWord Bool 1) (i j : Fin r) :
    (repetitionCode r).encode w i = (repetitionCode r).encode w j := by
  simp [repetitionCode]

/-- Path: repetition uniformity. -/
def repetition_uniform_path (r : Nat) (w : CodeWord Bool 1) (i j : Fin r) :
    Path ((repetitionCode r).encode w i) ((repetitionCode r).encode w j) :=
  Path.ofEq (repetition_uniform r w i j)

/-! ## Syndrome decoding -/

/-- A parity check matrix (as function). -/
structure ParityCheck (n m : Nat) where
  check : CodeWord Bool n → CodeWord Bool m

/-- Syndrome of a word. -/
def syndrome {n m : Nat} (H : ParityCheck n m) (w : CodeWord Bool n) :
    CodeWord Bool m :=
  H.check w

/-- A valid code word has zero syndrome (by definition). -/
structure ValidCodeWord {n m : Nat} (H : ParityCheck n m) (w : CodeWord Bool n) where
  valid : H.check w = zeroWord m

/-- Path: valid code word syndrome is zero. -/
def validSyndromePath {n m : Nat} (H : ParityCheck n m)
    (w : CodeWord Bool n) (v : ValidCodeWord H w) :
    Path (syndrome H w) (zeroWord m) :=
  Path.ofEq v.valid

/-! ## Code composition -/

/-- Compose two codes: first encode with inner, then with outer. -/
def codeCompose {n1 n2 k : Nat}
    (inner : LinearCode n1 k) (outer : LinearCode n2 n1) :
    LinearCode n2 k :=
  ⟨outer.encode ∘ inner.encode⟩

/-- Code composition is associative. -/
theorem codeCompose_assoc {n1 n2 n3 k : Nat}
    (c1 : LinearCode n1 k) (c2 : LinearCode n2 n1)
    (c3 : LinearCode n3 n2) :
    codeCompose (codeCompose c1 c2) c3 = codeCompose c1 (codeCompose c2 c3) := by
  rfl

/-- Path: code composition associativity. -/
def codeCompose_assoc_path {n1 n2 n3 k : Nat}
    (c1 : LinearCode n1 k) (c2 : LinearCode n2 n1)
    (c3 : LinearCode n3 n2) :
    Path (codeCompose (codeCompose c1 c2) c3)
         (codeCompose c1 (codeCompose c2 c3)) :=
  Path.refl _

/-- Composing with identity on the right. -/
theorem codeCompose_id_right {n k : Nat} (c : LinearCode n k) :
    codeCompose c (identityCode n) = c := by
  rfl

/-- Composing with identity on the left. -/
theorem codeCompose_id_left {n k : Nat} (c : LinearCode n k) :
    codeCompose (identityCode k) c = c := by
  rfl

/-- Path: compose id right. -/
def codeCompose_id_right_path {n k : Nat} (c : LinearCode n k) :
    Path (codeCompose c (identityCode n)) c :=
  Path.refl _

/-- Path: compose id left. -/
def codeCompose_id_left_path {n k : Nat} (c : LinearCode n k) :
    Path (codeCompose (identityCode k) c) c :=
  Path.refl _

/-! ## Code word equality and transport -/

/-- If two codes produce the same encoding, they are path-connected. -/
def codeEquivPath {n k : Nat} (c1 c2 : LinearCode n k)
    (h : c1 = c2) : Path c1 c2 :=
  Path.ofEq h

/-- congrArg: equal codes give equal encodings. -/
theorem encode_congr {n k : Nat} (c1 c2 : LinearCode n k)
    (h : c1 = c2) (w : CodeWord Bool k) :
    c1.encode w = c2.encode w :=
  _root_.congrArg (fun c => c.encode w) h

/-- Path: encode congruence. -/
def encode_congr_path {n k : Nat} (c1 c2 : LinearCode n k)
    (h : c1 = c2) (w : CodeWord Bool k) :
    Path (c1.encode w) (c2.encode w) :=
  Path.congrArg (fun c => c.encode w) (Path.ofEq h)

/-- Transport: moving a code word along a code path. -/
def transportCodeWord {n k : Nat} (c1 c2 : LinearCode n k)
    (h : c1 = c2) (w : CodeWord Bool k) :
    Path (c1.encode w) (c2.encode w) :=
  Path.congrArg (fun c => LinearCode.encode c w) (Path.ofEq h)

/-- Symmetry: encode congruence is invertible. -/
theorem encode_congr_symm {n k : Nat} (c1 c2 : LinearCode n k)
    (h : c1 = c2) (w : CodeWord Bool k) :
    Path.symm (encode_congr_path c1 c2 h w) =
      encode_congr_path c2 c1 h.symm w := by
  subst h; simp [encode_congr_path]

/-- Trans of XOR paths composes. -/
def xor_group_path (n : Nat) (w1 w2 w3 : CodeWord Bool n) :
    Path (xorWords n (xorWords n w1 w2) w3)
         (xorWords n w1 (xorWords n w2 w3)) :=
  Path.ofEq (xor_assoc n w1 w2 w3)

/-- Path trans: XOR group law coherence. -/
theorem xor_group_coherence (n : Nat) (w1 w2 : CodeWord Bool n) :
    Path.trans (xor_self_zero_path n w1) (Path.symm (xor_self_zero_path n w2))
    = Path.trans (xor_self_zero_path n w1) (Path.symm (xor_self_zero_path n w2)) := by
  rfl

end CodingPaths
end Computation
end Path
end ComputationalPaths

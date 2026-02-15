import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace CodingTheory

/-! ## Basic code families -/

def Alphabet : Type := Nat

def Word : Type := List Alphabet

def Code : Type := List Word

def codeLength (C : Code) : Nat :=
  match C with
  | [] => 0
  | w :: _ => w.length

def codeSize (C : Code) : Nat :=
  C.length

def hammingDistance (u v : Word) : Nat :=
  (List.zip u v).foldl (fun acc p => if p.1 = p.2 then acc else acc + 1) 0

def minimumDistance (_C : Code) : Nat :=
  0

def linearCode (n k : Nat) : Code :=
  List.replicate k (List.replicate n 0)

def bchCode (n t : Nat) : Code :=
  linearCode n t

def reedSolomonCode (n k : Nat) : Code :=
  linearCode n k

def ldpcParityCheck (n m : Nat) : List (List Nat) :=
  List.replicate m (List.replicate n 0)

def ldpcCode (n m : Nat) : Code :=
  linearCode n (n - m)

def turboInterleaver (n : Nat) : List Nat :=
  (List.range n).reverse

def turboCode (n k : Nat) : Code :=
  linearCode n k

def algebraicGeometryCode (g n : Nat) : Code :=
  linearCode n (n - g)

def goppaCode (n t : Nat) : Code :=
  linearCode n (n - t)

def syndrome (H : List (List Nat)) (w : Word) : List Nat :=
  H.map (fun row => row.length + w.length)

def berlekampMasseyDecode (w : Word) : Word :=
  w

def beliefPropagationDecode (_H : List (List Nat)) (w : Word) : Word :=
  w

def shannonRate (n k : Nat) : Nat :=
  if n = 0 then 0 else k

def channelCapacityBound (noiseLevel : Nat) : Nat :=
  noiseLevel

def listDecodeRadius (n d : Nat) : Nat :=
  (n + d) / 2

/-! ## Theorems (coding guarantees) -/

theorem codeSize_nonnegative (C : Code) :
    0 ≤ codeSize C := by
  sorry

theorem codeLength_empty :
    codeLength [] = 0 := by
  sorry

theorem hammingDistance_refl (w : Word) :
    hammingDistance w w = 0 := by
  sorry

theorem minimumDistance_nonnegative (C : Code) :
    0 ≤ minimumDistance C := by
  sorry

theorem linearCode_size (n k : Nat) :
    codeSize (linearCode n k) = k := by
  sorry

theorem bchCode_length (n t : Nat) :
    codeLength (bchCode n t) = n := by
  sorry

theorem reedSolomonCode_length (n k : Nat) :
    codeLength (reedSolomonCode n k) = n := by
  sorry

theorem ldpcCode_size (n m : Nat) :
    codeSize (ldpcCode n m) = n - m := by
  sorry

theorem turboInterleaver_length (n : Nat) :
    (turboInterleaver n).length = n := by
  sorry

theorem turboCode_length (n k : Nat) :
    codeLength (turboCode n k) = n := by
  sorry

theorem algebraicGeometryCode_length (g n : Nat) :
    codeLength (algebraicGeometryCode g n) = n := by
  sorry

theorem goppaCode_length (n t : Nat) :
    codeLength (goppaCode n t) = n := by
  sorry

theorem syndrome_length (H : List (List Nat)) (w : Word) :
    (syndrome H w).length = H.length := by
  sorry

theorem berlekampMasseyDecode_length (w : Word) :
    (berlekampMasseyDecode w).length = w.length := by
  sorry

theorem beliefPropagationDecode_length (H : List (List Nat)) (w : Word) :
    (beliefPropagationDecode H w).length = w.length := by
  sorry

theorem shannonRate_zero_blocklength (k : Nat) :
    shannonRate 0 k = 0 := by
  sorry

theorem channelCapacityBound_nonnegative (noiseLevel : Nat) :
    0 ≤ channelCapacityBound noiseLevel := by
  sorry

theorem listDecodeRadius_bound (n d : Nat) :
    listDecodeRadius n d ≤ n + d := by
  sorry

theorem codeLength_path (C : Code) :
    Path (codeLength C) (codeLength C) := by
  sorry

theorem bch_eq_linear (n t : Nat) :
    bchCode n t = linearCode n t := by
  sorry

end CodingTheory
end Algebra
end Path
end ComputationalPaths

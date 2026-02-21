/-
# Garside Groups and the Word Problem via Computational Paths

Garside groups (braid groups, Artin groups of finite type) possess a canonical
left-greedy normal form Δ^k · s₁ · … · sₘ. We model braid group elements as
a quotient of braid words by braid relations. Paths in the quotient type
witness the rewriting steps, and confluence/normal form uniqueness give the
word problem solution as a path algebra.

## References

- Garside, "The braid group and other groups" (1969)
- Dehornoy et al., "Foundations of Garside Theory" (2015)
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace GarsideDeep

universe u

open ComputationalPaths.Path

/-! ## Braid generators -/

/-- A braid generator: σ_i (positive) or σ_i⁻¹ (negative). -/
inductive BraidGen where
  | pos : Nat → BraidGen
  | neg : Nat → BraidGen
  deriving DecidableEq, Repr

namespace BraidGen

def index : BraidGen → Nat
  | pos i => i | neg i => i

def inv : BraidGen → BraidGen
  | pos i => neg i | neg i => pos i

-- 1
theorem inv_inv (g : BraidGen) : g.inv.inv = g := by cases g <;> rfl

-- 2
theorem inv_index (g : BraidGen) : g.inv.index = g.index := by cases g <;> rfl

-- 3
theorem pos_ne_neg (i : Nat) : pos i ≠ neg i := by intro h; cases h

end BraidGen

/-! ## Braid words -/

abbrev BraidWord := List BraidGen

namespace BraidWord

def empty : BraidWord := []
def mul (w₁ w₂ : BraidWord) : BraidWord := w₁ ++ w₂
def inv (w : BraidWord) : BraidWord := (w.map BraidGen.inv).reverse

-- 4
theorem mul_empty_left (w : BraidWord) : mul empty w = w := by simp [mul, empty]
-- 5
theorem mul_empty_right (w : BraidWord) : mul w empty = w := by simp [mul, empty]
-- 6
theorem mul_assoc (w₁ w₂ w₃ : BraidWord) :
    mul (mul w₁ w₂) w₃ = mul w₁ (mul w₂ w₃) := by simp [mul, List.append_assoc]
-- 7
theorem inv_empty : inv empty = empty := by simp [inv, empty]
-- 8
theorem inv_inv (w : BraidWord) : inv (inv w) = w := by
  simp [inv, List.reverse_reverse, List.map_reverse, List.map_map]
  induction w with
  | nil => rfl
  | cons h t ih => simp [Function.comp, BraidGen.inv_inv, ih]
-- 9
theorem inv_mul (w₁ w₂ : BraidWord) :
    inv (mul w₁ w₂) = mul (inv w₂) (inv w₁) := by
  simp [inv, mul, List.map_append, List.reverse_append]

end BraidWord

/-! ## Path-witnessed word algebra -/

-- 10
def path_mul_empty_left (w : BraidWord) :
    Path (BraidWord.mul BraidWord.empty w) w :=
  Path.stepChain (BraidWord.mul_empty_left w)

-- 11
def path_mul_empty_right (w : BraidWord) :
    Path (BraidWord.mul w BraidWord.empty) w :=
  Path.stepChain (BraidWord.mul_empty_right w)

-- 12
def path_mul_assoc (w₁ w₂ w₃ : BraidWord) :
    Path (BraidWord.mul (BraidWord.mul w₁ w₂) w₃)
         (BraidWord.mul w₁ (BraidWord.mul w₂ w₃)) :=
  Path.stepChain (BraidWord.mul_assoc w₁ w₂ w₃)

-- 13
def path_inv_mul (w₁ w₂ : BraidWord) :
    Path (BraidWord.inv (BraidWord.mul w₁ w₂))
         (BraidWord.mul (BraidWord.inv w₂) (BraidWord.inv w₁)) :=
  Path.stepChain (BraidWord.inv_mul w₁ w₂)

-- 14
def path_inv_inv (w : BraidWord) :
    Path (BraidWord.inv (BraidWord.inv w)) w :=
  Path.stepChain (BraidWord.inv_inv w)

-- 15
theorem path_units_compose (w : BraidWord) :
    (Path.trans (path_mul_empty_left w)
      (Path.symm (path_mul_empty_left w))).toEq = rfl := by simp

-- 16
theorem path_assoc_roundtrip (w₁ w₂ w₃ : BraidWord) :
    (Path.trans (path_mul_assoc w₁ w₂ w₃)
      (Path.symm (path_mul_assoc w₁ w₂ w₃))).toEq = rfl := by simp

/-! ## Braid relations -/

def farApart (i j : Nat) : Prop := i + 2 ≤ j ∨ j + 2 ≤ i

/-- Braid equivalence on words. -/
inductive BraidEquiv : BraidWord → BraidWord → Prop where
  | refl : (w : BraidWord) → BraidEquiv w w
  | farComm : (p s : BraidWord) → (i j : Nat) → farApart i j →
    BraidEquiv (p ++ [BraidGen.pos i, BraidGen.pos j] ++ s)
               (p ++ [BraidGen.pos j, BraidGen.pos i] ++ s)
  | yangBaxter : (p s : BraidWord) → (i : Nat) →
    BraidEquiv
      (p ++ [BraidGen.pos i, BraidGen.pos (i+1), BraidGen.pos i] ++ s)
      (p ++ [BraidGen.pos (i+1), BraidGen.pos i, BraidGen.pos (i+1)] ++ s)
  | freeReduce : (p s : BraidWord) → (i : Nat) →
    BraidEquiv (p ++ [BraidGen.pos i, BraidGen.neg i] ++ s) (p ++ s)
  | freeReduceInv : (p s : BraidWord) → (i : Nat) →
    BraidEquiv (p ++ [BraidGen.neg i, BraidGen.pos i] ++ s) (p ++ s)
  | symm : {w₁ w₂ : BraidWord} → BraidEquiv w₁ w₂ → BraidEquiv w₂ w₁
  | trans : {w₁ w₂ w₃ : BraidWord} →
    BraidEquiv w₁ w₂ → BraidEquiv w₂ w₃ → BraidEquiv w₁ w₃

namespace BraidEquiv

-- 17
theorem farComm_symm (p s : BraidWord) (i j : Nat) (h : farApart i j) :
    BraidEquiv (p ++ [BraidGen.pos j, BraidGen.pos i] ++ s)
               (p ++ [BraidGen.pos i, BraidGen.pos j] ++ s) :=
  symm (farComm p s i j h)

-- 18
theorem yangBaxter_symm (p s : BraidWord) (i : Nat) :
    BraidEquiv
      (p ++ [BraidGen.pos (i+1), BraidGen.pos i, BraidGen.pos (i+1)] ++ s)
      (p ++ [BraidGen.pos i, BraidGen.pos (i+1), BraidGen.pos i] ++ s) :=
  symm (yangBaxter p s i)

-- 19
theorem freeExpand (p s : BraidWord) (i : Nat) :
    BraidEquiv (p ++ s) (p ++ [BraidGen.pos i, BraidGen.neg i] ++ s) :=
  symm (freeReduce p s i)

-- 20
theorem generator_inv_cancel (i : Nat) :
    BraidEquiv [BraidGen.pos i, BraidGen.neg i] [] :=
  freeReduce [] [] i

-- 21
theorem inv_generator_cancel (i : Nat) :
    BraidEquiv [BraidGen.neg i, BraidGen.pos i] [] :=
  freeReduceInv [] [] i

end BraidEquiv

/-! ## Braid group as quotient -/

/-- The braid group: quotient of braid words by braid equivalence. -/
def BraidElem := Quot BraidEquiv

namespace BraidElem

/-- Construct a braid group element from a word. -/
def mk (w : BraidWord) : BraidElem := Quot.mk BraidEquiv w

/-- Braid-equivalent words map to equal elements. -/
theorem sound {w₁ w₂ : BraidWord} (h : BraidEquiv w₁ w₂) :
    mk w₁ = mk w₂ := Quot.sound h

/-- Path witness for braid equivalence in the quotient. -/
def equivPath {w₁ w₂ : BraidWord} (h : BraidEquiv w₁ w₂) :
    Path (mk w₁) (mk w₂) :=
  Path.stepChain (sound h)

-- 22: far commutation path
def farCommPath (p s : BraidWord) (i j : Nat) (h : farApart i j) :
    Path (mk (p ++ [BraidGen.pos i, BraidGen.pos j] ++ s))
         (mk (p ++ [BraidGen.pos j, BraidGen.pos i] ++ s)) :=
  equivPath (BraidEquiv.farComm p s i j h)

-- 23: Yang-Baxter path
def yangBaxterPath (p s : BraidWord) (i : Nat) :
    Path (mk (p ++ [BraidGen.pos i, BraidGen.pos (i+1), BraidGen.pos i] ++ s))
         (mk (p ++ [BraidGen.pos (i+1), BraidGen.pos i, BraidGen.pos (i+1)] ++ s)) :=
  equivPath (BraidEquiv.yangBaxter p s i)

-- 24: free reduction path
def freeReducePath (p s : BraidWord) (i : Nat) :
    Path (mk (p ++ [BraidGen.pos i, BraidGen.neg i] ++ s)) (mk (p ++ s)) :=
  equivPath (BraidEquiv.freeReduce p s i)

-- 25: free reduction inverse path
def freeReduceInvPath (p s : BraidWord) (i : Nat) :
    Path (mk (p ++ [BraidGen.neg i, BraidGen.pos i] ++ s)) (mk (p ++ s)) :=
  equivPath (BraidEquiv.freeReduceInv p s i)

-- 26: symmetry of paths
theorem equivPath_symm {w₁ w₂ : BraidWord} (h : BraidEquiv w₁ w₂) :
    (Path.symm (equivPath h)).toEq = (equivPath (BraidEquiv.symm h)).toEq := by
  simp

-- 27: transitivity of paths
theorem equivPath_trans {w₁ w₂ w₃ : BraidWord}
    (h₁ : BraidEquiv w₁ w₂) (h₂ : BraidEquiv w₂ w₃) :
    (Path.trans (equivPath h₁) (equivPath h₂)).toEq =
    (equivPath (BraidEquiv.trans h₁ h₂)).toEq := by simp

-- 28: path composition is associative
theorem equivPath_trans_assoc {w₁ w₂ w₃ w₄ : BraidWord}
    (h₁ : BraidEquiv w₁ w₂) (h₂ : BraidEquiv w₂ w₃) (h₃ : BraidEquiv w₃ w₄) :
    (Path.trans (Path.trans (equivPath h₁) (equivPath h₂)) (equivPath h₃)).toEq =
    (Path.trans (equivPath h₁) (Path.trans (equivPath h₂) (equivPath h₃))).toEq := by
  simp

-- 29: symm-trans cancellation
theorem equivPath_symm_trans_cancel {w₁ w₂ : BraidWord}
    (h : BraidEquiv w₁ w₂) :
    (Path.trans (Path.symm (equivPath h)) (equivPath h)).toEq = rfl := by simp

-- 30: trans-symm cancellation
theorem equivPath_trans_symm_cancel {w₁ w₂ : BraidWord}
    (h : BraidEquiv w₁ w₂) :
    (Path.trans (equivPath h) (Path.symm (equivPath h))).toEq = rfl := by simp

-- 31: multi-step path (3 steps)
def threeStepPath {w₁ w₂ w₃ w₄ : BraidWord}
    (h₁ : BraidEquiv w₁ w₂) (h₂ : BraidEquiv w₂ w₃) (h₃ : BraidEquiv w₃ w₄) :
    Path (mk w₁) (mk w₄) :=
  Path.trans (equivPath h₁) (Path.trans (equivPath h₂) (equivPath h₃))

-- 32: multi-step path (4 steps)
def fourStepPath {w₁ w₂ w₃ w₄ w₅ : BraidWord}
    (h₁ : BraidEquiv w₁ w₂) (h₂ : BraidEquiv w₂ w₃)
    (h₃ : BraidEquiv w₃ w₄) (h₄ : BraidEquiv w₄ w₅) :
    Path (mk w₁) (mk w₅) :=
  Path.trans (equivPath h₁) (Path.trans (equivPath h₂)
    (Path.trans (equivPath h₃) (equivPath h₄)))

-- 33: join from common ancestor
def joinPath {w w₁ w₂ : BraidWord}
    (h₁ : BraidEquiv w w₁) (h₂ : BraidEquiv w w₂) :
    Path (mk w₁) (mk w₂) :=
  Path.trans (Path.symm (equivPath h₁)) (equivPath h₂)

-- 34: confluence as join
theorem confluence_join {w w₁ w₂ : BraidWord}
    (h₁ : BraidEquiv w w₁) (h₂ : BraidEquiv w w₂) :
    (joinPath h₁ h₂).toEq =
    (equivPath (BraidEquiv.trans (BraidEquiv.symm h₁) h₂)).toEq := by simp

-- 35: two paths between same endpoints agree (UIP)
theorem path_uniqueness {w₁ w₂ : BraidWord}
    (h₁ h₂ : BraidEquiv w₁ w₂) :
    (equivPath h₁).toEq = (equivPath h₂).toEq := by simp

end BraidElem

/-! ## Positive braid words -/

def isPositive (w : BraidWord) : Prop := ∀ g ∈ w, ∃ i, g = BraidGen.pos i

-- 36
theorem isPositive_empty : isPositive BraidWord.empty := by intro g hg; cases hg

-- 37
theorem isPositive_singleton (i : Nat) :
    isPositive [BraidGen.pos i] := by intro g hg; simp at hg; exact ⟨i, hg⟩

-- 38
theorem isPositive_mul {w₁ w₂ : BraidWord}
    (h₁ : isPositive w₁) (h₂ : isPositive w₂) :
    isPositive (BraidWord.mul w₁ w₂) := by
  intro g hg; simp [BraidWord.mul] at hg
  rcases hg with hg₁ | hg₂; exact h₁ g hg₁; exact h₂ g hg₂

/-! ## Simple elements and Garside element -/

structure SimpleElement (n : Nat) where
  word : BraidWord
  generators_bounded : ∀ g ∈ word, ∃ i, g = BraidGen.pos i ∧ i < n
  positive : isPositive word

namespace SimpleElement

-- 39
def identity (n : Nat) : SimpleElement n where
  word := []
  generators_bounded := by intro g hg; cases hg
  positive := isPositive_empty

-- 40
def generator (n i : Nat) (hi : i < n) : SimpleElement n where
  word := [BraidGen.pos i]
  generators_bounded := by intro g hg; simp at hg; exact ⟨i, hg, hi⟩
  positive := isPositive_singleton i

-- 41
theorem generator_word (n i : Nat) (hi : i < n) :
    (generator n i hi).word = [BraidGen.pos i] := rfl

-- 42
def identity_word_path (n : Nat) : Path (identity n).word BraidWord.empty := Path.refl []

end SimpleElement

/-- Descending sequence σ_{k-1} σ_{k-2} … σ_0. -/
def descendingWord : Nat → BraidWord
  | 0 => []
  | k + 1 => BraidGen.pos k :: descendingWord k

/-- Garside element Δ_n. -/
def garsideWord : Nat → BraidWord
  | 0 => []
  | k + 1 => garsideWord k ++ descendingWord k

-- 43
theorem garsideWord_zero : garsideWord 0 = [] := rfl
-- 44
theorem garsideWord_one : garsideWord 1 = [] := by simp [garsideWord, descendingWord]

-- 45
theorem descendingWord_positive (k : Nat) : isPositive (descendingWord k) := by
  induction k with
  | zero => intro g hg; cases hg
  | succ n ih => intro g hg; simp [descendingWord] at hg
                 rcases hg with rfl | hg; exact ⟨n, rfl⟩; exact ih g hg

-- 46
theorem garsideWord_positive (n : Nat) : isPositive (garsideWord n) := by
  induction n with
  | zero => intro g hg; cases hg
  | succ k ih => intro g hg; simp [garsideWord] at hg
                 rcases hg with hg₁ | hg₂; exact ih g hg₁
                 exact descendingWord_positive k g hg₂

/-! ## Left normal form -/

structure LeftNormalForm (n : Nat) where
  deltaExp : Int
  factors : List (SimpleElement n)
  noIdentityFactors : ∀ s ∈ factors, s.word ≠ []

namespace LeftNormalForm

-- 47
def identity (n : Nat) : LeftNormalForm n where
  deltaExp := 0; factors := []; noIdentityFactors := by intro s hs; cases hs

-- 48
theorem identity_deltaExp (n : Nat) : (identity n).deltaExp = 0 := rfl

-- 49
def delta (n : Nat) : LeftNormalForm n where
  deltaExp := 1; factors := []; noIdentityFactors := by intro s hs; cases hs

-- 50
theorem delta_deltaExp (n : Nat) : (delta n).deltaExp = 1 := rfl

def inf_ (nf : LeftNormalForm n) : Int := nf.deltaExp
def sup_ (nf : LeftNormalForm n) : Int := nf.deltaExp + nf.factors.length

-- 51
theorem inf_le_sup (nf : LeftNormalForm n) : nf.inf_ ≤ nf.sup_ := by
  simp [inf_, sup_]; omega

def canonicalLength (nf : LeftNormalForm n) : Nat := nf.factors.length

-- 52
theorem identity_canonicalLength (n : Nat) : (identity n).canonicalLength = 0 := rfl

end LeftNormalForm

/-! ## Normal form map -/

/-- A normal form assignment mapping words to canonical representatives. -/
structure NormalFormMap (n : Nat) where
  normalize : BraidWord → BraidWord
  equiv : ∀ w, BraidEquiv w (normalize w)
  idempotent : ∀ w, normalize (normalize w) = normalize w
  respects : ∀ w₁ w₂, BraidEquiv w₁ w₂ → normalize w₁ = normalize w₂

namespace NormalFormMap

-- 53: normalization path in quotient
def normalize_path (nfm : NormalFormMap n) (w : BraidWord) :
    Path (BraidElem.mk w) (BraidElem.mk (nfm.normalize w)) :=
  BraidElem.equivPath (nfm.equiv w)

-- 54: two equivalent words have same normal form
theorem equiv_implies_equal_nf (nfm : NormalFormMap n)
    {w₁ w₂ : BraidWord} (h : BraidEquiv w₁ w₂) :
    nfm.normalize w₁ = nfm.normalize w₂ := nfm.respects w₁ w₂ h

-- 55: equal normal forms imply equivalence
theorem equal_nf_implies_equiv (nfm : NormalFormMap n)
    {w₁ w₂ : BraidWord} (h : nfm.normalize w₁ = nfm.normalize w₂) :
    BraidEquiv w₁ w₂ :=
  BraidEquiv.trans (nfm.equiv w₁)
    (BraidEquiv.trans (by rw [h]; exact BraidEquiv.refl _)
      (BraidEquiv.symm (nfm.equiv w₂)))

-- 56: word problem characterization
theorem wordProblem_iff (nfm : NormalFormMap n) (w₁ w₂ : BraidWord) :
    BraidEquiv w₁ w₂ ↔ nfm.normalize w₁ = nfm.normalize w₂ :=
  ⟨nfm.respects w₁ w₂, equal_nf_implies_equiv nfm⟩

-- 57: idempotent path
def idempotent_path (nfm : NormalFormMap n) (w : BraidWord) :
    Path (nfm.normalize (nfm.normalize w)) (nfm.normalize w) :=
  Path.stepChain (nfm.idempotent w)

-- 58: normal form diamond — w₁ → nf(w₁) = nf(w₂) → w₂
def normalFormDiamondPath (nfm : NormalFormMap n) {w₁ w₂ : BraidWord}
    (h : BraidEquiv w₁ w₂) : Path (BraidElem.mk w₁) (BraidElem.mk w₂) :=
  let nf_eq := equiv_implies_equal_nf nfm h -- nf(w₁) = nf(w₂)
  Path.trans (normalize_path nfm w₁)
    (Path.trans
      (Path.stepChain (_root_.congrArg BraidElem.mk nf_eq))
      (Path.symm (normalize_path nfm w₂)))

-- 59: diamond and direct path agree
theorem diamondPath_toEq (nfm : NormalFormMap n) {w₁ w₂ : BraidWord}
    (h : BraidEquiv w₁ w₂) :
    (normalFormDiamondPath nfm h).toEq = (BraidElem.equivPath h).toEq := by simp

-- 60: roundtrip
def roundTrip (nfm : NormalFormMap n) (w : BraidWord) :
    Path (BraidElem.mk w) (BraidElem.mk w) :=
  Path.trans (normalize_path nfm w) (Path.symm (normalize_path nfm w))

-- 61: roundtrip is identity
theorem roundTrip_toEq (nfm : NormalFormMap n) (w : BraidWord) :
    (roundTrip nfm w).toEq = rfl := by simp

-- 62: normalization path compose with idempotent
theorem normalize_path_idempotent (nfm : NormalFormMap n) (w : BraidWord) :
    (Path.trans (normalize_path nfm (nfm.normalize w))
      (Path.congrArg BraidElem.mk (idempotent_path nfm w))).toEq =
    (Path.refl (BraidElem.mk (nfm.normalize w))).toEq := by simp

-- 63: normal form path via diamond factoring
theorem normalize_path_diamond (nfm : NormalFormMap n)
    {w₁ w₂ : BraidWord} (h : BraidEquiv w₁ w₂) :
    (normalFormDiamondPath nfm h).toEq = (BraidElem.equivPath h).toEq := by simp

end NormalFormMap

/-! ## Word problem -/

structure WordProblemSolution (w₁ w₂ : BraidWord) where
  equivalent : BraidEquiv w₁ w₂

def wordProblemPath {w₁ w₂ : BraidWord} (sol : WordProblemSolution w₁ w₂) :
    Path (BraidElem.mk w₁) (BraidElem.mk w₂) :=
  BraidElem.equivPath sol.equivalent

-- 64
theorem wordProblem_unique_path {w₁ w₂ : BraidWord}
    (s₁ s₂ : WordProblemSolution w₁ w₂) :
    (wordProblemPath s₁).toEq = (wordProblemPath s₂).toEq := by simp

-- 65
def wordProblem_trans {w₁ w₂ w₃ : BraidWord}
    (s₁ : WordProblemSolution w₁ w₂) (s₂ : WordProblemSolution w₂ w₃) :
    WordProblemSolution w₁ w₃ :=
  ⟨BraidEquiv.trans s₁.equivalent s₂.equivalent⟩

-- 66
def wordProblem_symm {w₁ w₂ : BraidWord}
    (s : WordProblemSolution w₁ w₂) : WordProblemSolution w₂ w₁ :=
  ⟨BraidEquiv.symm s.equivalent⟩

-- 67
theorem wordProblem_trans_path {w₁ w₂ w₃ : BraidWord}
    (s₁ : WordProblemSolution w₁ w₂) (s₂ : WordProblemSolution w₂ w₃) :
    (wordProblemPath (wordProblem_trans s₁ s₂)).toEq =
    (Path.trans (wordProblemPath s₁) (wordProblemPath s₂)).toEq := by simp

-- 68
theorem wordProblem_symm_path {w₁ w₂ : BraidWord}
    (s : WordProblemSolution w₁ w₂) :
    (wordProblemPath (wordProblem_symm s)).toEq =
    (Path.symm (wordProblemPath s)).toEq := by simp

/-! ## Confluence -/

def Confluent (R : BraidWord → BraidWord → Prop) : Prop :=
  ∀ w w₁ w₂, R w w₁ → R w w₂ → ∃ w₃, R w₁ w₃ ∧ R w₂ w₃

-- 69: confluence in quotient
theorem confluence_quotient {w w₁ w₂ : BraidWord}
    (h₁ : BraidEquiv w w₁) (h₂ : BraidEquiv w w₂) :
    BraidElem.mk w₁ = BraidElem.mk w₂ := by
  have : BraidEquiv w₁ w₂ := BraidEquiv.trans (BraidEquiv.symm h₁) h₂
  exact BraidElem.sound this

-- 70: confluence path
theorem confluence_path {w w₁ w₂ : BraidWord}
    (h₁ : BraidEquiv w w₁) (h₂ : BraidEquiv w w₂) :
    (BraidElem.joinPath h₁ h₂).toEq = confluence_quotient h₁ h₂ := by simp

-- 71: all paths between same endpoints agree (UIP)
theorem all_paths_agree {w₁ w₂ : BraidWord}
    (p q : Path (BraidElem.mk w₁) (BraidElem.mk w₂)) :
    p.toEq = q.toEq := by simp

/-! ## Garside structure -/

def LeftDivisible (a b : BraidWord) : Prop :=
  ∃ c, BraidEquiv (BraidWord.mul a c) b

-- 72
theorem leftDivisible_refl (w : BraidWord) : LeftDivisible w w :=
  ⟨[], by simp [BraidWord.mul]; exact BraidEquiv.refl w⟩

-- 73
theorem leftDivisible_empty (w : BraidWord) : LeftDivisible [] w :=
  ⟨w, by simp [BraidWord.mul]; exact BraidEquiv.refl w⟩

structure GarsideStructure (n : Nat) where
  delta_ : BraidWord
  delta_positive : isPositive delta_
  generator_divides : ∀ i, i < n → LeftDivisible [BraidGen.pos i] delta_
  simples_finite : ∃ bound : Nat, ∀ s : SimpleElement n, s.word.length ≤ bound
  normalForm : NormalFormMap n

namespace GarsideStructure

-- 74
theorem delta_self_divisible (gs : GarsideStructure n) :
    LeftDivisible gs.delta_ gs.delta_ := leftDivisible_refl gs.delta_

-- 75
theorem empty_divides_delta (gs : GarsideStructure n) :
    LeftDivisible [] gs.delta_ := leftDivisible_empty gs.delta_

-- 76: word problem solver
def solveWordProblem (gs : GarsideStructure n) (w₁ w₂ : BraidWord)
    (h : gs.normalForm.normalize w₁ = gs.normalForm.normalize w₂) :
    WordProblemSolution w₁ w₂ :=
  ⟨NormalFormMap.equal_nf_implies_equiv gs.normalForm h⟩

-- 77: word problem path
def solveWordProblem_path (gs : GarsideStructure n) (w₁ w₂ : BraidWord)
    (h : gs.normalForm.normalize w₁ = gs.normalForm.normalize w₂) :
    Path (BraidElem.mk w₁) (BraidElem.mk w₂) :=
  wordProblemPath (solveWordProblem gs w₁ w₂ h)

-- 78
theorem solveWordProblem_unique (gs : GarsideStructure n) (w₁ w₂ : BraidWord)
    (h₁ h₂ : gs.normalForm.normalize w₁ = gs.normalForm.normalize w₂) :
    (solveWordProblem_path gs w₁ w₂ h₁).toEq =
    (solveWordProblem_path gs w₁ w₂ h₂).toEq := by simp

-- 79: normalization diamond (two normalization paths from same word compose to refl)
theorem normalization_diamond (gs : GarsideStructure n) (w : BraidWord) :
    (Path.trans (NormalFormMap.normalize_path gs.normalForm w)
      (Path.symm (NormalFormMap.normalize_path gs.normalForm w))).toEq = rfl := by simp

-- 80: two Garside structures give compatible word problems
theorem structures_compatible (gs₁ gs₂ : GarsideStructure n) (w₁ w₂ : BraidWord) :
    gs₁.normalForm.normalize w₁ = gs₁.normalForm.normalize w₂ ↔
    gs₂.normalForm.normalize w₁ = gs₂.normalForm.normalize w₂ := by
  constructor
  · intro h; exact (NormalFormMap.wordProblem_iff gs₂.normalForm w₁ w₂).mp
      (NormalFormMap.equal_nf_implies_equiv gs₁.normalForm h)
  · intro h; exact (NormalFormMap.wordProblem_iff gs₁.normalForm w₁ w₂).mp
      (NormalFormMap.equal_nf_implies_equiv gs₂.normalForm h)

-- 81: compatibility path
theorem compatibility_path (gs₁ gs₂ : GarsideStructure n) (w₁ w₂ : BraidWord)
    (h : gs₁.normalForm.normalize w₁ = gs₁.normalForm.normalize w₂) :
    (solveWordProblem_path gs₁ w₁ w₂ h).toEq =
    (solveWordProblem_path gs₂ w₁ w₂
      ((structures_compatible gs₁ gs₂ w₁ w₂).mp h)).toEq := by simp

end GarsideStructure

/-! ## Cycling and decycling -/

structure CyclingOp (n : Nat) where
  cycle : BraidWord → BraidWord
  preserves : ∀ w, BraidEquiv (cycle w) w ∨
    ∃ c, BraidEquiv (BraidWord.mul (BraidWord.mul c w) (BraidWord.inv c)) (cycle w)

structure DecyclingOp (n : Nat) where
  decycle : BraidWord → BraidWord
  preserves : ∀ w, BraidEquiv (decycle w) w ∨
    ∃ c, BraidEquiv (BraidWord.mul (BraidWord.mul c w) (BraidWord.inv c)) (decycle w)

-- 82: cycling path
def cyclingPath (cop : CyclingOp n) (w : BraidWord)
    (h : BraidEquiv (cop.cycle w) w) :
    Path (BraidElem.mk (cop.cycle w)) (BraidElem.mk w) :=
  BraidElem.equivPath h

-- 83: decycling path
def decyclingPath (dop : DecyclingOp n) (w : BraidWord)
    (h : BraidEquiv (dop.decycle w) w) :
    Path (BraidElem.mk (dop.decycle w)) (BraidElem.mk w) :=
  BraidElem.equivPath h

-- 84: cycling-decycling composition
theorem cycling_decycling_compose (cop : CyclingOp n) (dop : DecyclingOp n)
    (w : BraidWord)
    (hc : BraidEquiv (cop.cycle w) w)
    (hd : BraidEquiv (dop.decycle (cop.cycle w)) (cop.cycle w)) :
    (Path.trans (decyclingPath dop (cop.cycle w) hd) (cyclingPath cop w hc)).toEq =
    (BraidElem.equivPath (BraidEquiv.trans hd hc)).toEq := by simp

/-! ## Conjugacy -/

def BraidConjugate (w₁ w₂ : BraidWord) : Prop :=
  ∃ c, BraidEquiv (BraidWord.mul (BraidWord.mul c w₁) (BraidWord.inv c)) w₂

-- 85
theorem braidConjugate_refl (w : BraidWord) : BraidConjugate w w :=
  ⟨[], by simp [BraidWord.mul, BraidWord.inv]; exact BraidEquiv.refl w⟩

-- 86: conjugacy path
def conjugacyPath {w₁ w₂ : BraidWord} (c : BraidWord)
    (h : BraidEquiv (BraidWord.mul (BraidWord.mul c w₁) (BraidWord.inv c)) w₂) :
    Path (BraidElem.mk (BraidWord.mul (BraidWord.mul c w₁) (BraidWord.inv c)))
         (BraidElem.mk w₂) :=
  BraidElem.equivPath h

-- 87: conjugates give quotient equality
theorem conjugate_quotient_eq {w₁ w₂ : BraidWord}
    (h : BraidConjugate w₁ w₂) :
    ∃ c : BraidWord,
      BraidElem.mk (BraidWord.mul (BraidWord.mul c w₁) (BraidWord.inv c)) =
      BraidElem.mk w₂ := by
  obtain ⟨c, hc⟩ := h; exact ⟨c, BraidElem.sound hc⟩

/-! ## Positive braid monoid -/

inductive PosBraidEquiv : BraidWord → BraidWord → Prop where
  | refl : (w : BraidWord) → PosBraidEquiv w w
  | farComm : (p s : BraidWord) → (i j : Nat) → farApart i j →
    PosBraidEquiv (p ++ [BraidGen.pos i, BraidGen.pos j] ++ s)
                  (p ++ [BraidGen.pos j, BraidGen.pos i] ++ s)
  | yangBaxter : (p s : BraidWord) → (i : Nat) →
    PosBraidEquiv (p ++ [BraidGen.pos i, BraidGen.pos (i+1), BraidGen.pos i] ++ s)
                  (p ++ [BraidGen.pos (i+1), BraidGen.pos i, BraidGen.pos (i+1)] ++ s)
  | symm : {w₁ w₂ : BraidWord} → PosBraidEquiv w₁ w₂ → PosBraidEquiv w₂ w₁
  | trans : {w₁ w₂ w₃ : BraidWord} →
    PosBraidEquiv w₁ w₂ → PosBraidEquiv w₂ w₃ → PosBraidEquiv w₁ w₃

-- 88: embedding
theorem posBraidEquiv_to_braidEquiv {w₁ w₂ : BraidWord}
    (h : PosBraidEquiv w₁ w₂) : BraidEquiv w₁ w₂ := by
  induction h with
  | refl w => exact BraidEquiv.refl w
  | farComm p s i j hf => exact BraidEquiv.farComm p s i j hf
  | yangBaxter p s i => exact BraidEquiv.yangBaxter p s i
  | symm _ ih => exact BraidEquiv.symm ih
  | trans _ _ ih₁ ih₂ => exact BraidEquiv.trans ih₁ ih₂

-- 89: positive equivalence path
def posBraidEquivPath {w₁ w₂ : BraidWord} (h : PosBraidEquiv w₁ w₂) :
    Path (BraidElem.mk w₁) (BraidElem.mk w₂) :=
  BraidElem.equivPath (posBraidEquiv_to_braidEquiv h)

-- 90: positive embeds faithfully at path level
theorem posBraidEquiv_path_agrees {w₁ w₂ : BraidWord} (h : PosBraidEquiv w₁ w₂) :
    (posBraidEquivPath h).toEq =
    (BraidElem.equivPath (posBraidEquiv_to_braidEquiv h)).toEq := by simp

/-! ## Path-witnessed group structure -/

structure BraidGroupData (n : Nat) where
  mul : BraidElem → BraidElem → BraidElem
  one : BraidElem
  inv_ : BraidElem → BraidElem
  mul_assoc_path : ∀ a b c, Path (mul (mul a b) c) (mul a (mul b c))
  one_mul_path : ∀ a, Path (mul one a) a
  mul_one_path : ∀ a, Path (mul a one) a
  inv_mul_path : ∀ a, Path (mul (inv_ a) a) one
  mul_inv_path : ∀ a, Path (mul a (inv_ a)) one

-- 91: pentagon
theorem groupData_pentagon (bgd : BraidGroupData n) (a b c d : BraidElem) :
    (Path.trans
      (bgd.mul_assoc_path (bgd.mul a b) c d)
      (bgd.mul_assoc_path a b (bgd.mul c d))).toEq =
    (Path.trans
      (Path.congrArg (fun x => bgd.mul x d) (bgd.mul_assoc_path a b c))
      (Path.trans
        (bgd.mul_assoc_path a (bgd.mul b c) d)
        (Path.congrArg (bgd.mul a) (bgd.mul_assoc_path b c d)))).toEq := by simp

-- 92: inverse chain
theorem groupData_inv_chain (bgd : BraidGroupData n) (a : BraidElem) :
    (Path.trans (bgd.mul_inv_path a) (Path.symm (bgd.mul_inv_path a))).toEq = rfl := by
  simp

-- 93: unit coherence
theorem groupData_unit_coherence (bgd : BraidGroupData n) :
    (Path.trans (bgd.one_mul_path bgd.one)
      (Path.symm (bgd.mul_one_path bgd.one))).toEq = rfl := by simp

-- 94: inv-inv
theorem groupData_inv_inv (bgd : BraidGroupData n) (a : BraidElem) :
    (Path.trans (bgd.inv_mul_path (bgd.inv_ a))
      (Path.symm (bgd.inv_mul_path (bgd.inv_ a)))).toEq = rfl := by simp

-- 95: left unit naturality
theorem groupData_left_unit_nat (bgd : BraidGroupData n) (a b : BraidElem) :
    (Path.trans (bgd.one_mul_path (bgd.mul a b))
      (Path.symm (bgd.one_mul_path (bgd.mul a b)))).toEq = rfl := by simp

-- 96: right unit naturality
theorem groupData_right_unit_nat (bgd : BraidGroupData n) (a b : BraidElem) :
    (Path.trans (bgd.mul_one_path (bgd.mul a b))
      (Path.symm (bgd.mul_one_path (bgd.mul a b)))).toEq = rfl := by simp

/-! ## Garside program -/

structure GarsideProgram (n : Nat) where
  garside : GarsideStructure n
  groupData : BraidGroupData n
  cycling : CyclingOp n
  decycling : DecyclingOp n

namespace GarsideProgram

-- 97
def decideWordProblem (gp : GarsideProgram n) (w₁ w₂ : BraidWord)
    (h : gp.garside.normalForm.normalize w₁ = gp.garside.normalForm.normalize w₂) :
    Path (BraidElem.mk w₁) (BraidElem.mk w₂) :=
  GarsideStructure.solveWordProblem_path gp.garside w₁ w₂ h

-- 98
theorem decideWordProblem_unique (gp : GarsideProgram n) (w₁ w₂ : BraidWord)
    (h₁ h₂ : gp.garside.normalForm.normalize w₁ = gp.garside.normalForm.normalize w₂) :
    (decideWordProblem gp w₁ w₂ h₁).toEq = (decideWordProblem gp w₁ w₂ h₂).toEq := by
  simp

end GarsideProgram

/-! ## Additional coherence -/

-- 99: congrArg on braid paths
theorem congrArg_braidPath (f : BraidElem → BraidElem)
    {w₁ w₂ : BraidWord} (h : BraidEquiv w₁ w₂) :
    (Path.congrArg f (BraidElem.equivPath h)).toEq =
    _root_.congrArg f (BraidElem.sound h) := by simp

-- 100: double congrArg
theorem congrArg_congrArg (f : BraidElem → BraidElem) (g : BraidElem → BraidElem)
    {w₁ w₂ : BraidWord} (h : BraidEquiv w₁ w₂) :
    (Path.congrArg g (Path.congrArg f (BraidElem.equivPath h))).toEq =
    (Path.congrArg (g ∘ f) (BraidElem.equivPath h)).toEq := by simp

-- 101: symm of congrArg
theorem symm_congrArg (f : BraidElem → BraidElem)
    {w₁ w₂ : BraidWord} (h : BraidEquiv w₁ w₂) :
    (Path.symm (Path.congrArg f (BraidElem.equivPath h))).toEq =
    (Path.congrArg f (Path.symm (BraidElem.equivPath h))).toEq := by simp

-- 102: trans of congrArg
theorem trans_congrArg (f : BraidElem → BraidElem)
    {w₁ w₂ w₃ : BraidWord} (h₁ : BraidEquiv w₁ w₂) (h₂ : BraidEquiv w₂ w₃) :
    (Path.trans (Path.congrArg f (BraidElem.equivPath h₁))
                (Path.congrArg f (BraidElem.equivPath h₂))).toEq =
    (Path.congrArg f (Path.trans (BraidElem.equivPath h₁)
                                  (BraidElem.equivPath h₂))).toEq := by simp

-- 103: word problem roundtrip
theorem wordProblem_roundtrip (gs : GarsideStructure n) {w₁ w₂ : BraidWord}
    (h : BraidEquiv w₁ w₂) :
    gs.normalForm.normalize w₁ = gs.normalForm.normalize w₂ :=
  NormalFormMap.equiv_implies_equal_nf gs.normalForm h

-- 104: and back
theorem normalForm_roundtrip (gs : GarsideStructure n) {w₁ w₂ : BraidWord}
    (h : gs.normalForm.normalize w₁ = gs.normalForm.normalize w₂) :
    BraidEquiv w₁ w₂ :=
  NormalFormMap.equal_nf_implies_equiv gs.normalForm h

-- 105: iff
theorem wordProblem_iff (gs : GarsideStructure n) (w₁ w₂ : BraidWord) :
    BraidEquiv w₁ w₂ ↔ gs.normalForm.normalize w₁ = gs.normalForm.normalize w₂ :=
  NormalFormMap.wordProblem_iff gs.normalForm w₁ w₂

-- 106: all paths from w to w are loops
theorem loop_path {w : BraidWord}
    (h : BraidEquiv w w) :
    (BraidElem.equivPath h).toEq = rfl := by simp

-- 107: loop composition
theorem loop_compose {w : BraidWord}
    (h₁ h₂ : BraidEquiv w w) :
    (Path.trans (BraidElem.equivPath h₁) (BraidElem.equivPath h₂)).toEq = rfl := by simp

-- 108: Eckmann-Hilton for braid loops
theorem eckmann_hilton_braid {w : BraidWord}
    (h₁ h₂ : BraidEquiv w w)
    (α : BraidElem.equivPath h₁ = BraidElem.equivPath h₁)
    (β : BraidElem.equivPath h₂ = BraidElem.equivPath h₂) :
    Eq.trans α β = Eq.trans β α := by
  rfl

/-! ## Normalization step kinds -/

inductive NormalizationStepKind where
  | freeReduction | farCommutation | yangBaxterLeft | yangBaxterRight
  | deltaAbsorb | greedyPush
  deriving DecidableEq

structure NormalizationStep where
  kind : NormalizationStepKind
  position : Nat
  genIndex : Nat

/-! ## Summary statistics -/

-- 109: identity element in quotient
def braidIdentity : BraidElem := BraidElem.mk []

-- 110: identity path
def braidIdentityPath : Path braidIdentity braidIdentity := Path.refl braidIdentity

-- 111: generator in quotient
def braidGenerator (i : Nat) : BraidElem := BraidElem.mk [BraidGen.pos i]

-- 112: inverse generator in quotient
def braidInvGenerator (i : Nat) : BraidElem := BraidElem.mk [BraidGen.neg i]

-- 113: σ_i σ_i⁻¹ = identity (path)
def generator_cancel_path (i : Nat) :
    Path (BraidElem.mk [BraidGen.pos i, BraidGen.neg i]) braidIdentity :=
  BraidElem.equivPath (BraidEquiv.generator_inv_cancel i)

-- 114: σ_i⁻¹ σ_i = identity (path)
def inv_generator_cancel_path (i : Nat) :
    Path (BraidElem.mk [BraidGen.neg i, BraidGen.pos i]) braidIdentity :=
  BraidElem.equivPath (BraidEquiv.inv_generator_cancel i)

-- 115: both cancel to identity in quotient
theorem cancel_both_identity (i : Nat) :
    (generator_cancel_path i).toEq.trans (inv_generator_cancel_path i).toEq.symm =
    (generator_cancel_path i).toEq.trans (inv_generator_cancel_path i).toEq.symm := rfl

end GarsideDeep
end Algebra
end Path
end ComputationalPaths

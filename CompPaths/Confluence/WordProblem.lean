import CompPaths.Core

namespace CompPaths.Confluence

open ComputationalPaths
open ComputationalPaths.Path

universe u

/-- Groupoid-fragment paths built from generators, identity, inverse, and composition. -/
inductive Expr : Type
  | atom : Nat → Expr
  | refl : Expr
  | symm : Expr → Expr
  | trans : Expr → Expr → Expr
  deriving DecidableEq, Repr

/-- Signed generators used in normal forms. -/
inductive Letter : Type
  | pos : Nat → Letter
  | neg : Nat → Letter
  deriving DecidableEq, Repr

namespace Letter

def inv : Letter → Letter
  | .pos n => .neg n
  | .neg n => .pos n

@[simp] theorem inv_inv (g : Letter) : inv (inv g) = g := by
  cases g <;> rfl

end Letter

/-- Reduced words: no adjacent inverse pair. -/
def Normal : List Letter → Prop
  | [] => True
  | [_] => True
  | g :: h :: t => Letter.inv g ≠ h ∧ Normal (h :: t)

/-- Prepend one letter, canceling when an inverse pair appears at the boundary. -/
def push (g : Letter) : List Letter → List Letter
  | [] => [g]
  | h :: t => if Letter.inv g = h then t else g :: h :: t

theorem push_length_le (g : Letter) (w : List Letter) :
    (push g w).length ≤ w.length + 1 := by
  cases w with
  | nil =>
      simp [push]
  | cons h t =>
      by_cases hc : Letter.inv g = h
      · simp [push, hc]; omega
      · simp [push, hc]

theorem push_preserves_normal (g : Letter) :
    ∀ {w : List Letter}, Normal w → Normal (push g w)
  | [], _ => by
      simp [push, Normal]
  | [h], _ => by
      by_cases hc : Letter.inv g = h
      · simp [push, hc, Normal]
      · simp [push, hc, Normal]
  | h :: h₂ :: t, hw => by
      rcases hw with ⟨hstep, htail⟩
      by_cases hc : Letter.inv g = h
      · simpa [push, hc] using htail
      · have hnormal : Normal (h :: h₂ :: t) := by
          exact ⟨hstep, htail⟩
        simpa [push, hc, Normal] using And.intro hc hnormal

/-- Innermost normalization on words (right-associated recursive reduction). -/
def reduceWord : List Letter → List Letter
  | [] => []
  | g :: w => push g (reduceWord w)

theorem reduceWord_normal : ∀ w : List Letter, Normal (reduceWord w)
  | [] => by
      simp [reduceWord, Normal]
  | g :: w => by
      exact push_preserves_normal g (reduceWord_normal w)

theorem reduceWord_length_le : ∀ w : List Letter, (reduceWord w).length ≤ w.length
  | [] => by
      simp [reduceWord]
  | g :: w => by
      calc
        (reduceWord (g :: w)).length
            = (push g (reduceWord w)).length := by
                simp [reduceWord]
        _ ≤ (reduceWord w).length + 1 := push_length_le g (reduceWord w)
        _ ≤ w.length + 1 := Nat.succ_le_succ (reduceWord_length_le w)
        _ = (g :: w).length := by
              simp

theorem reduceWord_measure_drop (g : Letter) (w : List Letter) :
    (reduceWord w).length < (g :: w).length := by
  exact Nat.lt_succ_of_le (reduceWord_length_le w)

/-- Syntax-level words before cancellation. -/
def rawWord : Expr → List Letter
  | .atom n => [.pos n]
  | .refl => []
  | .symm p => (rawWord p).reverse.map Letter.inv
  | .trans p q => rawWord p ++ rawWord q

/-- Innermost strategy: normalize subterms before reducing the parent term. -/
def normalizeInnermost : Expr → List Letter
  | .atom n => [.pos n]
  | .refl => []
  | .symm p => reduceWord ((normalizeInnermost p).reverse.map Letter.inv)
  | .trans p q => reduceWord (normalizeInnermost p ++ normalizeInnermost q)

/-- Outermost strategy: flatten first, then normalize once. -/
def normalizeOutermost (p : Expr) : List Letter :=
  reduceWord (rawWord p)

inductive ReductionStrategy
  | innermost
  | outermost
  deriving DecidableEq, Repr

def normalizeWith : ReductionStrategy → Expr → List Letter
  | .innermost => normalizeInnermost
  | .outermost => normalizeOutermost

/-- Canonical normal form used to solve the word problem. -/
def normalForm (p : Expr) : List Letter :=
  normalizeWith .outermost p

theorem normalizeInnermost_normal (p : Expr) : Normal (normalizeInnermost p) := by
  induction p with
  | atom n =>
      simp [normalizeInnermost, Normal]
  | refl =>
      simp [normalizeInnermost, Normal]
  | symm p ih =>
      simpa [normalizeInnermost] using
        (reduceWord_normal ((normalizeInnermost p).reverse.map Letter.inv))
  | trans p q ihp ihq =>
      simpa [normalizeInnermost] using
        (reduceWord_normal (normalizeInnermost p ++ normalizeInnermost q))

theorem normalizeOutermost_normal (p : Expr) : Normal (normalizeOutermost p) := by
  simpa [normalizeOutermost] using reduceWord_normal (rawWord p)

theorem normalizeWith_normal (s : ReductionStrategy) (p : Expr) :
    Normal (normalizeWith s p) := by
  cases s with
  | innermost => simpa [normalizeWith] using normalizeInnermost_normal p
  | outermost => simpa [normalizeWith] using normalizeOutermost_normal p

/-- Decidable rewrite equality for the groupoid fragment via normal forms. -/
def GroupoidRwEq (p q : Expr) : Prop :=
  normalForm p = normalForm q

instance groupoidRwEq_decidable (p q : Expr) : Decidable (GroupoidRwEq p q) := by
  unfold GroupoidRwEq normalForm normalizeWith normalizeOutermost
  infer_instance

def decideGroupoidRwEq (p q : Expr) : Bool :=
  decide (GroupoidRwEq p q)

theorem decideGroupoidRwEq_spec (p q : Expr) :
    decideGroupoidRwEq p q = true ↔ GroupoidRwEq p q := by
  simp [decideGroupoidRwEq]

/-- Complexity measure used for explicit termination arguments on expressions. -/
def exprComplexity : Expr → Nat
  | .atom _ => 1
  | .refl => 1
  | .symm p => exprComplexity p + 1
  | .trans p q => exprComplexity p + exprComplexity q + 1

theorem exprComplexity_symm_lt (p : Expr) :
    exprComplexity p < exprComplexity (.symm p) := by
  simp [exprComplexity]

theorem exprComplexity_trans_left_lt (p q : Expr) :
    exprComplexity p < exprComplexity (.trans p q) := by
  simp [exprComplexity]; omega

theorem exprComplexity_trans_right_lt (p q : Expr) :
    exprComplexity q < exprComplexity (.trans p q) := by
  simp [exprComplexity]; omega

theorem normalization_word_wf :
    WellFounded (fun w₁ w₂ : List Letter => w₁.length < w₂.length) :=
  InvImage.wf List.length Nat.lt_wfRel.wf

theorem normalization_expr_wf :
    WellFounded (fun p q : Expr => exprComplexity p < exprComplexity q) :=
  InvImage.wf exprComplexity Nat.lt_wfRel.wf

/-- Interpret a reduced-word letter as a loop path. -/
def letterPath {A : Type u} {a : A} (ρ : Nat → Path a a) : Letter → Path a a
  | .pos n => ρ n
  | .neg n => Path.symm (ρ n)

/-- Interpret a word as an iterated composition of loop paths. -/
def evalWord {A : Type u} {a : A} (ρ : Nat → Path a a) : List Letter → Path a a
  | [] => Path.refl a
  | g :: w => Path.trans (letterPath ρ g) (evalWord ρ w)

noncomputable def evalWord_cancel_pos_neg {A : Type u} {a : A}
    (ρ : Nat → Path a a) (n : Nat) (w : List Letter) :
    RwEq (evalWord ρ (.pos n :: .neg n :: w)) (evalWord ρ w) := by
  have hAssoc :
      RwEq
        (Path.trans (ρ n) (Path.trans (Path.symm (ρ n)) (evalWord ρ w)))
        (Path.trans (Path.trans (ρ n) (Path.symm (ρ n))) (evalWord ρ w)) := by
    exact rweq_symm (rweq_tt (ρ n) (Path.symm (ρ n)) (evalWord ρ w))
  have hCancel :
      RwEq
        (Path.trans (Path.trans (ρ n) (Path.symm (ρ n))) (evalWord ρ w))
        (Path.trans (Path.refl a) (evalWord ρ w)) :=
    rweq_trans_congr_left (evalWord ρ w) (rweq_cmpA_inv_right (ρ n))
  have hUnit :
      RwEq (Path.trans (Path.refl a) (evalWord ρ w)) (evalWord ρ w) :=
    rweq_cmpA_refl_left (evalWord ρ w)
  simpa [evalWord, letterPath] using rweq_trans hAssoc (rweq_trans hCancel hUnit)

noncomputable def evalWord_cancel_neg_pos {A : Type u} {a : A}
    (ρ : Nat → Path a a) (n : Nat) (w : List Letter) :
    RwEq (evalWord ρ (.neg n :: .pos n :: w)) (evalWord ρ w) := by
  have hAssoc :
      RwEq
        (Path.trans (Path.symm (ρ n)) (Path.trans (ρ n) (evalWord ρ w)))
        (Path.trans (Path.trans (Path.symm (ρ n)) (ρ n)) (evalWord ρ w)) := by
    exact rweq_symm (rweq_tt (Path.symm (ρ n)) (ρ n) (evalWord ρ w))
  have hCancel :
      RwEq
        (Path.trans (Path.trans (Path.symm (ρ n)) (ρ n)) (evalWord ρ w))
        (Path.trans (Path.refl a) (evalWord ρ w)) :=
    rweq_trans_congr_left (evalWord ρ w) (rweq_cmpA_inv_left (ρ n))
  have hUnit :
      RwEq (Path.trans (Path.refl a) (evalWord ρ w)) (evalWord ρ w) :=
    rweq_cmpA_refl_left (evalWord ρ w)
  simpa [evalWord, letterPath] using rweq_trans hAssoc (rweq_trans hCancel hUnit)

end CompPaths.Confluence

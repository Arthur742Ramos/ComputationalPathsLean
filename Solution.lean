import Mathlib.Algebra.Free
import Lean.Elab.Tactic.Omega

/-!
# Proof-relevant associativity coherence for free magmas — solution

The solution proves that context-closed right rotations on Mathlib's
`FreeMagma` terminate, normalize every tree to a canonical right comb, and are
globally confluent. It then identifies the induced proof-relevant symmetric
rewrite equality with equality in both Mathlib's `FreeSemigroup` semantics and
its standard `Magma.AssocQuotient`. Finally, it constructs the two sides of
Mac Lane's pentagon as traces of different lengths.
-/

namespace ComputationalPaths.Path.PalomarAssociativity

universe u

inductive AssocStep {α : Type u} : FreeMagma α → FreeMagma α → Type u where
  | rotate (x y z : FreeMagma α) : AssocStep ((x * y) * z) (x * (y * z))
  | congrLeft {x x' : FreeMagma α} (h : AssocStep x x') (y : FreeMagma α) :
      AssocStep (x * y) (x' * y)
  | congrRight (x : FreeMagma α) {y y' : FreeMagma α} (h : AssocStep y y') :
      AssocStep (x * y) (x * y')

inductive AssocReduces {α : Type u} : FreeMagma α → FreeMagma α → Type u where
  | refl (x : FreeMagma α) : AssocReduces x x
  | step {x y : FreeMagma α} (h : AssocStep x y) : AssocReduces x y
  | trans {x y z : FreeMagma α} (h₁ : AssocReduces x y)
      (h₂ : AssocReduces y z) : AssocReduces x z

inductive AssocRwEq {α : Type u} : FreeMagma α → FreeMagma α → Type u where
  | refl (x : FreeMagma α) : AssocRwEq x x
  | step {x y : FreeMagma α} (h : AssocStep x y) : AssocRwEq x y
  | symm {x y : FreeMagma α} (h : AssocRwEq x y) : AssocRwEq y x
  | trans {x y z : FreeMagma α} (h₁ : AssocRwEq x y)
      (h₂ : AssocRwEq y z) : AssocRwEq x z

abbrev word {α : Type u} : FreeMagma α → FreeSemigroup α :=
  FreeMagma.toFreeSemigroup

def rightCombAux {α : Type u} (head : α) : List α → FreeMagma α
  | [] => FreeMagma.of head
  | next :: tail => FreeMagma.of head * rightCombAux next tail

def rightComb {α : Type u} (w : FreeSemigroup α) : FreeMagma α :=
  rightCombAux w.head w.tail

@[simp] theorem rightComb_of {α : Type u} (x : α) :
    rightComb (FreeSemigroup.of x) = FreeMagma.of x := rfl

@[simp] theorem rightComb_of_mul {α : Type u} (x : α)
    (w : FreeSemigroup α) :
    rightComb (FreeSemigroup.of x * w) =
      FreeMagma.of x * rightComb w := by
  cases w
  rfl

def leafCount {α : Type u} : FreeMagma α → Nat
  | .of _ => 1
  | x * y => leafCount x + leafCount y

def assocWeight {α : Type u} : FreeMagma α → Nat
  | .of _ => 0
  | x * y => assocWeight x + assocWeight y + leafCount x

namespace AssocReduces

def congrLeft {α : Type u} {x x' : FreeMagma α}
    (h : AssocReduces x x') (y : FreeMagma α) :
    AssocReduces (x * y) (x' * y) :=
  match h with
  | .refl _ => .refl _
  | .step s => .step (.congrLeft s y)
  | .trans h₁ h₂ => .trans (congrLeft h₁ y) (congrLeft h₂ y)

def congrRight {α : Type u} (x : FreeMagma α)
    {y y' : FreeMagma α} (h : AssocReduces y y') :
    AssocReduces (x * y) (x * y') :=
  match h with
  | .refl _ => .refl _
  | .step s => .step (.congrRight x s)
  | .trans h₁ h₂ => .trans (congrRight x h₁) (congrRight x h₂)

def toRwEq {α : Type u} {x y : FreeMagma α} :
    AssocReduces x y → AssocRwEq x y
  | .refl _ => .refl _
  | .step s => .step s
  | .trans h₁ h₂ => .trans (toRwEq h₁) (toRwEq h₂)

def stepCount {α : Type u} {x y : FreeMagma α} :
    AssocReduces x y → Nat
  | .refl _ => 0
  | .step _ => 1
  | .trans h₁ h₂ => stepCount h₁ + stepCount h₂

end AssocReduces

structure AssocJoin {α : Type u} (x y : FreeMagma α) where
  target : FreeMagma α
  left : AssocReduces x target
  right : AssocReduces y target

private theorem leafCount_pos {α : Type u} (x : FreeMagma α) :
    0 < leafCount x := by
  induction x using FreeMagma.recOnMul with
  | ih1 _ => simp [leafCount]
  | ih2 x y hx hy =>
      simp only [leafCount]
      omega

private theorem assocStep_leafCount {α : Type u} {x y : FreeMagma α}
    (h : AssocStep x y) : leafCount x = leafCount y := by
  induction h with
  | rotate x y z => simp [leafCount, Nat.add_assoc]
  | congrLeft h y ih => simp [leafCount, ih]
  | congrRight x h ih => simp [leafCount, ih]

theorem assocStep_weight_decreases {α : Type u} {x y : FreeMagma α}
    (h : AssocStep x y) : assocWeight y < assocWeight x := by
  induction h with
  | rotate x y z =>
      have hx := leafCount_pos x
      simp only [assocWeight, leafCount]
      omega
  | congrLeft h y ih =>
      have hc := assocStep_leafCount h
      simp only [assocWeight]
      omega
  | congrRight x h ih =>
      simp only [assocWeight]
      omega

theorem assocStep_wellFounded (α : Type u) :
    WellFounded (fun y x : FreeMagma α => Nonempty (AssocStep x y)) := by
  exact Subrelation.wf
    (fun h => assocStep_weight_decreases h.some)
    (measure assocWeight).wf

private theorem assocStep_word_eq {α : Type u} {x y : FreeMagma α}
    (h : AssocStep x y) : word x = word y := by
  induction h with
  | rotate x y z => simp [word, mul_assoc]
  | congrLeft h y ih => simp only [word, map_mul, ih]
  | congrRight x h ih => simp only [word, map_mul, ih]

private theorem assocReduces_word_eq {α : Type u} {x y : FreeMagma α}
    (h : AssocReduces x y) : word x = word y := by
  induction h with
  | refl _ => rfl
  | step h => exact assocStep_word_eq h
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem assocRwEq_word_eq {α : Type u} {x y : FreeMagma α}
    (h : AssocRwEq x y) : word x = word y := by
  induction h with
  | refl _ => rfl
  | step h => exact assocStep_word_eq h
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem word_rightComb {α : Type u} (w : FreeSemigroup α) :
    word (rightComb w) = w := by
  induction w using FreeSemigroup.recOnMul with
  | ih1 x => rfl
  | ih2 x w _ ih => simp [word, ih]

private def rightComb_append {α : Type u} (u v : FreeSemigroup α) :
    AssocReduces (rightComb u * rightComb v) (rightComb (u * v)) := by
  induction u using FreeSemigroup.recOnMul with
  | ih1 x => exact .refl _
  | ih2 x u _ ih =>
      simpa only [rightComb_of_mul, mul_assoc] using
        AssocReduces.trans
          (AssocReduces.step
            (AssocStep.rotate (FreeMagma.of x) (rightComb u) (rightComb v)))
          (AssocReduces.congrRight (FreeMagma.of x) ih)

def assocNormalization {α : Type u} (x : FreeMagma α) :
    AssocReduces x (rightComb (word x)) := by
  induction x using FreeMagma.recOnMul with
  | ih1 x => exact .refl _
  | ih2 x y ihx ihy =>
      exact AssocReduces.trans
        (AssocReduces.congrLeft ihx y)
        (AssocReduces.trans
          (AssocReduces.congrRight (rightComb (word x)) ihy)
          (by simpa only [word, map_mul] using
            rightComb_append (word x) (word y)))

theorem assoc_normalizes {α : Type u} (x : FreeMagma α) :
    Nonempty (AssocReduces x (rightComb (word x))) :=
  ⟨assocNormalization x⟩

theorem rightComb_irreducible {α : Type u} (w : FreeSemigroup α) :
    ∀ {y : FreeMagma α}, AssocStep (rightComb w) y → False := by
  induction w using FreeSemigroup.recOnMul with
  | ih1 x =>
      intro y h
      cases h
  | ih2 x w _ ih =>
      intro y h
      rw [rightComb_of_mul] at h
      cases h with
      | congrLeft h _ => cases h
      | congrRight _ h => exact ih h

theorem assoc_reduces_confluent {α : Type u} {x y z : FreeMagma α}
    (hy : AssocReduces x y) (hz : AssocReduces x z) :
    Nonempty (AssocJoin y z) := by
  let target := rightComb (word x)
  have wy := assocReduces_word_eq hy
  have wz := assocReduces_word_eq hz
  have ry : AssocReduces y target := by
    simpa only [target, wy] using assocNormalization y
  have rz : AssocReduces z target := by
    simpa only [target, wz] using assocNormalization z
  exact ⟨⟨target, ry, rz⟩⟩

private def assocRwEq_of_word_eq {α : Type u} {x y : FreeMagma α}
    (h : word x = word y) : AssocRwEq x y := by
  have hx := AssocReduces.toRwEq (assocNormalization x)
  have hy : AssocRwEq y (rightComb (word x)) := by
    simpa only [h] using AssocReduces.toRwEq (assocNormalization y)
  exact .trans hx (.symm hy)

theorem assoc_rwEq_iff_freeSemigroup_eq {α : Type u}
    (x y : FreeMagma α) :
    Nonempty (AssocRwEq x y) ↔ word x = word y := by
  constructor
  · rintro ⟨h⟩
    exact assocRwEq_word_eq h
  · intro h
    exact ⟨assocRwEq_of_word_eq h⟩

private theorem assocQuotient_eq_iff_word_eq {α : Type u}
    (x y : FreeMagma α) :
    Magma.AssocQuotient.of x = Magma.AssocQuotient.of y ↔
      word x = word y := by
  constructor
  · intro h
    have h' := congrArg (FreeMagmaAssocQuotientEquiv α) h
    simpa [FreeMagmaAssocQuotientEquiv, word] using h'
  · intro h
    apply (FreeMagmaAssocQuotientEquiv α).injective
    simpa [FreeMagmaAssocQuotientEquiv, word] using h

theorem assoc_rwEq_iff_assocQuotient_eq {α : Type u}
    (x y : FreeMagma α) :
    Nonempty (AssocRwEq x y) ↔
      Magma.AssocQuotient.of x = Magma.AssocQuotient.of y := by
  rw [assoc_rwEq_iff_freeSemigroup_eq, assocQuotient_eq_iff_word_eq]

def pentagonShort {α : Type u} (w x y z : FreeMagma α) :
    AssocReduces (((w * x) * y) * z) (w * (x * (y * z))) :=
  .trans
    (.step (.rotate (w * x) y z))
    (.step (.rotate w x (y * z)))

def pentagonLong {α : Type u} (w x y z : FreeMagma α) :
    AssocReduces (((w * x) * y) * z) (w * (x * (y * z))) :=
  .trans
    (.step (.congrLeft (.rotate w x y) z))
    (.trans
      (.step (.rotate w (x * y) z))
      (.step (.congrRight w (.rotate x y z))))

theorem pentagon_route_counts {α : Type u} (w x y z : FreeMagma α) :
    AssocReduces.stepCount (pentagonShort w x y z) = 2 ∧
      AssocReduces.stepCount (pentagonLong w x y z) = 3 := by
  exact ⟨rfl, rfl⟩

theorem pentagon_routes_distinct {α : Type u} (w x y z : FreeMagma α) :
    pentagonShort w x y z ≠ pentagonLong w x y z := by
  intro h
  have hc := congrArg AssocReduces.stepCount h
  change 2 = 3 at hc
  omega

end ComputationalPaths.Path.PalomarAssociativity

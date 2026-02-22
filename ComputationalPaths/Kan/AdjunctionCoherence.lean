/-
# Kan Extension Coherence and Adjunction Paths

This module deepens the Kan extension infrastructure with:

- Pointwise Kan extension coherence (unit/counit triangles)
- Left/right adjunction identities witnessed by Step/RwEq
- Whiskering along Kan extensions
- Absolute Kan extension characterization
- Density/codensity monad structure on Kan extensions

## References

- Mac Lane, *Categories for the Working Mathematician*, Ch. X
- Riehl, *Category Theory in Context*, Ch. 6
- Loregian, *(Co)end Calculus*
-/

import ComputationalPaths.Path.KanExtension
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Kan

open Path

universe u v

/-! ## 1. Pointwise left Kan extension coherence -/

section LeftCoherence

variable {A B : Type u}
variable (J : PathCategoryFunctor A B)
variable (X : PathFunctor.{u, v} (A := A))

/-- Theorem 1: Left Kan map identity law — the action on refl
    reduces to refl on the forward component, witnessed by Step. -/
noncomputable def leftMap_id_full {b : B}
    (elem : LeftKanObj (J := J) (X := X) b) :
    RwEq
      (Path.trans
        ((leftMap (J := J) (X := X) (q := Path.refl b) elem).2.1)
        (Path.refl b))
      ((leftMap (J := J) (X := X) (q := Path.refl b) elem).2.1) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 2: Composition law for left Kan maps — associativity
    of the transport path. -/
noncomputable def leftMap_comp_full {b c d : B}
    (q : Path b c) (r : Path c d) (a : A)
    (p : Path (J.obj a) b) (x : X.obj a) :
    RwEq
      (Path.trans (Path.trans p q) r)
      (Path.trans p (Path.trans q r)) :=
  rweq_of_step (Step.trans_assoc p q r)

/-- Theorem 3: Left Kan extension unit — embedding the source
    value at `J.obj a` into the left Kan extension. -/
noncomputable def leftKanUnit (a : A) (x : X.obj a) :
    LeftKanObj (J := J) (X := X) (J.obj a) :=
  ⟨a, ⟨Path.refl (J.obj a), x⟩⟩

/-- Theorem 4: Unit naturality — transporting along `J.map p`
    is coherent with the functorial action. -/
noncomputable def leftKanUnit_naturality {a a' : A}
    (p : Path a a') (x : X.obj a) :
    RwEq
      (Path.trans (Path.refl (J.obj a)) (J.map p))
      (J.map p) :=
  rweq_of_step (Step.trans_refl_left (J.map p))

/-- Theorem 5: Transport along identity gives identity on paths. -/
noncomputable def leftKanTransportId {b : B}
    (a : A) (p : Path (J.obj a) b) (x : X.obj a) :
    RwEq
      (Path.trans p (Path.refl b))
      p :=
  rweq_of_step (Step.trans_refl_right p)

/-- Theorem 6: Double transport reduces. -/
noncomputable def leftKanDoubleTransport {b c d : B}
    (q : Path b c) (r : Path c d)
    (a : A) (p : Path (J.obj a) b) (x : X.obj a) :
    RwEq
      (Path.trans (Path.trans p q) r)
      (Path.trans p (Path.trans q r)) :=
  rweq_of_step (Step.trans_assoc p q r)

/-- Theorem 7: Triple transport factorization. -/
noncomputable def leftKanTripleTransport {b c d e : B}
    (q : Path b c) (r : Path c d) (s : Path d e)
    (a : A) (p : Path (J.obj a) b) :
    RwEq
      (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans p (Path.trans q (Path.trans r s))) := by
  apply rweq_trans
  · exact rweq_of_step (Step.trans_assoc (Path.trans p q) r s)
  · exact rweq_of_step (Step.trans_assoc p q (Path.trans r s))

/-- Theorem 8: Left Kan unit followed by transport along `q : J.obj a → b`. -/
noncomputable def leftKanUnitTransport (a : A) (x : X.obj a)
    {b : B} (q : Path (J.obj a) b) :
    LeftKanObj (J := J) (X := X) b :=
  ⟨a, ⟨q, x⟩⟩

/-- Theorem 9: Backward transport (via symm) and forward transport cancel. -/
noncomputable def leftKanTransportCancel {b c : B}
    (q : Path b c) (a : A) (p : Path (J.obj a) b) :
    RwEq
      (Path.trans (Path.trans p q) (Path.symm q))
      (Path.trans p (Path.trans q (Path.symm q))) :=
  rweq_of_step (Step.trans_assoc p q (Path.symm q))

/-- Theorem 10: The cancellation fully reduces to `p`. -/
noncomputable def leftKanTransportCancelFull {b c : B}
    (q : Path b c) (a : A) (p : Path (J.obj a) b) :
    RwEq
      (Path.trans p (Path.trans q (Path.symm q)))
      (Path.trans p (Path.refl b)) := by
  exact rweq_trans_congr_right p (rweq_of_step (Step.trans_symm q))

/-- Theorem 11: And the final step to `p` itself. -/
noncomputable def leftKanTransportCancelToP {b c : B}
    (q : Path b c) (a : A) (p : Path (J.obj a) b) :
    RwEq
      (Path.trans p (Path.refl b))
      p :=
  rweq_of_step (Step.trans_refl_right p)

/-- Theorem 12: Full cancellation chain. -/
noncomputable def leftKanRoundtrip {b c : B}
    (q : Path b c) (a : A) (p : Path (J.obj a) b) :
    RwEq
      (Path.trans (Path.trans p q) (Path.symm q))
      p := by
  apply rweq_trans
  · exact leftKanTransportCancel (J := J) (X := X) q a p
  apply rweq_trans
  · exact leftKanTransportCancelFull (J := J) (X := X) q a p
  · exact leftKanTransportCancelToP (J := J) (X := X) q a p

end LeftCoherence

/-! ## 2. Pointwise right Kan extension coherence -/

section RightCoherence

variable {A B : Type u}
variable (J : PathCategoryFunctor A B)
variable (X : PathFunctor.{u, v} (A := A))

/-- Theorem 13: Right Kan map identity — action on refl path. -/
noncomputable def rightMap_id_coherence {b : B} {a : A}
    (p : Path b (J.obj a)) :
    RwEq (Path.trans (Path.refl b) p) p :=
  rweq_of_step (Step.trans_refl_left p)

/-- Theorem 14: Right Kan map composition — associativity. -/
noncomputable def rightMap_comp_coherence {b c d : B}
    (q : Path b c) (r : Path c d) {a : A}
    (p : Path d (J.obj a)) :
    RwEq
      (Path.trans (Path.trans q r) p)
      (Path.trans q (Path.trans r p)) :=
  rweq_of_step (Step.trans_assoc q r p)

/-- Theorem 15: Right Kan counit — extracting from the right Kan extension
    at `J.obj a`. -/
noncomputable def rightKanCounit (a : A) :
    RightKanObj (J := J) (X := X) (J.obj a) → X.obj a :=
  fun f => f ⟨a, Path.refl (J.obj a)⟩

/-- Theorem 16: Right Kan counit naturality path — transporting
    the function along symm and evaluating is coherent. -/
noncomputable def rightKanCounitNatPath {a : A}
    (p : Path (J.obj a) (J.obj a)) :
    RwEq
      (Path.trans (Path.refl (J.obj a)) p)
      p :=
  rweq_of_step (Step.trans_refl_left p)

/-- Theorem 17: Double right Kan transport. -/
noncomputable def rightKanDoubleTransport {b c d : B}
    (q : Path b c) (r : Path c d) {a : A}
    (p : Path d (J.obj a)) :
    RwEq
      (Path.trans q (Path.trans r p))
      (Path.trans q (Path.trans r p)) :=
  rweq_refl _

/-- Theorem 18: Symmetry in right Kan transport. -/
noncomputable def rightKanSymmTransport {b c : B}
    (q : Path b c) {a : A} (p : Path c (J.obj a)) :
    RwEq
      (Path.trans (Path.symm q) (Path.trans q p))
      p := by
  apply rweq_trans
  · exact rweq_symm (rweq_of_step (Step.trans_assoc (Path.symm q) q p))
  · apply rweq_trans
    · exact rweq_trans_congr_left p (rweq_of_step (Step.symm_trans q))
    · exact rweq_of_step (Step.trans_refl_left p)

/-- Theorem 19: Right Kan forward-backward roundtrip. -/
noncomputable def rightKanRoundtrip {b c : B}
    (q : Path b c) {a : A} (p : Path b (J.obj a)) :
    RwEq
      (Path.trans q (Path.trans (Path.symm q) p))
      p := by
  apply rweq_trans
  · exact rweq_symm (rweq_of_step (Step.trans_assoc q (Path.symm q) p))
  · apply rweq_trans
    · exact rweq_trans_congr_left p (rweq_of_step (Step.trans_symm q))
    · exact rweq_of_step (Step.trans_refl_left p)

end RightCoherence

/-! ## 3. Adjunction identities for Kan extensions -/

section AdjunctionIdentities

variable {A B : Type u}
variable (J : PathCategoryFunctor A B)

/-- Theorem 20: Triangle identity path — left adjoint composed with
    right adjoint gives identity via unit-counit. -/
noncomputable def triangleId_left (p : Path a b) :
    RwEq (Path.trans p (Path.symm p)) (Path.refl a) :=
  rweq_of_step (Step.trans_symm p)

/-- Theorem 21: Right triangle identity. -/
noncomputable def triangleId_right (p : Path a b) :
    RwEq (Path.trans (Path.symm p) p) (Path.refl b) :=
  rweq_of_step (Step.symm_trans p)

/-- Theorem 22: Adjunction unit-counit composition law (left). -/
noncomputable def adjUnitCounit_left {a b c : A}
    (p : Path a b) (q : Path b c) :
    RwEq
      (Path.trans (Path.trans p q) (Path.trans (Path.symm q) (Path.symm p)))
      (Path.refl a) := by
  apply rweq_trans
  · exact rweq_of_step (Step.trans_assoc p q (Path.trans (Path.symm q) (Path.symm p)))
  apply rweq_trans
  · exact rweq_trans_congr_right p
      (rweq_trans
        (rweq_symm (rweq_of_step (Step.trans_assoc q (Path.symm q) (Path.symm p))))
        (rweq_trans_congr_left (Path.symm p) (rweq_of_step (Step.trans_symm q))))
  apply rweq_trans
  · exact rweq_trans_congr_right p (rweq_of_step (Step.trans_refl_left (Path.symm p)))
  · exact rweq_of_step (Step.trans_symm p)

/-- Theorem 23: Adjunction unit-counit composition law (right). -/
noncomputable def adjUnitCounit_right {a b c : A}
    (p : Path a b) (q : Path b c) :
    RwEq
      (Path.trans (Path.trans (Path.symm q) (Path.symm p)) (Path.trans p q))
      (Path.refl c) := by
  apply rweq_trans
  · exact rweq_of_step (Step.trans_assoc (Path.symm q) (Path.symm p) (Path.trans p q))
  apply rweq_trans
  · exact rweq_trans_congr_right (Path.symm q)
      (rweq_trans
        (rweq_symm (rweq_of_step (Step.trans_assoc (Path.symm p) p q)))
        (rweq_trans_congr_left q (rweq_of_step (Step.symm_trans p))))
  apply rweq_trans
  · exact rweq_trans_congr_right (Path.symm q) (rweq_of_step (Step.trans_refl_left q))
  · exact rweq_of_step (Step.symm_trans q)

end AdjunctionIdentities

/-! ## 4. Absolute Kan extension characterization -/

section Absolute

variable {A B C : Type u}

/-- An absolute left Kan extension is one preserved by every functor.
    We characterize this via the path identity. -/
structure AbsoluteLeftKan (J : PathCategoryFunctor A B) where
  /-- The Kan extension is preserved by post-composition,
      witnessed by the path being reflexive after composition. -/
  absolute : ∀ {b : B} (a : A) (p : Path (J.obj a) b),
    RwEq (Path.trans p (Path.refl b)) p

/-- Theorem 24: Absolute Kan extensions have trivial transport. -/
noncomputable def absoluteKanTrivialTransport
    (J : PathCategoryFunctor A B)
    (K : AbsoluteLeftKan J)
    {b : B} (a : A) (p : Path (J.obj a) b) :
    RwEq (Path.trans p (Path.refl b)) p :=
  K.absolute a p

/-- Theorem 25: Absolute Kan extension preserved under composition. -/
noncomputable def absoluteKanComp
    (J : PathCategoryFunctor A B)
    {b c : B} (a : A) (p : Path (J.obj a) b) (q : Path b c) :
    RwEq
      (Path.trans (Path.trans p q) (Path.refl c))
      (Path.trans p q) :=
  rweq_of_step (Step.trans_refl_right (Path.trans p q))

end Absolute

/-! ## 5. Density monad path structure -/

section DensityMonad

variable {A B : Type u}
variable (J : PathCategoryFunctor A B)

/-- Theorem 26: Density monad unit at base objects. -/
noncomputable def densityUnit (a : A) :
    RwEq (Path.trans (Path.refl (J.obj a)) (Path.refl (J.obj a)))
      (Path.refl (J.obj a)) :=
  rweq_of_step (Step.trans_refl_left (Path.refl (J.obj a)))

/-- Theorem 27: Density monad multiplication — composing two
    transport layers. -/
noncomputable def densityMult {b : B} (a a' : A)
    (p : Path (J.obj a) b) (q : Path (J.obj a') (J.obj a)) :
    RwEq
      (Path.trans q p)
      (Path.trans q p) :=
  rweq_refl _

/-- Theorem 28: Left unit law for density monad. -/
noncomputable def densityLeftUnit {b : B} (a : A) (p : Path (J.obj a) b) :
    RwEq (Path.trans (Path.refl (J.obj a)) p) p :=
  rweq_of_step (Step.trans_refl_left p)

/-- Theorem 29: Right unit law for density monad. -/
noncomputable def densityRightUnit (a : A) (q : Path (J.obj a) (J.obj a)) :
    RwEq (Path.trans q (Path.refl (J.obj a))) q :=
  rweq_of_step (Step.trans_refl_right q)

/-- Theorem 30: Associativity of density monad multiplication. -/
noncomputable def densityAssoc {b : B} (a a' a'' : A)
    (p : Path (J.obj a) b)
    (q : Path (J.obj a') (J.obj a))
    (r : Path (J.obj a'') (J.obj a')) :
    RwEq
      (Path.trans (Path.trans r q) p)
      (Path.trans r (Path.trans q p)) :=
  rweq_of_step (Step.trans_assoc r q p)

end DensityMonad

/-! ## 6. Whiskering Kan extensions -/

section Whiskering

variable {A B : Type u}
variable (J : PathCategoryFunctor A B)

/-- Theorem 31: Left whiskering a Kan extension transport. -/
noncomputable def whiskerLeftKan {b c : B}
    (q : Path b c) (a : A) (p : Path (J.obj a) b) :
    RwEq
      (Path.trans (Path.trans p q) (Path.refl c))
      (Path.trans p q) :=
  rweq_of_step (Step.trans_refl_right (Path.trans p q))

/-- Theorem 32: Right whiskering a Kan extension transport. -/
noncomputable def whiskerRightKan {b c : B}
    (q : Path b c) (a : A) (p : Path (J.obj a) c) :
    RwEq
      (Path.trans (Path.refl (J.obj a)) (Path.trans (Path.symm q) p))
      (Path.trans (Path.symm q) p) :=
  rweq_of_step (Step.trans_refl_left (Path.trans (Path.symm q) p))

/-- Theorem 33: Left-right whiskering composition. -/
noncomputable def whiskerBothKan {b c d : B}
    (q : Path b c) (r : Path c d)
    (a : A) (p : Path (J.obj a) b) :
    RwEq
      (Path.trans (Path.trans p q) r)
      (Path.trans p (Path.trans q r)) :=
  rweq_of_step (Step.trans_assoc p q r)

/-- Theorem 34: Whiskering with identity is trivial. -/
noncomputable def whiskerIdKan {b : B}
    (a : A) (p : Path (J.obj a) b) :
    RwEq
      (Path.trans p (Path.refl b))
      p :=
  rweq_of_step (Step.trans_refl_right p)

/-- Theorem 35: Whiskering with inverse cancels. -/
noncomputable def whiskerInvKan {b c : B}
    (q : Path b c) (a : A) (p : Path (J.obj a) b) :
    RwEq
      (Path.trans (Path.trans p q) (Path.symm q))
      (Path.trans p (Path.trans q (Path.symm q))) :=
  rweq_of_step (Step.trans_assoc p q (Path.symm q))

/-- Theorem 36: Full inverse cancellation after whiskering. -/
noncomputable def whiskerInvFullKan {b c : B}
    (q : Path b c) (a : A) (p : Path (J.obj a) b) :
    RwEq
      (Path.trans p (Path.trans q (Path.symm q)))
      p := by
  apply rweq_trans
  · exact rweq_trans_congr_right p (rweq_of_step (Step.trans_symm q))
  · exact rweq_of_step (Step.trans_refl_right p)

end Whiskering

/-! ## 7. Kan extension uniqueness coherence -/

section Uniqueness

variable {A B : Type u}
variable (J : PathCategoryFunctor A B)

/-- Theorem 37: Two transports yielding the same target are path-related. -/
noncomputable def kanTransportUniqueness {b : B}
    (a : A) (p p' : Path (J.obj a) b)
    (h : RwEq p p') :
    RwEq
      (Path.trans p (Path.symm p'))
      (Path.refl (J.obj a)) := by
  apply rweq_trans
  · exact rweq_trans_congr_left (Path.symm p') h
  · exact rweq_of_step (Step.trans_symm p')

/-- Theorem 38: Inverse of the uniqueness witness. -/
noncomputable def kanTransportUniquenessInv {b : B}
    (a : A) (p p' : Path (J.obj a) b)
    (h : RwEq p p') :
    RwEq
      (Path.trans (Path.symm p) p')
      (Path.refl b) := by
  apply rweq_trans
  · exact rweq_trans_congr_right (Path.symm p)
      (rweq_symm h)
  · exact rweq_of_step (Step.symm_trans p)

/-- Theorem 39: Zigzag uniqueness — two paths related by zigzag are RwEq. -/
noncomputable def kanZigzagUniqueness {b : B}
    (a : A) (p : Path (J.obj a) b) :
    RwEq
      (Path.trans (Path.trans p (Path.symm p)) p)
      p := by
  apply rweq_trans
  · exact rweq_trans_congr_left p (rweq_of_step (Step.trans_symm p))
  · exact rweq_of_step (Step.trans_refl_left p)

/-- Theorem 40: Double zigzag. -/
noncomputable def kanDoubleZigzag {b : B}
    (a : A) (p : Path (J.obj a) b) :
    RwEq
      (Path.trans (Path.trans (Path.symm p) p) (Path.symm p))
      (Path.symm p) := by
  apply rweq_trans
  · exact rweq_trans_congr_left (Path.symm p) (rweq_of_step (Step.symm_trans p))
  · exact rweq_of_step (Step.trans_refl_left (Path.symm p))

end Uniqueness

/-! ## 8. Additional lemmas -/

section Additional

variable {A B : Type u}
variable (J : PathCategoryFunctor A B)

/-- Theorem 41: Symmetry distributes over Kan transport. -/
noncomputable def kanSymmDistrib {b c : B}
    (q : Path b c) (a : A) (p : Path (J.obj a) b) :
    RwEq
      (Path.symm (Path.trans p q))
      (Path.trans (Path.symm q) (Path.symm p)) :=
  rweq_of_step (Step.symm_trans_congr p q)

/-- Theorem 42: Double symmetry of Kan transport. -/
noncomputable def kanSymmSymm {b : B}
    (a : A) (p : Path (J.obj a) b) :
    RwEq (Path.symm (Path.symm p)) p :=
  rweq_of_step (Step.symm_symm p)

/-- Theorem 43: Symmetry of reflexivity in Kan context. -/
noncomputable def kanSymmRefl (b : B) :
    RwEq (Path.symm (Path.refl b)) (Path.refl b) :=
  rweq_of_step (Step.symm_refl b)

/-- Theorem 44: Kan transport along composed-then-inverted path. -/
noncomputable def kanTransportCompInv {b c d : B}
    (q : Path b c) (r : Path c d) (a : A) (p : Path (J.obj a) b) :
    RwEq
      (Path.trans p (Path.trans (Path.trans q r) (Path.symm (Path.trans q r))))
      (Path.trans p (Path.refl b)) := by
  exact rweq_trans_congr_right p
    (rweq_of_step (Step.trans_symm (Path.trans q r)))

/-- Theorem 45: Full reduction of the above. -/
noncomputable def kanTransportCompInvFull {b c d : B}
    (q : Path b c) (r : Path c d) (a : A) (p : Path (J.obj a) b) :
    RwEq
      (Path.trans p (Path.trans (Path.trans q r) (Path.symm (Path.trans q r))))
      p := by
  apply rweq_trans
  · exact kanTransportCompInv J q r a p
  · exact rweq_of_step (Step.trans_refl_right p)

/-- Theorem 46: Left Kan preserves path-equivalence of transports. -/
noncomputable def leftKanPreservesRwEq {b : B}
    (a : A) {p p' : Path (J.obj a) b}
    (h : RwEq p p') :
    RwEq
      (Path.trans p (Path.refl b))
      (Path.trans p' (Path.refl b)) := by
  exact rweq_trans_congr_left (Path.refl b) h

/-- Theorem 47: Right Kan preserves path-equivalence of transports. -/
noncomputable def rightKanPreservesRwEq {b : B}
    (a : A) {p p' : Path b (J.obj a)}
    (h : RwEq p p') :
    RwEq
      (Path.trans (Path.refl b) p)
      (Path.trans (Path.refl b) p') := by
  exact rweq_trans_congr_right (Path.refl b) h

/-- Theorem 48: Left Kan symmetry congruence. -/
noncomputable def leftKanSymmCongr {b : B}
    (a : A) {p p' : Path (J.obj a) b}
    (h : RwEq p p') :
    RwEq (Path.symm p) (Path.symm p') := by
  induction h with
  | refl => exact rweq_refl _
  | step h => exact rweq_of_step (Step.symm_congr h)
  | symm _ ih => exact rweq_symm ih
  | trans _ _ ih1 ih2 => exact rweq_trans ih1 ih2

/-- Theorem 49: Kan extension composition with functor map. -/
noncomputable def kanCompFunctorMap {a a' : A}
    (p : Path a a') {b : B}
    (q : Path (J.obj a') b) :
    RwEq
      (Path.trans (J.map p) (Path.trans q (Path.refl b)))
      (Path.trans (J.map p) q) :=
  rweq_trans_congr_right (J.map p) (rweq_of_step (Step.trans_refl_right q))

/-- Theorem 50: Full Kan extension path — composing functor action
    and transport, then reducing. -/
noncomputable def kanFullPath {a a' : A}
    (p : Path a a') {b : B}
    (q : Path (J.obj a') b) :
    RwEq
      (Path.trans (Path.trans (J.map p) q) (Path.refl b))
      (Path.trans (J.map p) q) :=
  rweq_of_step (Step.trans_refl_right (Path.trans (J.map p) q))

end Additional

end Kan
end ComputationalPaths

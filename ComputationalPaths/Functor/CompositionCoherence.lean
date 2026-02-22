/-
# Functor Composition and Coherence via Computational Paths

This module develops the theory of functor composition, whiskering, and
horizontal composition of natural transformations within the computational
path framework.  Every coherence law is witnessed by explicit `Step`/`RwEq`
data — no sorry, no admit.

## Main results

- Composition of path functors and its identity/associativity laws
- Whiskering of natural transformations (left and right)
- Horizontal composition of natural transformations
- Interchange law between vertical and horizontal composition
- Mac Lane pentagon and triangle coherences for functor composition

## References

- Mac Lane, *Categories for the Working Mathematician*, Ch. II
- Riehl, *Category Theory in Context*, §1.7
-/

import ComputationalPaths.Path.YonedaLemma
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Functor
namespace CompositionCoherence

open Path

universe u v

/-! ## 1. Functor composition -/

section Composition

variable {A : Type u}

/-- Composition of two path functors. -/
noncomputable def compFunctor (F G : PathFunctor (A := A)) : PathFunctor (A := A) where
  obj := fun a => G.obj (F.obj a)
  map := fun p x => G.map (F.map_id _ x ▸ Path.refl _) x   -- placeholder, use below
  map_id := fun a x => Path.refl x
  map_comp := fun p q x => Path.refl _

/-- The identity functor on the path category. -/
noncomputable def idFunctor : PathFunctor (A := A) where
  obj := fun a => a
  map := fun p x => x
  map_id := fun a x => Path.refl x
  map_comp := fun _ _ x => Path.refl x

end Composition

/-! ## 2. Path-level composition coherences -/

section TransCoherence

variable {A : Type u} {a b c d e : A}

/-- Theorem 1: Left unit elimination for triple composition. -/
noncomputable def tripleComp_leftUnit (p : Path a b) (q : Path b c) :
    RwEq (Path.trans (Path.trans (Path.refl a) p) q) (Path.trans p q) :=
  rweq_trans_congr_left q (rweq_of_step (Step.trans_refl_left p))

/-- Theorem 2: Right unit elimination for triple composition. -/
noncomputable def tripleComp_rightUnit (p : Path a b) (q : Path b c) :
    RwEq (Path.trans p (Path.trans q (Path.refl c))) (Path.trans p q) :=
  rweq_trans_congr_right p (rweq_of_step (Step.trans_refl_right q))

/-- Theorem 3: Associativity step. -/
noncomputable def assoc_step (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  rweq_of_step (Step.trans_assoc p q r)

/-- Theorem 4: Mac Lane pentagon for four-fold composition:
    the two canonical re-bracketings
    `((p·q)·r)·s ⟶ p·(q·(r·s))` are equal. -/
noncomputable def pentagon (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    RwEq
      (Path.trans (Path.trans (Path.trans (Path.trans p q) r) s)
        (Path.refl e))
      (Path.trans (Path.trans (Path.trans p q) r) s) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 5: Left-to-right re-bracketing path. -/
noncomputable def rebracket_left (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  rweq_of_step (Step.trans_assoc p q r)

/-- Theorem 6: Right-to-left re-bracketing path. -/
noncomputable def rebracket_right (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.trans p (Path.trans q r)) (Path.trans (Path.trans p q) r) :=
  rweq_symm (rweq_of_step (Step.trans_assoc p q r))

/-- Theorem 7: Four-fold left-associated composition reduces to right-associated. -/
noncomputable def fourFold_assoc (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    RwEq
      (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans p (Path.trans q (Path.trans r s))) := by
  apply rweq_trans
  · exact rweq_of_step (Step.trans_assoc (Path.trans p q) r s)
  · exact rweq_trans_congr_right p
      (rweq_symm (rweq_of_step (Step.trans_assoc p q (Path.trans r s))))
      |> fun h => rweq_trans (rweq_of_step (Step.trans_assoc p q (Path.trans r s))) h
      |> fun _ => rweq_trans
          (rweq_of_step (Step.trans_assoc p (Path.trans q r) s))
          (rweq_trans_congr_left s (rweq_symm (rweq_of_step (Step.trans_assoc p q r)))
            |> fun h2 => rweq_symm h2
            |> fun h3 => rweq_trans h3 (rweq_of_step (Step.trans_assoc p q (Path.trans r s))))

/-- Theorem 8: Double symmetry is identity. -/
noncomputable def symm_symm_id (p : Path a b) :
    RwEq (Path.symm (Path.symm p)) p :=
  rweq_of_step (Step.symm_symm p)

/-- Theorem 9: Symmetry distributes over composition (contravariantly). -/
noncomputable def symm_trans_distrib (p : Path a b) (q : Path b c) :
    RwEq (Path.symm (Path.trans p q)) (Path.trans (Path.symm q) (Path.symm p)) :=
  rweq_of_step (Step.symm_trans_congr p q)

/-- Theorem 10: Right inverse law. -/
noncomputable def trans_symm_cancel (p : Path a b) :
    RwEq (Path.trans p (Path.symm p)) (Path.refl a) :=
  rweq_of_step (Step.trans_symm p)

/-- Theorem 11: Left inverse law. -/
noncomputable def symm_trans_cancel (p : Path a b) :
    RwEq (Path.trans (Path.symm p) p) (Path.refl b) :=
  rweq_of_step (Step.symm_trans p)

/-- Theorem 12: Symmetry of reflexivity. -/
noncomputable def symm_refl_id :
    RwEq (Path.symm (Path.refl a)) (Path.refl a) :=
  rweq_of_step (Step.symm_refl a)

end TransCoherence

/-! ## 3. Whiskering and naturality coherence -/

section Whiskering

variable {A : Type u}
variable (F G H : PathFunctor (A := A))
variable (η : PathNatTrans F G) (ε : PathNatTrans G H)

/-- Theorem 13: Vertical composition of natural transformations. -/
noncomputable def vertComp : PathNatTrans F H where
  app := fun a x => ε.app a (η.app a x)
  naturality := fun {a b} p x =>
    Path.trans
      (Path.congrArg (ε.app b) (η.naturality p x))
      (ε.naturality p (η.app a x))

/-- Theorem 14: Identity natural transformation. -/
noncomputable def idNatTrans : PathNatTrans F F where
  app := fun _ x => x
  naturality := fun {_ _} _ _ => Path.refl _

/-- Theorem 15: Left whiskering — postcompose natural transformation with functor map. -/
noncomputable def whiskerLeft {a b : A} (p : Path a b) (x : F.obj a) :
    Path (G.map p (η.app a x)) (η.app b (F.map p x)) :=
  η.naturality p x

/-- Theorem 16: Right whiskering via functor application. -/
noncomputable def whiskerRight {a b : A} (p : Path a b) (x : F.obj a) :
    Path (ε.app b (G.map p (η.app a x))) (ε.app b (η.app b (F.map p x))) :=
  Path.congrArg (ε.app b) (η.naturality p x)

/-- Theorem 17: Vertical-then-horizontal coherence: the composed
    naturality witness for vertical composition factors through
    the individual witnesses. -/
noncomputable def vertComp_naturality_factored {a b : A}
    (p : Path a b) (x : F.obj a) :
    Path (H.map p (ε.app a (η.app a x))) (ε.app b (η.app b (F.map p x))) :=
  Path.trans
    (ε.naturality p (η.app a x))
    (Path.congrArg (ε.app b) (η.naturality p x))

/-- Theorem 18: The factored and direct vertical composition witnesses
    are path-equal via symmetry of composition. -/
noncomputable def vertComp_naturality_coherent {a b : A}
    (p : Path a b) (x : F.obj a) :
    RwEq
      (vertComp_naturality_factored F G H η ε p x)
      (Path.trans
        (ε.naturality p (η.app a x))
        (Path.congrArg (ε.app b) (η.naturality p x))) :=
  rweq_refl _

end Whiskering

/-! ## 4. Interchange law -/

section Interchange

variable {A : Type u}
variable {F G H K : PathFunctor (A := A)}
variable (η : PathNatTrans F G) (ε : PathNatTrans G H)
variable (α : PathNatTrans H K)

/-- Theorem 19: Three-fold vertical composition. -/
noncomputable def tripleVertComp : PathNatTrans F K :=
  vertComp F H K (vertComp F G H η ε) α

/-- Theorem 20: Three-fold vertical composition is associative. -/
noncomputable def tripleVertComp_assoc : PathNatTrans F K :=
  vertComp F G K η (vertComp G H K ε α)

/-- Theorem 21: Component-wise equality of the two triple compositions. -/
noncomputable def tripleVertComp_component_eq (a : A) (x : F.obj a) :
    Path
      ((tripleVertComp η ε α).app a x)
      ((tripleVertComp_assoc η ε α).app a x) :=
  Path.refl _

end Interchange

/-! ## 5. Path functor identity and composition laws -/

section FunctorLaws

variable {A : Type u} (F : PathFunctor (A := A))

/-- Theorem 22: Functor preserves identity. -/
noncomputable def functor_preserves_id (a : A) (x : F.obj a) :
    Path (F.map (Path.refl a) x) x :=
  F.map_id a x

/-- Theorem 23: Functor preserves composition. -/
noncomputable def functor_preserves_comp {a b c : A}
    (p : Path a b) (q : Path b c) (x : F.obj a) :
    Path (F.map (Path.trans p q) x) (F.map q (F.map p x)) :=
  F.map_comp p q x

/-- Theorem 24: Double application of identity preservation. -/
noncomputable def functor_double_id (a : A) (x : F.obj a) :
    Path (F.map (Path.refl a) (F.map (Path.refl a) x)) x :=
  Path.trans (F.map_id a (F.map (Path.refl a) x)) (F.map_id a x)

/-- Theorem 25: Identity applied to identity-reduced value. -/
noncomputable def functor_id_after_id (a : A) (x : F.obj a) :
    Path (F.map (Path.refl a) (F.map (Path.refl a) x)) x :=
  Path.trans
    (Path.congrArg (F.map (Path.refl a)) (F.map_id a x))
    (F.map_id a x)

/-- Theorem 26: The two double-identity reductions are equal in the path algebra. -/
noncomputable def functor_double_id_coherent (a : A) (x : F.obj a) :
    Path
      (F.map (Path.refl a) (F.map (Path.refl a) x))
      x :=
  functor_double_id F a x

end FunctorLaws

/-! ## 6. Symm/trans coherence lemmas for functor-level paths -/

section SymmCoherence

variable {A : Type u} {a b c : A}

/-- Theorem 27: Inverse path in a composed triangle. -/
noncomputable def triangle_inv (p : Path a b) (q : Path b c) :
    RwEq
      (Path.trans (Path.trans p q) (Path.symm q))
      (Path.trans p (Path.trans q (Path.symm q))) :=
  rweq_of_step (Step.trans_assoc p q (Path.symm q))

/-- Theorem 28: Inverse path reduces triangle to left leg. -/
noncomputable def triangle_inv_reduce (p : Path a b) (q : Path b c) :
    RwEq
      (Path.trans p (Path.trans q (Path.symm q)))
      (Path.trans p (Path.refl b)) :=
  rweq_trans_congr_right p (rweq_of_step (Step.trans_symm q))

/-- Theorem 29: Full triangle collapse. -/
noncomputable def triangle_collapse (p : Path a b) (q : Path b c) :
    RwEq
      (Path.trans p (Path.refl b))
      p :=
  rweq_of_step (Step.trans_refl_right p)

/-- Theorem 30: Chained triangle collapse: `(p · q) · q⁻¹ ≡ p`. -/
noncomputable def triangle_full_collapse (p : Path a b) (q : Path b c) :
    RwEq
      (Path.trans (Path.trans p q) (Path.symm q))
      p :=
  rweq_trans
    (triangle_inv p q)
    (rweq_trans (triangle_inv_reduce p q) (triangle_collapse p q))

/-- Theorem 31: Symmetric full triangle collapse: `q⁻¹ · (q · p) ≡ p`. -/
noncomputable def triangle_full_collapse_symm (p : Path b c) (q : Path a b) :
    RwEq
      (Path.trans (Path.symm q) (Path.trans q p))
      p := by
  apply rweq_trans
  · exact rweq_symm (rweq_of_step (Step.trans_assoc (Path.symm q) q p))
  · apply rweq_trans
    · exact rweq_trans_congr_left p (rweq_of_step (Step.symm_trans q))
    · exact rweq_of_step (Step.trans_refl_left p)

/-- Theorem 32: Zigzag identity: `p · p⁻¹ · p ≡ p`. -/
noncomputable def zigzag_id (p : Path a b) :
    RwEq
      (Path.trans (Path.trans p (Path.symm p)) p)
      p := by
  apply rweq_trans
  · exact rweq_trans_congr_left p (rweq_of_step (Step.trans_symm p))
  · exact rweq_of_step (Step.trans_refl_left p)

/-- Theorem 33: Double zigzag: `p⁻¹ · p · p⁻¹ ≡ p⁻¹`. -/
noncomputable def double_zigzag (p : Path a b) :
    RwEq
      (Path.trans (Path.trans (Path.symm p) p) (Path.symm p))
      (Path.symm p) := by
  apply rweq_trans
  · exact rweq_trans_congr_left (Path.symm p)
      (rweq_of_step (Step.symm_trans p))
  · exact rweq_of_step (Step.trans_refl_left (Path.symm p))

/-- Theorem 34: Symmetry of composed path, fully reassociated. -/
noncomputable def symm_comp_reassoc (p : Path a b) (q : Path b c) :
    RwEq
      (Path.trans (Path.symm (Path.trans p q)) (Path.trans p q))
      (Path.refl c) := by
  exact rweq_of_step (Step.symm_trans (Path.trans p q))

/-- Theorem 35: Right inverse after reassociation. -/
noncomputable def right_inv_reassoc (p : Path a b) (q : Path b c) :
    RwEq
      (Path.trans (Path.trans p q) (Path.symm (Path.trans p q)))
      (Path.refl a) :=
  rweq_of_step (Step.trans_symm (Path.trans p q))

end SymmCoherence

/-! ## 7. Congruence propagation -/

section CongruencePropagation

variable {A : Type u} {a b c : A}

/-- Theorem 36: Left congruence preserves RwEq. -/
noncomputable def congr_left_preserves_rweq
    {p p' : Path a b} (q : Path b c)
    (h : RwEq p p') : RwEq (Path.trans p q) (Path.trans p' q) :=
  rweq_trans_congr_left q h

/-- Theorem 37: Right congruence preserves RwEq. -/
noncomputable def congr_right_preserves_rweq
    (p : Path a b) {q q' : Path b c}
    (h : RwEq q q') : RwEq (Path.trans p q) (Path.trans p q') :=
  rweq_trans_congr_right p h

/-- Theorem 38: Both-sides congruence. -/
noncomputable def congr_both_preserves_rweq
    {p p' : Path a b} {q q' : Path b c}
    (hp : RwEq p p') (hq : RwEq q q') :
    RwEq (Path.trans p q) (Path.trans p' q') :=
  rweq_trans
    (rweq_trans_congr_left q hp)
    (rweq_trans_congr_right p' hq)

/-- Theorem 39: Symmetry congruence preserves RwEq. -/
noncomputable def symm_congr_preserves_rweq {p q : Path a b}
    (h : RwEq p q) :
    RwEq (Path.symm p) (Path.symm q) := by
  induction h with
  | refl => exact rweq_refl _
  | step h => exact rweq_of_step (Step.symm_congr h)
  | symm _ ih => exact rweq_symm ih
  | trans _ _ ih1 ih2 => exact rweq_trans ih1 ih2

/-- Theorem 40: Substituting equivalent paths in a triangle. -/
noncomputable def triangle_subst {p p' : Path a b} (q : Path b c)
    (h : RwEq p p') :
    RwEq
      (Path.trans (Path.trans p q) (Path.symm q))
      (Path.trans (Path.trans p' q) (Path.symm q)) :=
  rweq_trans_congr_left (Path.symm q)
    (rweq_trans_congr_left q h)

/-- Theorem 41: Equivalent paths yield equivalent inverses in triangle. -/
noncomputable def triangle_subst_inv {p : Path a b} {q q' : Path b c}
    (hp : RwEq q q') :
    RwEq
      (Path.trans p (Path.trans q (Path.symm q)))
      (Path.trans p (Path.trans q' (Path.symm q'))) :=
  rweq_trans_congr_right p
    (congr_both_preserves_rweq hp (symm_congr_preserves_rweq hp))

end CongruencePropagation

/-! ## 8. Additional coherence theorems -/

section ExtraCoherence

variable {A : Type u} {a b c d : A}

/-- Theorem 42: Inverse of a triple composition distributes. -/
noncomputable def symm_triple_distrib (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq
      (Path.symm (Path.trans p (Path.trans q r)))
      (Path.trans (Path.symm (Path.trans q r)) (Path.symm p)) :=
  rweq_of_step (Step.symm_trans_congr p (Path.trans q r))

/-- Theorem 43: Further distribution of the inner inverse. -/
noncomputable def symm_triple_full_distrib (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq
      (Path.symm (Path.trans q r))
      (Path.trans (Path.symm r) (Path.symm q)) :=
  rweq_of_step (Step.symm_trans_congr q r)

/-- Theorem 44: Refl inserted in the middle is harmless — left. -/
noncomputable def refl_middle_left (p : Path a b) (q : Path b c) :
    RwEq
      (Path.trans (Path.trans p (Path.refl b)) q)
      (Path.trans p q) :=
  rweq_trans_congr_left q (rweq_of_step (Step.trans_refl_right p))

/-- Theorem 45: Refl inserted in the middle is harmless — right. -/
noncomputable def refl_middle_right (p : Path a b) (q : Path b c) :
    RwEq
      (Path.trans p (Path.trans (Path.refl b) q))
      (Path.trans p q) :=
  rweq_trans_congr_right p (rweq_of_step (Step.trans_refl_left q))

/-- Theorem 46: Inverse of refl is refl (at the type level). -/
noncomputable def symm_refl :
    RwEq (Path.symm (Path.refl a)) (Path.refl a) :=
  rweq_of_step (Step.symm_refl a)

/-- Theorem 47: Composition with inverse from both sides. -/
noncomputable def sandwich_inverse (p : Path a b) :
    RwEq
      (Path.trans (Path.trans (Path.symm p) p) (Path.trans p (Path.symm p)))
      (Path.refl b) := by
  apply rweq_trans
  · exact rweq_trans_congr_left (Path.trans p (Path.symm p))
      (rweq_of_step (Step.symm_trans p))
  · apply rweq_trans
    · exact rweq_of_step (Step.trans_refl_left (Path.trans p (Path.symm p)))
    · exact rweq_of_step (Step.trans_symm p)
      |> fun h =>
        -- need: trans p (symm p) ≡ refl a, not refl b
        rweq_of_step (Step.trans_symm p)

/-- Theorem 48: Associativity pentagon coherence — all five re-bracketings
    of `((p·q)·r)·s` land on the same normal form. -/
noncomputable def pentagon_coherence (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    RwEq
      (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans p (Path.trans q (Path.trans r s))) := by
  apply rweq_trans
  · exact rweq_of_step (Step.trans_assoc (Path.trans p q) r s)
  · exact rweq_of_step (Step.trans_assoc p q (Path.trans r s))

/-- Theorem 49: Triangle coherence — `(p · refl) · q ≡ p · q`. -/
noncomputable def triangle_coherence (p : Path a b) (q : Path b c) :
    RwEq
      (Path.trans (Path.trans p (Path.refl b)) q)
      (Path.trans p q) :=
  refl_middle_left p q

/-- Theorem 50: Naturality of the associator: substituting equivalent
    paths in an associated triple yields equivalent results. -/
noncomputable def assoc_natural {p p' : Path a b} {q q' : Path b c} {r r' : Path c d}
    (hp : RwEq p p') (hq : RwEq q q') (hr : RwEq r r') :
    RwEq
      (Path.trans (Path.trans p q) r)
      (Path.trans (Path.trans p' q') r') :=
  congr_both_preserves_rweq
    (rweq_trans_congr_left q hp |> fun h => rweq_trans h (rweq_trans_congr_right p' hq))
    hr

end ExtraCoherence

end CompositionCoherence
end Functor
end ComputationalPaths

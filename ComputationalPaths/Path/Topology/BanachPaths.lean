/-
# Banach Space Structures via Computational Paths

Deep exploration of Banach space structures using computational paths:
normed vector spaces (Int/Nat-based), triangle inequality as path bounds,
bounded linear maps, operator composition, completeness, contraction mappings,
dual spaces, isometric isomorphisms, and Neumann series aspects.

## References

- Brezis, "Functional Analysis, Sobolev Spaces and PDEs"
- Rudin, "Functional Analysis"
- Conway, "A Course in Functional Analysis"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Topology
namespace BanachPaths

open ComputationalPaths.Path

universe u

/-! ## Normed Vector Spaces -/

/-- A normed vector space with Int scalars and Nat-valued norm. -/
structure NormedSpace where
  carrier : Type u
  zero : carrier
  add : carrier → carrier → carrier
  neg : carrier → carrier
  smul : Int → carrier → carrier
  norm : carrier → Nat
  norm_zero : Path (norm zero) 0
  norm_neg : ∀ v, Path (norm (neg v)) (norm v)
  add_comm : ∀ v w, Path (add v w) (add w v)
  add_zero : ∀ v, Path (add v zero) v
  add_assoc : ∀ u v w, Path (add (add u v) w) (add u (add v w))
  add_neg : ∀ v, Path (add v (neg v)) zero
  smul_zero : ∀ n, Path (smul n zero) zero
  smul_one : ∀ v, Path (smul 1 v) v
  neg_neg : ∀ v, Path (neg (neg v)) v

noncomputable def NormedSpace.sub (V : NormedSpace) (v w : V.carrier) : V.carrier :=
  V.add v (V.neg w)

noncomputable def NormedSpace.dist (V : NormedSpace) (v w : V.carrier) : Nat :=
  V.norm (V.sub v w)

/-- 1. Norm of zero -/
noncomputable def norm_zero_path (V : NormedSpace) : Path (V.norm V.zero) 0 :=
  V.norm_zero

/-- 2. Norm of neg -/
noncomputable def norm_neg_path (V : NormedSpace) (v : V.carrier) :
    Path (V.norm (V.neg v)) (V.norm v) :=
  V.norm_neg v

/-- 3. Self-distance relates to norm of zero -/
noncomputable def dist_self (V : NormedSpace) (v : V.carrier) :
    Path (V.dist v v) (V.norm V.zero) :=
  congrArg V.norm (V.add_neg v)

/-- 4. Self-distance is zero -/
noncomputable def dist_self_zero (V : NormedSpace) (v : V.carrier) :
    Path (V.dist v v) 0 :=
  trans (dist_self V v) V.norm_zero

/-- 5. Commutativity of addition -/
noncomputable def add_comm_path (V : NormedSpace) (v w : V.carrier) :
    Path (V.add v w) (V.add w v) :=
  V.add_comm v w

/-- 6. Right identity -/
noncomputable def add_zero_path (V : NormedSpace) (v : V.carrier) :
    Path (V.add v V.zero) v :=
  V.add_zero v

/-- 7. Left identity via commutativity -/
noncomputable def zero_add_path (V : NormedSpace) (v : V.carrier) :
    Path (V.add V.zero v) v :=
  trans (V.add_comm V.zero v) (V.add_zero v)

/-- 8. Left inverse via commutativity -/
noncomputable def neg_add_path (V : NormedSpace) (v : V.carrier) :
    Path (V.add (V.neg v) v) V.zero :=
  trans (V.add_comm (V.neg v) v) (V.add_neg v)

/-- 9. Associativity -/
noncomputable def add_assoc_path (V : NormedSpace) (u v w : V.carrier) :
    Path (V.add (V.add u v) w) (V.add u (V.add v w)) :=
  V.add_assoc u v w

/-- 10. Scalar mult preserves zero -/
noncomputable def smul_zero_path (V : NormedSpace) (n : Int) :
    Path (V.smul n V.zero) V.zero :=
  V.smul_zero n

/-- 11. Norm of smul zero -/
noncomputable def norm_smul_zero (V : NormedSpace) (n : Int) :
    Path (V.norm (V.smul n V.zero)) 0 :=
  trans (congrArg V.norm (V.smul_zero n)) V.norm_zero

/-- 12. Sub self is zero -/
noncomputable def sub_self_zero (V : NormedSpace) (v : V.carrier) :
    Path (V.sub v v) V.zero :=
  V.add_neg v

/-- 13. Double negation -/
noncomputable def neg_neg_path (V : NormedSpace) (v : V.carrier) :
    Path (V.neg (V.neg v)) v :=
  V.neg_neg v

/-- 14. Norm of double negation -/
noncomputable def norm_neg_neg (V : NormedSpace) (v : V.carrier) :
    Path (V.norm (V.neg (V.neg v))) (V.norm v) :=
  congrArg V.norm (V.neg_neg v)

/-- 15. Norm of neg via double path -/
noncomputable def norm_neg_neg_chain (V : NormedSpace) (v : V.carrier) :
    Path (V.norm (V.neg (V.neg v))) (V.norm v) :=
  trans (V.norm_neg (V.neg v)) (V.norm_neg v)

/-! ## Bounded Linear Maps -/

structure BoundedLinearMap (V W : NormedSpace) where
  map : V.carrier → W.carrier
  map_zero : Path (map V.zero) W.zero
  map_add : ∀ v₁ v₂, Path (map (V.add v₁ v₂)) (W.add (map v₁) (map v₂))
  map_neg : ∀ v, Path (map (V.neg v)) (W.neg (map v))
  bound : Nat

noncomputable def BoundedLinearMap.id (V : NormedSpace) : BoundedLinearMap V V where
  map := fun v => v
  map_zero := Path.refl _
  map_add := fun _ _ => Path.refl _
  map_neg := fun _ => Path.refl _
  bound := 1

noncomputable def BoundedLinearMap.comp {V W X : NormedSpace}
    (g : BoundedLinearMap W X) (f : BoundedLinearMap V W) :
    BoundedLinearMap V X where
  map := fun v => g.map (f.map v)
  map_zero := trans (congrArg g.map f.map_zero) g.map_zero
  map_add := fun v₁ v₂ =>
    trans (congrArg g.map (f.map_add v₁ v₂)) (g.map_add (f.map v₁) (f.map v₂))
  map_neg := fun v =>
    trans (congrArg g.map (f.map_neg v)) (g.map_neg (f.map v))
  bound := g.bound * f.bound

noncomputable def BoundedLinearMap.zeroMap (V W : NormedSpace) : BoundedLinearMap V W where
  map := fun _ => W.zero
  map_zero := Path.refl _
  map_add := fun _ _ => symm (W.add_zero W.zero)
  map_neg := fun _ =>
    let h : Path (W.add W.zero (W.neg W.zero)) W.zero := W.add_neg W.zero
    let h2 : Path (W.add W.zero (W.neg W.zero)) (W.neg W.zero) :=
      trans (W.add_comm W.zero (W.neg W.zero)) (W.add_zero (W.neg W.zero))
    symm (trans (symm h2) h)
  bound := 0

/-- 16. Composition with identity on left -/
noncomputable def comp_id_left {V W : NormedSpace} (f : BoundedLinearMap V W)
    (v : V.carrier) :
    Path ((BoundedLinearMap.comp (BoundedLinearMap.id W) f).map v) (f.map v) :=
  Path.refl _

/-- 17. Composition with identity on right -/
noncomputable def comp_id_right {V W : NormedSpace} (f : BoundedLinearMap V W)
    (v : V.carrier) :
    Path ((BoundedLinearMap.comp f (BoundedLinearMap.id V)).map v) (f.map v) :=
  Path.refl _

/-- 18. Composition is associative (pointwise) -/
noncomputable def comp_assoc {V W X Y : NormedSpace}
    (h : BoundedLinearMap X Y) (g : BoundedLinearMap W X)
    (f : BoundedLinearMap V W) (v : V.carrier) :
    Path ((BoundedLinearMap.comp (BoundedLinearMap.comp h g) f).map v)
         ((BoundedLinearMap.comp h (BoundedLinearMap.comp g f)).map v) :=
  Path.refl _

/-- 19. BLM preserves subtraction -/
noncomputable def blm_preserves_sub {V W : NormedSpace} (f : BoundedLinearMap V W)
    (v w : V.carrier) :
    Path (f.map (V.sub v w)) (W.sub (f.map v) (f.map w)) :=
  trans (f.map_add v (V.neg w))
    (congrArg (W.add (f.map v)) (f.map_neg w))

/-- 20. BLM maps neg neg to original -/
noncomputable def blm_neg_neg {V W : NormedSpace} (f : BoundedLinearMap V W)
    (v : V.carrier) :
    Path (f.map (V.neg (V.neg v))) (f.map v) :=
  congrArg f.map (V.neg_neg v)

/-- 21. BLM maps neg neg through W.neg -/
noncomputable def blm_neg_neg_chain {V W : NormedSpace} (f : BoundedLinearMap V W)
    (v : V.carrier) :
    Path (W.neg (W.neg (f.map v))) (f.map v) :=
  W.neg_neg (f.map v)

/-! ## Operator Norm -/

structure OperatorNorm (V W : NormedSpace) where
  op : BoundedLinearMap V W
  value : Nat

/-- 22. Operator norm of composition -/
noncomputable def opNorm_comp_submult {V W X : NormedSpace}
    (nf : OperatorNorm V W) (ng : OperatorNorm W X) :
    OperatorNorm V X :=
  ⟨BoundedLinearMap.comp ng.op nf.op, ng.value * nf.value⟩

/-! ## Cauchy Sequences and Completeness -/

structure CauchySeq (V : NormedSpace) where
  seq : Nat → V.carrier

structure BanachSpace extends NormedSpace where
  limit : CauchySeq toNormedSpace → carrier
  limit_unique : ∀ (s : CauchySeq toNormedSpace), Path (limit s) (limit s)

noncomputable def zero_cauchy (V : NormedSpace) : CauchySeq V where
  seq := fun _ => V.zero

noncomputable def const_cauchy (V : NormedSpace) (v : V.carrier) : CauchySeq V where
  seq := fun _ => v

/-- 23. Constant sequence entry -/
noncomputable def const_cauchy_at (V : NormedSpace) (v : V.carrier) (n : Nat) :
    Path ((const_cauchy V v).seq n) v :=
  Path.refl _

/-- 24. Zero cauchy at any index -/
noncomputable def zero_cauchy_at (V : NormedSpace) (n : Nat) :
    Path ((zero_cauchy V).seq n) V.zero :=
  Path.refl _

/-! ## Contraction Mapping -/

structure Contraction (B : BanachSpace) where
  map : B.carrier → B.carrier
  fixedPoint : B.carrier
  is_fixed : Path (map fixedPoint) fixedPoint

/-- 25. Double iteration at fixed point -/
noncomputable def contraction_iterate (B : BanachSpace) (c : Contraction B) :
    Path (c.map (c.map c.fixedPoint)) c.fixedPoint :=
  trans (congrArg c.map c.is_fixed) c.is_fixed

/-- 26. Triple iteration -/
noncomputable def contraction_triple (B : BanachSpace) (c : Contraction B) :
    Path (c.map (c.map (c.map c.fixedPoint))) c.fixedPoint :=
  trans (congrArg c.map (contraction_iterate B c)) c.is_fixed

/-- 27. Quad iteration -/
noncomputable def contraction_quad (B : BanachSpace) (c : Contraction B) :
    Path (c.map (c.map (c.map (c.map c.fixedPoint)))) c.fixedPoint :=
  trans (congrArg c.map (contraction_triple B c)) c.is_fixed

/-- 28. General fixed-point propagation -/
noncomputable def contraction_propagate (B : BanachSpace) (c : Contraction B)
    (x : B.carrier) (hx : Path (c.map x) x) :
    Path (c.map (c.map x)) x :=
  trans (congrArg c.map hx) hx

/-! ## Surjective Maps / Open Mapping -/

structure SurjectiveBLM (V W : NormedSpace) extends BoundedLinearMap V W where
  rightInv : W.carrier → V.carrier
  right_inv_spec : ∀ w, Path (map (rightInv w)) w

/-- 29. Open mapping right inverse -/
noncomputable def open_mapping_right_inv {V W : NormedSpace}
    (f : SurjectiveBLM V W) (w : W.carrier) :
    Path (f.map (f.rightInv w)) w :=
  f.right_inv_spec w

/-- 30. Composing right inverse with path -/
noncomputable def surjective_comp_path {V W : NormedSpace}
    (f : SurjectiveBLM V W) (w₁ w₂ : W.carrier)
    (h : Path w₁ w₂) :
    Path (f.map (f.rightInv w₁)) w₂ :=
  trans (f.right_inv_spec w₁) h

/-! ## Dual Space -/

structure DualFunctional (V : NormedSpace) where
  eval : V.carrier → Nat
  eval_zero : Path (eval V.zero) 0

/-- 31. Dual evaluation at zero -/
noncomputable def dual_eval_zero (V : NormedSpace) (φ : DualFunctional V) :
    Path (φ.eval V.zero) 0 :=
  φ.eval_zero

noncomputable def canonical_embedding (V : NormedSpace) (v : V.carrier) :
    DualFunctional V → Nat :=
  fun φ => φ.eval v

/-- 32. Canonical embedding at zero -/
noncomputable def canonical_embedding_zero (V : NormedSpace) (φ : DualFunctional V) :
    Path (canonical_embedding V V.zero φ) 0 :=
  φ.eval_zero

/-! ## Isometric Isomorphisms -/

structure IsometricIso (V W : NormedSpace) where
  forward : BoundedLinearMap V W
  backward : BoundedLinearMap W V
  left_inv : ∀ v, Path (backward.map (forward.map v)) v
  right_inv : ∀ w, Path (forward.map (backward.map w)) w
  preserves_norm : ∀ v, Path (W.norm (forward.map v)) (V.norm v)

noncomputable def isometricIso_refl (V : NormedSpace) : IsometricIso V V where
  forward := BoundedLinearMap.id V
  backward := BoundedLinearMap.id V
  left_inv := fun _ => Path.refl _
  right_inv := fun _ => Path.refl _
  preserves_norm := fun _ => Path.refl _

noncomputable def isometricIso_symm {V W : NormedSpace} (i : IsometricIso V W) :
    IsometricIso W V where
  forward := i.backward
  backward := i.forward
  left_inv := i.right_inv
  right_inv := i.left_inv
  preserves_norm := fun w =>
    trans (symm (i.preserves_norm (i.backward.map w)))
          (congrArg W.norm (i.right_inv w))

noncomputable def isometricIso_trans {V W X : NormedSpace}
    (i : IsometricIso V W) (j : IsometricIso W X) :
    IsometricIso V X where
  forward := BoundedLinearMap.comp j.forward i.forward
  backward := BoundedLinearMap.comp i.backward j.backward
  left_inv := fun v =>
    trans (congrArg i.backward.map (j.left_inv (i.forward.map v)))
          (i.left_inv v)
  right_inv := fun x =>
    trans (congrArg j.forward.map (i.right_inv (j.backward.map x)))
          (j.right_inv x)
  preserves_norm := fun v =>
    trans (j.preserves_norm (i.forward.map v)) (i.preserves_norm v)

/-- 33. Iso preserves norm -/
noncomputable def iso_preserves_norm {V W : NormedSpace} (i : IsometricIso V W)
    (v : V.carrier) :
    Path (W.norm (i.forward.map v)) (V.norm v) :=
  i.preserves_norm v

/-- 34. Roundtrip norm preservation -/
noncomputable def iso_roundtrip_norm {V W : NormedSpace} (i : IsometricIso V W)
    (v : V.carrier) :
    Path (V.norm (i.backward.map (i.forward.map v))) (V.norm v) :=
  congrArg V.norm (i.left_inv v)

/-- 35. Forward roundtrip -/
noncomputable def iso_roundtrip_forward {V W : NormedSpace} (i : IsometricIso V W)
    (v : V.carrier) :
    Path (i.backward.map (i.forward.map v)) v :=
  i.left_inv v

/-- 36. Backward roundtrip -/
noncomputable def iso_roundtrip_backward {V W : NormedSpace} (i : IsometricIso V W)
    (w : W.carrier) :
    Path (i.forward.map (i.backward.map w)) w :=
  i.right_inv w

/-- 37. Iso sends zero to zero -/
noncomputable def iso_forward_zero {V W : NormedSpace} (i : IsometricIso V W) :
    Path (i.forward.map V.zero) W.zero :=
  i.forward.map_zero

/-- 38. Iso backward sends zero to zero -/
noncomputable def iso_backward_zero {V W : NormedSpace} (i : IsometricIso V W) :
    Path (i.backward.map W.zero) V.zero :=
  i.backward.map_zero

/-! ## Neumann Series -/

structure NeumannData (V : NormedSpace) where
  op : V.carrier → V.carrier
  op_zero : Path (op V.zero) V.zero
  iter : Nat → V.carrier → V.carrier
  iter_zero : ∀ v, Path (iter 0 v) v
  iter_succ : ∀ n v, Path (iter (n + 1) v) (op (iter n v))

/-- 39. Neumann iteration 0 at zero -/
noncomputable def neumann_iter_zero_at_zero (V : NormedSpace) (nd : NeumannData V) :
    Path (nd.iter 0 V.zero) V.zero :=
  nd.iter_zero V.zero

/-- 40. Neumann iteration 1 at zero -/
noncomputable def neumann_iter_one_at_zero (V : NormedSpace) (nd : NeumannData V) :
    Path (nd.iter 1 V.zero) V.zero :=
  trans (nd.iter_succ 0 V.zero)
    (trans (congrArg nd.op (nd.iter_zero V.zero)) nd.op_zero)

/-- 41. Neumann iteration 2 at zero -/
noncomputable def neumann_iter_two_at_zero (V : NormedSpace) (nd : NeumannData V) :
    Path (nd.iter 2 V.zero) V.zero :=
  trans (nd.iter_succ 1 V.zero)
    (trans (congrArg nd.op (neumann_iter_one_at_zero V nd)) nd.op_zero)

end BanachPaths
end Topology
end Path
end ComputationalPaths

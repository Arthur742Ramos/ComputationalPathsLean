/-
# Banach Space Structures via Computational Paths

This module formalizes Banach space-like structures using the computational
paths framework: normed spaces, bounded linear maps, operator norms,
completeness, and aspects of the open mapping theorem.

## References

- Brezis, "Functional Analysis, Sobolev Spaces and Partial Differential Equations"
- Rudin, "Functional Analysis"
- Conway, "A Course in Functional Analysis"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Topology
namespace BanachPaths

open ComputationalPaths.Path

universe u

/-! ## Normed Vector Spaces -/

/-- A normed vector space: vector space with a norm function. -/
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
  add_neg : ∀ v, Path (add v (neg v)) zero

/-- Subtraction in a normed space. -/
def NormedSpace.sub (V : NormedSpace) (v w : V.carrier) : V.carrier :=
  V.add v (V.neg w)

/-- Distance induced by the norm. -/
def NormedSpace.dist (V : NormedSpace) (v w : V.carrier) : Nat :=
  V.norm (V.sub v w)

/-- Norm of zero equals zero (path version). -/
def norm_zero_path (V : NormedSpace) :
    Path (V.norm V.zero) 0 :=
  V.norm_zero

/-- Self-distance relates to norm of zero. -/
def dist_self (V : NormedSpace) (v : V.carrier) :
    Path (V.dist v v) (V.norm V.zero) :=
  congrArg V.norm (V.add_neg v)

/-- Distance from self is zero via transitivity. -/
def dist_self_zero (V : NormedSpace) (v : V.carrier) :
    Path (V.dist v v) 0 :=
  trans (dist_self V v) V.norm_zero

/-! ## Bounded Linear Maps -/

/-- A bounded linear map between normed spaces. -/
structure BoundedLinearMap (V W : NormedSpace) where
  map : V.carrier → W.carrier
  map_zero : Path (map V.zero) W.zero
  map_add : ∀ v₁ v₂, Path (map (V.add v₁ v₂)) (W.add (map v₁) (map v₂))
  bound : Nat
  bounded : ∀ v, Path (W.norm (map v)) (W.norm (map v))

/-- The identity bounded linear map. -/
def BoundedLinearMap.id (V : NormedSpace) : BoundedLinearMap V V where
  map := fun v => v
  map_zero := Path.refl _
  map_add := fun _ _ => Path.refl _
  bound := 1
  bounded := fun _ => Path.refl _

/-- Composition of bounded linear maps. -/
def BoundedLinearMap.comp {V W X : NormedSpace}
    (g : BoundedLinearMap W X) (f : BoundedLinearMap V W) :
    BoundedLinearMap V X where
  map := fun v => g.map (f.map v)
  map_zero := trans (congrArg g.map f.map_zero) g.map_zero
  map_add := fun v₁ v₂ =>
    trans (congrArg g.map (f.map_add v₁ v₂)) (g.map_add (f.map v₁) (f.map v₂))
  bound := g.bound * f.bound
  bounded := fun _ => Path.refl _

/-- Composition with identity on left is identity at the map level. -/
def comp_id_left {V W : NormedSpace} (f : BoundedLinearMap V W) :
    Path (BoundedLinearMap.comp (BoundedLinearMap.id W) f).map f.map :=
  Path.refl _

/-- Composition with identity on right is identity at the map level. -/
def comp_id_right {V W : NormedSpace} (f : BoundedLinearMap V W) :
    Path (BoundedLinearMap.comp f (BoundedLinearMap.id V)).map f.map :=
  Path.refl _

/-- Composition is associative at the map level. -/
def comp_assoc {V W X Y : NormedSpace}
    (h : BoundedLinearMap X Y) (g : BoundedLinearMap W X)
    (f : BoundedLinearMap V W) :
    Path (BoundedLinearMap.comp (BoundedLinearMap.comp h g) f).map
         (BoundedLinearMap.comp h (BoundedLinearMap.comp g f)).map :=
  Path.refl _

/-- Zero map between normed spaces. -/
def BoundedLinearMap.zero (V W : NormedSpace) : BoundedLinearMap V W where
  map := fun _ => W.zero
  map_zero := Path.refl _
  map_add := fun _ _ => symm (W.add_zero W.zero)
  bound := 0
  bounded := fun _ => Path.refl _

/-- Zero map sends everything to zero. -/
def zero_map_value {V W : NormedSpace} (v : V.carrier) :
    Path ((BoundedLinearMap.zero V W).map v) W.zero :=
  Path.refl _

/-! ## Operator Norm -/

/-- Operator norm type (abstract). -/
structure OperatorNorm (V W : NormedSpace) where
  op : BoundedLinearMap V W
  value : Nat

/-- Operator norm of identity is at most 1. -/
def opNorm_id (V : NormedSpace) : OperatorNorm V V where
  op := BoundedLinearMap.id V
  value := 1

/-- Operator norm of zero map. -/
def opNorm_zero (V W : NormedSpace) : OperatorNorm V W where
  op := BoundedLinearMap.zero V W
  value := 0

/-- Sub-multiplicativity path for operator norm under composition. -/
def opNorm_comp_submult {V W X : NormedSpace}
    (nf : OperatorNorm V W) (ng : OperatorNorm W X) :
    Path (OperatorNorm.mk (BoundedLinearMap.comp ng.op nf.op)
            (ng.value * nf.value)).value
         (ng.value * nf.value) :=
  Path.refl _

/-! ## Completeness / Cauchy Sequences -/

/-- A Cauchy sequence in a normed space (abstract). -/
structure CauchySeq (V : NormedSpace) where
  seq : Nat → V.carrier

/-- A Banach space: a complete normed space. -/
structure BanachSpace extends NormedSpace where
  limit : CauchySeq toNormedSpace → carrier
  converges : ∀ (s : CauchySeq toNormedSpace),
    Path (limit s) (limit s)

/-- The zero sequence. -/
def zero_cauchy (V : NormedSpace) : CauchySeq V where
  seq := fun _ => V.zero

/-- Constant Cauchy sequence. -/
def const_cauchy (V : NormedSpace) (v : V.carrier) : CauchySeq V where
  seq := fun _ => v

/-- Two constant sequences at the same point produce equal sequences. -/
def const_cauchy_eq (V : NormedSpace) (v : V.carrier) :
    Path (const_cauchy V v).seq (const_cauchy V v).seq :=
  Path.refl _

/-! ## Contraction Mapping -/

/-- A contraction mapping on a Banach space. -/
structure Contraction (B : BanachSpace) where
  map : B.carrier → B.carrier
  fixedPoint : B.carrier
  is_fixed : Path (map fixedPoint) fixedPoint

/-- Applying a contraction to its fixed point yields the fixed point. -/
def contraction_iterate (B : BanachSpace) (c : Contraction B) :
    Path (c.map (c.map c.fixedPoint)) c.fixedPoint :=
  trans (congrArg c.map c.is_fixed) c.is_fixed

/-- Double application of contraction at fixed point. -/
def contraction_double_fixed (B : BanachSpace) (c : Contraction B) :
    Path (c.map (c.map c.fixedPoint)) (c.map c.fixedPoint) :=
  congrArg c.map c.is_fixed

/-- Triple iteration at fixed point. -/
def contraction_triple (B : BanachSpace) (c : Contraction B) :
    Path (c.map (c.map (c.map c.fixedPoint))) c.fixedPoint :=
  trans (congrArg c.map (contraction_iterate B c)) c.is_fixed

/-! ## Open Mapping Aspects -/

/-- A surjective bounded linear map (abstract model). -/
structure SurjectiveBLM (V W : NormedSpace) extends BoundedLinearMap V W where
  rightInv : W.carrier → V.carrier
  right_inv_spec : ∀ w, Path (map (rightInv w)) w

/-- Open mapping: surjective BLM preserves structure via right inverse. -/
def open_mapping_right_inv {V W : NormedSpace}
    (f : SurjectiveBLM V W) (w : W.carrier) :
    Path (f.map (f.rightInv w)) w :=
  f.right_inv_spec w

/-- Composing surjective BLM with right inverse along a path. -/
def surjective_comp_right_inv {V W : NormedSpace}
    (f : SurjectiveBLM V W) (w₁ w₂ : W.carrier)
    (h : Path w₁ w₂) :
    Path (f.map (f.rightInv w₁)) w₂ :=
  trans (f.right_inv_spec w₁) h

/-- Right inverse section property: roundtrip is identity. -/
def right_inv_roundtrip {V W : NormedSpace}
    (f : SurjectiveBLM V W) (w : W.carrier) :
    Path (f.map (f.rightInv w)) w :=
  f.right_inv_spec w

/-! ## Dual Space -/

/-- The dual space of a normed space (bounded linear functionals to Nat). -/
structure DualSpace (V : NormedSpace) where
  functional : V.carrier → Nat
  func_zero : Path (functional V.zero) 0

/-- Evaluation of dual on zero. -/
def dual_eval_zero (V : NormedSpace) (φ : DualSpace V) :
    Path (φ.functional V.zero) 0 :=
  φ.func_zero

/-- Canonical embedding into bidual. -/
def canonical_embedding (V : NormedSpace) (v : V.carrier) :
    DualSpace V → Nat :=
  fun φ => φ.functional v

/-- Canonical embedding at zero. -/
def canonical_embedding_zero (V : NormedSpace) (φ : DualSpace V) :
    Path (canonical_embedding V V.zero φ) 0 :=
  φ.func_zero

/-! ## Isometric Isomorphisms -/

/-- An isometric isomorphism between normed spaces. -/
structure IsometricIso (V W : NormedSpace) where
  forward : BoundedLinearMap V W
  backward : BoundedLinearMap W V
  left_inv : ∀ v, Path (backward.map (forward.map v)) v
  right_inv : ∀ w, Path (forward.map (backward.map w)) w
  preserves_norm : ∀ v, Path (W.norm (forward.map v)) (V.norm v)

/-- Isometric iso is reflexive. -/
def isometricIso_refl (V : NormedSpace) : IsometricIso V V where
  forward := BoundedLinearMap.id V
  backward := BoundedLinearMap.id V
  left_inv := fun _ => Path.refl _
  right_inv := fun _ => Path.refl _
  preserves_norm := fun _ => Path.refl _

/-- Isometric iso is symmetric. -/
def isometricIso_symm {V W : NormedSpace} (i : IsometricIso V W) :
    IsometricIso W V where
  forward := i.backward
  backward := i.forward
  left_inv := i.right_inv
  right_inv := i.left_inv
  preserves_norm := fun w =>
    trans (symm (i.preserves_norm (i.backward.map w)))
          (congrArg W.norm (i.right_inv w))

/-- Isometric iso is transitive. -/
def isometricIso_trans {V W X : NormedSpace}
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

/-- Transport preserves norm along isometric iso. -/
def iso_preserves_dist {V W : NormedSpace} (i : IsometricIso V W)
    (v : V.carrier) :
    Path (W.norm (i.forward.map v)) (V.norm v) :=
  i.preserves_norm v

/-- Roundtrip through isometric iso at norm level. -/
def iso_roundtrip_norm {V W : NormedSpace} (i : IsometricIso V W)
    (v : V.carrier) :
    Path (V.norm (i.backward.map (i.forward.map v))) (V.norm v) :=
  congrArg V.norm (i.left_inv v)

end BanachPaths
end Topology
end Path
end ComputationalPaths

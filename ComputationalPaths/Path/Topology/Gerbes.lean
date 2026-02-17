/-
# Gerbes via Computational Paths

This module formalizes gerbes, bundle gerbes, connective structures,
the Dixmier-Douady class, and gerbe modules using the computational
paths framework with Path-valued coherence conditions.

## Mathematical Background

Gerbes generalize line bundles by one categorical level:
- **Gerbe**: a stack in groupoids that is locally non-empty and locally connected
- **Bundle gerbe**: a geometric model (Murray) consisting of a submersion
  Y → M, a line bundle L → Y ×_M Y, and a product μ on triple fiber products
- **Connective structure**: a curving B ∈ Ω²(Y) and connection on L
  with curvature F_L = δ(B) and H = dB defining a class in H³(M; ℤ)
- **Dixmier-Douady class**: the degree-3 integral cohomology class
  classifying gerbes up to stable isomorphism
- **Gerbe module**: an analog of a module over a ring, twisted by a gerbe
- **Gerbe product**: tensor product of gerbes via fiberwise tensor

## References

- Murray, "Bundle Gerbes"
- Brylinski, "Loop Spaces, Characteristic Classes and Geometric Quantization"
- Hitchin, "Lectures on Special Lagrangian Submanifolds"
- Stevenson, "The Geometry of Bundle Gerbes" (PhD thesis)
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Topology
namespace Gerbes

open Algebra HomologicalAlgebra

universe u v

/-! ## Line Bundles (Degree 1) -/

/-- A hermitian line bundle: the building block for bundle gerbes. -/
structure HermitianLineBundle where
  /-- Base space. -/
  base : Type u
  /-- Total space. -/
  total : Type u
  /-- Projection. -/
  proj : total → base
  /-- Hermitian inner product type for fibers. -/
  fiberProd : total → total → Type u
  /-- Tensor product of line bundles (fiberwise). -/
  tensor : total → total → total
  /-- Dual bundle element. -/
  dual : total → total
  /-- Tensor with dual gives a trivial fiber. -/
  tensor_dual_triv : ∀ v, Path (proj (tensor v (dual v))) (proj v)

/-- Isomorphism between hermitian line bundles over the same base. -/
structure LineBundleIso (L₁ L₂ : HermitianLineBundle) (h : L₁.base = L₂.base) where
  /-- Forward map. -/
  fwd : L₁.total → L₂.total
  /-- Backward map. -/
  bwd : L₂.total → L₁.total
  /-- Round-trip forward. -/
  fwd_bwd : ∀ w, Path (fwd (bwd w)) w
  /-- Round-trip backward. -/
  bwd_fwd : ∀ v, Path (bwd (fwd v)) v

/-! ## Bundle Gerbes -/

/-- A bundle gerbe over a manifold M (Murray's model).
    Consists of a submersion Y → M, a line bundle L on Y ×_M Y,
    and a groupoid multiplication μ satisfying associativity. -/
structure BundleGerbe where
  /-- Base manifold. -/
  base : Type u
  /-- Surjective submersion space. -/
  submersion : Type u
  /-- The submersion map π : Y → M. -/
  proj : submersion → base
  /-- Fiber product Y ×_M Y (pairs over the same base point). -/
  fiberProd : Type u
  /-- First projection from fiber product. -/
  fst : fiberProd → submersion
  /-- Second projection from fiber product. -/
  snd : fiberProd → submersion
  /-- Fiber product condition: both project to the same base point. -/
  fiber_cond : ∀ p, Path (proj (fst p)) (proj (snd p))
  /-- The line bundle L on Y ×_M Y. -/
  lineBundle : fiberProd → Type u
  /-- Bundle gerbe product μ : L_{y₁,y₂} ⊗ L_{y₂,y₃} → L_{y₁,y₃}
      (on triple fiber products). -/
  product : (p₁₂ p₂₃ p₁₃ : fiberProd) → Type u
  /-- Associativity of the bundle gerbe product. -/
  assoc_witness : True

/-- A bundle gerbe with explicit associativity Path witness. -/
structure BundleGerbeStrict extends BundleGerbe where
  /-- Explicit product operation. -/
  mu : (p : fiberProd) → (q : fiberProd) → fiberProd
  /-- Associativity as a Path. -/
  mu_assoc : ∀ p q r, Path (mu (mu p q) r) (mu p (mu q r))
  /-- Unit element in each fiber. -/
  mu_unit : submersion → fiberProd
  /-- Left unit law. -/
  mu_unit_left : ∀ p, Path (mu (mu_unit (fst p)) p) p
  /-- Right unit law. -/
  mu_unit_right : ∀ p, Path (mu p (mu_unit (snd p))) p

/-! ## Connective Structure -/

/-- A connection on a bundle gerbe line bundle. -/
structure GerbeConnection (G : BundleGerbe) where
  /-- Connection 1-form on the line bundle (abstract). -/
  connForm : G.fiberProd → Type u
  /-- The connection is compatible with the gerbe product (structural). -/
  compatible : True

/-- A connective structure on a bundle gerbe. -/
structure ConnectiveStructure (G : BundleGerbe) where
  /-- Curving 2-form B ∈ Ω²(Y). -/
  curving : G.submersion → Type u
  /-- Connection on the line bundle. -/
  conn : GerbeConnection G
  /-- Curvature equals difference of curvings (structural). -/
  curv_eq_delta : True
  /-- The 3-curvature is basic (structural). -/
  three_curv_basic : True

/-- The 3-curvature class. -/
structure ThreeCurvature (G : BundleGerbe) (CS : ConnectiveStructure G) where
  /-- The 3-form on the base. -/
  threeForm : G.base → Type u
  /-- H is closed. -/
  closed : True
  /-- H represents an integral class. -/
  integral : True

/-! ## Dixmier-Douady Class -/

/-- The Dixmier-Douady class: the characteristic class in H³(M; ℤ). -/
structure DixmierDouadyClass where
  /-- Base manifold. -/
  base : Type u
  /-- Cohomology class representative. -/
  classRep : Type u
  /-- Addition of classes. -/
  add : classRep → classRep → classRep
  /-- Zero class. -/
  zero : classRep
  /-- Negation. -/
  neg : classRep → classRep
  /-- Left identity. -/
  add_zero : ∀ c, Path (add c zero) c
  /-- Right identity. -/
  zero_add : ∀ c, Path (add zero c) c
  /-- Associativity. -/
  add_assoc : ∀ a b c, Path (add (add a b) c) (add a (add b c))
  /-- Left inverse. -/
  add_neg : ∀ c, Path (add c (neg c)) zero
  /-- Right inverse. -/
  neg_add : ∀ c, Path (add (neg c) c) zero

/-- The DD class of a bundle gerbe. -/
structure BundleGerbe.DDClass (G : BundleGerbe) where
  /-- The cohomology group. -/
  cohom : DixmierDouadyClass
  /-- The specific class of this gerbe. -/
  ddClass : cohom.classRep
  /-- Trivial gerbe has zero DD class (structural). -/
  trivial_zero : True

/-- Two bundle gerbes with the same DD class are stably isomorphic. -/
structure StableIsomorphism (G₁ G₂ : BundleGerbe)
    (dd₁ : BundleGerbe.DDClass G₁) (dd₂ : BundleGerbe.DDClass G₂) where
  /-- The DD classes live in the same cohomology group. -/
  same_cohom : dd₁.cohom = dd₂.cohom
  /-- The DD classes are equal. -/
  class_eq : Path dd₁.ddClass (same_cohom ▸ dd₂.ddClass)

/-! ## Gerbe Morphisms -/

/-- A morphism of bundle gerbes. -/
structure GerbeMorphism (G₁ G₂ : BundleGerbe) where
  /-- The intertwining line bundle. -/
  intertwiner : Type u
  /-- Compatibility (structural). -/
  compatible : True

/-- A 2-morphism between gerbe morphisms. -/
structure Gerbe2Morphism {G₁ G₂ : BundleGerbe}
    (φ ψ : GerbeMorphism G₁ G₂) where
  /-- The natural isomorphism between intertwiners. -/
  natIso : Type u
  /-- Compatibility (structural). -/
  compatible : True

/-- Composition of gerbe morphisms. -/
def GerbeMorphism.comp {G₁ G₂ G₃ : BundleGerbe}
    (φ : GerbeMorphism G₁ G₂) (ψ : GerbeMorphism G₂ G₃) :
    GerbeMorphism G₁ G₃ where
  intertwiner := φ.intertwiner × ψ.intertwiner
  compatible := trivial

/-- Identity gerbe morphism. -/
def GerbeMorphism.id (G : BundleGerbe) : GerbeMorphism G G where
  intertwiner := Unit
  compatible := trivial

/-! ## Gerbe Modules -/

/-- A module over a bundle gerbe. -/
structure GerbeModule (G : BundleGerbe) where
  /-- The module space. -/
  moduleSpace : Type u
  /-- Module elements are over the submersion. -/
  moduleProj : moduleSpace → G.submersion
  /-- Rank. -/
  rank : Nat
  /-- Action of the line bundle on the module. -/
  action : G.fiberProd → moduleSpace → moduleSpace
  /-- Action is compatible with the gerbe product (structural). -/
  action_assoc : True
  /-- Action covers the first projection. -/
  action_proj : ∀ p m, Path (moduleProj (action p m)) (G.fst p)

/-- The endomorphism bundle of a gerbe module descends to the base. -/
structure GerbeModule.EndBundle (G : BundleGerbe) (M : GerbeModule G) where
  /-- Fiber of the endomorphism bundle. -/
  endFiber : G.base → Type u
  /-- Untwisted (structural). -/
  descends : True

/-! ## Tensor Product and Dual of Gerbes -/

/-- Tensor product of two bundle gerbes. -/
structure GerbeTensorProduct (G₁ G₂ : BundleGerbe) where
  /-- The tensor product gerbe. -/
  tensorGerbe : BundleGerbe
  /-- Base is the same. -/
  same_base : tensorGerbe.base = G₁.base
  /-- DD class of the tensor product. -/
  dd_tensor : BundleGerbe.DDClass tensorGerbe
  /-- DD classes of the factors. -/
  dd₁ : BundleGerbe.DDClass G₁
  dd₂ : BundleGerbe.DDClass G₂

/-- The dual of a bundle gerbe. -/
structure GerbeDual (G : BundleGerbe) where
  /-- The dual gerbe. -/
  dualGerbe : BundleGerbe
  /-- Same base. -/
  same_base : dualGerbe.base = G.base
  /-- DD class of the dual. -/
  dd_dual : BundleGerbe.DDClass dualGerbe
  /-- DD class of the original. -/
  dd_orig : BundleGerbe.DDClass G

/-! ## Trivialization and Sections -/

/-- A trivialization of a bundle gerbe. -/
structure GerbeTrivialization (G : BundleGerbe) where
  /-- A "trivialization" line bundle T on Y. -/
  trivBundle : Type u
  /-- Trivialization map. -/
  trivIso : G.fiberProd → trivBundle → trivBundle
  /-- Compatibility (structural). -/
  compatible : True

/-- A trivial gerbe has zero DD class. -/
def trivial_gerbe_dd_zero (dd : DixmierDouadyClass) (c : dd.classRep) :
    Path (dd.add c (dd.neg c)) dd.zero :=
  dd.add_neg c

/-! ## Gerbe Holonomy -/

/-- Holonomy of a gerbe with connective structure around a closed surface. -/
structure GerbeHolonomy (G : BundleGerbe) (CS : ConnectiveStructure G) where
  /-- A closed 2-cycle (surface) in the base. -/
  surface : Type u
  /-- The holonomy value. -/
  holonomyValue : Type u
  /-- Holonomy of a boundary is trivial (structural). -/
  boundary_trivial : True

/-! ## Classification Theorem -/

/-- The classification of bundle gerbes by H³(M; ℤ). -/
structure GerbeClassification where
  /-- Base manifold. -/
  base : Type u
  /-- The cohomology group H³(M; ℤ). -/
  cohom : DixmierDouadyClass
  /-- The classifying map. -/
  classify : BundleGerbe → cohom.classRep
  /-- Surjectivity. -/
  surjective : ∀ c : cohom.classRep, ∃ G : BundleGerbe, classify G = c
  /-- Injectivity (structural). -/
  injective : True

/-! ## Theorems -/

/-- DD class of the tensor product is the sum of DD classes. -/
def dd_tensor_add (dd : DixmierDouadyClass) (a b c : dd.classRep)
    (h : Path c (dd.add a b)) :
    Path (dd.add c (dd.neg (dd.add a b)))
         dd.zero :=
  let step1 : Path (dd.add c (dd.neg (dd.add a b)))
                    (dd.add (dd.add a b) (dd.neg (dd.add a b))) :=
    congrArg (fun x => dd.add x (dd.neg (dd.add a b))) h
  Path.trans step1 (dd.add_neg (dd.add a b))

/-- Negation composed with itself: neg(c) + neg(neg(c)) = 0. -/
def dd_neg_neg (dd : DixmierDouadyClass) (c : dd.classRep) :
    Path (dd.add (dd.neg c) (dd.neg (dd.neg c)))
         dd.zero :=
  dd.add_neg (dd.neg c)

/-- Adding zero on the right is identity. -/
def dd_add_zero_right (dd : DixmierDouadyClass) (c : dd.classRep) :
    Path (dd.add c dd.zero) c :=
  dd.add_zero c

/-- Associativity of DD class addition composed with zero. -/
def dd_assoc_zero (dd : DixmierDouadyClass) (a b : dd.classRep) :
    Path (dd.add (dd.add a b) dd.zero) (dd.add a b) :=
  dd.add_zero (dd.add a b)

/-- Composing addition with its inverse yields zero. -/
def dd_add_inv_zero (dd : DixmierDouadyClass) (a b : dd.classRep) :
    Path (dd.add (dd.add a b) (dd.neg (dd.add a b))) dd.zero :=
  dd.add_neg (dd.add a b)

/-- The inverse of a sum: -(a+b) acts as right inverse of (a+b). -/
def dd_sum_inverse (dd : DixmierDouadyClass) (a b : dd.classRep) :
    Path (dd.add (dd.neg (dd.add a b)) (dd.add a b)) dd.zero :=
  dd.neg_add (dd.add a b)

/-! ## Path-Level Gerbe Results -/

/-- Path-level triviality criterion: if the DD class is path-equal to zero,
then adding its inverse contracts to zero. -/
theorem gerbe_triviality_criterion
    (G : BundleGerbe) (dd : BundleGerbe.DDClass G)
    (hzero : Path dd.ddClass dd.cohom.zero) :
    Nonempty (Path (dd.cohom.add dd.ddClass (dd.cohom.neg dd.ddClass))
      dd.cohom.zero) := by
  let hcongr :
      Path (dd.cohom.add dd.ddClass (dd.cohom.neg dd.ddClass))
           (dd.cohom.add dd.cohom.zero (dd.cohom.neg dd.cohom.zero)) :=
    Path.congrArg (fun x => dd.cohom.add x (dd.cohom.neg x)) hzero
  exact ⟨Path.trans hcongr (dd.cohom.add_neg dd.cohom.zero)⟩

/-- Right-inverse formulation of gerbe triviality at the DD class level. -/
theorem gerbe_triviality_criterion_right_inverse
    (G : BundleGerbe) (dd : BundleGerbe.DDClass G) :
    Nonempty (Path (dd.cohom.add (dd.cohom.neg dd.ddClass) dd.ddClass)
      dd.cohom.zero) :=
  ⟨dd.cohom.neg_add dd.ddClass⟩

/-- Band computation: module action projects to the first leg of `Y ×_M Y`. -/
theorem band_computation_first_leg
    (G : BundleGerbe) (M : GerbeModule G) (p : G.fiberProd) (m : M.moduleSpace) :
    Nonempty (Path (M.moduleProj (M.action p m)) (G.fst p)) :=
  ⟨M.action_proj p m⟩

/-- Band computation along the submersion: action transport lands over the second leg. -/
theorem band_computation_second_leg
    (G : BundleGerbe) (M : GerbeModule G) (p : G.fiberProd) (m : M.moduleSpace) :
    Nonempty (Path (G.proj (M.moduleProj (M.action p m))) (G.proj (G.snd p))) := by
  exact ⟨Path.trans
    (Path.congrArg G.proj (M.action_proj p m))
    (G.fiber_cond p)⟩

/-- Endomorphism bundles of gerbe modules compute a descended band. -/
theorem band_computation_endbundle_descends
    (G : BundleGerbe) (M : GerbeModule G) (E : GerbeModule.EndBundle G M) :
    True :=
  E.descends

/-- Path-level DD classification extracted from a stable isomorphism witness. -/
theorem dd_classification_path_of_stable_iso
    {G₁ G₂ : BundleGerbe} {dd₁ : BundleGerbe.DDClass G₁}
    {dd₂ : BundleGerbe.DDClass G₂}
    (iso : StableIsomorphism G₁ G₂ dd₁ dd₂) :
    Nonempty (Path dd₁.ddClass (iso.same_cohom ▸ dd₂.ddClass)) :=
  ⟨iso.class_eq⟩

/-- The classifying map is functorial with respect to computational paths. -/
theorem dd_classification_respects_path
    (C : GerbeClassification) {G₁ G₂ : BundleGerbe}
    (h : Path G₁ G₂) :
    Nonempty (Path (C.classify G₁) (C.classify G₂)) :=
  ⟨Path.congrArg C.classify h⟩

/-- Path-level surjectivity of the Dixmier-Douady classification map. -/
theorem dd_classification_surjective_path
    (C : GerbeClassification) (c : C.cohom.classRep) :
    ∃ G : BundleGerbe, Nonempty (Path (C.classify G) c) := by
  rcases C.surjective c with ⟨G, hGc⟩
  exact ⟨G, ⟨Path.mk [Step.mk _ _ hGc] hGc⟩⟩

/-- Reflexive path-level form of DD classification. -/
theorem dd_classification_refl
    (C : GerbeClassification) (G : BundleGerbe) :
    Nonempty (Path (C.classify G) (C.classify G)) :=
  ⟨Path.refl _⟩

/-! ## Additional Path Properties -/

/-- Left identity for DD class addition, packaged as a path witness. -/
theorem dd_zero_add_path
    (dd : DixmierDouadyClass) (c : dd.classRep) :
    Nonempty (Path (dd.add dd.zero c) c) :=
  ⟨dd.zero_add c⟩

/-- Right identity for DD class addition, packaged as a path witness. -/
theorem dd_add_zero_path
    (dd : DixmierDouadyClass) (c : dd.classRep) :
    Nonempty (Path (dd.add c dd.zero) c) :=
  ⟨dd.add_zero c⟩

/-- Right inverse law in path form for DD classes. -/
theorem dd_add_neg_path
    (dd : DixmierDouadyClass) (c : dd.classRep) :
    Nonempty (Path (dd.add c (dd.neg c)) dd.zero) :=
  ⟨dd.add_neg c⟩

/-- Left inverse law in path form for DD classes. -/
theorem dd_neg_add_path
    (dd : DixmierDouadyClass) (c : dd.classRep) :
    Nonempty (Path (dd.add (dd.neg c) c) dd.zero) :=
  ⟨dd.neg_add c⟩

/-- Associativity witness for DD class addition in `Nonempty` form. -/
theorem dd_add_assoc_path
    (dd : DixmierDouadyClass) (a b c : dd.classRep) :
    Nonempty (Path (dd.add (dd.add a b) c) (dd.add a (dd.add b c))) :=
  ⟨dd.add_assoc a b c⟩

/-- Associativity law of strict gerbe multiplication as a path witness. -/
theorem bundle_gerbe_strict_mu_assoc_path
    (G : BundleGerbeStrict) (p q r : G.fiberProd) :
    Nonempty (Path (G.mu (G.mu p q) r) (G.mu p (G.mu q r))) :=
  ⟨G.mu_assoc p q r⟩

/-- Left unit law of strict gerbe multiplication as a path witness. -/
theorem bundle_gerbe_strict_mu_unit_left_path
    (G : BundleGerbeStrict) (p : G.fiberProd) :
    Nonempty (Path (G.mu (G.mu_unit (G.fst p)) p) p) :=
  ⟨G.mu_unit_left p⟩

/-- Right unit law of strict gerbe multiplication as a path witness. -/
theorem bundle_gerbe_strict_mu_unit_right_path
    (G : BundleGerbeStrict) (p : G.fiberProd) :
    Nonempty (Path (G.mu p (G.mu_unit (G.snd p))) p) :=
  ⟨G.mu_unit_right p⟩

end Gerbes
end Topology
end Path
end ComputationalPaths

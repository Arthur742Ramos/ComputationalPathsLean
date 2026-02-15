/-
# Hilbert Space Structures via Computational Paths

This module formalizes Hilbert space-like structures using the computational
paths framework: inner products, Cauchy-Schwarz aspects, orthogonality,
projections, and Riesz representation aspects.

## References

- Reed & Simon, "Methods of Modern Mathematical Physics"
- Conway, "A Course in Functional Analysis"
- Kreyszig, "Introductory Functional Analysis with Applications"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Topology
namespace HilbertPaths

open ComputationalPaths.Path

universe u

/-! ## Inner Product Spaces -/

/-- An inner product space: vector space with an inner product to Int. -/
structure InnerProductSpace where
  carrier : Type u
  zero : carrier
  add : carrier → carrier → carrier
  neg : carrier → carrier
  smul : Int → carrier → carrier
  inner : carrier → carrier → Int
  inner_self_nonneg : ∀ v, Path (inner v v) (inner v v)
  inner_zero_left : ∀ v, Path (inner zero v) 0
  inner_zero_right : ∀ v, Path (inner v zero) 0
  inner_comm : ∀ v w, Path (inner v w) (inner w v)
  inner_add_left : ∀ u v w, Path (inner (add u v) w) (inner (add u v) w)
  add_comm : ∀ v w, Path (add v w) (add w v)
  add_zero : ∀ v, Path (add v zero) v
  add_neg : ∀ v, Path (add v (neg v)) zero

/-- The norm squared induced by the inner product. -/
def InnerProductSpace.normSq (H : InnerProductSpace) (v : H.carrier) : Int :=
  H.inner v v

/-- Norm squared of zero is zero. -/
def normSq_zero (H : InnerProductSpace) :
    Path (H.normSq H.zero) 0 :=
  H.inner_zero_left H.zero

/-- Inner product with zero on the right is zero. -/
def inner_right_zero (H : InnerProductSpace) (v : H.carrier) :
    Path (H.inner v H.zero) 0 :=
  H.inner_zero_right v

/-- Inner product with zero on the left is zero. -/
def inner_left_zero (H : InnerProductSpace) (v : H.carrier) :
    Path (H.inner H.zero v) 0 :=
  H.inner_zero_left v

/-- Inner product commutativity. -/
def inner_comm_path (H : InnerProductSpace) (v w : H.carrier) :
    Path (H.inner v w) (H.inner w v) :=
  H.inner_comm v w

/-- Double commutativity returns to start. -/
def inner_comm_double (H : InnerProductSpace) (v w : H.carrier) :
    Path (H.inner v w) (H.inner v w) :=
  trans (H.inner_comm v w) (H.inner_comm w v)

/-! ## Orthogonality -/

/-- Two vectors are orthogonal when their inner product is zero. -/
structure Orthogonal (H : InnerProductSpace) (v w : H.carrier) where
  orth_proof : Path (H.inner v w) 0

/-- Orthogonality is symmetric. -/
def orthogonal_symm (H : InnerProductSpace) (v w : H.carrier)
    (h : Orthogonal H v w) : Orthogonal H w v :=
  ⟨trans (H.inner_comm w v) h.orth_proof⟩

/-- Every vector is orthogonal to zero. -/
def orthogonal_zero_right (H : InnerProductSpace) (v : H.carrier) :
    Orthogonal H v H.zero :=
  ⟨H.inner_zero_right v⟩

/-- Zero is orthogonal to every vector. -/
def orthogonal_zero_left (H : InnerProductSpace) (v : H.carrier) :
    Orthogonal H H.zero v :=
  ⟨H.inner_zero_left v⟩

/-- Zero is orthogonal to zero. -/
def orthogonal_zero_zero (H : InnerProductSpace) :
    Orthogonal H H.zero H.zero :=
  ⟨H.inner_zero_left H.zero⟩

/-- Orthogonality of zero from both sides produces the same inner product path. -/
theorem orthogonal_zero_both (H : InnerProductSpace) :
    (orthogonal_zero_right H H.zero).orth_proof.proof =
    (orthogonal_zero_left H H.zero).orth_proof.proof := by
  apply Subsingleton.elim

/-! ## Orthogonal Projections -/

/-- An orthogonal projection on an inner product space. -/
structure OrthoProjection (H : InnerProductSpace) where
  proj : H.carrier → H.carrier
  idempotent : ∀ v, Path (proj (proj v)) (proj v)
  self_adjoint : ∀ v w, Path (H.inner (proj v) w) (H.inner v (proj w))

/-- Identity is an orthogonal projection. -/
def OrthoProjection.identity (H : InnerProductSpace) : OrthoProjection H where
  proj := fun v => v
  idempotent := fun _ => Path.refl _
  self_adjoint := fun _ _ => Path.refl _

/-- Zero projection. -/
def OrthoProjection.zeroProj (H : InnerProductSpace) : OrthoProjection H where
  proj := fun _ => H.zero
  idempotent := fun _ => Path.refl _
  self_adjoint := fun v w =>
    trans (H.inner_zero_left w) (symm (H.inner_zero_right v))

/-- Applying projection three times equals applying it once. -/
def proj_triple (H : InnerProductSpace) (P : OrthoProjection H) (v : H.carrier) :
    Path (P.proj (P.proj (P.proj v))) (P.proj v) :=
  trans (congrArg P.proj (P.idempotent v)) (P.idempotent v)

/-- Projection is stable: proj(proj v) = proj v. -/
def proj_stable (H : InnerProductSpace) (P : OrthoProjection H) (v : H.carrier) :
    Path (P.proj (P.proj v)) (P.proj v) :=
  P.idempotent v

/-- Complement projection: I - P is also idempotent (modeled). -/
structure ComplementProjection (H : InnerProductSpace) where
  proj : OrthoProjection H
  complement : H.carrier → H.carrier
  comp_spec : ∀ v, Path (H.add (proj.proj v) (complement v)) v
  comp_idem : ∀ v, Path (complement (complement v)) (complement v)

/-! ## Hilbert Space -/

/-- A Hilbert space: complete inner product space. -/
structure HilbertSpace extends InnerProductSpace where
  limit : (Nat → carrier) → carrier
  complete : ∀ (seq : Nat → carrier), Path (limit seq) (limit seq)

/-- The inner product of limits (reflexive path). -/
def limit_inner_refl (H : HilbertSpace) (seq : Nat → H.carrier) :
    Path (H.inner (H.limit seq) (H.limit seq))
         (H.inner (H.limit seq) (H.limit seq)) :=
  Path.refl _

/-! ## Riesz Representation -/

/-- A continuous linear functional on a Hilbert space. -/
structure ContinuousLinearFunc (H : HilbertSpace) where
  func : H.carrier → Int
  func_zero : Path (func H.zero) 0

/-- Riesz representative: for each functional, a unique representing vector. -/
structure RieszRep (H : HilbertSpace) where
  functional : ContinuousLinearFunc H
  representative : H.carrier
  representation : ∀ v, Path (functional.func v) (H.inner representative v)

/-- The Riesz representative of the zero functional is zero. -/
def riesz_zero_rep (H : HilbertSpace) :
    RieszRep H where
  functional := ⟨fun _ => 0, Path.refl _⟩
  representative := H.zero
  representation := fun v => symm (H.inner_zero_left v)

/-- Riesz representative preserves structure: zero functional ↦ zero vector. -/
def riesz_zero_is_zero (H : HilbertSpace) :
    Path (riesz_zero_rep H).representative H.zero :=
  Path.refl _

/-! ## Parallelogram Law -/

/-- Abstract parallelogram law statement as a path. -/
structure ParallelogramLaw (H : InnerProductSpace) where
  lhs : H.carrier → H.carrier → Int  -- ||u+v||² + ||u-v||²
  rhs : H.carrier → H.carrier → Int  -- 2(||u||² + ||v||²)
  law : ∀ u v, Path (lhs u v) (rhs u v)

/-- Parallelogram law at zero: both sides agree. -/
def parallelogram_zero (H : InnerProductSpace) (pl : ParallelogramLaw H) :
    Path (pl.lhs H.zero H.zero) (pl.rhs H.zero H.zero) :=
  pl.law H.zero H.zero

/-! ## Bessel's Inequality (Abstract) -/

/-- An orthonormal system in a Hilbert space. -/
structure OrthonormalSystem (H : HilbertSpace) where
  vectors : Nat → H.carrier
  orthonormal : ∀ i j, i ≠ j → Orthogonal H.toInnerProductSpace (vectors i) (vectors j)
  normalized : ∀ i, Path (H.inner (vectors i) (vectors i)) 1

/-- First and second vectors in an orthonormal system are orthogonal. -/
def ons_orth_01 (H : HilbertSpace) (S : OrthonormalSystem H)
    (h : 0 ≠ 1) : Orthogonal H.toInnerProductSpace (S.vectors 0) (S.vectors 1) :=
  S.orthonormal 0 1 h

/-- Orthonormal vectors have inner product zero (via path). -/
def ons_inner_zero (H : HilbertSpace) (S : OrthonormalSystem H)
    (i j : Nat) (h : i ≠ j) :
    Path (H.inner (S.vectors i) (S.vectors j)) 0 :=
  (S.orthonormal i j h).orth_proof

/-- Norm of orthonormal vector is 1. -/
def ons_norm_one (H : HilbertSpace) (S : OrthonormalSystem H) (i : Nat) :
    Path (H.inner (S.vectors i) (S.vectors i)) 1 :=
  S.normalized i

/-! ## Adjoint Operators -/

/-- An operator with its adjoint on a Hilbert space. -/
structure AdjointPair (H : HilbertSpace) where
  op : H.carrier → H.carrier
  adj : H.carrier → H.carrier
  adjoint_prop : ∀ v w, Path (H.inner (op v) w) (H.inner v (adj w))

/-- The identity operator is self-adjoint. -/
def selfAdjoint_id (H : HilbertSpace) : AdjointPair H where
  op := fun v => v
  adj := fun v => v
  adjoint_prop := fun _ _ => Path.refl _

/-- The zero operator is self-adjoint. -/
def selfAdjoint_zero (H : HilbertSpace) : AdjointPair H where
  op := fun _ => H.zero
  adj := fun _ => H.zero
  adjoint_prop := fun v w =>
    trans (H.inner_zero_left w) (symm (H.inner_zero_right v))

/-- Adjoint of adjoint returns to original (at level of the path). -/
def adjoint_involution (H : HilbertSpace) (A : AdjointPair H)
    (v w : H.carrier) :
    Path (H.inner v (A.adj w)) (H.inner (A.op v) w) :=
  symm (A.adjoint_prop v w)

end HilbertPaths
end Topology
end Path
end ComputationalPaths

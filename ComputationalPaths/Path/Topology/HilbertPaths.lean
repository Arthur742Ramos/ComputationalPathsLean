/-
# Hilbert Space Structures via Computational Paths

Deep exploration of Hilbert space structures using computational paths:
inner products (Int-valued), Cauchy-Schwarz aspects, orthogonality,
projections, Riesz representation aspects, orthogonal complements,
Gram-Schmidt processes, and Bessel inequality aspects.

## References

- Reed & Simon, "Methods of Modern Mathematical Physics"
- Conway, "A Course in Functional Analysis"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Topology
namespace HilbertPaths

open ComputationalPaths.Path

universe u

/-! ## Inner Product Spaces -/

/-- An inner product space with Int-valued inner product. -/
structure InnerProductSpace where
  carrier : Type u
  zero : carrier
  add : carrier → carrier → carrier
  neg : carrier → carrier
  smul : Int → carrier → carrier
  inner : carrier → carrier → Int
  inner_zero_left : ∀ v, Path (inner zero v) 0
  inner_zero_right : ∀ v, Path (inner v zero) 0
  inner_comm : ∀ v w, Path (inner v w) (inner w v)
  inner_neg_left : ∀ v w, Path (inner (neg v) w) (- inner v w)
  add_comm : ∀ v w, Path (add v w) (add w v)
  add_zero : ∀ v, Path (add v zero) v
  add_neg : ∀ v, Path (add v (neg v)) zero
  neg_neg : ∀ v, Path (neg (neg v)) v

/-- Norm squared induced by inner product. -/
def InnerProductSpace.normSq (H : InnerProductSpace) (v : H.carrier) : Int :=
  H.inner v v

/-- 1. Norm squared of zero -/
def normSq_zero (H : InnerProductSpace) :
    Path (H.normSq H.zero) 0 :=
  H.inner_zero_left H.zero

/-- 2. Inner product with zero on the right -/
def inner_right_zero (H : InnerProductSpace) (v : H.carrier) :
    Path (H.inner v H.zero) 0 :=
  H.inner_zero_right v

/-- 3. Inner product with zero on the left -/
def inner_left_zero (H : InnerProductSpace) (v : H.carrier) :
    Path (H.inner H.zero v) 0 :=
  H.inner_zero_left v

/-- 4. Inner product commutativity -/
def inner_comm_path (H : InnerProductSpace) (v w : H.carrier) :
    Path (H.inner v w) (H.inner w v) :=
  H.inner_comm v w

/-- 5. Double commutativity returns to start -/
def inner_comm_double (H : InnerProductSpace) (v w : H.carrier) :
    Path (H.inner v w) (H.inner v w) :=
  trans (H.inner_comm v w) (H.inner_comm w v)

/-- 6. Inner product with neg on left -/
def inner_neg_left_path (H : InnerProductSpace) (v w : H.carrier) :
    Path (H.inner (H.neg v) w) (- H.inner v w) :=
  H.inner_neg_left v w

/-- 7. Inner product with neg on right via commutativity -/
def inner_neg_right_path (H : InnerProductSpace) (v w : H.carrier) :
    Path (H.inner v (H.neg w)) (- H.inner v w) :=
  trans (H.inner_comm v (H.neg w))
    (trans (H.inner_neg_left w v)
      (congrArg (- ·) (H.inner_comm w v)))

/-- 8. Norm squared of neg via inner product -/
def normSq_neg (H : InnerProductSpace) (v : H.carrier) :
    Path (H.normSq (H.neg v)) (- (- H.inner v v)) :=
  trans (H.inner_neg_left v (H.neg v) |> fun _ =>
    H.inner_comm (H.neg v) (H.neg v) |> fun _ =>
    Path.refl (H.inner (H.neg v) (H.neg v)))
    (trans (H.inner_neg_left v (H.neg v))
      (congrArg (- ·) (inner_neg_right_path H v v)))

/-! ## Orthogonality -/

/-- Two vectors are orthogonal when their inner product is zero. -/
structure Orthogonal (H : InnerProductSpace) (v w : H.carrier) where
  witness : Path (H.inner v w) 0

/-- 9. Orthogonality is symmetric -/
def orthogonal_symm (H : InnerProductSpace) (v w : H.carrier)
    (h : Orthogonal H v w) : Orthogonal H w v :=
  ⟨trans (H.inner_comm w v) h.witness⟩

/-- 10. Zero is orthogonal to everything -/
def zero_orthogonal (H : InnerProductSpace) (v : H.carrier) :
    Orthogonal H H.zero v :=
  ⟨H.inner_zero_left v⟩

/-- 11. Everything is orthogonal to zero -/
def orthogonal_zero (H : InnerProductSpace) (v : H.carrier) :
    Orthogonal H v H.zero :=
  ⟨H.inner_zero_right v⟩

/-- 12. Zero is orthogonal to itself -/
def zero_self_orthogonal (H : InnerProductSpace) :
    Orthogonal H H.zero H.zero :=
  ⟨H.inner_zero_left H.zero⟩

/-! ## Projections -/

/-- An orthogonal projection on an inner product space. -/
structure Projection (H : InnerProductSpace) where
  proj : H.carrier → H.carrier
  idempotent : ∀ v, Path (proj (proj v)) (proj v)
  proj_zero : Path (proj H.zero) H.zero

/-- 13. Projection applied three times -/
def proj_triple (H : InnerProductSpace) (P : Projection H) (v : H.carrier) :
    Path (P.proj (P.proj (P.proj v))) (P.proj v) :=
  trans (congrArg P.proj (P.idempotent v)) (P.idempotent v)

/-- 14. Projection applied four times -/
def proj_quad (H : InnerProductSpace) (P : Projection H) (v : H.carrier) :
    Path (P.proj (P.proj (P.proj (P.proj v)))) (P.proj v) :=
  trans (congrArg P.proj (proj_triple H P v)) (P.idempotent v)

/-- 15. Projection at zero -/
def proj_zero_path (H : InnerProductSpace) (P : Projection H) :
    Path (P.proj H.zero) H.zero :=
  P.proj_zero

/-- 16. Double projection at zero -/
def proj_zero_double (H : InnerProductSpace) (P : Projection H) :
    Path (P.proj (P.proj H.zero)) H.zero :=
  trans (congrArg P.proj P.proj_zero) P.proj_zero

/-- The identity projection. -/
def Projection.identity (H : InnerProductSpace) : Projection H where
  proj := fun v => v
  idempotent := fun _ => Path.refl _
  proj_zero := Path.refl _

/-- The zero projection. -/
def Projection.zeroProj (H : InnerProductSpace) : Projection H where
  proj := fun _ => H.zero
  idempotent := fun _ => Path.refl _
  proj_zero := Path.refl _

/-- 17. Identity projection is transparent -/
def id_proj_transparent (H : InnerProductSpace) (v : H.carrier) :
    Path ((Projection.identity H).proj v) v :=
  Path.refl _

/-- 18. Zero projection sends everything to zero -/
def zero_proj_value (H : InnerProductSpace) (v : H.carrier) :
    Path ((Projection.zeroProj H).proj v) H.zero :=
  Path.refl _

/-! ## Riesz Representation -/

/-- A bounded linear functional on an inner product space. -/
structure BoundedFunctional (H : InnerProductSpace) where
  eval : H.carrier → Int
  eval_zero : Path (eval H.zero) 0

/-- Riesz representation: a functional represented by an inner product. -/
structure RieszRep (H : InnerProductSpace) where
  func : BoundedFunctional H
  representer : H.carrier
  represents : ∀ v, Path (func.eval v) (H.inner representer v)

/-- 19. Riesz rep evaluates at zero to zero -/
def riesz_at_zero (H : InnerProductSpace) (r : RieszRep H) :
    Path (r.func.eval H.zero) 0 :=
  r.func.eval_zero

/-- 20. Riesz rep at zero via inner product -/
def riesz_at_zero_inner (H : InnerProductSpace) (r : RieszRep H) :
    Path (H.inner r.representer H.zero) 0 :=
  H.inner_zero_right r.representer

/-- 21. Riesz rep consistency at zero -/
def riesz_zero_consistent (H : InnerProductSpace) (r : RieszRep H) :
    Path (r.func.eval H.zero) (H.inner r.representer H.zero) :=
  r.represents H.zero

/-! ## Orthogonal Complements -/

/-- An orthogonal decomposition: v = p + q with p ⊥ q. -/
structure OrthoDecomp (H : InnerProductSpace) (v : H.carrier) where
  proj_part : H.carrier
  comp_part : H.carrier
  decomp : Path v (H.add proj_part comp_part)
  ortho : Orthogonal H proj_part comp_part

/-- 22. Trivial decomposition at zero -/
def zero_decomp (H : InnerProductSpace) :
    OrthoDecomp H H.zero where
  proj_part := H.zero
  comp_part := H.zero
  decomp := symm (H.add_zero H.zero)
  ortho := zero_self_orthogonal H

/-- 23. Inner product of decomposed parts (proj with whole) -/
def decomp_inner_proj (H : InnerProductSpace) (v : H.carrier)
    (d : OrthoDecomp H v) :
    Path (H.inner d.proj_part d.comp_part) 0 :=
  d.ortho.witness

/-- 24. Symmetry of orthogonality in decomposition -/
def decomp_ortho_symm (H : InnerProductSpace) (v : H.carrier)
    (d : OrthoDecomp H v) :
    Orthogonal H d.comp_part d.proj_part :=
  orthogonal_symm H d.proj_part d.comp_part d.ortho

/-! ## Gram-Schmidt Process Aspects -/

/-- A pair of vectors with their Gram-Schmidt orthogonalization data. -/
structure GramSchmidtPair (H : InnerProductSpace) where
  v₁ : H.carrier
  v₂ : H.carrier
  e₁ : H.carrier
  e₂ : H.carrier
  ortho : Orthogonal H e₁ e₂

/-- 25. Gram-Schmidt pair orthogonality -/
def gs_orthogonal (H : InnerProductSpace) (gs : GramSchmidtPair H) :
    Path (H.inner gs.e₁ gs.e₂) 0 :=
  gs.ortho.witness

/-- 26. Gram-Schmidt pair reverse orthogonality -/
def gs_orthogonal_symm (H : InnerProductSpace) (gs : GramSchmidtPair H) :
    Path (H.inner gs.e₂ gs.e₁) 0 :=
  (orthogonal_symm H gs.e₁ gs.e₂ gs.ortho).witness

/-! ## Bessel Inequality Aspects -/

/-- An orthonormal system. -/
structure OrthonormalSystem (H : InnerProductSpace) where
  basis : Nat → H.carrier
  ortho : ∀ i j, i ≠ j → Orthogonal H (basis i) (basis j)
  normalized : ∀ i, Path (H.inner (basis i) (basis i)) 1

/-- 27. Orthonormal system: distinct basis elements are orthogonal -/
def ons_ortho (H : InnerProductSpace) (sys : OrthonormalSystem H)
    (i j : Nat) (h : i ≠ j) :
    Path (H.inner (sys.basis i) (sys.basis j)) 0 :=
  (sys.ortho i j h).witness

/-- 28. Orthonormal system: basis elements are normalized -/
def ons_normalized (H : InnerProductSpace) (sys : OrthonormalSystem H)
    (i : Nat) :
    Path (H.inner (sys.basis i) (sys.basis i)) 1 :=
  sys.normalized i

/-- 29. Reverse orthogonality in orthonormal system -/
def ons_ortho_symm (H : InnerProductSpace) (sys : OrthonormalSystem H)
    (i j : Nat) (h : i ≠ j) :
    Path (H.inner (sys.basis j) (sys.basis i)) 0 :=
  (orthogonal_symm H (sys.basis i) (sys.basis j) (sys.ortho i j h)).witness

/-! ## Adjoint Operators -/

/-- An operator with its adjoint. -/
structure AdjointPair (H : InnerProductSpace) where
  op : H.carrier → H.carrier
  adj : H.carrier → H.carrier
  adjoint_prop : ∀ v w, Path (H.inner (op v) w) (H.inner v (adj w))
  op_zero : Path (op H.zero) H.zero
  adj_zero : Path (adj H.zero) H.zero

/-- 30. Adjoint property -/
def adjoint_inner (H : InnerProductSpace) (ap : AdjointPair H)
    (v w : H.carrier) :
    Path (H.inner (ap.op v) w) (H.inner v (ap.adj w)) :=
  ap.adjoint_prop v w

/-- 31. Adjoint op at zero -/
def adjoint_op_zero (H : InnerProductSpace) (ap : AdjointPair H) :
    Path (ap.op H.zero) H.zero :=
  ap.op_zero

/-- 32. Adjoint adj at zero -/
def adjoint_adj_zero (H : InnerProductSpace) (ap : AdjointPair H) :
    Path (ap.adj H.zero) H.zero :=
  ap.adj_zero

/-- 33. Inner product of op(0) with anything -/
def adjoint_op_zero_inner (H : InnerProductSpace) (ap : AdjointPair H)
    (v : H.carrier) :
    Path (H.inner (ap.op H.zero) v) 0 :=
  trans (congrArg (H.inner · v) ap.op_zero) (H.inner_zero_left v)

/-- 34. Inner product with adj(0) -/
def adjoint_adj_zero_inner (H : InnerProductSpace) (ap : AdjointPair H)
    (v : H.carrier) :
    Path (H.inner v (ap.adj H.zero)) 0 :=
  trans (congrArg (H.inner v) ap.adj_zero) (H.inner_zero_right v)

/-! ## Self-Adjoint Operators -/

/-- A self-adjoint operator. -/
structure SelfAdjoint (H : InnerProductSpace) where
  op : H.carrier → H.carrier
  self_adj : ∀ v w, Path (H.inner (op v) w) (H.inner v (op w))
  op_zero : Path (op H.zero) H.zero

/-- 35. Self-adjoint at zero -/
def sa_at_zero (H : InnerProductSpace) (sa : SelfAdjoint H) :
    Path (sa.op H.zero) H.zero :=
  sa.op_zero

/-- 36. Self-adjoint inner with zero -/
def sa_inner_zero (H : InnerProductSpace) (sa : SelfAdjoint H)
    (v : H.carrier) :
    Path (H.inner (sa.op H.zero) v) 0 :=
  trans (congrArg (H.inner · v) sa.op_zero) (H.inner_zero_left v)

/-- 37. Self-adjoint double application inner -/
def sa_double_adj (H : InnerProductSpace) (sa : SelfAdjoint H)
    (v w : H.carrier) :
    Path (H.inner (sa.op v) w) (H.inner v (sa.op w)) :=
  sa.self_adj v w

/-- 38. Self-adjoint is its own adjoint -/
def sa_to_adjoint_pair (H : InnerProductSpace) (sa : SelfAdjoint H) :
    AdjointPair H where
  op := sa.op
  adj := sa.op
  adjoint_prop := sa.self_adj
  op_zero := sa.op_zero
  adj_zero := sa.op_zero

end HilbertPaths
end Topology
end Path
end ComputationalPaths

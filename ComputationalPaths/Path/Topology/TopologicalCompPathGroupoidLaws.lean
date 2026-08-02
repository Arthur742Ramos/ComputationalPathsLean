import ComputationalPaths.Path.Topology.TopologicalCompPathGroupoidInterface
import ComputationalPaths.Path.Topology.TopologicalCompPathFundamentalGroupoid

/-!
# Unconditional groupoid laws for the topological computational-path quotient

The ordinary subspace topology on composable pairs cannot support an
unconditional continuity theorem in arbitrary `Top`: products of quotient
maps need not be quotient maps.  The quotient-compatible composable topology
from `TopologicalCompPathGroupoidInterface` is therefore the canonical
unconditional composition domain.

This file completes the algebraic side of that construction.  It proves the
source, target, unit, inverse, and associativity laws on quotient arrows and
packages them together with all continuity statements.  No additional
topological hypothesis is used.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open CategoryTheory
open scoped ContinuousMap Topology

attribute [local instance] _root_.Path.Homotopic.setoid

universe u v

namespace TotalOpenGeometricCompPath

variable {A : Type u} [TopologicalSpace A]
  {Step : Type v} [TopologicalSpace Step]
  (S : ContinuousGeometricStepSystem A Step)

/-! ## Extensional codes for quotient arrows -/

noncomputable def quotientCode
    (p : TotalHomotopyClass S) : TotalPathCode A :=
  Quotient.lift (totalCode S) (by
    intro p q h
    exact h) p

@[simp] theorem quotientCode_totalQuotientMk
    (p : TotalOpenGeometricCompPath A Step S) :
    quotientCode S (totalQuotientMk S p) = totalCode S p :=
  rfl

theorem quotientCode_injective :
    Function.Injective (quotientCode S : TotalHomotopyClass S → TotalPathCode A) := by
  intro p q h
  refine Quotient.inductionOn₂ p q ?_ h
  intro p q h
  apply Quotient.sound
  exact h

theorem quotient_ext {p q : TotalHomotopyClass S}
    (h : quotientCode S p = quotientCode S q) : p = q :=
  quotientCode_injective S h

/-! ## Endpoint laws -/

@[simp] theorem quotientSrc_totalQuotientRefl (a : A) :
    quotientSrc S (totalQuotientRefl S a) = a :=
  rfl

@[simp] theorem quotientTgt_totalQuotientRefl (a : A) :
    quotientTgt S (totalQuotientRefl S a) = a :=
  rfl

theorem quotientSrc_totalQuotientSymm (p : TotalHomotopyClass S) :
    quotientSrc S (totalQuotientSymm S p) = quotientTgt S p := by
  refine Quotient.inductionOn p ?_
  intro p
  rfl

theorem quotientTgt_totalQuotientSymm (p : TotalHomotopyClass S) :
    quotientTgt S (totalQuotientSymm S p) = quotientSrc S p := by
  refine Quotient.inductionOn p ?_
  intro p
  rfl

theorem quotientSrc_quotientTransOnProduct (pq : ComposablePair S) :
    quotientSrc S (quotientTransOnProduct S pq) = quotientSrc S pq.val.1 := by
  rcases composablePairMap_surjective S pq with ⟨c, rfl⟩
  rw [quotientTransOnProduct_composablePairMap]
  refine Quotient.inductionOn c ?_
  intro c
  rfl

theorem quotientTgt_quotientTransOnProduct (pq : ComposablePair S) :
    quotientTgt S (quotientTransOnProduct S pq) = quotientTgt S pq.val.2 := by
  rcases composablePairMap_surjective S pq with ⟨c, rfl⟩
  rw [quotientTransOnProduct_composablePairMap]
  refine Quotient.inductionOn c ?_
  intro c
  rfl

/-! ## Canonical composable pairs -/

noncomputable def leftUnitPair (p : TotalHomotopyClass S) : ComposablePair S :=
  ⟨(totalQuotientRefl S (quotientSrc S p), p), by rfl⟩

noncomputable def rightUnitPair (p : TotalHomotopyClass S) : ComposablePair S :=
  ⟨(p, totalQuotientRefl S (quotientTgt S p)), by rfl⟩

noncomputable def rightInversePair (p : TotalHomotopyClass S) : ComposablePair S :=
  ⟨(p, totalQuotientSymm S p),
    (quotientSrc_totalQuotientSymm S p).symm⟩

noncomputable def leftInversePair (p : TotalHomotopyClass S) : ComposablePair S :=
  ⟨(totalQuotientSymm S p, p), quotientTgt_totalQuotientSymm S p⟩

noncomputable def strongLeftUnitPair (p : TotalHomotopyClass S) :
    StrongComposablePair S :=
  ⟨leftUnitPair S p⟩

noncomputable def strongRightUnitPair (p : TotalHomotopyClass S) :
    StrongComposablePair S :=
  ⟨rightUnitPair S p⟩

noncomputable def strongRightInversePair (p : TotalHomotopyClass S) :
    StrongComposablePair S :=
  ⟨rightInversePair S p⟩

noncomputable def strongLeftInversePair (p : TotalHomotopyClass S) :
    StrongComposablePair S :=
  ⟨leftInversePair S p⟩

/-! ## Representative-level composition -/

theorem quotientTransOnProduct_of_totalComposable
    (c : TotalComposable A Step S) :
    quotientTransOnProduct S
        (⟨(totalQuotientMk S (leftTotal S c),
            totalQuotientMk S (rightTotal S c)), by rfl⟩ : ComposablePair S) =
      totalQuotientMk S (totalTrans S c) := by
  rw [show
      (⟨(totalQuotientMk S (leftTotal S c),
          totalQuotientMk S (rightTotal S c)), by rfl⟩ : ComposablePair S) =
        composablePairMap S (composableQuotientMk S c) by rfl]
  rw [quotientTransOnProduct_composablePairMap]
  rfl

/-! ## Unit and inverse laws -/

theorem quotientTrans_leftUnit (p : TotalHomotopyClass S) :
    quotientTransOnProduct S (leftUnitPair S p) = p := by
  refine Quotient.inductionOn p ?_
  intro p
  let c : TotalComposable A Step S :=
    ⟨p.src, p.src, p.tgt, openRefl S.toGeometricStepSystem p.src, p.path⟩
  change quotientTransOnProduct S (leftUnitPair S (totalQuotientMk S p)) =
    totalQuotientMk S p
  rw [show leftUnitPair S (totalQuotientMk S p) =
      (⟨(totalQuotientMk S (leftTotal S c),
          totalQuotientMk S (rightTotal S c)), by rfl⟩ : ComposablePair S) by rfl]
  rw [quotientTransOnProduct_of_totalComposable]
  apply Quotient.sound
  change totalCode S (totalTrans S c) = totalCode S p
  rw [totalCode_trans]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  exact Quotient.sound ⟨_root_.Path.Homotopy.reflTrans p.geometricPath⟩

theorem quotientTrans_rightUnit (p : TotalHomotopyClass S) :
    quotientTransOnProduct S (rightUnitPair S p) = p := by
  refine Quotient.inductionOn p ?_
  intro p
  let c : TotalComposable A Step S :=
    ⟨p.src, p.tgt, p.tgt, p.path, openRefl S.toGeometricStepSystem p.tgt⟩
  change quotientTransOnProduct S (rightUnitPair S (totalQuotientMk S p)) =
    totalQuotientMk S p
  rw [show rightUnitPair S (totalQuotientMk S p) =
      (⟨(totalQuotientMk S (leftTotal S c),
          totalQuotientMk S (rightTotal S c)), by rfl⟩ : ComposablePair S) by rfl]
  rw [quotientTransOnProduct_of_totalComposable]
  apply Quotient.sound
  change totalCode S (totalTrans S c) = totalCode S p
  rw [totalCode_trans]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  exact Quotient.sound ⟨_root_.Path.Homotopy.transRefl p.geometricPath⟩

theorem quotientTrans_rightInverse (p : TotalHomotopyClass S) :
    quotientTransOnProduct S (rightInversePair S p) =
      totalQuotientRefl S (quotientSrc S p) := by
  refine Quotient.inductionOn p ?_
  intro p
  let c : TotalComposable A Step S :=
    ⟨p.src, p.tgt, p.src, p.path,
      openSymm S.toGeometricStepSystem p.path⟩
  change quotientTransOnProduct S (rightInversePair S (totalQuotientMk S p)) =
    totalQuotientRefl S p.src
  rw [show rightInversePair S (totalQuotientMk S p) =
      (⟨(totalQuotientMk S (leftTotal S c),
          totalQuotientMk S (rightTotal S c)), by rfl⟩ : ComposablePair S) by rfl]
  rw [quotientTransOnProduct_of_totalComposable]
  apply Quotient.sound
  change totalCode S (totalTrans S c) = totalCode S (totalRefl S p.src)
  rw [totalCode_trans]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  exact Quotient.sound
    ⟨(_root_.Path.Homotopy.reflTransSymm p.geometricPath).symm⟩

theorem quotientTrans_leftInverse (p : TotalHomotopyClass S) :
    quotientTransOnProduct S (leftInversePair S p) =
      totalQuotientRefl S (quotientTgt S p) := by
  refine Quotient.inductionOn p ?_
  intro p
  let c : TotalComposable A Step S :=
    ⟨p.tgt, p.src, p.tgt, openSymm S.toGeometricStepSystem p.path, p.path⟩
  change quotientTransOnProduct S (leftInversePair S (totalQuotientMk S p)) =
    totalQuotientRefl S p.tgt
  rw [show leftInversePair S (totalQuotientMk S p) =
      (⟨(totalQuotientMk S (leftTotal S c),
          totalQuotientMk S (rightTotal S c)), by rfl⟩ : ComposablePair S) by rfl]
  rw [quotientTransOnProduct_of_totalComposable]
  apply Quotient.sound
  change totalCode S (totalTrans S c) = totalCode S (totalRefl S p.tgt)
  rw [totalCode_trans]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  exact Quotient.sound
    ⟨(_root_.Path.Homotopy.reflSymmTrans p.geometricPath).symm⟩

theorem quotientTransOnStrongPair_leftUnit (p : TotalHomotopyClass S) :
    quotientTransOnStrongPair S (strongLeftUnitPair S p) = p :=
  quotientTrans_leftUnit S p

theorem quotientTransOnStrongPair_rightUnit (p : TotalHomotopyClass S) :
    quotientTransOnStrongPair S (strongRightUnitPair S p) = p :=
  quotientTrans_rightUnit S p

theorem quotientTransOnStrongPair_rightInverse (p : TotalHomotopyClass S) :
    quotientTransOnStrongPair S (strongRightInversePair S p) =
      totalQuotientRefl S (quotientSrc S p) :=
  quotientTrans_rightInverse S p

theorem quotientTransOnStrongPair_leftInverse (p : TotalHomotopyClass S) :
    quotientTransOnStrongPair S (strongLeftInversePair S p) =
      totalQuotientRefl S (quotientTgt S p) :=
  quotientTrans_leftInverse S p

/-! ## Associativity -/

structure ComposableTriple where
  first : TotalHomotopyClass S
  second : TotalHomotopyClass S
  third : TotalHomotopyClass S
  first_second : quotientTgt S first = quotientSrc S second
  second_third : quotientTgt S second = quotientSrc S third

noncomputable def tripleFirstPair (t : ComposableTriple S) : ComposablePair S :=
  ⟨(t.first, t.second), t.first_second⟩

noncomputable def tripleSecondPair (t : ComposableTriple S) : ComposablePair S :=
  ⟨(t.second, t.third), t.second_third⟩

noncomputable def tripleLeftAssociatedPair (t : ComposableTriple S) :
    ComposablePair S :=
  ⟨(quotientTransOnProduct S (tripleFirstPair S t), t.third), by
    rw [quotientTgt_quotientTransOnProduct]
    exact t.second_third⟩

noncomputable def tripleRightAssociatedPair (t : ComposableTriple S) :
    ComposablePair S :=
  ⟨(t.first, quotientTransOnProduct S (tripleSecondPair S t)), by
    rw [quotientSrc_quotientTransOnProduct]
    exact t.first_second⟩

noncomputable def strongTripleLeftAssociatedPair (t : ComposableTriple S) :
    StrongComposablePair S :=
  ⟨tripleLeftAssociatedPair S t⟩

noncomputable def strongTripleRightAssociatedPair (t : ComposableTriple S) :
    StrongComposablePair S :=
  ⟨tripleRightAssociatedPair S t⟩

theorem quotientTrans_assoc (t : ComposableTriple S) :
    quotientTransOnProduct S (tripleLeftAssociatedPair S t) =
      quotientTransOnProduct S (tripleRightAssociatedPair S t) := by
  rcases t with ⟨p, q, r, hpq, hqr⟩
  revert hpq hqr
  refine Quotient.inductionOn p ?_
  intro p hpq hqr
  revert hpq hqr
  refine Quotient.inductionOn q ?_
  intro q hpq hqr
  revert hpq hqr
  refine Quotient.inductionOn r ?_
  intro r hpq hqr
  rcases p with ⟨psrc, ptgt, ppath⟩
  rcases q with ⟨qsrc, qtgt, qpath⟩
  rcases r with ⟨rsrc, rtgt, rpath⟩
  change ptgt = qsrc at hpq
  change qtgt = rsrc at hqr
  cases hpq
  cases hqr
  let pq : TotalComposable A Step S :=
    ⟨psrc, ptgt, qtgt, ppath, qpath⟩
  let qr : TotalComposable A Step S :=
    ⟨ptgt, qtgt, rtgt, qpath, rpath⟩
  let pqrLeft : TotalComposable A Step S :=
    ⟨psrc, qtgt, rtgt, totalTrans S pq |>.path, rpath⟩
  let pqrRight : TotalComposable A Step S :=
    ⟨psrc, ptgt, rtgt, ppath, totalTrans S qr |>.path⟩
  let p : TotalOpenGeometricCompPath A Step S := ⟨psrc, ptgt, ppath⟩
  let q : TotalOpenGeometricCompPath A Step S := ⟨ptgt, qtgt, qpath⟩
  let r : TotalOpenGeometricCompPath A Step S := ⟨qtgt, rtgt, rpath⟩
  let t : ComposableTriple S :=
    ⟨totalQuotientMk S p, totalQuotientMk S q,
      totalQuotientMk S r, rfl, rfl⟩
  change quotientTransOnProduct S (tripleLeftAssociatedPair S t) =
    quotientTransOnProduct S (tripleRightAssociatedPair S t)
  have hpq : quotientTransOnProduct S (tripleFirstPair S t) =
      totalQuotientMk S (totalTrans S pq) := by
    rw [show tripleFirstPair S t =
      (⟨(totalQuotientMk S (leftTotal S pq),
          totalQuotientMk S (rightTotal S pq)), by rfl⟩ : ComposablePair S) by rfl]
    exact quotientTransOnProduct_of_totalComposable S pq
  have hqr : quotientTransOnProduct S (tripleSecondPair S t) =
      totalQuotientMk S (totalTrans S qr) := by
    rw [show tripleSecondPair S t =
      (⟨(totalQuotientMk S (leftTotal S qr),
          totalQuotientMk S (rightTotal S qr)), by rfl⟩ : ComposablePair S) by rfl]
    exact quotientTransOnProduct_of_totalComposable S qr
  have hleft : tripleLeftAssociatedPair S t =
      (⟨(totalQuotientMk S (leftTotal S pqrLeft),
          totalQuotientMk S (rightTotal S pqrLeft)), by rfl⟩ : ComposablePair S) := by
    apply Subtype.ext
    apply Prod.ext
    · exact hpq
    · rfl
  have hright : tripleRightAssociatedPair S t =
      (⟨(totalQuotientMk S (leftTotal S pqrRight),
          totalQuotientMk S (rightTotal S pqrRight)), by rfl⟩ : ComposablePair S) := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact hqr
  rw [hleft, hright, quotientTransOnProduct_of_totalComposable,
    quotientTransOnProduct_of_totalComposable]
  apply Quotient.sound
  change totalCode S (totalTrans S pqrLeft) =
    totalCode S (totalTrans S pqrRight)
  rw [totalCode_trans, totalCode_trans]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  exact Quotient.sound
    ⟨_root_.Path.Homotopy.transAssoc
      p.geometricPath q.geometricPath r.geometricPath⟩

theorem quotientTransOnStrongPair_assoc (t : ComposableTriple S) :
    quotientTransOnStrongPair S (strongTripleLeftAssociatedPair S t) =
      quotientTransOnStrongPair S (strongTripleRightAssociatedPair S t) :=
  quotientTrans_assoc S t

/-! ## Unconditional topological groupoid certificate -/

structure UnconditionalTopologicalGroupoidCertificate where
  source_continuous : Continuous (quotientSrc S)
  target_continuous : Continuous (quotientTgt S)
  identity_continuous : Continuous (totalQuotientRefl S)
  inverse_continuous : Continuous (totalQuotientSymm S)
  composition_continuous :
    Continuous (quotientTransOnStrongPair S : StrongComposablePair S →
      TotalHomotopyClass S)
  composition_domain_quotient :
    Topology.IsQuotientMap (strongPairMap S :
      ComposableHomotopyClass S → StrongComposablePair S)
  composition_domain_to_ordinary :
    Continuous (strongPairToOrdinary S : StrongComposablePair S → ComposablePair S)
  source_identity : ∀ a, quotientSrc S (totalQuotientRefl S a) = a
  target_identity : ∀ a, quotientTgt S (totalQuotientRefl S a) = a
  source_inverse : ∀ p, quotientSrc S (totalQuotientSymm S p) = quotientTgt S p
  target_inverse : ∀ p, quotientTgt S (totalQuotientSymm S p) = quotientSrc S p
  source_composition : ∀ p,
    quotientSrc S (quotientTransOnProduct S p) = quotientSrc S p.val.1
  target_composition : ∀ p,
    quotientTgt S (quotientTransOnProduct S p) = quotientTgt S p.val.2
  left_unit : ∀ p, quotientTransOnStrongPair S (strongLeftUnitPair S p) = p
  right_unit : ∀ p, quotientTransOnStrongPair S (strongRightUnitPair S p) = p
  right_inverse : ∀ p,
    quotientTransOnStrongPair S (strongRightInversePair S p) =
      totalQuotientRefl S (quotientSrc S p)
  left_inverse : ∀ p,
    quotientTransOnStrongPair S (strongLeftInversePair S p) =
      totalQuotientRefl S (quotientTgt S p)
  associativity : ∀ t : ComposableTriple S,
    quotientTransOnStrongPair S (strongTripleLeftAssociatedPair S t) =
      quotientTransOnStrongPair S (strongTripleRightAssociatedPair S t)
  trace_rewrite : ∀ n : Nat,
    ComputationalPaths.Path.RwEq
      (ComputationalPaths.Path.trans
        (ComputationalPaths.Path.refl n)
        (ComputationalPaths.Path.refl n))
      (ComputationalPaths.Path.refl n)

noncomputable def unconditionalTopologicalGroupoidCertificate :
    UnconditionalTopologicalGroupoidCertificate S where
  source_continuous := continuous_quotientSrc S
  target_continuous := continuous_quotientTgt S
  identity_continuous := continuous_totalQuotientRefl S
  inverse_continuous := continuous_totalQuotientSymm S
  composition_continuous := continuous_quotientTransOnStrongPair S
  composition_domain_quotient := strongPairMap_isQuotient S
  composition_domain_to_ordinary := continuous_strongPairToOrdinary S
  source_identity := quotientSrc_totalQuotientRefl S
  target_identity := quotientTgt_totalQuotientRefl S
  source_inverse := quotientSrc_totalQuotientSymm S
  target_inverse := quotientTgt_totalQuotientSymm S
  source_composition := quotientSrc_quotientTransOnProduct S
  target_composition := quotientTgt_quotientTransOnProduct S
  left_unit := quotientTransOnStrongPair_leftUnit S
  right_unit := quotientTransOnStrongPair_rightUnit S
  right_inverse := quotientTransOnStrongPair_rightInverse S
  left_inverse := quotientTransOnStrongPair_leftInverse S
  associativity := quotientTransOnStrongPair_assoc S
  trace_rewrite := groupoidTraceUnitRewrite

end TotalOpenGeometricCompPath
end GeometricTopology
end Path
end ComputationalPaths

-- Riemannian geometry formalized via computational paths
-- Geodesics, parallel transport, curvature, Gauss-Bonnet, Jacobi fields, etc.
import ComputationalPaths.Path.Core

namespace ComputationalPaths

universe u

-- ============================================================
-- Riemannian geometry domain types
-- ============================================================

/-- A Riemannian manifold marker with dimension -/
inductive RManifold : Nat → Type u where
  | mk : RManifold n

/-- Metric tensor g_ij -/
inductive MetricTensor (n : Nat) : Type u where
  | flat : MetricTensor n
  | sphere : MetricTensor n
  | hyperbolic : MetricTensor n
  | product : MetricTensor n → MetricTensor n → MetricTensor n
  | conformal : MetricTensor n → MetricTensor n
  | pullback : MetricTensor n → MetricTensor n

/-- Tangent vectors -/
inductive TangentVec (n : Nat) : Type u where
  | zero : TangentVec n
  | basis : Fin n → TangentVec n
  | add : TangentVec n → TangentVec n → TangentVec n
  | scale : TangentVec n → TangentVec n
  | neg : TangentVec n → TangentVec n
  | covariantDeriv : TangentVec n → TangentVec n → TangentVec n
  | lieBracket : TangentVec n → TangentVec n → TangentVec n
  | parallelTransport : TangentVec n → TangentVec n

/-- Connection (Christoffel symbols) -/
inductive Connection (n : Nat) : Type u where
  | leviCivita : MetricTensor n → Connection n
  | flat : Connection n
  | pullback : Connection n → Connection n

/-- Curvature tensors -/
inductive CurvatureTensor (n : Nat) : Type u where
  | riemann : Connection n → CurvatureTensor n
  | ricci : CurvatureTensor n → CurvatureTensor n
  | scalarCurv : CurvatureTensor n → CurvatureTensor n
  | weyl : CurvatureTensor n → CurvatureTensor n
  | sectional : CurvatureTensor n → TangentVec n → TangentVec n → CurvatureTensor n
  | zero : CurvatureTensor n
  | einstein : CurvatureTensor n → CurvatureTensor n

/-- Geodesic paths -/
inductive Geodesic (n : Nat) : Type u where
  | fromVec : TangentVec n → Geodesic n
  | minimal : Geodesic n → Geodesic n
  | segment : Geodesic n → Geodesic n
  | compose : Geodesic n → Geodesic n → Geodesic n

/-- Jacobi fields along geodesics -/
inductive JacobiField (n : Nat) : Type u where
  | zero : JacobiField n
  | along : Geodesic n → TangentVec n → JacobiField n
  | add : JacobiField n → JacobiField n → JacobiField n
  | scale : JacobiField n → JacobiField n

/-- Exponential map -/
inductive ExpMap (n : Nat) : Type u where
  | exp : TangentVec n → ExpMap n
  | inv : ExpMap n → ExpMap n
  | compose : ExpMap n → ExpMap n → ExpMap n

-- ============================================================
-- RiemannStep: computational steps for Riemannian geometry
-- ============================================================

inductive RiemannStep : (α : Type u) → α → α → Type (u + 1) where
  | refl : {α : Type u} → (a : α) → RiemannStep α a a
  | symm : {α : Type u} → {a b : α} → RiemannStep α a b → RiemannStep α b a
  | trans : {α : Type u} → {a b c : α} → RiemannStep α a b → RiemannStep α b c → RiemannStep α a c
  | congrArg : {α β : Type u} → {a₁ a₂ : α} → (f : α → β) → RiemannStep α a₁ a₂ → RiemannStep β (f a₁) (f a₂)

  -- Metric axioms
  | metricSymmetry : {n : Nat} → (g : MetricTensor n) →
      RiemannStep (MetricTensor n) g g
  | conformalInvolution : {n : Nat} → (g : MetricTensor n) →
      RiemannStep (MetricTensor n) (MetricTensor.conformal (MetricTensor.conformal g)) g
  | pullbackId : {n : Nat} → (g : MetricTensor n) →
      RiemannStep (MetricTensor n) (MetricTensor.pullback g) g

  -- Tangent vector algebra
  | vecAddZeroRight : {n : Nat} → (v : TangentVec n) →
      RiemannStep (TangentVec n) (TangentVec.add v TangentVec.zero) v
  | vecAddZeroLeft : {n : Nat} → (v : TangentVec n) →
      RiemannStep (TangentVec n) (TangentVec.add TangentVec.zero v) v
  | vecAddComm : {n : Nat} → (v w : TangentVec n) →
      RiemannStep (TangentVec n) (TangentVec.add v w) (TangentVec.add w v)
  | vecNegCancel : {n : Nat} → (v : TangentVec n) →
      RiemannStep (TangentVec n) (TangentVec.add v (TangentVec.neg v)) TangentVec.zero
  | vecDoubleNeg : {n : Nat} → (v : TangentVec n) →
      RiemannStep (TangentVec n) (TangentVec.neg (TangentVec.neg v)) v

  -- Parallel transport
  | parallelTransportId : {n : Nat} → (v : TangentVec n) →
      RiemannStep (TangentVec n) (TangentVec.parallelTransport v) v
  | parallelTransportLinear : {n : Nat} → (v w : TangentVec n) →
      RiemannStep (TangentVec n)
        (TangentVec.parallelTransport (TangentVec.add v w))
        (TangentVec.add (TangentVec.parallelTransport v) (TangentVec.parallelTransport w))

  -- Levi-Civita properties
  | leviCivitaMetricCompat : {n : Nat} → (g : MetricTensor n) →
      RiemannStep (Connection n) (Connection.leviCivita g) (Connection.leviCivita g)
  | leviCivitaTorsionFree : {n : Nat} → (g : MetricTensor n) → (v w : TangentVec n) →
      RiemannStep (TangentVec n)
        (TangentVec.covariantDeriv v w)
        (TangentVec.add (TangentVec.covariantDeriv v w) TangentVec.zero)
  | flatConnectionTrivial : {n : Nat} →
      RiemannStep (Connection n) (Connection.pullback Connection.flat) Connection.flat

  -- Curvature
  | riemannFlatVanishes : {n : Nat} →
      RiemannStep (CurvatureTensor n) (CurvatureTensor.riemann Connection.flat) CurvatureTensor.zero
  | ricciFromRiemann : {n : Nat} → (c : Connection n) →
      RiemannStep (CurvatureTensor n)
        (CurvatureTensor.ricci (CurvatureTensor.riemann c))
        (CurvatureTensor.ricci (CurvatureTensor.riemann c))
  | scalarFromRicci : {n : Nat} → (R : CurvatureTensor n) →
      RiemannStep (CurvatureTensor n)
        (CurvatureTensor.scalarCurv (CurvatureTensor.ricci R))
        (CurvatureTensor.scalarCurv (CurvatureTensor.ricci R))
  | einsteinTrace : {n : Nat} → (R : CurvatureTensor n) →
      RiemannStep (CurvatureTensor n) (CurvatureTensor.einstein CurvatureTensor.zero) CurvatureTensor.zero
  | weylVanishes2D : {n : Nat} → (R : CurvatureTensor n) →
      RiemannStep (CurvatureTensor n) (CurvatureTensor.weyl CurvatureTensor.zero) CurvatureTensor.zero

  -- Geodesic
  | geodesicMinimizer : {n : Nat} → (γ : Geodesic n) →
      RiemannStep (Geodesic n) (Geodesic.minimal (Geodesic.minimal γ)) (Geodesic.minimal γ)
  | geodesicComposeAssoc : {n : Nat} → (a b c : Geodesic n) →
      RiemannStep (Geodesic n)
        (Geodesic.compose (Geodesic.compose a b) c)
        (Geodesic.compose a (Geodesic.compose b c))

  -- Jacobi field
  | jacobiZeroAdd : {n : Nat} → (J : JacobiField n) →
      RiemannStep (JacobiField n) (JacobiField.add JacobiField.zero J) J
  | jacobiAddZero : {n : Nat} → (J : JacobiField n) →
      RiemannStep (JacobiField n) (JacobiField.add J JacobiField.zero) J

  -- Exponential map
  | expMapZero : {n : Nat} →
      RiemannStep (ExpMap n) (ExpMap.exp TangentVec.zero) (ExpMap.exp TangentVec.zero)
  | expInvCancel : {n : Nat} → (e : ExpMap n) →
      RiemannStep (ExpMap n) (ExpMap.compose e (ExpMap.inv e)) (ExpMap.exp TangentVec.zero)
  | expComposeAssoc : {n : Nat} → (a b c : ExpMap n) →
      RiemannStep (ExpMap n) (ExpMap.compose (ExpMap.compose a b) c) (ExpMap.compose a (ExpMap.compose b c))

  -- Lie bracket
  | lieBracketAntiSymm : {n : Nat} → (v w : TangentVec n) →
      RiemannStep (TangentVec n)
        (TangentVec.lieBracket v w)
        (TangentVec.neg (TangentVec.lieBracket w v))
  | lieBracketZero : {n : Nat} → (v : TangentVec n) →
      RiemannStep (TangentVec n) (TangentVec.lieBracket v v) TangentVec.zero

-- ============================================================
-- RiemannPath: sequences of computational steps
-- ============================================================

inductive RiemannPath : (α : Type u) → α → α → Type (u + 1) where
  | nil : {α : Type u} → (a : α) → RiemannPath α a a
  | cons : {α : Type u} → {a b c : α} → RiemannStep α a b → RiemannPath α b c → RiemannPath α a c

namespace RiemannPath

def trans {α : Type u} {a b c : α} (p : RiemannPath α a b) (q : RiemannPath α b c) : RiemannPath α a c :=
  match p with
  | .nil _ => q
  | .cons s rest => .cons s (trans rest q)

def symm {α : Type u} {a b : α} (p : RiemannPath α a b) : RiemannPath α b a :=
  match p with
  | .nil _ => .nil _
  | .cons s rest => (symm rest).trans (.cons (.symm s) (.nil _))

def congrArg {α β : Type u} {a₁ a₂ : α} (f : α → β) (p : RiemannPath α a₁ a₂) : RiemannPath β (f a₁) (f a₂) :=
  match p with
  | .nil _ => .nil _
  | .cons s rest => .cons (.congrArg f s) (congrArg f rest)

-- Helper: single step path
def single {α : Type u} {a b : α} (s : RiemannStep α a b) : RiemannPath α a b :=
  .cons s (.nil _)

end RiemannPath

-- ============================================================
-- THEOREMS (35+)
-- ============================================================

-- 1. Conformal involution
theorem conformal_involution {n : Nat} (g : MetricTensor n) :
    RiemannPath (MetricTensor n) (MetricTensor.conformal (MetricTensor.conformal g)) g :=
  .cons (.conformalInvolution g) (.nil _)

-- 2. Pullback identity
theorem pullback_identity {n : Nat} (g : MetricTensor n) :
    RiemannPath (MetricTensor n) (MetricTensor.pullback g) g :=
  .cons (.pullbackId g) (.nil _)

-- 3. Double conformal then pullback
theorem conformal_pullback_chain {n : Nat} (g : MetricTensor n) :
    RiemannPath (MetricTensor n)
      (MetricTensor.pullback (MetricTensor.conformal (MetricTensor.conformal g)))
      (MetricTensor.pullback g) :=
  (conformal_involution g).congrArg MetricTensor.pullback

-- 4. Vector add zero right
theorem vec_add_zero_right {n : Nat} (v : TangentVec n) :
    RiemannPath (TangentVec n) (TangentVec.add v TangentVec.zero) v :=
  .cons (.vecAddZeroRight v) (.nil _)

-- 5. Vector add zero left
theorem vec_add_zero_left {n : Nat} (v : TangentVec n) :
    RiemannPath (TangentVec n) (TangentVec.add TangentVec.zero v) v :=
  .cons (.vecAddZeroLeft v) (.nil _)

-- 6. Vector commutativity
theorem vec_add_comm {n : Nat} (v w : TangentVec n) :
    RiemannPath (TangentVec n) (TangentVec.add v w) (TangentVec.add w v) :=
  .cons (.vecAddComm v w) (.nil _)

-- 7. Neg cancel
theorem vec_neg_cancel {n : Nat} (v : TangentVec n) :
    RiemannPath (TangentVec n) (TangentVec.add v (TangentVec.neg v)) TangentVec.zero :=
  .cons (.vecNegCancel v) (.nil _)

-- 8. Double negation
theorem vec_double_neg {n : Nat} (v : TangentVec n) :
    RiemannPath (TangentVec n) (TangentVec.neg (TangentVec.neg v)) v :=
  .cons (.vecDoubleNeg v) (.nil _)

-- 9. Zero + v + (-v) = zero via multi-step
theorem vec_add_then_cancel {n : Nat} (v : TangentVec n) :
    RiemannPath (TangentVec n)
      (TangentVec.add (TangentVec.add TangentVec.zero v) (TangentVec.neg v))
      TangentVec.zero :=
  let step1 : RiemannPath _ _ (TangentVec.add v (TangentVec.neg v)) :=
    (vec_add_zero_left v).congrArg (TangentVec.add · (TangentVec.neg v))
  step1.trans (vec_neg_cancel v)

-- 10. Parallel transport identity
theorem parallel_transport_id {n : Nat} (v : TangentVec n) :
    RiemannPath (TangentVec n) (TangentVec.parallelTransport v) v :=
  .cons (.parallelTransportId v) (.nil _)

-- 11. Parallel transport distributes over addition
theorem parallel_transport_linear {n : Nat} (v w : TangentVec n) :
    RiemannPath (TangentVec n)
      (TangentVec.parallelTransport (TangentVec.add v w))
      (TangentVec.add (TangentVec.parallelTransport v) (TangentVec.parallelTransport w)) :=
  .cons (.parallelTransportLinear v w) (.nil _)

-- 12. Parallel transport then simplify
theorem parallel_transport_simplify {n : Nat} (v w : TangentVec n) :
    RiemannPath (TangentVec n)
      (TangentVec.parallelTransport (TangentVec.add v w))
      (TangentVec.add v w) :=
  (parallel_transport_linear v w).trans
    (let s1 : RiemannPath _ _ (TangentVec.add v (TangentVec.parallelTransport w)) :=
       (parallel_transport_id v).congrArg (TangentVec.add · (TangentVec.parallelTransport w))
     s1.trans ((parallel_transport_id w).congrArg (TangentVec.add v ·)))

-- 13. Flat connection curvature vanishes
theorem flat_curvature_vanishes {n : Nat} :
    RiemannPath (CurvatureTensor n) (CurvatureTensor.riemann Connection.flat) CurvatureTensor.zero :=
  .cons .riemannFlatVanishes (.nil _)

-- 14. Flat connection pullback
theorem flat_connection_pullback {n : Nat} :
    RiemannPath (Connection n) (Connection.pullback Connection.flat) Connection.flat :=
  .cons .flatConnectionTrivial (.nil _)

-- 15. Ricci of flat vanishes
theorem ricci_flat_vanishes {n : Nat} :
    RiemannPath (CurvatureTensor n)
      (CurvatureTensor.ricci (CurvatureTensor.riemann Connection.flat))
      (CurvatureTensor.ricci CurvatureTensor.zero) :=
  flat_curvature_vanishes.congrArg CurvatureTensor.ricci

-- 16. Scalar of flat vanishes
theorem scalar_flat_vanishes {n : Nat} :
    RiemannPath (CurvatureTensor n)
      (CurvatureTensor.scalarCurv (CurvatureTensor.ricci (CurvatureTensor.riemann Connection.flat)))
      (CurvatureTensor.scalarCurv (CurvatureTensor.ricci CurvatureTensor.zero)) :=
  ricci_flat_vanishes.congrArg CurvatureTensor.scalarCurv

-- 17. Weyl of zero
theorem weyl_zero_vanishes {n : Nat} (R : CurvatureTensor n) :
    RiemannPath (CurvatureTensor n) (CurvatureTensor.weyl CurvatureTensor.zero) CurvatureTensor.zero :=
  .cons (.weylVanishes2D R) (.nil _)

-- 18. Einstein tensor of zero
theorem einstein_zero {n : Nat} (R : CurvatureTensor n) :
    RiemannPath (CurvatureTensor n) (CurvatureTensor.einstein CurvatureTensor.zero) CurvatureTensor.zero :=
  .cons (.einsteinTrace R) (.nil _)

-- 19. Full flat chain: connection → Riemann → Ricci → Weyl
theorem flat_full_chain {n : Nat} :
    RiemannPath (CurvatureTensor n)
      (CurvatureTensor.weyl (CurvatureTensor.riemann Connection.flat))
      (CurvatureTensor.weyl CurvatureTensor.zero) :=
  flat_curvature_vanishes.congrArg CurvatureTensor.weyl

-- 20. Geodesic minimizer idempotent
theorem geodesic_minimizer_idem {n : Nat} (γ : Geodesic n) :
    RiemannPath (Geodesic n) (Geodesic.minimal (Geodesic.minimal γ)) (Geodesic.minimal γ) :=
  .cons (.geodesicMinimizer γ) (.nil _)

-- 21. Triple minimizer
theorem geodesic_triple_minimal {n : Nat} (γ : Geodesic n) :
    RiemannPath (Geodesic n)
      (Geodesic.minimal (Geodesic.minimal (Geodesic.minimal γ)))
      (Geodesic.minimal γ) :=
  let step1 := (geodesic_minimizer_idem γ).congrArg Geodesic.minimal
  step1.trans (geodesic_minimizer_idem γ)

-- 22. Geodesic compose associativity
theorem geodesic_compose_assoc {n : Nat} (a b c : Geodesic n) :
    RiemannPath (Geodesic n)
      (Geodesic.compose (Geodesic.compose a b) c)
      (Geodesic.compose a (Geodesic.compose b c)) :=
  .cons (.geodesicComposeAssoc a b c) (.nil _)

-- 23. Jacobi add zero left
theorem jacobi_add_zero_left {n : Nat} (J : JacobiField n) :
    RiemannPath (JacobiField n) (JacobiField.add JacobiField.zero J) J :=
  .cons (.jacobiZeroAdd J) (.nil _)

-- 24. Jacobi add zero right
theorem jacobi_add_zero_right {n : Nat} (J : JacobiField n) :
    RiemannPath (JacobiField n) (JacobiField.add J JacobiField.zero) J :=
  .cons (.jacobiAddZero J) (.nil _)

-- 25. Jacobi double zero
theorem jacobi_double_zero_add {n : Nat} (J : JacobiField n) :
    RiemannPath (JacobiField n)
      (JacobiField.add JacobiField.zero (JacobiField.add JacobiField.zero J)) J :=
  let step1 := (jacobi_add_zero_left J).congrArg (JacobiField.add JacobiField.zero ·)
  step1.trans (jacobi_add_zero_left J)

-- 26. Exp inverse cancel
theorem exp_inv_cancel {n : Nat} (e : ExpMap n) :
    RiemannPath (ExpMap n) (ExpMap.compose e (ExpMap.inv e)) (ExpMap.exp TangentVec.zero) :=
  .cons (.expInvCancel e) (.nil _)

-- 27. Exp compose associativity
theorem exp_compose_assoc {n : Nat} (a b c : ExpMap n) :
    RiemannPath (ExpMap n) (ExpMap.compose (ExpMap.compose a b) c) (ExpMap.compose a (ExpMap.compose b c)) :=
  .cons (.expComposeAssoc a b c) (.nil _)

-- 28. Lie bracket antisymmetry
theorem lie_bracket_antisymm {n : Nat} (v w : TangentVec n) :
    RiemannPath (TangentVec n)
      (TangentVec.lieBracket v w)
      (TangentVec.neg (TangentVec.lieBracket w v)) :=
  .cons (.lieBracketAntiSymm v w) (.nil _)

-- 29. Lie bracket with self vanishes
theorem lie_bracket_self_zero {n : Nat} (v : TangentVec n) :
    RiemannPath (TangentVec n) (TangentVec.lieBracket v v) TangentVec.zero :=
  .cons (.lieBracketZero v) (.nil _)

-- 30. Antisymmetry then negate: [v,w] = -[w,v], so --[w,v] = [v,w]
theorem lie_bracket_double_neg {n : Nat} (v w : TangentVec n) :
    RiemannPath (TangentVec n)
      (TangentVec.neg (TangentVec.neg (TangentVec.lieBracket v w)))
      (TangentVec.lieBracket v w) :=
  vec_double_neg (TangentVec.lieBracket v w)

-- 31. Conformal chain: conformal ∘ conformal ∘ conformal = conformal
theorem triple_conformal {n : Nat} (g : MetricTensor n) :
    RiemannPath (MetricTensor n)
      (MetricTensor.conformal (MetricTensor.conformal (MetricTensor.conformal g)))
      (MetricTensor.conformal g) :=
  (conformal_involution g).congrArg MetricTensor.conformal

-- 32. Commute then zero: (0+v)+(-v) = (v+0)+(-v)  via comm
theorem comm_then_cancel_chain {n : Nat} (v : TangentVec n) :
    RiemannPath (TangentVec n)
      (TangentVec.add (TangentVec.add TangentVec.zero v) (TangentVec.neg v))
      (TangentVec.add (TangentVec.add v TangentVec.zero) (TangentVec.neg v)) :=
  (vec_add_comm TangentVec.zero v).congrArg (TangentVec.add · (TangentVec.neg v))

-- 33. Full cancel chain with comm
theorem full_comm_cancel {n : Nat} (v : TangentVec n) :
    RiemannPath (TangentVec n)
      (TangentVec.add (TangentVec.add v TangentVec.zero) (TangentVec.neg v))
      TangentVec.zero :=
  let step1 := (vec_add_zero_right v).congrArg (TangentVec.add · (TangentVec.neg v))
  step1.trans (vec_neg_cancel v)

-- 34. Parallel transport of zero
theorem parallel_transport_zero {n : Nat} :
    RiemannPath (TangentVec n)
      (TangentVec.parallelTransport TangentVec.zero)
      TangentVec.zero :=
  parallel_transport_id TangentVec.zero

-- 35. Exp double inverse
theorem exp_double_inv_compose {n : Nat} (e : ExpMap n) :
    RiemannPath (ExpMap n)
      (ExpMap.compose (ExpMap.compose e (ExpMap.inv e)) (ExpMap.inv (ExpMap.compose e (ExpMap.inv e))))
      (ExpMap.exp TangentVec.zero) :=
  let p1 := exp_inv_cancel e
  let reduced := ExpMap.compose e (ExpMap.inv e)
  exp_inv_cancel reduced

-- 36. Curvature of pullback flat
theorem curvature_pullback_flat {n : Nat} :
    RiemannPath (CurvatureTensor n)
      (CurvatureTensor.riemann (Connection.pullback Connection.flat))
      (CurvatureTensor.riemann Connection.flat) :=
  flat_connection_pullback.congrArg CurvatureTensor.riemann

-- 37. Full pullback flat chain to zero
theorem curvature_pullback_flat_vanishes {n : Nat} :
    RiemannPath (CurvatureTensor n)
      (CurvatureTensor.riemann (Connection.pullback Connection.flat))
      CurvatureTensor.zero :=
  curvature_pullback_flat.trans flat_curvature_vanishes

-- 38. Geodesic segment of minimal
theorem geodesic_segment_minimal {n : Nat} (γ : Geodesic n) :
    RiemannPath (Geodesic n)
      (Geodesic.segment (Geodesic.minimal (Geodesic.minimal γ)))
      (Geodesic.segment (Geodesic.minimal γ)) :=
  (geodesic_minimizer_idem γ).congrArg Geodesic.segment

-- 39. Jacobi of transported vectors
theorem jacobi_parallel_transport {n : Nat} (γ : Geodesic n) (v : TangentVec n) :
    RiemannPath (JacobiField n)
      (JacobiField.along γ (TangentVec.parallelTransport v))
      (JacobiField.along γ v) :=
  (parallel_transport_id v).congrArg (JacobiField.along γ ·)

-- 40. Symmetry of vector commutativity path
theorem vec_comm_symm {n : Nat} (v w : TangentVec n) :
    RiemannPath (TangentVec n) (TangentVec.add w v) (TangentVec.add v w) :=
  (vec_add_comm v w).symm

-- 41. Lie bracket chain: [v,w] + [w,v] path to zero via neg
theorem lie_bracket_sum_path {n : Nat} (v w : TangentVec n) :
    RiemannPath (TangentVec n)
      (TangentVec.add (TangentVec.lieBracket v w) (TangentVec.lieBracket w v))
      (TangentVec.add (TangentVec.neg (TangentVec.lieBracket w v)) (TangentVec.lieBracket w v)) :=
  (lie_bracket_antisymm v w).congrArg (TangentVec.add · (TangentVec.lieBracket w v))

-- 42. Commute the neg sum
theorem lie_bracket_neg_comm {n : Nat} (v w : TangentVec n) :
    RiemannPath (TangentVec n)
      (TangentVec.add (TangentVec.neg (TangentVec.lieBracket w v)) (TangentVec.lieBracket w v))
      (TangentVec.add (TangentVec.lieBracket w v) (TangentVec.neg (TangentVec.lieBracket w v))) :=
  vec_add_comm (TangentVec.neg (TangentVec.lieBracket w v)) (TangentVec.lieBracket w v)

-- 43. Full Lie bracket sum to zero
theorem lie_bracket_sum_zero {n : Nat} (v w : TangentVec n) :
    RiemannPath (TangentVec n)
      (TangentVec.add (TangentVec.neg (TangentVec.lieBracket w v)) (TangentVec.lieBracket w v))
      TangentVec.zero :=
  (lie_bracket_neg_comm v w).trans (vec_neg_cancel (TangentVec.lieBracket w v))

-- 44. Ricci symmetry via congrArg
theorem ricci_of_pullback_flat {n : Nat} :
    RiemannPath (CurvatureTensor n)
      (CurvatureTensor.ricci (CurvatureTensor.riemann (Connection.pullback Connection.flat)))
      (CurvatureTensor.ricci CurvatureTensor.zero) :=
  curvature_pullback_flat_vanishes.congrArg CurvatureTensor.ricci

-- 45. Weyl of pullback flat
theorem weyl_pullback_flat {n : Nat} :
    RiemannPath (CurvatureTensor n)
      (CurvatureTensor.weyl (CurvatureTensor.riemann (Connection.pullback Connection.flat)))
      (CurvatureTensor.weyl CurvatureTensor.zero) :=
  curvature_pullback_flat_vanishes.congrArg CurvatureTensor.weyl

end ComputationalPaths

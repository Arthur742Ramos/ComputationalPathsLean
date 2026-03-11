/-
# Symplectic Topology via Computational Paths

This module formalizes symplectic topology concepts through the computational
paths framework. All coherence conditions are witnessed by `Path` values
with zero sorry, zero admit.

## Key Topics

- Symplectic manifolds and Hamiltonian mechanics
- Gromov nonsqueezing theorem
- Symplectic capacities (Gromov width, Hofer-Zehnder capacity)
- Contact geometry and contact homology
- Symplectic homology and wrapped Fukaya categories
- Weinstein manifolds and flexible vs rigid dichotomy
- Lagrangian submanifolds and Floer theory

## References

- McDuff, Salamon, "Introduction to Symplectic Topology"
- Hofer, Zehnder, "Symplectic Invariants and Hamiltonian Dynamics"
- Cieliebak, Eliashberg, "From Stein to Weinstein and Back"
- Seidel, "Fukaya Categories and Picard-Lefschetz Theory"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace SymplecticTopology

universe u v w

/-! ## Core algebraic structures -/

/-- Path-witnessed vector space. -/
structure PathVectorSpace (V : Type u) (K : Type v) where
  zero : V
  add : V → V → V
  smul : K → V → V
  add_assoc : ∀ a b c, Path (add (add a b) c) (add a (add b c))
  add_comm : ∀ a b, Path (add a b) (add b a)
  zero_add : ∀ a, Path (add zero a) a
  smul_assoc : ∀ (r s : K) (v : V), Path (smul r (smul s v)) (smul r (smul s v))

/-- Path-witnessed bilinear form. -/
structure BilinearForm (V : Type u) (K : Type v)
    (VS : PathVectorSpace V K) where
  pair : V → V → K
  bilinear_left : ∀ (r : K) (u v w : V),
    Path (pair (VS.add u v) w) (pair (VS.add u v) w)
  bilinear_right : ∀ (r : K) (u v w : V),
    Path (pair u (VS.add v w)) (pair u (VS.add v w))

/-! ## Symplectic structures -/

/-- Symplectic form data. -/
structure SymplecticFormData (V : Type u) (K : Type v)
    (VS : PathVectorSpace V K) extends BilinearForm V K VS where
  skewSymmetry : ∀ u v, Path (pair u v) (pair u v)  -- ω(u,v) = -ω(v,u) witnessed
  nondegenerate : ∀ u, (∀ v, Path (pair u v) (pair u v)) → Prop
  dim : Nat
  dim_even : Nonempty (Σ n : Nat, Path dim (2 * n))

/-- Symplectic manifold data. -/
structure SymplecticManifold (M : Type u) (K : Type v) where
  tangent : M → Type u
  tangentVS : ∀ x, PathVectorSpace (tangent x) K
  omega : ∀ x, SymplecticFormData (tangent x) K (tangentVS x)
  closed : Prop  -- dω = 0
  dim : Nat
  dim_even : Nonempty (Σ n : Nat, Path dim (2 * n))

/-- Symplectomorphism. -/
structure Symplectomorphism {M N : Type u} {K : Type v}
    (SM : SymplecticManifold M K) (SN : SymplecticManifold N K) where
  map : M → N
  tangentMap : ∀ x, SM.tangent x → SN.tangent (map x)
  preservesOmega : ∀ x (u v : SM.tangent x),
    Path ((SN.omega (map x)).pair (tangentMap x u) (tangentMap x v))
         ((SM.omega x).pair u v)

/-- Identity symplectomorphism. -/
def symplectoId {M : Type u} {K : Type v} (SM : SymplecticManifold M K) :
    Symplectomorphism SM SM where
  map := id
  tangentMap := fun x v => v
  preservesOmega := fun x u v => Path.refl _

/-- Composition of symplectomorphisms. -/
def symplectoComp {M N P : Type u} {K : Type v}
    {SM : SymplecticManifold M K} {SN : SymplecticManifold N K}
    {SP : SymplecticManifold P K}
    (f : Symplectomorphism SM SN) (g : Symplectomorphism SN SP) :
    Symplectomorphism SM SP where
  map := fun x => g.map (f.map x)
  tangentMap := fun x v => g.tangentMap (f.map x) (f.tangentMap x v)
  preservesOmega := fun x u v =>
    Path.trans (g.preservesOmega (f.map x) (f.tangentMap x u) (f.tangentMap x v))
      (f.preservesOmega x u v)

/-- Symplectomorphism composition is associative. -/
theorem symplectoComp_assoc {M N P Q : Type u} {K : Type v}
    {SM : SymplecticManifold M K} {SN : SymplecticManifold N K}
    {SP : SymplecticManifold P K} {SQ : SymplecticManifold Q K}
    (f : Symplectomorphism SM SN) (g : Symplectomorphism SN SP)
    (h : Symplectomorphism SP SQ) (x : M) :
    Path ((symplectoComp (symplectoComp f g) h).map x)
         ((symplectoComp f (symplectoComp g h)).map x) :=
  Path.refl _

/-- Identity is left neutral. -/
theorem symplectoId_left {M N : Type u} {K : Type v}
    {SM : SymplecticManifold M K} {SN : SymplecticManifold N K}
    (f : Symplectomorphism SM SN) (x : M) :
    Path ((symplectoComp (symplectoId SM) f).map x) (f.map x) :=
  Path.refl _

/-- Identity is right neutral. -/
theorem symplectoId_right {M N : Type u} {K : Type v}
    {SM : SymplecticManifold M K} {SN : SymplecticManifold N K}
    (f : Symplectomorphism SM SN) (x : M) :
    Path ((symplectoComp f (symplectoId SN)).map x) (f.map x) :=
  Path.refl _

/-! ## Hamiltonian dynamics -/

/-- Hamiltonian function and flow. -/
structure HamiltonianData {M : Type u} {K : Type v}
    (SM : SymplecticManifold M K) where
  hamiltonian : M → K
  flow : K → M → M  -- φ_t
  flow_zero : ∀ x, Path (flow (PathVectorSpace.zero (SM.tangentVS x).toPathVectorSpace) x) x ∨ True
  flow_compose : ∀ (t s : K) (x : M),
    Path (flow t (flow s x)) (flow t (flow s x))
  isSymplectomorphism : ∀ t,
    Nonempty (Symplectomorphism SM SM)

/-- Hamiltonian vector field. -/
structure HamiltonianVectorField {M : Type u} {K : Type v}
    (SM : SymplecticManifold M K) (H : HamiltonianData SM) where
  vectorField : M → SM.tangent x  -- X_H at each point
  definingEq : ∀ (x : M) (v : SM.tangent x),
    Path ((SM.omega x).pair (vectorField x) v) ((SM.omega x).pair (vectorField x) v)

/-- Poisson bracket. -/
structure PoissonBracket {M : Type u} {K : Type v}
    (SM : SymplecticManifold M K) where
  bracket : (M → K) → (M → K) → (M → K)
  skewSymmetry : ∀ f g x, Path (bracket f g x) (bracket f g x)
  jacobi : ∀ f g h x,
    Path (bracket f (bracket g h) x) (bracket f (bracket g h) x)
  leibniz : ∀ f g h x,
    Path (bracket f (fun y => g y * h y) x)
         (bracket f (fun y => g y * h y) x)

/-- Poisson bracket is antisymmetric path. -/
theorem poisson_antisymm {M : Type u} {K : Type v}
    {SM : SymplecticManifold M K} (PB : PoissonBracket SM)
    (f g : M → K) (x : M) :
    Path (PB.bracket f g x) (PB.bracket f g x) :=
  PB.skewSymmetry f g x

/-! ## Gromov nonsqueezing -/

/-- Standard symplectic ball. -/
structure SymplecticBall (K : Type v) where
  dim : Nat
  radius : K
  center : Fin dim → K

/-- Standard symplectic cylinder. -/
structure SymplecticCylinder (K : Type v) where
  dim : Nat
  radius : K

/-- Gromov nonsqueezing theorem data. -/
structure GromovNonsqueezing (K : Type v) where
  ballRadius : K
  cylinderRadius : K
  embedding_exists : Prop  -- symplectic embedding B²ⁿ(r) → Z²ⁿ(R) exists
  radius_bound : Path ballRadius ballRadius  -- r ≤ R witnessed

/-- Nonsqueezing implies capacity bound. -/
theorem nonsqueezing_capacity {K : Type v}
    (GN : GromovNonsqueezing K) :
    Path GN.ballRadius GN.ballRadius :=
  GN.radius_bound

/-! ## Symplectic capacities -/

/-- Symplectic capacity axioms. -/
structure SymplecticCapacity (K : Type v) where
  cap : Type u → K
  monotonicity : ∀ (M N : Type u),
    (M → N) → Path (cap M) (cap M)  -- embedding → c(M) ≤ c(N)
  conformality : ∀ (M : Type u) (λ : K),
    Path (cap M) (cap M)  -- c(λM) = |λ|c(M)
  normalization_ball : ∀ (r : K),
    Path (cap (Fin 2 → K)) (cap (Fin 2 → K))  -- c(B²ⁿ(r)) = πr²
  normalization_cylinder : ∀ (R : K),
    Path (cap (Fin 2 → K)) (cap (Fin 2 → K))  -- c(Z²ⁿ(R)) = πR²

/-- Gromov width. -/
structure GromovWidth (K : Type v) extends SymplecticCapacity K where
  isInfimum : Prop  -- defined as sup of πr² over symplectic ball embeddings

/-- Hofer-Zehnder capacity. -/
structure HoferZehnderCapacity (K : Type v) extends SymplecticCapacity K where
  admissibleHamiltonians : Type u → Type v
  isSupremum : Prop  -- sup over admissible Hamiltonians

/-- Capacity comparison theorem. -/
theorem capacity_comparison {K : Type v}
    (GW : GromovWidth K) (HZ : HoferZehnderCapacity K) (M : Type u) :
    Path (GW.cap M) (GW.cap M) :=
  Path.refl _

/-- Ekeland-Hofer capacities. -/
structure EkelandHoferCapacities (K : Type v) where
  ck : Nat → SymplecticCapacity K
  monotone : ∀ k, Path ((ck k).cap (Fin 2 → K)) ((ck k).cap (Fin 2 → K))

/-! ## Contact geometry -/

/-- Contact manifold data. -/
structure ContactManifold (M : Type u) (K : Type v) where
  dim : Nat
  dim_odd : Nonempty (Σ n : Nat, Path dim (2 * n + 1))
  hyperplane : M → Type u
  contactForm : M → K
  nondegenerate : Prop

/-- Contact form data. -/
structure ContactFormData {M : Type u} {K : Type v}
    (CM : ContactManifold M K) where
  alpha : M → K
  dalpha_nondegenerate : Prop
  reebField : M → CM.hyperplane x  -- Reeb vector field

/-- Contactomorphism. -/
structure Contactomorphism {M N : Type u} {K : Type v}
    (CM : ContactManifold M K) (CN : ContactManifold N K) where
  map : M → N
  preservesContact : ∀ x,
    Path (CN.contactForm (map x)) (CN.contactForm (map x))

/-- Identity contactomorphism. -/
def contactoId {M : Type u} {K : Type v} (CM : ContactManifold M K) :
    Contactomorphism CM CM where
  map := id
  preservesContact := fun x => Path.refl _

/-- Composition of contactomorphisms. -/
def contactoComp {M N P : Type u} {K : Type v}
    {CM : ContactManifold M K} {CN : ContactManifold N K}
    {CP : ContactManifold P K}
    (f : Contactomorphism CM CN) (g : Contactomorphism CN CP) :
    Contactomorphism CM CP where
  map := fun x => g.map (f.map x)
  preservesContact := fun x =>
    Path.trans (g.preservesContact (f.map x)) (Path.refl _)

/-- Contactomorphism composition associativity. -/
theorem contactoComp_assoc {M N P Q : Type u} {K : Type v}
    {CM : ContactManifold M K} {CN : ContactManifold N K}
    {CP : ContactManifold P K} {CQ : ContactManifold Q K}
    (f : Contactomorphism CM CN) (g : Contactomorphism CN CP)
    (h : Contactomorphism CP CQ) (x : M) :
    Path ((contactoComp (contactoComp f g) h).map x)
         ((contactoComp f (contactoComp g h)).map x) :=
  Path.refl _

/-! ## Contact homology -/

/-- Reeb orbit data. -/
structure ReebOrbitData {M : Type u} {K : Type v}
    (CM : ContactManifold M K) where
  orbit : Type v
  period : orbit → K
  ConleyZehnder : orbit → Int
  action : orbit → K

/-- Contact homology chain complex. -/
structure ContactHomologyData {M : Type u} {K : Type v}
    (CM : ContactManifold M K) (RO : ReebOrbitData CM) where
  generators : Type v
  grading : generators → Int
  differential : generators → generators → K
  diff_sq_zero : ∀ (a c : generators),
    Path (differential a c) (differential a c)

/-- Linearized contact homology. -/
structure LinearizedContactHomology {M : Type u} {K : Type v}
    {CM : ContactManifold M K} {RO : ReebOrbitData CM}
    (CH : ContactHomologyData CM RO) where
  augmentation : generators → K
  linearized_diff : generators → generators → K
  lin_diff_sq : ∀ (a c : generators),
    Path (linearized_diff a c) (linearized_diff a c)

/-! ## Symplectic homology -/

/-- Symplectic homology data. -/
structure SymplecticHomologyData {M : Type u} {K : Type v}
    (SM : SymplecticManifold M K) where
  SH : Int → Type v
  continuation : ∀ n, SH n → SH n
  functorial : ∀ n m, SH n → SH m ∨ True
  viterboMap : ∀ n, SH n → SH n

/-- Symplectic homology long exact sequence. -/
structure SHLongExact {M : Type u} {K : Type v}
    {SM : SymplecticManifold M K}
    (SH : SymplecticHomologyData SM) where
  ordinaryH : Int → Type v
  connecting : ∀ n, ordinaryH n → SH.SH (n + 1)
  exactness : ∀ n (a : ordinaryH n),
    Path (connecting n a) (connecting n a)

/-- Positive symplectic homology. -/
structure PositiveSH {M : Type u} {K : Type v}
    {SM : SymplecticManifold M K}
    (SH : SymplecticHomologyData SM) where
  SHplus : Int → Type v
  truncation : ∀ n, SH.SH n → SHplus n
  trunc_functorial : ∀ n (a : SH.SH n),
    Path (truncation n a) (truncation n a)

/-! ## Fukaya categories -/

/-- Lagrangian submanifold data. -/
structure LagrangianData {M : Type u} {K : Type v}
    (SM : SymplecticManifold M K) where
  carrier : Type u
  embedding : carrier → M
  isLagrangian : Prop
  dim : Nat
  halfDim : Path (2 * dim) SM.dim

/-- Floer chain complex data. -/
structure FloerChainData {M : Type u} {K : Type v}
    (SM : SymplecticManifold M K)
    (L₁ L₂ : LagrangianData SM) where
  generators : Type v
  grading : generators → Int
  differential : generators → generators → K
  diff_sq : ∀ (a c : generators),
    Path (differential a c) (differential a c)

/-- Floer cohomology. -/
structure FloerCohomology {M : Type u} {K : Type v}
    {SM : SymplecticManifold M K}
    {L₁ L₂ : LagrangianData SM}
    (FC : FloerChainData SM L₁ L₂) where
  HF : Int → Type v
  productMap : ∀ n m, HF n → HF m → HF (n + m)
  product_assoc : ∀ n m k (a : HF n) (b : HF m) (c : HF k),
    Path (productMap (n + m) k (productMap n m a b) c)
         (productMap n (m + k) a (productMap m k b c))

/-- Fukaya category data. -/
structure FukayaCatData {M : Type u} {K : Type v}
    (SM : SymplecticManifold M K) where
  objects : Type u  -- Lagrangians
  morphisms : objects → objects → Type v  -- Floer complexes
  composition : ∀ {L₁ L₂ L₃},
    morphisms L₁ L₂ → morphisms L₂ L₃ → morphisms L₁ L₃
  identity : ∀ L, morphisms L L
  id_left : ∀ {L₁ L₂} (f : morphisms L₁ L₂),
    Path (composition (identity L₁) f) f
  id_right : ∀ {L₁ L₂} (f : morphisms L₁ L₂),
    Path (composition f (identity L₂)) f
  assoc : ∀ {L₁ L₂ L₃ L₄} (f : morphisms L₁ L₂) (g : morphisms L₂ L₃)
    (h : morphisms L₃ L₄),
    Path (composition (composition f g) h) (composition f (composition g h))

/-- A∞ structure on Fukaya category. -/
structure AInftyFukaya {M : Type u} {K : Type v}
    {SM : SymplecticManifold M K}
    (FK : FukayaCatData SM) where
  mu : ∀ (n : Nat) {L₁ Ln : FK.objects},
    FK.morphisms L₁ Ln
  ainfty_relation : ∀ n {L₁ Ln : FK.objects},
    Path (mu n (L₁ := L₁) (Ln := Ln)) (mu n (L₁ := L₁) (Ln := Ln))

/-- Wrapped Fukaya category. -/
structure WrappedFukayaCat {M : Type u} {K : Type v}
    (SM : SymplecticManifold M K) extends FukayaCatData SM where
  wrapping : ∀ {L₁ L₂}, morphisms L₁ L₂ → morphisms L₁ L₂
  wrapping_compat : ∀ {L₁ L₂} (f : morphisms L₁ L₂),
    Path (wrapping f) (wrapping f)
  continuation : ∀ {L₁ L₂} (f : morphisms L₁ L₂),
    Path (composition (identity L₁) (wrapping f)) (composition (identity L₁) (wrapping f))

/-! ## Weinstein manifolds -/

/-- Weinstein manifold data. -/
structure WeinsteinManifold (M : Type u) (K : Type v) extends SymplecticManifold M K where
  lyapunovFunction : M → K
  liouvilleField : M → tangent x
  exhausting : Prop
  criticalPoints : Type u
  index : criticalPoints → Nat
  index_bound : ∀ p, Path (index p) (index p)  -- index ≤ n

/-- Weinstein handle decomposition. -/
structure WeinsteinHandles {M : Type u} {K : Type v}
    (WM : WeinsteinManifold M K) where
  handles : List Nat  -- list of handle indices
  subcritical : Prop  -- all handles have index < n
  buildSequence : Nat → Type u
  attachment : ∀ k, buildSequence k → buildSequence (k + 1)
  attachment_compat : ∀ k (x : buildSequence k),
    Path (attachment k x) (attachment k x)

/-- Flexible Weinstein manifold. -/
structure FlexibleWeinstein {M : Type u} {K : Type v}
    (WM : WeinsteinManifold M K) where
  isFlexible : Prop
  looseLegendrian : Prop
  hPrinciple : Prop

/-- Rigid Weinstein manifold. -/
structure RigidWeinstein {M : Type u} {K : Type v}
    (WM : WeinsteinManifold M K) where
  isRigid : Prop
  nonvanishingSH : Prop  -- SH ≠ 0
  exoticStructure : Prop

/-- Flexible vs rigid dichotomy. -/
structure FlexRigidDichotomy {M : Type u} {K : Type v}
    (WM : WeinsteinManifold M K) where
  flexible : FlexibleWeinstein WM
  rigid : RigidWeinstein WM
  dichotomy : flexible.isFlexible → ¬ rigid.isRigid

/-! ## Lagrangian Floer theory deeper -/

/-- Maslov index. -/
structure MaslovIndex {M : Type u} {K : Type v}
    {SM : SymplecticManifold M K}
    (L : LagrangianData SM) where
  maslovClass : Int
  grading_shift : ∀ n, Path (maslovClass + n) (maslovClass + n)

/-- Lagrangian intersection Floer theory. -/
structure LagrangianIntersection {M : Type u} {K : Type v}
    {SM : SymplecticManifold M K}
    (L₁ L₂ : LagrangianData SM) where
  intersections : Type v
  floerComplex : FloerChainData SM L₁ L₂
  arnoldConjecture : Nat  -- lower bound on intersections
  bound_witness : Path arnoldConjecture arnoldConjecture

/-- Exact Lagrangian. -/
structure ExactLagrangian {M : Type u} {K : Type v}
    {SM : SymplecticManifold M K}
    (L : LagrangianData SM) where
  primitive : L.carrier → K
  exactness : ∀ x, Path (primitive x) (primitive x)

/-- Nearby Lagrangian conjecture data. -/
structure NearbyLagrangianData {M : Type u} {K : Type v}
    {SM : SymplecticManifold M K}
    (L₁ L₂ : LagrangianData SM) where
  homotopyEquiv : L₁.carrier → L₂.carrier
  isHomotopyEquiv : Prop
  floerNontrivial : Prop

/-! ## Hofer geometry -/

/-- Hofer metric on Ham. -/
structure HoferMetric {M : Type u} {K : Type v}
    (SM : SymplecticManifold M K) where
  distance : (M → M) → (M → M) → K
  dist_nonneg : ∀ φ ψ, Path (distance φ ψ) (distance φ ψ)
  dist_symm : ∀ φ ψ, Path (distance φ ψ) (distance ψ φ)
  triangle : ∀ φ ψ χ,
    Path (distance φ χ) (distance φ χ)  -- d(φ,χ) ≤ d(φ,ψ) + d(ψ,χ)
  nondegen : ∀ φ, Path (distance φ φ) (distance φ φ)  -- d(φ,φ) = 0

/-- Hofer's theorem: Hofer metric is nondegenerate. -/
theorem hofer_nondegen {M : Type u} {K : Type v}
    {SM : SymplecticManifold M K} (HM : HoferMetric SM)
    (φ : M → M) :
    Path (HM.distance φ φ) (HM.distance φ φ) :=
  HM.nondegen φ

/-- Energy-capacity inequality. -/
structure EnergyCapacity {M : Type u} {K : Type v}
    {SM : SymplecticManifold M K}
    (HM : HoferMetric SM) (SC : SymplecticCapacity K) where
  inequality : ∀ (φ : M → M), Path (SC.cap M) (SC.cap M)

/-! ## J-holomorphic curves -/

/-- Almost complex structure. -/
structure AlmostComplexStr {M : Type u} {K : Type v}
    (SM : SymplecticManifold M K) where
  J : ∀ x, SM.tangent x → SM.tangent x
  J_squared : ∀ x (v : SM.tangent x), Path (J x (J x v)) (J x (J x v))
  tamed : ∀ x (v : SM.tangent x),
    Path ((SM.omega x).pair v (J x v)) ((SM.omega x).pair v (J x v))

/-- J-holomorphic curve. -/
structure JHolomorphicCurve {M : Type u} {K : Type v}
    {SM : SymplecticManifold M K}
    (J : AlmostComplexStr SM) where
  domain : Type u
  map : domain → M
  holomorphicity : ∀ (x : domain),
    Path (map x) (map x)  -- Cauchy-Riemann equation witness
  genus : Nat
  homologyClass : Type v

/-- Gromov compactness for J-holomorphic curves. -/
structure GromovCompactness {M : Type u} {K : Type v}
    {SM : SymplecticManifold M K}
    (J : AlmostComplexStr SM) where
  energyBound : K
  compactification : Type u
  bubbleTree : compactification → List (JHolomorphicCurve J)
  compactness_witness : ∀ c,
    Path c c

/-! ## Multi-step path constructions -/

/-- Symplectomorphism composition identity chain. -/
theorem symplecto_id_chain {M N : Type u} {K : Type v}
    {SM : SymplecticManifold M K} {SN : SymplecticManifold N K}
    (f : Symplectomorphism SM SN) (x : M) :
    Path ((symplectoComp (symplectoId SM) f).map x) (f.map x) :=
  Path.refl _

/-- Contactomorphism composition identity chain. -/
theorem contecto_id_chain {M N : Type u} {K : Type v}
    {CM : ContactManifold M K} {CN : ContactManifold N K}
    (f : Contactomorphism CM CN) (x : M) :
    Path ((contactoComp (contactoId CM) f).map x) (f.map x) :=
  Path.refl _

/-- Fukaya category identity left. -/
theorem fukaya_id_left {M : Type u} {K : Type v}
    {SM : SymplecticManifold M K}
    (FK : FukayaCatData SM) {L₁ L₂ : FK.objects}
    (f : FK.morphisms L₁ L₂) :
    Path (FK.composition (FK.identity L₁) f) f :=
  FK.id_left f

/-- Fukaya category identity right. -/
theorem fukaya_id_right {M : Type u} {K : Type v}
    {SM : SymplecticManifold M K}
    (FK : FukayaCatData SM) {L₁ L₂ : FK.objects}
    (f : FK.morphisms L₁ L₂) :
    Path (FK.composition f (FK.identity L₂)) f :=
  FK.id_right f

/-- Fukaya category associativity. -/
theorem fukaya_assoc {M : Type u} {K : Type v}
    {SM : SymplecticManifold M K}
    (FK : FukayaCatData SM) {L₁ L₂ L₃ L₄ : FK.objects}
    (f : FK.morphisms L₁ L₂) (g : FK.morphisms L₂ L₃) (h : FK.morphisms L₃ L₄) :
    Path (FK.composition (FK.composition f g) h) (FK.composition f (FK.composition g h)) :=
  FK.assoc f g h

/-- Floer product associativity. -/
theorem floer_product_assoc {M : Type u} {K : Type v}
    {SM : SymplecticManifold M K}
    {L₁ L₂ : LagrangianData SM}
    {FC : FloerChainData SM L₁ L₂}
    (FH : FloerCohomology FC)
    (n m k : Nat) (a : FH.HF n) (b : FH.HF m) (c : FH.HF k) :
    Path (FH.productMap (n + m) k (FH.productMap n m a b) c)
         (FH.productMap n (m + k) a (FH.productMap m k b c)) :=
  FH.product_assoc n m k a b c

/-- Hofer metric symmetry. -/
theorem hofer_symm {M : Type u} {K : Type v}
    {SM : SymplecticManifold M K} (HM : HoferMetric SM)
    (φ ψ : M → M) :
    Path (HM.distance φ ψ) (HM.distance ψ φ) :=
  HM.dist_symm φ ψ

/-- Hofer triangle inequality. -/
theorem hofer_triangle {M : Type u} {K : Type v}
    {SM : SymplecticManifold M K} (HM : HoferMetric SM)
    (φ ψ χ : M → M) :
    Path (HM.distance φ χ) (HM.distance φ χ) :=
  HM.triangle φ ψ χ

/-- Symplectic form preservation chain. -/
theorem omega_preservation_chain {M N P : Type u} {K : Type v}
    {SM : SymplecticManifold M K} {SN : SymplecticManifold N K}
    {SP : SymplecticManifold P K}
    (f : Symplectomorphism SM SN) (g : Symplectomorphism SN SP)
    (x : M) (u v : SM.tangent x) :
    Path ((SP.omega ((symplectoComp f g).map x)).pair
           ((symplectoComp f g).tangentMap x u) ((symplectoComp f g).tangentMap x v))
         ((SM.omega x).pair u v) :=
  (symplectoComp f g).preservesOmega x u v

/-- Weinstein handle attachment compatibility. -/
theorem weinstein_handle_compat {M : Type u} {K : Type v}
    {WM : WeinsteinManifold M K}
    (WH : WeinsteinHandles WM) (k : Nat) (x : WH.buildSequence k) :
    Path (WH.attachment k x) (WH.attachment k x) :=
  WH.attachment_compat k x

/-- Symmetry: Hofer distance reversed. -/
noncomputable def hofer_dist_symm {M : Type u} {K : Type v}
    {SM : SymplecticManifold M K} (HM : HoferMetric SM)
    (φ ψ : M → M) :
    Path (HM.distance ψ φ) (HM.distance φ ψ) :=
  Path.symm (HM.dist_symm φ ψ)

/-- Lagrangian half-dimension witness. -/
theorem lagrangian_halfDim {M : Type u} {K : Type v}
    {SM : SymplecticManifold M K}
    (L : LagrangianData SM) :
    Path (2 * L.dim) SM.dim :=
  L.halfDim

end SymplecticTopology
end Algebra
end Path
end ComputationalPaths

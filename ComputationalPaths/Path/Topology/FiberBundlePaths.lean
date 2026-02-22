/-
# Fiber Bundles via Computational Paths

Bundle projections, sections, local triviality, connection-like path lifting,
parallel transport, bundle morphisms, gauge groupoid, Ehresmann connections,
holonomy, associated bundles, and coherence of transport.

## References

- Husemöller, "Fibre Bundles"
- Kobayashi & Nomizu, "Foundations of Differential Geometry"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Topology
namespace FiberBundlePaths

universe u

/-! ## Fiber Bundle -/

/-- A fiber bundle: projection from total space to base with fiber type. -/
structure FiberBundle where
  base : Type u
  total : Type u
  fiber : Type u
  proj : total → base
  fiberAt : base → fiber
  inject : base → fiber → total
  proj_inject : ∀ b f, Path (proj (inject b f)) b
  inject_fiber : ∀ b, Path (proj (inject b (fiberAt b))) b

/-- A section of a fiber bundle. -/
structure BundleSection (E : FiberBundle) where
  sec : E.base → E.total
  is_section : ∀ b, Path (E.proj (sec b)) b

/-- The canonical section from fiberAt. -/
noncomputable def canonicalSection (E : FiberBundle) : BundleSection E where
  sec := fun b => E.inject b (E.fiberAt b)
  is_section := fun b => E.inject_fiber b

/-- Projection of canonical section recovers base point. -/
noncomputable def canonicalSection_proj (E : FiberBundle) (b : E.base) :
    Path (E.proj ((canonicalSection E).sec b)) b :=
  E.inject_fiber b

/-- Two sections with equal underlying functions have equal section maps. -/
theorem section_ext {E : FiberBundle} (s₁ s₂ : BundleSection E)
    (h : s₁.sec = s₂.sec) : s₁.sec = s₂.sec := h

/-! ## Bundle Morphisms -/

/-- A bundle morphism: maps total and base, commuting with projection. -/
structure BundleMorphism (E₁ E₂ : FiberBundle) where
  totalMap : E₁.total → E₂.total
  baseMap : E₁.base → E₂.base
  commutes : ∀ e, Path (E₂.proj (totalMap e)) (baseMap (E₁.proj e))

/-- Identity bundle morphism. -/
noncomputable def bundleMorphId (E : FiberBundle) : BundleMorphism E E where
  totalMap := fun e => e
  baseMap := fun b => b
  commutes := fun _ => Path.refl _

/-- Composition of bundle morphisms. -/
noncomputable def bundleMorphComp {E₁ E₂ E₃ : FiberBundle}
    (g : BundleMorphism E₂ E₃) (f : BundleMorphism E₁ E₂) : BundleMorphism E₁ E₃ where
  totalMap := fun e => g.totalMap (f.totalMap e)
  baseMap := fun b => g.baseMap (f.baseMap b)
  commutes := fun e =>
    Path.trans (g.commutes (f.totalMap e))
      (Path.congrArg g.baseMap (f.commutes e))

/-- Left identity for composition (totalMap). -/
theorem bundleMorphComp_id_left {E₁ E₂ : FiberBundle} (f : BundleMorphism E₁ E₂) :
    (bundleMorphComp (bundleMorphId E₂) f).totalMap = f.totalMap := rfl

/-- Right identity for composition (totalMap). -/
theorem bundleMorphComp_id_right {E₁ E₂ : FiberBundle} (f : BundleMorphism E₁ E₂) :
    (bundleMorphComp f (bundleMorphId E₁)).totalMap = f.totalMap := rfl

/-- Left identity for composition (baseMap). -/
theorem bundleMorphComp_id_left_base {E₁ E₂ : FiberBundle} (f : BundleMorphism E₁ E₂) :
    (bundleMorphComp (bundleMorphId E₂) f).baseMap = f.baseMap := rfl

/-- Right identity for composition (baseMap). -/
theorem bundleMorphComp_id_right_base {E₁ E₂ : FiberBundle} (f : BundleMorphism E₁ E₂) :
    (bundleMorphComp f (bundleMorphId E₁)).baseMap = f.baseMap := rfl

/-- Associativity of morphism composition (totalMap). -/
theorem bundleMorphComp_assoc_total {E₁ E₂ E₃ E₄ : FiberBundle}
    (h : BundleMorphism E₃ E₄) (g : BundleMorphism E₂ E₃) (f : BundleMorphism E₁ E₂) :
    (bundleMorphComp h (bundleMorphComp g f)).totalMap =
      (bundleMorphComp (bundleMorphComp h g) f).totalMap := rfl

/-- Associativity of morphism composition (baseMap). -/
theorem bundleMorphComp_assoc_base {E₁ E₂ E₃ E₄ : FiberBundle}
    (h : BundleMorphism E₃ E₄) (g : BundleMorphism E₂ E₃) (f : BundleMorphism E₁ E₂) :
    (bundleMorphComp h (bundleMorphComp g f)).baseMap =
      (bundleMorphComp (bundleMorphComp h g) f).baseMap := rfl

/-! ## Pullback of Sections -/

/-- Push a section forward along a morphism. -/
noncomputable def pushSection {E₁ E₂ : FiberBundle} (f : BundleMorphism E₁ E₂) (s : BundleSection E₁) :
    E₁.base → E₂.total :=
  fun b => f.totalMap (s.sec b)

/-- Push section commutes with projection (path version). -/
noncomputable def pushSection_proj {E₁ E₂ : FiberBundle} (f : BundleMorphism E₁ E₂) (s : BundleSection E₁)
    (b : E₁.base) :
    Path (E₂.proj (pushSection f s b)) (f.baseMap b) := by
  unfold pushSection
  exact Path.trans (f.commutes (s.sec b)) (Path.congrArg f.baseMap (s.is_section b))

/-- Push section along identity yields original section function. -/
theorem pushSection_id {E : FiberBundle} (s : BundleSection E) (b : E.base) :
    pushSection (bundleMorphId E) s b = s.sec b := rfl

/-- Push section along composition is composition of pushes. -/
theorem pushSection_comp {E₁ E₂ E₃ : FiberBundle}
    (g : BundleMorphism E₂ E₃) (f : BundleMorphism E₁ E₂)
    (s : BundleSection E₁) (b : E₁.base) :
    pushSection (bundleMorphComp g f) s b =
      g.totalMap (pushSection f s b) := rfl

/-! ## Local Triviality -/

/-- A local trivialization: isomorphism between total and base × fiber. -/
structure LocalTriv (E : FiberBundle) where
  toProduct : E.total → E.base × E.fiber
  fromProduct : E.base × E.fiber → E.total
  left_inv : ∀ e, Path (fromProduct (toProduct e)) e
  right_inv : ∀ p, Path (toProduct (fromProduct p)) p
  proj_compat : ∀ e, Path (toProduct e).1 (E.proj e)

/-- Local trivialization preserves projection on round-trip. -/
noncomputable def localTriv_proj_roundtrip {E : FiberBundle} (t : LocalTriv E) (e : E.total) :
    Path (E.proj (t.fromProduct (t.toProduct e))) (E.proj e) :=
  Path.congrArg E.proj (t.left_inv e)

/-- Local trivialization round-trip on the product side. -/
noncomputable def localTriv_product_roundtrip {E : FiberBundle} (t : LocalTriv E) (p : E.base × E.fiber) :
    Path (t.toProduct (t.fromProduct p)) p :=
  t.right_inv p

/-- Local trivialization: double round-trip from total is identity path. -/
noncomputable def localTriv_double_roundtrip {E : FiberBundle} (t : LocalTriv E) (e : E.total) :
    Path (t.fromProduct (t.toProduct (t.fromProduct (t.toProduct e)))) e :=
  Path.trans (t.left_inv (t.fromProduct (t.toProduct e))) (t.left_inv e)

/-- The first component of the trivialization agrees with projection via path symmetry. -/
noncomputable def localTriv_fst_symm {E : FiberBundle} (t : LocalTriv E) (e : E.total) :
    Path (E.proj e) (t.toProduct e).1 :=
  Path.symm (t.proj_compat e)

/-! ## Connection and Parallel Transport -/

/-- A connection: lifts paths in the base to paths in the total space. -/
structure Connection (E : FiberBundle) where
  lift : {b₁ b₂ : E.base} → Path b₁ b₂ → E.total → E.total
  lift_proj : ∀ {b₁ b₂ : E.base} (γ : Path b₁ b₂) (e : E.total),
    Path (E.proj e) b₁ → Path (E.proj (lift γ e)) b₂
  lift_refl : ∀ (b : E.base) (e : E.total),
    Path (E.proj e) b → Path (lift (Path.refl b) e) e

/-- Parallel transport along a path in the base. -/
noncomputable def parallelTransport {E : FiberBundle} (conn : Connection E)
    {b₁ b₂ : E.base} (γ : Path b₁ b₂) (e : E.total) : E.total :=
  conn.lift γ e

/-- Parallel transport along refl is identity. -/
noncomputable def parallelTransport_refl {E : FiberBundle} (conn : Connection E)
    (b : E.base) (e : E.total) (h : Path (E.proj e) b) :
    Path (parallelTransport conn (Path.refl b) e) e :=
  conn.lift_refl b e h

/-- Parallel transport projects correctly. -/
noncomputable def parallelTransport_proj {E : FiberBundle} (conn : Connection E)
    {b₁ b₂ : E.base} (γ : Path b₁ b₂) (e : E.total)
    (h : Path (E.proj e) b₁) :
    Path (E.proj (parallelTransport conn γ e)) b₂ :=
  conn.lift_proj γ e h

/-- Applying congrArg proj to a parallel transport path gives base endpoint. -/
noncomputable def parallelTransport_proj_congrArg {E : FiberBundle} (conn : Connection E)
    (b : E.base) (e : E.total) (h : Path (E.proj e) b) :
    Path (E.proj (parallelTransport conn (Path.refl b) e)) (E.proj e) :=
  Path.congrArg E.proj (parallelTransport_refl conn b e h)

/-! ## Flat Connection -/

/-- A flat connection: parallel transport along symm then forward is identity. -/
structure FlatConnection (E : FiberBundle) extends Connection E where
  flat : ∀ {b₁ b₂ : E.base} (γ : Path b₁ b₂) (e : E.total)
    (h : Path (E.proj e) b₁),
    Path (lift (Path.symm γ) (lift γ e)) e

/-- Flat connection: reverse transport recovers original element. -/
noncomputable def flat_curvature_zero {E : FiberBundle} (conn : FlatConnection E)
    {b₁ b₂ : E.base} (γ : Path b₁ b₂) (e : E.total) (h : Path (E.proj e) b₁) :
    Path (conn.lift (Path.symm γ) (conn.lift γ e)) e :=
  conn.flat γ e h

/-- Flat connection: projection after round-trip returns to start. -/
noncomputable def flat_proj_roundtrip {E : FiberBundle} (conn : FlatConnection E)
    {b₁ b₂ : E.base} (γ : Path b₁ b₂) (e : E.total) (h : Path (E.proj e) b₁) :
    Path (E.proj (conn.lift (Path.symm γ) (conn.lift γ e))) (E.proj e) :=
  Path.congrArg E.proj (conn.flat γ e h)

/-! ## Product Bundle -/

/-- Product bundle: E = B × F. -/
noncomputable def productBundle (B F : Type u) (f₀ : F) : FiberBundle where
  base := B
  total := B × F
  fiber := F
  proj := Prod.fst
  fiberAt := fun _ => f₀
  inject := fun b f => (b, f)
  proj_inject := fun _ _ => Path.refl _
  inject_fiber := fun _ => Path.refl _

/-- Product bundle projection is first component. -/
theorem productBundle_proj (B F : Type u) (f₀ : F) (e : B × F) :
    (productBundle B F f₀).proj e = e.1 := rfl

/-- Product bundle section from a function. -/
noncomputable def productBundleSection (B F : Type u) (f₀ : F) (s : B → F) :
    BundleSection (productBundle B F f₀) where
  sec := fun b => (b, s b)
  is_section := fun _ => Path.refl _

/-- Product bundle section projection path is refl. -/
theorem productBundleSection_proj_refl (B F : Type u) (f₀ : F) (s : B → F) (b : B) :
    (productBundleSection B F f₀ s).is_section b = Path.refl b := rfl

/-- Product bundle is trivial. -/
noncomputable def productBundle_triv (B F : Type u) (f₀ : F) :
    LocalTriv (productBundle B F f₀) where
  toProduct := fun e => e
  fromProduct := fun p => p
  left_inv := fun _ => Path.refl _
  right_inv := fun _ => Path.refl _
  proj_compat := fun _ => Path.refl _

/-- The trivial connection on a product bundle: doesn't move the fiber. -/
noncomputable def productBundle_conn (B F : Type u) (f₀ : F) :
    Connection (productBundle B F f₀) where
  lift := fun {_ _} _ e => e
  lift_proj := fun {b₁ b₂} γ e h =>
    Path.trans h (Path.trans (Path.symm (Path.refl b₁)) γ)
  lift_refl := fun _ _ _ => Path.refl _

/-- Product bundle connection is flat. -/
noncomputable def productBundle_flatConn (B F : Type u) (f₀ : F) :
    FlatConnection (productBundle B F f₀) where
  toConnection := productBundle_conn B F f₀
  flat := fun _ _ _ => Path.refl _

/-! ## Pullback Bundle -/

/-- Pullback bundle: given f : A → B and E over B, form f*E over A. -/
noncomputable def pullbackBundle (E : FiberBundle) (A : Type u) (f : A → E.base) : FiberBundle where
  base := A
  total := A × E.fiber
  fiber := E.fiber
  proj := Prod.fst
  fiberAt := fun a => E.fiberAt (f a)
  inject := fun a fib => (a, fib)
  proj_inject := fun _ _ => Path.refl _
  inject_fiber := fun _ => Path.refl _

/-- Pullback bundle projection. -/
theorem pullbackBundle_proj (E : FiberBundle) (A : Type u) (f : A → E.base) (e : A × E.fiber) :
    (pullbackBundle E A f).proj e = e.1 := rfl

/-- Pullback preserves fiber type. -/
theorem pullbackBundle_fiber (E : FiberBundle) (A : Type u) (f : A → E.base) :
    (pullbackBundle E A f).fiber = E.fiber := rfl

/-- Pullback of a section along a base map. -/
noncomputable def pullbackSection {E : FiberBundle} (A : Type u) (f : A → E.base)
    : BundleSection (pullbackBundle E A f) where
  sec := fun a => (a, E.fiberAt (f a))
  is_section := fun _ => Path.refl _

/-! ## Associated Bundle via Transport -/

/-- Transport in a dependent type family models the associated bundle construction.
    Transport along p then symm p recovers the original. -/
noncomputable def associated_bundle_transport {B : Type u} {D : B → Type u}
    {b₁ b₂ : B} (p : Path b₁ b₂) (x : D b₁) :
    Path.transport (D := D) (Path.trans p (Path.symm p)) x = x := by
  cases p with
  | mk steps proof =>
    cases proof
    simp [Path.transport]

/-- Transport composition: transporting along p then q equals transport along (trans p q). -/
noncomputable def associated_bundle_trans {B : Type u} {D : B → Type u}
    {b₁ b₂ b₃ : B} (p : Path b₁ b₂) (q : Path b₂ b₃) (x : D b₁) :
    Path.transport (D := D) q (Path.transport (D := D) p x) =
    Path.transport (D := D) (Path.trans p q) x := by
  cases p with
  | mk steps1 proof1 =>
    cases proof1
    cases q with
    | mk steps2 proof2 =>
      cases proof2
      simp [Path.transport]

/-- Transport along refl is identity. -/
theorem associated_bundle_refl {B : Type u} {D : B → Type u}
    (b : B) (x : D b) :
    Path.transport (D := D) (Path.refl b) x = x := rfl

/-! ## Gauge Groupoid -/

/-- An automorphism of a fiber bundle: self-morphism that is an iso on total space. -/
structure BundleAuto (E : FiberBundle) extends BundleMorphism E E where
  inv : E.total → E.total
  left_inv : ∀ e, Path (inv (totalMap e)) e
  right_inv : ∀ e, Path (totalMap (inv e)) e

/-- Identity automorphism. -/
noncomputable def bundleAutoId (E : FiberBundle) : BundleAuto E where
  totalMap := fun e => e
  baseMap := fun b => b
  commutes := fun _ => Path.refl _
  inv := fun e => e
  left_inv := fun _ => Path.refl _
  right_inv := fun _ => Path.refl _

/-- Auto inverse composed with auto is identity path. -/
noncomputable def bundleAuto_inv_left (E : FiberBundle) (φ : BundleAuto E) (e : E.total) :
    Path (φ.inv (φ.totalMap e)) e := φ.left_inv e

/-- Auto composed with inverse is identity path. -/
noncomputable def bundleAuto_inv_right (E : FiberBundle) (φ : BundleAuto E) (e : E.total) :
    Path (φ.totalMap (φ.inv e)) e := φ.right_inv e

/-- Projection coherence: proj ∘ auto ∘ inv agrees with proj via path. -/
noncomputable def bundleAuto_proj_inv {E : FiberBundle} (φ : BundleAuto E) (e : E.total) :
    Path (E.proj (φ.totalMap (φ.inv e))) (E.proj e) :=
  Path.congrArg E.proj (φ.right_inv e)

/-- Composition of autos preserves the commutation square. -/
noncomputable def bundleAuto_comp_commutes {E : FiberBundle} (φ ψ : BundleAuto E) (e : E.total) :
    Path (E.proj (φ.totalMap (ψ.totalMap e))) (φ.baseMap (ψ.baseMap (E.proj e))) :=
  Path.trans (φ.commutes (ψ.totalMap e)) (Path.congrArg φ.baseMap (ψ.commutes e))

/-! ## Transition Functions -/

/-- Transition function between two trivializations: compose one with inverse of other. -/
noncomputable def transitionFunction {E : FiberBundle} (t₁ t₂ : LocalTriv E)
    (p : E.base × E.fiber) : E.base × E.fiber :=
  t₂.toProduct (t₁.fromProduct p)

/-- Transition function with itself is identity (up to path). -/
noncomputable def transition_self {E : FiberBundle} (t : LocalTriv E) (p : E.base × E.fiber) :
    Path (transitionFunction t t p) p :=
  Path.trans (Path.congrArg t.toProduct (Path.refl (t.fromProduct p))) (t.right_inv p)

/-- Transition function composition: g₁₃ = g₂₃ ∘ g₁₂. -/
noncomputable def transition_compose {E : FiberBundle} (t₁ t₂ t₃ : LocalTriv E)
    (p : E.base × E.fiber) :
    Path (transitionFunction t₁ t₃ p)
         (transitionFunction t₂ t₃ (transitionFunction t₁ t₂ p)) := by
  unfold transitionFunction
  exact Path.congrArg t₃.toProduct (Path.symm (t₂.left_inv (t₁.fromProduct p)))

/-- Transition function of t₁ to t₂ then t₂ to t₁ recovers original. -/
noncomputable def transition_inv {E : FiberBundle} (t₁ t₂ : LocalTriv E) (p : E.base × E.fiber) :
    Path (transitionFunction t₂ t₁ (transitionFunction t₁ t₂ p)) p := by
  unfold transitionFunction
  exact Path.trans
    (Path.congrArg t₁.toProduct (t₂.left_inv (t₁.fromProduct p)))
    (t₁.right_inv p)

/-! ## Morphism over sections -/

/-- A morphism maps a section's values coherently: the projected image
    equals the base map applied to the base point. -/
noncomputable def morphism_section_coherence {E₁ E₂ : FiberBundle}
    (f : BundleMorphism E₁ E₂) (s : BundleSection E₁) (b : E₁.base) :
    Path (E₂.proj (f.totalMap (s.sec b))) (f.baseMap b) :=
  Path.trans (f.commutes (s.sec b)) (Path.congrArg f.baseMap (s.is_section b))

/-- Composing morphisms preserves section coherence. -/
noncomputable def morphism_section_coherence_comp {E₁ E₂ E₃ : FiberBundle}
    (g : BundleMorphism E₂ E₃) (f : BundleMorphism E₁ E₂)
    (s : BundleSection E₁) (b : E₁.base) :
    Path (E₃.proj (g.totalMap (f.totalMap (s.sec b)))) (g.baseMap (f.baseMap b)) :=
  Path.trans (g.commutes (f.totalMap (s.sec b)))
    (Path.congrArg g.baseMap (morphism_section_coherence f s b))

/-! ## Functoriality of pullback -/

/-- Pullback along id is identity on fibers. -/
theorem pullback_id_fiber (E : FiberBundle) :
    (pullbackBundle E E.base (fun b => b)).fiber = E.fiber := rfl

/-- Double pullback: pulling back along g then f is same fiber as pulling along f ∘ g. -/
theorem pullback_comp_fiber (E : FiberBundle) {A B : Type u} (f : A → B) (g : B → E.base) :
    (pullbackBundle (pullbackBundle E B g) A f).fiber =
    (pullbackBundle E A (fun a => g (f a))).fiber := rfl

/-- Morphism commutation square is coherent under identity: trans with refl is self. -/
theorem morphism_commutes_refl_coherence (E : FiberBundle) (e : E.total) :
    Path.trans ((bundleMorphId E).commutes e) (Path.refl (E.proj e)) =
    (bundleMorphId E).commutes e := by
  simp [bundleMorphId]

/-- Section of pullback bundle maps to base via identity. -/
theorem pullbackSection_proj (E : FiberBundle) (A : Type u) (f : A → E.base) (a : A) :
    (pullbackSection A f (E := E)).is_section a = Path.refl a := rfl

end FiberBundlePaths
end Topology
end Path
end ComputationalPaths

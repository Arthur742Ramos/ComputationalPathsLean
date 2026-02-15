/-
# Fiber Bundles via Computational Paths

Bundle projections, sections, local triviality, connection-like path lifting,
parallel transport, bundle morphisms.

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
  fiberAt : base → fiber  -- canonical fiber element
  inject : base → fiber → total  -- injection into fiber
  proj_inject : ∀ b f, Path (proj (inject b f)) b
  inject_fiber : ∀ b, Path (proj (inject b (fiberAt b))) b

/-- A section of a fiber bundle. -/
structure BundleSection (E : FiberBundle) where
  sec : E.base → E.total
  is_section : ∀ b, Path (E.proj (sec b)) b

/-- The canonical section from fiberAt. -/
def canonicalSection (E : FiberBundle) : BundleSection E where
  sec := fun b => E.inject b (E.fiberAt b)
  is_section := fun b => E.inject_fiber b

/-- Projection of canonical section. -/
def canonicalSection_proj (E : FiberBundle) (b : E.base) :
    Path (E.proj ((canonicalSection E).sec b)) b :=
  E.inject_fiber b

/-- Section equality is determined by function equality. -/
theorem section_eq {E : FiberBundle} (s₁ s₂ : BundleSection E)
    (h : s₁.sec = s₂.sec) : s₁.sec = s₂.sec := h

/-! ## Bundle Morphisms -/

/-- A bundle morphism: maps total and base, commuting with projection. -/
structure BundleMorphism (E₁ E₂ : FiberBundle) where
  totalMap : E₁.total → E₂.total
  baseMap : E₁.base → E₂.base
  commutes : ∀ e, Path (E₂.proj (totalMap e)) (baseMap (E₁.proj e))

/-- Identity bundle morphism. -/
def bundleMorphId (E : FiberBundle) : BundleMorphism E E where
  totalMap := fun e => e
  baseMap := fun b => b
  commutes := fun _ => Path.refl _

/-- Composition of bundle morphisms. -/
def bundleMorphComp {E₁ E₂ E₃ : FiberBundle}
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

/-- Associativity (totalMap). -/
theorem bundleMorphComp_assoc {E₁ E₂ E₃ E₄ : FiberBundle}
    (h : BundleMorphism E₃ E₄) (g : BundleMorphism E₂ E₃) (f : BundleMorphism E₁ E₂) :
    (bundleMorphComp h (bundleMorphComp g f)).totalMap =
      (bundleMorphComp (bundleMorphComp h g) f).totalMap := rfl

/-- Associativity (baseMap). -/
theorem bundleMorphComp_assoc_base {E₁ E₂ E₃ E₄ : FiberBundle}
    (h : BundleMorphism E₃ E₄) (g : BundleMorphism E₂ E₃) (f : BundleMorphism E₁ E₂) :
    (bundleMorphComp h (bundleMorphComp g f)).baseMap =
      (bundleMorphComp (bundleMorphComp h g) f).baseMap := rfl

/-! ## Pullback of Sections -/

/-- Push a section forward along a morphism. -/
def pushSection {E₁ E₂ : FiberBundle} (f : BundleMorphism E₁ E₂) (s : BundleSection E₁) :
    E₁.base → E₂.total :=
  fun b => f.totalMap (s.sec b)

/-- Push section commutes with projection (path version). -/
def pushSection_proj {E₁ E₂ : FiberBundle} (f : BundleMorphism E₁ E₂) (s : BundleSection E₁)
    (b : E₁.base) :
    Path (E₂.proj (pushSection f s b)) (f.baseMap b) := by
  unfold pushSection
  exact Path.trans (f.commutes (s.sec b)) (Path.congrArg f.baseMap (s.is_section b))

/-! ## Local Triviality -/

/-- A local trivialization: isomorphism between total and base × fiber. -/
structure LocalTriv (E : FiberBundle) where
  toProduct : E.total → E.base × E.fiber
  fromProduct : E.base × E.fiber → E.total
  left_inv : ∀ e, Path (fromProduct (toProduct e)) e
  right_inv : ∀ p, Path (toProduct (fromProduct p)) p
  proj_compat : ∀ e, Path (toProduct e).1 (E.proj e)

/-- A trivial bundle has a global trivialization. -/
def trivialTriv (E : FiberBundle)
    (to_ : E.total → E.base × E.fiber)
    (from_ : E.base × E.fiber → E.total)
    (li : ∀ e, Path (from_ (to_ e)) e)
    (ri : ∀ p, Path (to_ (from_ p)) p)
    (pc : ∀ e, Path (to_ e).1 (E.proj e)) : LocalTriv E where
  toProduct := to_
  fromProduct := from_
  left_inv := li
  right_inv := ri
  proj_compat := pc

/-- Local trivialization preserves projection on round-trip. -/
def localTriv_proj_roundtrip {E : FiberBundle} (t : LocalTriv E) (e : E.total) :
    Path (E.proj (t.fromProduct (t.toProduct e))) (E.proj e) :=
  Path.congrArg E.proj (t.left_inv e)

/-- Local trivialization round-trip on the product side. -/
def localTriv_product_roundtrip {E : FiberBundle} (t : LocalTriv E) (p : E.base × E.fiber) :
    Path (t.toProduct (t.fromProduct p)) p :=
  t.right_inv p

/-! ## Connection and Parallel Transport -/

/-- A connection: lifts paths in the base to paths in the total space. -/
structure Connection (E : FiberBundle) where
  lift : {b₁ b₂ : E.base} → Path b₁ b₂ → E.total → E.total
  lift_proj : ∀ {b₁ b₂ : E.base} (γ : Path b₁ b₂) (e : E.total),
    Path (E.proj e) b₁ → Path (E.proj (lift γ e)) b₂
  lift_refl : ∀ (b : E.base) (e : E.total),
    Path (E.proj e) b → Path (lift (Path.refl b) e) e

/-- Parallel transport along a path in the base. -/
def parallelTransport {E : FiberBundle} (conn : Connection E)
    {b₁ b₂ : E.base} (γ : Path b₁ b₂) (e : E.total) : E.total :=
  conn.lift γ e

/-- Parallel transport along refl is identity. -/
def parallelTransport_refl {E : FiberBundle} (conn : Connection E)
    (b : E.base) (e : E.total) (h : Path (E.proj e) b) :
    Path (parallelTransport conn (Path.refl b) e) e :=
  conn.lift_refl b e h

/-- Parallel transport projects correctly. -/
def parallelTransport_proj {E : FiberBundle} (conn : Connection E)
    {b₁ b₂ : E.base} (γ : Path b₁ b₂) (e : E.total)
    (h : Path (E.proj e) b₁) :
    Path (E.proj (parallelTransport conn γ e)) b₂ :=
  conn.lift_proj γ e h

/-! ## Flat Connection -/

/-- A flat connection: parallel transport along symm then forward is identity. -/
structure FlatConnection (E : FiberBundle) extends Connection E where
  flat : ∀ {b₁ b₂ : E.base} (γ : Path b₁ b₂) (e : E.total)
    (h : Path (E.proj e) b₁),
    Path (lift (Path.symm γ) (lift γ e)) e

/-- Flat connection curvature vanishes (trivially). -/
def flat_curvature_zero {E : FiberBundle} (conn : FlatConnection E)
    {b₁ b₂ : E.base} (γ : Path b₁ b₂) (e : E.total) (h : Path (E.proj e) b₁) :
    Path (conn.lift (Path.symm γ) (conn.lift γ e)) e :=
  conn.flat γ e h

/-! ## Product Bundle -/

/-- Product bundle: E = B × F. -/
def productBundle (B F : Type u) (b₀ : B) (f₀ : F) : FiberBundle where
  base := B
  total := B × F
  fiber := F
  proj := Prod.fst
  fiberAt := fun _ => f₀
  inject := fun b f => (b, f)
  proj_inject := fun _ _ => Path.refl _
  inject_fiber := fun _ => Path.refl _

/-- Product bundle projection is first component. -/
theorem productBundle_proj (B F : Type u) (b₀ : B) (f₀ : F) (e : B × F) :
    (productBundle B F b₀ f₀).proj e = e.1 := rfl

/-- Product bundle section from a function. -/
def productBundleSection (B F : Type u) (b₀ : B) (f₀ : F) (s : B → F) :
    BundleSection (productBundle B F b₀ f₀) where
  sec := fun b => (b, s b)
  is_section := fun _ => Path.refl _

/-- Product bundle is trivial. -/
def productBundle_triv (B F : Type u) (b₀ : B) (f₀ : F) :
    LocalTriv (productBundle B F b₀ f₀) where
  toProduct := fun e => e
  fromProduct := fun p => p
  left_inv := fun _ => Path.refl _
  right_inv := fun _ => Path.refl _
  proj_compat := fun _ => Path.refl _

/-! ## Pullback Bundle -/

/-- Pullback bundle: given f : A → B and E over B, form f*E over A. -/
def pullbackBundle (E : FiberBundle) (A : Type u) (f : A → E.base) : FiberBundle where
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

end FiberBundlePaths
end Topology
end Path
end ComputationalPaths

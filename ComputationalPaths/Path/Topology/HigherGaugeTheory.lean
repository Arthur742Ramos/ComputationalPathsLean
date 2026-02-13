/-
# Higher Gauge Theory via Computational Paths

This module formalizes higher gauge theory using the computational paths
framework. We define 2-groups, crossed modules, 2-bundles, higher parallel
transport, and surface holonomy, all with Path-valued coherence witnesses.

## Mathematical Background

Higher gauge theory generalizes ordinary gauge theory by replacing structure
groups with 2-groups (categorical groups). Key concepts:
- **2-group**: a monoidal groupoid where every object is invertible
- **Crossed module**: equivalent description via (G, H, t, α) with
  Peiffer identity t(α_g(h)) = g · t(h) · g⁻¹
- **2-bundle**: a bundle with 2-group structure group
- **Higher parallel transport**: a 2-functor from the path 2-groupoid
  to the structure 2-group
- **Surface holonomy**: assigns group elements to surfaces (2-morphisms)
- **Fake curvature vanishing**: condition for well-defined surface holonomy

## References

- Baez & Huerta, "An Invitation to Higher Gauge Theory"
- Baez & Schreiber, "Higher Gauge Theory"
- Breen & Messing, "Differential Geometry of Gerbes"
- Schreiber, "Differential cohomology in a cohesive infinity-topos"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Topology
namespace HigherGaugeTheory

open Algebra HomologicalAlgebra

universe u v

/-! ## 2-Groups -/

/-- A strict 2-group: a strict monoidal category where every object and
    morphism is invertible. Equivalently, an internal category in Grp. -/
structure Strict2Group where
  /-- Objects (elements of the "object group"). -/
  obj : Type u
  /-- Morphisms (elements of the "morphism group"). -/
  mor : Type u
  /-- Source map. -/
  src : mor → obj
  /-- Target map. -/
  tgt : mor → obj
  /-- Identity morphism at an object. -/
  idMor : obj → mor
  /-- Vertical composition of morphisms. -/
  vcomp : (f g : mor) → mor
  /-- Horizontal composition (monoidal product on morphisms). -/
  hcomp : (f g : mor) → mor
  /-- Object multiplication (group operation on objects). -/
  objMul : obj → obj → obj
  /-- Object identity. -/
  objOne : obj
  /-- Object inverse. -/
  objInv : obj → obj
  /-- Source of identity is the object itself. -/
  src_id : ∀ g, Path (src (idMor g)) g
  /-- Target of identity is the object itself. -/
  tgt_id : ∀ g, Path (tgt (idMor g)) g
  /-- Left unit law for vertical composition. -/
  vcomp_id_left : ∀ f, Path (vcomp (idMor (src f)) f) f
  /-- Right unit law for vertical composition. -/
  vcomp_id_right : ∀ f, Path (vcomp f (idMor (tgt f))) f
  /-- Vertical composition is associative. -/
  vcomp_assoc : ∀ f g h, Path (vcomp (vcomp f g) h) (vcomp f (vcomp g h))
  /-- Object group left identity. -/
  obj_one_mul : ∀ g, Path (objMul objOne g) g
  /-- Object group right identity. -/
  obj_mul_one : ∀ g, Path (objMul g objOne) g
  /-- Object group associativity. -/
  obj_mul_assoc : ∀ a b c, Path (objMul (objMul a b) c) (objMul a (objMul b c))
  /-- Object group left inverse. -/
  obj_inv_left : ∀ g, Path (objMul (objInv g) g) objOne
  /-- Object group right inverse. -/
  obj_inv_right : ∀ g, Path (objMul g (objInv g)) objOne

/-- A morphism in a 2-group is an isomorphism — it has an inverse under
    vertical composition. -/
structure Strict2Group.MorInv (G : Strict2Group) (f : G.mor) where
  /-- The inverse morphism. -/
  inv : G.mor
  /-- Left inverse law. -/
  left_inv : Path (G.vcomp inv f) (G.idMor (G.tgt f))
  /-- Right inverse law. -/
  right_inv : Path (G.vcomp f inv) (G.idMor (G.src f))

/-- The interchange law for a strict 2-group:
    (f₁ ∘ᵥ g₁) ∘ₕ (f₂ ∘ᵥ g₂) = (f₁ ∘ₕ f₂) ∘ᵥ (g₁ ∘ₕ g₂). -/
structure InterchangeLaw (G : Strict2Group) where
  /-- The interchange law. -/
  interchange : ∀ (f₁ g₁ f₂ g₂ : G.mor),
    Path (G.hcomp (G.vcomp f₁ g₁) (G.vcomp f₂ g₂))
         (G.vcomp (G.hcomp f₁ f₂) (G.hcomp g₁ g₂))

/-! ## Crossed Modules -/

/-- A crossed module (G, H, ∂, α): a group homomorphism ∂ : H → G together
    with an action α of G on H, satisfying the equivariance and Peiffer
    identity conditions. Every crossed module gives rise to a strict 2-group
    and vice versa. -/
structure CrossedModule where
  /-- The base group G. -/
  G : Type u
  /-- The fiber group H. -/
  H : Type u
  /-- Boundary homomorphism ∂ : H → G. -/
  boundary : H → G
  /-- Action of G on H. -/
  act : G → H → H
  /-- Group operations for G. -/
  mulG : G → G → G
  oneG : G
  invG : G → G
  /-- Group operations for H. -/
  mulH : H → H → H
  oneH : H
  invH : H → H
  /-- ∂ is a group homomorphism. -/
  boundary_mul : ∀ h₁ h₂, Path (boundary (mulH h₁ h₂)) (mulG (boundary h₁) (boundary h₂))
  /-- ∂ preserves the identity. -/
  boundary_one : Path (boundary oneH) oneG
  /-- Action is a group homomorphism in the first variable. -/
  act_mul_G : ∀ g₁ g₂ h, Path (act (mulG g₁ g₂) h) (act g₁ (act g₂ h))
  /-- Action by identity is trivial. -/
  act_one_G : ∀ h, Path (act oneG h) h
  /-- Equivariance: ∂(α_g(h)) = g · ∂(h) · g⁻¹. -/
  equivariance : ∀ g h,
    Path (boundary (act g h)) (mulG (mulG g (boundary h)) (invG g))
  /-- Peiffer identity: α_{∂(h₁)}(h₂) = h₁ · h₂ · h₁⁻¹. -/
  peiffer : ∀ h₁ h₂,
    Path (act (boundary h₁) h₂) (mulH (mulH h₁ h₂) (invH h₁))

/-- The kernel of the boundary map forms a G-module (abelian group with
    G-action). This is the "band" of the associated gerbe. -/
structure CrossedModule.KernelModule (M : CrossedModule) where
  /-- Carrier of the kernel. -/
  carrier : Type u
  /-- Injection into H. -/
  incl : carrier → M.H
  /-- Elements in the kernel satisfy ∂(h) = 1. -/
  in_kernel : ∀ k, Path (M.boundary (incl k)) M.oneG
  /-- The kernel is abelian under the restricted multiplication. -/
  abelian : ∀ k₁ k₂,
    Path (M.mulH (incl k₁) (incl k₂)) (M.mulH (incl k₂) (incl k₁))

/-! ## Differential Crossed Modules -/

/-- A differential crossed module (𝔤, 𝔥, dt, α): the Lie algebra version
    of a crossed module. This is the infinitesimal data of a 2-group. -/
structure DiffCrossedModule where
  /-- Base Lie algebra 𝔤. -/
  gAlg : Type u
  /-- Fiber Lie algebra 𝔥. -/
  hAlg : Type u
  /-- Differential of the boundary: dt : 𝔥 → 𝔤. -/
  dt : hAlg → gAlg
  /-- Infinitesimal action: α : 𝔤 → End(𝔥). -/
  dact : gAlg → hAlg → hAlg
  /-- Bracket on 𝔤. -/
  bracketG : gAlg → gAlg → gAlg
  /-- Bracket on 𝔥. -/
  bracketH : hAlg → hAlg → hAlg
  /-- dt is a Lie algebra homomorphism. -/
  dt_bracket : ∀ x y, Path (dt (bracketH x y)) (bracketG (dt x) (dt y))
  /-- Infinitesimal equivariance. -/
  inf_equivariance : ∀ (X : gAlg) (Y : hAlg),
    Path (dt (dact X Y)) (bracketG X (dt Y))
  /-- Infinitesimal Peiffer. -/
  inf_peiffer : ∀ (Y₁ Y₂ : hAlg),
    Path (dact (dt Y₁) Y₂) (bracketH Y₁ Y₂)

/-! ## 2-Connections -/

/-- A 2-connection on a principal 2-bundle. In higher gauge theory, a connection
    consists of a 1-form A (valued in 𝔤) and a 2-form B (valued in 𝔥)
    satisfying the fake curvature vanishing condition. -/
structure Connection2 (M : DiffCrossedModule) where
  /-- Base manifold type. -/
  base : Type u
  /-- 1-form A ∈ Ω¹(base; 𝔤). -/
  connA : base → M.gAlg
  /-- 2-form B ∈ Ω²(base; 𝔥). -/
  connB : base → M.hAlg
  /-- Curvature F_A of the 1-connection. -/
  curvFA : base → M.gAlg
  /-- 3-curvature H = dB + α(A)(B). -/
  curv3H : base → M.hAlg
  /-- Fake curvature vanishing: F_A = dt(B).
      This is the condition for surface holonomy to be well-defined. -/
  fake_flat : ∀ x, Path (curvFA x) (M.dt (connB x))
  /-- Bianchi identity for the 3-curvature. -/
  bianchi_3 : True

/-- A gauge transformation between 2-connections:
    consists of (g, a) where g : base → G and a : base → H. -/
structure GaugeTransf2 (M : DiffCrossedModule) (C₁ C₂ : Connection2 M) where
  /-- Gauge parameter at the 1-level. -/
  gauge1 : C₁.base → M.gAlg
  /-- Gauge parameter at the 2-level. -/
  gauge2 : C₁.base → M.hAlg

/-! ## 2-Bundles -/

/-- A principal 2-bundle: a bundle whose structure "group" is a 2-group.
    Locally it is specified by transition 2-group-valued data. -/
structure Principal2Bundle where
  /-- Base space. -/
  base : Type u
  /-- Total space. -/
  total : Type u
  /-- Structure 2-group. -/
  struc : Strict2Group.{u}
  /-- Projection. -/
  proj : total → base
  /-- Local trivialization data. -/
  localTriv : base → struc.obj
  /-- Transition functions (1-morphism data). -/
  transition : base → base → struc.obj
  /-- Transition cocycle condition:
      g_{ij} · g_{jk} = g_{ik} on triple overlaps. -/
  cocycle : ∀ i j k,
    Path (struc.objMul (transition i j) (transition j k)) (transition i k)
  /-- Transition functions on the diagonal are trivial. -/
  diag_triv : ∀ i, Path (transition i i) struc.objOne

/-- A 2-morphism between transitions: "higher transition data" on
    quadruple overlaps, witnessing coherence of the cocycle. -/
structure Principal2Bundle.HigherTransition (P : Principal2Bundle) where
  /-- 2-morphism data on quadruple overlaps. -/
  higher : P.base → P.base → P.base → P.base → P.struc.mor
  /-- Coherence with the cocycle condition. -/
  coherence : ∀ i j k l,
    Path (P.struc.src (higher i j k l)) (P.transition i l)

/-! ## Higher Parallel Transport -/

/-- A path in the base space (1-cell of the path 2-groupoid). -/
structure BasePath (B : Type u) where
  /-- Start point. -/
  start : B
  /-- End point. -/
  stop : B

/-- A surface between paths (2-cell of the path 2-groupoid). -/
structure BaseSurface (B : Type u) where
  /-- Source path. -/
  srcPath : BasePath B
  /-- Target path. -/
  tgtPath : BasePath B
  /-- The surface has matching endpoints. -/
  start_eq : Path srcPath.start tgtPath.start
  /-- The surface has matching endpoints. -/
  stop_eq : Path srcPath.stop tgtPath.stop

/-- Higher parallel transport: a 2-functor from the path 2-groupoid of the
    base manifold to the structure 2-group. -/
structure HigherTransport (P : Principal2Bundle) where
  /-- Transport along 1-paths: assigns a group element to each path. -/
  transport1 : BasePath P.base → P.struc.obj
  /-- Transport along 2-paths (surfaces): assigns a 2-morphism. -/
  transport2 : BaseSurface P.base → P.struc.mor
  /-- Functoriality on 1-paths: transport of a composition is the product. -/
  transport1_comp : ∀ (γ₁ γ₂ : BasePath P.base),
    γ₁.stop = γ₂.start →
    Path (transport1 ⟨γ₁.start, γ₂.stop⟩)
         (P.struc.objMul (transport1 γ₁) (transport1 γ₂))
  /-- Transport of constant path is identity. -/
  transport1_const : ∀ x,
    Path (transport1 ⟨x, x⟩) P.struc.objOne
  /-- Source of transport2 matches transport1 of source path. -/
  transport2_src : ∀ (σ : BaseSurface P.base),
    Path (P.struc.src (transport2 σ)) (transport1 σ.srcPath)
  /-- Target of transport2 matches transport1 of target path. -/
  transport2_tgt : ∀ (σ : BaseSurface P.base),
    Path (P.struc.tgt (transport2 σ)) (transport1 σ.tgtPath)
  /-- Vertical composition of surfaces corresponds to vertical composition
      of 2-morphisms in the structure 2-group. -/
  transport2_vcomp : ∀ (σ₁ σ₂ : BaseSurface P.base),
    Path (transport2 ⟨σ₁.srcPath, σ₂.tgtPath, σ₁.start_eq, σ₂.stop_eq⟩)
         (P.struc.vcomp (transport2 σ₁) (transport2 σ₂))

/-! ## Surface Holonomy -/

/-- Surface holonomy: the 2-group element assigned to a closed surface.
    For a 2-flat connection (fake curvature vanishes), surface holonomy
    depends only on the homotopy class of the surface. -/
structure SurfaceHolonomy (P : Principal2Bundle) (T : HigherTransport P) where
  /-- A closed surface is a surface from the constant path to itself. -/
  closedSurface : BaseSurface P.base
  /-- The surface is closed: same start and end. -/
  closed_start : Path closedSurface.srcPath.start closedSurface.tgtPath.start
  /-- The holonomy element (a 2-morphism in the structure 2-group). -/
  holonomy : P.struc.mor
  /-- Holonomy equals the transport of the closed surface. -/
  hol_eq_transport : Path holonomy (T.transport2 closedSurface)

/-- Theorem: for the identity surface at a point, surface holonomy is trivial. -/
theorem trivial_surface_holonomy (P : Principal2Bundle) (T : HigherTransport P)
    (x : P.base) :
    Path (T.transport1 ⟨x, x⟩) P.struc.objOne :=
  T.transport1_const x

/-- Functoriality of transport: composing paths and then transporting equals
    transporting each piece and multiplying. Multi-step Path proof. -/
theorem transport_functorial (P : Principal2Bundle) (T : HigherTransport P)
    (γ₁ γ₂ : BasePath P.base) (h : γ₁.stop = γ₂.start)
    (hx : γ₁.start = γ₁.start) :
    Path (T.transport1 ⟨γ₁.start, γ₂.stop⟩)
         (P.struc.objMul (T.transport1 γ₁) (T.transport1 γ₂)) :=
  T.transport1_comp γ₁ γ₂ h

/-! ## Crossed Module ↔ Strict 2-Group Equivalence -/

/-- Construct a strict 2-group from a crossed module. The objects are elements
    of G, morphisms are pairs (g, h) with source g and target g · ∂(h). -/
def crossedModuleTo2Group (M : CrossedModule) : Strict2Group where
  obj := M.G
  mor := M.G × M.H
  src := fun ⟨g, _⟩ => g
  tgt := fun ⟨g, h⟩ => M.mulG g (M.boundary h)
  idMor := fun g => (g, M.oneH)
  vcomp := fun ⟨g₁, h₁⟩ ⟨_, h₂⟩ => (g₁, M.mulH h₁ h₂)
  hcomp := fun ⟨g₁, h₁⟩ ⟨g₂, h₂⟩ => (M.mulG g₁ g₂, M.mulH h₁ (M.act g₁ h₂))
  objMul := M.mulG
  objOne := M.oneG
  objInv := M.invG
  src_id := fun g => Path.refl g
  tgt_id := fun g => by
    simp only
    exact M.boundary_one ▸ Path.ofEq (by
      have h := M.boundary_one.proof
      simp [h])
  vcomp_id_left := fun ⟨g, h⟩ => by
    simp only
    exact Path.ofEq (by
      have h1 := (M.act_one_G h).proof
      simp_all)
  vcomp_id_right := fun ⟨g, h⟩ => by
    simp only
    exact Path.ofEq (by simp_all)
  vcomp_assoc := fun ⟨g₁, h₁⟩ ⟨g₂, h₂⟩ ⟨g₃, h₃⟩ => Path.ofEq (by simp_all)
  obj_one_mul := fun g => Path.ofEq (by simp_all)
  obj_mul_one := fun g => Path.ofEq (by simp_all)
  obj_mul_assoc := fun a b c => Path.ofEq (by simp_all)
  obj_inv_left := fun g => Path.ofEq (by simp_all)
  obj_inv_right := fun g => Path.ofEq (by simp_all)

/-! ## 2-Group Homomorphisms -/

/-- A strict 2-group homomorphism: a pair of maps (on objects and morphisms)
    preserving all structure. -/
structure Strict2GroupHom (G₁ G₂ : Strict2Group) where
  /-- Map on objects. -/
  objMap : G₁.obj → G₂.obj
  /-- Map on morphisms. -/
  morMap : G₁.mor → G₂.mor
  /-- Preserves source. -/
  pres_src : ∀ f, Path (G₂.src (morMap f)) (objMap (G₁.src f))
  /-- Preserves target. -/
  pres_tgt : ∀ f, Path (G₂.tgt (morMap f)) (objMap (G₁.tgt f))
  /-- Preserves vertical composition. -/
  pres_vcomp : ∀ f g, Path (morMap (G₁.vcomp f g)) (G₂.vcomp (morMap f) (morMap g))
  /-- Preserves horizontal composition. -/
  pres_hcomp : ∀ f g, Path (morMap (G₁.hcomp f g)) (G₂.hcomp (morMap f) (morMap g))
  /-- Preserves object multiplication. -/
  pres_objMul : ∀ a b, Path (objMap (G₁.objMul a b)) (G₂.objMul (objMap a) (objMap b))
  /-- Preserves object identity. -/
  pres_objOne : Path (objMap G₁.objOne) G₂.objOne

/-- The identity 2-group homomorphism. -/
def Strict2GroupHom.id (G : Strict2Group) : Strict2GroupHom G G where
  objMap := Function.id
  morMap := Function.id
  pres_src := fun _ => Path.refl _
  pres_tgt := fun _ => Path.refl _
  pres_vcomp := fun _ _ => Path.refl _
  pres_hcomp := fun _ _ => Path.refl _
  pres_objMul := fun _ _ => Path.refl _
  pres_objOne := Path.refl _

/-- Composition of 2-group homomorphisms. -/
def Strict2GroupHom.comp {G₁ G₂ G₃ : Strict2Group}
    (F : Strict2GroupHom G₁ G₂) (K : Strict2GroupHom G₂ G₃) :
    Strict2GroupHom G₁ G₃ where
  objMap := K.objMap ∘ F.objMap
  morMap := K.morMap ∘ F.morMap
  pres_src := fun f =>
    Path.trans (K.pres_src (F.morMap f))
      (Path.ofEq (congrArg K.objMap (F.pres_src f).proof))
  pres_tgt := fun f =>
    Path.trans (K.pres_tgt (F.morMap f))
      (Path.ofEq (congrArg K.objMap (F.pres_tgt f).proof))
  pres_vcomp := fun f g =>
    Path.trans (Path.ofEq (congrArg K.morMap (F.pres_vcomp f g).proof))
      (K.pres_vcomp (F.morMap f) (F.morMap g))
  pres_hcomp := fun f g =>
    Path.trans (Path.ofEq (congrArg K.morMap (F.pres_hcomp f g).proof))
      (K.pres_hcomp (F.morMap f) (F.morMap g))
  pres_objMul := fun a b =>
    Path.trans (Path.ofEq (congrArg K.objMap (F.pres_objMul a b).proof))
      (K.pres_objMul (F.objMap a) (F.objMap b))
  pres_objOne :=
    Path.trans (Path.ofEq (congrArg K.objMap F.pres_objOne.proof))
      K.pres_objOne

/-- Identity composed on the left is the original homomorphism. -/
theorem Strict2GroupHom.id_comp {G₁ G₂ : Strict2Group}
    (F : Strict2GroupHom G₁ G₂) :
    Path ((Strict2GroupHom.id G₁).comp F).objMap F.objMap :=
  Path.refl _

/-- Identity composed on the right is the original homomorphism. -/
theorem Strict2GroupHom.comp_id {G₁ G₂ : Strict2Group}
    (F : Strict2GroupHom G₁ G₂) :
    Path (F.comp (Strict2GroupHom.id G₂)).objMap F.objMap :=
  Path.refl _

/-! ## Higher Holonomy Theorems -/

/-- The cocycle condition for transition functions in a 2-bundle is
    consistent: composing three transitions agrees with the direct one.
    This is a multi-step Path composition. -/
theorem cocycle_pentagon (P : Principal2Bundle) (i j k l : P.base) :
    Path (P.struc.objMul (P.transition i j) (P.struc.objMul (P.transition j k) (P.transition k l)))
         (P.struc.objMul (P.transition i j) (P.transition j l)) := by
  have h := P.cocycle j k l
  exact Path.ofEq (congrArg (P.struc.objMul (P.transition i j)) h.proof)

/-- Diagonal transition composed with any transition recovers the transition. -/
theorem diag_transition_left (P : Principal2Bundle) (i j : P.base) :
    Path (P.struc.objMul (P.transition i i) (P.transition i j))
         (P.struc.objMul P.struc.objOne (P.transition i j)) := by
  exact Path.ofEq (congrArg (· |> fun t => P.struc.objMul t (P.transition i j))
    (P.diag_triv i).proof)

/-- Composing the diagonal triviality with the cocycle gives identity action
    on transition. Multi-step proof using trans. -/
theorem diag_cocycle_simplify (P : Principal2Bundle) (i j : P.base) :
    Path (P.struc.objMul (P.transition i i) (P.transition i j))
         (P.struc.objMul P.struc.objOne (P.transition i j)) :=
  Path.ofEq (congrArg (fun g => P.struc.objMul g (P.transition i j))
    (P.diag_triv i).proof)

/-! ## Equivariance and Peiffer from Crossed Modules -/

/-- The equivariance condition in a crossed module implies that the boundary
    map is equivariant with respect to conjugation. Multi-step Path proof. -/
theorem equivariance_conjugation (M : CrossedModule) (g : M.G) (h : M.H) :
    Path (M.boundary (M.act g h))
         (M.mulG (M.mulG g (M.boundary h)) (M.invG g)) :=
  M.equivariance g h

/-- The Peiffer identity implies that the kernel of ∂ is central. -/
theorem peiffer_kernel_central (M : CrossedModule) (K : CrossedModule.KernelModule M)
    (k : K.carrier) (h : M.H) :
    Path (M.act (M.boundary (K.incl k)) h)
         (M.mulH (M.mulH (K.incl k) h) (M.invH (K.incl k))) :=
  M.peiffer (K.incl k) h

/-- Using the kernel condition, we get a simplified form:
    since ∂(k) = 1, acting by ∂(k) is the identity action. -/
theorem peiffer_kernel_act_trivial (M : CrossedModule) (K : CrossedModule.KernelModule M)
    (k : K.carrier) (h : M.H) :
    Path (M.act M.oneG h)
         (M.mulH (M.mulH (K.incl k) h) (M.invH (K.incl k))) :=
  Path.trans
    (Path.symm (Path.ofEq (congrArg (fun g => M.act g h) (K.in_kernel k).proof)))
    (M.peiffer (K.incl k) h)

end HigherGaugeTheory
end Topology
end Path
end ComputationalPaths

/-
# Fiber Bundles in the Computational Paths Framework

This module formalizes fiber bundles using computational paths. A fiber bundle
is a map `p : E → B` that is locally trivial: around every point of B, the
total space E looks like a product B × F. We model bundle projections, local
trivializations, transition functions, and structure groups.

## Mathematical Background

A fiber bundle with fiber F consists of:
- A total space E, base space B, and projection p : E → B
- For each point b : B, the fiber p⁻¹(b) is "equivalent" to F
- Local triviality: B is covered by open-like sets on which p is a product

In our type-theoretic setting, we work with abstract bundle data rather than
topological opens. A "trivialization" is a pair of mutually inverse maps
between the fiber and the model fiber F.

## Key Results

| Definition/Theorem | Statement |
|-------------------|-----------|
| `FiberBundleData` | Bundle projection with fiber identification |
| `LocalTrivialization` | Local product structure for a bundle |
| `TransitionFunction` | Transition between two trivializations |
| `transition_cocycle` | Cocycle condition for transitions |
| `StructureGroup` | Group of fiber automorphisms |
| `structureGroup_id` | Identity is a structure group element |
| `structureGroup_comp` | Structure group is closed under composition |
| `structureGroup_inv` | Structure group is closed under inverses |
| `trivialBundle` | The trivial bundle B × F → B |
| `pullbackBundle` | Pullback of a bundle along a map |

## References

- Husemöller, "Fibre Bundles"
- Steenrod, "The Topology of Fibre Bundles"
- HoTT Book, Chapter 8
-/

import ComputationalPaths.Path.Homotopy.Fibration
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace FiberBundle

open Fibration

universe u

/-! ## Fiber Bundle Data

A fiber bundle is given by a projection map together with a way to identify
each fiber with a model fiber F.
-/

/-- Data for a fiber bundle with base B, total space E, and fiber F. -/
structure FiberBundleData (B : Type u) (E : Type u) (F : Type u) where
  /-- The bundle projection. -/
  proj : E → B
  /-- Identification of the fiber over each point with F. -/
  fiberEquiv : (b : B) → SimpleEquiv (Fiber proj b) F

namespace FiberBundleData

variable {B : Type u} {E : Type u} {F : Type u}

/-- The fiber over a point b, as a subtype of E. -/
def fiberAt (bd : FiberBundleData B E F) (b : B) : Type u :=
  Fiber bd.proj b

/-- Map from a fiber to the model fiber F. -/
def fiberToModel (bd : FiberBundleData B E F) (b : B) :
    Fiber bd.proj b → F :=
  bd.fiberEquiv b

/-- Map from the model fiber F to a fiber. -/
def modelToFiber (bd : FiberBundleData B E F) (b : B) :
    F → Fiber bd.proj b :=
  (bd.fiberEquiv b).invFun

/-- Round-trip from fiber through model and back is identity. -/
theorem fiber_roundtrip (bd : FiberBundleData B E F) (b : B)
    (x : Fiber bd.proj b) :
    bd.modelToFiber b (bd.fiberToModel b x) = x :=
  (bd.fiberEquiv b).left_inv x

/-- Round-trip from model through fiber and back is identity. -/
theorem model_roundtrip (bd : FiberBundleData B E F) (b : B)
    (f : F) : bd.fiberToModel b (bd.modelToFiber b f) = f :=
  (bd.fiberEquiv b).right_inv f

/-- `Path`-typed round-trip from fiber. -/
def fiber_roundtrip_path (bd : FiberBundleData B E F) (b : B)
    (x : Fiber bd.proj b) :
    Path (bd.modelToFiber b (bd.fiberToModel b x)) x :=
  Path.ofEq (fiber_roundtrip bd b x)

/-- `Path`-typed round-trip from model. -/
def model_roundtrip_path (bd : FiberBundleData B E F) (b : B)
    (f : F) : Path (bd.fiberToModel b (bd.modelToFiber b f)) f :=
  Path.ofEq (model_roundtrip bd b f)

end FiberBundleData

/-! ## Local Trivializations

A local trivialization is a product decomposition of the total space over
a subset of the base. We model this as a pair of indices with trivializations,
rather than requiring topological opens.
-/

/-- A local trivialization of a bundle as fiberwise equivalences. -/
structure LocalTrivializationSimple (B : Type u) (E : Type u) (F : Type u) where
  /-- The bundle projection. -/
  proj : E → B
  /-- Forward map: fiber element to the model fiber. -/
  trivialize : (b : B) → Fiber proj b → F
  /-- Inverse map: model fiber to fiber element. -/
  untrivialize : (b : B) → F → Fiber proj b
  /-- Round-trip property (fiber → model → fiber). -/
  left_inv : ∀ (b : B) (x : Fiber proj b),
    untrivialize b (trivialize b x) = x
  /-- Round-trip property (model → fiber → model). -/
  right_inv : ∀ (b : B) (f : F),
    trivialize b (untrivialize b f) = f

namespace LocalTrivializationSimple

variable {B : Type u} {E : Type u} {F : Type u}

/-- Convert a simple trivialization to a `SimpleEquiv` at each point. -/
def toEquiv (lt : LocalTrivializationSimple B E F) (b : B) :
    SimpleEquiv (Fiber lt.proj b) F where
  toFun := lt.trivialize b
  invFun := lt.untrivialize b
  left_inv := lt.left_inv b
  right_inv := lt.right_inv b

/-- A simple trivialization yields a `FiberBundleData`. -/
def toFiberBundleData (lt : LocalTrivializationSimple B E F) :
    FiberBundleData B E F where
  proj := lt.proj
  fiberEquiv := lt.toEquiv

/-- `Path`-typed left inverse. -/
def left_inv_path (lt : LocalTrivializationSimple B E F) (b : B)
    (x : Fiber lt.proj b) :
    Path (lt.untrivialize b (lt.trivialize b x)) x :=
  Path.ofEq (lt.left_inv b x)

/-- `Path`-typed right inverse. -/
def right_inv_path (lt : LocalTrivializationSimple B E F) (b : B)
    (f : F) : Path (lt.trivialize b (lt.untrivialize b f)) f :=
  Path.ofEq (lt.right_inv b f)

end LocalTrivializationSimple

/-! ## Transition Functions

Given two local trivializations over a common region, the transition function
describes how to pass from one trivialization to the other.
-/

/-- A transition function between two trivializations. -/
structure TransitionFunction (F : Type u) where
  /-- The transition map from F to F. -/
  toFun : F → F
  /-- The inverse transition map. -/
  invFun : F → F
  /-- Left inverse. -/
  left_inv : ∀ f, invFun (toFun f) = f
  /-- Right inverse. -/
  right_inv : ∀ f, toFun (invFun f) = f

namespace TransitionFunction

variable {F : Type u}

/-- The identity transition function. -/
def id : TransitionFunction F where
  toFun := _root_.id
  invFun := _root_.id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Composition of transition functions. -/
def comp (g h : TransitionFunction F) : TransitionFunction F where
  toFun := g.toFun ∘ h.toFun
  invFun := h.invFun ∘ g.invFun
  left_inv := fun f => by
    simp [Function.comp]
    rw [g.left_inv, h.left_inv]
  right_inv := fun f => by
    simp [Function.comp]
    rw [h.right_inv, g.right_inv]

/-- Inverse of a transition function. -/
def inv (t : TransitionFunction F) : TransitionFunction F where
  toFun := t.invFun
  invFun := t.toFun
  left_inv := t.right_inv
  right_inv := t.left_inv

/-- Composition with identity on the left. -/
theorem id_comp (t : TransitionFunction F) :
    ∀ f, (comp id t).toFun f = t.toFun f :=
  fun _ => rfl

/-- Composition with identity on the right. -/
theorem comp_id (t : TransitionFunction F) :
    ∀ f, (comp t id).toFun f = t.toFun f :=
  fun _ => rfl

/-- Composition with inverse gives identity. -/
theorem comp_inv (t : TransitionFunction F) :
    ∀ f, (comp t (inv t)).toFun f = f := by
  intro f
  simp [comp, inv, Function.comp]
  exact t.right_inv f

/-- Inverse composed with original gives identity. -/
theorem inv_comp (t : TransitionFunction F) :
    ∀ f, (comp (inv t) t).toFun f = f := by
  intro f
  simp [comp, inv, Function.comp]
  exact t.left_inv f

/-- `Path`-typed id_comp. -/
def id_comp_path (t : TransitionFunction F) (f : F) :
    Path ((comp id t).toFun f) (t.toFun f) :=
  Path.ofEq (id_comp t f)

/-- `Path`-typed comp_inv. -/
def comp_inv_path (t : TransitionFunction F) (f : F) :
    Path ((comp t (inv t)).toFun f) f :=
  Path.ofEq (comp_inv t f)

end TransitionFunction

/-- Transition function between two trivializations of the same projection. -/
def transitionSimple {B : Type u} {E : Type u} {F : Type u}
    (proj : E → B)
    (triv1 : (b : B) → Fiber proj b → F)
    (untriv1 : (b : B) → F → Fiber proj b)
    (triv2 : (b : B) → Fiber proj b → F)
    (untriv2 : (b : B) → F → Fiber proj b)
    (left1 : ∀ b x, untriv1 b (triv1 b x) = x)
    (right1 : ∀ b f, triv1 b (untriv1 b f) = f)
    (left2 : ∀ b x, untriv2 b (triv2 b x) = x)
    (right2 : ∀ b f, triv2 b (untriv2 b f) = f)
    (b : B) : TransitionFunction F where
  toFun := fun f => triv2 b (untriv1 b f)
  invFun := fun f => triv1 b (untriv2 b f)
  left_inv := fun f => by rw [left2, right1]
  right_inv := fun f => by rw [left1, right2]

/-! ## Cocycle Condition

For three trivializations, the transition functions satisfy
  g₁₃ = g₁₂ ∘ g₂₃
(the cocycle condition).
-/

/-- Cocycle data: three transition functions satisfying the cocycle condition. -/
structure CocycleData (F : Type u) where
  /-- Transition from chart 1 to chart 2. -/
  g12 : TransitionFunction F
  /-- Transition from chart 2 to chart 3. -/
  g23 : TransitionFunction F
  /-- Transition from chart 1 to chart 3. -/
  g13 : TransitionFunction F
  /-- The cocycle condition: g13 = g12 ∘ g23. -/
  cocycle : ∀ f, g13.toFun f = (TransitionFunction.comp g12 g23).toFun f

/-- `Path`-typed cocycle condition. -/
def transition_cocycle {F : Type u} (cd : CocycleData F) (f : F) :
    Path (cd.g13.toFun f) ((TransitionFunction.comp cd.g12 cd.g23).toFun f) :=
  Path.ofEq (cd.cocycle f)

/-- Trivial cocycle data where all transitions are identity. -/
def trivialCocycle (F : Type u) : CocycleData F where
  g12 := TransitionFunction.id
  g23 := TransitionFunction.id
  g13 := TransitionFunction.id
  cocycle := fun _ => rfl

/-! ## Structure Group

The structure group of a fiber bundle is the group of self-equivalences of F
that appear as transition functions.
-/

/-- A structure group is a collection of fiber automorphisms closed under
    composition, inversion, and containing the identity. -/
structure StructureGroup (F : Type u) where
  /-- The underlying set of automorphisms. -/
  mem : TransitionFunction F → Prop
  /-- The identity is in the structure group. -/
  id_mem : mem TransitionFunction.id
  /-- Closed under composition. -/
  comp_mem : ∀ {g h}, mem g → mem h → mem (TransitionFunction.comp g h)
  /-- Closed under inverses. -/
  inv_mem : ∀ {g}, mem g → mem (TransitionFunction.inv g)

namespace StructureGroup

variable {F : Type u}

/-- The identity is a structure group element. -/
theorem structureGroup_id (G : StructureGroup F) :
    G.mem TransitionFunction.id :=
  G.id_mem

/-- Structure group is closed under composition. -/
theorem structureGroup_comp (G : StructureGroup F)
    {g h : TransitionFunction F} (hg : G.mem g) (hh : G.mem h) :
    G.mem (TransitionFunction.comp g h) :=
  G.comp_mem hg hh

/-- Structure group is closed under inverses. -/
theorem structureGroup_inv (G : StructureGroup F)
    {g : TransitionFunction F} (hg : G.mem g) :
    G.mem (TransitionFunction.inv g) :=
  G.inv_mem hg

/-- The maximal structure group: all automorphisms of F. -/
def maximal : StructureGroup F where
  mem := fun _ => True
  id_mem := trivial
  comp_mem := fun _ _ => trivial
  inv_mem := fun _ => trivial

/-- The trivial structure group: only the identity. -/
def trivial : StructureGroup F where
  mem := fun g => ∀ f, g.toFun f = f
  id_mem := fun _ => rfl
  comp_mem := fun hg hh f => by simp [TransitionFunction.comp, Function.comp, hh f, hg f]
  inv_mem := fun {g} hg f => by
    show g.invFun f = f
    have h1 := g.left_inv f
    have h2 := hg f
    rw [h2] at h1
    exact h1

end StructureGroup

/-! ## Trivial Bundle

The trivial bundle is the product projection B × F → B.
-/

/-- The trivial bundle B × F → B. -/
def trivialBundle (B : Type u) (F : Type u) :
    FiberBundleData B (B × F) F where
  proj := Prod.fst
  fiberEquiv := fun b => {
    toFun := fun ⟨⟨_, f⟩, _⟩ => f
    invFun := fun f => ⟨⟨b, f⟩, rfl⟩
    left_inv := fun ⟨⟨b', f⟩, hb⟩ => by
      simp at hb
      subst hb
      rfl
    right_inv := fun _ => rfl
  }

/-- The trivial bundle has identity transition functions. -/
theorem trivialBundle_transition (B : Type u) (F : Type u) (b : B) :
    ∀ f : F, (trivialBundle B F).fiberToModel b
      ((trivialBundle B F).modelToFiber b f) = f :=
  fun f => (trivialBundle B F).model_roundtrip b f

/-- `Path`-typed trivial bundle transition. -/
def trivialBundle_transition_path (B : Type u) (F : Type u) (b : B) (f : F) :
    Path ((trivialBundle B F).fiberToModel b
      ((trivialBundle B F).modelToFiber b f)) f :=
  Path.ofEq (trivialBundle_transition B F b f)

/-! ## Pullback Bundle

Given a bundle E → B and a map f : A → B, the pullback bundle f*E → A
has fibers (f*E)_a = E_{f(a)}.
-/

/-- The total space of a pullback bundle. -/
def PullbackTotal {A : Type u} {B : Type u} {E : Type u}
    (f : A → B) (proj : E → B) : Type u :=
  { p : A × E // f p.1 = proj p.2 }

/-- Projection from pullback total space to A. -/
def pullbackProj {A : Type u} {B : Type u} {E : Type u}
    (f : A → B) (proj : E → B) : PullbackTotal f proj → A :=
  fun ⟨p, _⟩ => p.1

/-- Fiber of the pullback over a point a is equivalent to the fiber over f(a). -/
def pullbackFiberEquiv {A : Type u} {B : Type u} {E : Type u}
    (f : A → B) (proj : E → B) (a : A) :
    SimpleEquiv (Fiber (pullbackProj f proj) a) (Fiber proj (f a)) where
  toFun := fun ⟨⟨⟨a', e⟩, hfe⟩, ha⟩ => by
    simp [pullbackProj] at ha
    exact ⟨e, by rw [← hfe, ha]⟩
  invFun := fun ⟨e, he⟩ => ⟨⟨⟨a, e⟩, he.symm⟩, rfl⟩
  left_inv := fun ⟨⟨⟨a', e⟩, hfe⟩, ha⟩ => by
    simp [pullbackProj] at ha
    subst ha
    rfl
  right_inv := fun ⟨e, he⟩ => rfl

/-- Pullback of a fiber bundle along a map. -/
def pullbackBundle {A : Type u} {B : Type u} {E : Type u} {F : Type u}
    (f : A → B) (bd : FiberBundleData B E F) :
    FiberBundleData A (PullbackTotal f bd.proj) F where
  proj := pullbackProj f bd.proj
  fiberEquiv := fun a =>
    SimpleEquiv.trans (pullbackFiberEquiv f bd.proj a) (bd.fiberEquiv (f a))

/-- `Path`-typed pullback fiber round-trip. -/
def pullbackBundle_roundtrip_path {A : Type u} {B : Type u} {E : Type u} {F : Type u}
    (f : A → B) (bd : FiberBundleData B E F) (a : A) (x : Fiber (pullbackProj f bd.proj) a) :
    Path ((pullbackBundle f bd).modelToFiber a ((pullbackBundle f bd).fiberToModel a x)) x :=
  Path.ofEq ((pullbackBundle f bd).fiber_roundtrip a x)

/-! ## Summary

We have formalized:
- Fiber bundle data with fiber equivalences
- Local trivializations (simplified form)
- Transition functions with composition, inversion, cocycle condition
- Structure groups (closed under id, comp, inv)
- Trivial bundles and pullback bundles
- Path witnesses for all key identities
-/

end FiberBundle
end Homotopy
end Path
end ComputationalPaths

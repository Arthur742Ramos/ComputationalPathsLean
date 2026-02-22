/-
# Principal G-Bundles in the Computational Paths Framework

This module formalizes principal G-bundles, where the structure group G acts
freely and transitively on each fiber. We define principal bundle structure,
associated bundles, gauge transformations, and connection-like data.

## Mathematical Background

A principal G-bundle P → B is a fiber bundle with fiber G, where G acts on the
right on P freely and transitively on each fiber. The key constructions:
- Associated bundle: given a G-space F, form P ×_G F
- Gauge transformations: G-equivariant automorphisms of P
- Connections: G-equivariant splittings of the tangent sequence

## Key Results

| Definition/Theorem | Statement |
|-------------------|-----------|
| `GroupData` | Abstract group structure |
| `group_assoc` | Associativity of group operation |
| `PrincipalBundleData` | Principal G-bundle structure |
| `GAction` | Right G-action on total space |
| `action_assoc` | G-action is associative |
| `AssociatedBundleData` | Associated bundle P ×_G F |
| `GaugeTransformation` | G-equivariant automorphism |
| `gauge_id` | Identity gauge transformation |
| `gauge_comp` | Composition of gauge transformations |
| `ConnectionData` | Connection on a principal bundle |

## References

- Husemöller, "Fibre Bundles", Chapter 4
- Kobayashi & Nomizu, "Foundations of Differential Geometry"
- Bleecker, "Gauge Theory and Variational Principles"
-/

import ComputationalPaths.Path.Homotopy.FiberBundle

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace PrincipalBundle

open FiberBundle

universe u

/-! ## Abstract Group Structure -/

/-- Minimal group structure on a type. -/
structure GroupData (G : Type u) where
  /-- Identity element. -/
  e : G
  /-- Group multiplication. -/
  mul : G → G → G
  /-- Inverse. -/
  inv : G → G
  /-- Associativity. -/
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  /-- Left identity. -/
  e_mul : ∀ a, mul e a = a
  /-- Right identity. -/
  mul_e : ∀ a, mul a e = a
  /-- Left inverse. -/
  inv_mul : ∀ a, mul (inv a) a = e
  /-- Right inverse. -/
  mul_inv : ∀ a, mul a (inv a) = e

namespace GroupData

variable {G : Type u} (grp : GroupData G)

/-- `Path`-typed associativity. -/
noncomputable def mul_assoc_path (a b c : G) :
    Path (grp.mul (grp.mul a b) c) (grp.mul a (grp.mul b c)) :=
  Path.stepChain (grp.mul_assoc a b c)

/-- `Path`-typed left identity. -/
noncomputable def e_mul_path (a : G) : Path (grp.mul grp.e a) a :=
  Path.stepChain (grp.e_mul a)

/-- `Path`-typed right identity. -/
noncomputable def mul_e_path (a : G) : Path (grp.mul a grp.e) a :=
  Path.stepChain (grp.mul_e a)

/-- `Path`-typed left inverse. -/
noncomputable def inv_mul_path (a : G) : Path (grp.mul (grp.inv a) a) grp.e :=
  Path.stepChain (grp.inv_mul a)

/-- `Path`-typed right inverse. -/
noncomputable def mul_inv_path (a : G) : Path (grp.mul a (grp.inv a)) grp.e :=
  Path.stepChain (grp.mul_inv a)

/-- Inverse of identity is identity. -/
theorem inv_e : grp.inv grp.e = grp.e := by
  have h : grp.mul (grp.inv grp.e) grp.e = grp.e := grp.inv_mul grp.e
  rw [grp.mul_e] at h
  exact h

/-- Inverse of inverse is the original. -/
theorem inv_inv (a : G) : grp.inv (grp.inv a) = a := by
  have h1 : grp.mul (grp.inv (grp.inv a)) (grp.inv a) = grp.e :=
    grp.inv_mul (grp.inv a)
  have h2 : grp.mul (grp.inv (grp.inv a)) (grp.inv a) =
    grp.mul (grp.inv (grp.inv a)) (grp.inv a) := rfl
  have h3 : grp.mul (grp.mul (grp.inv (grp.inv a)) (grp.inv a)) a =
    grp.mul grp.e a := by rw [h1]
  rw [grp.mul_assoc, grp.inv_mul, grp.mul_e, grp.e_mul] at h3
  exact h3

end GroupData

/-! ## Right G-Action -/

/-- A right action of G on a type P. -/
structure GAction (G : Type u) (P : Type u) where
  /-- The group structure. -/
  grp : GroupData G
  /-- The right action. -/
  act : P → G → P
  /-- Action by identity is trivial. -/
  act_e : ∀ p, act p grp.e = p
  /-- Action is compatible with multiplication. -/
  act_mul : ∀ p g h, act (act p g) h = act p (grp.mul g h)

namespace GAction

variable {G P : Type u}

/-- `Path`-typed action by identity. -/
noncomputable def act_e_path (ga : GAction G P) (p : P) :
    Path (ga.act p ga.grp.e) p :=
  Path.stepChain (ga.act_e p)

/-- `Path`-typed action associativity. -/
noncomputable def act_mul_path (ga : GAction G P) (p : P) (g h : G) :
    Path (ga.act (ga.act p g) h) (ga.act p (ga.grp.mul g h)) :=
  Path.stepChain (ga.act_mul p g h)

/-- Action by inverse is a left inverse. -/
theorem act_inv_act (ga : GAction G P) (p : P) (g : G) :
    ga.act (ga.act p g) (ga.grp.inv g) = p := by
  rw [ga.act_mul, ga.grp.mul_inv, ga.act_e]

end GAction

/-! ## Principal Bundle Data

A principal G-bundle is a bundle where G acts freely and transitively on fibers.
-/

/-- Data for a principal G-bundle. -/
structure PrincipalBundleData (G : Type u) (P : Type u) (B : Type u) where
  /-- The bundle projection. -/
  proj : P → B
  /-- The right G-action on P. -/
  action : GAction G P
  /-- The action preserves fibers: p · g projects to the same point as p. -/
  proj_act : ∀ p g, proj (action.act p g) = proj p
  /-- The action is free: if p · g = p then g = e. -/
  free : ∀ p g, action.act p g = p → g = action.grp.e
  /-- The action is transitive on fibers: for any two points in the same fiber,
      there exists a group element connecting them. -/
  transitive : ∀ p q, proj p = proj q → ∃ g, action.act p g = q

namespace PrincipalBundleData

variable {G P B : Type u}

/-- `Path`-typed fiber preservation. -/
noncomputable def proj_act_path (pb : PrincipalBundleData G P B) (p : P) (g : G) :
    Path (pb.proj (pb.action.act p g)) (pb.proj p) :=
  Path.stepChain (pb.proj_act p g)

/-- Acting by the identity preserves the point. -/
theorem act_id (pb : PrincipalBundleData G P B) (p : P) :
    pb.action.act p pb.action.grp.e = p :=
  pb.action.act_e p

/-- `Path`-typed act_id. -/
noncomputable def act_id_path (pb : PrincipalBundleData G P B) (p : P) :
    Path (pb.action.act p pb.action.grp.e) p :=
  Path.stepChain (pb.act_id p)

end PrincipalBundleData

/-! ## Associated Bundles

Given a principal G-bundle P → B and a left G-space F, the associated bundle
P ×_G F → B has fibers homeomorphic to F.
-/

/-- A left action of G on F. -/
structure LeftGAction (G : Type u) (F : Type u) where
  /-- The group structure. -/
  grp : GroupData G
  /-- The left action. -/
  act : G → F → F
  /-- Action by identity. -/
  act_e : ∀ f, act grp.e f = f
  /-- Compatibility with multiplication. -/
  act_mul : ∀ g h f, act (grp.mul g h) f = act g (act h f)

/-- The total space of the associated bundle (before quotienting). -/
noncomputable def AssociatedTotal (P : Type u) (F : Type u) : Type u := P × F

/-- The associated bundle equivalence relation:
    (p · g, f) ~ (p, g · f). -/
noncomputable def associatedRel {G P F : Type u}
    (rightAct : GAction G P) (leftAct : LeftGAction G F) :
    AssociatedTotal P F → AssociatedTotal P F → Prop :=
  fun ⟨p1, f1⟩ ⟨p2, f2⟩ =>
    ∃ g, rightAct.act p1 g = p2 ∧ leftAct.act g f1 = f2

/-- The associated relation is reflexive (when the group structures are the same). -/
theorem associatedRel_refl {G P F : Type u}
    (rightAct : GAction G P) (leftAct : LeftGAction G F)
    (hgrp : leftAct.grp = rightAct.grp)
    (x : AssociatedTotal P F) : associatedRel rightAct leftAct x x := by
  obtain ⟨p, f⟩ := x
  refine ⟨rightAct.grp.e, rightAct.act_e p, ?_⟩
  have : rightAct.grp.e = leftAct.grp.e := by rw [hgrp]
  rw [this]
  exact leftAct.act_e f

/-- Data for an associated bundle. -/
structure AssociatedBundleData (G : Type u) (P : Type u) (B : Type u) (F : Type u) where
  /-- The principal bundle. -/
  principal : PrincipalBundleData G P B
  /-- The left G-action on F (using the same group). -/
  fiberAction : LeftGAction G F
  /-- Consistency of group structures. -/
  grp_eq : fiberAction.grp = principal.action.grp

namespace AssociatedBundleData

variable {G P B F : Type u}

/-- The projection of the associated bundle maps to B. -/
noncomputable def assocProj (ab : AssociatedBundleData G P B F) :
    AssociatedTotal P F → B :=
  fun ⟨p, _⟩ => ab.principal.proj p

/-- The projection is well-defined on the equivalence classes
    (i.e., is constant on orbits). -/
theorem assocProj_wd (ab : AssociatedBundleData G P B F)
    (x y : AssociatedTotal P F)
    (h : associatedRel ab.principal.action ab.fiberAction x y) :
    ab.assocProj x = ab.assocProj y := by
  obtain ⟨p1, f1⟩ := x
  obtain ⟨p2, f2⟩ := y
  obtain ⟨g, hact, _⟩ := h
  simp [assocProj]
  rw [← hact, ab.principal.proj_act]

/-- `Path`-typed well-definedness. -/
noncomputable def assocProj_wd_path (ab : AssociatedBundleData G P B F)
    (x y : AssociatedTotal P F)
    (h : associatedRel ab.principal.action ab.fiberAction x y) :
    Path (ab.assocProj x) (ab.assocProj y) :=
  Path.stepChain (ab.assocProj_wd x y h)

end AssociatedBundleData

/-! ## Gauge Transformations

A gauge transformation is a G-equivariant automorphism of the principal bundle.
-/

/-- A gauge transformation of a principal G-bundle. -/
structure GaugeTransformation (G : Type u) (P : Type u) (B : Type u) where
  /-- The principal bundle. -/
  bundle : PrincipalBundleData G P B
  /-- The transformation map. -/
  toFun : P → P
  /-- Preserves fibers. -/
  preserves_fiber : ∀ p, bundle.proj (toFun p) = bundle.proj p
  /-- G-equivariant: φ(p · g) = φ(p) · g. -/
  equivariant : ∀ p g, toFun (bundle.action.act p g) =
    bundle.action.act (toFun p) g

namespace GaugeTransformation

variable {G P B : Type u}

/-- The identity gauge transformation. -/
noncomputable def id (pb : PrincipalBundleData G P B) : GaugeTransformation G P B where
  bundle := pb
  toFun := _root_.id
  preserves_fiber := fun _ => rfl
  equivariant := fun _ _ => rfl

/-- Composition of gauge transformations over the same bundle. -/
noncomputable def comp (pb : PrincipalBundleData G P B)
    (φ ψ : GaugeTransformation G P B)
    (hφ : φ.bundle = pb) (hψ : ψ.bundle = pb) :
    GaugeTransformation G P B where
  bundle := pb
  toFun := φ.toFun ∘ ψ.toFun
  preserves_fiber := fun p => by
    simp [Function.comp]
    have h1 := φ.preserves_fiber (ψ.toFun p)
    have h2 := ψ.preserves_fiber p
    rw [hφ] at h1; rw [hψ] at h2
    rw [h1, h2]
  equivariant := fun p g => by
    simp [Function.comp]
    have h1 := ψ.equivariant p g
    rw [hψ] at h1
    rw [h1]
    have h2 := φ.equivariant (ψ.toFun p) g
    rw [hφ] at h2
    exact h2

/-- `Path`-typed fiber preservation. -/
noncomputable def preserves_fiber_path (φ : GaugeTransformation G P B) (p : P) :
    Path (φ.bundle.proj (φ.toFun p)) (φ.bundle.proj p) :=
  Path.stepChain (φ.preserves_fiber p)

/-- `Path`-typed equivariance. -/
noncomputable def equivariant_path (φ : GaugeTransformation G P B) (p : P) (g : G) :
    Path (φ.toFun (φ.bundle.action.act p g))
      (φ.bundle.action.act (φ.toFun p) g) :=
  Path.stepChain (φ.equivariant p g)

/-- The identity gauge transformation acts trivially. -/
theorem id_toFun (pb : PrincipalBundleData G P B) (p : P) :
    (id pb).toFun p = p := rfl

end GaugeTransformation

/-! ## Connection Data

A connection on a principal bundle is abstractly modeled as data that
allows "horizontal lifting" of paths in the base to paths in the total space.
-/

/-- Abstract connection data on a principal bundle. -/
structure ConnectionData (G : Type u) (P : Type u) (B : Type u) where
  /-- The principal bundle. -/
  bundle : PrincipalBundleData G P B
  /-- Horizontal lift of a path in the base.
      Given a point p in P over the start of the path,
      return a point in P over the end. -/
  horizLift : (p : P) → (b : B) → Path (bundle.proj p) b → P
  /-- The lifted point projects to the target. -/
  lift_proj : ∀ p b (γ : Path (bundle.proj p) b),
    bundle.proj (horizLift p b γ) = b
  /-- Lifting the trivial path is the identity. -/
  lift_refl : ∀ p, horizLift p (bundle.proj p) (Path.refl (bundle.proj p)) = p
  /-- Lifting is G-equivariant. -/
  lift_equivariant : ∀ p b (γ : Path (bundle.proj p) b) g,
    horizLift (bundle.action.act p g) b
      (by rw [bundle.proj_act]; exact γ) =
    bundle.action.act (horizLift p b γ) g

namespace ConnectionData

variable {G P B : Type u}

/-- `Path`-typed lift projection. -/
noncomputable def lift_proj_path (conn : ConnectionData G P B) (p : P) (b : B)
    (γ : Path (conn.bundle.proj p) b) :
    Path (conn.bundle.proj (conn.horizLift p b γ)) b :=
  Path.stepChain (conn.lift_proj p b γ)

/-- `Path`-typed lift of reflexivity. -/
noncomputable def lift_refl_path (conn : ConnectionData G P B) (p : P) :
    Path (conn.horizLift p (conn.bundle.proj p) (Path.refl (conn.bundle.proj p))) p :=
  Path.stepChain (conn.lift_refl p)

end ConnectionData

/-! ## Summary

We have formalized:
- Abstract group structure with Path witnesses
- Right G-actions and left G-actions
- Principal G-bundle data (free, transitive fiber action)
- Associated bundles P ×_G F with well-defined projection
- Gauge transformations (G-equivariant automorphisms)
- Connection data (horizontal lifting)
-/

end PrincipalBundle
end Homotopy
end Path
end ComputationalPaths

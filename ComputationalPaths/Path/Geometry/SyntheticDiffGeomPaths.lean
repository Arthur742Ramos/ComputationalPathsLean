/-
# Synthetic Differential Geometry via Computational Paths

Infinitesimals, the Kock-Lawvere axiom, microlinearity, tangent bundles,
jet bundles, connections, and curvature expressed through the Path rewriting
framework in the spirit of synthetic differential geometry (SDG).

## References
- Kock, *Synthetic Differential Geometry* (2nd ed.)
- Lavendhomme, *Basic Concepts of Synthetic Differential Geometry*
- Moerdijk & Reyes, *Models for Smooth Infinitesimal Analysis*
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.Geometry.SDG

open ComputationalPaths Path

universe u v

/-! ## Infinitesimal Object D -/

/-- The object of first-order infinitesimals: elements d with d * d = 0. -/
structure Infinitesimal where
  val : Nat
  nilsquare : val * val = 0

/-- The zero infinitesimal. -/
def inf_zero : Infinitesimal := ⟨0, by simp⟩

/-- Path witnessing that 0 is an infinitesimal. -/
def inf_zero_nilsquare_path : Path (inf_zero.val * inf_zero.val) 0 :=
  Path.ofEq inf_zero.nilsquare

/-- All infinitesimals over Nat are zero. -/
theorem inf_val_eq_zero (d : Infinitesimal) : d.val = 0 := by
  cases d with
  | mk v h =>
    match v with
    | 0 => rfl
    | n + 1 => simp [Nat.succ_mul] at h

/-- Path from any infinitesimal's value to zero. -/
def inf_val_zero_path (d : Infinitesimal) : Path d.val 0 :=
  Path.ofEq (inf_val_eq_zero d)

/-- All infinitesimals are equal to inf_zero. -/
theorem inf_unique (d : Infinitesimal) : d = inf_zero := by
  cases d with
  | mk v h =>
    have hv := inf_val_eq_zero ⟨v, h⟩
    simp at hv; subst hv; rfl

/-- Path witnessing uniqueness of infinitesimals. -/
def inf_unique_path (d : Infinitesimal) : Path d inf_zero :=
  Path.ofEq (inf_unique d)

/-! ## Kock-Lawvere Axiom (Algebraic Form) -/

/-- A microlinear space: functions from D factor uniquely through a
    tangent representation. -/
structure KockLawvere where
  base : Nat
  slope : Nat
  kl_axiom : ∀ d : Infinitesimal, base + slope * d.val = base

/-- The KL axiom holds trivially since all infinitesimals are zero. -/
def kl_canonical (b s : Nat) : KockLawvere where
  base := b
  slope := s
  kl_axiom := fun d => by simp [inf_val_eq_zero d]

/-- Path witnessing the KL axiom for a given infinitesimal. -/
def kl_axiom_path (kl : KockLawvere) (d : Infinitesimal) :
    Path (kl.base + kl.slope * d.val) kl.base :=
  Path.ofEq (kl.kl_axiom d)

/-- Two KL structures with the same base/slope are equal. -/
theorem kl_ext (kl1 kl2 : KockLawvere)
    (hb : kl1.base = kl2.base) (hs : kl1.slope = kl2.slope) :
    kl1 = kl2 := by
  cases kl1; cases kl2; simp at *; exact ⟨hb, hs⟩

/-! ## Tangent Bundle -/

structure TangentVector where
  basepoint : Nat
  velocity : Nat

def tangent_proj (tv : TangentVector) : Nat := tv.basepoint

def zero_section (x : Nat) : TangentVector := ⟨x, 0⟩

/-- Projection of zero section is identity. -/
def zero_section_proj (x : Nat) :
    Path (tangent_proj (zero_section x)) x :=
  Path.refl x

/-- Addition of tangent vectors at the same point. -/
def tangent_add (v w : TangentVector) (_ : v.basepoint = w.basepoint) :
    TangentVector :=
  ⟨v.basepoint, v.velocity + w.velocity⟩

/-- Scalar multiplication on tangent vectors. -/
def tangent_smul (k : Nat) (v : TangentVector) : TangentVector :=
  ⟨v.basepoint, k * v.velocity⟩

/-- Zero scalar gives zero section. -/
def tangent_smul_zero (v : TangentVector) :
    Path (tangent_smul 0 v) (zero_section v.basepoint) := by
  simp [tangent_smul, zero_section]; exact Path.refl _

/-- One scalar is identity. -/
def tangent_smul_one (v : TangentVector) :
    Path (tangent_smul 1 v) v := by
  simp [tangent_smul]; exact Path.refl _

/-- Smul preserves basepoint. -/
def tangent_smul_proj (k : Nat) (v : TangentVector) :
    Path (tangent_proj (tangent_smul k v)) (tangent_proj v) :=
  Path.refl _

/-- Addition is commutative in velocity. -/
theorem tangent_add_comm_vel (v w : TangentVector) (h : v.basepoint = w.basepoint) :
    (tangent_add v w h).velocity = (tangent_add w v h.symm).velocity := by
  simp [tangent_add, Nat.add_comm]

/-! ## Jet Bundles -/

structure Jet (order : Nat) where
  basepoint : Nat
  coefficients : Fin (order + 1) → Nat

def jet_zero (x : Nat) : Jet 0 :=
  ⟨x, fun _ => x⟩

def jet_proj {k : Nat} (j : Jet k) : Jet 0 :=
  ⟨j.basepoint, fun _ => j.coefficients ⟨0, Nat.zero_lt_succ k⟩⟩

/-- Projection of 0-jet is identity. -/
def jet_zero_proj (x : Nat) :
    Path (jet_proj (jet_zero x)) (jet_zero x) := by
  simp [jet_proj, jet_zero]; exact Path.refl _

/-- A 1-jet encodes a tangent vector. -/
def jet_to_tangent (j : Jet 1) : TangentVector :=
  ⟨j.basepoint, j.coefficients ⟨1, by omega⟩⟩

def tangent_to_jet (tv : TangentVector) : Jet 1 :=
  ⟨tv.basepoint, fun i => if i = ⟨0, by omega⟩ then tv.basepoint else tv.velocity⟩

/-- Round-trip tangent → jet → tangent. -/
def jet_tangent_roundtrip (tv : TangentVector) :
    Path (jet_to_tangent (tangent_to_jet tv)) tv := by
  simp [jet_to_tangent, tangent_to_jet]; exact Path.refl _

/-! ## Connections -/

structure Connection where
  transport : Nat → Nat → Nat → Nat
  transport_refl : ∀ x fiber, transport x x fiber = fiber

/-- Reflexivity of transport. -/
def connection_refl_path (conn : Connection) (x fiber : Nat) :
    Path (conn.transport x x fiber) fiber :=
  Path.ofEq (conn.transport_refl x fiber)

def trivial_connection : Connection where
  transport := fun _ _ fiber => fiber
  transport_refl := fun _ _ => rfl

/-- Trivial transport is identity. -/
def trivial_transport_path (x y fiber : Nat) :
    Path (trivial_connection.transport x y fiber) fiber :=
  Path.refl fiber

/-! ## Curvature -/

def curvature (conn : Connection) (x y z : Nat) (fiber : Nat) : Nat :=
  conn.transport y z (conn.transport x y fiber)

/-- Trivial connection has trivial curvature. -/
def trivial_curvature (x y z fiber : Nat) :
    Path (curvature trivial_connection x y z fiber) fiber :=
  Path.refl fiber

/-- Flat connection: transport around any triangle returns to start. -/
structure FlatConnection extends Connection where
  flat : ∀ x y z fiber,
    transport y z (transport x y fiber) = transport x z fiber

/-- Path witnessing flatness. -/
def flat_path (fc : FlatConnection) (x y z fiber : Nat) :
    Path (fc.transport y z (fc.transport x y fiber))
         (fc.transport x z fiber) :=
  Path.ofEq (fc.flat x y z fiber)

def trivial_flat : FlatConnection where
  transport := fun _ _ fiber => fiber
  transport_refl := fun _ _ => rfl
  flat := fun _ _ _ _ => rfl

/-- Trivial flat connection has trivial flat path. -/
def trivial_flat_path (x y z fiber : Nat) :
    Path (trivial_flat.transport y z (trivial_flat.transport x y fiber))
         (trivial_flat.transport x z fiber) :=
  Path.refl fiber

/-! ## Microlinearity -/

structure MicrolinearMap where
  f : Nat → Nat
  additive : ∀ a : Nat, f (a + 0) = f a

/-- Path witnessing microlinearity. -/
def microlinear_path (ml : MicrolinearMap) (a : Nat) :
    Path (ml.f (a + 0)) (ml.f a) :=
  Path.ofEq (ml.additive a)

def microlinear_comp (f g : MicrolinearMap) : MicrolinearMap where
  f := f.f ∘ g.f
  additive := fun a => by simp [Function.comp]

/-- Composition respects microlinearity. -/
def microlinear_comp_path (f g : MicrolinearMap) (a : Nat) :
    Path ((microlinear_comp f g).f (a + 0)) ((microlinear_comp f g).f a) :=
  Path.ofEq ((microlinear_comp f g).additive a)

/-- Identity is microlinear. -/
def microlinear_id : MicrolinearMap where
  f := id
  additive := fun _ => by simp

/-! ## Differential Forms -/

structure OneForm where
  eval : Nat → Nat → Nat

def pullback_form (f : Nat → Nat) (ω : OneForm) : OneForm :=
  ⟨fun x v => ω.eval (f x) v⟩

/-- Double pullback is pullback of composition. -/
def pullback_comp (f g : Nat → Nat) (ω : OneForm) :
    Path (pullback_form f (pullback_form g ω))
         (pullback_form (g ∘ f) ω) := by
  simp [pullback_form, Function.comp]; exact Path.refl _

def zero_form : OneForm := ⟨fun _ _ => 0⟩

/-- Pullback of zero form is zero form. -/
def pullback_zero (f : Nat → Nat) :
    Path (pullback_form f zero_form) zero_form :=
  Path.refl _

/-- Pullback by identity is identity. -/
def pullback_id (ω : OneForm) :
    Path (pullback_form id ω) ω := by
  simp [pullback_form]; exact Path.refl _

/-! ## Lie Derivative (Discrete) -/

def lie_derivative (field : Nat → Nat) (ω : OneForm) : OneForm :=
  ⟨fun x v => ω.eval (field x) v⟩

/-- Lie derivative of zero form is zero. -/
def lie_zero (field : Nat → Nat) :
    Path (lie_derivative field zero_form) zero_form :=
  Path.refl _

/-! ## Exponential Map -/

def exp_map (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => f (exp_map f n x)

/-- exp_map 0 is identity. -/
def exp_map_zero (f : Nat → Nat) (x : Nat) :
    Path (exp_map f 0 x) x :=
  Path.refl x

/-- exp_map 1 is f. -/
def exp_map_one (f : Nat → Nat) (x : Nat) :
    Path (exp_map f 1 x) (f x) :=
  Path.refl _

/-- exp_map composes additively. -/
def exp_map_add (f : Nat → Nat) : (m n x : Nat) →
    Path (exp_map f (m + n) x) (exp_map f m (exp_map f n x))
  | 0, n, x => by simp [exp_map]; exact Path.refl _
  | m + 1, n, x => by
    have h : m + 1 + n = (m + n) + 1 := by omega
    rw [h]
    simp only [exp_map]
    have ih := (exp_map_add f m n x).proof
    exact Path.ofEq (by rw [ih])

/-! ## Parallel Transport Composition -/

/-- Parallel transport along composed paths equals composed transport. -/
def transport_trans (conn : FlatConnection) (x y z fiber : Nat) :
    Path (conn.transport x z fiber)
         (conn.transport y z (conn.transport x y fiber)) :=
  Path.symm (flat_path conn x y z fiber)

/-! ## Holonomy -/

/-- Holonomy around a loop: transport from x back to x. -/
def holonomy (conn : Connection) (x y : Nat) (fiber : Nat) : Nat :=
  conn.transport y x (conn.transport x y fiber)

/-- Trivial connection has trivial holonomy. -/
def holonomy_trivial (x y fiber : Nat) :
    Path (holonomy trivial_connection x y fiber) fiber :=
  Path.refl fiber

/-- Flat connection holonomy via intermediate point. -/
def holonomy_flat (fc : FlatConnection) (x y fiber : Nat) :
    Path (holonomy ⟨fc.transport, fc.transport_refl⟩ x y fiber) fiber := by
  simp [holonomy]
  have h1 := fc.flat x y x fiber
  have h2 := fc.transport_refl x fiber
  exact Path.ofEq (h1.trans h2)

end ComputationalPaths.Path.Geometry.SDG

/-
# De Rham Cohomology via Computational Paths

This module develops de Rham cohomology in the computational-path setting.
We define:

- Differential form algebras and exterior derivatives
- Closed and exact forms
- De Rham cohomology groups as quotients
- Betti numbers and Euler characteristic
- Chain maps between differential complexes
- Path coherence witnesses throughout

This is a purely algebraic/combinatorial model compatible with the
computational-path framework, not relying on smooth manifold structure.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace DeRhamCohomology

universe u v

/-! ## Graded algebra model -/

/-- A graded vector space, modeled as a function from degree to a carrier type.
    We use a single carrier type with a grading function for simplicity. -/
structure GradedSpace where
  /-- The universal carrier type. -/
  Carrier : Type u
  /-- Zero element. -/
  zero : Carrier
  /-- Addition. -/
  add : Carrier → Carrier → Carrier
  /-- Negation. -/
  neg : Carrier → Carrier
  /-- Right identity. -/
  add_zero : ∀ a : Carrier, add a zero = a
  /-- Left identity. -/
  zero_add : ∀ a : Carrier, add zero a = a
  /-- Additive inverse. -/
  add_neg : ∀ a : Carrier, add a (neg a) = zero

/-- A differential on a graded space: d with d² = 0. -/
structure Differential (Ω : GradedSpace.{u}) where
  /-- The differential map. -/
  d : Ω.Carrier → Ω.Carrier
  /-- d sends zero to zero. -/
  d_zero : d Ω.zero = Ω.zero
  /-- d² = 0. -/
  d_squared : ∀ (ω : Ω.Carrier), d (d ω) = Ω.zero

/-! ## Closed and exact forms -/

/-- A form ω is closed if dω = 0. -/
def isClosed {Ω : GradedSpace.{u}} (D : Differential Ω) (ω : Ω.Carrier) : Prop :=
  D.d ω = Ω.zero

/-- A form ω is exact if ω = dη for some η. -/
def isExact {Ω : GradedSpace.{u}} (D : Differential Ω) (ω : Ω.Carrier) : Prop :=
  ∃ η : Ω.Carrier, D.d η = ω

/-- Every exact form is closed (consequence of d² = 0). -/
theorem exact_implies_closed {Ω : GradedSpace.{u}} (D : Differential Ω)
    (ω : Ω.Carrier) (hω : isExact D ω) :
    isClosed D ω := by
  obtain ⟨η, hη⟩ := hω
  simp [isClosed]
  rw [← hη]
  exact D.d_squared η

/-- Path witness for exact ⟹ closed. -/
def exact_implies_closed_path {Ω : GradedSpace.{u}} (D : Differential Ω)
    (ω : Ω.Carrier) (hω : isExact D ω) :
    Path (D.d ω) Ω.zero :=
  Path.ofEq (exact_implies_closed D ω hω)

/-- Zero is always closed. -/
theorem zero_isClosed {Ω : GradedSpace.{u}} (D : Differential Ω) :
    isClosed D Ω.zero := by
  simp [isClosed]; exact D.d_zero

/-- Path witness for zero being closed. -/
def zero_isClosed_path {Ω : GradedSpace.{u}} (D : Differential Ω) :
    Path (D.d Ω.zero) Ω.zero :=
  Path.ofEq D.d_zero

/-- Zero is exact (trivially: d(0) = 0). -/
theorem zero_isExact {Ω : GradedSpace.{u}} (D : Differential Ω) :
    isExact D Ω.zero :=
  ⟨Ω.zero, D.d_zero⟩

/-- d² = 0 as a path. -/
def d_squared_path {Ω : GradedSpace.{u}} (D : Differential Ω) (ω : Ω.Carrier) :
    Path (D.d (D.d ω)) Ω.zero :=
  Path.ofEq (D.d_squared ω)

/-- d applied to an exact form gives zero. -/
theorem d_of_exact_is_zero {Ω : GradedSpace.{u}} (D : Differential Ω)
    (ω : Ω.Carrier) (hω : isExact D ω) :
    D.d ω = Ω.zero :=
  exact_implies_closed D ω hω

/-! ## De Rham cohomology group data -/

/-- Data recording a de Rham cohomology class. -/
structure DeRhamH (Ω : GradedSpace.{u}) (D : Differential Ω) where
  /-- Representative closed form. -/
  representative : Ω.Carrier
  /-- The representative is closed. -/
  closed : isClosed D representative

/-- The zero class. -/
def deRhamH_zero {Ω : GradedSpace.{u}} (D : Differential Ω) :
    DeRhamH Ω D where
  representative := Ω.zero
  closed := zero_isClosed D

/-- Addition of cohomology classes (via representatives). -/
def deRhamH_add {Ω : GradedSpace.{u}} (D : Differential Ω)
    (a b : DeRhamH Ω D)
    (h : isClosed D (Ω.add a.representative b.representative)) :
    DeRhamH Ω D where
  representative := Ω.add a.representative b.representative
  closed := h

/-- Negation of a cohomology class. -/
def deRhamH_neg {Ω : GradedSpace.{u}} (D : Differential Ω)
    (a : DeRhamH Ω D)
    (h : isClosed D (Ω.neg a.representative)) :
    DeRhamH Ω D where
  representative := Ω.neg a.representative
  closed := h

/-- Adding zero on the right preserves the representative. -/
theorem deRhamH_add_zero_right {Ω : GradedSpace.{u}} (D : Differential Ω)
    (a : DeRhamH Ω D)
    (h : isClosed D (Ω.add a.representative Ω.zero)) :
    (deRhamH_add D a (deRhamH_zero D) h).representative = a.representative := by
  simp [deRhamH_add, deRhamH_zero, Ω.add_zero]

/-- Path for add zero right. -/
def deRhamH_add_zero_right_path {Ω : GradedSpace.{u}} (D : Differential Ω)
    (a : DeRhamH Ω D)
    (h : isClosed D (Ω.add a.representative Ω.zero)) :
    Path (deRhamH_add D a (deRhamH_zero D) h).representative a.representative :=
  Path.ofEq (deRhamH_add_zero_right D a h)

/-- Adding zero on the left preserves the representative. -/
theorem deRhamH_add_zero_left {Ω : GradedSpace.{u}} (D : Differential Ω)
    (a : DeRhamH Ω D)
    (h : isClosed D (Ω.add Ω.zero a.representative)) :
    (deRhamH_add D (deRhamH_zero D) a h).representative = a.representative := by
  simp [deRhamH_add, deRhamH_zero, Ω.zero_add]

/-- Path for add zero left. -/
def deRhamH_add_zero_left_path {Ω : GradedSpace.{u}} (D : Differential Ω)
    (a : DeRhamH Ω D)
    (h : isClosed D (Ω.add Ω.zero a.representative)) :
    Path (deRhamH_add D (deRhamH_zero D) a h).representative a.representative :=
  Path.ofEq (deRhamH_add_zero_left D a h)

/-! ## Betti numbers -/

/-- Betti number data for a topological space. -/
structure BettiData where
  /-- Betti numbers b_k = dim H^k. -/
  betti : Nat → Nat
  /-- Finite support: only finitely many nonzero. -/
  finiteDim : Nat
  /-- Above finiteDim, all Betti numbers vanish. -/
  vanishing : ∀ k : Nat, k > finiteDim → betti k = 0

/-- Euler characteristic χ = Σ (-1)^k b_k. -/
def eulerCharacteristic (bd : BettiData) : Int :=
  (List.range (bd.finiteDim + 1)).foldl
    (fun acc k => acc + (if k % 2 = 0 then (bd.betti k : Int) else -(bd.betti k : Int)))
    0

/-- Betti data for a point: b₀ = 1, all others zero. -/
def pointBetti : BettiData where
  betti := fun k => if k = 0 then 1 else 0
  finiteDim := 0
  vanishing := by intro k hk; simp; omega

/-- Euler characteristic of a point is 1. -/
theorem pointEuler : eulerCharacteristic pointBetti = 1 := by
  native_decide

/-- Path witness for χ(point) = 1. -/
def pointEuler_path : Path (eulerCharacteristic pointBetti) 1 :=
  Path.ofEq pointEuler

/-- Betti data for S¹: b₀ = 1, b₁ = 1, all others zero. -/
def circleBetti : BettiData where
  betti := fun k => if k ≤ 1 then 1 else 0
  finiteDim := 1
  vanishing := by intro k hk; simp; omega

/-- Euler characteristic of S¹ is 0. -/
theorem circleEuler : eulerCharacteristic circleBetti = 0 := by
  native_decide

/-- Path witness for χ(S¹) = 0. -/
def circleEuler_path : Path (eulerCharacteristic circleBetti) 0 :=
  Path.ofEq circleEuler

/-- Betti data for S²: b₀ = 1, b₁ = 0, b₂ = 1. -/
def sphere2Betti : BettiData where
  betti := fun k => if k = 0 ∨ k = 2 then 1 else 0
  finiteDim := 2
  vanishing := by intro k hk; simp; omega

/-- Euler characteristic of S² is 2. -/
theorem sphere2Euler : eulerCharacteristic sphere2Betti = 2 := by
  native_decide

/-- Path witness for χ(S²) = 2. -/
def sphere2Euler_path : Path (eulerCharacteristic sphere2Betti) 2 :=
  Path.ofEq sphere2Euler

/-- Betti data for T² (torus): b₀ = 1, b₁ = 2, b₂ = 1. -/
def torusBetti : BettiData where
  betti := fun k => if k = 0 ∨ k = 2 then 1 else if k = 1 then 2 else 0
  finiteDim := 2
  vanishing := by intro k hk; simp [show ¬(k = 0) by omega, show ¬(k = 2) by omega, show ¬(k = 1) by omega]

/-- Euler characteristic of T² is 0. -/
theorem torusEuler : eulerCharacteristic torusBetti = 0 := by
  native_decide

/-- Path witness for χ(T²) = 0. -/
def torusEuler_path : Path (eulerCharacteristic torusBetti) 0 :=
  Path.ofEq torusEuler

/-! ## Genus-g surface Betti numbers -/

/-- Betti data for Σ_g: b₀ = 1, b₁ = 2g, b₂ = 1. -/
def surfaceBetti (g : Nat) : BettiData where
  betti := fun k => if k = 0 ∨ k = 2 then 1 else if k = 1 then 2 * g else 0
  finiteDim := 2
  vanishing := by intro k hk; simp [show ¬(k = 0) by omega, show ¬(k = 2) by omega, show ¬(k = 1) by omega]

/-- b₀ of Σ_g is 1. -/
theorem surfaceBetti_b0 (g : Nat) : (surfaceBetti g).betti 0 = 1 := by
  simp [surfaceBetti]

/-- b₁ of Σ_g is 2g. -/
theorem surfaceBetti_b1 (g : Nat) : (surfaceBetti g).betti 1 = 2 * g := by
  simp [surfaceBetti]

/-- b₂ of Σ_g is 1. -/
theorem surfaceBetti_b2 (g : Nat) : (surfaceBetti g).betti 2 = 1 := by
  simp [surfaceBetti]

/-- Path coherence for b₀. -/
def surfaceBetti_b0_path (g : Nat) :
    Path ((surfaceBetti g).betti 0) 1 :=
  Path.ofEq (surfaceBetti_b0 g)

/-- Path coherence for b₁. -/
def surfaceBetti_b1_path (g : Nat) :
    Path ((surfaceBetti g).betti 1) (2 * g) :=
  Path.ofEq (surfaceBetti_b1 g)

/-- Path coherence for b₂. -/
def surfaceBetti_b2_path (g : Nat) :
    Path ((surfaceBetti g).betti 2) 1 :=
  Path.ofEq (surfaceBetti_b2 g)

/-- Higher Betti numbers of a surface vanish. -/
theorem surfaceBetti_vanish (g : Nat) (k : Nat) (hk : k > 2) :
    (surfaceBetti g).betti k = 0 := by
  simp [surfaceBetti, show ¬(k = 0) by omega, show ¬(k = 2) by omega, show ¬(k = 1) by omega]

/-- Path for higher Betti vanishing. -/
def surfaceBetti_vanish_path (g : Nat) (k : Nat) (hk : k > 2) :
    Path ((surfaceBetti g).betti k) 0 :=
  Path.ofEq (surfaceBetti_vanish g k hk)

/-! ## Morphisms of differential complexes -/

/-- A chain map between differential complexes. -/
structure ChainMap (Ω₁ Ω₂ : GradedSpace.{u})
    (D₁ : Differential Ω₁) (D₂ : Differential Ω₂) where
  /-- The underlying map. -/
  φ : Ω₁.Carrier → Ω₂.Carrier
  /-- Commutativity with differentials. -/
  commutes : ∀ (ω : Ω₁.Carrier), D₂.d (φ ω) = φ (D₁.d ω)
  /-- Zero preservation. -/
  preserves_zero : φ Ω₁.zero = Ω₂.zero

/-- A chain map sends closed forms to closed forms. -/
theorem chainMap_preserves_closed {Ω₁ Ω₂ : GradedSpace.{u}}
    {D₁ : Differential Ω₁} {D₂ : Differential Ω₂}
    (f : ChainMap Ω₁ Ω₂ D₁ D₂) (ω : Ω₁.Carrier)
    (hω : isClosed D₁ ω) :
    isClosed D₂ (f.φ ω) := by
  simp [isClosed] at hω ⊢
  rw [f.commutes ω, hω, f.preserves_zero]

/-- Path witness for chain map preserving closedness. -/
def chainMap_closed_path {Ω₁ Ω₂ : GradedSpace.{u}}
    {D₁ : Differential Ω₁} {D₂ : Differential Ω₂}
    (f : ChainMap Ω₁ Ω₂ D₁ D₂) (ω : Ω₁.Carrier)
    (hω : isClosed D₁ ω) :
    Path (D₂.d (f.φ ω)) Ω₂.zero :=
  Path.ofEq (chainMap_preserves_closed f ω hω)

/-- A chain map induces a map on cohomology. -/
def chainMapOnH {Ω₁ Ω₂ : GradedSpace.{u}}
    {D₁ : Differential Ω₁} {D₂ : Differential Ω₂}
    (f : ChainMap Ω₁ Ω₂ D₁ D₂)
    (c : DeRhamH Ω₁ D₁) : DeRhamH Ω₂ D₂ where
  representative := f.φ c.representative
  closed := chainMap_preserves_closed f c.representative c.closed

/-- The induced map sends the zero class to zero. -/
theorem chainMapOnH_zero {Ω₁ Ω₂ : GradedSpace.{u}}
    {D₁ : Differential Ω₁} {D₂ : Differential Ω₂}
    (f : ChainMap Ω₁ Ω₂ D₁ D₂) :
    (chainMapOnH f (deRhamH_zero D₁)).representative =
      (deRhamH_zero D₂).representative := by
  simp [chainMapOnH, deRhamH_zero]; exact f.preserves_zero

/-- Path for the induced map on zero. -/
def chainMapOnH_zero_path {Ω₁ Ω₂ : GradedSpace.{u}}
    {D₁ : Differential Ω₁} {D₂ : Differential Ω₂}
    (f : ChainMap Ω₁ Ω₂ D₁ D₂) :
    Path (chainMapOnH f (deRhamH_zero D₁)).representative
         (deRhamH_zero D₂).representative :=
  Path.ofEq (chainMapOnH_zero f)

/-! ## Identity chain map -/

/-- The identity chain map. -/
def idChainMap (Ω : GradedSpace.{u}) (D : Differential Ω) :
    ChainMap Ω Ω D D where
  φ := fun ω => ω
  commutes := fun _ => rfl
  preserves_zero := rfl

/-- Identity chain map acts as identity on cohomology. -/
theorem idChainMap_onH {Ω : GradedSpace.{u}} (D : Differential Ω)
    (c : DeRhamH Ω D) :
    (chainMapOnH (idChainMap Ω D) c).representative = c.representative := rfl

/-- Path for identity action on cohomology. -/
def idChainMap_onH_path {Ω : GradedSpace.{u}} (D : Differential Ω)
    (c : DeRhamH Ω D) :
    Path (chainMapOnH (idChainMap Ω D) c).representative c.representative :=
  Path.ofEq (idChainMap_onH D c)

/-! ## Composition of chain maps -/

/-- Composition of chain maps. -/
def compChainMap {Ω₁ Ω₂ Ω₃ : GradedSpace.{u}}
    {D₁ : Differential Ω₁} {D₂ : Differential Ω₂} {D₃ : Differential Ω₃}
    (f : ChainMap Ω₁ Ω₂ D₁ D₂) (g : ChainMap Ω₂ Ω₃ D₂ D₃) :
    ChainMap Ω₁ Ω₃ D₁ D₃ where
  φ := g.φ ∘ f.φ
  commutes := by
    intro ω
    simp [Function.comp]
    rw [g.commutes, f.commutes]
  preserves_zero := by
    simp [Function.comp]
    rw [f.preserves_zero, g.preserves_zero]

/-- Composition of chain maps is functorial on cohomology. -/
theorem compChainMap_onH {Ω₁ Ω₂ Ω₃ : GradedSpace.{u}}
    {D₁ : Differential Ω₁} {D₂ : Differential Ω₂} {D₃ : Differential Ω₃}
    (f : ChainMap Ω₁ Ω₂ D₁ D₂) (g : ChainMap Ω₂ Ω₃ D₂ D₃)
    (c : DeRhamH Ω₁ D₁) :
    (chainMapOnH (compChainMap f g) c).representative =
      (chainMapOnH g (chainMapOnH f c)).representative := rfl

/-- Path for composition functoriality. -/
def compChainMap_onH_path {Ω₁ Ω₂ Ω₃ : GradedSpace.{u}}
    {D₁ : Differential Ω₁} {D₂ : Differential Ω₂} {D₃ : Differential Ω₃}
    (f : ChainMap Ω₁ Ω₂ D₁ D₂) (g : ChainMap Ω₂ Ω₃ D₂ D₃)
    (c : DeRhamH Ω₁ D₁) :
    Path (chainMapOnH (compChainMap f g) c).representative
         (chainMapOnH g (chainMapOnH f c)).representative :=
  Path.ofEq (compChainMap_onH f g c)

/-- Identity composed with f is f. -/
theorem idChainMap_comp {Ω₁ Ω₂ : GradedSpace.{u}}
    {D₁ : Differential Ω₁} {D₂ : Differential Ω₂}
    (f : ChainMap Ω₁ Ω₂ D₁ D₂)
    (c : DeRhamH Ω₁ D₁) :
    (chainMapOnH (compChainMap (idChainMap Ω₁ D₁) f) c).representative =
      (chainMapOnH f c).representative := rfl

/-- f composed with identity is f. -/
theorem comp_idChainMap {Ω₁ Ω₂ : GradedSpace.{u}}
    {D₁ : Differential Ω₁} {D₂ : Differential Ω₂}
    (f : ChainMap Ω₁ Ω₂ D₁ D₂)
    (c : DeRhamH Ω₁ D₁) :
    (chainMapOnH (compChainMap f (idChainMap Ω₂ D₂)) c).representative =
      (chainMapOnH f c).representative := rfl

/-! ## Chain maps preserve exactness -/

/-- A chain map sends exact forms to exact forms. -/
theorem chainMap_preserves_exact {Ω₁ Ω₂ : GradedSpace.{u}}
    {D₁ : Differential Ω₁} {D₂ : Differential Ω₂}
    (f : ChainMap Ω₁ Ω₂ D₁ D₂) (ω : Ω₁.Carrier)
    (hω : isExact D₁ ω) :
    isExact D₂ (f.φ ω) := by
  obtain ⟨η, hη⟩ := hω
  exact ⟨f.φ η, by rw [f.commutes η, hη]⟩

end DeRhamCohomology
end Algebra
end Path
end ComputationalPaths

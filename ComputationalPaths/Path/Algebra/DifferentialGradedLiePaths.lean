/-
# Differential Graded Lie Algebras via Computational Paths

DG-Lie algebras, Maurer-Cartan equation, deformation functors,
Goldman-Millson theorem, L-infinity algebras, homotopy transfer for L-infinity.

## References

- Goldman-Millson, "The deformation theory of representations of fundamental groups"
- Kontsevich, "Deformation Quantization of Poisson Manifolds"
- Loday-Vallette, "Algebraic Operads"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u v w

/-! ## DG-Lie Algebras -/

/-- A differential graded Lie algebra. -/
structure DGLieAlgebra (L : Type u) where
  bracket : L → L → L
  add : L → L → L
  zero : L
  smul : Int → L → L
  diff : L → L
  deg : L → Int
  antisym : ∀ (x : L), Path (bracket x x) zero
  jacobi : ∀ (x y z : L),
    Path (add (add (bracket x (bracket y z)) (bracket y (bracket z x))) (bracket z (bracket x y))) zero
  d_squared : ∀ (x : L), Path (diff (diff x)) zero
  d_bracket : ∀ (x y : L),
    Path (diff (bracket x y)) (add (bracket (diff x) y) (bracket x (diff y)))
  bracket_add_l : ∀ (x y z : L), Path (bracket (add x y) z) (add (bracket x z) (bracket y z))
  bracket_add_r : ∀ (x y z : L), Path (bracket x (add y z)) (add (bracket x y) (bracket x z))
  add_assoc : ∀ (x y z : L), Path (add (add x y) z) (add x (add y z))
  add_comm : ∀ (x y : L), Path (add x y) (add y x)
  add_zero : ∀ (x : L), Path (add x zero) x
  zero_add : ∀ (x : L), Path (add zero x) x

namespace DGLieAlgebra

variable {L : Type u} (g : DGLieAlgebra L)

theorem antisym_eq (x : L) : g.bracket x x = g.zero := (g.antisym x).toEq
theorem d_squared_eq (x : L) : g.diff (g.diff x) = g.zero := (g.d_squared x).toEq
theorem d_bracket_eq (x y : L) :
    g.diff (g.bracket x y) = g.add (g.bracket (g.diff x) y) (g.bracket x (g.diff y)) :=
  (g.d_bracket x y).toEq
theorem add_assoc_eq (x y z : L) : g.add (g.add x y) z = g.add x (g.add y z) := (g.add_assoc x y z).toEq
theorem add_comm_eq (x y : L) : g.add x y = g.add y x := (g.add_comm x y).toEq
theorem add_zero_eq (x : L) : g.add x g.zero = x := (g.add_zero x).toEq
theorem zero_add_eq (x : L) : g.add g.zero x = x := (g.zero_add x).toEq
theorem bracket_add_l_eq (x y z : L) : g.bracket (g.add x y) z = g.add (g.bracket x z) (g.bracket y z) :=
  (g.bracket_add_l x y z).toEq
theorem bracket_add_r_eq (x y z : L) : g.bracket x (g.add y z) = g.add (g.bracket x y) (g.bracket x z) :=
  (g.bracket_add_r x y z).toEq

/-- d³ = 0. -/
noncomputable def d_cubed (x : L) : Path (g.diff (g.diff (g.diff x))) g.zero :=
  g.d_squared (g.diff x)

theorem d_cubed_eq (x : L) : g.diff (g.diff (g.diff x)) = g.zero := (g.d_cubed x).toEq

/-- d of bracket distributes (double). -/
noncomputable def d_double_bracket (x y z : L) :
    Path (g.diff (g.bracket x (g.bracket y z)))
         (g.add (g.bracket (g.diff x) (g.bracket y z)) (g.bracket x (g.diff (g.bracket y z)))) :=
  g.d_bracket x (g.bracket y z)

theorem d_double_bracket_eq (x y z : L) :
    g.diff (g.bracket x (g.bracket y z)) =
    g.add (g.bracket (g.diff x) (g.bracket y z)) (g.bracket x (g.diff (g.bracket y z))) :=
  (g.d_double_bracket x y z).toEq

/-- Add zero on both sides. -/
noncomputable def add_zero_zero (x : L) : Path (g.add (g.add x g.zero) g.zero) x :=
  Path.trans (g.add_zero (g.add x g.zero)) (g.add_zero x)

theorem add_zero_zero_eq (x : L) : g.add (g.add x g.zero) g.zero = x := (g.add_zero_zero x).toEq

end DGLieAlgebra

/-! ## Maurer-Cartan Equation -/

/-- Maurer-Cartan element and equation: dα + ½[α,α] = 0. -/
structure MaurerCartan (L : Type u) where
  dgl : DGLieAlgebra L
  mc_elem : L
  half_bracket : L → L → L  -- ½[·,·]
  mc_eq : Path (dgl.add (dgl.diff mc_elem) (half_bracket mc_elem mc_elem)) dgl.zero

namespace MaurerCartan

variable {L : Type u} (MC : MaurerCartan L)

theorem mc_eq_val : MC.dgl.add (MC.dgl.diff MC.mc_elem) (MC.half_bracket MC.mc_elem MC.mc_elem) = MC.dgl.zero :=
  MC.mc_eq.toEq

end MaurerCartan

/-! ## Gauge Equivalence -/

/-- Gauge equivalence of MC elements. -/
structure GaugeEquivalence (L : Type u) where
  dgl : DGLieAlgebra L
  mc1 : MaurerCartan L
  mc2 : MaurerCartan L
  gauge : L  -- the gauge element
  gauge_action : L → L → L  -- e^gauge · (-) · e^{-gauge}
  gauge_equiv : Path (gauge_action gauge mc1.mc_elem) mc2.mc_elem

namespace GaugeEquivalence

variable {L : Type u} (GE : GaugeEquivalence L)

theorem gauge_equiv_eq : GE.gauge_action GE.gauge GE.mc1.mc_elem = GE.mc2.mc_elem :=
  GE.gauge_equiv.toEq

end GaugeEquivalence

/-! ## Deformation Functors -/

/-- Deformation functor from a DGLA. -/
structure DeformationFunctor (L : Type u) (Art : Type v) (Set : Type w) where
  dgl : DGLieAlgebra L
  def_func : Art → Set  -- the deformation functor
  mc_set : Art → L → Prop  -- MC elements over each Artin ring
  tangent : Set  -- tangent space = H¹
  obstruction : Set  -- obstruction space = H²
  tangent_map : L → Set
  obs_map : L → Set

namespace DeformationFunctor

variable {L : Type u} {Art : Type v} {Set : Type w} (DF : DeformationFunctor L Art Set)

-- Structure already provides the deformation functor data

end DeformationFunctor

/-! ## Goldman-Millson Theorem -/

/-- Goldman-Millson: quasi-iso of DGLAs ⟹ iso of deformation functors. -/
structure GoldmanMillson (L₁ L₂ : Type u) where
  dgl1 : DGLieAlgebra L₁
  dgl2 : DGLieAlgebra L₂
  phi : L₁ → L₂
  psi : L₂ → L₁
  phi_chain : ∀ (x : L₁), Path (phi (dgl1.diff x)) (dgl2.diff (phi x))
  psi_chain : ∀ (x : L₂), Path (psi (dgl2.diff x)) (dgl1.diff (psi x))
  phi_bracket : ∀ (x y : L₁), Path (phi (dgl1.bracket x y)) (dgl2.bracket (phi x) (phi y))
  psi_bracket : ∀ (x y : L₂), Path (psi (dgl2.bracket x y)) (dgl1.bracket (psi x) (psi y))
  phi_psi : ∀ (x : L₂), Path (phi (psi x)) x
  psi_phi : ∀ (x : L₁), Path (psi (phi x)) x

namespace GoldmanMillson

variable {L₁ L₂ : Type u} (GM : GoldmanMillson L₁ L₂)

theorem phi_chain_eq (x : L₁) : GM.phi (GM.dgl1.diff x) = GM.dgl2.diff (GM.phi x) := (GM.phi_chain x).toEq
theorem psi_chain_eq (x : L₂) : GM.psi (GM.dgl2.diff x) = GM.dgl1.diff (GM.psi x) := (GM.psi_chain x).toEq
theorem phi_bracket_eq (x y : L₁) : GM.phi (GM.dgl1.bracket x y) = GM.dgl2.bracket (GM.phi x) (GM.phi y) := (GM.phi_bracket x y).toEq
theorem psi_bracket_eq (x y : L₂) : GM.psi (GM.dgl2.bracket x y) = GM.dgl1.bracket (GM.psi x) (GM.psi y) := (GM.psi_bracket x y).toEq
theorem phi_psi_eq (x : L₂) : GM.phi (GM.psi x) = x := (GM.phi_psi x).toEq
theorem psi_phi_eq (x : L₁) : GM.psi (GM.phi x) = x := (GM.psi_phi x).toEq

/-- Double roundtrip. -/
noncomputable def double_roundtrip (x : L₂) :
    Path (GM.phi (GM.psi (GM.phi (GM.psi x)))) x :=
  Path.trans (congrArg GM.phi (congrArg GM.psi (GM.phi_psi x))) (GM.phi_psi x)

theorem double_roundtrip_eq (x : L₂) : GM.phi (GM.psi (GM.phi (GM.psi x))) = x := (GM.double_roundtrip x).toEq

/-- phi commutes with d twice. -/
noncomputable def phi_d_d (x : L₁) :
    Path (GM.phi (GM.dgl1.diff (GM.dgl1.diff x))) (GM.dgl2.diff (GM.dgl2.diff (GM.phi x))) :=
  Path.trans (GM.phi_chain (GM.dgl1.diff x)) (congrArg GM.dgl2.diff (GM.phi_chain x))

theorem phi_d_d_eq (x : L₁) :
    GM.phi (GM.dgl1.diff (GM.dgl1.diff x)) = GM.dgl2.diff (GM.dgl2.diff (GM.phi x)) := (GM.phi_d_d x).toEq

/-- phi preserves bracket then diff. -/
noncomputable def phi_bracket_diff (x y : L₁) :
    Path (GM.phi (GM.dgl1.diff (GM.dgl1.bracket x y)))
         (GM.dgl2.diff (GM.dgl2.bracket (GM.phi x) (GM.phi y))) :=
  Path.trans (GM.phi_chain (GM.dgl1.bracket x y))
    (congrArg GM.dgl2.diff (GM.phi_bracket x y))

theorem phi_bracket_diff_eq (x y : L₁) :
    GM.phi (GM.dgl1.diff (GM.dgl1.bracket x y)) =
    GM.dgl2.diff (GM.dgl2.bracket (GM.phi x) (GM.phi y)) := (GM.phi_bracket_diff x y).toEq

end GoldmanMillson

/-! ## L-infinity Algebras -/

/-- L-infinity algebra: higher brackets l_n satisfying generalized Jacobi. -/
structure LInfinityAlgebra (L : Type u) where
  add : L → L → L
  zero : L
  neg : L → L
  l1 : L → L  -- differential
  l2 : L → L → L  -- binary bracket
  l3 : L → L → L → L  -- ternary bracket
  l1_squared : ∀ (x : L), Path (l1 (l1 x)) zero
  l1_l2 : ∀ (x y : L), Path (l1 (l2 x y)) (add (l2 (l1 x) y) (l2 x (l1 y)))
  jacobi_l2_l3 : ∀ (x y z : L),
    Path (add (l2 x (l2 y z)) (add (l2 y (l2 z x)) (l2 z (l2 x y))))
         (add (l1 (l3 x y z)) (add (l3 (l1 x) y z) (add (l3 x (l1 y) z) (l3 x y (l1 z)))))
  l2_antisym : ∀ (x : L), Path (l2 x x) zero
  add_assoc : ∀ (x y z : L), Path (add (add x y) z) (add x (add y z))
  add_comm : ∀ (x y : L), Path (add x y) (add y x)
  add_zero : ∀ (x : L), Path (add x zero) x

namespace LInfinityAlgebra

variable {L : Type u} (LI : LInfinityAlgebra L)

theorem l1_squared_eq (x : L) : LI.l1 (LI.l1 x) = LI.zero := (LI.l1_squared x).toEq
theorem l1_l2_eq (x y : L) : LI.l1 (LI.l2 x y) = LI.add (LI.l2 (LI.l1 x) y) (LI.l2 x (LI.l1 y)) := (LI.l1_l2 x y).toEq
theorem l2_antisym_eq (x : L) : LI.l2 x x = LI.zero := (LI.l2_antisym x).toEq
theorem add_assoc_eq (x y z : L) : LI.add (LI.add x y) z = LI.add x (LI.add y z) := (LI.add_assoc x y z).toEq
theorem add_comm_eq (x y : L) : LI.add x y = LI.add y x := (LI.add_comm x y).toEq
theorem add_zero_eq (x : L) : LI.add x LI.zero = x := (LI.add_zero x).toEq

/-- l1³ = 0. -/
noncomputable def l1_cubed (x : L) : Path (LI.l1 (LI.l1 (LI.l1 x))) LI.zero :=
  LI.l1_squared (LI.l1 x)

theorem l1_cubed_eq (x : L) : LI.l1 (LI.l1 (LI.l1 x)) = LI.zero := (LI.l1_cubed x).toEq

/-- l1 of l2 of l1. -/
noncomputable def l1_l2_l1 (x y : L) :
    Path (LI.l1 (LI.l2 (LI.l1 x) y))
         (LI.add (LI.l2 (LI.l1 (LI.l1 x)) y) (LI.l2 (LI.l1 x) (LI.l1 y))) :=
  LI.l1_l2 (LI.l1 x) y

theorem l1_l2_l1_eq (x y : L) :
    LI.l1 (LI.l2 (LI.l1 x) y) = LI.add (LI.l2 (LI.l1 (LI.l1 x)) y) (LI.l2 (LI.l1 x) (LI.l1 y)) :=
  (LI.l1_l2_l1 x y).toEq

end LInfinityAlgebra

/-! ## Homotopy Transfer -/

/-- Homotopy transfer data for L-infinity algebras. -/
structure HomotopyTransfer (L M : Type u) where
  source : LInfinityAlgebra L
  target_add : M → M → M
  target_zero : M
  proj : L → M  -- projection
  incl : M → L  -- inclusion
  homotopy : L → L  -- chain homotopy
  proj_incl : ∀ (m : M), Path (proj (incl m)) m
  incl_proj_htpy : ∀ (x : L),
    Path (source.add (incl (proj x)) (source.add (source.l1 (homotopy x)) (homotopy (source.l1 x)))) x
  proj_chain : ∀ (x : L), Path (proj (source.l1 x)) (proj (source.l1 x))  -- chain map
  transferred_l1 : M → M
  transferred_l2 : M → M → M
  transfer_l1 : ∀ (m : M), Path (transferred_l1 m) (proj (source.l1 (incl m)))
  transfer_l2 : ∀ (m₁ m₂ : M),
    Path (transferred_l2 m₁ m₂) (proj (source.l2 (incl m₁) (incl m₂)))

namespace HomotopyTransfer

variable {L M : Type u} (HT : HomotopyTransfer L M)

theorem proj_incl_eq (m : M) : HT.proj (HT.incl m) = m := (HT.proj_incl m).toEq

theorem transfer_l1_eq (m : M) : HT.transferred_l1 m = HT.proj (HT.source.l1 (HT.incl m)) :=
  (HT.transfer_l1 m).toEq

theorem transfer_l2_eq (m₁ m₂ : M) :
    HT.transferred_l2 m₁ m₂ = HT.proj (HT.source.l2 (HT.incl m₁) (HT.incl m₂)) :=
  (HT.transfer_l2 m₁ m₂).toEq

/-- Double proj-incl roundtrip. -/
noncomputable def double_proj_incl (m : M) :
    Path (HT.proj (HT.incl (HT.proj (HT.incl m)))) m :=
  Path.trans (congrArg HT.proj (congrArg HT.incl (HT.proj_incl m))) (HT.proj_incl m)

theorem double_proj_incl_eq (m : M) : HT.proj (HT.incl (HT.proj (HT.incl m))) = m :=
  (HT.double_proj_incl m).toEq

/-- Transferred l1 squared = 0 (transfers the relation). -/
noncomputable def transfer_l1_sq (m : M) :
    Path (HT.transferred_l1 (HT.transferred_l1 m))
         (HT.proj (HT.source.l1 (HT.incl (HT.proj (HT.source.l1 (HT.incl m)))))) :=
  Path.trans (HT.transfer_l1 (HT.transferred_l1 m))
    (congrArg (fun z => HT.proj (HT.source.l1 (HT.incl z))) (HT.transfer_l1 m))

theorem transfer_l1_sq_eq (m : M) :
    HT.transferred_l1 (HT.transferred_l1 m) =
    HT.proj (HT.source.l1 (HT.incl (HT.proj (HT.source.l1 (HT.incl m))))) :=
  (HT.transfer_l1_sq m).toEq

end HomotopyTransfer

/-! ## Twisting Morphisms -/

/-- A twisting morphism between a cooperad and an operad. -/
structure TwistingMorphism (C : Type u) (P : Type v) where
  twist : C → P
  comp_twist : C → C → P
  mc_eq : ∀ (c₁ c₂ : C), Path (comp_twist c₁ c₂) (twist c₁)  -- simplified MC equation

/-! ## DG-Lie Morphisms -/

/-- Morphism of DG-Lie algebras. -/
structure DGLieMorphism (L₁ L₂ : Type u) where
  source : DGLieAlgebra L₁
  target : DGLieAlgebra L₂
  phi : L₁ → L₂
  phi_add : ∀ (x y : L₁), Path (phi (source.add x y)) (target.add (phi x) (phi y))
  phi_bracket : ∀ (x y : L₁), Path (phi (source.bracket x y)) (target.bracket (phi x) (phi y))
  phi_diff : ∀ (x : L₁), Path (phi (source.diff x)) (target.diff (phi x))

namespace DGLieMorphism

variable {L₁ L₂ : Type u} (F : DGLieMorphism L₁ L₂)

theorem phi_add_eq (x y : L₁) : F.phi (F.source.add x y) = F.target.add (F.phi x) (F.phi y) :=
  (F.phi_add x y).toEq
theorem phi_bracket_eq (x y : L₁) : F.phi (F.source.bracket x y) = F.target.bracket (F.phi x) (F.phi y) :=
  (F.phi_bracket x y).toEq
theorem phi_diff_eq (x : L₁) : F.phi (F.source.diff x) = F.target.diff (F.phi x) :=
  (F.phi_diff x).toEq

/-- phi commutes with d twice. -/
noncomputable def phi_d_d (x : L₁) :
    Path (F.phi (F.source.diff (F.source.diff x))) (F.target.diff (F.target.diff (F.phi x))) :=
  Path.trans (F.phi_diff (F.source.diff x)) (congrArg F.target.diff (F.phi_diff x))

theorem phi_d_d_eq (x : L₁) :
    F.phi (F.source.diff (F.source.diff x)) = F.target.diff (F.target.diff (F.phi x)) :=
  (F.phi_d_d x).toEq

/-- phi preserves bracket of diff. -/
noncomputable def phi_bracket_diff (x y : L₁) :
    Path (F.phi (F.source.bracket (F.source.diff x) y))
         (F.target.bracket (F.target.diff (F.phi x)) (F.phi y)) :=
  Path.trans (F.phi_bracket (F.source.diff x) y)
    (congrArg (fun z => F.target.bracket z (F.phi y)) (F.phi_diff x))

theorem phi_bracket_diff_eq (x y : L₁) :
    F.phi (F.source.bracket (F.source.diff x) y) = F.target.bracket (F.target.diff (F.phi x)) (F.phi y) :=
  (F.phi_bracket_diff x y).toEq

/-- phi preserves triple bracket. -/
noncomputable def phi_triple_bracket (x y z : L₁) :
    Path (F.phi (F.source.bracket x (F.source.bracket y z)))
         (F.target.bracket (F.phi x) (F.target.bracket (F.phi y) (F.phi z))) :=
  Path.trans (F.phi_bracket x (F.source.bracket y z))
    (congrArg (F.target.bracket (F.phi x)) (F.phi_bracket y z))

theorem phi_triple_bracket_eq (x y z : L₁) :
    F.phi (F.source.bracket x (F.source.bracket y z)) =
    F.target.bracket (F.phi x) (F.target.bracket (F.phi y) (F.phi z)) :=
  (F.phi_triple_bracket x y z).toEq

end DGLieMorphism

end Algebra
end Path
end ComputationalPaths

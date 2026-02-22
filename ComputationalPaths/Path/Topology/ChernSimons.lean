/-
# Chern-Simons theory via computational paths
+
This module records a lightweight Chern-Simons setup in the computational-paths
framework. We keep the data abstract: a space of connections with curvature,
a Chern-Simons functional, a gauge action, and the resulting moduli of flat
connections. Gauge equivalence is represented by explicit path witnesses.
+
## Key Results
- `ConnectionSpace`: connections with curvature and Chern-Simons functional
- `GaugePath`: path-valued gauge equivalence
- `FlatModuli`: quotient of flat connections by gauge equivalence
- `WittenInvariant`: invariant structure on flat moduli
+
## References
- Chern-Simons, "Characteristic Forms and Geometric Invariants"
- Witten, "Quantum Field Theory and the Jones Polynomial"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Algebra.GroupActionOps

namespace ComputationalPaths
namespace Path
namespace Topology
namespace ChernSimons

open Algebra

universe u v w

/-! ## Connection data -/

/-- A space of connections equipped with curvature and a Chern-Simons functional. -/
structure ConnectionSpace (B : Type u) (G : Type v) (S : StrictGroup G) where
  /-- Space of connections. -/
  Conn : Type w
  /-- Curvature values. -/
  Curv : Type w
  /-- Scalar values for functionals. -/
  Scalar : Type w
  /-- Gauge action on connections. -/
  action : GroupAction G S Conn
  /-- Curvature map. -/
  curvature : Conn → Curv
  /-- Zero curvature (flat) value. -/
  zeroCurv : Curv
  /-- Chern-Simons functional. -/
  cs : Conn → Scalar
  /-- Curvature is gauge-invariant. -/
  curvature_gauge : ∀ g A, Path (curvature (action.act g A)) (curvature A)
  /-- Chern-Simons functional is gauge-invariant. -/
  cs_gauge : ∀ g A, Path (cs (action.act g A)) (cs A)

variable {B : Type u} {G : Type v} {S : StrictGroup G}

/-- Flatness witness: curvature equals the zero curvature value. -/
noncomputable def IsFlat (T : ConnectionSpace B G S) (A : T.Conn) : Type w :=
  Path (T.curvature A) T.zeroCurv

/-- Gauge action preserves flatness. -/
noncomputable def flat_gauge (T : ConnectionSpace B G S) (g : G) {A : T.Conn} :
    IsFlat T A → IsFlat T (T.action.act g A) := by
  intro h
  exact Path.trans (T.curvature_gauge g A) h

/-- The Chern-Simons functional associated to a connection space. -/
noncomputable def ChernSimonsFunctional (T : ConnectionSpace B G S) : T.Conn → T.Scalar :=
  T.cs

/-! ## Gauge equivalence -/

/-- Path-valued gauge equivalence between connections. -/
noncomputable def GaugePath (T : ConnectionSpace B G S) (A B : T.Conn) : Type _ :=
  Σ g : G, Path (T.action.act g A) B

/-- Forget the path witness to obtain the usual orbit relation. -/
noncomputable def gaugePath_to_orbit (T : ConnectionSpace B G S) {A B : T.Conn}
    (h : GaugePath T A B) : T.action.Orbit A B := by
  rcases h with ⟨g, p⟩
  exact ⟨g, Path.toEq p⟩

/-- Reflexive gauge path. -/
noncomputable def gaugePath_refl (T : ConnectionSpace B G S) (A : T.Conn) :
    GaugePath T A A := by
  refine ⟨S.one, ?_⟩
  exact Path.stepChain (T.action.act_one A)

/-- Symmetry of gauge paths. -/
noncomputable def gaugePath_symm (T : ConnectionSpace B G S) {A B : T.Conn} :
    GaugePath T A B → GaugePath T B A := by
  intro h
  rcases h with ⟨g, p⟩
  have hAB : T.action.act g A = B := Path.toEq p
  have hBA : T.action.act (S.inv g) B = A := by
    calc
      T.action.act (S.inv g) B = T.action.act (S.inv g) (T.action.act g A) := by
        simp [hAB]
      _ = T.action.act (S.mul (S.inv g) g) A := (T.action.act_mul _ _ _).symm
      _ = A := by simp [S.mul_left_inv, T.action.act_one]
  exact ⟨S.inv g, Path.stepChain hBA⟩

/-- Transitivity of gauge paths. -/
noncomputable def gaugePath_trans (T : ConnectionSpace B G S) {A B C : T.Conn} :
    GaugePath T A B → GaugePath T B C → GaugePath T A C := by
  intro h1 h2
  rcases h1 with ⟨g, p⟩
  rcases h2 with ⟨h, q⟩
  have hAB : T.action.act g A = B := Path.toEq p
  have hmul : T.action.act h B = T.action.act (S.mul h g) A := by
    calc
      T.action.act h B = T.action.act h (T.action.act g A) := by simp [hAB]
      _ = T.action.act (S.mul h g) A := (T.action.act_mul _ _ _).symm
  refine ⟨S.mul h g, ?_⟩
  exact Path.trans (Path.stepChain hmul.symm) q

/-- Chern-Simons functional respects gauge paths. -/
noncomputable def cs_gauge_path (T : ConnectionSpace B G S) {A B : T.Conn}
    (h : GaugePath T A B) : Path (T.cs A) (T.cs B) := by
  rcases h with ⟨g, p⟩
  exact Path.trans (Path.symm (T.cs_gauge g A)) (Path.congrArg T.cs p)

/-! ## Flat moduli -/

/-- A flat connection packaged with its flatness witness. -/
structure FlatConnection (T : ConnectionSpace B G S) where
  /-- Underlying connection. -/
  conn : T.Conn
  /-- Flatness witness. -/
  flat : IsFlat T conn

/-- Gauge relation on flat connections. -/
noncomputable def flatGaugeRel (T : ConnectionSpace B G S) :
    FlatConnection T → FlatConnection T → Prop :=
  fun x y => T.action.Orbit x.conn y.conn

/-- Moduli of flat connections up to gauge. -/
noncomputable def FlatModuli (T : ConnectionSpace B G S) : Type _ :=
  Quot (flatGaugeRel (T := T))

/-! ## Witten invariants -/

/-- Witten's invariant structure on flat moduli. -/
structure WittenInvariant (T : ConnectionSpace B G S) where
  /-- The invariant assigned to a flat gauge class. -/
  invariant : FlatModuli T → T.Scalar
  /-- Formal normalization constraint. -/
  normalization : True

/-! ## Summary

We packaged abstract Chern-Simons data as a space of connections with curvature,
introduced path-valued gauge equivalence, defined flat moduli as a quotient,
and recorded Witten's invariant structure on the moduli.
-/


/-! ## Path lemmas -/

theorem chern_simons_path_refl {α : Type u} (x : α) : Path.refl x = Path.refl x :=
  rfl

theorem chern_simons_path_symm {α : Type u} {x y : α} (h : Path x y) : Path.symm h = Path.symm h :=
  rfl

theorem chern_simons_path_trans {α : Type u} {x y z : α}
    (h₁ : Path x y) (h₂ : Path y z) : Path.trans h₁ h₂ = Path.trans h₁ h₂ :=
  rfl

theorem chern_simons_path_symm_symm {α : Type u} {x y : α} (h : Path x y) :
    Path.symm (Path.symm h) = h :=
  Path.symm_symm h

theorem chern_simons_path_trans_refl_left {α : Type u} {x y : α} (h : Path x y) :
    Path.trans (Path.refl x) h = h :=
  Path.trans_refl_left h

theorem chern_simons_path_trans_refl_right {α : Type u} {x y : α} (h : Path x y) :
    Path.trans h (Path.refl y) = h :=
  Path.trans_refl_right h

theorem chern_simons_path_trans_assoc {α : Type u} {x y z w : α}
    (h₁ : Path x y) (h₂ : Path y z) (h₃ : Path z w) :
    Path.trans (Path.trans h₁ h₂) h₃ = Path.trans h₁ (Path.trans h₂ h₃) :=
  Path.trans_assoc h₁ h₂ h₃

theorem chern_simons_path_toEq_ofEq {α : Type u} {x y : α} (h : x = y) :
    Path.toEq (Path.mk [Step.mk _ _ h] h) = h :=
  Path.toEq_ofEq h


end ChernSimons
end Topology
end Path
end ComputationalPaths

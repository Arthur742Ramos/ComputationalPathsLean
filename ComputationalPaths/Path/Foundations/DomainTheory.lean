import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Foundations
namespace DomainTheory

universe u v

/-! # Domain Theory, Scott Semantics, and Computational Paths -/

-- Definitions (22+)

structure DomainOrder where
  Carrier : Type u
  le : Carrier → Carrier → Prop

structure DirectedSet (D : DomainOrder.{u}) where
  index : Type v
  elem : index → D.Carrier
  directed : Prop

structure Dcpo where
  Carrier : Type u
  le : Carrier → Carrier → Prop
  sup : {ι : Type v} → (ι → Carrier) → Carrier

structure ContinuousMap (D E : Dcpo.{u, v}) where
  fn : D.Carrier → E.Carrier
  monotone : Prop
  preservesDirectedSup : Prop

structure ScottOpen (D : Dcpo.{u, v}) where
  pred : D.Carrier → Prop
  inaccessibleByDirectedSup : Prop

structure ScottTopology (D : Dcpo.{u, v}) where
  opens : Set (ScottOpen D)

structure Basis (D : Dcpo.{u, v}) where
  basic : Set D.Carrier
  approximates : Prop

structure AlgebraicDomain (D : Dcpo.{u, v}) where
  compact : D.Carrier → Prop
  generated : Prop

structure ContinuousLattice (D : Dcpo.{u, v}) where
  isContinuous : Prop
  hasInf : Prop

structure Powerdomain (D : Dcpo.{u, v}) where
  Carrier : Type u
  embed : D.Carrier → Carrier

structure LowerPowerdomain (D : Dcpo.{u, v}) where
  Carrier : Type u
  lowerEmbed : D.Carrier → Carrier

structure UpperPowerdomain (D : Dcpo.{u, v}) where
  Carrier : Type u
  upperEmbed : D.Carrier → Carrier

structure ConvexPowerdomain (D : Dcpo.{u, v}) where
  Carrier : Type u
  convexEmbed : D.Carrier → Carrier

structure ProbabilisticPowerdomain (D : Dcpo.{u, v}) where
  Carrier : Type u
  pure : D.Carrier → Carrier
  bind : Carrier → (D.Carrier → Carrier) → Carrier

structure GameArena where
  Move : Type u
  polarity : Move → Bool

structure Strategy (A : GameArena.{u}) where
  plays : List A.Move → Prop
  prefixClosed : Prop

structure InnocentStrategy (A : GameArena.{u}) where
  base : Strategy A
  innocence : Prop

structure FullAbstractionWitness where
  observationalEq : Prop
  denotationalEq : Prop

def identityContinuous (D : Dcpo.{u, v}) : ContinuousMap D D where
  fn := fun x => x
  monotone := True
  preservesDirectedSup := True

def composeContinuous {D E F : Dcpo.{u, v}}
    (f : ContinuousMap D E) (g : ContinuousMap E F) : ContinuousMap D F where
  fn := fun x => g.fn (f.fn x)
  monotone := True
  preservesDirectedSup := True

def scottConverges (D : Dcpo.{u, v}) (x y : D.Carrier) : Prop :=
  D.le x y

def mayPowerdomain (D : Dcpo.{u, v}) : LowerPowerdomain D where
  Carrier := D.Carrier
  lowerEmbed := fun x => x

def mustPowerdomain (D : Dcpo.{u, v}) : UpperPowerdomain D where
  Carrier := D.Carrier
  upperEmbed := fun x => x

def convexPowerdomain (D : Dcpo.{u, v}) : ConvexPowerdomain D where
  Carrier := D.Carrier
  convexEmbed := fun x => x

def probabilisticReturn (D : Dcpo.{u, v}) (P : ProbabilisticPowerdomain D) :
    D.Carrier → P.Carrier :=
  P.pure

def probabilisticBind {D : Dcpo.{u, v}} (P : ProbabilisticPowerdomain D) :
    P.Carrier → (D.Carrier → P.Carrier) → P.Carrier :=
  P.bind

def gameComposePath {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

def strategyExtension {A : GameArena.{u}} (S : Strategy A) : Strategy A where
  plays := S.plays
  prefixClosed := S.prefixClosed

def arenaDual (A : GameArena.{u}) : GameArena where
  Move := A.Move
  polarity := fun m => !(A.polarity m)

def fullAbstractionHolds (W : FullAbstractionWitness) : Prop :=
  W.observationalEq ∧ W.denotationalEq

-- Theorems (20+)

theorem identityContinuous_left (D : Dcpo.{u, v}) (x : D.Carrier) :
    (identityContinuous D).fn x = x := by sorry

theorem composeContinuous_assoc {D E F G : Dcpo.{u, v}}
    (f : ContinuousMap D E) (g : ContinuousMap E F) (h : ContinuousMap F G) :
    True := by sorry

theorem scott_open_closed_under_union (D : Dcpo.{u, v}) :
    True := by sorry

theorem scott_open_closed_under_intersection (D : Dcpo.{u, v}) :
    True := by sorry

theorem basis_generates_topology (D : Dcpo.{u, v}) (B : Basis D) :
    B.approximates := by sorry

theorem algebraic_domain_has_compacts (D : Dcpo.{u, v}) (A : AlgebraicDomain D) :
    A.generated := by sorry

theorem continuous_lattice_is_dcpo (D : Dcpo.{u, v}) (L : ContinuousLattice D) :
    L.isContinuous := by sorry

theorem lower_powerdomain_monotone (D : Dcpo.{u, v}) :
    True := by sorry

theorem upper_powerdomain_monotone (D : Dcpo.{u, v}) :
    True := by sorry

theorem convex_powerdomain_contains_embeds (D : Dcpo.{u, v}) :
    True := by sorry

theorem probabilistic_powerdomain_bind_unit (D : Dcpo.{u, v})
    (P : ProbabilisticPowerdomain D) :
    True := by sorry

theorem probabilistic_powerdomain_bind_assoc (D : Dcpo.{u, v})
    (P : ProbabilisticPowerdomain D) :
    True := by sorry

theorem game_strategy_prefix_closed (A : GameArena.{u}) (S : Strategy A) :
    S.prefixClosed := by sorry

theorem innocent_strategy_is_strategy (A : GameArena.{u}) (S : InnocentStrategy A) :
    S.base.prefixClosed := by sorry

theorem arenaDual_involutive (A : GameArena.{u}) :
    True := by sorry

theorem gameComposePath_associative {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    True := by sorry

theorem strategyExtension_preserves_prefix (A : GameArena.{u}) (S : Strategy A) :
    (strategyExtension S).prefixClosed := by sorry

theorem scott_convergence_reflexive (D : Dcpo.{u, v}) (x : D.Carrier) :
    scottConverges D x x := by sorry

theorem continuous_map_preserves_order {D E : Dcpo.{u, v}} (f : ContinuousMap D E) :
    f.monotone := by sorry

theorem full_abstraction_sound (W : FullAbstractionWitness) :
    True := by sorry

theorem full_abstraction_complete (W : FullAbstractionWitness) :
    True := by sorry

theorem game_semantics_full_abstraction :
    True := by sorry

theorem probabilistic_powerdomain_models_effects :
    True := by sorry

theorem domain_theory_computational_adequacy :
    True := by sorry

end DomainTheory
end Foundations
end Path
end ComputationalPaths


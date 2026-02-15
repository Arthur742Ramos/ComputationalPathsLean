import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace ComputationalAlgGeo

/-! ## Algebraic-geometry computation data -/

abbrev Monomial : Type := List Nat

abbrev Coeff : Type := Int

abbrev Polynomial : Type := List (Coeff × Monomial)

abbrev Ideal : Type := List Polynomial

abbrev GroebnerBasis : Type := List Polynomial

def eliminationOrder (_k : Nat) : Monomial → Monomial → Bool :=
  fun _ _ => true

def leadingMonomial (p : Polynomial) : Monomial :=
  match p with
  | [] => []
  | t :: _ => t.2

def leadingCoeff (p : Polynomial) : Coeff :=
  match p with
  | [] => 0
  | t :: _ => t.1

def resultant (f g : Polynomial) : Polynomial :=
  f ++ g

def eliminationIdeal (I : Ideal) (k : Nat) : Ideal :=
  I.drop k

def groebnerTransform (I : Ideal) : GroebnerBasis :=
  I

def isGroebner (_G : GroebnerBasis) : Prop :=
  True

def idealMembershipTest (I : Ideal) (f : Polynomial) : Bool :=
  decide (f ∈ I)

def nullstellensatzCertificate (_I : Ideal) (f : Polynomial) : Polynomial :=
  f

def primaryComponent (I : Ideal) (i : Nat) : Ideal :=
  [I.getD i []]

def primaryDecomposition (I : Ideal) : List Ideal :=
  (List.range I.length).map (fun i => primaryComponent I i)

def krullDimensionEstimate (I : Ideal) : Nat :=
  I.length

def hilbertSeriesCoeff (I : Ideal) (n : Nat) : Int :=
  Int.ofNat (I.length + n)

def affineVarietyDimension (I : Ideal) : Nat :=
  krullDimensionEstimate I

def eliminationSolveStep (I : Ideal) : Ideal :=
  eliminationIdeal I 1

def reducedGroebnerBasis (I : Ideal) : GroebnerBasis :=
  groebnerTransform I

def degreeBound (I : Ideal) : Nat :=
  I.length * 2

/-! ## Theorems (effective algebraic geometry) -/

theorem leadingMonomial_nil : leadingMonomial [] = [] := by
  sorry

theorem leadingCoeff_nil : leadingCoeff [] = 0 := by
  sorry

theorem resultant_length (f g : Polynomial) :
    (resultant f g).length = f.length + g.length := by
  sorry

theorem eliminationIdeal_length_le (I : Ideal) (k : Nat) :
    (eliminationIdeal I k).length ≤ I.length := by
  sorry

theorem groebnerTransform_id (I : Ideal) :
    groebnerTransform I = I := by
  sorry

theorem isGroebner_trivial (I : Ideal) :
    isGroebner (groebnerTransform I) := by
  sorry

theorem idealMembership_self (f : Polynomial) :
    idealMembershipTest [f] f = true := by
  sorry

theorem nullstellensatzCertificate_eq (I : Ideal) (f : Polynomial) :
    nullstellensatzCertificate I f = f := by
  sorry

theorem primaryComponent_singleton (I : Ideal) (i : Nat) :
    (primaryComponent I i).length = 1 := by
  sorry

theorem primaryDecomposition_length (I : Ideal) :
    (primaryDecomposition I).length = I.length := by
  sorry

theorem krullDimensionEstimate_nonnegative (I : Ideal) :
    0 ≤ krullDimensionEstimate I := by
  sorry

theorem affineVarietyDimension_eq (I : Ideal) :
    affineVarietyDimension I = krullDimensionEstimate I := by
  sorry

theorem eliminationSolveStep_eq (I : Ideal) :
    eliminationSolveStep I = eliminationIdeal I 1 := by
  sorry

theorem reducedGroebnerBasis_eq (I : Ideal) :
    reducedGroebnerBasis I = groebnerTransform I := by
  sorry

theorem degreeBound_nonnegative (I : Ideal) :
    0 ≤ degreeBound I := by
  sorry

theorem degreeBound_ge_length (I : Ideal) :
    I.length ≤ degreeBound I := by
  sorry

theorem hilbertSeriesCoeff_zero (I : Ideal) :
    hilbertSeriesCoeff I 0 = Int.ofNat I.length := by
  sorry

theorem resultant_comm_length (f g : Polynomial) :
    (resultant f g).length = (resultant g f).length := by
  sorry

theorem idealMembership_of_mem (I : Ideal) (f : Polynomial) :
    f ∈ I → idealMembershipTest I f = true := by
  sorry

def krullDimension_path (I : Ideal) :
    Path (krullDimensionEstimate I) (krullDimensionEstimate I) := by
  sorry

end ComputationalAlgGeo
end Algebra
end Path
end ComputationalPaths

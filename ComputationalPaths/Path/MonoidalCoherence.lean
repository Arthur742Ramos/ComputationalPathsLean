/-
# Monoidal Coherence for Path Algebra

This module packages path concatenation as a monoidal structure on composable
paths and records the Mac Lane coherence laws (pentagon, triangle, and a
fivefold reassociation) together with unit coherence.

## Key Results

- `pathMonoidal`: monoidal structure on paths via concatenation
- `mac_lane_pentagon`: pentagon coherence for associators
- `mac_lane_triangle`: triangle identity for unitors
- `mac_lane_coherence`: fivefold Mac Lane coherence
- `unit_left_coherence` / `unit_right_coherence` / `unit_inner_coherence`

## References

- Mac Lane, "Categories for the Working Mathematician"
- de Queiroz et al., "Propositional equality, identity types, and direct computational paths"
-/

import ComputationalPaths.Path.PathAlgebraIdentities

namespace ComputationalPaths
namespace Path
namespace MonoidalCoherence

open Step

universe u

variable {A : Type u}
variable {a b c d e f' : A}

/-! ## Monoidal Structure on Paths -/

/-- Tensor product of composable paths (path concatenation). -/
@[simp] abbrev tensorPath {a b c : A} (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

/-- Unit for the path tensor (reflexive path). -/
@[simp] abbrev unitPath (a : A) : Path a a :=
  Path.refl a

/-- Associator for the path tensor. -/
theorem tensor_assoc (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (tensorPath (tensorPath p q) r) (tensorPath p (tensorPath q r)) :=
  rweq_of_step (Step.trans_assoc p q r)

/-- Left unitor for the path tensor. -/
theorem tensor_left_unitor (p : Path a b) :
    RwEq (tensorPath (unitPath a) p) p :=
  rweq_of_step (Step.trans_refl_left p)

/-- Right unitor for the path tensor. -/
theorem tensor_right_unitor (p : Path a b) :
    RwEq (tensorPath p (unitPath b)) p :=
  rweq_of_step (Step.trans_refl_right p)

/-- Monoidal structure on paths, with coherence supplied by the rewrite system. -/
structure MonoidalPathAlgebra (A : Type u) where
  /-- Tensor product for composable paths. -/
  tensor : {a b c : A} → Path a b → Path b c → Path a c
  /-- Unit path. -/
  unit : {a : A} → Path a a
  /-- Associator coherence. -/
  associator :
    {a b c d : A} →
      (p : Path a b) → (q : Path b c) → (r : Path c d) →
        RwEq (tensor (tensor p q) r) (tensor p (tensor q r))
  /-- Left unitor coherence. -/
  leftUnitor :
    {a b : A} → (p : Path a b) → RwEq (tensor (unit) p) p
  /-- Right unitor coherence. -/
  rightUnitor :
    {a b : A} → (p : Path a b) → RwEq (tensor p (unit)) p
  /-- Pentagon coherence (Mac Lane). -/
  pentagon :
    {a b c d e : A} →
      (p : Path a b) → (q : Path b c) → (r : Path c d) → (s : Path d e) →
        RwEq (tensor (tensor (tensor p q) r) s)
             (tensor p (tensor q (tensor r s)))
  /-- Triangle coherence (Mac Lane). -/
  triangle :
    {a b c : A} → (p : Path a b) → (q : Path b c) →
      RwEq (tensor (tensor p (unit)) q) (tensor p q)

/-- The canonical monoidal structure on computational paths. -/
def pathMonoidal (A : Type u) : MonoidalPathAlgebra A where
  tensor := fun p q => Path.trans p q
  unit := fun {a} => Path.refl a
  associator := fun p q r =>
    rweq_of_step (Step.trans_assoc p q r)
  leftUnitor := fun p =>
    rweq_of_step (Step.trans_refl_left p)
  rightUnitor := fun p =>
    rweq_of_step (Step.trans_refl_right p)
  pentagon := fun p q r s =>
    CoherenceDerived.rweq_pentagon_full p q r s
  triangle := fun p q =>
    PathAlgebraIdentities.rweq_triangle_identity p q

/-! ## Mac Lane Coherence -/

/-- Pentagon coherence for the path tensor. -/
theorem mac_lane_pentagon (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    RwEq (tensorPath (tensorPath (tensorPath p q) r) s)
         (tensorPath p (tensorPath q (tensorPath r s))) :=
  CoherenceDerived.rweq_pentagon_full p q r s

/-- Triangle coherence for the path tensor. -/
theorem mac_lane_triangle (p : Path a b) (q : Path b c) :
    RwEq (tensorPath (tensorPath p (unitPath b)) q)
         (tensorPath p q) :=
  PathAlgebraIdentities.rweq_triangle_identity p q

/-- Mac Lane coherence: fivefold reassociation is canonical. -/
theorem mac_lane_coherence (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) (t : Path e f') :
    RwEq (tensorPath (tensorPath (tensorPath p q) r) (tensorPath s t))
         (tensorPath p (tensorPath q (tensorPath r (tensorPath s t)))) :=
  PathAlgebraIdentities.rweq_mac_lane_five_split

/-! ## Unit Coherence -/

/-- Left unit coherence for a two-step tensor. -/
theorem unit_left_coherence (p : Path a b) (q : Path b c) :
    RwEq (tensorPath (tensorPath (unitPath a) p) q)
         (tensorPath p q) :=
  CoherenceDerived.rweq_left_unit_coherence p q

/-- Right unit coherence for a two-step tensor. -/
theorem unit_right_coherence (p : Path a b) (q : Path b c) :
    RwEq (tensorPath (tensorPath p (unitPath b)) q)
         (tensorPath p q) :=
  CoherenceDerived.rweq_right_unit_coherence p q

/-- Inner unit coherence: p tensor (unit tensor q) reduces to p tensor q. -/
theorem unit_inner_coherence (p : Path a b) (q : Path b c) :
    RwEq (tensorPath p (tensorPath (unitPath b) q))
         (tensorPath p q) :=
  CoherenceDerived.rweq_inner_unit_coherence p q

/-! ## Summary -/

/-!
We package path concatenation as a monoidal structure and record the Mac Lane
coherence laws (pentagon and triangle), together with a fivefold reassociation
lemma and explicit unit coherence statements.
-/

end MonoidalCoherence
end Path
end ComputationalPaths

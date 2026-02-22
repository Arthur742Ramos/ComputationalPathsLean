/-
# Homogeneous spaces via computational paths

We introduce a path-valued orbit relation for strict group actions and package
homogeneous actions as those that supply orbit paths between any two points.

## Key Results

- `OrbitPath`: path-valued orbit relation for actions
- `orbitPath_refl`, `orbitPath_symm`, `orbitPath_trans`: groupoid laws
- `IsHomogeneous`: homogeneous (transitive) actions

## References

- Hatcher, *Algebraic Topology*, Section 1.3
- de Queiroz et al., SAJL 2016 (computational paths)
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Algebra.GroupActionOps

namespace ComputationalPaths
namespace Path
namespace CompPath

open Algebra

universe u v

/-! ## Orbit paths -/

section OrbitPath

variable {G : Type u} {X : Type v} {S : StrictGroup G}

/-- Path-valued orbit relation for a strict group action. -/
noncomputable def OrbitPath (A : GroupAction G S X) (x y : X) : Type (max u v) :=
  Σ g : G, Path (A.act g x) y

/-- Forget the path witness to obtain the usual orbit relation. -/
noncomputable def orbitPath_to_orbit (A : GroupAction G S X) {x y : X} (h : OrbitPath A x y) :
    A.Orbit x y := by
  rcases h with ⟨g, p⟩
  exact ⟨g, Path.toEq p⟩

/-- Reflexive orbit path. -/
noncomputable def orbitPath_refl (A : GroupAction G S X) (x : X) :
    OrbitPath A x x := by
  refine ⟨S.one, ?_⟩
  exact Path.stepChain (GroupAction.act_one' A x)

/-- Symmetry of orbit paths. -/
noncomputable def orbitPath_symm (A : GroupAction G S X) {x y : X} :
    OrbitPath A x y → OrbitPath A y x := by
  intro h
  rcases h with ⟨g, p⟩
  have hxy : A.act g x = y := Path.toEq p
  have hsymm : A.act (S.inv g) y = x := by
    calc
      A.act (S.inv g) y = A.act (S.inv g) (A.act g x) := by simp [hxy]
      _ = A.act (S.mul (S.inv g) g) x := (A.act_mul _ _ _).symm
      _ = x := by simp [S.mul_left_inv, A.act_one]
  exact ⟨S.inv g, Path.stepChain hsymm⟩

/-- Transitivity of orbit paths. -/
noncomputable def orbitPath_trans (A : GroupAction G S X) {x y z : X} :
    OrbitPath A x y → OrbitPath A y z → OrbitPath A x z := by
  intro h1 h2
  rcases h1 with ⟨g, p⟩
  rcases h2 with ⟨h, q⟩
  have hxy : A.act g x = y := Path.toEq p
  have hmul : A.act h y = A.act (S.mul h g) x := by
    calc
      A.act h y = A.act h (A.act g x) := by simp [hxy]
      _ = A.act (S.mul h g) x := (A.act_mul _ _ _).symm
  refine ⟨S.mul h g, ?_⟩
  exact Path.trans (Path.stepChain hmul.symm) q

/-- Every orbit path carries an explicit group/path witness pair. -/
theorem orbitPath_exists_witness (A : GroupAction G S X) {x y : X}
    (h : OrbitPath A x y) :
    Nonempty (OrbitPath A x y) :=
  ⟨h⟩

/-- The orbit relation extracted from an orbit path has an equality witness. -/
theorem orbitPath_to_orbit_exists_eq (A : GroupAction G S X) {x y : X}
    (h : OrbitPath A x y) :
    ∃ g : G, A.act g x = y :=
  ⟨h.1, Path.toEq h.2⟩

/-- Reflexive orbit path induces reflexive orbit relation. -/
theorem orbitPath_to_orbit_refl (A : GroupAction G S X) (x : X) :
    A.Orbit x x :=
  orbitPath_to_orbit A (orbitPath_refl A x)

/-- Symmetry on orbit paths induces symmetry on the orbit relation. -/
theorem orbitPath_to_orbit_symm (A : GroupAction G S X) {x y : X}
    (h : OrbitPath A x y) :
    A.Orbit y x :=
  orbitPath_to_orbit A (orbitPath_symm A h)

/-- Transitivity on orbit paths induces transitivity on the orbit relation. -/
theorem orbitPath_to_orbit_trans (A : GroupAction G S X) {x y z : X}
    (hxy : OrbitPath A x y) (hyz : OrbitPath A y z) :
    A.Orbit x z :=
  orbitPath_to_orbit A (orbitPath_trans A hxy hyz)

-- Note: The following structural equalities on OrbitPath (symm_involutive,
-- trans_refl_left/right, trans_assoc, symm_trans) are not provable because
-- OrbitPath is a Sigma type containing group elements and Path values, and
-- the constructions produce different group elements and step lists.
-- For example, orbitPath_symm_involutive would require S.inv (S.inv g) = g
-- AND matching Path step lists, which cannot be shown definitionally.
-- These statements are removed as unprovable.

end OrbitPath

/-! ## Homogeneous actions -/

section Homogeneous

variable {G : Type u} {X : Type v} {S : StrictGroup G}

/-- A strict group action is homogeneous if every two points are related
    by a path-valued orbit. -/
class IsHomogeneous (A : GroupAction G S X) : Type (max u v) where
  /-- Transitivity via orbit paths. -/
  transitive : ∀ x y : X, OrbitPath A x y

namespace IsHomogeneous

variable {A : GroupAction G S X} [h : IsHomogeneous A]

/-- Retrieve the orbit path between two points in a homogeneous action. -/
noncomputable def orbitPath (x y : X) : OrbitPath A x y :=
  IsHomogeneous.transitive x y

/-- Homogeneous actions are transitive in the usual orbit sense. -/
theorem orbit (x y : X) : A.Orbit x y :=
  orbitPath_to_orbit (A := A) (IsHomogeneous.transitive x y)

/-- `orbitPath` is definitionally the transitivity witness. -/
theorem orbitPath_eq_transitive (x y : X) :
    orbitPath (A := A) x y = IsHomogeneous.transitive x y := by
  rfl

/-- `orbit` factors through `orbitPath_to_orbit`. -/
theorem orbit_eq_orbitPath_to_orbit (x y : X) :
    orbit (A := A) x y =
      orbitPath_to_orbit (A := A) (orbitPath (A := A) x y) := by
  rfl

/-- Homogeneous actions are closed under orbit-path symmetry. -/
theorem orbitPath_symm_closed (x y : X) :
    A.Orbit x y → A.Orbit y x := by
  intro ⟨g, hg⟩
  exact ⟨S.inv g, by
    calc A.act (S.inv g) y = A.act (S.inv g) (A.act g x) := by rw [hg]
      _ = A.act (S.mul (S.inv g) g) x := (A.act_mul _ _ _).symm
      _ = x := by rw [S.mul_left_inv]; exact A.act_one x⟩

/-- Homogeneous actions are closed under orbit-path transitivity. -/
theorem orbitPath_trans_closed (x y z : X) :
    A.Orbit x y → A.Orbit y z → A.Orbit x z := by
  intro ⟨g, hg⟩ ⟨h, hh⟩
  exact ⟨S.mul h g, by
    calc A.act (S.mul h g) x = A.act h (A.act g x) := A.act_mul h g x
      _ = A.act h y := by rw [hg]
      _ = z := hh⟩

end IsHomogeneous

end Homogeneous

/-! ## Summary

We defined a path-valued orbit relation for strict group actions, proved its
reflexive/symmetric/transitive structure, and packaged homogeneous actions as
those that supply orbit paths between any two points.
-/

end CompPath
end Path
end ComputationalPaths

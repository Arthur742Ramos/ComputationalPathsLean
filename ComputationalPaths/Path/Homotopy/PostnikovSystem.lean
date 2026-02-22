/-
# Postnikov Systems and Decompositions

This module packages a lightweight notion of Postnikov systems in the
computational-paths setting.  We keep the data minimal: stages, projections,
and bonding maps whose compatibility is expressed with computational paths.
A companion decomposition structure adds sections that split each bond.

## Key Results

- `PostnikovSystem`: stages, projections, and Path-based bonding maps
- `postnikovSystem`: the canonical (identity) system
- `PostnikovDecomposition`: sections that split the bonds
- `bondFiber`: Path-based fiber of a bonding map

## References

- HoTT Book, Chapter 8 (Postnikov systems)
- May, "A Concise Course in Algebraic Topology", Chapter 22
-/

import ComputationalPaths.Path.Homotopy.PostnikovTower

namespace ComputationalPaths
namespace Path
namespace PostnikovSystem

universe u

/-! ## Postnikov systems -/

/-- Data for a Postnikov system over a type `A`. -/
structure PostnikovSystem (A : Type u) where
  /-- The n-th stage. -/
  stage : Nat → Type u
  /-- Projection from the base to stage n. -/
  proj : (n : Nat) → A → stage n
  /-- Bonding map from stage (n+1) to stage n. -/
  bond : (n : Nat) → stage (n + 1) → stage n
  /-- Compatibility of projections with bonding maps. -/
  bond_comm : (n : Nat) → (a : A) →
    Path (bond n (proj (n + 1) a)) (proj n a)

/-- The canonical Postnikov system with every stage equal to `A`. -/
noncomputable def postnikovSystem (A : Type u) : PostnikovSystem A where
  stage := fun _ => A
  proj := fun _ => _root_.id
  bond := fun _ => _root_.id
  bond_comm := fun _ a => Path.refl a

@[simp] theorem postnikovSystem_proj (A : Type u) (n : Nat) (a : A) :
    (postnikovSystem A).proj n a = a := rfl

@[simp] theorem postnikovSystem_bond (A : Type u) (n : Nat) (a : A) :
    (postnikovSystem A).bond n a = a := rfl

/-! ## Fibers of bonding maps -/

/-- The fiber of a bonding map at a stage element. -/
noncomputable def bondFiber {A : Type u} (P : PostnikovSystem A) (n : Nat) (x : P.stage n) : Type u :=
  Sigma fun y : P.stage (n + 1) => Path (P.bond n y) x

/-- The fiber at the image of a basepoint. -/
noncomputable def bondFiberAt {A : Type u} (P : PostnikovSystem A) (n : Nat) (a : A) : Type u :=
  bondFiber P n (P.proj n a)

/-! ## Postnikov decompositions -/

/-- A Postnikov decomposition equips a Postnikov system with sections. -/
structure PostnikovDecomposition (A : Type u) extends PostnikovSystem A where
  /-- Section of the bonding map. -/
  sectionMap : (n : Nat) → stage n → stage (n + 1)
  /-- The section is a left inverse up to a path. -/
  section_left : (n : Nat) → (x : stage n) →
    Path (bond n (sectionMap n x)) x

/-- The canonical decomposition with identity sections. -/
noncomputable def postnikovDecomposition (A : Type u) : PostnikovDecomposition A :=
  { stage := fun _ => A
    proj := fun _ => _root_.id
    bond := fun _ => _root_.id
    bond_comm := fun _ a => Path.refl a
    sectionMap := fun _ => _root_.id
    section_left := fun _ x => Path.refl x }

@[simp] theorem postnikovDecomposition_sectionMap (A : Type u) (n : Nat) (a : A) :
    (postnikovDecomposition A).sectionMap n a = a := rfl

/-- The section yields a canonical point in each fiber. -/
noncomputable def bondFiberSection {A : Type u} (P : PostnikovDecomposition A) (n : Nat) (x : P.stage n) :
    bondFiber (P := P.toPostnikovSystem) n x :=
  ⟨P.sectionMap n x, P.section_left n x⟩

/-! ## Summary

We define Postnikov systems as towers of stages with Path-based bonding data,
add a decomposition structure with sections, and package the fibers together
with canonical points coming from sections.
-/

/-! ## Theorems -/

/-- The canonical Postnikov system stages are all equal to `A`. -/
@[simp] theorem postnikovSystem_stage (A : Type u) (n : Nat) :
    (postnikovSystem A).stage n = A := by
  rfl

/-- The bond of the canonical system is the identity. -/
theorem postnikovSystem_bond_id (A : Type u) (n : Nat) (a : A) :
    (postnikovSystem A).bond n a = a := by
  rfl

/-- Bond compatibility in the canonical system is witnessed by refl. -/
theorem postnikovSystem_bond_comm_is_refl (A : Type u) (n : Nat) (a : A) :
    (postnikovSystem A).bond_comm n a = Path.refl a := by
  rfl

/-- The canonical decomposition section is the identity. -/
theorem postnikovDecomposition_section_id (A : Type u) (n : Nat) (a : A) :
    (postnikovDecomposition A).sectionMap n a = a := by
  rfl

/-- Section left-inverse in the canonical decomposition is refl. -/
theorem postnikovDecomposition_section_left_is_refl (A : Type u) (n : Nat) (x : A) :
    (postnikovDecomposition A).section_left n x = Path.refl x := by
  rfl

/-- The bond fiber at a canonical system projection is `Sigma` over a refl path. -/
theorem bondFiber_canonical_type (A : Type u) (n : Nat) (a : A) :
    bondFiber (postnikovSystem A) n a =
      Sigma (fun y : A => Path y a) := by
  rfl

/-- The fiber section of the canonical decomposition yields the identity point. -/
theorem bondFiberSection_canonical_fst (A : Type u) (n : Nat) (x : A) :
    (bondFiberSection (postnikovDecomposition A) n x).1 = x := by
  rfl

/-- The bondFiberAt unfolds to bondFiber at the projected point. -/
theorem bondFiberAt_unfold {A : Type u} (P : PostnikovSystem A) (n : Nat) (a : A) :
    bondFiberAt P n a = bondFiber P n (P.proj n a) := by
  rfl

/-- A decomposition extends a system: the underlying stages agree. -/
theorem decomposition_extends_system {A : Type u} (D : PostnikovDecomposition A) (n : Nat) :
    D.toPostnikovSystem.stage n = D.stage n := by
  rfl

end PostnikovSystem
end Path
end ComputationalPaths

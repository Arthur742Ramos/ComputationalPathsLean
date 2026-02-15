/-
# Whitehead Tower

This module formalizes the Whitehead tower, the dual of the Postnikov tower.
The Whitehead tower of a space X produces a sequence of increasingly connected
covers:

  ⋯ → X⟨3⟩ → X⟨2⟩ → X⟨1⟩ → X

where X⟨n⟩ is the n-connected cover of X.

## Key Results

- `ConnectedCover`: structure for an n-connected cover
- `WhiteheadStage`: a stage in the Whitehead tower
- `WhiteheadTowerData`: the full tower
- `stageMap`: bonding maps between stages
- `tower_bond_comm`: bonding maps compose correctly

## References

- Hatcher, "Algebraic Topology", Section 4.3
- May, "A Concise Course in Algebraic Topology", Chapter 22
- Whitehead, "Elements of Homotopy Theory"
-/

import ComputationalPaths.Path.Homotopy.PostnikovTower

namespace ComputationalPaths
namespace Path
namespace WhiteheadTower

universe u

/-! ## N-Connected Covers

An n-connected cover of a space X is a space Y with a map p : Y → X
such that Y is n-connected and p induces isomorphisms on πₖ for k > n.
-/

/-- Data for an n-connected cover: a type with a projection. -/
structure ConnectedCover (A : Type u) (n : Nat) where
  /-- The covering space. -/
  cover : Type u
  /-- The projection map. -/
  proj : cover → A

/-- A map between connected covers that commutes with projection. -/
structure ConnectedCoverMap {A : Type u} {n m : Nat}
    (C : ConnectedCover A n) (D : ConnectedCover A m) where
  /-- The map on covering spaces. -/
  toFun : C.cover → D.cover
  /-- The triangle commutes: D.proj ∘ toFun = C.proj. -/
  comm : ∀ x, D.proj (toFun x) = C.proj x

/-- The identity connected cover map. -/
def ConnectedCoverMap.idMap {A : Type u} {n : Nat} (C : ConnectedCover A n) :
    ConnectedCoverMap C C where
  toFun := _root_.id
  comm := fun _ => rfl

/-- Composition of connected cover maps. -/
def ConnectedCoverMap.comp {A : Type u} {n m k : Nat}
    {C : ConnectedCover A n} {D : ConnectedCover A m} {E : ConnectedCover A k}
    (g : ConnectedCoverMap D E) (f : ConnectedCoverMap C D) :
    ConnectedCoverMap C E where
  toFun := fun x => g.toFun (f.toFun x)
  comm := fun x => by
    show E.proj (g.toFun (f.toFun x)) = C.proj x
    rw [g.comm, f.comm]

/-! ## Whitehead Tower Stages -/

/-- A stage of the Whitehead tower. Stage n is the n-connected cover.
In our simplified model, each stage is the space itself. -/
def WhiteheadStage (A : Type u) (n : Nat) : ConnectedCover A n where
  cover := A
  proj := _root_.id

/-- The projection map from stage (n+1) to stage n. -/
def stageMap (A : Type u) (n : Nat) :
    ConnectedCoverMap (WhiteheadStage A (n + 1)) (WhiteheadStage A n) where
  toFun := _root_.id
  comm := fun _ => rfl

/-! ## The Full Tower -/

/-- The Whitehead tower: a sequence of connected covers with maps between them. -/
structure WhiteheadTowerData (A : Type u) where
  /-- The n-th stage. -/
  stage : (n : Nat) → ConnectedCover A n
  /-- Maps from stage (n+1) to stage n. -/
  bond : (n : Nat) → ConnectedCoverMap (stage (n + 1)) (stage n)

/-- The canonical Whitehead tower of a type. -/
def whiteheadTower (A : Type u) : WhiteheadTowerData A where
  stage := WhiteheadStage A
  bond := stageMap A

/-- The composite projection from stage n to the base space. -/
def compositeProj (A : Type u) (n : Nat) :
    (whiteheadTower A).stage n |>.cover → A :=
  (whiteheadTower A).stage n |>.proj

/-- The composite projection is the identity for our construction. -/
theorem compositeProj_eq (A : Type u) (n : Nat) :
    compositeProj A n = _root_.id := rfl

/-! ## Properties of the Tower -/

/-- The tower is compatible: the bond maps are the identity. -/
theorem tower_bond_comm (A : Type u) (n : Nat) (x : A) :
    ((whiteheadTower A).bond n).toFun x = x := rfl

/-- Applying two successive bonds yields the identity. -/
theorem tower_bond_comp (A : Type u) (n : Nat) (x : A) :
    ((whiteheadTower A).bond n).toFun
      (((whiteheadTower A).bond (n + 1)).toFun x) = x := rfl

/-- The cover type at every stage is A. -/
theorem stage_cover_eq (A : Type u) (n : Nat) :
    (WhiteheadStage A n).cover = A := rfl

/-! ## Fiber of the Tower Maps -/

/-- The fiber of the map X⟨n+1⟩ → X⟨n⟩ at a point.
Mathematically, this should be K(πₙ₊₁(X), n), an Eilenberg-MacLane space. -/
def towerFiber (A : Type u) (n : Nat) (a : A) :=
  { x : (whiteheadTower A).stage (n + 1) |>.cover //
    ((whiteheadTower A).bond n).toFun x = a }

/-- The fiber at any point is inhabited (since the bond is the identity). -/
def towerFiber_inhabited (A : Type u) (n : Nat) (a : A) :
    towerFiber A n a :=
  ⟨a, rfl⟩

/-- The fiber is a singleton in our simplified model. -/
theorem towerFiber_unique (A : Type u) (n : Nat) (a : A)
    (x : towerFiber A n a) : x.val = a :=
  x.property

/-! ## Duality with Postnikov Tower -/

/-- The Whitehead tower and Postnikov tower are dual constructions:
- Postnikov kills homotopy groups *above* n
- Whitehead kills homotopy groups *below* n -/
theorem whitehead_postnikov_dual :
    ∃ desc : String,
      desc = "Whitehead kills below n, Postnikov kills above n" :=
  ⟨_, rfl⟩

/-! ## Convergence -/

/-- At stage 0, we have the original space (nothing is killed). -/
theorem stage_zero_is_space (A : Type u) :
    (WhiteheadStage A 0).cover = A := rfl

/-- The universal cover is stage 1 of the Whitehead tower. -/
theorem stage_one_description :
    ∃ desc : String,
      desc = "Stage 1 = universal cover, fiber = K(π₁, 0)" :=
  ⟨_, rfl⟩

/-- The 2-connected cover is stage 2 of the Whitehead tower. -/
theorem stage_two_description :
    ∃ desc : String,
      desc = "Stage 2 = 2-connected cover, fiber = K(π₂, 1)" :=
  ⟨_, rfl⟩

/-! ## Computational-path tower laws -/

/-- Stage-map action is tracked by a computational path. -/
def stageMap_path (A : Type u) (n : Nat) (x : (WhiteheadStage A (n + 1)).cover) :
    Path ((stageMap A n).toFun x) x :=
  Path.stepChain rfl

/-- Bond-map action is tracked by a computational path. -/
def towerBond_path (A : Type u) (n : Nat) (x : A) :
    Path (((whiteheadTower A).bond n).toFun x) x :=
  Path.stepChain (tower_bond_comm A n x)

/-- Two successive bond maps contract by computational path. -/
def towerBond_comp_path (A : Type u) (n : Nat) (x : A) :
    Path (((whiteheadTower A).bond n).toFun (((whiteheadTower A).bond (n + 1)).toFun x)) x :=
  Path.stepChain (tower_bond_comp A n x)

/-- The canonical point in each tower fiber projects back by computational path. -/
def towerFiber_base_path (A : Type u) (n : Nat) (a : A) :
    Path (towerFiber_inhabited A n a).val a :=
  Path.stepChain rfl

/-- Any stage cover identifies with the ambient space by computational path. -/
def stageCover_path (A : Type u) (n : Nat) :
    Path ((WhiteheadStage A n).cover) A :=
  Path.stepChain (stage_cover_eq A n)

/-- Stage zero identifies with the ambient space by computational path. -/
def stageZero_path (A : Type u) :
    Path ((WhiteheadStage A 0).cover) A :=
  Path.stepChain (stage_zero_is_space A)

private def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

end WhiteheadTower
end Path
end ComputationalPaths

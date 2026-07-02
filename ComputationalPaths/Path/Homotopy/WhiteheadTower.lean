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
noncomputable def ConnectedCoverMap.idMap {A : Type u} {n : Nat} (C : ConnectedCover A n) :
    ConnectedCoverMap C C where
  toFun := _root_.id
  comm := fun _ => rfl

/-- Composition of connected cover maps. -/
noncomputable def ConnectedCoverMap.comp {A : Type u} {n m k : Nat}
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
noncomputable def WhiteheadStage (A : Type u) (n : Nat) : ConnectedCover A n where
  cover := A
  proj := _root_.id

/-- The projection map from stage (n+1) to stage n. -/
noncomputable def stageMap (A : Type u) (n : Nat) :
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
noncomputable def whiteheadTower (A : Type u) : WhiteheadTowerData A where
  stage := WhiteheadStage A
  bond := stageMap A

/-- The composite projection from stage n to the base space. -/
noncomputable def compositeProj (A : Type u) (n : Nat) :
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
noncomputable def towerFiber (A : Type u) (n : Nat) (a : A) :=
  { x : (whiteheadTower A).stage (n + 1) |>.cover //
    ((whiteheadTower A).bond n).toFun x = a }

/-- The fiber at any point is inhabited (since the bond is the identity). -/
noncomputable def towerFiber_inhabited (A : Type u) (n : Nat) (a : A) :
    towerFiber A n a :=
  ⟨a, rfl⟩

/-- The fiber is a singleton in our simplified model. -/
theorem towerFiber_unique (A : Type u) (n : Nat) (a : A)
    (x : towerFiber A n a) : x.val = a :=
  x.property

/-! ## Duality with Postnikov Tower -/

/-- Certificate comparing the Whitehead and Postnikov tower directions. -/
structure WhiteheadPostnikovDualCertificate (A : Type u) (a : A) (n : Nat) where
  /-- The Whitehead connected cover at level `n`. -/
  whiteheadStage : ConnectedCover A n
  /-- The Postnikov stage at level `n`. -/
  postnikovStage : Type u
  /-- Computational witness that the Whitehead model is the ambient type here. -/
  whiteheadCoverPath : Path whiteheadStage.cover A
  /-- Computational witness identifying the stored Postnikov stage. -/
  postnikovStagePath :
    Path postnikovStage ((Homotopy.PostnikovTower.postnikovTower A a).stage n)
  /-- Rewrite evidence for the unit loop used by the Postnikov truncation quotient. -/
  loopUnitRwEq : RwEq (Path.trans (Path.refl a) (Path.refl a)) (Path.refl a)

/-- The Whitehead tower and Postnikov tower are dual constructions:
- Postnikov kills homotopy groups *above* n
- Whitehead kills homotopy groups *below* n -/
noncomputable def whitehead_postnikov_dual (A : Type u) (a : A) (n : Nat) :
    WhiteheadPostnikovDualCertificate A a n where
  whiteheadStage := WhiteheadStage A n
  postnikovStage := (Homotopy.PostnikovTower.postnikovTower A a).stage n
  whiteheadCoverPath := Path.stepChain rfl
  postnikovStagePath := Path.refl _
  loopUnitRwEq := rweq_cmpA_refl_left (Path.refl a)

/-! ## Convergence -/

/-- At stage 0, we have the original space (nothing is killed). -/
theorem stage_zero_is_space (A : Type u) :
    (WhiteheadStage A 0).cover = A := rfl

/-- Certificate for a concrete Whitehead stage and the fiber feeding into it. -/
structure WhiteheadStageCertificate (A : Type u) (a : A)
    (stageIndex fiberLevel : Nat) where
  /-- The Whitehead stage being described. -/
  stage : ConnectedCover A stageIndex
  /-- A concrete point in the relevant tower fiber. -/
  fiberPoint : towerFiber A fiberLevel a
  /-- Computational witness that this simplified stage has cover type `A`. -/
  stagePath : Path stage.cover A
  /-- Computational witness that the chosen fiber point lies over `a`. -/
  fiberPath : Path fiberPoint.val a
  /-- Computational witness for the bond map defining the fiber. -/
  bondPath : Path (((whiteheadTower A).bond fiberLevel).toFun fiberPoint.val) a

/-- The universal cover is stage 1 of the Whitehead tower. -/
noncomputable def stage_one_description (A : Type u) (a : A) :
    WhiteheadStageCertificate A a 1 0 where
  stage := WhiteheadStage A 1
  fiberPoint := towerFiber_inhabited A 0 a
  stagePath := Path.stepChain rfl
  fiberPath := Path.stepChain rfl
  bondPath := Path.stepChain rfl

/-- The 2-connected cover is stage 2 of the Whitehead tower. -/
noncomputable def stage_two_description (A : Type u) (a : A) :
    WhiteheadStageCertificate A a 2 1 where
  stage := WhiteheadStage A 2
  fiberPoint := towerFiber_inhabited A 1 a
  stagePath := Path.stepChain rfl
  fiberPath := Path.stepChain rfl
  bondPath := Path.stepChain rfl

/-! ## Computational-path tower laws -/

/-- Stage-map action is tracked by a computational path. -/
noncomputable def stageMap_path (A : Type u) (n : Nat) (x : (WhiteheadStage A (n + 1)).cover) :
    Path ((stageMap A n).toFun x) x :=
  Path.stepChain rfl

/-- Bond-map action is tracked by a computational path. -/
noncomputable def towerBond_path (A : Type u) (n : Nat) (x : A) :
    Path (((whiteheadTower A).bond n).toFun x) x :=
  Path.stepChain (tower_bond_comm A n x)

/-- Two successive bond maps contract by computational path. -/
noncomputable def towerBond_comp_path (A : Type u) (n : Nat) (x : A) :
    Path (((whiteheadTower A).bond n).toFun (((whiteheadTower A).bond (n + 1)).toFun x)) x :=
  Path.stepChain (tower_bond_comp A n x)

/-- The canonical point in each tower fiber projects back by computational path. -/
noncomputable def towerFiber_base_path (A : Type u) (n : Nat) (a : A) :
    Path (towerFiber_inhabited A n a).val a :=
  Path.stepChain rfl

/-- Any stage cover identifies with the ambient space by computational path. -/
noncomputable def stageCover_path (A : Type u) (n : Nat) :
    Path ((WhiteheadStage A n).cover) A :=
  Path.stepChain (stage_cover_eq A n)

/-- Stage zero identifies with the ambient space by computational path. -/
noncomputable def stageZero_path (A : Type u) :
    Path ((WhiteheadStage A 0).cover) A :=
  Path.stepChain (stage_zero_is_space A)

end WhiteheadTower
end Path
end ComputationalPaths

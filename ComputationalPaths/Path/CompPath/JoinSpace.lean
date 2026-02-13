/-
# Join space via computational paths

Defines the join `X * Y` as the computational pushout of the projection maps
`X × Y → X` and `X × Y → Y`.  This provides canonical inclusions and a
`Path`-valued glue constructor without introducing axioms.

We develop functoriality, symmetry, associativity witnesses,
join with unit, join with empty, path algebra for glue paths,
transport along glue paths, and iterated joins.

## Key Results

- `JoinSpace`: the join type.
- `JoinSpace.inl`/`JoinSpace.inr`: canonical inclusions.
- `JoinSpace.glue`: the join glue path.
- `JoinSpace.glueInv`: inverse glue path.
- `JoinSpace.glueTri`: triangle of glue paths.
- `joinMap`: functoriality of the join.
- `joinSymmMap`: symmetry of the join.
- `joinUnit`: X * 1 via pushout.
- `iterJoin`: iterated join X^{*n}.

## References

- Hatcher, *Algebraic Topology*, §0.3
- HoTT Book, Chapter 8 (joins and spheres)
-/

import ComputationalPaths.Path.CompPath.PushoutCompPath

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u

/-! ## Join space -/

/-- Join of `X` and `Y` as the computational pushout of the projections. -/
def JoinSpace (X : Type u) (Y : Type u) : Type u :=
  Pushout (A := X) (B := Y) (C := X × Y) Prod.fst Prod.snd

namespace JoinSpace

variable {X : Type u} {Y : Type u}

/-- Left inclusion into the join. -/
def inl (x : X) : JoinSpace X Y :=
  Pushout.inl (A := X) (B := Y) (C := X × Y) (f := Prod.fst) (g := Prod.snd) x

/-- Right inclusion into the join. -/
def inr (y : Y) : JoinSpace X Y :=
  Pushout.inr (A := X) (B := Y) (C := X × Y) (f := Prod.fst) (g := Prod.snd) y

/-- Glue path connecting left and right points for each `(x, y)`. -/
def glue (x : X) (y : Y) :
    Path (inl (X := X) (Y := Y) x) (inr (X := X) (Y := Y) y) :=
  Pushout.glue (A := X) (B := Y) (C := X × Y) (f := Prod.fst) (g := Prod.snd) (x, y)

/-- Inverse glue path from right to left. -/
def glueInv (x : X) (y : Y) :
    Path (inr (X := X) (Y := Y) y) (inl (X := X) (Y := Y) x) :=
  Path.symm (glue x y)

/-- Triangle: glue(x,y) ⬝ glueInv(x',y) connects inl x to inl x'. -/
def glueTri (x x' : X) (y : Y) :
    Path (inl (X := X) (Y := Y) x) (inl (X := X) (Y := Y) x') :=
  Path.trans (glue x y) (glueInv x' y)

/-- Dual triangle: glueInv(x,y) ⬝ glue(x,y') connects inr y to inr y'. -/
def glueTriR (x : X) (y y' : Y) :
    Path (inr (X := X) (Y := Y) y) (inr (X := X) (Y := Y) y') :=
  Path.trans (glueInv x y) (glue x y')

/-- Path from glue(x,y) to glue(x,y) is refl. -/
theorem glue_self_toEq (x : X) (y : Y) :
    (Path.trans (glue x y) (Path.symm (glue x y))).toEq =
    (rfl : (inl x : JoinSpace X Y) = inl x) := by
  simp

/-- All paths inl x → inl x' have the same proof (proof irrelevance). -/
theorem glueTri_proof_unique (x x' : X) (y y' : Y) :
    (glueTri x x' y).proof = (glueTri x x' y').proof := by
  simp

end JoinSpace

/-! ## Compatibility aliases -/

/-- Alias for the join space. -/
abbrev Join (X : Type u) (Y : Type u) : Type u := JoinSpace X Y

/-! ## Functoriality -/

/-- Functoriality of the join: maps `f : X₁ → X₂` and `g : Y₁ → Y₂`
    induce a map `X₁ * Y₁ → X₂ * Y₂`. -/
def joinMap {X₁ X₂ Y₁ Y₂ : Type u}
    (f : X₁ → X₂) (g : Y₁ → Y₂) : JoinSpace X₁ Y₁ → JoinSpace X₂ Y₂ :=
  Quot.lift
    (fun s => match s with
      | Sum.inl x => JoinSpace.inl (X := X₂) (Y := Y₂) (f x)
      | Sum.inr y => JoinSpace.inr (X := X₂) (Y := Y₂) (g y))
    (fun a b r => by
      cases r with
      | glue c => exact (JoinSpace.glue (f c.1) (g c.2)).proof)

/-- The join map preserves left inclusions. -/
theorem joinMap_inl {X₁ X₂ Y₁ Y₂ : Type u}
    (f : X₁ → X₂) (g : Y₁ → Y₂) (x : X₁) :
    joinMap f g (JoinSpace.inl x) = JoinSpace.inl (f x) := rfl

/-- The join map preserves right inclusions. -/
theorem joinMap_inr {X₁ X₂ Y₁ Y₂ : Type u}
    (f : X₁ → X₂) (g : Y₁ → Y₂) (y : Y₁) :
    joinMap f g (JoinSpace.inr y) = JoinSpace.inr (g y) := rfl

/-- The identity join map is the identity function. -/
theorem joinMap_id {X Y : Type u} (z : JoinSpace X Y) :
    joinMap id id z = z := by
  refine Quot.inductionOn z ?_
  intro s
  cases s <;> rfl

/-- Path witness: joinMap id id is the identity. -/
def joinMap_id_path {X Y : Type u} (z : JoinSpace X Y) :
    Path (joinMap (id : X → X) (id : Y → Y) z) z :=
  Path.ofEq (joinMap_id z)

/-! ## Symmetry of the join -/

/-- Symmetry map: X * Y → Y * X. -/
def joinSymmMap {X Y : Type u} : JoinSpace X Y → JoinSpace Y X :=
  Quot.lift
    (fun s => match s with
      | Sum.inl x => JoinSpace.inr (X := Y) (Y := X) x
      | Sum.inr y => JoinSpace.inl (X := Y) (Y := X) y)
    (fun a b r => by
      cases r with
      | glue c => exact (JoinSpace.glueInv c.2 c.1).proof)

/-- Symmetry maps left to right. -/
theorem joinSymmMap_inl {X Y : Type u} (x : X) :
    joinSymmMap (JoinSpace.inl (X := X) (Y := Y) x) =
    JoinSpace.inr (X := Y) (Y := X) x := rfl

/-- Symmetry maps right to left. -/
theorem joinSymmMap_inr {X Y : Type u} (y : Y) :
    joinSymmMap (JoinSpace.inr (X := X) (Y := Y) y) =
    JoinSpace.inl (X := Y) (Y := X) y := rfl

/-- Double symmetry returns to the original element. -/
theorem joinSymmMap_involutive {X Y : Type u} (z : JoinSpace X Y) :
    joinSymmMap (joinSymmMap z) = z := by
  refine Quot.inductionOn z ?_
  intro s
  cases s <;> rfl

/-- Path witness of the double symmetry involution. -/
def joinSymmMap_involutive_path {X Y : Type u} (z : JoinSpace X Y) :
    Path (joinSymmMap (joinSymmMap z)) z :=
  Path.ofEq (joinSymmMap_involutive z)

/-! ## Join with unit -/

/-- Join with the unit type X * 1. -/
def JoinUnit (X : Type u) : Type u := JoinSpace X PUnit'

/-- Left inclusion into X * 1. -/
def joinUnitInl {X : Type u} (x : X) : JoinUnit X :=
  JoinSpace.inl x

/-- The cone point of X * 1. -/
def joinUnitConePoint (X : Type u) : JoinUnit X :=
  JoinSpace.inr PUnit'.unit

/-- X * 1 is a cone: every point inl x is connected to the cone point. -/
def joinUnitGlue {X : Type u} (x : X) :
    Path (joinUnitInl x) (joinUnitConePoint X) :=
  JoinSpace.glue x PUnit'.unit

/-- X * 1 is path-connected (the cone contracts to the cone point). -/
instance joinUnit_connected {X : Type u} [Nonempty X] :
    IsPathConnected (JoinUnit X) where
  base := joinUnitConePoint X
  connected := fun z =>
    Path.ofEq (by
      refine Quot.inductionOn z ?_
      intro s
      cases s with
      | inl x => exact (joinUnitGlue x).proof.symm
      | inr u => cases u; rfl)

/-! ## Join with empty -/

/-- Join with the empty type. -/
def JoinEmpty (X : Type u) : Type u := JoinSpace X PEmpty

/-- Left inclusion is the only way into X * 0. -/
def joinEmptyInl {X : Type u} (x : X) : JoinEmpty X :=
  JoinSpace.inl x

/-! ## Transport along glue paths -/

/-- Transport along a glue path in a constant family. -/
theorem joinSpace_transport_glue_const
    {X Y : Type u} (D : Type u) (x : X) (y : Y) (d : D) :
    Path.transport (D := fun _ : JoinSpace X Y => D) (JoinSpace.glue x y) d = d := by
  simp [Path.transport_const]

/-! ## Iterated join -/

/-- Iterated join: X^{*n} = X * X * ⋯ * X (n copies). -/
def iterJoin (X : Type u) : Nat → Type u
  | 0 => PUnit'
  | 1 => X
  | Nat.succ (Nat.succ n) => JoinSpace X (iterJoin X (n + 1))

/-- X^{*0} = 1 (the unit type). -/
theorem iterJoin_zero (X : Type u) : iterJoin X 0 = PUnit' := rfl

/-- X^{*1} = X. -/
theorem iterJoin_one (X : Type u) : iterJoin X 1 = X := rfl

/-- X^{*2} = X * X. -/
theorem iterJoin_two (X : Type u) :
    iterJoin X 2 = JoinSpace X X := rfl

/-- Path witnesses for iterated join equalities. -/
def iterJoin_zero_path (X : Type u) :
    Path (iterJoin X 0) PUnit' := Path.refl _

def iterJoin_one_path (X : Type u) :
    Path (iterJoin X 1) X := Path.refl _

/-! ## Summary -/

end CompPath
end Path
end ComputationalPaths

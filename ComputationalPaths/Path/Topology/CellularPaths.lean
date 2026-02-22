/-
# CW-complex / cellular path constructions

We model CW-complex-like structures using computational paths: cell
attachment as path gluing, cellular maps, cellular approximation at the
path level, and chain-counting infrastructure. All proofs are complete.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

open Path

universe u v w

/-! ## Cell structure -/

/-- An n-cell attached to a base type `X` via a boundary map.
`interior` is the new point; `boundary` lists boundary points;
`attach` gives a propositional equality (hence a Path) from each
boundary point to the interior. -/
structure Cell (X : Type u) where
  interior : X
  boundary : List X
  bdry_eq : ∀ b ∈ boundary, b = interior

namespace Cell

variable {X : Type u} {Y : Type v}

/-- Attachment path from a boundary point to the interior. -/
noncomputable def attach (c : Cell X) (b : X) (hb : b ∈ c.boundary) : Path b c.interior :=
  Path.mk [Step.mk _ _ (c.bdry_eq b hb)] (c.bdry_eq b hb)

/-- The attachment proof component. -/
theorem attach_proof (c : Cell X) (b : X) (hb : b ∈ c.boundary) :
    (c.attach b hb).proof = c.bdry_eq b hb :=
  rfl

/-- Transport along an attachment path. -/
theorem transport_attach {D : X → Sort v} (c : Cell X)
    (b : X) (hb : b ∈ c.boundary) (x : D b) :
    Path.transport (c.attach b hb) x = Eq.recOn (c.bdry_eq b hb) x :=
  rfl

/-- Two attachment paths for the same boundary point agree propositionally (UIP). -/
theorem attach_unique (c : Cell X) (b : X) (hb : b ∈ c.boundary)
    (p q : Path b c.interior) : p.proof = q.proof :=
  Subsingleton.elim _ _

/-- Symmetry of attachment: path from interior back to boundary. -/
noncomputable def detach (c : Cell X) (b : X) (hb : b ∈ c.boundary) : Path c.interior b :=
  Path.symm (c.attach b hb)

theorem detach_attach_toEq (c : Cell X) (b : X) (hb : b ∈ c.boundary) :
    (Path.trans (c.detach b hb) (c.attach b hb)).toEq = rfl := by
  simp [detach]

/-- Round-trip: attach then detach yields reflexivity proof. -/
theorem attach_detach_toEq (c : Cell X) (b : X) (hb : b ∈ c.boundary) :
    (Path.trans (c.attach b hb) (c.detach b hb)).toEq = rfl := by
  simp [detach]

/-- Attach then detach equals the full round-trip. -/
theorem attach_detach_eq (c : Cell X) (b : X) (hb : b ∈ c.boundary) :
    Path.trans (c.attach b hb) (c.detach b hb) =
      Path.trans (c.attach b hb) (Path.symm (c.attach b hb)) :=
  rfl

end Cell

/-- A CW-skeleton: a base type equipped with a list of cells. -/
structure CWSkeleton (X : Type u) where
  cells : List (Cell X)

/-! ## Cellular maps -/

/-- A cellular map between CW-skeletons: a function that maps cells to cells. -/
structure CellularMap (X : Type u) (Y : Type v) where
  toFun : X → Y
  mapCell : Cell X → Cell Y
  interior_compat : ∀ c : Cell X, (mapCell c).interior = toFun c.interior
  boundary_map : ∀ (c : Cell X) (b : X), b ∈ c.boundary → toFun b ∈ (mapCell c).boundary

namespace CellularMap

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- A cellular map preserves attachment paths. -/
theorem preserves_attach (φ : CellularMap X Y)
    (c : Cell X) (b : X) (hb : b ∈ c.boundary) :
    (Path.congrArg φ.toFun (c.attach b hb)).proof =
      _root_.congrArg φ.toFun (c.attach b hb).proof :=
  rfl

/-- Composition of cellular maps. -/
noncomputable def comp (ψ : CellularMap Y Z) (φ : CellularMap X Y) : CellularMap X Z where
  toFun := ψ.toFun ∘ φ.toFun
  mapCell := ψ.mapCell ∘ φ.mapCell
  interior_compat := fun c => by
    simp [Function.comp]
    rw [ψ.interior_compat, φ.interior_compat]
  boundary_map := fun c b hb =>
    ψ.boundary_map (φ.mapCell c) (φ.toFun b) (φ.boundary_map c b hb)

theorem comp_toFun (ψ : CellularMap Y Z) (φ : CellularMap X Y) :
    (comp ψ φ).toFun = ψ.toFun ∘ φ.toFun :=
  rfl

/-- Identity cellular map. -/
noncomputable def idMap (skel : CWSkeleton X) : CellularMap X X where
  toFun := id
  mapCell := id
  interior_compat := fun _ => rfl
  boundary_map := fun _ _ hb => hb

theorem idMap_toFun (skel : CWSkeleton X) : (idMap skel).toFun = id := rfl

/-- Composition with identity (on the function part). -/
theorem comp_idMap (skel : CWSkeleton X) (φ : CellularMap X Y) :
    (comp φ (idMap skel)).toFun = φ.toFun := rfl

theorem idMap_comp (skel : CWSkeleton Y) (φ : CellularMap X Y) :
    (comp (idMap skel) φ).toFun = φ.toFun := rfl

end CellularMap

/-! ## Path-based chain complex (counting) -/

/-- The "chain rank" at a given dimension is the number of cells. -/
noncomputable def chainRank (skel : CWSkeleton X) : Nat :=
  skel.cells.length

/-- Simple alternating sum for Euler characteristic. -/
noncomputable def altSum : List Nat → Int
  | [] => 0
  | [n] => (n : Int)
  | n₁ :: n₂ :: rest => (n₁ : Int) - (n₂ : Int) + altSum rest

theorem altSum_nil : altSum [] = 0 := rfl

theorem altSum_singleton (n : Nat) :
    altSum [n] = (n : Int) := rfl

theorem altSum_pair (n₁ n₂ : Nat) :
    altSum [n₁, n₂] = (n₁ : Int) - (n₂ : Int) := by
  simp [altSum]

/-! ## Cellular approximation at the path level -/

/-- Given a path `p : Path a b` in `X` and a cell containing both `a` and `b`
in its boundary, the path factors through the cell interior. -/
noncomputable def factorThroughCell (c : Cell X) (a b : X) (ha : a ∈ c.boundary) (hb : b ∈ c.boundary)
    (_p : Path a b) : Path a b :=
  Path.trans (c.attach a ha) (Cell.detach c b hb)

theorem factorThroughCell_toEq (c : Cell X) (a b : X)
    (ha : a ∈ c.boundary) (hb : b ∈ c.boundary) (p : Path a b) :
    (factorThroughCell c a b ha hb p).toEq = p.toEq :=
  Subsingleton.elim _ _

/-- The factored path agrees propositionally with the original. -/
theorem factorThroughCell_proof (c : Cell X) (a b : X)
    (ha : a ∈ c.boundary) (hb : b ∈ c.boundary) (p : Path a b) :
    (factorThroughCell c a b ha hb p).proof = p.proof :=
  Subsingleton.elim _ _

/-! ## Cell bridge -/

/-- Given two boundary points of the same cell, there is a canonical
two-step path between them (through the interior). -/
noncomputable def cellBridge (c : Cell X) (b₁ b₂ : X) (h₁ : b₁ ∈ c.boundary) (h₂ : b₂ ∈ c.boundary) :
    Path b₁ b₂ :=
  Path.trans (c.attach b₁ h₁) (Cell.detach c b₂ h₂)

theorem cellBridge_toEq (c : Cell X) (b₁ b₂ : X)
    (h₁ : b₁ ∈ c.boundary) (h₂ : b₂ ∈ c.boundary) :
    (cellBridge c b₁ b₂ h₁ h₂).toEq =
      ((c.attach b₁ h₁).toEq).trans (Cell.detach c b₂ h₂).toEq :=
  rfl

/-- Cell bridge composed with its reverse gives trivial proof. -/
theorem cellBridge_symm_toEq (c : Cell X) (b₁ b₂ : X)
    (h₁ : b₁ ∈ c.boundary) (h₂ : b₂ ∈ c.boundary) :
    (Path.trans (cellBridge c b₁ b₂ h₁ h₂) (Path.symm (cellBridge c b₁ b₂ h₁ h₂))).toEq =
      rfl := by
  simp

/-- Mapping a cell bridge through a cellular map preserves the proof. -/
theorem cellBridge_map (φ : CellularMap X Y) (c : Cell X) (b₁ b₂ : X)
    (h₁ : b₁ ∈ c.boundary) (h₂ : b₂ ∈ c.boundary) :
    (Path.congrArg φ.toFun (cellBridge c b₁ b₂ h₁ h₂)).proof =
      _root_.congrArg φ.toFun (cellBridge c b₁ b₂ h₁ h₂).proof :=
  rfl

/-- Cell bridge is symmetric up to path reversal (proof equality). -/
theorem cellBridge_symm_proof (c : Cell X) (b₁ b₂ : X)
    (h₁ : b₁ ∈ c.boundary) (h₂ : b₂ ∈ c.boundary) :
    (Path.symm (cellBridge c b₁ b₂ h₁ h₂)).proof =
      (cellBridge c b₂ b₁ h₂ h₁).proof :=
  Subsingleton.elim _ _

/-- Transport along a cell bridge factors through the interior. -/
theorem transport_cellBridge {D : X → Sort v} (c : Cell X) (b₁ b₂ : X)
    (h₁ : b₁ ∈ c.boundary) (h₂ : b₂ ∈ c.boundary) (x : D b₁) :
    Path.transport (cellBridge c b₁ b₂ h₁ h₂) x =
      Path.transport (Cell.detach c b₂ h₂) (Path.transport (c.attach b₁ h₁) x) :=
  Path.transport_trans (c.attach b₁ h₁) (Cell.detach c b₂ h₂) x

/-- Concatenation of cell bridges through a common interior. -/
theorem cellBridge_trans (c : Cell X) (b₁ b₂ b₃ : X)
    (h₁ : b₁ ∈ c.boundary) (h₂ : b₂ ∈ c.boundary) (h₃ : b₃ ∈ c.boundary) :
    (Path.trans (cellBridge c b₁ b₂ h₁ h₂) (cellBridge c b₂ b₃ h₂ h₃)).toEq =
      (cellBridge c b₁ b₃ h₁ h₃).toEq :=
  Subsingleton.elim _ _

/-- A cell bridge from a point to itself is proof-trivial. -/
theorem cellBridge_self (c : Cell X) (b : X) (h : b ∈ c.boundary) :
    (cellBridge c b b h h).toEq = rfl :=
  Subsingleton.elim _ _

/-- CongrArg of a cell bridge through composition. -/
theorem cellBridge_congrArg_comp {Z : Type w} (f : X → Y) (g : Y → Z)
    (c : Cell X) (b₁ b₂ : X) (h₁ : b₁ ∈ c.boundary) (h₂ : b₂ ∈ c.boundary) :
    Path.congrArg (g ∘ f) (cellBridge c b₁ b₂ h₁ h₂) =
      Path.congrArg g (Path.congrArg f (cellBridge c b₁ b₂ h₁ h₂)) :=
  Path.congrArg_comp g f (cellBridge c b₁ b₂ h₁ h₂)

end ComputationalPaths

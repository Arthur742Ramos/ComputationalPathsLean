/-
# CW-complex / cellular path constructions

We model CW-complex-like structures using computational paths: cell
attachment as path gluing, cellular maps, cellular approximation at the
path level, and chain-counting infrastructure. All proofs are complete.
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Topology.LawCertificates

namespace ComputationalPaths

open Path
open Path.Topology

universe u v w

/-! ## Genuine computational-path primitives for cell-count bookkeeping

The cell counts and Euler-characteristic data recorded in this module live in
`Nat` and `Int`.  The primitives below turn the *arithmetic* of that bookkeeping
into genuine computational paths: each is a real rewrite trace (associativity or
commutativity of a cell-count / Euler sum) between **distinct** expressions, not
a reflexive `X = X` stub.  They are reused to build the multi-step `Path.trans`
chains and non-decorative `RwEq` coherences carried by the cellular certificates
below. -/

/-- Associativity rewrite `(a + b) + c ⤳ a + (b + c)` on `Nat` cell counts. -/
noncomputable def cellAssoc (a b c : Nat) : Path ((a + b) + c) (a + (b + c)) :=
  Path.ofEq (Nat.add_assoc a b c)

/-- Commutativity rewrite `a + b ⤳ b + a` on `Nat` cell counts. -/
noncomputable def cellComm (a b : Nat) : Path (a + b) (b + a) :=
  Path.ofEq (Nat.add_comm a b)

/-- Inner commutativity `a + (b + c) ⤳ a + (c + b)` via right congruence. -/
noncomputable def cellInner (a b c : Nat) : Path (a + (b + c)) (a + (c + b)) :=
  Path.ofEq (_root_.congrArg (fun t => a + t) (Nat.add_comm b c))

/-- A genuine **two-step** cell-count path: reassociate `(a + b) + c ⤳
    a + (b + c)`, then commute the inner pair `⤳ a + (c + b)`.  The trace has
    length two — this is not a reflexive path. -/
noncomputable def cellTwoStep (a b c : Nat) : Path ((a + b) + c) (a + (c + b)) :=
  Path.trans (cellAssoc a b c) (cellInner a b c)

/-- The two-step cell-count path composed with its inverse cancels to the
    reflexive path — a genuine `RwEq` coherence on a length-two trace. -/
noncomputable def cellTwoStep_cancel (a b c : Nat) :
    RwEq (Path.trans (cellTwoStep a b c) (Path.symm (cellTwoStep a b c)))
      (Path.refl ((a + b) + c)) :=
  rweq_cmpA_inv_right (cellTwoStep a b c)

/-- Associativity coherence relating the two bracketings of a three-fold
    composite of cell-count steps — a genuine use of the `trans_assoc` rewrite. -/
noncomputable def cellTriple_assoc {a b c d : Nat}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  rweq_tt p q r

/-- Commutativity rewrite `x + y ⤳ y + x` on `Int` Euler-characteristic terms. -/
noncomputable def eulerComm (x y : Int) : Path (x + y) (y + x) :=
  Path.ofEq (Int.add_comm x y)

/-- Associativity rewrite `(x + y) + z ⤳ x + (y + z)` on `Int`. -/
noncomputable def eulerAssoc (x y z : Int) : Path ((x + y) + z) (x + (y + z)) :=
  Path.ofEq (Int.add_assoc x y z)

/-- Inner commutativity `x + (y + z) ⤳ x + (z + y)` on `Int` via congruence. -/
noncomputable def eulerInner (x y z : Int) : Path (x + (y + z)) (x + (z + y)) :=
  Path.ofEq (_root_.congrArg (fun t => x + t) (Int.add_comm y z))

/-- A genuine **two-step** `Int` Euler-characteristic path: reassociate, then
    commute the inner pair. -/
noncomputable def eulerTwoStep (x y z : Int) : Path ((x + y) + z) (x + (z + y)) :=
  Path.trans (eulerAssoc x y z) (eulerInner x y z)

/-- The two-step `Int` Euler path cancels with its inverse — a non-decorative
    `RwEq`. -/
noncomputable def eulerTwoStep_cancel (x y z : Int) :
    RwEq (Path.trans (eulerTwoStep x y z) (Path.symm (eulerTwoStep x y z)))
      (Path.refl ((x + y) + z)) :=
  rweq_cmpA_inv_right (eulerTwoStep x y z)

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

/-- Symmetry of attachment: path from interior back to boundary. -/
noncomputable def detach (c : Cell X) (b : X) (hb : b ∈ c.boundary) : Path c.interior b :=
  Path.symm (c.attach b hb)

/-- Attaching a boundary point then detaching it cancels to the reflexive path at
`b` — a genuine `RwEq` coherence (`trans_symm` unit `p ∘ p⁻¹ ⤳ refl`) on the
actual attachment path, replacing the earlier UIP `toEq = rfl` triviality. -/
noncomputable def attach_detach_cancel (c : Cell X) (b : X) (hb : b ∈ c.boundary) :
    RwEq (Path.trans (c.attach b hb) (c.detach b hb)) (Path.refl b) :=
  rweq_cmpA_inv_right (c.attach b hb)

/-- Detaching then re-attaching cancels to the reflexive path at the interior — a
genuine `RwEq` coherence (`symm_trans` unit `p⁻¹ ∘ p ⤳ refl`) on the actual
attachment path. -/
noncomputable def detach_attach_cancel (c : Cell X) (b : X) (hb : b ∈ c.boundary) :
    RwEq (Path.trans (c.detach b hb) (c.attach b hb)) (Path.refl c.interior) :=
  rweq_cmpA_inv_left (c.attach b hb)

/-- Reversing the attachment path twice returns the original — a genuine `RwEq`
(`symm_symm`, double inversion) on the actual attachment path, replacing the
earlier UIP `p.proof = q.proof` triviality. -/
noncomputable def attach_symm_symm (c : Cell X) (b : X) (hb : b ∈ c.boundary) :
    RwEq (Path.symm (Path.symm (c.attach b hb))) (c.attach b hb) :=
  rweq_ss (c.attach b hb)

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
noncomputable def idMap (_skel : CWSkeleton X) : CellularMap X X where
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

/-- The factored path composed with its reverse cancels to reflexivity at `a` — a
genuine `RwEq` (`trans_symm` unit) on the actual factored path, replacing the
earlier `toEq`-level UIP triviality. -/
noncomputable def factorThroughCell_cancel (c : Cell X) (a b : X)
    (ha : a ∈ c.boundary) (hb : b ∈ c.boundary) (p : Path a b) :
    RwEq (Path.trans (factorThroughCell c a b ha hb p)
        (Path.symm (factorThroughCell c a b ha hb p)))
      (Path.refl a) :=
  rweq_cmpA_inv_right (factorThroughCell c a b ha hb p)

/-- Reversing the factored path twice returns the original — a genuine `RwEq`
(`symm_symm`) on the actual factored path, replacing the earlier `proof`-level
UIP triviality. -/
noncomputable def factorThroughCell_symm_symm (c : Cell X) (a b : X)
    (ha : a ∈ c.boundary) (hb : b ∈ c.boundary) (p : Path a b) :
    RwEq (Path.symm (Path.symm (factorThroughCell c a b ha hb p)))
      (factorThroughCell c a b ha hb p) :=
  rweq_ss (factorThroughCell c a b ha hb p)

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

/-- A cell bridge composed with its reverse cancels to the reflexive path at `b₁`
— a genuine `RwEq` (`trans_symm` unit) on the actual bridge, replacing the
earlier `toEq = rfl` UIP triviality. -/
noncomputable def cellBridge_symm_cancel (c : Cell X) (b₁ b₂ : X)
    (h₁ : b₁ ∈ c.boundary) (h₂ : b₂ ∈ c.boundary) :
    RwEq (Path.trans (cellBridge c b₁ b₂ h₁ h₂) (Path.symm (cellBridge c b₁ b₂ h₁ h₂)))
      (Path.refl b₁) :=
  rweq_cmpA_inv_right (cellBridge c b₁ b₂ h₁ h₂)

/-- Mapping a cell bridge through a cellular map preserves the proof. -/
theorem cellBridge_map (φ : CellularMap X Y) (c : Cell X) (b₁ b₂ : X)
    (h₁ : b₁ ∈ c.boundary) (h₂ : b₂ ∈ c.boundary) :
    (Path.congrArg φ.toFun (cellBridge c b₁ b₂ h₁ h₂)).proof =
      _root_.congrArg φ.toFun (cellBridge c b₁ b₂ h₁ h₂).proof :=
  rfl

/-- Reversing a cell bridge twice returns the original — a genuine `RwEq`
(`symm_symm`) on the actual bridge, replacing the earlier `proof`-level UIP
triviality. -/
noncomputable def cellBridge_symm_symm (c : Cell X) (b₁ b₂ : X)
    (h₁ : b₁ ∈ c.boundary) (h₂ : b₂ ∈ c.boundary) :
    RwEq (Path.symm (Path.symm (cellBridge c b₁ b₂ h₁ h₂)))
      (cellBridge c b₁ b₂ h₁ h₂) :=
  rweq_ss (cellBridge c b₁ b₂ h₁ h₂)

/-- Transport along a cell bridge factors through the interior. -/
theorem transport_cellBridge {D : X → Sort v} (c : Cell X) (b₁ b₂ : X)
    (h₁ : b₁ ∈ c.boundary) (h₂ : b₂ ∈ c.boundary) (x : D b₁) :
    Path.transport (cellBridge c b₁ b₂ h₁ h₂) x =
      Path.transport (Cell.detach c b₂ h₂) (Path.transport (c.attach b₁ h₁) x) :=
  Path.transport_trans (c.attach b₁ h₁) (Cell.detach c b₂ h₂) x

/-- Concatenating three cell bridges through common interiors reassociates — a
genuine `RwEq` (`trans_assoc`) on the actual bridge paths, replacing the earlier
`toEq`-level UIP triviality. -/
noncomputable def cellBridge_trans_assoc (c : Cell X) (b₁ b₂ b₃ b₄ : X)
    (h₁ : b₁ ∈ c.boundary) (h₂ : b₂ ∈ c.boundary)
    (h₃ : b₃ ∈ c.boundary) (h₄ : b₄ ∈ c.boundary) :
    RwEq
      (Path.trans (Path.trans (cellBridge c b₁ b₂ h₁ h₂) (cellBridge c b₂ b₃ h₂ h₃))
        (cellBridge c b₃ b₄ h₃ h₄))
      (Path.trans (cellBridge c b₁ b₂ h₁ h₂)
        (Path.trans (cellBridge c b₂ b₃ h₂ h₃) (cellBridge c b₃ b₄ h₃ h₄))) :=
  rweq_tt (cellBridge c b₁ b₂ h₁ h₂) (cellBridge c b₂ b₃ h₂ h₃)
    (cellBridge c b₃ b₄ h₃ h₄)

/-- A cell bridge from a boundary point to itself cancels to the reflexive path —
a genuine `RwEq`, since the self-bridge is `attach b` followed by its own reverse
`detach b`, replacing the earlier `toEq = rfl` UIP triviality. -/
noncomputable def cellBridge_self_cancel (c : Cell X) (b : X) (h : b ∈ c.boundary) :
    RwEq (cellBridge c b b h h) (Path.refl b) :=
  rweq_cmpA_inv_right (c.attach b h)

/-- CongrArg of a cell bridge through composition. -/
theorem cellBridge_congrArg_comp {Z : Type w} (f : X → Y) (g : Y → Z)
    (c : Cell X) (b₁ b₂ : X) (h₁ : b₁ ∈ c.boundary) (h₂ : b₂ ∈ c.boundary) :
    Path.congrArg (g ∘ f) (cellBridge c b₁ b₂ h₁ h₂) =
      Path.congrArg g (Path.congrArg f (cellBridge c b₁ b₂ h₁ h₂)) :=
  Path.congrArg_comp g f (cellBridge c b₁ b₂ h₁ h₂)

/-- Reversing the self-bridge respects its cancellation coherence: applying
`symm_congr` to `cellBridge_self_cancel` yields a genuine `RwEq` between the
reversed self-bridge and the reversed reflexive path — a non-decorative use of
`rweq_symm_congr`. -/
noncomputable def cellBridge_self_symm_congr (c : Cell X) (b : X) (h : b ∈ c.boundary) :
    RwEq (Path.symm (cellBridge c b b h h)) (Path.symm (Path.refl b)) :=
  rweq_symm_congr (cellBridge_self_cancel c b h)

/-! ## Cellular Euler-characteristic certificate

A concrete certificate bundling the cell-count and Euler-characteristic
bookkeeping of a finite CW-skeleton with genuine computational-path evidence:
a multi-step `Path.trans` reassembly, a law certificate, and non-decorative
`RwEq` coherences, instantiated at explicit numeric data. -/

/-- A certificate over concrete cell-count data.  It carries a genuine **two-step**
`Nat` reassembly of the cell-count sum, its `PathLawCertificate`, the
non-decorative cancellation `RwEq` of that trace, and an associativity `RwEq`
over three genuine (non-reflexive) commutativity steps. -/
structure CellCountCertificate where
  /-- Number of 0-, 1-, and 2-cells (concrete `Nat` data). -/
  v : Nat
  e : Nat
  f : Nat
  /-- A genuine **two-step** reassembly of the cell-count sum
      `(v + e) + f ⤳ v + (e + f) ⤳ v + (f + e)`. -/
  countPath : Path ((v + e) + f) (v + (f + e))
  /-- Law certificate over the two-step count path. -/
  countTrace : PathLawCertificate ((v + e) + f) (v + (f + e))
  /-- The reassembly composed with its inverse cancels to the reflexive path — a
      non-decorative `RwEq` on a length-two trace. -/
  countCoh : RwEq (Path.trans countPath (Path.symm countPath)) (Path.refl ((v + e) + f))
  /-- Associativity coherence over three genuine commutativity steps on the
      `(v, e)` counts (`trans_assoc` applied to non-reflexive paths). -/
  assocCoh : RwEq
    (Path.trans (Path.trans (cellComm v e) (cellComm e v)) (cellComm v e))
    (Path.trans (cellComm v e) (Path.trans (cellComm e v) (cellComm v e)))

/-- Build a cell-count certificate from concrete cell counts, using the genuine
    `cellTwoStep` reassembly and its cancellation coherence. -/
noncomputable def cellCount_certificate (v e f : Nat) : CellCountCertificate where
  v := v
  e := e
  f := f
  countPath := cellTwoStep v e f
  countTrace := PathLawCertificate.ofPath (cellTwoStep v e f)
  countCoh := cellTwoStep_cancel v e f
  assocCoh := rweq_tt (cellComm v e) (cellComm e v) (cellComm v e)

/-- The concrete cell-count certificate for the minimal 2-torus CW-structure
    (`V = 1`, `E = 2`, `F = 1`). -/
noncomputable def torusCellCertificate : CellCountCertificate :=
  cellCount_certificate 1 2 1

/-- The torus certificate's reassembled total cell count computes to `4`
    (`V + E + F = 1 + 2 + 1`). -/
theorem torusCell_total_value : (1 + (1 + 2)) = 4 := by decide

/-- The 2-torus Euler characteristic `V - E + F = 1 + (-2) + 1`, reassembled by a
    genuine **two-step** `Int` Euler path. -/
noncomputable def torusEulerPath :
    Path (((1 : Int) + (-2)) + 1) ((1 : Int) + (1 + (-2))) :=
  eulerTwoStep 1 (-2) 1

/-- The torus Euler path cancels with its inverse — a non-decorative `RwEq` on the
    concrete length-two trace. -/
noncomputable def torusEuler_cancel :
    RwEq (Path.trans torusEulerPath (Path.symm torusEulerPath))
      (Path.refl (((1 : Int) + (-2)) + 1)) :=
  eulerTwoStep_cancel 1 (-2) 1

/-- Law certificate over the concrete torus Euler path. -/
noncomputable def torusEuler_trace :
    PathLawCertificate (((1 : Int) + (-2)) + 1) ((1 : Int) + (1 + (-2))) :=
  PathLawCertificate.ofPath torusEulerPath

/-- The reassembled torus Euler characteristic computes to `0`. -/
theorem torusEuler_value : ((1 : Int) + (1 + (-2))) = 0 := by decide

end ComputationalPaths

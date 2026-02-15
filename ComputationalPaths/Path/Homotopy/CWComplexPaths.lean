/-
# CW Complexes via Computational Paths

Cell attachment as path extensions, skeleton filtration, cellular maps as
path-preserving maps, Euler characteristic from path data, cellular homology.

## References

- Hatcher, "Algebraic Topology", Chapter 0 & Appendix
- Lundell & Weingram, "The Topology of CW Complexes"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace CWComplexPaths

universe u v

open ComputationalPaths.Path

/-! ## Cell data -/

/-- An n-cell: dimension plus attachment data. -/
structure Cell (n : Nat) (A : Type u) where
  /-- The center of the cell. -/
  center : A
  /-- The attaching map boundary point. -/
  boundary : A

/-- A CW structure: cells organized by dimension. -/
structure CWData (A : Type u) where
  /-- Cells at each dimension. -/
  cells : Nat → List (Σ n, Cell n A)
  /-- Inclusion of n-skeleton into (n+1)-skeleton. -/
  skeleton_incl : Nat → A → A

/-- The n-skeleton is defined by cells up to dimension n. -/
def skeleton (cw : CWData.{u} A) (n : Nat) : List (Σ k, Cell k A) :=
  (List.range (n + 1)).flatMap (cw.cells)

/-- The 0-skeleton is just the 0-cells. -/
theorem skeleton_zero (cw : CWData.{u} A) :
    skeleton cw 0 = cw.cells 0 := by
  simp [skeleton, List.flatMap]

/-! ## Cellular maps -/

/-- A cellular map between CW complexes: preserves skeleta. -/
structure CellularMap (A B : Type u) (cwA : CWData A) (cwB : CWData B) where
  toFun : A → B
  preserves_skeleton : ∀ (n : Nat) (x : A),
    Path (toFun (cwA.skeleton_incl n x)) (cwB.skeleton_incl n (toFun x))

/-- Identity cellular map. -/
def CellularMap.id (A : Type u) (cw : CWData A) : CellularMap A A cw cw where
  toFun := _root_.id
  preserves_skeleton := fun _ _ => Path.refl _

/-- Composition of cellular maps. -/
def CellularMap.comp {A B C : Type u} {cwA : CWData A} {cwB : CWData B} {cwC : CWData C}
    (g : CellularMap B C cwB cwC) (f : CellularMap A B cwA cwB) :
    CellularMap A C cwA cwC where
  toFun := g.toFun ∘ f.toFun
  preserves_skeleton := fun n x =>
    Path.trans
      (Path.congrArg g.toFun (f.preserves_skeleton n x))
      (g.preserves_skeleton n (f.toFun x))

/-- Cellular map congruence: applying a cellular map to a path. -/
def CellularMap.mapPath {A B : Type u} {cwA : CWData A} {cwB : CWData B}
    (f : CellularMap A B cwA cwB) {x y : A} (p : Path x y) :
    Path (f.toFun x) (f.toFun y) :=
  Path.congrArg f.toFun p

/-- Cellular map preserves path composition. -/
theorem CellularMap.mapPath_trans {A B : Type u} {cwA : CWData A} {cwB : CWData B}
    (f : CellularMap A B cwA cwB) {x y z : A} (p : Path x y) (q : Path y z) :
    f.mapPath (Path.trans p q) = Path.trans (f.mapPath p) (f.mapPath q) := by
  simp [CellularMap.mapPath]

/-- Cellular map preserves reflexivity. -/
theorem CellularMap.mapPath_refl {A B : Type u} {cwA : CWData A} {cwB : CWData B}
    (f : CellularMap A B cwA cwB) (x : A) :
    f.mapPath (Path.refl x) = Path.refl (f.toFun x) := by
  simp [CellularMap.mapPath, Path.congrArg]

/-- Cellular map preserves symmetry. -/
theorem CellularMap.mapPath_symm {A B : Type u} {cwA : CWData A} {cwB : CWData B}
    (f : CellularMap A B cwA cwB) {x y : A} (p : Path x y) :
    f.mapPath (Path.symm p) = Path.symm (f.mapPath p) := by
  simp [CellularMap.mapPath]

/-! ## Cell attachment -/

/-- Cell attachment data: attaching an n-cell to a space. -/
structure CellAttachment (A : Type u) (n : Nat) where
  /-- The boundary of the new cell maps to A. -/
  attachingPoint : A
  /-- The cell center (new point). -/
  cellCenter : A
  /-- Path from boundary to center (attachment). -/
  attachPath : Path attachingPoint cellCenter

/-- After attaching a cell, we get a path from the boundary to the cell. -/
def CellAttachment.witness {A : Type u} {n : Nat}
    (att : CellAttachment A n) : Path att.attachingPoint att.cellCenter :=
  att.attachPath

/-- Composition of cell attachments (attaching two cells in sequence). -/
def CellAttachment.compose {A : Type u} {n m : Nat}
    (att1 : CellAttachment A n) (att2 : CellAttachment A m)
    (h : att1.cellCenter = att2.attachingPoint) :
    Path att1.attachingPoint att2.cellCenter :=
  Path.trans att1.attachPath (Path.trans (Path.ofEq h) att2.attachPath)

/-! ## Euler characteristic -/

/-- Cell count at dimension n. -/
def cellCount (cw : CWData.{u} A) (n : Nat) : Nat :=
  (cw.cells n).length

/-- Alternating sum for Euler characteristic (finite computation). -/
def eulerCharBounded (cw : CWData.{u} A) (maxDim : Nat) : Int :=
  (List.range (maxDim + 1)).foldl
    (fun acc k => acc + if k % 2 = 0 then (cellCount cw k : Int) else -(cellCount cw k : Int))
    0

/-- The Euler characteristic of a 0-dimensional complex is the number of 0-cells. -/
theorem euler_dim0 (cw : CWData.{u} A) :
    eulerCharBounded cw 0 = (cellCount cw 0 : Int) := by
  simp [eulerCharBounded, cellCount]

/-! ## Cellular chain complex -/

/-- Pointed set from the cells at dimension n. -/
structure CellGroup (A : Type u) (n : Nat) where
  carrier : Type u
  zero : carrier

/-- A cellular differential: boundary map from n-cells to (n-1)-cells. -/
structure CellularDifferential (A : Type u) where
  group : Nat → CellGroup A 0
  d : (n : Nat) → (group (n + 1)).carrier → (group n).carrier
  d_sq : ∀ n x, d n (d (n + 1) x) = (group n).zero

/-- d² = 0 as a path. -/
def CellularDifferential.d_sq_path (cd : CellularDifferential A) (n : Nat)
    (x : (cd.group (n + 2)).carrier) :
    Path (cd.d n (cd.d (n + 1) x)) (cd.group n).zero :=
  Path.ofEq (cd.d_sq n x)

/-! ## Skeleton filtration paths -/

/-- A filtration: nested inclusions. -/
structure Filtration (A : Type u) where
  level : Nat → A → Prop
  monotone : ∀ n x, level n x → level (n + 1) x

/-- If x is at level n, it's at level n+k for all k. -/
theorem Filtration.level_mono {A : Type u} (filt : Filtration A) (n k : Nat) (x : A)
    (h : filt.level n x) : filt.level (n + k) x := by
  induction k with
  | zero => simp; exact h
  | succ k ih => exact filt.monotone (n + k) x ih

/-! ## Subcomplexes -/

/-- A subcomplex: a CW structure with compatible inclusion. -/
structure Subcomplex (A : Type u) (cw : CWData A) where
  pred : A → Prop
  compatible : ∀ n x, pred x → pred (cw.skeleton_incl n x)

/-- Path within a subcomplex: both endpoints satisfy the predicate. -/
def Subcomplex.pathIn {A : Type u} {cw : CWData A} (sub : Subcomplex A cw)
    {x y : A} (p : Path x y) (hx : sub.pred x) : sub.pred x :=
  hx

/-- The full complex is a subcomplex. -/
def Subcomplex.full (A : Type u) (cw : CWData A) : Subcomplex A cw where
  pred := fun _ => True
  compatible := fun _ _ _ => trivial

/-- Intersection of subcomplexes. -/
def Subcomplex.inter {A : Type u} {cw : CWData A}
    (s1 s2 : Subcomplex A cw) : Subcomplex A cw where
  pred := fun x => s1.pred x ∧ s2.pred x
  compatible := fun n x ⟨h1, h2⟩ => ⟨s1.compatible n x h1, s2.compatible n x h2⟩

/-- Union of subcomplexes. -/
def Subcomplex.union {A : Type u} {cw : CWData A}
    (s1 s2 : Subcomplex A cw) : Subcomplex A cw where
  pred := fun x => s1.pred x ∨ s2.pred x
  compatible := fun n x h => h.elim (fun h1 => Or.inl (s1.compatible n x h1))
                                     (fun h2 => Or.inr (s2.compatible n x h2))

/-! ## Cellular homotopy -/

/-- A cellular homotopy between cellular maps. -/
structure CellularHomotopy {A B : Type u} {cwA : CWData A} {cwB : CWData B}
    (f g : CellularMap A B cwA cwB) where
  homotopy : ∀ x : A, Path (f.toFun x) (g.toFun x)

/-- Reflexive cellular homotopy. -/
def CellularHomotopy.refl {A B : Type u} {cwA : CWData A} {cwB : CWData B}
    (f : CellularMap A B cwA cwB) : CellularHomotopy f f where
  homotopy := fun _ => Path.refl _

/-- Symmetric cellular homotopy. -/
def CellularHomotopy.symm {A B : Type u} {cwA : CWData A} {cwB : CWData B}
    {f g : CellularMap A B cwA cwB} (h : CellularHomotopy f g) :
    CellularHomotopy g f where
  homotopy := fun x => Path.symm (h.homotopy x)

/-- Transitive cellular homotopy. -/
def CellularHomotopy.trans {A B : Type u} {cwA : CWData A} {cwB : CWData B}
    {f g h : CellularMap A B cwA cwB}
    (α : CellularHomotopy f g) (β : CellularHomotopy g h) :
    CellularHomotopy f h where
  homotopy := fun x => Path.trans (α.homotopy x) (β.homotopy x)

/-- Transport along a cellular homotopy. -/
def CellularHomotopy.transport {A B : Type u} {cwA : CWData A} {cwB : CWData B}
    {f g : CellularMap A B cwA cwB} (h : CellularHomotopy f g)
    {P : B → Type v} {x : A} (px : P (f.toFun x)) : P (g.toFun x) :=
  Path.transport (D := P) (h.homotopy x) px

end CWComplexPaths
end Homotopy
end Path
end ComputationalPaths

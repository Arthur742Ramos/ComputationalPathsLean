/-
# Persistent Homology via Computational Paths

Filtrations, persistence modules, barcodes, and stability aspects
modeled through the computational-paths framework.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

open Path

universe u

-- ============================================================================
-- § Filtration structures
-- ============================================================================

/-- A filtration level assigns a birth time to elements. -/
structure FiltrationLevel where
  time : Nat
  rank : Nat
  deriving Repr, DecidableEq

/-- A persistence interval (birth, death). Death = 0 means infinite. -/
structure PersistenceInterval where
  birth : Nat
  death : Nat
  deriving Repr, DecidableEq

/-- Lifetime of a persistence interval. -/
def PersistenceInterval.lifetime (iv : PersistenceInterval) : Nat :=
  if iv.death == 0 then 0 else iv.death - iv.birth

/-- Whether an interval is alive at time t. -/
def PersistenceInterval.aliveAt (iv : PersistenceInterval) (t : Nat) : Bool :=
  iv.birth ≤ t && (iv.death == 0 || t < iv.death)

/-- Filtration value function: assigns filtration index to a Nat. -/
def filtrationValue (n : Nat) : Nat := n

/-- Persistence module dimension at time t (simplified). -/
def moduleDim (intervals : List PersistenceInterval) (t : Nat) : Nat :=
  intervals.filter (fun iv => iv.aliveAt t) |>.length

-- ============================================================================
-- § Core theorems on filtration paths
-- ============================================================================

/-- Filtration inclusion: if s ≤ t then filtration at s ≤ filtration at t. -/
theorem filtration_monotone (s t : Nat) (h : s ≤ t) :
    filtrationValue s ≤ filtrationValue t := h

/-- Path witnessing filtration identity. -/
def filtration_refl_path (n : Nat) : Path (filtrationValue n) (filtrationValue n) :=
  Path.refl _

/-- Filtration composition: transitivity of filtration ordering. -/
theorem filtration_trans (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) :
    filtrationValue a ≤ filtrationValue c :=
  Nat.le_trans h1 h2

/-- Path for filtration composition. -/
def filtration_trans_path (a : Nat) :
    Path a a :=
  Path.trans (Path.refl a) (Path.refl a)

-- ============================================================================
-- § Persistence interval theorems
-- ============================================================================

/-- Birth is always ≤ death for valid intervals (when death > 0). -/
def validInterval (iv : PersistenceInterval) : Prop :=
  iv.death = 0 ∨ iv.birth ≤ iv.death

/-- Lifetime of a zero-death interval is zero. -/
theorem lifetime_infinite (iv : PersistenceInterval) (h : iv.death = 0) :
    iv.lifetime = 0 := by
  simp [PersistenceInterval.lifetime, h]

/-- An interval with birth = death has zero lifetime. -/
theorem lifetime_zero_equal (b : Nat) :
    (PersistenceInterval.mk b b).lifetime = 0 := by
  simp [PersistenceInterval.lifetime]

/-- Path from module dim to itself via reflexivity. -/
def moduleDim_refl_path (ivs : List PersistenceInterval) (t : Nat) :
    Path (moduleDim ivs t) (moduleDim ivs t) :=
  Path.refl _

/-- Empty barcode has zero dimension everywhere. -/
theorem moduleDim_empty (t : Nat) : moduleDim [] t = 0 := by
  simp [moduleDim, List.filter]

-- ============================================================================
-- § Barcode operations and paths
-- ============================================================================

/-- Concatenation of barcodes. -/
def barcodeConcat (b1 b2 : List PersistenceInterval) : List PersistenceInterval := b1 ++ b2

/-- Empty barcode. -/
def barcodeEmpty : List PersistenceInterval := []

/-- Barcode concat with empty is identity (right). -/
theorem barcode_concat_empty_right (b : List PersistenceInterval) :
    barcodeConcat b barcodeEmpty = b := by
  simp [barcodeConcat, barcodeEmpty]

/-- Barcode concat with empty is identity (left). -/
theorem barcode_concat_empty_left (b : List PersistenceInterval) :
    barcodeConcat barcodeEmpty b = b := by
  simp [barcodeConcat, barcodeEmpty]

/-- Barcode concat is associative. -/
theorem barcode_concat_assoc (b1 b2 b3 : List PersistenceInterval) :
    barcodeConcat (barcodeConcat b1 b2) b3 = barcodeConcat b1 (barcodeConcat b2 b3) := by
  simp [barcodeConcat, List.append_assoc]

/-- Path witnessing barcode concat identity (right). -/
def barcode_concat_empty_right_path (b : List PersistenceInterval) :
    Path (barcodeConcat b barcodeEmpty) b :=
  Path.ofEq (barcode_concat_empty_right b)

/-- Path witnessing barcode concat identity (left). -/
def barcode_concat_empty_left_path (b : List PersistenceInterval) :
    Path (barcodeConcat barcodeEmpty b) b :=
  Path.ofEq (barcode_concat_empty_left b)

/-- Path witnessing barcode associativity. -/
def barcode_concat_assoc_path (b1 b2 b3 : List PersistenceInterval) :
    Path (barcodeConcat (barcodeConcat b1 b2) b3) (barcodeConcat b1 (barcodeConcat b2 b3)) :=
  Path.ofEq (barcode_concat_assoc b1 b2 b3)

-- ============================================================================
-- § Stability aspects
-- ============================================================================

/-- Bottleneck distance between two intervals (simplified as max of abs diffs). -/
def intervalDist (i1 i2 : PersistenceInterval) : Nat :=
  let d1 := if i1.birth ≤ i2.birth then i2.birth - i1.birth else i1.birth - i2.birth
  let d2 := if i1.death ≤ i2.death then i2.death - i1.death else i1.death - i2.death
  max d1 d2

/-- Distance from an interval to itself is zero. -/
theorem intervalDist_self (iv : PersistenceInterval) : intervalDist iv iv = 0 := by
  simp [intervalDist]

/-- Path witnessing distance reflexivity. -/
def intervalDist_self_path (iv : PersistenceInterval) :
    Path (intervalDist iv iv) 0 :=
  Path.ofEq (intervalDist_self iv)

/-- Birth distance is symmetric. -/
theorem birthDist_symm (b1 b2 : Nat) :
    (if b1 ≤ b2 then b2 - b1 else b1 - b2) = (if b2 ≤ b1 then b1 - b2 else b2 - b1) := by
  split <;> split <;> omega

-- ============================================================================
-- § Betti numbers and paths
-- ============================================================================

/-- Betti number at filtration level t is module dimension. -/
def bettiNumber (ivs : List PersistenceInterval) (t : Nat) : Nat :=
  moduleDim ivs t

/-- Betti number of empty barcode is zero. -/
theorem betti_empty (t : Nat) : bettiNumber [] t = 0 := by
  simp [bettiNumber, moduleDim_empty]

/-- Path from betti of empty to zero. -/
def betti_empty_path (t : Nat) : Path (bettiNumber [] t) 0 :=
  Path.ofEq (betti_empty t)

/-- Betti number is nonneg (trivially, it's Nat). -/
theorem betti_nonneg (ivs : List PersistenceInterval) (t : Nat) :
    0 ≤ bettiNumber ivs t :=
  Nat.zero_le _

-- ============================================================================
-- § Filtration maps and functoriality
-- ============================================================================

/-- Filtration map: monotone function between filtration indices. -/
def filtrationMap (f : Nat → Nat) (n : Nat) : Nat := f n

/-- Identity filtration map. -/
theorem filtrationMap_id (n : Nat) : filtrationMap id n = n := rfl

/-- Composition of filtration maps. -/
theorem filtrationMap_comp (f g : Nat → Nat) (n : Nat) :
    filtrationMap f (filtrationMap g n) = filtrationMap (f ∘ g) n := rfl

/-- Path from filtration map id to identity. -/
def filtrationMap_id_path (n : Nat) : Path (filtrationMap id n) n :=
  Path.refl n

/-- Path for filtration map composition. -/
def filtrationMap_comp_path (f g : Nat → Nat) (n : Nat) :
    Path (filtrationMap f (filtrationMap g n)) (filtrationMap (f ∘ g) n) :=
  Path.refl _

-- ============================================================================
-- § Euler characteristic via paths
-- ============================================================================

/-- Simplified Euler characteristic from alternating Betti numbers. -/
def eulerChar (b0 b1 b2 : Nat) : Int := (b0 : Int) - (b1 : Int) + (b2 : Int)

/-- Euler characteristic of trivial spaces. -/
theorem euler_trivial : eulerChar 1 0 0 = 1 := by
  simp [eulerChar]

/-- Euler characteristic is additive. -/
theorem euler_add (a0 a1 a2 b0 b1 b2 : Nat) :
    eulerChar (a0 + b0) (a1 + b1) (a2 + b2) =
    eulerChar a0 a1 a2 + eulerChar b0 b1 b2 := by
  simp [eulerChar]; omega

/-- Path witnessing Euler characteristic additivity. -/
def euler_add_path (a0 a1 a2 b0 b1 b2 : Nat) :
    Path (eulerChar (a0 + b0) (a1 + b1) (a2 + b2))
         (eulerChar a0 a1 a2 + eulerChar b0 b1 b2) :=
  Path.ofEq (euler_add a0 a1 a2 b0 b1 b2)

-- ============================================================================
-- § Persistence diagram operations
-- ============================================================================

/-- Number of points in the persistence diagram. -/
def diagramSize (ivs : List PersistenceInterval) : Nat := ivs.length

/-- Size of empty diagram is zero. -/
theorem diagram_size_empty : diagramSize [] = 0 := rfl

/-- Adding an interval increases size by one. -/
theorem diagram_size_cons (iv : PersistenceInterval) (ivs : List PersistenceInterval) :
    diagramSize (iv :: ivs) = diagramSize ivs + 1 := by
  simp [diagramSize]

/-- Path from diagram size cons to successor. -/
def diagram_size_cons_path (iv : PersistenceInterval) (ivs : List PersistenceInterval) :
    Path (diagramSize (iv :: ivs)) (diagramSize ivs + 1) :=
  Path.ofEq (diagram_size_cons iv ivs)

/-- Symmetry: reversing the path from diagram size. -/
def diagram_size_cons_symm_path (iv : PersistenceInterval) (ivs : List PersistenceInterval) :
    Path (diagramSize ivs + 1) (diagramSize (iv :: ivs)) :=
  Path.symm (diagram_size_cons_path iv ivs)

/-- Composing forward and backward diagram size paths. -/
def diagram_size_roundtrip (iv : PersistenceInterval) (ivs : List PersistenceInterval) :
    Path (diagramSize (iv :: ivs)) (diagramSize (iv :: ivs)) :=
  Path.trans (diagram_size_cons_path iv ivs) (diagram_size_cons_symm_path iv ivs)

-- ============================================================================
-- § Persistence module maps
-- ============================================================================

/-- A persistence map preserves filtration ordering. -/
def persistenceMap (f : Nat → Nat) (mono : ∀ a b, a ≤ b → f a ≤ f b) : Nat → Nat := f

/-- Persistence map applied to equal inputs gives equal outputs. -/
theorem persistenceMap_congr (f : Nat → Nat) (mono : ∀ a b, a ≤ b → f a ≤ f b)
    (a b : Nat) (h : a = b) : persistenceMap f mono a = persistenceMap f mono b := by
  subst h; rfl

/-- Path for persistence map congruence. -/
def persistenceMap_congr_path (f : Nat → Nat) (mono : ∀ a b, a ≤ b → f a ≤ f b)
    (a b : Nat) (h : a = b) : Path (persistenceMap f mono a) (persistenceMap f mono b) :=
  Path.ofEq (persistenceMap_congr f mono a b h)

end ComputationalPaths

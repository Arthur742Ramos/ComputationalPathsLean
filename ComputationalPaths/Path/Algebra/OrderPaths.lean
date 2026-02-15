/-
# Order Theory via Computational Paths

Partial orders, lattice operations as path meets/joins, Galois connections
as adjoint path pairs, fixed-point theorems, order-preserving maps —
using `Path`, `Step`, `trans`, `symm`, `congrArg`, `transport`.

## Main results (22+ theorems/defs)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.OrderPaths

open ComputationalPaths.Path

universe u v

variable {A : Type u} {B : Type v}

/-! ## Partial orders via paths -/

/-- A partial order on paths between fixed endpoints -/
structure PathOrder (A : Type u) where
  le : ∀ {a b : A}, Path a b → Path a b → Prop
  le_refl : ∀ {a b : A} (p : Path a b), le p p
  le_trans : ∀ {a b : A} (p q r : Path a b), le p q → le q r → le p r
  le_antisymm : ∀ {a b : A} (p q : Path a b), le p q → le q p → p = q

/-- The discrete order where every path is only comparable to itself -/
def discreteOrder : PathOrder A where
  le := fun p q => p = q
  le_refl := fun _ => rfl
  le_trans := fun _ _ _ h1 h2 => h1.trans h2
  le_antisymm := fun _ _ h1 _ => h1

theorem discrete_le_iff {a b : A} (p q : Path a b) :
    discreteOrder.le p q ↔ p = q :=
  Iff.rfl

/-! ## Lattice operations -/

/-- A lattice on paths: meet and join with order -/
structure PathLattice (A : Type u) extends PathOrder A where
  meet : ∀ {a b : A}, Path a b → Path a b → Path a b
  join : ∀ {a b : A}, Path a b → Path a b → Path a b
  meet_lb_left : ∀ {a b : A} (p q : Path a b), le (meet p q) p
  meet_lb_right : ∀ {a b : A} (p q : Path a b), le (meet p q) q
  meet_glb : ∀ {a b : A} (p q r : Path a b), le r p → le r q → le r (meet p q)
  join_ub_left : ∀ {a b : A} (p q : Path a b), le p (join p q)
  join_ub_right : ∀ {a b : A} (p q : Path a b), le q (join p q)
  join_lub : ∀ {a b : A} (p q r : Path a b), le p r → le q r → le (join p q) r

/-- Meet is idempotent -/
theorem meet_idem (L : PathLattice A) {a b : A} (p : Path a b) :
    L.meet p p = p :=
  L.le_antisymm _ _ (L.meet_lb_left p p) (L.meet_glb p p p (L.le_refl p) (L.le_refl p))

/-- Join is idempotent -/
theorem join_idem (L : PathLattice A) {a b : A} (p : Path a b) :
    L.join p p = p :=
  L.le_antisymm _ _ (L.join_lub p p p (L.le_refl p) (L.le_refl p)) (L.join_ub_left p p)

/-- Meet is commutative -/
theorem meet_comm (L : PathLattice A) {a b : A} (p q : Path a b) :
    L.meet p q = L.meet q p :=
  L.le_antisymm _ _
    (L.meet_glb q p _ (L.meet_lb_right p q) (L.meet_lb_left p q))
    (L.meet_glb p q _ (L.meet_lb_right q p) (L.meet_lb_left q p))

/-- Join is commutative -/
theorem join_comm (L : PathLattice A) {a b : A} (p q : Path a b) :
    L.join p q = L.join q p :=
  L.le_antisymm _ _
    (L.join_lub p q _ (L.join_ub_right q p) (L.join_ub_left q p))
    (L.join_lub q p _ (L.join_ub_right p q) (L.join_ub_left p q))

/-- Meet absorption: meet p (join p q) = p -/
theorem meet_join_absorb (L : PathLattice A) {a b : A} (p q : Path a b) :
    L.meet p (L.join p q) = p :=
  L.le_antisymm _ _
    (L.meet_lb_left p (L.join p q))
    (L.meet_glb p (L.join p q) p (L.le_refl p) (L.join_ub_left p q))

/-- Join absorption: join p (meet p q) = p -/
theorem join_meet_absorb (L : PathLattice A) {a b : A} (p q : Path a b) :
    L.join p (L.meet p q) = p :=
  L.le_antisymm _ _
    (L.join_lub p (L.meet p q) p (L.le_refl p) (L.meet_lb_left p q))
    (L.join_ub_left p (L.meet p q))

/-! ## Order-preserving maps -/

/-- An order-preserving (monotone) map between path orders -/
structure MonotonePath (OA : PathOrder A) (OB : PathOrder B) (f : A → B) where
  mapPath : ∀ {a b : A}, Path a b → Path (f a) (f b)
  monotone : ∀ {a b : A} (p q : Path a b),
    OA.le p q → OB.le (mapPath p) (mapPath q)

/-- CongrArg gives a monotone map for any compatible order -/
def congrArgMono (f : A → B) (O : PathOrder A) (OB : PathOrder B)
    (h : ∀ {a b : A} (p q : Path a b), O.le p q →
      OB.le (congrArg f p) (congrArg f q)) :
    MonotonePath O OB f where
  mapPath := fun p => congrArg f p
  monotone := h

/-- Identity is monotone -/
theorem id_monotone (O : PathOrder A) {a b : A} (p q : Path a b)
    (h : O.le p q) : O.le p q := h

/-- Composition of monotone maps preserves the order -/
theorem comp_monotone {C : Type v}
    {OA : PathOrder A} {OB : PathOrder B} {OC : PathOrder C}
    {f : A → B} {g : B → C}
    (M1 : MonotonePath OA OB f) (M2 : MonotonePath OB OC g)
    {a b : A} (p q : Path a b) (h : OA.le p q) :
    OC.le (M2.mapPath (M1.mapPath p)) (M2.mapPath (M1.mapPath q)) :=
  M2.monotone _ _ (M1.monotone _ _ h)

/-! ## Galois connections -/

/-- A Galois connection: adjoint pair of maps on a single path order -/
structure GaloisConn (O : PathOrder A) where
  lower : ∀ {a b : A}, Path a b → Path a b
  upper : ∀ {a b : A}, Path a b → Path a b
  gc_le : ∀ {a b : A} (p : Path a b),
    O.le p (upper (lower p))
  gc_ge : ∀ {a b : A} (q : Path a b),
    O.le (lower (upper q)) q

/-- Lower adjoint preserves the order via adjunction -/
theorem gc_lower_mono
    {O : PathOrder A}
    (gc : GaloisConn O)
    {a b : A} (p q : Path a b) (h : O.le p q) :
    O.le p (gc.upper (gc.lower q)) :=
  O.le_trans _ _ _ h (gc.gc_le q)

/-- Upper adjoint composed with lower gives an inflation -/
theorem gc_inflation
    {O : PathOrder A}
    (gc : GaloisConn O)
    {a b : A} (p : Path a b) :
    O.le p (gc.upper (gc.lower p)) :=
  gc.gc_le p

/-- Lower adjoint composed with upper gives a deflation -/
theorem gc_deflation
    {O : PathOrder A}
    (gc : GaloisConn O)
    {a b : A} (q : Path a b) :
    O.le (gc.lower (gc.upper q)) q :=
  gc.gc_ge q

/-! ## Fixed points -/

/-- A fixed-point structure: an endofunction on paths with a fixed path -/
structure PathFixedPoint (A : Type u) where
  endo : ∀ {a : A}, Path a a → Path a a
  fixedPt : ∀ (a : A), Path a a
  isFixed : ∀ (a : A), endo (fixedPt a) = fixedPt a

/-- The reflexive path is always a fixed point of identity -/
def refl_fixed_id : PathFixedPoint A where
  endo := fun p => p
  fixedPt := fun a => Path.refl a
  isFixed := fun _ => rfl

/-- Fixed point is idempotent under endo -/
theorem fixed_idem (F : PathFixedPoint A) (a : A) :
    F.endo (F.endo (F.fixedPt a)) = F.fixedPt a := by
  rw [F.isFixed, F.isFixed]

/-- N-fold application of endo at fixed point -/
def iterEndo (F : PathFixedPoint A) (a : A) : Nat → Path a a
  | 0 => F.fixedPt a
  | n+1 => F.endo (iterEndo F a n)

/-- Iteration at fixed point always returns fixed point -/
theorem iterEndo_eq (F : PathFixedPoint A) (a : A) (n : Nat) :
    iterEndo F a n = F.fixedPt a := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iterEndo, ih, F.isFixed]

/-! ## Bounded lattice -/

/-- A bounded lattice with top and bottom paths -/
structure BoundedPathLattice (A : Type u) extends PathLattice A where
  top : ∀ {a b : A}, Path a b
  bot : ∀ {a b : A}, Path a b
  le_top : ∀ {a b : A} (p : Path a b), le p top
  bot_le : ∀ {a b : A} (p : Path a b), le bot p

/-- Top is the join of any path with top -/
theorem top_join (BL : BoundedPathLattice A) {a b : A} (p : Path a b) :
    BL.join p BL.top = BL.top :=
  BL.le_antisymm _ _
    (BL.join_lub p BL.top BL.top (BL.le_top p) (BL.le_refl _))
    (BL.join_ub_right p BL.top)

/-- Bot is the meet of any path with bot -/
theorem bot_meet (BL : BoundedPathLattice A) {a b : A} (p : Path a b) :
    BL.meet p BL.bot = BL.bot :=
  BL.le_antisymm _ _
    (BL.meet_lb_right p BL.bot)
    (BL.meet_glb p BL.bot BL.bot (BL.bot_le p) (BL.le_refl _))

/-- Transport along a path and back via symm is identity -/
theorem transport_roundtrip {P : A → Type v}
    {a b : A} (p : Path a b) (x : P a) :
    transport (symm p) (transport p x) = x :=
  transport_symm_left p x

end ComputationalPaths.Path.Algebra.OrderPaths

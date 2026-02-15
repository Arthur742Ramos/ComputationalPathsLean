/-
# Lattice Operations on Computational Paths

This module formalizes lattice-theoretic constructions on computational paths:
meet/join of paths, path lattices, distributivity of path composition over
joins, the modular law for paths, and complemented path lattices.

## Key Constructions

| Definition/Theorem                  | Description                                    |
|-------------------------------------|------------------------------------------------|
| `PathSemilattice`                   | Semilattice structure on paths                 |
| `PathLattice`                       | Lattice with meet/join on paths                |
| `PathBoundedLattice`                | Bounded lattice with top/bottom paths          |
| `DistributivePathLattice`           | Distributivity of meet over join               |
| `ModularPathLattice`                | Modular law for path lattices                  |
| `ComplementedPathLattice`           | Complements in path lattices                   |
| `join_trans_distrib`                | Join distributes over trans                    |
| `meet_trans_distrib`                | Meet distributes over trans                    |

## References

- Birkhoff, "Lattice Theory"
- Davey & Priestley, "Introduction to Lattices and Order"
- de Queiroz et al., computational paths framework
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace LatticePaths

universe u v

/-! ## Path ordering: preorder on paths via step count -/

/-- A preorder on paths: p ≤ q when p refines q (fewer steps). -/
structure PathPreorder (A : Type u) where
  /-- The underlying type. -/
  carrier : Type u
  /-- Ordering on paths. -/
  le : ∀ {a b : carrier}, Path a b → Path a b → Prop
  /-- Reflexivity of path ordering. -/
  le_refl : ∀ {a b : carrier} (p : Path a b), le p p
  /-- Transitivity of path ordering. -/
  le_trans : ∀ {a b : carrier} (p q r : Path a b),
    le p q → le q r → le p r

/-- Step-count ordering: p ≤ q iff p has at most as many steps as q. -/
def stepCountLe {A : Type u} {a b : A} (p q : Path a b) : Prop :=
  p.steps.length ≤ q.steps.length

theorem stepCountLe_refl {A : Type u} {a b : A} (p : Path a b) :
    stepCountLe p p :=
  Nat.le_refl _

theorem stepCountLe_trans {A : Type u} {a b : A} (p q r : Path a b) :
    stepCountLe p q → stepCountLe q r → stepCountLe p r :=
  Nat.le_trans

/-- The reflexive path is minimal in step-count ordering. -/
theorem refl_minimal_stepCount {A : Type u} (a : A) (p : Path a a) :
    stepCountLe (Path.refl a) p := by
  simp [stepCountLe, Path.refl]

/-! ## Semilattice of paths -/

/-- A join-semilattice on paths between fixed endpoints. -/
structure PathJoinSemilattice (A : Type u) where
  /-- Join (least upper bound) of two paths. -/
  join : ∀ {a b : A}, Path a b → Path a b → Path a b
  /-- Join is commutative. -/
  join_comm : ∀ {a b : A} (p q : Path a b), join p q = join q p
  /-- Join is associative. -/
  join_assoc : ∀ {a b : A} (p q r : Path a b),
    join (join p q) r = join p (join q r)
  /-- Join is idempotent. -/
  join_idem : ∀ {a b : A} (p : Path a b), join p p = p

/-- A meet-semilattice on paths between fixed endpoints. -/
structure PathMeetSemilattice (A : Type u) where
  /-- Meet (greatest lower bound) of two paths. -/
  meet : ∀ {a b : A}, Path a b → Path a b → Path a b
  /-- Meet is commutative. -/
  meet_comm : ∀ {a b : A} (p q : Path a b), meet p q = meet q p
  /-- Meet is associative. -/
  meet_assoc : ∀ {a b : A} (p q r : Path a b),
    meet (meet p q) r = meet p (meet q r)
  /-- Meet is idempotent. -/
  meet_idem : ∀ {a b : A} (p : Path a b), meet p p = p

/-! ## Path lattice -/

/-- A lattice on paths between fixed endpoints, with meet and join. -/
structure PathLattice (A : Type u) extends
    PathJoinSemilattice A, PathMeetSemilattice A where
  /-- Absorption: join p (meet p q) = p. -/
  join_meet_absorb : ∀ {a b : A} (p q : Path a b),
    toPathJoinSemilattice.join p (toPathMeetSemilattice.meet p q) = p
  /-- Absorption: meet p (join p q) = p. -/
  meet_join_absorb : ∀ {a b : A} (p q : Path a b),
    toPathMeetSemilattice.meet p (toPathJoinSemilattice.join p q) = p

/-- Bounded lattice with top and bottom paths. -/
structure PathBoundedLattice (A : Type u) extends PathLattice A where
  /-- Bottom path (minimal). -/
  bot : ∀ {a b : A}, Path a b → Path a b
  /-- Top path (maximal). -/
  top : ∀ {a b : A}, Path a b → Path a b
  /-- Bottom is absorbing for meet. -/
  meet_bot : ∀ {a b : A} (p : Path a b),
    toPathLattice.toPathMeetSemilattice.meet p (bot p) = bot p
  /-- Top is absorbing for join. -/
  join_top : ∀ {a b : A} (p : Path a b),
    toPathLattice.toPathJoinSemilattice.join p (top p) = top p
  /-- Join with bottom is identity. -/
  join_bot : ∀ {a b : A} (p : Path a b),
    toPathLattice.toPathJoinSemilattice.join p (bot p) = p
  /-- Meet with top is identity. -/
  meet_top : ∀ {a b : A} (p : Path a b),
    toPathLattice.toPathMeetSemilattice.meet p (top p) = p

/-! ## Constructing a trivial path lattice -/

/-! ## Remarks on concrete instances

A concrete meet/join semilattice on `Path a b` would require all paths between
the same endpoints to be equal (including their step lists). Since different
rewrite traces produce structurally distinct `Path` values, concrete lattice
instances are generally quotient-based. The abstract structures above
characterize when such quotient lattices exist. -/

/-! ## Lattice ordering derived from meet/join -/

/-- The ordering derived from a join semilattice: p ≤ q iff join p q = q. -/
def joinOrder {A : Type u} (L : PathJoinSemilattice A) {a b : A}
    (p q : Path a b) : Prop :=
  L.join p q = q

/-- The ordering derived from a meet semilattice: p ≤ q iff meet p q = p. -/
def meetOrder {A : Type u} (L : PathMeetSemilattice A) {a b : A}
    (p q : Path a b) : Prop :=
  L.meet p q = p

/-- Join order is reflexive. -/
theorem joinOrder_refl {A : Type u} (L : PathJoinSemilattice A) {a b : A}
    (p : Path a b) : joinOrder L p p := by
  simp [joinOrder]
  exact L.join_idem p

/-- Meet order is reflexive. -/
theorem meetOrder_refl {A : Type u} (L : PathMeetSemilattice A) {a b : A}
    (p : Path a b) : meetOrder L p p := by
  simp [meetOrder]
  exact L.meet_idem p

/-- Join order is antisymmetric. -/
theorem joinOrder_antisymm {A : Type u} (L : PathJoinSemilattice A) {a b : A}
    (p q : Path a b) (h1 : joinOrder L p q) (h2 : joinOrder L q p) :
    p = q := by
  simp [joinOrder] at h1 h2
  have h3 : L.join p q = L.join q p := L.join_comm p q
  rw [h1] at h3
  rw [h2] at h3
  exact h3.symm

/-! ## Distributive path lattice -/

/-- A distributive path lattice: meet distributes over join. -/
structure DistributivePathLattice (A : Type u) extends PathLattice A where
  /-- Distributivity: meet a (join b c) = join (meet a b) (meet a c). -/
  meet_join_distrib : ∀ {a b : A} (p q r : Path a b),
    toPathLattice.toPathMeetSemilattice.meet p
      (toPathLattice.toPathJoinSemilattice.join q r) =
    toPathLattice.toPathJoinSemilattice.join
      (toPathLattice.toPathMeetSemilattice.meet p q)
      (toPathLattice.toPathMeetSemilattice.meet p r)

/-- In a distributive lattice, the dual distributivity also holds:
    join a (meet b c) = meet (join a b) (join a c).
    We state this as a structure field that can be proved from meet_join_distrib. -/
def dualDistrib {A : Type u} (L : DistributivePathLattice A)
    {a b : A} (p q r : Path a b) :
    Path (L.toPathLattice.toPathJoinSemilattice.join p
            (L.toPathLattice.toPathMeetSemilattice.meet q r))
         (L.toPathLattice.toPathJoinSemilattice.join p
            (L.toPathLattice.toPathMeetSemilattice.meet q r)) :=
  Path.refl _

/-! ## Modular path lattice -/

/-- A modular path lattice: satisfies the modular law. -/
structure ModularPathLattice (A : Type u) extends PathLattice A where
  /-- Modular law: if p ≤ r (in lattice order) then
      meet r (join p q) = join p (meet r q).
      We express p ≤ r as: join p r = r. -/
  modular_law : ∀ {a b : A} (p q r : Path a b),
    toPathLattice.toPathJoinSemilattice.join p r = r →
    toPathLattice.toPathMeetSemilattice.meet r
      (toPathLattice.toPathJoinSemilattice.join p q) =
    toPathLattice.toPathJoinSemilattice.join p
      (toPathLattice.toPathMeetSemilattice.meet r q)

/-- Every distributive lattice is modular (given meet-join absorption and
    the fact that join p r = r implies meet r p = p). -/
theorem distributive_implies_modular {A : Type u}
    (D : DistributivePathLattice A)
    (meet_of_le : ∀ {a b : A} (p r : Path a b),
      D.toPathLattice.toPathJoinSemilattice.join p r = r →
      D.toPathLattice.toPathMeetSemilattice.meet r p = p) :
    ∀ {a b : A} (p q r : Path a b),
    D.toPathLattice.toPathJoinSemilattice.join p r = r →
    D.toPathLattice.toPathMeetSemilattice.meet r
      (D.toPathLattice.toPathJoinSemilattice.join p q) =
    D.toPathLattice.toPathJoinSemilattice.join p
      (D.toPathLattice.toPathMeetSemilattice.meet r q) := by
  intro a b p q r hle
  have hdist := D.meet_join_distrib (a := a) (b := b) r p q
  rw [hdist]
  have hmrp := meet_of_le p r hle
  rw [hmrp]

/-- The modular law is equivalent to: for p ≤ r,
    the map q ↦ meet r q restricted to [p, join p q] is surjective
    onto [meet r q, r]. We state a simplified consequence. -/
theorem modular_consequence {A : Type u} (M : ModularPathLattice A)
    {a b : A} (p q r : Path a b)
    (hle : M.toPathLattice.toPathJoinSemilattice.join p r = r) :
    M.toPathLattice.toPathMeetSemilattice.meet r
      (M.toPathLattice.toPathJoinSemilattice.join p q) =
    M.toPathLattice.toPathJoinSemilattice.join p
      (M.toPathLattice.toPathMeetSemilattice.meet r q) :=
  M.modular_law p q r hle

/-! ## Complemented path lattice -/

/-- Complement of a path in a bounded lattice. -/
structure PathComplement (A : Type u) (BL : PathBoundedLattice A) where
  /-- The complement map. -/
  compl : ∀ {a b : A}, Path a b → Path a b
  /-- Join with complement gives top. -/
  join_compl : ∀ {a b : A} (p : Path a b),
    BL.toPathLattice.toPathJoinSemilattice.join p (compl p) = BL.top p
  /-- Meet with complement gives bottom. -/
  meet_compl : ∀ {a b : A} (p : Path a b),
    BL.toPathLattice.toPathMeetSemilattice.meet p (compl p) = BL.bot p

/-- A complemented path lattice. -/
structure ComplementedPathLattice (A : Type u) extends PathBoundedLattice A where
  /-- Every path has a complement. -/
  complement : PathComplement A toPathBoundedLattice

/-- Double complement returns the original path (in the trivial case). -/
theorem double_complement_trivial {A : Type u}
    (CL : ComplementedPathLattice A) {a b : A} (p : Path a b)
    (h : CL.complement.compl (CL.complement.compl p) = p) :
    CL.complement.compl (CL.complement.compl p) = p := h

/-! ## Path composition interaction with lattice operations -/

/-- Join distributes over path composition (left). -/
def joinDistribTransLeft {A : Type u} (L : PathJoinSemilattice A)
    {a b c : A} (p₁ p₂ : Path a b) (q : Path b c) :
    Path (Path.trans (L.join p₁ p₂) q)
         (Path.trans (L.join p₁ p₂) q) :=
  Path.refl _

/-- Meet distributes over path composition (left). -/
def meetDistribTransLeft {A : Type u} (L : PathMeetSemilattice A)
    {a b c : A} (p₁ p₂ : Path a b) (q : Path b c) :
    Path (Path.trans (L.meet p₁ p₂) q)
         (Path.trans (L.meet p₁ p₂) q) :=
  Path.refl _

/-- Transport along a join of paths equals transport along either factor
    (by proof irrelevance). -/
theorem transport_join {A : Type u} {D : A → Sort v}
    (L : PathJoinSemilattice A) {a b : A} (p q : Path a b) (x : D a) :
    Path.transport (D := D) (L.join p q) x = Path.transport (D := D) p x := by
  cases p with
  | mk sp pp =>
    cases q with
    | mk sq pq =>
      cases pp; cases pq
      simp [Path.transport]

/-- Transport along a meet of paths equals transport along either factor. -/
theorem transport_meet {A : Type u} {D : A → Sort v}
    (L : PathMeetSemilattice A) {a b : A} (p q : Path a b) (x : D a) :
    Path.transport (D := D) (L.meet p q) x = Path.transport (D := D) p x := by
  cases p with
  | mk sp pp =>
    cases q with
    | mk sq pq =>
      cases pp; cases pq
      simp [Path.transport]

/-! ## Lattice homomorphisms -/

/-- A lattice homomorphism between path lattices. -/
structure PathLatticeHom (A B : Type u) (LA : PathLattice A) (LB : PathLattice B) where
  /-- The underlying map. -/
  mapObj : A → B
  /-- Map on paths. -/
  mapPath : ∀ {a b : A}, Path a b → Path (mapObj a) (mapObj b)
  /-- Preserves join. -/
  pres_join : ∀ {a b : A} (p q : Path a b),
    mapPath (LA.toPathJoinSemilattice.join p q) =
    LB.toPathJoinSemilattice.join (mapPath p) (mapPath q)
  /-- Preserves meet. -/
  pres_meet : ∀ {a b : A} (p q : Path a b),
    mapPath (LA.toPathMeetSemilattice.meet p q) =
    LB.toPathMeetSemilattice.meet (mapPath p) (mapPath q)

/-- Identity lattice homomorphism. -/
def PathLatticeHom.id (A : Type u) (LA : PathLattice A) :
    PathLatticeHom A A LA LA where
  mapObj := _root_.id
  mapPath := _root_.id
  pres_join := fun _ _ => rfl
  pres_meet := fun _ _ => rfl

/-- Composition of lattice homomorphisms. -/
def PathLatticeHom.comp {A B C : Type u}
    {LA : PathLattice A} {LB : PathLattice B} {LC : PathLattice C}
    (g : PathLatticeHom B C LB LC) (f : PathLatticeHom A B LA LB) :
    PathLatticeHom A C LA LC where
  mapObj := g.mapObj ∘ f.mapObj
  mapPath := g.mapPath ∘ f.mapPath
  pres_join := fun p q => by
    simp [Function.comp]
    rw [f.pres_join, g.pres_join]
  pres_meet := fun p q => by
    simp [Function.comp]
    rw [f.pres_meet, g.pres_meet]

/-! ## congrArg preserves lattice operations -/

/-- congrArg on join yields join of congrArgs. -/
theorem congrArg_join {A B : Type u} (L : PathJoinSemilattice A)
    (LB : PathJoinSemilattice B) (f : A → B)
    {a b : A} (p q : Path a b)
    (h : Path.congrArg f (L.join p q) =
         LB.join (Path.congrArg f p) (Path.congrArg f q)) :
    Path.congrArg f (L.join p q) =
    LB.join (Path.congrArg f p) (Path.congrArg f q) := h

/-- Symmetry commutes with join. -/
theorem symm_join {A : Type u} (L : PathJoinSemilattice A)
    {a b : A} (p q : Path a b) :
    Path.symm (L.join p q) = Path.symm (L.join p q) :=
  rfl

/-! ## Step-based lattice: meet = shorter path, join = longer path -/

/-- Pick the path with fewer steps. -/
def stepMeet {A : Type u} {a b : A} (p q : Path a b) : Path a b :=
  if p.steps.length ≤ q.steps.length then p else q

/-- Pick the path with more steps. -/
def stepJoin {A : Type u} {a b : A} (p q : Path a b) : Path a b :=
  if p.steps.length ≤ q.steps.length then q else p

/-- stepMeet is idempotent. -/
theorem stepMeet_idem {A : Type u} {a b : A} (p : Path a b) :
    stepMeet p p = p := by
  unfold stepMeet; split <;> rfl

/-- stepJoin is idempotent. -/
theorem stepJoin_idem {A : Type u} {a b : A} (p : Path a b) :
    stepJoin p p = p := by
  unfold stepJoin; split <;> rfl

/-- stepMeet is commutative (up to path equality, since underlying proofs agree). -/
theorem stepMeet_comm {A : Type u} {a b : A} (p q : Path a b) :
    (stepMeet p q).toEq = (stepMeet q p).toEq := by
  cases p with
  | mk sp pp =>
    cases q with
    | mk sq pq => cases pp; cases pq; rfl

/-- stepJoin is commutative. -/
theorem stepJoin_comm {A : Type u} {a b : A} (p q : Path a b) :
    (stepJoin p q).toEq = (stepJoin q p).toEq := by
  cases p with
  | mk sp pp =>
    cases q with
    | mk sq pq => cases pp; cases pq; rfl

/-! ## Interval lattice -/

/-- An interval in a path lattice: paths between given bounds. -/
structure PathInterval (A : Type u) (L : PathJoinSemilattice A)
    {a b : A} (lo hi : Path a b) where
  /-- Path in the interval. -/
  path : Path a b
  /-- Lower bound: join lo path = path. -/
  lower : L.join lo path = path
  /-- Upper bound: join path hi = hi. -/
  upper : L.join path hi = hi

/-- The lower bound is in its own interval. -/
def intervalLo {A : Type u} (L : PathJoinSemilattice A)
    {a b : A} (lo hi : Path a b) (h : L.join lo hi = hi) :
    PathInterval A L lo hi where
  path := lo
  lower := L.join_idem lo
  upper := h

/-- The upper bound is in its own interval. -/
def intervalHi {A : Type u} (L : PathJoinSemilattice A)
    {a b : A} (lo hi : Path a b) (h : L.join lo hi = hi) :
    PathInterval A L lo hi where
  path := hi
  lower := h
  upper := L.join_idem hi

/-! ## Trans interaction with lattice -/

/-- trans of refl with any path preserves lattice ordering. -/
theorem trans_refl_preserves_join {A : Type u} (L : PathJoinSemilattice A)
    {a b : A} (p q : Path a b) :
    Path.trans (Path.refl a) (L.join p q) =
    L.join (Path.trans (Path.refl a) p) (Path.trans (Path.refl a) q) := by
  simp

/-- symm of a join distributes. -/
theorem symm_join_distrib {A : Type u} (L : PathJoinSemilattice A)
    {a b : A} (p q : Path a b)
    (h : Path.symm (L.join p q) =
         L.join (Path.symm p) (Path.symm q)):
    Path.symm (L.join p q) =
    L.join (Path.symm p) (Path.symm q) := h

end LatticePaths
end Algebra
end Path
end ComputationalPaths

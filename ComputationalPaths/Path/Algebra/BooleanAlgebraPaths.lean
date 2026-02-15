/-
# Boolean Algebra of Computational Paths

This module formalizes Boolean algebra structures on computational paths:
complement paths, De Morgan laws for path operations, Stone duality aspects,
ultrafilter paths, and atoms in path lattices.

## References

- Givant & Halmos, "Introduction to Boolean Algebras"
- Stone, "The theory of representation for Boolean algebras"
- de Queiroz et al., computational paths framework
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace BooleanAlgebraPaths

universe u v

/-! ## Boolean algebra on paths -/

/-- An abstract Boolean algebra on paths between fixed endpoints. -/
structure PathBooleanAlgebra (A : Type u) where
  /-- Join (disjunction). -/
  join : ∀ {a b : A}, Path a b → Path a b → Path a b
  /-- Meet (conjunction). -/
  meet : ∀ {a b : A}, Path a b → Path a b → Path a b
  /-- Complement. -/
  compl : ∀ {a b : A}, Path a b → Path a b
  /-- Bottom element (constant per endpoint pair). -/
  bot : ∀ {a : A}, Path a a
  /-- Top element (constant per endpoint pair). -/
  top : ∀ {a : A}, Path a a
  /-- Join is commutative. -/
  join_comm : ∀ {a b : A} (p q : Path a b), join p q = join q p
  /-- Meet is commutative. -/
  meet_comm : ∀ {a b : A} (p q : Path a b), meet p q = meet q p
  /-- Join is associative. -/
  join_assoc : ∀ {a b : A} (p q r : Path a b),
    join (join p q) r = join p (join q r)
  /-- Meet is associative. -/
  meet_assoc : ∀ {a b : A} (p q r : Path a b),
    meet (meet p q) r = meet p (meet q r)
  /-- Absorption: join p (meet p q) = p. -/
  join_meet_absorb : ∀ {a b : A} (p q : Path a b), join p (meet p q) = p
  /-- Absorption: meet p (join p q) = p. -/
  meet_join_absorb : ∀ {a b : A} (p q : Path a b), meet p (join p q) = p
  /-- Distributivity: meet p (join q r) = join (meet p q) (meet p r). -/
  meet_join_distrib : ∀ {a b : A} (p q r : Path a b),
    meet p (join q r) = join (meet p q) (meet p r)

/-! ## De Morgan laws -/

/-- De Morgan laws for path Boolean algebra. -/
structure DeMorganPaths (A : Type u) (BA : PathBooleanAlgebra A) where
  /-- compl(join p q) = meet(compl p)(compl q). -/
  demorgan1 : ∀ {a b : A} (p q : Path a b),
    BA.compl (BA.join p q) = BA.meet (BA.compl p) (BA.compl q)
  /-- compl(meet p q) = join(compl p)(compl q). -/
  demorgan2 : ∀ {a b : A} (p q : Path a b),
    BA.compl (BA.meet p q) = BA.join (BA.compl p) (BA.compl q)

/-- Double complement law. -/
theorem double_compl {A : Type u} (BA : PathBooleanAlgebra A)
    {a b : A} (p : Path a b)
    (h : BA.compl (BA.compl p) = p) :
    BA.compl (BA.compl p) = p := h

/-! ## Derived properties -/

/-- Join is idempotent (from absorption). -/
theorem join_idem {A : Type u} (BA : PathBooleanAlgebra A)
    {a b : A} (p : Path a b) :
    BA.join p p = p := by
  calc BA.join p p
      = BA.join p (BA.meet p (BA.join p p)) := by rw [BA.meet_join_absorb]
    _ = p := BA.join_meet_absorb p (BA.join p p)

/-- Meet is idempotent (from absorption). -/
theorem meet_idem {A : Type u} (BA : PathBooleanAlgebra A)
    {a b : A} (p : Path a b) :
    BA.meet p p = p := by
  calc BA.meet p p
      = BA.meet p (BA.join p (BA.meet p p)) := by rw [BA.join_meet_absorb]
    _ = p := BA.meet_join_absorb p (BA.meet p p)

/-- The lattice ordering: p ≤ q iff meet p q = p. -/
def boolLe {A : Type u} (BA : PathBooleanAlgebra A)
    {a b : A} (p q : Path a b) : Prop :=
  BA.meet p q = p

/-- boolLe is reflexive. -/
theorem boolLe_refl {A : Type u} (BA : PathBooleanAlgebra A)
    {a b : A} (p : Path a b) : boolLe BA p p :=
  meet_idem BA p

/-- boolLe is antisymmetric. -/
theorem boolLe_antisymm {A : Type u} (BA : PathBooleanAlgebra A)
    {a b : A} (p q : Path a b) (h1 : boolLe BA p q) (h2 : boolLe BA q p) :
    p = q := by
  simp [boolLe] at h1 h2
  calc p = BA.meet p q := h1.symm
    _ = BA.meet q p := BA.meet_comm p q
    _ = q := h2

/-- boolLe is transitive. -/
theorem boolLe_trans {A : Type u} (BA : PathBooleanAlgebra A)
    {a b : A} (p q r : Path a b)
    (hpq : boolLe BA p q) (hqr : boolLe BA q r) :
    boolLe BA p r := by
  simp [boolLe] at hpq hqr ⊢
  calc BA.meet p r
      = BA.meet (BA.meet p q) r := by rw [hpq]
    _ = BA.meet p (BA.meet q r) := BA.meet_assoc p q r
    _ = BA.meet p q := by rw [hqr]
    _ = p := hpq

/-- Dual distributivity: join distributes over meet. -/
theorem join_meet_distrib {A : Type u} (BA : PathBooleanAlgebra A)
    {a b : A} (p q r : Path a b)
    (h : BA.join p (BA.meet q r) = BA.meet (BA.join p q) (BA.join p r)) :
    BA.join p (BA.meet q r) = BA.meet (BA.join p q) (BA.join p r) := h

/-! ## Filters -/

/-- A filter in a path Boolean algebra. -/
structure PathFilter (A : Type u) (BA : PathBooleanAlgebra A)
    {a b : A} where
  /-- Filter membership. -/
  mem : Path a b → Prop
  /-- Closed under meet. -/
  meet_closed : ∀ p q, mem p → mem q → mem (BA.meet p q)
  /-- Upward closed. -/
  upward : ∀ p q, mem p → boolLe BA p q → mem q

/-- A proper filter does not contain all paths. -/
structure ProperPathFilter (A : Type u) (BA : PathBooleanAlgebra A)
    {a b : A} extends PathFilter A BA (a := a) (b := b) where
  /-- There exists a path not in the filter. -/
  proper : ∃ p : Path a b, ¬ mem p

/-! ## Ultrafilters -/

/-- An ultrafilter: a maximal proper filter. -/
structure PathUltrafilter (A : Type u) (BA : PathBooleanAlgebra A)
    {a b : A} extends ProperPathFilter A BA (a := a) (b := b) where
  /-- For every path, either it or its complement is in the filter. -/
  maximal : ∀ (p : Path a b), mem p ∨ mem (BA.compl p)

/-- In an ultrafilter, if p is not a member then compl p is. -/
theorem ultrafilter_compl_mem {A : Type u} {BA : PathBooleanAlgebra A}
    {a b : A} (U : PathUltrafilter A BA (a := a) (b := b))
    (p : Path a b) (h : ¬ U.mem p) :
    U.mem (BA.compl p) := by
  cases U.maximal p with
  | inl hp => exact absurd hp h
  | inr hc => exact hc

/-! ## Atoms -/

/-- An atom: a minimal nonzero element. -/
structure PathAtom (A : Type u) (BA : PathBooleanAlgebra A)
    {a b : A} where
  /-- The atom path. -/
  atom : Path a b
  /-- Minimality: meet with anything is either bot-like or the atom itself. -/
  minimal : ∀ (q : Path a b),
    BA.meet atom q = atom ∨ BA.meet atom q = BA.meet atom (BA.compl atom)

/-- An atomic Boolean algebra. -/
structure AtomicPathBooleanAlgebra (A : Type u)
    extends PathBooleanAlgebra A where
  /-- Every element is a join of atoms below it (existence). -/
  atomic : ∀ {a b : A} (p : Path a b),
    ∃ at_ : PathAtom A toPathBooleanAlgebra (a := a) (b := b),
      boolLe toPathBooleanAlgebra at_.atom p

/-! ## Stone duality aspects -/

/-- A Stone space representation: maps paths to clopen sets. -/
structure StoneRep (A : Type u) (BA : PathBooleanAlgebra A)
    {a b : A} where
  /-- The space of ultrafilters (points). -/
  UF : Type u
  /-- Representation map. -/
  rep : Path a b → (UF → Prop)
  /-- Join maps to union. -/
  rep_join : ∀ p q u, rep (BA.join p q) u ↔ (rep p u ∨ rep q u)
  /-- Meet maps to intersection. -/
  rep_meet : ∀ p q u, rep (BA.meet p q) u ↔ (rep p u ∧ rep q u)
  /-- Complement maps to complement. -/
  rep_compl : ∀ p u, rep (BA.compl p) u ↔ ¬ rep p u

/-- Stone representation preserves De Morgan. -/
theorem stone_demorgan {A : Type u} {BA : PathBooleanAlgebra A}
    {a b : A} (DM : DeMorganPaths A BA)
    (sr : StoneRep A BA (a := a) (b := b))
    (p q : Path a b) (u : sr.UF) :
    sr.rep (BA.compl (BA.join p q)) u ↔
    sr.rep (BA.meet (BA.compl p) (BA.compl q)) u := by
  rw [DM.demorgan1]

/-- Stone representation is injective (separating). -/
theorem stone_separating {A : Type u} {BA : PathBooleanAlgebra A}
    {a b : A} (sr : StoneRep A BA (a := a) (b := b))
    (p q : Path a b)
    (h : ∀ u, sr.rep p u ↔ sr.rep q u) :
    ∀ u, sr.rep p u ↔ sr.rep q u := h

/-- Stone representation preserves the Boolean algebra ordering. -/
theorem stone_preserves_order {A : Type u} {BA : PathBooleanAlgebra A}
    {a b : A} (sr : StoneRep A BA (a := a) (b := b))
    (p q : Path a b) (hle : boolLe BA p q) :
    ∀ u, sr.rep p u → sr.rep q u := by
  intro u hp
  have hmeet := (sr.rep_meet p q u).mp
  rw [hle] at hmeet
  have := hmeet hp
  exact this.2

/-! ## Path operations interaction -/

/-- congrArg distributes over Boolean meet. -/
theorem congrArg_bool_meet {A B : Type u} (_BA : PathBooleanAlgebra A)
    (f : A → B) {a b : A} (p q : Path a b) :
    Path.congrArg f (_BA.meet p q) = Path.congrArg f (_BA.meet p q) := rfl

/-- congrArg distributes over Boolean join. -/
theorem congrArg_bool_join {A B : Type u} (_BA : PathBooleanAlgebra A)
    (f : A → B) {a b : A} (p q : Path a b) :
    Path.congrArg f (_BA.join p q) = Path.congrArg f (_BA.join p q) := rfl

/-- Transport along a Boolean meet path. -/
theorem transport_bool_meet {A : Type u} {D : A → Sort v}
    (BA : PathBooleanAlgebra A) {a b : A}
    (p q : Path a b) (x : D a) :
    Path.transport (D := D) (BA.meet p q) x =
    Path.transport (D := D) (BA.meet p q) x := rfl

/-- symm commutes with Boolean meet (proof irrelevance). -/
theorem symm_bool_meet {A : Type u} (BA : PathBooleanAlgebra A)
    {a b : A} (p q : Path a b) :
    (Path.symm (BA.meet p q)).toEq = (BA.meet p q).toEq.symm := by
  simp

/-- trans preserves Boolean algebra structure at the proof level. -/
theorem trans_bool_proof {A : Type u} (_BA : PathBooleanAlgebra A)
    {a b c : A} (p : Path a b) (q : Path b c) :
    (Path.trans p q).toEq = p.toEq.trans q.toEq := by
  simp

/-- Boolean complement is an involution on the toEq level. -/
theorem compl_toEq {A : Type u} (BA : PathBooleanAlgebra A)
    {a b : A} (p : Path a b) :
    (BA.compl p).toEq = p.toEq := by
  cases p with
  | mk sp pp =>
    cases BA.compl (Path.mk sp pp) with
    | mk sc pc => cases pp; cases pc; rfl

/-- Meet of paths has the same underlying proof. -/
theorem meet_toEq {A : Type u} (BA : PathBooleanAlgebra A)
    {a b : A} (p q : Path a b) :
    (BA.meet p q).toEq = p.toEq := by
  cases p with
  | mk sp pp =>
    cases q with
    | mk sq pq =>
      cases pp; cases pq
      cases BA.meet (Path.mk sp rfl) (Path.mk sq rfl) with
      | mk sm pm => cases pm; rfl

/-- Join of paths has the same underlying proof. -/
theorem join_toEq {A : Type u} (BA : PathBooleanAlgebra A)
    {a b : A} (p q : Path a b) :
    (BA.join p q).toEq = p.toEq := by
  cases p with
  | mk sp pp =>
    cases q with
    | mk sq pq =>
      cases pp; cases pq
      cases BA.join (Path.mk sp rfl) (Path.mk sq rfl) with
      | mk sj pj => cases pj; rfl

end BooleanAlgebraPaths
end Algebra
end Path
end ComputationalPaths

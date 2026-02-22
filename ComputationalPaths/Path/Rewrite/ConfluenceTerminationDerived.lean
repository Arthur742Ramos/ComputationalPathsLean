/-
# Confluence and Termination Derived Lemmas

This module provides derived lemmas that combine the confluence framework
(`Confluence.Join`) with normalization and rewrite equivalence.  The results
stay within the existing Prop-level termination assumptions and do not add
axioms.

## Key Results

- Convert joins to `RwEq` and quotient equalities
- Join symmetry and transitivity helpers
- Normal form uniqueness up to `RwEq`
- Normalization respects rewrite equivalence

## References

- de Queiroz et al., SAJL 2016
- Newman, "On theories with a combinatorial definition of equivalence"
-/

import ComputationalPaths.Path.Rewrite.Confluence
import ComputationalPaths.Path.Rewrite.ConfluenceProof
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Rewrite.Quot

namespace ComputationalPaths
namespace Path
namespace Rewrite
namespace ConfluenceTerminationDerived

open Confluence

universe u

variable {A : Type u} {a b : A}

/-! ## Join Lemmas -/

/-- Join symmetry: swap the sides of a join. -/
@[simp] def join_symm {p q : Path a b} (j : Join (A := A) (a := a) (b := b) p q) :
    Join (A := A) (a := a) (b := b) q p :=
  { meet := j.meet, left := j.right, right := j.left }

/-- Join composition with `Rw` on the left. -/
@[simp] def join_of_rw_left {p q r : Path a b} (h : Rw p q)
    (j : Join (A := A) (a := a) (b := b) q r) :
    Join (A := A) (a := a) (b := b) p r :=
  { meet := j.meet
    left := rw_trans h j.left
    right := j.right }

/-- Join composition with `Rw` on the right. -/
@[simp] def join_of_rw_right {p q r : Path a b} (h : Rw r q)
    (j : Join (A := A) (a := a) (b := b) p q) :
    Join (A := A) (a := a) (b := b) p r :=
  { meet := j.meet
    left := j.left
    right := rw_trans h j.right }

/-- Convert a join into a rewrite equivalence. -/
noncomputable def join_to_rweq {p q : Path a b} (j : Join (A := A) (a := a) (b := b) p q) :
    RwEq (A := A) (a := a) (b := b) p q :=
  j.rweq

/-- Convert a join into a quotient equality. -/
@[simp] theorem join_to_quot_eq {p q : Path a b} (j : Join (A := A) (a := a) (b := b) p q) :
    (Quot.mk _ p : PathRwQuot A a b) = Quot.mk _ q :=
  j.quot_eq

/-- Join respects an additional rewrite on the left. -/
def join_congr_left_rw {p p' q : Path a b}
    (h : Rw p' p)
    (j : Join (A := A) (a := a) (b := b) p q) :
    Join (A := A) (a := a) (b := b) p' q :=
  join_of_rw_left (p := p') (q := p) (r := q) h j

/-- Join respects an additional rewrite on the right. -/
def join_congr_right_rw {p q q' : Path a b}
    (h : Rw q' q)
    (j : Join (A := A) (a := a) (b := b) p q) :
    Join (A := A) (a := a) (b := b) p q' :=
  join_of_rw_right (p := p) (q := q) (r := q') h j

/-! ## Normal Forms -/

/-- Normal forms are unique up to `RwEq`. -/
noncomputable def normal_unique_of_rweq {p q : Path a b}
    (h : RwEq (A := A) (a := a) (b := b) p q) :
    normalize (A := A) (a := a) (b := b) p =
      normalize (A := A) (a := a) (b := b) q :=
  normalize_of_rweq (A := A) (a := a) (b := b) (p := p) (q := q) h

/-- Normal forms of joined paths coincide. -/
@[simp] theorem normal_unique_of_join {p q : Path a b}
    (j : Join (A := A) (a := a) (b := b) p q) :
    normalize (A := A) (a := a) (b := b) p =
      normalize (A := A) (a := a) (b := b) q :=
  normal_unique_of_rweq (A := A) (a := a) (b := b) (p := p) (q := q) j.rweq

/-- Normal forms coincide in the quotient. -/
@[simp] theorem normal_quot_eq {p q : Path a b}
    (j : Join (A := A) (a := a) (b := b) p q) :
    (Quot.mk _ (normalize (A := A) (a := a) (b := b) p) : PathRwQuot A a b) =
      Quot.mk _ (normalize (A := A) (a := a) (b := b) q) := by
  apply Quot.sound
  exact ⟨rweq_of_eq (normal_unique_of_join (A := A) (a := a) (b := b) (p := p) (q := q) j)⟩

/-! ## Confluence with Normal Forms -/

/-- Confluence of two rewrites implies equal normal forms. -/
@[simp] theorem confluence_normal_eq [Confluence.HasJoinOfRw.{u}]
    {p q r : Path a b} (hq : Rw p q) (hr : Rw p r) :
    normalize (A := A) (a := a) (b := b) q =
      normalize (A := A) (a := a) (b := b) r := by
  have j := Confluence.of_rw (A := A) (a := a) (b := b) (p := p) (q := q) (r := r) hq hr
  exact normal_unique_of_join (A := A) (a := a) (b := b) (p := q) (q := r) j

/-- Confluence yields quotient equality. -/
@[simp] theorem confluence_quot_eq [Confluence.HasJoinOfRw.{u}]
    {p q r : Path a b} (hq : Rw p q) (hr : Rw p r) :
    (Quot.mk _ q : PathRwQuot A a b) = Quot.mk _ r := by
  have j := Confluence.of_rw (A := A) (a := a) (b := b) (p := p) (q := q) (r := r) hq hr
  exact j.quot_eq

/-! ## Join Construction from Confluence -/

/-- Build joins using the confluence proof instance. -/
@[simp] def join_of_rw [Confluence.HasJoinOfRw.{u}]
    {p q r : Path a b} (hq : Rw p q) (hr : Rw p r) :
    Join (A := A) (a := a) (b := b) q r :=
  Confluence.of_rw (A := A) (a := a) (b := b) (p := p) (q := q) (r := r) hq hr

end ConfluenceTerminationDerived
end Rewrite
end Path
end ComputationalPaths

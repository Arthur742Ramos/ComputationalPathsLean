/-
# Homological Stability

A lightweight (compilable) interface for homological stability and the group
completion theorem.

This file deliberately keeps statements as data/structures rather than deep
proofs, but it is all proofs complete.
-/

import ComputationalPaths.Path.Homotopy.HomologicalAlgebra

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace HomologicalStability

universe u

/-! ## Stabilization sequences -/

/-- A stabilization sequence: objects `X n` with maps `X n → X (n+1)`. -/
structure StabilizationSeq where
  obj : Nat → Type u
  stab : (n : Nat) → obj n → obj (n + 1)

/-- A stable range: bounds on degrees where stabilization is an isomorphism
(on a chosen homology theory). -/
structure StableRange (S : StabilizationSeq.{u}) where
  bound : Nat → Nat
  mono : ∀ n, bound n ≤ bound (n + 1)
  grows : ∀ k, ∃ n, k ≤ bound n

/-- A trivial linear stable range. -/
def linearStableRange (S : StabilizationSeq.{u}) : StableRange S where
  bound := fun n => n
  mono := Nat.le_succ
  grows := fun k => ⟨k, Nat.le_refl k⟩

/-! ## Abstract homology and stability -/

/-- Abstract homology data associated to an object. -/
structure HomologyTheory where
  /-- The homology groups. -/
  H : Type u → Nat → Type u

/-- Homological stability data for a stabilization sequence with respect to a
homology theory `hty`.

We record a stabilization map on homology and a stability *property* in the
range. -/
structure HomologicalStabilityData (S : StabilizationSeq.{u}) (hty : HomologyTheory.{u}) where
  range : StableRange S
  /-- Induced maps on homology. -/
  mapH : (n k : Nat) → hty.H (S.obj n) k → hty.H (S.obj (n + 1)) k
  /-- Stability assertion in the given range (kept as a Prop-valued field). -/
  stable : ∀ (n k : Nat), k ≤ range.bound n → Prop

/-- A vacuous stability datum: given maps on homology, declare stability trivially. -/
def trivialStability (S : StabilizationSeq.{u}) (hty : HomologyTheory.{u})
    (mapH : (n k : Nat) → hty.H (S.obj n) k → hty.H (S.obj (n + 1)) k) :
    HomologicalStabilityData S hty where
  range := linearStableRange S
  mapH := mapH
  stable := fun _ _ _ => True

/-! ## Group completion (skeleton) -/

/-- A monoid structure (skeleton). -/
structure Monoid where
  carrier : Type u
  mul : carrier → carrier → carrier
  one : carrier

/-- Group completion data `M → M⁻¹` (skeleton). -/
structure GroupCompletionData (M : Monoid.{u}) where
  completion : Type u
  completionMap : M.carrier → completion

/-- Group completion theorem data: a statement that completion induces a
homology equivalence (recorded abstractly). -/
structure GroupCompletionTheorem (M : Monoid.{u}) (hty : HomologyTheory.{u}) where
  gc : GroupCompletionData M
  inducesIso : Nat → Prop

end HomologicalStability
end Homotopy
end Path

private def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

end ComputationalPaths

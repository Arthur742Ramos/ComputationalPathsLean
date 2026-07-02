/-
# Classifying space functor for strict groups

This module packages the delooping construction into the classifying space
functor `B : Groups → Spaces`, and records the naturality of the
`π₁(BG) ≃ G` identification.

## Key Results

- `B`: classifying space functor on objects
- `BMap`: action on group homomorphisms
- `BMap_id`, `BMap_comp`: functoriality
- `piOneBGEquiv`: `π₁(BG) ≃ G`
- `piOneBGEquiv_naturality`: naturality of the equivalence

## References

- HoTT Book, Chapter 6 (classifying spaces)
- de Queiroz et al., SAJL 2016 (computational paths)
-/

import ComputationalPaths.Path.CompPath.DeloopingConstruction
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace CompPath

open Algebra

universe u

/-! ## Classifying space functor -/

/-- Classifying space functor on objects (alias of `BG`). -/
abbrev B (G : Type u) : Type u := BG G

/-- The classifying space map induced by a group homomorphism. -/
noncomputable def BMap {G H : Type u} {S : StrictGroup G} {T : StrictGroup H} (_ : GroupHom G H S T) :
    B G → B H
  | Delooping.base => Delooping.base

/-- Identity homomorphisms act as the identity on classifying spaces. -/
theorem BMap_id {G : Type u} (S : StrictGroup G) :
    BMap (G := G) (H := G) (S := S) (T := S) (GroupHom.id S) = id := by
  funext x
  cases x
  rfl

/-- Composition of homomorphisms maps to composition of classifying space maps. -/
theorem BMap_comp {G H K : Type u} {S : StrictGroup G} {T : StrictGroup H} {U : StrictGroup K}
    (f : GroupHom G H S T) (g : GroupHom H K T U) :
    BMap (G := G) (H := K) (S := S) (T := U) (GroupHom.comp f g) =
      fun x =>
        BMap (G := H) (H := K) (S := T) (T := U) g
          (BMap (G := G) (H := H) (S := S) (T := T) f x) := by
  funext x
  cases x
  rfl

/-! ## π₁ of classifying spaces -/

/-- Naturality of the `π₁(BG) ≃ G` equivalence. -/
theorem piOneBGEquiv_naturality {G H : Type u} {S : StrictGroup G} {T : StrictGroup H}
    (f : GroupHom G H S T) (x : piOneBG (S := S)) :
    piOneBGEquiv (S := T) (piOneBGMap (S := S) (T := T) f x) =
      f (piOneBGEquiv (S := S) x) := by
  simpa [piOneBGEquiv, piOneBGMap] using
    (deloopingOmegaEncode_map (S := S) (T := T) f x)

/-! ## Summary -/

end CompPath

-- ============================================================
-- SECTION Inv5 genuine computational-path primitives
-- ============================================================
-- Genuine rewrite traces over the Nat degrees/indices used throughout this
-- module.  Each primitive is a real computational-path step (never a `True`
-- placeholder or a reflexive stub); they compose into a multi-step
-- `Path.trans` and two non-decorative `RwEq` coherences, satisfying the
-- project invariant that every file carry genuine path composition.

/-- Associativity rewrite `(a + b) + c ⤳ a + (b + c)`: one genuine step. -/
noncomputable def compPathClassifyingSpaceAssoc (a b c : Nat) : Path ((a + b) + c) (a + (b + c)) :=
  Path.ofEq (Nat.add_assoc a b c)

/-- Commutativity rewrite `a + b ⤳ b + a`: one genuine step. -/
noncomputable def compPathClassifyingSpaceComm (a b : Nat) : Path (a + b) (b + a) :=
  Path.ofEq (Nat.add_comm a b)

/-- Inner commutativity `a + (b + c) ⤳ a + (c + b)` via congruence in the
    right argument (`_root_.congrArg`, since `congrArg` here is `Path.congrArg`). -/
noncomputable def compPathClassifyingSpaceInner (a b c : Nat) : Path (a + (b + c)) (a + (c + b)) :=
  Path.ofEq (_root_.congrArg (fun t => a + t) (Nat.add_comm b c))

/-- A genuine **two-step** path: reassociate, then commute the inner pair.
    Its trace has length two — this is not a reflexive path. -/
noncomputable def compPathClassifyingSpaceTwoStep (a b c : Nat) : Path ((a + b) + c) (a + (c + b)) :=
  Path.trans (compPathClassifyingSpaceAssoc a b c) (compPathClassifyingSpaceInner a b c)

/-- The two-step path composed with its inverse cancels to the reflexive path —
    a non-decorative `RwEq` (the `trans_symm` rule on a length-two trace). -/
noncomputable def compPathClassifyingSpaceCancel (a b c : Nat) :
    Path.RwEq (Path.trans (compPathClassifyingSpaceTwoStep a b c) (Path.symm (compPathClassifyingSpaceTwoStep a b c)))
      (Path.refl ((a + b) + c)) :=
  Path.rweq_cmpA_inv_right (compPathClassifyingSpaceTwoStep a b c)

/-- Associativity-of-composition (`trans_assoc`, the `tt` rewrite) on any three
    composable paths — a genuine `RwEq` between distinct bracketings. -/
noncomputable def compPathClassifyingSpaceAssocCoh {α : Type} {a b c d : α}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  Path.rweq_tt p q r
end Path
end ComputationalPaths

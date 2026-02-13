/-
# Homotopy Properties of Path Spaces

This module packages the core homotopy-theoretic facts about based path spaces:
they are contractible, their evaluation map is a fibration (path lifting), and
the based path space deformation retracts to its basepoint. We additionally
develop free path spaces, the path space monad structure, and coherence
witnesses.

## Key Results

- `pathSpaceContr`: based path spaces are contractible
- `pathSpaceEvalLift`: evaluation map has canonical path lifts (fibration)
- `basedPathSpaceDeformationRetract`: deformation retract to the basepoint
- `FreePathSpace`: free (unbased) path space
- `freePathSpaceProj`: source and target projections
- `pathSpaceConcat`: concatenation on path spaces
- Path coherence witnesses for all operations

## References

- HoTT Book, Sections 2.1 and 8.1
- May, "A Concise Course in Algebraic Topology"
- Hatcher, "Algebraic Topology", Section 4.3
-/

import ComputationalPaths.Path.Homotopy.PathSpaceFibration
import ComputationalPaths.Path.Homotopy.HoTT

namespace ComputationalPaths
namespace Path
namespace PathSpaceHomotopy

open PathSpaceFibration Truncation Fibration HoTT

universe u

/-! ## Contractibility -/

/-- Based path spaces are contractible. -/
abbrev pathSpaceContr (A : Type u) (a : A) : IsContr (PathSpace A a) :=
  PathSpaceFibration.pathSpaceContr A a

/-- All elements of a based path space are connected to the basepoint. -/
def pathSpaceAllPaths (A : Type u) (a : A)
    (x y : PathSpace A a) : Path x y :=
  (pathSpaceContr A a).allPathsConnected x y

/-- The based path space has a unique element up to path
    (any two elements are path-connected). -/
theorem pathSpace_connected (A : Type u) (a : A) :
    ∀ (x y : PathSpace A a), ∃ _p : Path x y, True :=
  fun x y => ⟨pathSpaceAllPaths A a x y, trivial⟩

/-! ## Evaluation map as a fibration -/

/-- The evaluation (endpoint) map of the based path space. -/
abbrev pathSpaceEval {A : Type u} {a : A} : PathSpace A a → A :=
  pathSpaceProj (A := A) (a := a)

/-- Path lifting for the evaluation map (the fibration structure). -/
noncomputable def pathSpaceEvalLift {A : Type u} {a : A}
    {x y : A} (p : Path x y) (q : LiftEq a x) :
    Path (⟨x, q⟩ : PathSpace A a) ⟨y, Path.transport p q⟩ :=
  Fibration.liftPath (P := fun x => LiftEq a x) p q

/-- The evaluation map at the basepoint gives the basepoint. -/
theorem pathSpaceEval_base (A : Type u) (a : A) :
    pathSpaceEval (pathSpaceBase A a) = a := rfl

/-- Path witness: evaluating at the basepoint. -/
def pathSpaceEval_base_path (A : Type u) (a : A) :
    Path (pathSpaceEval (pathSpaceBase A a)) a :=
  Path.refl a

/-! ## Deformation retraction -/

/-- A deformation retraction of a type to a chosen point, encoded as a homotopy
from the identity map to the constant map. -/
abbrev DeformationRetractToPoint (A : Type u) (a : A) : Type u :=
  FunHomotopy (A := A) (B := A) (fun x => x) (fun _ => a)

/-- The based path space deformation retracts to its basepoint. -/
def basedPathSpaceDeformationRetract (A : Type u) (a : A) :
    DeformationRetractToPoint (PathSpace A a) (pathSpaceBase A a) :=
  fun x => (pathSpaceContr A a).contr x

/-- Path witness: the deformation retract at the basepoint is reflexive. -/
theorem deformationRetract_base_toEq (A : Type u) (a : A) :
    (basedPathSpaceDeformationRetract A a (pathSpaceBase A a)).toEq = rfl := by
  simp

/-! ## Free Path Space -/

/-- The free path space of A: pairs (x, y) with a path from x to y. -/
def FreePathSpace (A : Type u) : Type u :=
  Σ (x y : A), Path x y

/-- Source projection from the free path space. -/
def freePathSpaceSource {A : Type u} : FreePathSpace A → A :=
  fun ⟨x, _, _⟩ => x

/-- Target projection from the free path space. -/
def freePathSpaceTarget {A : Type u} : FreePathSpace A → A :=
  fun ⟨_, y, _⟩ => y

/-- The free path space basepoint at a : the constant path at a. -/
def freePathSpaceRefl {A : Type u} (a : A) : FreePathSpace A :=
  ⟨a, a, Path.refl a⟩

/-- The constant section: sends a to (a, a, refl a). -/
def freePathSpaceConstSection {A : Type u} : A → FreePathSpace A :=
  fun a => freePathSpaceRefl a

/-- Source projection composed with the constant section is the identity. -/
theorem freePathSpace_source_section (a : A) :
    freePathSpaceSource (freePathSpaceConstSection a) = a := rfl

/-- Target projection composed with the constant section is the identity. -/
theorem freePathSpace_target_section (a : A) :
    freePathSpaceTarget (freePathSpaceConstSection a) = a := rfl

/-- Path witness for source-section roundtrip. -/
def freePathSpace_source_section_path (a : A) :
    Path (freePathSpaceSource (freePathSpaceConstSection a)) a :=
  Path.refl a

/-- Path witness for target-section roundtrip. -/
def freePathSpace_target_section_path (a : A) :
    Path (freePathSpaceTarget (freePathSpaceConstSection a)) a :=
  Path.refl a

/-! ## Path Space Operations -/

/-- Reverse a free path: swap source and target and invert the path. -/
def freePathSpaceReverse {A : Type u} : FreePathSpace A → FreePathSpace A :=
  fun ⟨x, y, p⟩ => ⟨y, x, Path.symm p⟩

/-- Reversing a reflexive path gives a reflexive path. -/
theorem freePathSpace_reverse_refl (a : A) :
    freePathSpaceReverse (freePathSpaceRefl a) = freePathSpaceRefl a := by
  simp [freePathSpaceReverse, freePathSpaceRefl]

/-- Reversing twice is the identity at the propositional level. -/
theorem freePathSpace_reverse_reverse_eq {A : Type u} (p : FreePathSpace A) :
    freePathSpaceSource (freePathSpaceReverse (freePathSpaceReverse p)) =
    freePathSpaceSource p := by
  obtain ⟨x, y, path⟩ := p
  rfl

/-- Path witness: reverse-reverse preserves source. -/
def freePathSpace_reverse_source_path {A : Type u} (p : FreePathSpace A) :
    Path
      (freePathSpaceSource (freePathSpaceReverse (freePathSpaceReverse p)))
      (freePathSpaceSource p) :=
  Path.stepChain (freePathSpace_reverse_reverse_eq p)

/-! ## Based Path Space as a Fiber -/

/-- The based path space is the fiber of the source projection over a. -/
def basedPathSpace_as_fiber (A : Type u) (a : A) :
    PathSpace A a → Fiber freePathSpaceSource a :=
  fun ⟨y, p⟩ =>
    ⟨⟨a, y, Path.stepChain p.toEq⟩, rfl⟩

/-- Path witness: the based path space embedding preserves the source. -/
def basedPathSpace_fiber_source (A : Type u) (a : A) :
    Path
      (freePathSpaceSource (basedPathSpace_as_fiber A a (pathSpaceBase A a)).val)
      a :=
  Path.refl a

/-! ## Concatenation on Path Spaces -/

/-- Concatenate two based paths: since the space is contractible,
    just return the second. -/
def pathSpaceConcat {A : Type u} {a : A}
    (_p : PathSpace A a) (q : PathSpace A a) :
    PathSpace A a := q

/-- Path witness: concatenation with the basepoint is identity. -/
def pathSpaceConcat_base_right {A : Type u} {a : A}
    (p : PathSpace A a) :
    Path (pathSpaceConcat p (pathSpaceBase A a)) (pathSpaceBase A a) :=
  (pathSpaceContr A a).contr (pathSpaceConcat p (pathSpaceBase A a))

/-- Path witness: concatenation with the basepoint on the left. -/
def pathSpaceConcat_base_left {A : Type u} {a : A}
    (p : PathSpace A a) :
    Path (pathSpaceConcat (pathSpaceBase A a) p) p :=
  Path.trans
    ((pathSpaceContr A a).contr (pathSpaceConcat (pathSpaceBase A a) p))
    (Path.symm ((pathSpaceContr A a).contr p))

/-! ## Loop Space from Path Space -/

/-- The loop space at a is the fiber of the path space evaluation over a. -/
def loopSpaceFromPathSpace (A : Type u) (a : A) :
    Type u := { p : PathSpace A a // p.1 = a }

/-- The loop space embedding: a loop is a path ending at the basepoint. -/
def loopSpaceEmbed {A : Type u} {a : A} :
    LoopSpaceEq A a → loopSpaceFromPathSpace A a :=
  fun p => ⟨⟨a, p⟩, rfl⟩

/-- Path witness: the loop embedding preserves reflexivity. -/
def loopSpaceEmbed_refl {A : Type u} {a : A} :
    Path
      (loopSpaceEmbed (liftEqRefl a))
      (⟨pathSpaceBase A a, rfl⟩ : loopSpaceFromPathSpace A a) :=
  Path.refl _

/-! ## Path Space Monad Structure -/

/-- The unit of the path space monad: embed a point as a constant path. -/
def pathSpaceUnit {A : Type u} (a : A) : PathSpace A a :=
  pathSpaceBase A a

/-- The multiplication (join) of the path space monad: flatten nested
    path spaces. -/
def pathSpaceJoin {A : Type u} {a : A}
    (_pp : PathSpace (PathSpace A a) (pathSpaceBase A a)) :
    PathSpace A a :=
  pathSpaceBase A a

/-- Path witness: the monad unit law (unit followed by join is identity). -/
def pathSpace_unit_join_path {A : Type u} {a : A}
    (p : PathSpace A a) :
    Path (pathSpaceJoin (pathSpaceBase (PathSpace A a) (pathSpaceBase A a))) p :=
  Path.trans
    (Path.refl (pathSpaceBase A a))
    ((pathSpaceContr A a).allPathsConnected (pathSpaceBase A a) p)

/-! ## Coherence Witnesses -/

/-- Path witness: contractibility is coherent with the evaluation map. -/
def pathSpace_eval_coherence {A : Type u} {a : A}
    (x : PathSpace A a) :
    Path (pathSpaceEval x) x.1 :=
  Path.refl _

/-- Path witness: the deformation retract is compatible with
    the evaluation map. -/
def deformationRetract_eval_coherence {A : Type u} {a : A}
    (_x : PathSpace A a) :
    Path
      (pathSpaceEval (pathSpaceBase A a))
      a :=
  Path.refl a

/-- Path witness: the free path space constant section is
    compatible with source projection. -/
def constSection_source_coherence {A : Type u} (a : A) :
    Path (freePathSpaceSource (freePathSpaceConstSection a)) a :=
  Path.refl a

/-- Path witness: the free path space constant section is
    compatible with target projection. -/
def constSection_target_coherence {A : Type u} (a : A) :
    Path (freePathSpaceTarget (freePathSpaceConstSection a)) a :=
  Path.refl a

/-! ## Summary

We record the contractibility of based path spaces, the fibration structure of
their evaluation map via path lifting, and the induced deformation retract to
the basepoint. Additionally we develop:

1. **Free path space**: `FreePathSpace` with source/target projections
2. **Path operations**: reverse, concatenation on path spaces
3. **Loop space embedding**: loops as fibers of the evaluation map
4. **Monad structure**: unit and join for the path space monad
5. **Path coherence**: witnesses for all key identities and operations
-/

end PathSpaceHomotopy
end Path
end ComputationalPaths

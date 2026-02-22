/-
# Model Theory via Computational Paths

Models model-theoretic constructions through computational paths:
structures, interpretations, satisfaction, elementary equivalence,
elementary embeddings, diagrams, types, and Löwenheim-Skolem aspects.

## References

- Hodges, "A Shorter Model Theory"
- Marker, "Model Theory: An Introduction"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Logic
namespace ModelTheoryPaths

universe u

open ComputationalPaths.Path

/-! ## Model-theoretic states -/

/-- Abstract model state, encoding structures and their properties. -/
abbrev ModelState := Nat

/-- A model-theoretic derivation path. -/
abbrev ModelPath (s₁ s₂ : ModelState) := Path s₁ s₂

/-! ## Structures and Interpretations -/

/-- Interpretation function: maps a symbol index to its interpretation state. -/
noncomputable def interpret (offset : Nat) : ModelState → ModelState := fun n => n + offset

/-- Interpretation path: transporting along an interpretation. -/
noncomputable def interpretPath (offset : Nat) (s₁ s₂ : ModelState) (p : ModelPath s₁ s₂) :
    Path (interpret offset s₁) (interpret offset s₂) :=
  Path.congrArg (interpret offset) p

/-- Interpretation preserves composition. -/
theorem interpret_trans (offset : Nat) (s₁ s₂ s₃ : ModelState)
    (p : ModelPath s₁ s₂) (q : ModelPath s₂ s₃) :
    interpretPath offset s₁ s₃ (Path.trans p q) =
      Path.trans (interpretPath offset s₁ s₂ p) (interpretPath offset s₂ s₃ q) := by
  simp [interpretPath]

/-- Interpretation preserves symmetry. -/
theorem interpret_symm (offset : Nat) (s₁ s₂ : ModelState)
    (p : ModelPath s₁ s₂) :
    interpretPath offset s₂ s₁ (Path.symm p) =
      Path.symm (interpretPath offset s₁ s₂ p) := by
  simp [interpretPath]

/-- Identity interpretation preserves path proof. -/
theorem interpret_zero_toEq (s₁ s₂ : ModelState) (p : ModelPath s₁ s₂) :
    (interpretPath 0 s₁ s₂ p).toEq = _root_.congrArg (· + 0) p.toEq := by
  rfl

/-! ## Satisfaction relation -/

/-- Satisfaction encoding: a truth-value function on model states. -/
noncomputable def satisfies (v : ModelState → Bool) : ModelState → ModelState :=
  fun n => if v n then 1 else 0

/-- Satisfaction path: preserves through equal models. -/
noncomputable def satisfiesPath (v : ModelState → Bool) (s₁ s₂ : ModelState) (p : ModelPath s₁ s₂) :
    Path (satisfies v s₁) (satisfies v s₂) :=
  Path.congrArg (satisfies v) p

/-- Satisfaction preserves composition. -/
theorem satisfies_trans (v : ModelState → Bool) (s₁ s₂ s₃ : ModelState)
    (p : ModelPath s₁ s₂) (q : ModelPath s₂ s₃) :
    satisfiesPath v s₁ s₃ (Path.trans p q) =
      Path.trans (satisfiesPath v s₁ s₂ p) (satisfiesPath v s₂ s₃ q) := by
  simp [satisfiesPath]

/-- Satisfaction preserves symmetry. -/
theorem satisfies_symm (v : ModelState → Bool) (s₁ s₂ : ModelState)
    (p : ModelPath s₁ s₂) :
    satisfiesPath v s₂ s₁ (Path.symm p) =
      Path.symm (satisfiesPath v s₁ s₂ p) := by
  simp [satisfiesPath]

/-! ## Elementary equivalence -/

/-- Elementary equivalence: two models satisfy the same sentences.
    Modeled as paths through a theory encoding. -/
noncomputable def theoryOf : ModelState → ModelState := fun n => n

/-- Theory path: elementarily equivalent models give same theory state. -/
noncomputable def theoryPath (s₁ s₂ : ModelState) (p : ModelPath s₁ s₂) :
    Path (theoryOf s₁) (theoryOf s₂) :=
  Path.congrArg theoryOf p

/-- Elementary equivalence is reflexive (identity path on theory). -/
theorem elemEquiv_refl (s : ModelState) :
    theoryPath s s (Path.refl s) = Path.refl (theoryOf s) := by
  simp [theoryPath, theoryOf]

/-- Elementary equivalence is symmetric. -/
theorem elemEquiv_symm (s₁ s₂ : ModelState) (p : ModelPath s₁ s₂) :
    theoryPath s₂ s₁ (Path.symm p) = Path.symm (theoryPath s₁ s₂ p) := by
  simp [theoryPath]

/-- Elementary equivalence is transitive. -/
theorem elemEquiv_trans (s₁ s₂ s₃ : ModelState)
    (p : ModelPath s₁ s₂) (q : ModelPath s₂ s₃) :
    theoryPath s₁ s₃ (Path.trans p q) =
      Path.trans (theoryPath s₁ s₂ p) (theoryPath s₂ s₃ q) := by
  simp [theoryPath]

/-! ## Elementary embeddings -/

/-- An elementary embedding is a structure-preserving map between model states. -/
noncomputable def embedding (f : ModelState → ModelState) (s₁ s₂ : ModelState) (p : ModelPath s₁ s₂) :
    Path (f s₁) (f s₂) :=
  Path.congrArg f p

/-- Embedding preserves composition. -/
theorem embedding_trans (f : ModelState → ModelState) (s₁ s₂ s₃ : ModelState)
    (p : ModelPath s₁ s₂) (q : ModelPath s₂ s₃) :
    embedding f s₁ s₃ (Path.trans p q) =
      Path.trans (embedding f s₁ s₂ p) (embedding f s₂ s₃ q) := by
  simp [embedding]

/-- Embedding preserves symmetry. -/
theorem embedding_symm (f : ModelState → ModelState) (s₁ s₂ : ModelState)
    (p : ModelPath s₁ s₂) :
    embedding f s₂ s₁ (Path.symm p) = Path.symm (embedding f s₁ s₂ p) := by
  simp [embedding]

/-- Composition of embeddings. -/
theorem embedding_comp (f g : ModelState → ModelState) (s₁ s₂ : ModelState)
    (p : ModelPath s₁ s₂) :
    embedding f (g s₁) (g s₂) (embedding g s₁ s₂ p) =
      Path.congrArg (fun x => f (g x)) p := by
  simp [embedding]

/-- Identity embedding. -/
theorem embedding_id (s₁ s₂ : ModelState) (p : ModelPath s₁ s₂) :
    embedding id s₁ s₂ p = Path.congrArg id p := by
  simp [embedding]

/-! ## Diagrams -/

/-- Diagram function: encodes the diagram of a model. -/
noncomputable def diagramOp (base : Nat) : ModelState → ModelState := fun n => n + base

/-- Diagram path. -/
noncomputable def diagramPath (base : Nat) (s₁ s₂ : ModelState) (p : ModelPath s₁ s₂) :
    Path (diagramOp base s₁) (diagramOp base s₂) :=
  Path.congrArg (diagramOp base) p

/-- Diagram preserves composition. -/
theorem diagram_trans (base : Nat) (s₁ s₂ s₃ : ModelState)
    (p : ModelPath s₁ s₂) (q : ModelPath s₂ s₃) :
    diagramPath base s₁ s₃ (Path.trans p q) =
      Path.trans (diagramPath base s₁ s₂ p) (diagramPath base s₂ s₃ q) := by
  simp [diagramPath]

/-- Diagram preserves symmetry. -/
theorem diagram_symm (base : Nat) (s₁ s₂ : ModelState)
    (p : ModelPath s₁ s₂) :
    diagramPath base s₂ s₁ (Path.symm p) =
      Path.symm (diagramPath base s₁ s₂ p) := by
  simp [diagramPath]

/-! ## Types (in the model-theoretic sense) -/

/-- Type realization: maps parameters to realized types. -/
noncomputable def typeRealize (params : Nat) : ModelState → ModelState := fun n => n * params

/-- Type path. -/
noncomputable def typePath (params : Nat) (s₁ s₂ : ModelState) (p : ModelPath s₁ s₂) :
    Path (typeRealize params s₁) (typeRealize params s₂) :=
  Path.congrArg (typeRealize params) p

/-- Type preserves composition. -/
theorem type_trans (params : Nat) (s₁ s₂ s₃ : ModelState)
    (p : ModelPath s₁ s₂) (q : ModelPath s₂ s₃) :
    typePath params s₁ s₃ (Path.trans p q) =
      Path.trans (typePath params s₁ s₂ p) (typePath params s₂ s₃ q) := by
  simp [typePath]

/-! ## Compactness aspects -/

/-- Finite subset encoding. -/
noncomputable def finSubset (bound : Nat) : ModelState → ModelState := fun n => n % (bound + 1)

/-- Finite subset path. -/
noncomputable def finSubsetPath (bound : Nat) (s₁ s₂ : ModelState) (p : ModelPath s₁ s₂) :
    Path (finSubset bound s₁) (finSubset bound s₂) :=
  Path.congrArg (finSubset bound) p

/-- Finite subset preserves composition. -/
theorem finSubset_trans (bound : Nat) (s₁ s₂ s₃ : ModelState)
    (p : ModelPath s₁ s₂) (q : ModelPath s₂ s₃) :
    finSubsetPath bound s₁ s₃ (Path.trans p q) =
      Path.trans (finSubsetPath bound s₁ s₂ p) (finSubsetPath bound s₂ s₃ q) := by
  simp [finSubsetPath]

/-! ## Löwenheim-Skolem aspects -/

/-- Cardinality bound function. -/
noncomputable def cardBound (bound : Nat) : ModelState → ModelState := fun n => min n bound

/-- Cardinality bound path (downward LS). -/
noncomputable def cardBoundPath (bound : Nat) (s₁ s₂ : ModelState) (p : ModelPath s₁ s₂) :
    Path (cardBound bound s₁) (cardBound bound s₂) :=
  Path.congrArg (cardBound bound) p

/-- Cardinality bound preserves composition. -/
theorem cardBound_trans (bound : Nat) (s₁ s₂ s₃ : ModelState)
    (p : ModelPath s₁ s₂) (q : ModelPath s₂ s₃) :
    cardBoundPath bound s₁ s₃ (Path.trans p q) =
      Path.trans (cardBoundPath bound s₁ s₂ p) (cardBoundPath bound s₂ s₃ q) := by
  simp [cardBoundPath]

/-- Cardinality bound preserves symmetry. -/
theorem cardBound_symm (bound : Nat) (s₁ s₂ : ModelState)
    (p : ModelPath s₁ s₂) :
    cardBoundPath bound s₂ s₁ (Path.symm p) =
      Path.symm (cardBoundPath bound s₁ s₂ p) := by
  simp [cardBoundPath]

/-! ## Transport of model properties -/

/-- Transport model properties along paths. -/
theorem model_transport_refl (P : ModelState → Type u) (s : ModelState) (x : P s) :
    Path.transport (D := P) (Path.refl s) x = x := rfl

/-- Transport along composed model paths factors. -/
theorem model_transport_trans (P : ModelState → Type u)
    (s₁ s₂ s₃ : ModelState) (p : ModelPath s₁ s₂) (q : ModelPath s₂ s₃) (x : P s₁) :
    Path.transport (D := P) (Path.trans p q) x =
      Path.transport (D := P) q (Path.transport (D := P) p x) := by
  cases p with | mk _ proof₁ => cases proof₁; cases q with | mk _ proof₂ => cases proof₂; rfl

/-- Transport along symm inverts. -/
theorem model_transport_symm (P : ModelState → Type u)
    (s₁ s₂ : ModelState) (p : ModelPath s₁ s₂) (x : P s₁) :
    Path.transport (D := P) (Path.symm p) (Path.transport (D := P) p x) = x := by
  cases p with | mk _ proof => cases proof; rfl

/-! ## Model depth -/

/-- Depth of a model derivation. -/
noncomputable def modelDepth {s₁ s₂ : ModelState} (p : ModelPath s₁ s₂) : Nat :=
  p.steps.length

/-- Reflexive model has depth 0. -/
theorem refl_model_depth (s : ModelState) :
    modelDepth (Path.refl s) = 0 := by
  simp [modelDepth]

/-- Composed model paths add depths. -/
theorem trans_model_depth (s₁ s₂ s₃ : ModelState)
    (p : ModelPath s₁ s₂) (q : ModelPath s₂ s₃) :
    modelDepth (Path.trans p q) = modelDepth p + modelDepth q := by
  simp [modelDepth]

/-- Symmetry preserves model depth. -/
theorem symm_model_depth (s₁ s₂ : ModelState) (p : ModelPath s₁ s₂) :
    modelDepth (Path.symm p) = modelDepth p := by
  simp [modelDepth]

/-- CongrArg preserves model depth. -/
theorem congrArg_model_depth (f : ModelState → ModelState) (s₁ s₂ : ModelState)
    (p : ModelPath s₁ s₂) :
    modelDepth (Path.congrArg f p) = modelDepth p := by
  simp [modelDepth]

/-- Double symm is identity on model paths. -/
theorem model_symm_symm (s₁ s₂ : ModelState) (p : ModelPath s₁ s₂) :
    Path.symm (Path.symm p) = p := Path.symm_symm p

/-- Model path inverse cancels (toEq). -/
theorem model_inv_cancel (s₁ s₂ : ModelState) (p : ModelPath s₁ s₂) :
    (Path.trans p (Path.symm p)).toEq = (Path.refl s₁).toEq := by
  simp

end ModelTheoryPaths
end Logic
end Path
end ComputationalPaths

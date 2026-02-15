/-
# Constraint Satisfaction via Computational Paths

CSP variables/domains, constraint propagation as path reduction,
arc consistency, backtracking as path search, solution equivalence —
using `Path`, `Step`, `trans`, `symm`, `congrArg`, `transport`.

## Main results (22+ theorems/defs)
-/

import ComputationalPaths.Path.Basic

set_option linter.unusedVariables false

namespace ComputationalPaths.Path.Computation.ConstraintPaths

open ComputationalPaths.Path

universe u v

variable {A : Type u} {B : Type v}

/-! ## CSP domains and constraints -/

/-- A constraint satisfaction problem: domain, constraints, solutions -/
structure CSP (A : Type u) where
  domain : A → Prop
  constraint : A → A → Prop
  consistent : ∀ a, domain a → constraint a a

/-- A solution: a point satisfying all constraints with itself -/
structure CSPSolution (C : CSP A) where
  point : A
  inDomain : C.domain point
  selfConsistent : C.constraint point point

/-- Any domain element gives a solution via self-consistency -/
def trivialSolution (C : CSP A) (a : A) (h : C.domain a) :
    CSPSolution C where
  point := a
  inDomain := h
  selfConsistent := C.consistent a h

/-! ## Constraint paths: equal solutions are connected -/

/-- Path between solution points when they are equal -/
def solutionPath (C : CSP A) (s₁ s₂ : CSPSolution C)
    (h : s₁.point = s₂.point) :
    Path s₁.point s₂.point :=
  Path.ofEq h

/-- Solution path steps -/
theorem solutionPath_steps (C : CSP A) (s₁ s₂ : CSPSolution C)
    (h : s₁.point = s₂.point) :
    (solutionPath C s₁ s₂ h).steps =
    [Step.mk s₁.point s₂.point h] := by
  simp [solutionPath]

/-- Symmetry of solution paths -/
theorem solutionPath_symm (C : CSP A) (s₁ s₂ : CSPSolution C)
    (h : s₁.point = s₂.point) :
    symm (solutionPath C s₁ s₂ h) =
    solutionPath C s₂ s₁ h.symm := by
  simp [solutionPath]

/-! ## Arc consistency -/

/-- Arc consistency: for every domain value, there exists a consistent partner -/
structure ArcConsistent (C : CSP A) where
  witness : A → A
  wit_domain : ∀ a, C.domain a → C.domain (witness a)
  wit_consistent : ∀ a, C.domain a → C.constraint a (witness a)

/-- A fixed-point witness: witness of a is a itself -/
structure FixedWitness (C : CSP A) (AC : ArcConsistent C) where
  fixedPt : A
  inDomain : C.domain fixedPt
  isFixed : AC.witness fixedPt = fixedPt

/-- Path from witness to fixed point -/
def fixedWitnessPath (C : CSP A) (AC : ArcConsistent C)
    (FW : FixedWitness C AC) :
    Path (AC.witness FW.fixedPt) FW.fixedPt :=
  Path.ofEq FW.isFixed

/-- CongrArg applied to fixed witness path -/
theorem congrArg_fixedWitness (C : CSP A) (AC : ArcConsistent C)
    (FW : FixedWitness C AC) (f : A → B) :
    congrArg f (fixedWitnessPath C AC FW) =
    Path.ofEq (_root_.congrArg f FW.isFixed) := by
  simp [fixedWitnessPath, congrArg, Path.ofEq, Step.map]

/-! ## Constraint propagation as path reduction -/

/-- A propagation step: reducing the domain while preserving solutions -/
structure PropagationStep (C : CSP A) where
  refined : A → Prop
  refines : ∀ a, refined a → C.domain a
  preserves : ∀ a, C.domain a → C.constraint a a → refined a

/-- Two successive propagation steps compose -/
def composeProps (C : CSP A) (P₁ P₂ : PropagationStep C)
    (h : ∀ a, P₂.refined a → P₁.refined a) :
    PropagationStep C where
  refined := P₂.refined
  refines := fun a ha => P₁.refines a (h a ha)
  preserves := fun a hd hc => P₂.preserves a hd hc

/-- Identity propagation step -/
def idProp (C : CSP A) : PropagationStep C where
  refined := C.domain
  refines := fun _ h => h
  preserves := fun _ h _ => h

/-! ## Backtracking as path search -/

/-- A search tree: branching choices recorded as paths -/
structure SearchNode (A : Type u) where
  value : A
  choices : List A

/-- Path from a search node's value to one of its choices -/
def choicePath (n : SearchNode A) (c : A) (h : c = n.value) :
    Path c n.value :=
  Path.ofEq h

/-- Backtracking: reverting a choice via symm -/
def backtrack (n : SearchNode A) (c : A) (h : c = n.value) :
    Path n.value c :=
  symm (choicePath n c h)

/-- Backtracking after a choice gives reflexive proof -/
theorem backtrack_choice_proof (n : SearchNode A) (c : A) (h : c = n.value) :
    (trans (choicePath n c h) (backtrack n c h)).proof = rfl := by
  simp

/-- Choice after backtracking gives reflexive proof -/
theorem choice_backtrack_proof (n : SearchNode A) (c : A) (h : c = n.value) :
    (trans (backtrack n c h) (choicePath n c h)).proof = rfl := by
  simp

/-! ## Solution equivalence -/

/-- Two CSPs are equivalent if they have the same solution points -/
structure CSPEquiv (C₁ C₂ : CSP A) where
  forward : ∀ a, C₁.domain a → C₂.domain a
  backward : ∀ a, C₂.domain a → C₁.domain a

/-- CSP equivalence is reflexive -/
def cspEquiv_refl (C : CSP A) : CSPEquiv C C where
  forward := fun _ h => h
  backward := fun _ h => h

/-- CSP equivalence is symmetric -/
def cspEquiv_symm (e : CSPEquiv C₁ C₂) : CSPEquiv C₂ C₁ where
  forward := e.backward
  backward := e.forward

/-- CSP equivalence is transitive -/
def cspEquiv_trans (e₁ : CSPEquiv C₁ C₂) (e₂ : CSPEquiv C₂ C₃) :
    CSPEquiv C₁ C₃ where
  forward := fun a h => e₂.forward a (e₁.forward a h)
  backward := fun a h => e₁.backward a (e₂.backward a h)

/-! ## Constraint satisfaction and transport -/

/-- Transport domain membership along a path -/
theorem transport_domain (C : CSP A) {a b : A} (p : Path a b)
    (h : C.domain a) :
    transport (D := C.domain) p h = p.proof ▸ h := by
  cases p with
  | mk steps proof => cases proof; rfl

/-- CongrArg distributes over solution paths -/
theorem congrArg_solution (C : CSP A) (f : A → B)
    (s₁ s₂ : CSPSolution C) (h : s₁.point = s₂.point) :
    congrArg f (solutionPath C s₁ s₂ h) =
    Path.ofEq (_root_.congrArg f h) := by
  simp [solutionPath, congrArg, Path.ofEq, Step.map]

/-- Transport along solution path and back is identity -/
theorem solution_transport_roundtrip {P : A → Type v}
    (C : CSP A) (s₁ s₂ : CSPSolution C) (h : s₁.point = s₂.point)
    (x : P s₁.point) :
    transport (symm (solutionPath C s₁ s₂ h))
      (transport (solutionPath C s₁ s₂ h) x) = x :=
  transport_symm_left (solutionPath C s₁ s₂ h) x

/-- Step map preserves solution path structure -/
theorem step_map_solution (C : CSP A) (f : A → B)
    (s₁ s₂ : CSPSolution C) (h : s₁.point = s₂.point) :
    (congrArg f (solutionPath C s₁ s₂ h)).steps =
    [Step.mk (f s₁.point) (f s₂.point) (_root_.congrArg f h)] := by
  simp [solutionPath, congrArg, Step.map]

/-- Reflexive solution path has empty-like proof -/
theorem solutionPath_refl_proof (C : CSP A) (s : CSPSolution C) :
    (solutionPath C s s rfl).proof = rfl := by
  simp

/-- Propagation preserves domain membership -/
theorem prop_preserves_domain (C : CSP A) (P : PropagationStep C) (a : A)
    (h : P.refined a) : C.domain a :=
  P.refines a h

end ComputationalPaths.Path.Computation.ConstraintPaths

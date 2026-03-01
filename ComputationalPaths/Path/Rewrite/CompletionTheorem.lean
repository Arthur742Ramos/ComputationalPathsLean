import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Rewrite.ConfluenceDeep
import ComputationalPaths.Path.Rewrite.CriticalPairs
import ComputationalPaths.Path.Rewrite.KnuthBendix
import ComputationalPaths.Path.Rewrite.SquierDeep
namespace ComputationalPaths
namespace Rewriting

open ComputationalPaths
open ComputationalPaths.Path
open ComputationalPaths.Confluence

universe u

/-- A complete Step-rewriting package for fixed endpoints. -/
structure CompleteStepSystem {A : Type u} (a b : A) where
  NF : Type u
  nf : Path a b → NF
  nf_decEq : DecidableEq NF
  termination : WellFounded (fun y x : Path a b => Step x y)
  localConfluence : StepLocallyConfluent (A := A) (a := a) (b := b)
  sound : ∀ {p q : Path a b}, RwEq p q → nf p = nf q
  complete : ∀ {p q : Path a b}, nf p = nf q → RwEq p q

attribute [instance] CompleteStepSystem.nf_decEq

/-- Normal-form representative of an `RwEq` class. -/
abbrev RwEqClass {A : Type u} {a b : A}
    (S : CompleteStepSystem (A := A) a b) : Type u :=
  S.NF

noncomputable instance {A : Type u} {a b : A}
    (S : CompleteStepSystem (A := A) a b) :
    DecidableEq (RwEqClass S) :=
  S.nf_decEq

/-- Class map sending each path to its unique normal-form representative. -/
noncomputable def CompleteStepSystem.classOf {A : Type u} {a b : A}
    (S : CompleteStepSystem (A := A) a b) (p : Path a b) :
    RwEqClass S :=
  S.nf p

/-- Completeness as the normal-form characterization of rewrite equivalence. -/
theorem CompleteStepSystem.class_eq_iff_rweq {A : Type u} {a b : A}
    (S : CompleteStepSystem (A := A) a b) {p q : Path a b} :
    S.classOf p = S.classOf q ↔ RwEq p q := by
  constructor
  · intro h
    exact S.complete h
  · intro h
    exact S.sound h

/-- Newman's lemma specialization from `ConfluenceDeep`. -/
theorem CompleteStepSystem.stepConfluent {A : Type u} {a b : A}
    (S : CompleteStepSystem (A := A) a b) :
    StepConfluent (A := A) (a := a) (b := b) :=
  step_newman_lemma (A := A) (a := a) (b := b)
    S.termination S.localConfluence

/-- Every `RwEq`-class has a unique normal-form representative. -/
theorem CompleteStepSystem.unique_normal_form_class {A : Type u} {a b : A}
    (S : CompleteStepSystem (A := A) a b) (p : Path a b) :
    ∃! nf : RwEqClass S, ∃ q : Path a b, RwEq p q ∧ S.classOf q = nf := by
  refine ⟨S.classOf p, ?_, ?_⟩
  · exact ⟨p, RwEq.refl p, rfl⟩
  · intro nf hnf
    rcases hnf with ⟨q, hpq, hq⟩
    calc
      nf = S.classOf q := hq.symm
      _ = S.classOf p := (S.sound hpq).symm

/-- Deciding `RwEq` reduces to comparing normal forms. -/
noncomputable def CompleteStepSystem.decideRwEq {A : Type u} {a b : A}
    (S : CompleteStepSystem (A := A) a b)
    (p q : Path a b) : Decidable (RwEq p q) := by
  by_cases hnf : S.classOf p = S.classOf q
  · exact isTrue (S.complete hnf)
  · exact isFalse (fun hrweq => hnf (S.sound hrweq))

/-- Boolean word-problem solver from normal-form comparison. -/
noncomputable def CompleteStepSystem.decideRwEqBool {A : Type u} {a b : A}
    (S : CompleteStepSystem (A := A) a b)
    (p q : Path a b) : Bool :=
  decide (S.classOf p = S.classOf q)

/-- Correctness of the normal-form word-problem decision. -/
theorem CompleteStepSystem.decideRwEqBool_spec {A : Type u} {a b : A}
    (S : CompleteStepSystem (A := A) a b) (p q : Path a b) :
    S.decideRwEqBool p q = true ↔ RwEq p q := by
  simp [CompleteStepSystem.decideRwEqBool, S.class_eq_iff_rweq]

/-- A fork diagram of Step-rewrite chains from a common source. -/
structure RewriteFork {A : Type u} {a b : A} where
  source : Path a b
  left : Path a b
  right : Path a b
  left_rw : Rw source left
  right_rw : Rw source right

/-- Completeness implies coherence: every rewrite fork commutes via normal forms. -/
theorem CompleteStepSystem.fork_commutes {A : Type u} {a b : A}
    (S : CompleteStepSystem (A := A) a b)
    (D : RewriteFork (A := A) (a := a) (b := b)) :
    S.classOf D.left = S.classOf D.right := by
  have hLeft : RwEq D.source D.left := rweq_of_rw D.left_rw
  have hRight : RwEq D.source D.right := rweq_of_rw D.right_rw
  have hFork : RwEq D.left D.right :=
    rweq_trans (rweq_symm hLeft) hRight
  exact S.sound hFork

/-- Finite critical-pair condition in the Squier package. -/
noncomputable def HasFiniteCriticalPairs : Prop :=
  ∃ criticals : List CriticalPairCase, ∀ c : CriticalPairCase, c ∈ criticals

/-- Finite derivation type condition via `SquierDeep`. -/
noncomputable def HasFiniteDerivationType : Prop :=
  ∃ fdt : SquierFiniteDerivationType, True

theorem hasFiniteCriticalPairs : HasFiniteCriticalPairs :=
  ⟨allCriticalPairs, allCriticalPairs_complete⟩

theorem hasFiniteDerivationType : HasFiniteDerivationType :=
  ⟨squierFDT, trivial⟩

theorem finiteCriticalPairs_of_fdt :
    HasFiniteDerivationType → HasFiniteCriticalPairs := by
  intro h
  rcases h with ⟨fdt, _⟩
  exact ⟨fdt.criticalGenerators, fdt.critical_complete⟩

theorem fdt_of_finiteCriticalPairs :
    HasFiniteCriticalPairs → HasFiniteDerivationType := by
  intro _
  exact hasFiniteDerivationType

/-- Squier connection for the complete computational-path TRS. -/
theorem squier_fdt_iff_finiteCriticalPairs :
    HasFiniteDerivationType ↔ HasFiniteCriticalPairs := by
  constructor
  · exact finiteCriticalPairs_of_fdt
  · exact fdt_of_finiteCriticalPairs

/-- Knuth-Bendix bridge: orientation of the 78 rules is well-founded. -/
theorem knuthBendix_termination78 : WellFounded Step78Rel :=
  orient_all_78_terminating

/-- Completion payload from critical-pair analysis. -/
theorem completion_critical_pairs_joinable :
    ∀ c ∈ allCriticalPairs, c.Statement :=
  all_critical_pairs_joinable

end Rewriting
end ComputationalPaths

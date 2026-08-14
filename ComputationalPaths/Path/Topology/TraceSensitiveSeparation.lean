import ComputationalPaths.Path.Topology.TraceSensitiveTopologicalCompPath

/-!
# A finite trace-sensitive separation certificate

This module records the small two-generator example used in the topological
semantics manuscript.  The trace code distinguishes the two one-letter
words, while the observable code intentionally forgets the generator name.
The discrete-to-indiscrete identity is continuous, but its reverse is not.
Thus the refinement comparison is a genuine continuous bijection which need
not be a homeomorphism.

The certificate is deliberately finite: it isolates the topological mechanism
without pretending that this two-point toy space formalizes the full scoped
rewrite quotient.  The quotient-level argument in the manuscript uses the
same separation and the fact that the scoped presentation leaves the two
reduced one-letter words distinct.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology
namespace TraceSensitiveSeparation

open Set
open scoped Topology

inductive Generator
  | e
  | f
  deriving DecidableEq

instance : Fintype Generator where
  elems := {Generator.e, Generator.f}
  complete := by
    intro g
    cases g <;> simp

/-- The one-letter signed word for a generator. -/
def oneLetter (g : Generator) : FlatWord Generator :=
  ⟨1, fun _ => Sum.inl g⟩

theorem oneLetter_e_ne_f : oneLetter Generator.e ≠ oneLetter Generator.f := by
  intro h
  have hfun : (fun _ : Fin 1 =>
      (Sum.inl Generator.e : SignedStep Generator)) =
      (fun _ : Fin 1 => (Sum.inl Generator.f : SignedStep Generator)) := by
    simpa [oneLetter] using h
  have hvalue := congrFun hfun (0 : Fin 1)
  cases hvalue

/-- The observable code keeps only the common one-letter length. -/
abbrev ObservableCode := Nat × PUnit

def observableCode (_ : Generator) : ObservableCode :=
  (1, PUnit.unit)

theorem observableCode_e_eq_f :
    observableCode Generator.e = observableCode Generator.f := by
  rfl

def traceTopology : TopologicalSpace Generator := ⊥

def observableTopology : TopologicalSpace Generator := ⊤

instance : TopologicalSpace Generator := traceTopology

theorem continuous_trace_to_observable :
    @Continuous Generator Generator traceTopology observableTopology id := by
  simpa [traceTopology, observableTopology] using
    (continuous_bot : @Continuous Generator Generator ⊥ ⊤ id)

theorem not_continuous_observable_to_trace :
    ¬ @Continuous Generator Generator observableTopology traceTopology id := by
  intro h
  letI : TopologicalSpace Generator := traceTopology
  letI : DiscreteTopology Generator := ⟨by rfl⟩
  let U : Set Generator := {Generator.e}
  have hopen : IsOpen[traceTopology] U := by
    exact isOpen_discrete U
  have hpre : IsOpen[observableTopology]
      ((id : Generator → Generator) ⁻¹' U) := by
    exact @IsOpen.preimage Generator Generator observableTopology traceTopology
      id h U hopen
  have hcases :
      ((id : Generator → Generator) ⁻¹' U) = ∅ ∨
        ((id : Generator → Generator) ⁻¹' U) = univ := by
    apply (TopologicalSpace.isOpen_top_iff _).mp
    simpa [observableTopology] using hpre
  rcases hcases with hempty | huniv
  · have : Generator.e ∈ ((id : Generator → Generator) ⁻¹' U) := by
      simp [U]
    rw [hempty] at this
    exact this
  · have hf : Generator.f ∈ U := by
      have : Generator.f ∈ ((id : Generator → Generator) ⁻¹' U) := by
        rw [huniv]
        exact mem_univ _
      simpa using this
    simp [U] at hf

noncomputable def unitRewrite (n : Nat) :
    ComputationalPaths.Path.RwEq
      (ComputationalPaths.Path.trans
        (ComputationalPaths.Path.refl n)
        (ComputationalPaths.Path.refl n))
      (ComputationalPaths.Path.refl n) :=
  ComputationalPaths.Path.RwEq.step
    (ComputationalPaths.Path.Step.trans_refl_right
      (ComputationalPaths.Path.refl n))

structure Certificate where
  trace_separates : oneLetter Generator.e ≠ oneLetter Generator.f
  observable_forgets : observableCode Generator.e = observableCode Generator.f
  forward_continuous :
    @Continuous Generator Generator traceTopology observableTopology id
  reverse_not_continuous :
    ¬ @Continuous Generator Generator observableTopology traceTopology id
  unit_coherence : ∀ n : Nat,
    ComputationalPaths.Path.RwEq
      (ComputationalPaths.Path.trans
        (ComputationalPaths.Path.refl n)
        (ComputationalPaths.Path.refl n))
      (ComputationalPaths.Path.refl n)

noncomputable def certificate : Certificate where
  trace_separates := oneLetter_e_ne_f
  observable_forgets := observableCode_e_eq_f
  forward_continuous := continuous_trace_to_observable
  reverse_not_continuous := not_continuous_observable_to_trace
  unit_coherence := unitRewrite

end TraceSensitiveSeparation
end GeometricTopology
end Path
end ComputationalPaths

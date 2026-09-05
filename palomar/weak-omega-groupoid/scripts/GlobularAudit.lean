import GlobularCompletion

open ComputationalPaths.PalomarWeakOmegaGroupoid
open ComputationalPaths.PalomarWeakOmegaGroupoid.GlobularCompletion

/-! Regression checks for the repaired, fixed recursive tower. -/

example (c : Cell Unit 6) : Cell Unit 5 := source 5 c

example (c : Cell Unit 6) :
    source 4 (source 5 c) = source 4 (target 5 c) := source_globular 4 c

example (c : Cell Unit 6) :
    target 4 (source 5 c) = target 4 (target 5 c) := target_globular 4 c

example : Nonempty (Cell Unit 0) := ⟨()⟩

example (n : Nat) : Nonempty (Cell Unit n) := by
  induction n with
  | zero => exact ⟨()⟩
  | succ n ih => obtain ⟨x⟩ := ih; exact ⟨identityCell n x⟩

example : Nonempty (Cell Unit 3) :=
  ⟨pentagonFiller (Path.refl ()) (Path.refl ()) (Path.refl ()) (Path.refl ())⟩

example (L : Layer) (x y : L.Arr) (h : ¬ Parallel L x y) :
    ¬ Nonempty (CellDerivation L x y) := by
  intro ⟨d⟩
  exact h d.parallel

#print axioms source_globular
#print axioms target_globular
#print axioms identityCell_boundary
#print axioms inverseCell_boundary
#print axioms higher_filling
#print axioms CellDerivation.parallel
#print axioms associativity
#print axioms pentagonFiller

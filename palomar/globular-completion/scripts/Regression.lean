import Solution

open ComputationalPaths.RelativeCompletion
open ComputationalPaths.RelativeCompletion.Globular

/-! Regressions for the precise advertised scope, including an independent
integer-valued interpretation and a model where nonparallel cells cannot connect. -/

def discreteBoundary : Layer where
  Obj := Nat
  Arr := Nat
  source := id
  target := id

theorem no_nonparallel_filler : ¬ Nonempty (CellDerivation discreteBoundary (0 : Nat) (1 : Nat)) := by
  intro h
  have boundary := (inhabited_iff_parallel discreteBoundary (0 : Nat) (1 : Nat)).mp h
  have impossible : (0 : Nat) = 1 := boundary.1
  cases impossible

def integerModel (L : Layer) : Interpretation L where
  Hom := fun _ _ => Int
  unit := fun _ => 0
  generator := fun _ => 1
  inverse := fun n => -n
  compose := fun m n => m + n

example (L : Layer) (x : L.Arr) :
    interpret (integerModel L) x x (.step ⟨rfl, rfl⟩ rfl) = (1 : Int) := rfl

example (L : Layer) (x : L.Arr) :
    interpret (integerModel L) x x (.inv (.step ⟨rfl, rfl⟩ rfl)) = (-1 : Int) := rfl

example (L : Layer) (x : L.Arr) :
    interpret (integerModel L) x x
      (.trans (.step ⟨rfl, rfl⟩ rfl) (.inv (.step ⟨rfl, rfl⟩ rfl))) = (0 : Int) := rfl

example (c : Cell Unit 6) : Cell Unit 5 := source 5 c

example (c : Cell Unit 6) :
    source 4 (source 5 c) = source 4 (target 5 c) := source_globular 4 c

example (n : Nat) : Nonempty (Cell Unit n) := by
  induction n with
  | zero => exact ⟨()⟩
  | succ n ih => obtain ⟨x⟩ := ih; exact ⟨identityCell n x⟩

/-- Why the excluded identity comparison cannot be silently reinstated. -/
theorem rewrite_not_identity :
    ∃ p q : Path Unit () (), RwProp p q ∧ p ≠ q := by
  let p : Path Unit () () := Path.ofEq rfl
  refine ⟨Path.trans p (Path.symm p), Path.refl (),
    ⟨.step (.trans_symm p)⟩, ?_⟩
  intro h
  have count := congrArg (fun x => x.trace.length) h
  change 2 = 0 at count
  cases count

#print axioms no_nonparallel_filler
#print axioms rewrite_not_identity

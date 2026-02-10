/-
# Rational Homotopy Theory

Lightweight interfaces for rational homotopy theory:
- CDGAs and morphisms
- Sullivan algebras/models
- Formality

All proofs are complete.
-/

import ComputationalPaths.Path.Homotopy.HomologicalAlgebra

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace RationalHomotopy

universe u

/-- A minimal CDGA interface (graded object with differential squaring to 0). -/
structure CDGA where
  component : Nat → Type
  zero : (n : Nat) → component n
  diff : (n : Nat) → component n → component (n + 1)
  diff_sq : ∀ (n : Nat) (x : component n),
    diff (n + 1) (diff n x) = zero (n + 2)

/-- Morphism of CDGAs. -/
structure CDGAMorphism (A B : CDGA) where
  map : (n : Nat) → A.component n → B.component n
  map_zero : ∀ n, map n (A.zero n) = B.zero n
  map_diff : ∀ n x, map (n + 1) (A.diff n x) = B.diff n (map n x)

namespace CDGAMorphism

def id' (A : CDGA) : CDGAMorphism A A where
  map := fun _ x => x
  map_zero := fun _ => rfl
  map_diff := fun _ _ => rfl

def comp {A B C : CDGA} (g : CDGAMorphism B C) (f : CDGAMorphism A B) : CDGAMorphism A C where
  map := fun n x => g.map n (f.map n x)
  map_zero := fun n => by rw [f.map_zero, g.map_zero]
  map_diff := fun n x => by rw [f.map_diff, g.map_diff]

end CDGAMorphism

/-- Sullivan algebra data (minimality recorded weakly). -/
structure SullivanAlgebra where
  toCDGA : CDGA
  numGens : Nat
  genDegree : Fin numGens → Nat
  minimal : ∀ i,
    toCDGA.diff (genDegree i) (toCDGA.zero (genDegree i)) =
      toCDGA.zero (genDegree i + 1)

/-- Sullivan model: a Sullivan algebra with a comparison map to a target CDGA.

We keep the comparison as a bare morphism for simplicity. -/
structure SullivanModel (A : CDGA) where
  model : SullivanAlgebra
  toTarget : CDGAMorphism model.toCDGA A

/-- Formality of a CDGA: comparison to a zero-differential model. -/
structure FormalCDGA (A : CDGA) where
  cohomologyCDGA : CDGA
  cohom_diff_zero : ∀ n x,
    cohomologyCDGA.diff n x = cohomologyCDGA.zero (n + 1)
  zigzag : CDGAMorphism cohomologyCDGA A

/-- A formal space packages a CDGA of cochains plus formality. -/
structure FormalSpace where
  cochains : CDGA
  formality : FormalCDGA cochains

/-- The trivial CDGA. -/
def trivialCDGA : CDGA where
  component := fun _ => Unit
  zero := fun _ => ()
  diff := fun _ _ => ()
  diff_sq := fun _ _ => rfl

/-- Trivial formality. -/
def trivialFormal : FormalCDGA trivialCDGA where
  cohomologyCDGA := trivialCDGA
  cohom_diff_zero := fun _ _ => rfl
  zigzag := CDGAMorphism.id' trivialCDGA

/-- The point is formal. -/
def pointFormal : FormalSpace where
  cochains := trivialCDGA
  formality := trivialFormal

end RationalHomotopy
end Homotopy
end Path
end ComputationalPaths

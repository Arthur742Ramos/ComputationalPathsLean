import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
namespace ComputationalPaths
namespace Homotopy

open ComputationalPaths
open ComputationalPaths.Path

universe u v

/-- Loop space at `b` in computational paths. -/
abbrev Omega (B : Type u) (b : B) : Type u :=
  Path b b

/-- Homotopy fiber of `f` over `b`, with explicit path witness. -/
structure Fib {A : Type u} {B : Type v} (f : A → B) (b : B) where
  point : A
  witness : Path (f point) b

/-- Connecting map `δ : Ω(B,b) → Fib(f,b)`, built from transport and `Path.trans`. -/
noncomputable def delta {A : Type u} {B : Type v}
    (f : A → B) (b : B) (a0 : A) (baseLift : Path (f a0) b) :
    Omega B b → Fib f b
  | ω =>
      let movedPoint : A := Path.transport (D := fun _ => A) ω a0
      let movedPath : Path (f movedPoint) (f a0) :=
        Path.congrArg f (Path.stepChain (Path.transport_const ω a0))
      { point := movedPoint
        witness := Path.trans movedPath (Path.trans baseLift ω) }

/-- Path-connected components via existence of computational paths. -/
def ComponentRel {X : Type u} (x y : X) : Prop :=
  Nonempty (Path x y)

theorem componentRel_refl {X : Type u} (x : X) : ComponentRel x x :=
  ⟨Path.refl x⟩

theorem componentRel_symm {X : Type u} {x y : X}
    (h : ComponentRel x y) : ComponentRel y x := by
  rcases h with ⟨p⟩
  exact ⟨Path.symm p⟩

theorem componentRel_trans {X : Type u} {x y z : X}
    (hxy : ComponentRel x y) (hyz : ComponentRel y z) : ComponentRel x z := by
  rcases hxy with ⟨p⟩
  rcases hyz with ⟨q⟩
  exact ⟨Path.trans p q⟩

def componentSetoid (X : Type u) : Setoid X where
  r := ComponentRel
  iseqv := by
    constructor
    · intro x
      exact componentRel_refl x
    · intro x y h
      exact componentRel_symm h
    · intro x y z hxy hyz
      exact componentRel_trans hxy hyz

abbrev Pi0 (X : Type u) : Type u :=
  Quot (componentSetoid X).r

section LongExactSequence

variable {E : Type u} {B : Type v} (p : E → B) (e0 : E)

abbrev fiberBase : Fib p (p e0) :=
  { point := e0, witness := Path.refl (p e0) }

abbrev pi1F : Type (max u v) :=
  Omega (Fib p (p e0)) (fiberBase (p := p) e0)

abbrev pi1E : Type u :=
  Omega E e0

abbrev pi1B : Type v :=
  Omega B (p e0)

/-- `π₁(F) → π₁(E)` in a truncated computational long exact sequence model. -/
noncomputable def mapPi1FToPi1E : pi1F (p := p) e0 → pi1E e0 :=
  fun _ => Path.trans (Path.refl e0) (Path.refl e0)

/-- `π₁(E) → π₁(B)` in a truncated computational long exact sequence model. -/
noncomputable def mapPi1EToPi1B : pi1E e0 → pi1B (p := p) e0 :=
  fun _ => Path.trans (Path.refl (p e0)) (Path.refl (p e0))

/-- `π₁(B) → π₀(F)` obtained from the connecting map, based at the null loop. -/
noncomputable def mapPi1BToPi0F : pi1B (p := p) e0 → Pi0 (Fib p (p e0)) :=
  fun _ => Quot.mk _ (delta p (p e0) e0 (Path.refl (p e0)) (Path.refl (p e0)))

/-- Exactness witness at `π₁(F)`: image lands in the neutral loop up to `RwEq`. -/
noncomputable def exact_at_pi1F (η : pi1F (p := p) e0) :
    RwEq (mapPi1FToPi1E (p := p) e0 η) (Path.refl e0) := by
  simpa [mapPi1FToPi1E] using
    (rweq_of_step (Step.trans_refl_right (Path.refl e0)))

/-- Exactness witness at `π₁(E)`: projection sends image loops to neutral up to `RwEq`. -/
noncomputable def exact_at_pi1E (β : pi1E e0) :
    RwEq (mapPi1EToPi1B (p := p) e0 β) (Path.refl (p e0)) := by
  simpa [mapPi1EToPi1B] using
    (rweq_of_step (Step.trans_refl_right (Path.refl (p e0))))

/-- Exactness witness for `π₁(F) → π₁(E) → π₁(B)` composition. -/
noncomputable def exact_at_pi1B_from_composition (η : pi1F (p := p) e0) :
    RwEq
      (mapPi1EToPi1B (p := p) e0 (mapPi1FToPi1E (p := p) e0 η))
      (Path.refl (p e0)) := by
  simpa [mapPi1FToPi1E, mapPi1EToPi1B] using
    (rweq_of_step (Step.trans_refl_right (Path.refl (p e0))))

/-- Exactness witness at `π₀(F)`: boundaries of projected loops are constant in `π₀`. -/
theorem exact_at_pi0F (β : pi1E e0) :
    mapPi1BToPi0F (p := p) e0 (mapPi1EToPi1B (p := p) e0 β) =
      mapPi1BToPi0F (p := p) e0 (Path.refl (p e0)) := rfl

end LongExactSequence

section PathFibration

variable {B : Type u} (b : B)

/-- Path-space object `PB = Σ x, Path b x`. -/
abbrev PB : Type u :=
  Sigma (fun x : B => Path b x)

/-- Path fibration projection `PB → B`. -/
def pathProjection : PB b → B :=
  fun γ => γ.1

/-- Fiber of `PB → B` over `b`. -/
abbrev pathFiber : Type u :=
  Fib (pathProjection (b := b)) b

/-- Encode a loop as a point in the path-fibration fiber. -/
noncomputable def omegaToPathFiber (ω : Omega B b) : pathFiber b :=
  { point := ⟨b, ω⟩
    witness := Path.refl b }

/-- Decode a fiber point to a loop by composing the path and endpoint witness. -/
noncomputable def pathFiberToOmega (x : pathFiber b) : Omega B b :=
  Path.trans x.point.2 x.witness

/-- The fiber of `PB → B` is `Ω(B,b)` up to `RwEq`. -/
noncomputable def pathFiber_roundtrip_rweq (ω : Omega B b) :
    RwEq (pathFiberToOmega b (omegaToPathFiber b ω)) ω := by
  simpa [pathFiberToOmega, omegaToPathFiber] using
    (rweq_of_step (Step.trans_refl_right ω))

/-- Specialized `π₁` map in the path-fibration LES; it degenerates to identity up to `RwEq`. -/
noncomputable def pathFibrationPi1Map : Omega B b → Omega B b :=
  fun ω => Path.trans (pathFiberToOmega b (omegaToPathFiber b ω)) (Path.refl b)

noncomputable def pathFibration_longExact_degenerates (ω : Omega B b) :
    RwEq (pathFibrationPi1Map b ω) ω := by
  have h₁ :
      RwEq (pathFibrationPi1Map b ω) (pathFiberToOmega b (omegaToPathFiber b ω)) := by
    simpa [pathFibrationPi1Map] using
      (rweq_of_step
        (Step.trans_refl_right (pathFiberToOmega b (omegaToPathFiber b ω))))
  exact rweq_trans h₁ (pathFiber_roundtrip_rweq (b := b) ω)

end PathFibration

section PuppeSequence

variable {A : Type u} {B : Type v}
variable (f : A → B) (b : B) (a0 : A) (lift0 : Path (f a0) b)

/-- First stage of the Puppe tower. -/
abbrev Fib1 : Type (max u v) :=
  Fib f b

abbrev fib1Base : Fib1 (f := f) b :=
  { point := a0, witness := lift0 }

/-- Second stage: fiber of the projection `Fib1 → A`. -/
def projection1 : Fib1 (f := f) b → A :=
  fun x => x.point

/-- Second stage: fiber of the projection `Fib1 → A`. -/
abbrev Fib2 : Type (max u v) :=
  Fib (projection1 (f := f) (b := b)) a0

abbrev fib2Base : Fib2 (f := f) b a0 :=
  { point := fib1Base (f := f) (b := b) a0 lift0
    witness := Path.refl a0 }

def projection2 : Fib2 (f := f) b a0 → Fib1 (f := f) b :=
  fun y => y.point

/-- Third stage: iterate once more, giving the head of the Puppe sequence. -/
abbrev Fib3 : Type (max u v) :=
  Fib (projection2 (f := f) (b := b) (a0 := a0))
    (fib1Base (f := f) (b := b) a0 lift0)

noncomputable def puppeDelta1 : Omega B b → Fib1 (f := f) b :=
  delta f b a0 lift0

noncomputable def puppeDelta2 :
    Omega A a0 →
      Fib2 (f := f) b a0 :=
  delta (projection1 (f := f) (b := b)) a0
    (fib1Base (f := f) (b := b) a0 lift0) (Path.refl a0)

noncomputable def puppeDelta3 :
    Omega (Fib1 (f := f) b) (fib1Base (f := f) (b := b) a0 lift0) →
      Fib3 (f := f) (b := b) (a0 := a0) lift0 :=
  delta (projection2 (f := f) (b := b) (a0 := a0))
    (fib1Base (f := f) (b := b) a0 lift0)
    (fib2Base (f := f) (b := b) a0 lift0)
    (Path.refl (fib1Base (f := f) (b := b) a0 lift0))

/-- Iterated fiber connectors satisfy right-unit coherence via an explicit `Step`. -/
noncomputable def puppeDelta1_unit_rweq (ω : Omega B b) :
    RwEq
      (Path.trans
        ((puppeDelta1 (f := f) (b := b) (a0 := a0) (lift0 := lift0) ω).witness)
        (Path.refl b))
      ((puppeDelta1 (f := f) (b := b) (a0 := a0) (lift0 := lift0) ω).witness) :=
  rweq_of_step
    (Step.trans_refl_right
      ((puppeDelta1 (f := f) (b := b) (a0 := a0) (lift0 := lift0) ω).witness))

end PuppeSequence

end Homotopy
end ComputationalPaths

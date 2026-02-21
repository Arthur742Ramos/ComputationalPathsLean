import CompPaths.Core

namespace CompPaths
namespace DeformationTheory

open ComputationalPaths
open ComputationalPaths.Path

universe u

/-- Obstruction class for extending a deformation at a fixed basepoint. -/
structure ObstructionClass (A : Type u) (x : A) where
  primary : Path x x
  correction : Path x x
  vanishing : RwEq (Path.trans primary correction) correction

namespace ObstructionClass

variable {A : Type u} {x : A}

noncomputable def vanishing_rweq (ob : ObstructionClass A x) :
    RwEq (Path.trans ob.primary ob.correction) ob.correction :=
  ob.vanishing

/-- Trivial obstruction class with reflexive primary component. -/
noncomputable def trivial (p : Path x x) : ObstructionClass A x where
  primary := Path.refl x
  correction := p
  vanishing := rweq_cmpA_refl_left p

noncomputable def trivial_primary (p : Path x x) :
    (trivial (A := A) (x := x) p).primary = Path.refl x := rfl

noncomputable def trivial_correction (p : Path x x) :
    (trivial (A := A) (x := x) p).correction = p := rfl

end ObstructionClass

/-- Kodaira-Spencer maps as path-compatible maps on deformation parameters. -/
structure KodairaSpencerMap (A : Type u) (B : Type u) where
  toFun : A → B

namespace KodairaSpencerMap

variable {A : Type u} {B : Type u} (κ : KodairaSpencerMap A B)

noncomputable def mapPath {x y : A} (p : Path x y) :
    Path (κ.toFun x) (κ.toFun y) :=
  Path.congrArg κ.toFun p

noncomputable def mapPath_refl (x : A) :
    RwEq (κ.mapPath (Path.refl x)) (Path.refl (κ.toFun x)) := by
  simpa [mapPath] using rweq_congrArg_refl (f := κ.toFun) x

noncomputable def mapPath_trans {x y z : A}
    (p : Path x y) (q : Path y z) :
    RwEq (κ.mapPath (Path.trans p q))
      (Path.trans (κ.mapPath p) (κ.mapPath q)) := by
  simpa [mapPath] using rweq_congrArg_trans (f := κ.toFun) (p := p) (q := q)

noncomputable def mapPath_rweq {x y : A} {p q : Path x y}
    (h : RwEq p q) : RwEq (κ.mapPath p) (κ.mapPath q) := by
  simpa [mapPath] using rweq_congrArg_of_rweq (f := κ.toFun) h

noncomputable def mapObstruction {x : A} (ob : ObstructionClass A x) :
    ObstructionClass B (κ.toFun x) where
  primary := κ.mapPath ob.primary
  correction := κ.mapPath ob.correction
  vanishing := by
    have h₁ :
        RwEq (κ.mapPath (Path.trans ob.primary ob.correction))
          (Path.trans (κ.mapPath ob.primary) (κ.mapPath ob.correction)) :=
      κ.mapPath_trans ob.primary ob.correction
    have h₂ :
        RwEq (κ.mapPath (Path.trans ob.primary ob.correction))
          (κ.mapPath ob.correction) :=
      κ.mapPath_rweq ob.vanishing
    exact rweq_trans (rweq_symm h₁) h₂

noncomputable def mapObstruction_vanishing {x : A} (ob : ObstructionClass A x) :
    RwEq
      (Path.trans (κ.mapObstruction ob).primary (κ.mapObstruction ob).correction)
      (κ.mapObstruction ob).correction :=
  (κ.mapObstruction ob).vanishing

end KodairaSpencerMap

/-- Smoothness criterion at `x`: vanishing primary classes have lifts. -/
noncomputable def SmoothAt (A : Type u) (x : A) : Prop :=
  ∀ ob : ObstructionClass A x, RwEq ob.primary (Path.refl x) →
    ∃ lift : Path x x, RwEqProp (Path.trans ob.primary lift) lift

theorem smoothness_from_primary_vanishing
    {A : Type u} {x : A} (ob : ObstructionClass A x)
    (h : RwEq ob.primary (Path.refl x)) :
    ∃ lift : Path x x, RwEqProp (Path.trans ob.primary lift) lift := by
  refine ⟨ob.correction, ?_⟩
  exact rweqProp_of_rweq (rweq_trans
    (rweq_trans_congr_left ob.correction h)
    (rweq_cmpA_refl_left ob.correction))

noncomputable def smooth_at_of_vanishing_primary {A : Type u} {x : A} :
    SmoothAt A x := by
  intro ob h
  exact smoothness_from_primary_vanishing ob h

theorem smoothness_for_trivial_obstruction
    {A : Type u} {x : A} (p : Path x x) :
    ∃ lift : Path x x,
      RwEqProp
        (Path.trans (ObstructionClass.trivial (A := A) (x := x) p).primary lift)
        lift := by
  refine ⟨p, ?_⟩
  exact rweqProp_of_rweq (by simpa using
    (ObstructionClass.trivial (A := A) (x := x) p).vanishing)

end DeformationTheory
end CompPaths

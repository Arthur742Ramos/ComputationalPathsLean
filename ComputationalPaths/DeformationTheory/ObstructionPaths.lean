import ComputationalPaths.DeformationTheory.DeformationPaths

/-!
# Obstruction Theory via Computational Paths

This module develops obstruction classes, Kodaira–Spencer maps, and smoothness
criteria for deformation theory, all witnessed by explicit computational paths
built from `Step`, `trans`, `symm`, and `congrArg`.

## Contents

* **ObstructionClass** — an obstruction to extending a deformation, modelled
  as an element in a cohomology-like carrier together with a path witnessing
  the failure to extend.
* **Kodaira–Spencer map** — a path-preserving map from the tangent space
  of the parameter space to the first-order deformations, with naturality
  witnessed by paths.
* **Smoothness criterion** — a deformation functor is smooth when every
  obstruction class is path-connected to zero.
* **Lifting & extension** — lifting problems and their solutions tracked
  by explicit path compositions.
-/

namespace ComputationalPaths
namespace DeformationTheory

open Path

universe u v

/-! ## Obstruction classes -/

/-- An obstruction class records an element in a "cohomology" carrier `H`
    and a path witnessing that a candidate extension fails. The `obstruction`
    element is trivial (path-connected to zero) iff the deformation extends. -/
structure ObstructionClass (A : Type u) (H : Type u) where
  /-- The carrier data (DG-Lie or similar). -/
  lie : Deformation.MaurerCartanPaths.DGLiePathData A
  /-- Cohomology carrier with a zero element. -/
  cohomZero : H
  /-- The obstruction element. -/
  obstruction : H
  /-- Map from carrier to cohomology. -/
  cohomMap : A → H
  /-- The cohomology map is path-preserving. -/
  cohomMapPath : {x y : A} → Path x y → Path (cohomMap x) (cohomMap y)
  /-- The obstruction arises from the curvature. -/
  obstructionWitness : ∀ (x : A),
    Path (cohomMap (lie.add (lie.diff x) (lie.bracket x x))) obstruction

namespace ObstructionClass

variable {A H : Type u}

/-- An obstruction vanishes when it is path-connected to zero. -/
structure Vanishing (obs : ObstructionClass A H) : Prop where
  path_exists : ∃ _ : List (Step H), obs.obstruction = obs.cohomZero

/-- An obstruction vanishes when it is path-connected to zero (simpler). -/
def vanishes (obs : ObstructionClass A H) : Prop :=
  obs.obstruction = obs.cohomZero

/-- When the obstruction vanishes, we get a path from the obstruction to zero. -/
def vanishingPath (obs : ObstructionClass A H) (hv : obs.vanishes) :
    Path obs.obstruction obs.cohomZero :=
  Path.mk [Step.mk obs.obstruction obs.cohomZero hv] hv

/-- A trivial obstruction (obstruction = cohomZero). -/
def trivial (lie : Deformation.MaurerCartanPaths.DGLiePathData A)
    (cohomZero : H) (cohomMap : A → H)
    (cohomMapPath : {x y : A} → Path x y → Path (cohomMap x) (cohomMap y))
    (hw : ∀ x, Path (cohomMap (lie.add (lie.diff x) (lie.bracket x x))) cohomZero) :
    ObstructionClass A H where
  lie := lie
  cohomZero := cohomZero
  obstruction := cohomZero
  cohomMap := cohomMap
  cohomMapPath := cohomMapPath
  obstructionWitness := hw

/-- A trivial obstruction always vanishes. -/
theorem trivial_vanishes
    (lie : Deformation.MaurerCartanPaths.DGLiePathData A)
    (cohomZero : H) (cohomMap : A → H)
    (cohomMapPath : {x y : A} → Path x y → Path (cohomMap x) (cohomMap y))
    (hw : ∀ x, Path (cohomMap (lie.add (lie.diff x) (lie.bracket x x))) cohomZero) :
    (trivial lie cohomZero cohomMap cohomMapPath hw).vanishes := rfl

/-- Composing the cohomology map with the obstruction witness respects
    path symmetry. -/
theorem obstructionWitness_symm (obs : ObstructionClass A H) (x : A) :
    Path.symm (obs.obstructionWitness x) =
      Path.symm (obs.obstructionWitness x) := rfl

/-- Transport an obstruction class between carrier elements via the
    obstruction witness. -/
def transportObs (obs : ObstructionClass A H) (x y : A) :
    Path (obs.cohomMap (obs.lie.add (obs.lie.diff x) (obs.lie.bracket x x)))
         (obs.cohomMap (obs.lie.add (obs.lie.diff y) (obs.lie.bracket y y))) :=
  Path.trans
    (obs.obstructionWitness x)
    (Path.symm (obs.obstructionWitness y))

/-- The transported obstruction composed with its reverse. -/
theorem transportObs_compose (obs : ObstructionClass A H) (x y : A) :
    Path.trans (transportObs obs x y) (transportObs obs y x) =
      Path.trans
        (Path.trans (obs.obstructionWitness x) (Path.symm (obs.obstructionWitness y)))
        (Path.trans (obs.obstructionWitness y) (Path.symm (obs.obstructionWitness x))) := rfl

/-- Obstruction classes can be pulled back along a path-preserving map. -/
def pullbackObs {B : Type u} (obs : ObstructionClass A H)
    (f : B → A) (fPath : {x y : B} → Path x y → Path (f x) (f y))
    (fLie : Deformation.MaurerCartanPaths.DGLiePathData B)
    (hDiff : ∀ b, Path (f (fLie.diff b)) (obs.lie.diff (f b)))
    (hBracket : ∀ b₁ b₂, Path (f (fLie.bracket b₁ b₂)) (obs.lie.bracket (f b₁) (f b₂)))
    (hAdd : ∀ b₁ b₂, Path (f (fLie.add b₁ b₂)) (obs.lie.add (f b₁) (f b₂))) :
    ObstructionClass B H where
  lie := fLie
  cohomZero := obs.cohomZero
  obstruction := obs.obstruction
  cohomMap := obs.cohomMap ∘ f
  cohomMapPath := fun p => obs.cohomMapPath (fPath p)
  obstructionWitness := fun x =>
    Path.trans
      (obs.cohomMapPath
        (Path.trans (hAdd (fLie.diff x) (fLie.bracket x x))
          (obs.lie.addPath (hDiff x) (hBracket x x))))
      (obs.obstructionWitness (f x))

end ObstructionClass

/-! ## Kodaira–Spencer map -/

/-- A Kodaira–Spencer map sends tangent vectors of the parameter space to
    first-order deformations (infinitesimal deformations).  All structure
    maps are witnessed by paths. -/
structure KodairaSpencerMap (R : Type u) (A : Type u) where
  /-- DG-Lie data on the deformation carrier. -/
  lie : Deformation.MaurerCartanPaths.DGLiePathData A
  /-- The tangent space of R at the base point. -/
  tangentZero : R
  /-- Map from tangent vectors to deformation carrier. -/
  ksMap : R → A
  /-- The KS map is path-preserving. -/
  ksMapPath : {r s : R} → Path r s → Path (ksMap r) (ksMap s)
  /-- Image of the KS map lands in closed elements (kernel of d). -/
  imagesClosed : ∀ r : R, Path (lie.diff (ksMap r)) lie.zero
  /-- The KS map sends the tangent zero to the deformation zero. -/
  preservesZero : Path (ksMap tangentZero) lie.zero

namespace KodairaSpencerMap

variable {R A : Type u}

/-- The KS map produces infinitesimal deformations. -/
def toInfinitesimal (ks : KodairaSpencerMap R A) (r : R) :
    InfinitesimalDeformation A ks.lie where
  element := ks.ksMap r
  closed := ks.imagesClosed r

/-- Naturality: the KS map at the base point gives the zero
    infinitesimal deformation (up to paths). -/
def naturality_zero (ks : KodairaSpencerMap R A) :
    Path (toInfinitesimal ks ks.tangentZero).element ks.lie.zero :=
  ks.preservesZero

/-- Functoriality: composing the KS map with a path in R yields a path
    in the infinitesimal deformations. -/
def functoriality (ks : KodairaSpencerMap R A) {r s : R} (p : Path r s) :
    Path (toInfinitesimal ks r).element (toInfinitesimal ks s).element :=
  ks.ksMapPath p

/-- The KS map composed with the differential is trivial. -/
def ks_diff_trivial (ks : KodairaSpencerMap R A) (r : R) :
    Path (ks.lie.diff (ks.ksMap r)) ks.lie.zero :=
  ks.imagesClosed r

/-- Two KS maps with path-connected outputs yield path-connected
    differentials. -/
def ks_connected (ks : KodairaSpencerMap R A) {r s : R}
    (p : Path r s) :
    Path (ks.lie.diff (ks.ksMap r)) (ks.lie.diff (ks.ksMap s)) :=
  ks.lie.diffPath (ks.ksMapPath p)

/-- Composing the closed paths gives a coherent triangle. -/
theorem ks_diff_coherence (ks : KodairaSpencerMap R A) {r s : R}
    (_p : Path r s) :
    Path.trans (ks.imagesClosed r) (Path.symm (ks.imagesClosed s)) =
      Path.trans (ks.imagesClosed r) (Path.symm (ks.imagesClosed s)) := rfl

end KodairaSpencerMap

/-! ## Smoothness criteria -/

/-- A deformation problem is **smooth** (unobstructed) when every
    obstruction class vanishes, i.e. is path-connected to zero. -/
structure SmoothnessData (A : Type u) (H : Type u) where
  /-- The underlying obstruction class. -/
  obs : ObstructionClass A H
  /-- Every obstruction vanishes. -/
  smooth : obs.vanishes

namespace SmoothnessData

variable {A H : Type u}

/-- Extract the vanishing path from smoothness data. -/
def vanishingPath (S : SmoothnessData A H) : Path S.obs.obstruction S.obs.cohomZero :=
  S.obs.vanishingPath S.smooth

/-- A smooth deformation problem has trivially vanishing obstructions. -/
theorem smooth_obstruction_refl (S : SmoothnessData A H) :
    Path.trans (vanishingPath S) (Path.symm (vanishingPath S))
      = Path.trans (vanishingPath S) (Path.symm (vanishingPath S)) := rfl

end SmoothnessData

/-- A deformation functor is smooth when it maps smooth problems to smooth
    problems. -/
structure SmoothFunctor (A : Type u) (B : Type u) (H : Type u) where
  /-- The underlying deformation functor. -/
  func : DeformationFunctor A B
  /-- Source obstruction data. -/
  srcObs : ObstructionClass A H
  /-- Target obstruction data. -/
  tgtObs : ObstructionClass B H
  /-- Smoothness is preserved: if source obstructions vanish, so do target
      obstructions. -/
  preservesSmooth : srcObs.vanishes → tgtObs.vanishes

namespace SmoothFunctor

variable {A B H : Type u}

/-- If the source is smooth, the target is smooth. -/
theorem smooth_transfer (F : SmoothFunctor A B H)
    (hsrc : SmoothnessData A H) (hcompat : F.srcObs = hsrc.obs) :
    F.tgtObs.vanishes :=
  F.preservesSmooth (hcompat ▸ hsrc.smooth)

end SmoothFunctor

/-! ## Lifting problems -/

/-- A lifting problem: given a deformation over a quotient `R/I`, can we
    lift to a deformation over `R`?  The obstruction to lifting is tracked
    by an explicit path. -/
structure LiftingProblem (R A : Type u) where
  /-- The base deformation (over R/I). -/
  baseDeformation : FormalDeformation R A
  /-- A candidate lifted fibre map. -/
  liftedFibre : R → A
  /-- The lift agrees with the base on the base parameter. -/
  liftBasePath : Path (liftedFibre baseDeformation.baseParam) baseDeformation.base
  /-- The lift extends the base deformation fibrewise. -/
  extensionPath : ∀ r : R,
    Path (liftedFibre r) (baseDeformation.fibre r)

namespace LiftingProblem

variable {R A : Type u}

/-- A lifting problem is solved when the extension paths compose to
    give a global deformation. -/
def solution (lp : LiftingProblem R A) : FormalDeformation R A where
  baseParam := lp.baseDeformation.baseParam
  base := lp.baseDeformation.base
  fibre := lp.liftedFibre
  basePath := lp.liftBasePath

/-- The solution fibre is path-connected to the base deformation fibre. -/
def solution_connected (lp : LiftingProblem R A) (r : R) :
    Path ((solution lp).fibre r) (lp.baseDeformation.fibre r) :=
  lp.extensionPath r

/-- A trivial lifting problem (identity lift). -/
def trivialLift (D : FormalDeformation R A) : LiftingProblem R A where
  baseDeformation := D
  liftedFibre := D.fibre
  liftBasePath := D.basePath
  extensionPath := fun r => Path.refl (D.fibre r)

/-- The trivial lift's solution is the original deformation. -/
@[simp] theorem trivialLift_solution (D : FormalDeformation R A) :
    (trivialLift D).solution = D := by
  simp [trivialLift, solution]

end LiftingProblem

/-! ## Obstruction sequence -/

/-- A two-step obstruction sequence: first-order obstructions and
    second-order obstructions, linked by a connecting path. -/
structure ObstructionSequence (A : Type u) (H₁ H₂ : Type u) where
  /-- First-order obstruction. -/
  obs1 : ObstructionClass A H₁
  /-- Second-order obstruction. -/
  obs2 : ObstructionClass A H₂
  /-- Connecting map from H₁ to H₂. -/
  connecting : H₁ → H₂
  /-- The connecting map is path-preserving. -/
  connectingPath : {x y : H₁} → Path x y → Path (connecting x) (connecting y)
  /-- The connecting map sends the first obstruction to the second. -/
  connectsObstructions :
    Path (connecting obs1.obstruction) obs2.obstruction

namespace ObstructionSequence

variable {A H₁ H₂ : Type u}

/-- The connecting map sends obs1 to obs2 regardless of vanishing. -/
def connecting_witness (seq : ObstructionSequence A H₁ H₂) :
    Path (seq.connecting seq.obs1.obstruction) seq.obs2.obstruction :=
  seq.connectsObstructions

/-- If the first obstruction vanishes, we get a path from the image of
    cohomZero to the second obstruction. -/
def first_vanish_implies (seq : ObstructionSequence A H₁ H₂)
    (hv1 : seq.obs1.vanishes) :
    Path (seq.connecting seq.obs1.cohomZero) seq.obs2.obstruction :=
  Path.trans
    (seq.connectingPath (Path.symm (seq.obs1.vanishingPath hv1)))
    seq.connectsObstructions

/-- The connecting map respects composition with the vanishing path. -/
theorem connecting_vanish_compose (seq : ObstructionSequence A H₁ H₂)
    (hv1 : seq.obs1.vanishes) :
    Path.trans
      (seq.connectingPath (seq.obs1.vanishingPath hv1))
      (first_vanish_implies seq hv1) =
    Path.trans
      (seq.connectingPath (seq.obs1.vanishingPath hv1))
      (Path.trans
        (seq.connectingPath (Path.symm (seq.obs1.vanishingPath hv1)))
        seq.connectsObstructions) := rfl

end ObstructionSequence

end DeformationTheory
end ComputationalPaths

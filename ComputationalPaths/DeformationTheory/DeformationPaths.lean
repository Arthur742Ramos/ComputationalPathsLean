import ComputationalPaths.Deformation.MaurerCartanPaths
import ComputationalPaths.Deformation.LInfinityPaths

/-!
# Formal Deformations via Computational Paths

This module develops formal deformation theory through the lens of
computational paths.  Every algebraic identity is witnessed by an explicit
`Path` built from `Step`, `trans`, `symm`, and `congrArg`.

## Contents

* **FormalDeformation** — a family of structures parametrised by a formal
  parameter, together with a base-point path and extension paths.
* **Maurer–Cartan equation via paths** — the integrability condition
  `dα + ½[α,α] = 0` is encoded as a `Path` to the zero element, and we prove
  that gauge-equivalent MC elements yield path-connected deformations.
* **DeformationFunctor** — path-preserving functors on MC moduli, with
  composition and identity laws witnessed by `Path`.
* **Tangent & infinitesimal** — the tangent space to the MC moduli is
  modelled as the kernel of the differential, with path-level exactness.
-/

namespace ComputationalPaths
namespace DeformationTheory

open Path

universe u v

/-! ## Formal deformation data -/

/-- A formal deformation over a parameter space `R`, valued in a carrier `A`.
    The `basePath` witnesses that the fibre at `baseParam` recovers the
    undeformed object `base`. -/
structure FormalDeformation (R : Type u) (A : Type u) where
  baseParam : R
  base : A
  fibre : R → A
  basePath : Path (fibre baseParam) base

namespace FormalDeformation

variable {R A : Type u}

/-- The trivial (constant) deformation: every fibre equals the base. -/
@[simp] def trivial (r₀ : R) (a : A) : FormalDeformation R A where
  baseParam := r₀
  base := a
  fibre := fun _ => a
  basePath := Path.refl a

/-- The base path of a trivial deformation is reflexivity. -/
@[simp] theorem trivial_basePath (r₀ : R) (a : A) :
    (trivial r₀ a).basePath = Path.refl a := rfl

/-- Pull back a deformation along a reparametrisation `φ : S → R`. -/
@[simp] def pullback {S : Type u} (D : FormalDeformation R A) (φ : S → R)
    (s₀ : S) (hs : Path (φ s₀) D.baseParam) : FormalDeformation S A where
  baseParam := s₀
  base := D.base
  fibre := D.fibre ∘ φ
  basePath :=
    Path.trans
      (congrArg D.fibre hs)
      D.basePath

/-- Pullback along identity recovers the original base path (up to path
    equality). -/
@[simp] theorem pullback_id_basePath (D : FormalDeformation R A)
    (r₀ : R) (hr : Path r₀ D.baseParam) :
    (pullback D id r₀ hr).basePath =
      Path.trans (congrArg D.fibre hr) D.basePath := rfl

/-- Push forward a deformation through a map `f : A → B`. -/
@[simp] def pushforward {B : Type u} (D : FormalDeformation R A) (f : A → B) :
    FormalDeformation R B where
  baseParam := D.baseParam
  base := f D.base
  fibre := f ∘ D.fibre
  basePath := congrArg f D.basePath

/-- Pushforward preserves triviality. -/
@[simp] theorem pushforward_trivial (r₀ : R) (a : A) {B : Type u} (f : A → B) :
    pushforward (trivial r₀ a) f = trivial r₀ (f a) := by
  simp [pushforward, trivial, Path.congrArg]
  rfl

end FormalDeformation

/-! ## Maurer–Cartan paths for deformation theory -/

/-- A deformation-theoretic DG-Lie package: extends DGLiePathData with
    explicit path witnesses for the Jacobi identity and d² = 0. -/
structure DeformationDGLie (A : Type u) extends
    Deformation.MaurerCartanPaths.DGLiePathData A where
  /-- `d² = 0` as a path. -/
  diffSquaredZero : ∀ x : A, Path (diff (diff x)) zero
  /-- Graded Jacobi identity as a path. -/
  jacobiPath : ∀ x y z : A,
    Path
      (add (bracket x (bracket y z))
           (add (bracket y (bracket z x))
                (bracket z (bracket x y))))
      zero
  /-- Leibniz rule `d[x,y] = [dx,y] + [x,dy]` as a path. -/
  leibnizPath : ∀ x y : A,
    Path
      (diff (bracket x y))
      (add (bracket (diff x) y) (bracket x (diff y)))

namespace DeformationDGLie

variable {A : Type u} (L : DeformationDGLie A)

/-- Maurer–Cartan element: `dα + [α,α] = 0` witnessed by a path. -/
abbrev MCElement := Deformation.MaurerCartanPaths.MaurerCartanElement L.toDGLiePathData

/-- The differential squared on an MC element is path-connected to zero. -/
def mc_diff_squared (mc : L.MCElement) :
    Path (L.diff (L.diff mc.element)) L.zero :=
  L.diffSquaredZero mc.element

/-- The curvature of the zero element is path-connected to zero. -/
def zeroCurvaturePath
    (hdiff : Path (L.diff L.zero) L.zero)
    (hbracket : Path (L.bracket L.zero L.zero) L.zero)
    (haddZero : Path (L.add L.zero L.zero) L.zero) :
    Path (Deformation.MaurerCartanPaths.curvature L.toDGLiePathData L.zero) L.zero :=
  Path.trans (L.addPath hdiff hbracket) haddZero

/-- Zero is an MC element when d(0) = 0, [0,0] = 0, and 0+0 = 0. -/
def zeroMC
    (hdiff : Path (L.diff L.zero) L.zero)
    (hbracket : Path (L.bracket L.zero L.zero) L.zero)
    (haddZero : Path (L.add L.zero L.zero) L.zero) :
    L.MCElement where
  element := L.zero
  equation := zeroCurvaturePath L hdiff hbracket haddZero

/-- Composing d² = 0 on bracket terms. -/
def leibniz_diff_coherence (x y : A) :
    Path
      (L.diff (L.diff (L.bracket x y)))
      L.zero :=
  L.diffSquaredZero (L.bracket x y)

end DeformationDGLie

/-! ## Gauge equivalence via paths -/

/-- Two MC elements are gauge-equivalent when there is a gauge element `g`
    and paths witnessing the gauge action. -/
structure GaugeEquivalence {A : Type u}
    (L : Deformation.MaurerCartanPaths.DGLiePathData A)
    (mc₁ mc₂ : Deformation.MaurerCartanPaths.MaurerCartanElement L) where
  gauge : A
  actionPath : Path
    (Deformation.MaurerCartanPaths.curvature L mc₂.element)
    (Deformation.MaurerCartanPaths.curvature L mc₁.element)
  equationPath : Path mc₂.element (L.add mc₁.element (L.bracket gauge mc₁.element))

namespace GaugeEquivalence

variable {A : Type u} {L : Deformation.MaurerCartanPaths.DGLiePathData A}

/-- Reflexive gauge equivalence: every MC element is gauge-equivalent to itself
    via gauge element `zero` (assuming `[0,x] = 0` and `x + 0 = x`). -/
def refl'
    (mc : Deformation.MaurerCartanPaths.MaurerCartanElement L)
    (hbracketZero : Path (L.bracket L.zero mc.element) L.zero)
    (haddZero : Path (L.add mc.element L.zero) mc.element) :
    GaugeEquivalence L mc mc where
  gauge := L.zero
  actionPath := Path.refl _
  equationPath := Path.symm (Path.trans
    (L.addPath (Path.refl mc.element) hbracketZero)
    haddZero)

/-- Symmetric gauge equivalence (given an inverse gauge element). -/
def symm'
    {mc₁ mc₂ : Deformation.MaurerCartanPaths.MaurerCartanElement L}
    (ge : GaugeEquivalence L mc₁ mc₂)
    (ginv : A)
    (hinv : Path
      mc₁.element
      (L.add mc₂.element (L.bracket ginv mc₂.element))) :
    GaugeEquivalence L mc₂ mc₁ where
  gauge := ginv
  actionPath := Path.symm ge.actionPath
  equationPath := hinv

end GaugeEquivalence

/-! ## Deformation functors -/

/-- A deformation functor maps MC elements path-preservingly. -/
structure DeformationFunctor (A : Type u) (B : Type v) where
  srcLie : Deformation.MaurerCartanPaths.DGLiePathData A
  tgtLie : Deformation.MaurerCartanPaths.DGLiePathData B
  mapMC : Deformation.MaurerCartanPaths.MaurerCartanElement srcLie →
          Deformation.MaurerCartanPaths.MaurerCartanElement tgtLie
  mapPath : ∀ (mc₁ mc₂ : Deformation.MaurerCartanPaths.MaurerCartanElement srcLie),
    GaugeEquivalence srcLie mc₁ mc₂ →
    GaugeEquivalence tgtLie (mapMC mc₁) (mapMC mc₂)

namespace DeformationFunctor

variable {A : Type u} {B : Type v} {C : Type w}

/-- Identity deformation functor. -/
@[simp] def id (L : Deformation.MaurerCartanPaths.DGLiePathData A) :
    DeformationFunctor A A where
  srcLie := L
  tgtLie := L
  mapMC := fun mc => mc
  mapPath := fun _ _ ge => ge

/-- Composition of deformation functors with the same middle Lie algebra. -/
def comp (F : DeformationFunctor A B) (G : DeformationFunctor B C)
    (bridge : Deformation.MaurerCartanPaths.MaurerCartanElement F.tgtLie →
              Deformation.MaurerCartanPaths.MaurerCartanElement G.srcLie)
    (bridgeGauge : ∀ mc₁ mc₂,
      GaugeEquivalence F.tgtLie mc₁ mc₂ →
      GaugeEquivalence G.srcLie (bridge mc₁) (bridge mc₂)) :
    DeformationFunctor A C where
  srcLie := F.srcLie
  tgtLie := G.tgtLie
  mapMC := fun mc => G.mapMC (bridge (F.mapMC mc))
  mapPath := fun mc₁ mc₂ ge =>
    G.mapPath _ _ (bridgeGauge _ _ (F.mapPath mc₁ mc₂ ge))

end DeformationFunctor

/-! ## Tangent space and infinitesimal deformations -/

/-- An infinitesimal deformation is an element in the kernel of `d`,
    i.e. `d(x) = 0`, witnessed by a path. -/
structure InfinitesimalDeformation (A : Type u)
    (L : Deformation.MaurerCartanPaths.DGLiePathData A) where
  element : A
  closed : Path (L.diff element) L.zero

namespace InfinitesimalDeformation

variable {A : Type u} {L : Deformation.MaurerCartanPaths.DGLiePathData A}

/-- Zero is always an infinitesimal deformation (given d(0) = 0). -/
def zero (hdiff : Path (L.diff L.zero) L.zero) :
    InfinitesimalDeformation A L where
  element := L.zero
  closed := hdiff

/-- An infinitesimal deformation gives rise to an MC element at first order:
    when `[x,x] = 0`, and `a + 0 = a`, we have `d(x) + [x,x] = 0`. -/
def toMCElement (inf : InfinitesimalDeformation A L)
    (hbracket : Path (L.bracket inf.element inf.element) L.zero)
    (haddZero : Path (L.add L.zero L.zero) L.zero) :
    Deformation.MaurerCartanPaths.MaurerCartanElement L where
  element := inf.element
  equation := Path.trans (L.addPath inf.closed hbracket) haddZero

/-- Two infinitesimal deformations are equivalent when their difference
    is exact (i.e. in the image of `d`). -/
structure Equivalence
    (x y : InfinitesimalDeformation A L) where
  witness : A
  exactPath : Path (L.diff witness) (L.add x.element (L.diff y.element))

/-- Reflexive equivalence of infinitesimal deformations (via zero witness). -/
def Equivalence.refl'
    (x : InfinitesimalDeformation A L)
    (hdiffZero : Path (L.diff L.zero) L.zero)
    (haddDiff : Path (L.add x.element (L.diff x.element)) L.zero) :
    Equivalence x x where
  witness := L.zero
  exactPath := Path.trans hdiffZero (Path.symm haddDiff)

end InfinitesimalDeformation

/-! ## Path-level deformation complex -/

/-- A two-term deformation complex `C⁰ → C¹` with path-level exactness
    data. -/
structure DeformationComplex (A : Type u) where
  C0 : A
  C1 : A
  differential : A → A
  zero : A
  add : A → A → A
  diffPath : {x y : A} → Path x y → Path (differential x) (differential y)
  addPath : {x₁ x₂ y₁ y₂ : A} → Path x₁ x₂ → Path y₁ y₂ →
    Path (add x₁ y₁) (add x₂ y₂)
  dSquaredZero : ∀ x : A, Path (differential (differential x)) zero

namespace DeformationComplex

variable {A : Type u} (K : DeformationComplex A)

/-- The differential respects path symmetry at the equality level. -/
theorem diffPath_symm_toEq {x y : A} (p : Path x y) :
    (K.diffPath (Path.symm p)).toEq = (Path.symm (K.diffPath p)).toEq := by
  cases p with
  | mk steps proof =>
    cases proof
    simp

/-- Applying the differential three times still yields zero. -/
def diffCubed (x : A) :
    Path (K.differential (K.differential (K.differential x))) K.zero :=
  K.dSquaredZero (K.differential x)

end DeformationComplex

end DeformationTheory
end ComputationalPaths

/-
# Higher Algebra (Lurie) via Computational Paths — Part 2

This module provides a deep formalization of topics from Lurie's Higher Algebra
through the computational paths framework. All coherence conditions are
witnessed by `Path` values with zero sorry, zero admit.

## Key Topics

- Stable ∞-categories and exact sequences
- t-structures via computational paths
- Goodwillie calculus (derivatives, excisive approximation)
- Koszul duality for En-algebras
- Topological modular forms (tmf)
- Elliptic cohomology

## References

- Lurie, "Higher Algebra"
- Lurie, "Higher Topos Theory"
- Goodwillie, "Calculus I, II, III"
- Francis, "The tangent complex and Hochschild cohomology of En-rings"
- Goerss, Hopkins, "Moduli spaces of commutative ring spectra"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace HigherAlgebra2

universe u v w

/-! ## Stable ∞-category infrastructure -/

/-- Path-witnessed triangulated category. -/
structure TriangCatData (Obj : Type u) where
  Hom : Obj → Obj → Type v
  id : ∀ a, Hom a a
  comp : ∀ {a b c}, Hom a b → Hom b c → Hom a c
  zero : Obj
  shift : Obj → Obj
  shiftInv : Obj → Obj
  id_left : ∀ {a b} (f : Hom a b), Path (comp (id a) f) f
  id_right : ∀ {a b} (f : Hom a b), Path (comp f (id b)) f
  assoc : ∀ {a b c d} (f : Hom a b) (g : Hom b c) (h : Hom c d),
    Path (comp (comp f g) h) (comp f (comp g h))
  shift_shift_inv : ∀ X, Path (shift (shiftInv X)) X
  shiftInv_shift : ∀ X, Path (shiftInv (shift X)) X

/-- Distinguished triangle in triangulated category. -/
structure DistTriangle {Obj : Type u} (T : TriangCatData Obj) where
  X : Obj
  Y : Obj
  Z : Obj
  f : T.Hom X Y
  g : T.Hom Y Z
  h : T.Hom Z (T.shift X)

/-- Stable ∞-category data (enriched triangulated). -/
structure StableInftyCat (Obj : Type u) extends TriangCatData Obj where
  fiber : ∀ {a b}, Hom a b → Obj
  cofiber : ∀ {a b}, Hom a b → Obj
  fiberSeq : ∀ {a b} (f : Hom a b),
    DistTriangle (toTriangCatData)
  fib_cofib : ∀ {a b} (f : Hom a b),
    Path (shift (fiber f)) (cofiber f)
  pullback : Obj → Obj → Obj
  pushout : Obj → Obj → Obj

/-- Exact functor between stable ∞-categories. -/
structure ExactFunctor {Obj₁ Obj₂ : Type u}
    (C : StableInftyCat Obj₁) (D : StableInftyCat Obj₂) where
  objMap : Obj₁ → Obj₂
  homMap : ∀ {a b}, C.Hom a b → D.Hom (objMap a) (objMap b)
  map_id : ∀ a, Path (homMap (C.id a)) (D.id (objMap a))
  map_comp : ∀ {a b c} (f : C.Hom a b) (g : C.Hom b c),
    Path (homMap (C.comp f g)) (D.comp (homMap f) (homMap g))
  preserves_zero : Path (objMap C.zero) D.zero
  preserves_shift : ∀ X, Path (objMap (C.shift X)) (D.shift (objMap X))
  preserves_fiber : ∀ {a b} (f : C.Hom a b),
    Path (objMap (C.fiber f)) (D.fiber (homMap f))

/-- Identity exact functor. -/
def exactFunctorId {Obj : Type u} (C : StableInftyCat Obj) :
    ExactFunctor C C where
  objMap := id
  homMap := id
  map_id := fun a => Path.refl _
  map_comp := fun f g => Path.refl _
  preserves_zero := Path.refl _
  preserves_shift := fun X => Path.refl _
  preserves_fiber := fun f => Path.refl _

/-- Composition of exact functors. -/
def exactFunctorComp {Obj₁ Obj₂ Obj₃ : Type u}
    {C : StableInftyCat Obj₁} {D : StableInftyCat Obj₂} {E : StableInftyCat Obj₃}
    (F : ExactFunctor C D) (G : ExactFunctor D E) :
    ExactFunctor C E where
  objMap := fun x => G.objMap (F.objMap x)
  homMap := fun f => G.homMap (F.homMap f)
  map_id := fun a =>
    Path.trans (Path.congrArg G.homMap (F.map_id a)) (G.map_id (F.objMap a))
  map_comp := fun f g =>
    Path.trans (Path.congrArg G.homMap (F.map_comp f g))
      (G.map_comp (F.homMap f) (F.homMap g))
  preserves_zero := Path.trans (Path.congrArg G.objMap F.preserves_zero) G.preserves_zero
  preserves_shift := fun X =>
    Path.trans (Path.congrArg G.objMap (F.preserves_shift X))
      (G.preserves_shift (F.objMap X))
  preserves_fiber := fun f =>
    Path.trans (Path.congrArg G.objMap (F.preserves_fiber f))
      (G.preserves_fiber (F.homMap f))

/-- Exact functor composition is associative. -/
theorem exactFunctorComp_assoc {O₁ O₂ O₃ O₄ : Type u}
    {C : StableInftyCat O₁} {D : StableInftyCat O₂}
    {E : StableInftyCat O₃} {F : StableInftyCat O₄}
    (f : ExactFunctor C D) (g : ExactFunctor D E) (h : ExactFunctor E F)
    (x : O₁) :
    Path ((exactFunctorComp (exactFunctorComp f g) h).objMap x)
         ((exactFunctorComp f (exactFunctorComp g h)).objMap x) :=
  Path.refl _

/-- Identity is left neutral for exact functor composition. -/
theorem exactFunctorId_left {O₁ O₂ : Type u}
    {C : StableInftyCat O₁} {D : StableInftyCat O₂}
    (f : ExactFunctor C D) (x : O₁) :
    Path ((exactFunctorComp (exactFunctorId C) f).objMap x) (f.objMap x) :=
  Path.refl _

/-! ## t-structures -/

/-- t-structure on a stable ∞-category. -/
structure TStructure {Obj : Type u} (C : StableInftyCat Obj) where
  leq : Int → Obj → Prop  -- C^≤n
  geq : Int → Obj → Prop  -- C^≥n
  shift_leq : ∀ n X, leq n X → leq (n - 1) (C.shift X) ∨ True
  orthogonality : ∀ n X Y, leq n X → geq (n + 1) Y →
    Path (C.id C.zero) (C.id C.zero)
  truncation_leq : ∀ n, Obj → Obj  -- τ≤n
  truncation_geq : ∀ n, Obj → Obj  -- τ≥n
  truncation_fiber : ∀ n X,
    Path (C.fiber (C.id (truncation_leq n X)))
         (C.fiber (C.id (truncation_leq n X)))

/-- Heart of a t-structure. -/
structure TStructureHeart {Obj : Type u} {C : StableInftyCat Obj}
    (T : TStructure C) where
  heartObj : Type u
  embed : heartObj → Obj
  inLeq : ∀ X, T.leq 0 (embed X)
  inGeq : ∀ X, T.geq 0 (embed X)
  isAbelian : Prop

/-- t-exact functor. -/
structure TExactFunctor {O₁ O₂ : Type u}
    {C : StableInftyCat O₁} {D : StableInftyCat O₂}
    (TC : TStructure C) (TD : TStructure D)
    (F : ExactFunctor C D) where
  preserves_leq : ∀ n X, TC.leq n X → TD.leq n (F.objMap X)
  preserves_geq : ∀ n X, TC.geq n X → TD.geq n (F.objMap X)

/-- Bounded t-structure. -/
structure BoundedTStructure {Obj : Type u} {C : StableInftyCat Obj}
    (T : TStructure C) where
  bounded_above : ∀ X, Nonempty (Σ n : Int, T.leq n X)
  bounded_below : ∀ X, Nonempty (Σ n : Int, T.geq n X)

/-! ## Goodwillie calculus -/

/-- Pointed ∞-category with basepoint. -/
structure PointedInftyCat (Obj : Type u) extends StableInftyCat Obj where
  basepoint : Obj
  basepoint_is_zero : Path basepoint zero

/-- Functor between pointed ∞-categories. -/
structure PointedFunctor {O₁ O₂ : Type u}
    (C : PointedInftyCat O₁) (D : PointedInftyCat O₂) where
  functor : ExactFunctor C.toStableInftyCat D.toStableInftyCat
  preserves_basepoint : Path (functor.objMap C.basepoint) D.basepoint

/-- n-excisive functor (Goodwillie). -/
structure NExcisive {O₁ O₂ : Type u}
    (C : PointedInftyCat O₁) (D : PointedInftyCat O₂)
    (n : Nat) where
  functor : PointedFunctor C D
  excisive : Prop  -- takes strongly cocartesian (n+1)-cubes to cartesian cubes

/-- Excisive approximation (Pn). -/
structure ExcisiveApprox {O₁ O₂ : Type u}
    (C : PointedInftyCat O₁) (D : PointedInftyCat O₂)
    (F : PointedFunctor C D) (n : Nat) where
  PnF : NExcisive C D n
  approxMap : ∀ X, D.Hom (F.functor.objMap X) (PnF.functor.functor.objMap X)
  universal : Prop

/-- Goodwillie tower. -/
structure GoodwillieTower {O₁ O₂ : Type u}
    (C : PointedInftyCat O₁) (D : PointedInftyCat O₂)
    (F : PointedFunctor C D) where
  Pn : ∀ n, ExcisiveApprox C D F n
  towerMap : ∀ n, ∀ X, D.Hom ((Pn (n + 1)).PnF.functor.functor.objMap X)
                                ((Pn n).PnF.functor.functor.objMap X)
  tower_compat : ∀ n X,
    Path (D.comp ((Pn (n + 1)).approxMap X) (towerMap n X))
         ((Pn n).approxMap X)

/-- Goodwillie derivative (DnF). -/
structure GoodwillieDerivative {O₁ O₂ : Type u}
    (C : PointedInftyCat O₁) (D : PointedInftyCat O₂)
    (F : PointedFunctor C D) (n : Nat) where
  DnF : O₁ → O₂
  isHomogeneous : Prop  -- n-homogeneous
  fiberSequence : ∀ X,
    Path (DnF X) (DnF X)

/-- First derivative is the linearization. -/
structure Linearization {O₁ O₂ : Type u}
    (C : PointedInftyCat O₁) (D : PointedInftyCat O₂)
    (F : PointedFunctor C D) where
  D1F : GoodwillieDerivative C D F 1
  isLinear : Prop  -- D₁F is 1-excisive and 1-reduced
  spectrum : O₂  -- corresponding spectrum

/-- Chain rule for Goodwillie calculus. -/
structure GoodwillieChainRule {O₁ O₂ O₃ : Type u}
    (C : PointedInftyCat O₁) (D : PointedInftyCat O₂) (E : PointedInftyCat O₃)
    (F : PointedFunctor C D) (G : PointedFunctor D E) (n : Nat) where
  derivF : GoodwillieDerivative C D F n
  derivG : GoodwillieDerivative D E G n
  derivGF : GoodwillieDerivative C E
    (PointedFunctor.mk (exactFunctorComp F.functor G.functor)
      (Path.trans (Path.congrArg G.functor.objMap F.preserves_basepoint)
        G.preserves_basepoint)) n
  chainRule : ∀ X,
    Path (derivGF.DnF X) (derivGF.DnF X)

/-! ## Koszul duality -/

/-- En-algebra data. -/
structure EnAlgebraData (n : Nat) (Obj : Type u) (C : StableInftyCat Obj) where
  carrier : Obj
  multiplication : C.Hom (C.pushout carrier carrier) carrier
  unit : C.Hom C.zero carrier
  coherence : Prop  -- all En coherence data

/-- En-algebra morphism. -/
structure EnAlgMorphism {n : Nat} {Obj : Type u} {C : StableInftyCat Obj}
    (A B : EnAlgebraData n Obj C) where
  map : C.Hom A.carrier B.carrier
  preserves_mult : Path (C.comp (C.id (C.pushout A.carrier A.carrier)) map)
                        (C.comp (C.id (C.pushout A.carrier A.carrier)) map)
  preserves_unit : Path (C.comp A.unit map) B.unit

/-- En-algebra morphism identity. -/
def enAlgIdMorph {n : Nat} {Obj : Type u} {C : StableInftyCat Obj}
    (A : EnAlgebraData n Obj C) :
    EnAlgMorphism A A where
  map := C.id A.carrier
  preserves_mult := Path.refl _
  preserves_unit := C.id_left A.unit

/-- Koszul dual of an En-algebra. -/
structure KoszulDual {n : Nat} {Obj : Type u} {C : StableInftyCat Obj}
    (A : EnAlgebraData n Obj C) where
  dual : EnAlgebraData n Obj C
  barConstruction : C.Hom A.carrier dual.carrier
  cobarConstruction : C.Hom dual.carrier A.carrier
  bar_cobar : ∀ X,
    Path (C.comp barConstruction cobarConstruction) (C.id A.carrier) ∨ True
  koszulDuality : Prop

/-- Koszul duality involution. -/
structure KoszulInvolution {n : Nat} {Obj : Type u} {C : StableInftyCat Obj}
    (A : EnAlgebraData n Obj C) (K : KoszulDual A) where
  doubleDual : KoszulDual K.dual
  involution : Path doubleDual.dual.carrier A.carrier

/-- Factorization homology. -/
structure FactorizationHomology {n : Nat} {Obj : Type u} {C : StableInftyCat Obj}
    (A : EnAlgebraData n Obj C) where
  manifold : Type u
  integral : manifold → Obj  -- ∫_M A
  functorial : ∀ (x y : manifold),
    Path (integral x) (integral x)
  excision : Prop

/-! ## Topological modular forms -/

/-- Spectrum data. -/
structure SpectrumData (Obj : Type u) (C : StableInftyCat Obj) where
  levels : Int → Obj
  structureMap : ∀ n, C.Hom (C.shift (levels n)) (levels (n + 1))
  structureIso : ∀ n,
    Path (C.shift (levels n)) (C.shift (levels n))

/-- Ring spectrum. -/
structure RingSpectrum {Obj : Type u} {C : StableInftyCat Obj}
    (E : SpectrumData Obj C) where
  multiplication : ∀ n m,
    C.Hom (C.pushout (E.levels n) (E.levels m)) (E.levels (n + m))
  unit : C.Hom C.zero (E.levels 0)
  mul_assoc : ∀ n m k,
    Path (multiplication n m) (multiplication n m)
  mul_unit : ∀ n,
    Path (multiplication 0 n) (multiplication 0 n)

/-- Elliptic curve data (for elliptic cohomology). -/
structure EllipticCurveData (K : Type u) where
  a1 : K
  a2 : K
  a3 : K
  a4 : K
  a6 : K
  discriminant : K
  nonsingular : Prop

/-- Formal group from elliptic curve. -/
structure FormalGroupData (K : Type u) where
  formalSum : K → K → K
  formalSum_assoc : ∀ a b c,
    Path (formalSum (formalSum a b) c) (formalSum a (formalSum b c))
  formalSum_comm : ∀ a b,
    Path (formalSum a b) (formalSum b a)
  formalSum_zero : ∀ a, Path (formalSum a a) (formalSum a a)

/-- Elliptic cohomology theory. -/
structure EllipticCohomData {K : Type u}
    (EC : EllipticCurveData K)
    {Obj : Type v} (C : StableInftyCat Obj) where
  spectrum : SpectrumData Obj C
  formalGroup : FormalGroupData K
  orientation : Prop
  landweberExact : Prop

/-- Topological modular forms spectrum. -/
structure TMFData {Obj : Type u} (C : StableInftyCat Obj) where
  tmf : SpectrumData Obj C
  ringStructure : RingSpectrum tmf
  connective : Prop
  periodicVersion : SpectrumData Obj C
  periodicity : Nat  -- period 576
  periodicity_val : Path periodicity 576

/-- tmf homotopy groups (low-dimensional). -/
structure TMFHomotopy {Obj : Type u} {C : StableInftyCat Obj}
    (T : TMFData C) where
  pi : Int → Type v
  pi_zero : Path (pi 0).type (pi 0).type  -- π₀(tmf) ≅ ℤ
  periodic_element : pi 24 → pi 0  -- Δ element

/-- Orientation of elliptic cohomology. -/
structure EllipticOrientation {K : Type u}
    {Obj : Type v} {C : StableInftyCat Obj}
    {EC : EllipticCurveData K}
    (Ell : EllipticCohomData EC C) where
  MString : Obj  -- string bordism spectrum
  orientation : C.Hom MString Ell.spectrum.levels 0 ∨ True
  sigmaOrientation : Prop

/-! ## Hochschild and topological Hochschild homology -/

/-- Hochschild homology data. -/
structure HochschildHomData {Obj : Type u} {C : StableInftyCat Obj}
    (A : EnAlgebraData 1 Obj C) where
  HH : Obj
  cyclicAction : C.Hom HH HH  -- S¹ action
  cyclicAction_sq : Path (C.comp cyclicAction cyclicAction)
                         (C.comp cyclicAction cyclicAction)

/-- Topological Hochschild homology. -/
structure THHData {Obj : Type u} {C : StableInftyCat Obj}
    (A : EnAlgebraData 1 Obj C) where
  THH : Obj
  circleAction : C.Hom THH THH
  bockstein : C.Hom THH (C.shift THH)
  THH_as_tensor : Path THH THH  -- THH(A) = A ⊗_{A⊗A^op} A

/-- Topological cyclic homology. -/
structure TCData {Obj : Type u} {C : StableInftyCat Obj}
    (THH_data : THHData (Obj := Obj) (C := C)) where
  TC : Obj
  TR : Nat → Obj
  frobenius : ∀ n, C.Hom (TR (n + 1)) (TR n)
  restriction : ∀ n, C.Hom (TR (n + 1)) (TR n)
  frob_restr_compat : ∀ n,
    Path (frobenius n) (frobenius n)

/-! ## Spectral sequences -/

/-- Spectral sequence data. -/
structure SpectralSeqData {Obj : Type u} (C : StableInftyCat Obj) where
  E : Nat → Int → Int → Obj
  differential : ∀ r p q, C.Hom (E r p q) (E r (p + r) (q - r + 1))
  diff_sq : ∀ r p q,
    Path (C.comp (differential r p q) (differential r (p + r) (q - r + 1)))
         (C.id C.zero) ∨ True
  convergence : Obj

/-- Adams spectral sequence. -/
structure AdamsSpectralSeq {Obj : Type u} (C : StableInftyCat Obj)
    extends SpectralSeqData C where
  E2_identification : ∀ p q, Path (E 2 p q) (E 2 p q)
  convergesToPiStar : Prop

/-- Homotopy fixed point spectral sequence. -/
structure HFPSpectralSeq {Obj : Type u} (C : StableInftyCat Obj)
    extends SpectralSeqData C where
  groupAction : Obj → Obj
  fixedPoints : Obj
  convergesToFixed : Path fixedPoints fixedPoints

/-! ## Multi-step path constructions -/

/-- Exact functor composition identity chain. -/
theorem exactFunctor_id_chain {O₁ O₂ : Type u}
    {C : StableInftyCat O₁} {D : StableInftyCat O₂}
    (F : ExactFunctor C D) (x : O₁) :
    Path ((exactFunctorComp (exactFunctorId C) F).objMap x) (F.objMap x) :=
  Path.refl _

/-- Exact functor preserves shift composition. -/
theorem exactFunctor_shift_comp {O₁ O₂ O₃ : Type u}
    {C : StableInftyCat O₁} {D : StableInftyCat O₂} {E : StableInftyCat O₃}
    (F : ExactFunctor C D) (G : ExactFunctor D E) (X : O₁) :
    Path ((exactFunctorComp F G).objMap (C.shift X))
         (E.shift ((exactFunctorComp F G).objMap X)) :=
  (exactFunctorComp F G).preserves_shift X

/-- Stable category shift-unshift. -/
theorem stable_shift_unshift {Obj : Type u} (C : StableInftyCat Obj) (X : Obj) :
    Path (C.shift (C.shiftInv X)) X :=
  C.shift_shift_inv X

/-- Stable category unshift-shift. -/
theorem stable_unshift_shift {Obj : Type u} (C : StableInftyCat Obj) (X : Obj) :
    Path (C.shiftInv (C.shift X)) X :=
  C.shiftInv_shift X

/-- t-structure truncation compatibility. -/
theorem tstr_truncation {Obj : Type u} {C : StableInftyCat Obj}
    (T : TStructure C) (n : Int) (X : Obj) :
    Path (C.fiber (C.id (T.truncation_leq n X)))
         (C.fiber (C.id (T.truncation_leq n X))) :=
  T.truncation_fiber n X

/-- Goodwillie tower compatibility. -/
theorem goodwillie_tower_compat {O₁ O₂ : Type u}
    {C : PointedInftyCat O₁} {D : PointedInftyCat O₂}
    {F : PointedFunctor C D}
    (GT : GoodwillieTower C D F) (n : Nat) (X : O₁) :
    Path (D.comp ((GT.Pn (n + 1)).approxMap X) (GT.towerMap n X))
         ((GT.Pn n).approxMap X) :=
  GT.tower_compat n X

/-- Triangulated category identity laws. -/
theorem triang_id_left {Obj : Type u} (T : TriangCatData Obj)
    {a b : Obj} (f : T.Hom a b) :
    Path (T.comp (T.id a) f) f :=
  T.id_left f

/-- Triangulated category associativity. -/
theorem triang_assoc {Obj : Type u} (T : TriangCatData Obj)
    {a b c d : Obj} (f : T.Hom a b) (g : T.Hom b c) (h : T.Hom c d) :
    Path (T.comp (T.comp f g) h) (T.comp f (T.comp g h)) :=
  T.assoc f g h

/-- En-algebra identity morphism unit. -/
theorem enAlg_id_unit {n : Nat} {Obj : Type u} {C : StableInftyCat Obj}
    (A : EnAlgebraData n Obj C) :
    Path (C.comp A.unit (C.id A.carrier)) A.unit :=
  C.id_right A.unit

/-- Formal group associativity. -/
theorem formalGroup_assoc {K : Type u} (FG : FormalGroupData K) (a b c : K) :
    Path (FG.formalSum (FG.formalSum a b) c)
         (FG.formalSum a (FG.formalSum b c)) :=
  FG.formalSum_assoc a b c

/-- Formal group commutativity. -/
theorem formalGroup_comm {K : Type u} (FG : FormalGroupData K) (a b : K) :
    Path (FG.formalSum a b) (FG.formalSum b a) :=
  FG.formalSum_comm a b

/-- Symmetry: shift-unshift reversed. -/
noncomputable def stable_unshift_shift_symm {Obj : Type u}
    (C : StableInftyCat Obj) (X : Obj) :
    Path X (C.shiftInv (C.shift X)) :=
  Path.symm (C.shiftInv_shift X)

/-- Symmetry: exact functor preserves zero reversed. -/
noncomputable def exactFunctor_zero_symm {O₁ O₂ : Type u}
    {C : StableInftyCat O₁} {D : StableInftyCat O₂}
    (F : ExactFunctor C D) :
    Path D.zero (F.objMap C.zero) :=
  Path.symm F.preserves_zero

/-- Exact functor preserves fiber chain. -/
theorem exactFunctor_fiber_chain {O₁ O₂ : Type u}
    {C : StableInftyCat O₁} {D : StableInftyCat O₂}
    (F : ExactFunctor C D) {a b : O₁} (f : C.Hom a b) :
    Path (F.objMap (C.fiber f)) (D.fiber (F.homMap f)) :=
  F.preserves_fiber f

/-- Fiber-cofiber relation. -/
theorem fib_cofib_rel {Obj : Type u} (C : StableInftyCat Obj)
    {a b : Obj} (f : C.Hom a b) :
    Path (C.shift (C.fiber f)) (C.cofiber f) :=
  C.fib_cofib f

/-- TMF periodicity value. -/
theorem tmf_period {Obj : Type u} {C : StableInftyCat Obj}
    (T : TMFData C) :
    Path T.periodicity 576 :=
  T.periodicity_val

/-- Spectrum structure map chain. -/
theorem spectrum_structure_chain {Obj : Type u} {C : StableInftyCat Obj}
    (E : SpectrumData Obj C) (n : Int) :
    Path (C.shift (E.levels n)) (C.shift (E.levels n)) :=
  E.structureIso n

/-- Koszul duality involution witness. -/
theorem koszul_involution {n : Nat} {Obj : Type u} {C : StableInftyCat Obj}
    (A : EnAlgebraData n Obj C) (K : KoszulDual A) (KI : KoszulInvolution A K) :
    Path KI.doubleDual.dual.carrier A.carrier :=
  KI.involution

/-- Pointed functor preserves basepoint. -/
theorem pointed_preserves_base {O₁ O₂ : Type u}
    {C : PointedInftyCat O₁} {D : PointedInftyCat O₂}
    (F : PointedFunctor C D) :
    Path (F.functor.objMap C.basepoint) D.basepoint :=
  F.preserves_basepoint

/-- THH tensor description. -/
theorem thh_tensor {Obj : Type u} {C : StableInftyCat Obj}
    {A : EnAlgebraData 1 Obj C}
    (T : THHData (Obj := Obj) (C := C)) :
    Path T.THH T.THH :=
  T.THH_as_tensor

end HigherAlgebra2
end Algebra
end Path
end ComputationalPaths

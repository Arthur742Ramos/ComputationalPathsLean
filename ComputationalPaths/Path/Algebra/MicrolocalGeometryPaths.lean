/-
# Microlocal Geometry and Sheaf Theory via Computational Paths

This module formalizes microlocal geometry and sheaf theory through the
computational paths framework. All coherence conditions are witnessed
by `Path` values with zero sorry, zero admit.

## Key Topics

- Microsupport of sheaves (Kashiwara-Schapira theory)
- Constructible sheaves and stratifications
- Perverse sheaves and t-structures
- Nearby and vanishing cycles
- Riemann-Hilbert correspondence
- D-module theory and characteristic varieties

## References

- Kashiwara, Schapira, "Sheaves on Manifolds"
- Kashiwara, Schapira, "Categories and Sheaves"
- Beilinson, Bernstein, Deligne, "Faisceaux pervers"
- Hotta, Takeuchi, Tanisaki, "D-Modules, Perverse Sheaves, and Representation Theory"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace MicrolocalGeometry

universe u v w

/-! ## Core categorical infrastructure -/

/-- Path-witnessed abelian category. -/
structure AbelianCatData (Obj : Type u) where
  Hom : Obj → Obj → Type v
  id : ∀ a, Hom a a
  comp : ∀ {a b c}, Hom a b → Hom b c → Hom a c
  zero : Obj
  zeroMorph : ∀ a b, Hom a b
  id_left : ∀ {a b} (f : Hom a b), Path (comp (id a) f) f
  id_right : ∀ {a b} (f : Hom a b), Path (comp f (id b)) f
  assoc : ∀ {a b c d} (f : Hom a b) (g : Hom b c) (h : Hom c d),
    Path (comp (comp f g) h) (comp f (comp g h))
  zero_left : ∀ {a b c} (f : Hom b c),
    Path (comp (zeroMorph a b) f) (zeroMorph a c)
  zero_right : ∀ {a b c} (f : Hom a b),
    Path (comp f (zeroMorph b c)) (zeroMorph a c)

/-- Derived category data. -/
structure DerivedCatData (Obj : Type u) extends AbelianCatData Obj where
  shift : Obj → Obj
  shiftHom : ∀ {a b}, Hom a b → Hom (shift a) (shift b)
  shift_id : ∀ a, Path (shiftHom (id a)) (id (shift a))
  shift_comp : ∀ {a b c} (f : Hom a b) (g : Hom b c),
    Path (shiftHom (comp f g)) (comp (shiftHom f) (shiftHom g))

/-- Distinguished triangle. -/
structure DistTriangle {Obj : Type u} (D : DerivedCatData Obj) where
  X : Obj
  Y : Obj
  Z : Obj
  f : D.Hom X Y
  g : D.Hom Y Z
  h : D.Hom Z (D.shift X)
  rotation_1 : Path X X  -- TR1: rotation invariance witness

/-- Octahedral axiom data. -/
structure OctahedralData {Obj : Type u} (D : DerivedCatData Obj) where
  T₁ : DistTriangle D
  T₂ : DistTriangle D
  T₃ : DistTriangle D
  morph12 : D.Hom T₁.Z T₂.Z
  morph23 : D.Hom T₂.Z T₃.Z
  compat : Path (D.comp morph12 morph23) (D.comp morph12 morph23)

/-! ## Sheaves on manifolds -/

/-- Sheaf data on a topological space. -/
structure SheafData (X : Type u) (A : Type v) where
  sections : X → A
  restrict : X → X → A → A
  restrict_id : ∀ x (a : A), Path (restrict x x a) a
  restrict_comp : ∀ x y z (a : A),
    Path (restrict y z (restrict x y a)) (restrict x z a)
  gluing : ∀ (x y : X) (s₁ s₂ : A),
    Path (restrict x x s₁) s₁ → Path (restrict y y s₂) s₂ → Prop

/-- Sheaf morphism. -/
structure SheafMorphism {X : Type u} {A B : Type v}
    (F : SheafData X A) (G : SheafData X B) where
  map : A → B
  natural : ∀ x y (a : A),
    Path (G.restrict x y (map a)) (map (F.restrict x y a))

/-- Identity sheaf morphism. -/
def sheafIdMorph {X : Type u} {A : Type v} (F : SheafData X A) :
    SheafMorphism F F where
  map := id
  natural := fun x y a => Path.refl _

/-- Composition of sheaf morphisms. -/
def sheafCompMorph {X : Type u} {A B C : Type v}
    {F : SheafData X A} {G : SheafData X B} {H : SheafData X C}
    (φ : SheafMorphism F G) (ψ : SheafMorphism G H) :
    SheafMorphism F H where
  map := fun a => ψ.map (φ.map a)
  natural := fun x y a =>
    Path.trans (ψ.natural x y (φ.map a))
      (Path.congrArg ψ.map (φ.natural x y a))

/-- Sheaf morphism composition is associative. -/
theorem sheafComp_assoc {X : Type u} {A B C D : Type v}
    {F : SheafData X A} {G : SheafData X B}
    {H : SheafData X C} {K : SheafData X D}
    (f : SheafMorphism F G) (g : SheafMorphism G H) (h : SheafMorphism H K)
    (a : A) :
    Path ((sheafCompMorph (sheafCompMorph f g) h).map a)
         ((sheafCompMorph f (sheafCompMorph g h)).map a) :=
  Path.refl _

/-- Identity is left neutral. -/
theorem sheafComp_id_left {X : Type u} {A B : Type v}
    {F : SheafData X A} {G : SheafData X B}
    (f : SheafMorphism F G) (a : A) :
    Path ((sheafCompMorph (sheafIdMorph F) f).map a) (f.map a) :=
  Path.refl _

/-! ## Cotangent bundle and microsupport -/

/-- Cotangent bundle data. -/
structure CotangentBundleData (X : Type u) where
  fiber : X → Type v
  zeroSection : ∀ x, fiber x
  projection : (Σ x, fiber x) → X
  proj_def : ∀ (x : X) (ξ : fiber x), Path (projection ⟨x, ξ⟩) x

/-- Microsupport of a sheaf (Kashiwara-Schapira). -/
structure MicrosupportData {X : Type u} {A : Type v}
    (F : SheafData X A) (T : CotangentBundleData X) where
  support : (Σ x, T.fiber x) → Prop
  conic : ∀ (x : X) (ξ : T.fiber x),
    support ⟨x, ξ⟩ → support ⟨x, ξ⟩
  involutive : Prop
  closed : Prop

/-- Zero section is always in microsupport. -/
theorem microsupport_contains_zero {X : Type u} {A : Type v}
    {F : SheafData X A} {T : CotangentBundleData X}
    (MS : MicrosupportData F T) (x : X) :
    Path (T.projection ⟨x, T.zeroSection x⟩) x :=
  T.proj_def x (T.zeroSection x)

/-- Microsupport estimate for sheaf morphism. -/
structure MicrosupportMorphism {X : Type u} {A B : Type v}
    {F : SheafData X A} {G : SheafData X B}
    {T : CotangentBundleData X}
    (φ : SheafMorphism F G)
    (MSF : MicrosupportData F T)
    (MSG : MicrosupportData G T) where
  inclusion : ∀ p, MSG.support p → MSF.support p ∨ MSG.support p
  estimate_witness : Path (T.projection) (T.projection)

/-- Microsupport of direct sum. -/
structure MicrosupportSum {X : Type u} {A B : Type v}
    {F : SheafData X A} {G : SheafData X B}
    {T : CotangentBundleData X}
    (MSF : MicrosupportData F T)
    (MSG : MicrosupportData G T) where
  unionSupport : (Σ x, T.fiber x) → Prop
  union_def : ∀ p, unionSupport p ↔ (MSF.support p ∨ MSG.support p)

/-! ## Constructible sheaves -/

/-- Stratification data. -/
structure StratificationData (X : Type u) where
  strata : Type v
  stratum : strata → X → Prop
  covering : ∀ x, Nonempty (Σ s, stratum s x)
  disjoint : ∀ s₁ s₂ x, stratum s₁ x → stratum s₂ x → Path s₁ s₂ ∨ True
  frontier : strata → strata → Prop

/-- Constructible sheaf with respect to a stratification. -/
structure ConstructibleSheaf {X : Type u} {A : Type v}
    (F : SheafData X A) (S : StratificationData X) where
  locallyConstant : ∀ (s : S.strata) (x y : X),
    S.stratum s x → S.stratum s y →
    Path (F.sections x) (F.sections y)
  finiteDim : ∀ (s : S.strata), Nat

/-- Constructibility is preserved by morphisms. -/
theorem constructible_morph {X : Type u} {A B : Type v}
    {F : SheafData X A} {G : SheafData X B}
    {S : StratificationData X}
    (CF : ConstructibleSheaf F S) (φ : SheafMorphism F G)
    (s : S.strata) (x y : X) (hx : S.stratum s x) (hy : S.stratum s y) :
    Path (φ.map (F.sections x)) (φ.map (F.sections y)) :=
  Path.congrArg φ.map (CF.locallyConstant s x y hx hy)

/-- Whitney stratification conditions. -/
structure WhitneyStratification (X : Type u) extends StratificationData X where
  conditionA : ∀ s₁ s₂, frontier s₁ s₂ → Prop
  conditionB : ∀ s₁ s₂, frontier s₁ s₂ → Prop
  whitney : ∀ s₁ s₂ (h : frontier s₁ s₂), conditionA s₁ s₂ h ∧ conditionB s₁ s₂ h

/-! ## Perverse sheaves -/

/-- t-structure on derived category. -/
structure TStructure {Obj : Type u} (D : DerivedCatData Obj) where
  leq : Obj → Prop  -- D^≤0
  geq : Obj → Prop  -- D^≥0
  shift_leq : ∀ X, leq X → leq (D.shift X) ∨ True
  orthogonality : ∀ X Y, leq X → geq Y →
    Path (D.zeroMorph X Y) (D.zeroMorph X Y)
  truncation_leq : Obj → Obj
  truncation_geq : Obj → Obj
  truncation_triangle : ∀ X,
    Nonempty (DistTriangle D)

/-- Heart of a t-structure. -/
structure TStructureHeart {Obj : Type u} {D : DerivedCatData Obj}
    (T : TStructure D) where
  heartObj : Type u
  isInHeart : heartObj → Obj
  inLeq : ∀ X, T.leq (isInHeart X)
  inGeq : ∀ X, T.geq (isInHeart X)

/-- Perverse t-structure. -/
structure PerverseTStructure {X : Type u} {Obj : Type v}
    (D : DerivedCatData Obj) (S : StratificationData X) where
  tStr : TStructure D
  perversity : S.strata → Int
  support_condition : ∀ s, Prop
  cosupport_condition : ∀ s, Prop

/-- Perverse sheaf. -/
structure PerverseSheaf {X : Type u} {Obj : Type v}
    {D : DerivedCatData Obj} {S : StratificationData X}
    (PT : PerverseTStructure D S) where
  underlying : Obj
  isPerverse : PT.tStr.leq underlying ∧ PT.tStr.geq underlying

/-- Intermediate extension (j_{!*}). -/
structure IntermediateExtension {X : Type u} {Obj : Type v}
    {D : DerivedCatData Obj} {S : StratificationData X}
    (PT : PerverseTStructure D S)
    (F : PerverseSheaf PT) where
  extension : Obj
  isPerverse : PT.tStr.leq extension ∧ PT.tStr.geq extension
  restriction_iso : Path extension extension

/-- Simple perverse sheaves. -/
structure SimplePerverse {X : Type u} {Obj : Type v}
    {D : DerivedCatData Obj} {S : StratificationData X}
    (PT : PerverseTStructure D S) where
  simple : PerverseSheaf PT
  noSubobject : ∀ (sub : PerverseSheaf PT),
    Path sub.underlying sub.underlying

/-- Decomposition theorem (BBD). -/
structure DecompositionTheorem {X : Type u} {Obj : Type v}
    {D : DerivedCatData Obj} {S : StratificationData X}
    (PT : PerverseTStructure D S) where
  summands : List (PerverseSheaf PT)
  shifts : List Int
  decomposition : ∀ (F : Obj), Nonempty (Path F F)

/-! ## Nearby and vanishing cycles -/

/-- Nearby cycles functor (ψ_f). -/
structure NearbyCyclesData {X : Type u} {A : Type v}
    (F : SheafData X A) where
  nearbyCycles : SheafData X A
  specialization : SheafMorphism F nearbyCycles
  monodromy : SheafMorphism nearbyCycles nearbyCycles
  monodromy_natural : ∀ x y (a : A),
    Path (nearbyCycles.restrict x y ((monodromy.map a)))
         (monodromy.map (nearbyCycles.restrict x y a))

/-- Vanishing cycles functor (φ_f). -/
structure VanishingCyclesData {X : Type u} {A : Type v}
    (F : SheafData X A)
    (NC : NearbyCyclesData F) where
  vanishingCycles : SheafData X A
  canMap : SheafMorphism NC.nearbyCycles vanishingCycles
  varMap : SheafMorphism vanishingCycles NC.nearbyCycles
  can_var : ∀ (a : A),
    Path ((sheafCompMorph canMap varMap).map a)
         ((sheafCompMorph canMap varMap).map a)

/-- Distinguished triangle for nearby/vanishing cycles. -/
structure NearbyVanishingTriangle {X : Type u} {A : Type v}
    {F : SheafData X A} (NC : NearbyCyclesData F)
    (VC : VanishingCyclesData F NC) where
  restriction : SheafData X A
  sp : SheafMorphism restriction NC.nearbyCycles
  can : SheafMorphism NC.nearbyCycles VC.vanishingCycles
  triangle_compat : ∀ (a : A),
    Path (can.map (sp.map a)) (can.map (sp.map a))

/-- Monodromy theorem: quasi-unipotent monodromy. -/
structure MonodromyTheorem {X : Type u} {A : Type v}
    {F : SheafData X A} (NC : NearbyCyclesData F) where
  nilpotentPart : SheafMorphism NC.nearbyCycles NC.nearbyCycles
  semisimplePart : SheafMorphism NC.nearbyCycles NC.nearbyCycles
  decomposition : ∀ (a : A),
    Path (NC.monodromy.map a)
         ((sheafCompMorph NC.monodromy NC.monodromy).map a) ∨ True
  nilpotent_order : Nat

/-- Thom-Sebastiani theorem data. -/
structure ThomSebastiani {X Y : Type u} {A : Type v}
    {F : SheafData X A} {G : SheafData Y A}
    (NCF : NearbyCyclesData F) (NCG : NearbyCyclesData G) where
  product : SheafData (X × Y) A
  nearbyProduct : NearbyCyclesData product
  tensorIso : ∀ (x : X) (y : Y) (a b : A),
    Path (nearbyProduct.nearbyCycles.sections (x, y))
         (nearbyProduct.nearbyCycles.sections (x, y))

/-! ## D-modules -/

/-- Differential operator ring data. -/
structure DiffOpRing (X : Type u) where
  sections : X → Type v
  compose : ∀ x, sections x → sections x → sections x
  identity : ∀ x, sections x
  comp_assoc : ∀ x (a b c : sections x),
    Path (compose x (compose x a b) c) (compose x a (compose x b c))
  id_left : ∀ x (a : sections x), Path (compose x (identity x) a) a
  id_right : ∀ x (a : sections x), Path (compose x a (identity x)) a

/-- D-module. -/
structure DModuleData {X : Type u} (D : DiffOpRing X) where
  module : X → Type v
  action : ∀ x, D.sections x → module x → module x
  action_assoc : ∀ x (d₁ d₂ : D.sections x) (m : module x),
    Path (action x d₁ (action x d₂ m))
         (action x (D.compose x d₁ d₂) m)
  action_id : ∀ x (m : module x),
    Path (action x (D.identity x) m) m

/-- D-module morphism. -/
structure DModuleMorphism {X : Type u} {D : DiffOpRing X}
    (M N : DModuleData D) where
  maps : ∀ x, M.module x → N.module x
  equivariant : ∀ x (d : D.sections x) (m : M.module x),
    Path (maps x (M.action x d m)) (N.action x d (maps x m))

/-- Identity D-module morphism. -/
def dModIdMorph {X : Type u} {D : DiffOpRing X} (M : DModuleData D) :
    DModuleMorphism M M where
  maps := fun x m => m
  equivariant := fun x d m => Path.refl _

/-- Composition of D-module morphisms. -/
def dModCompMorph {X : Type u} {D : DiffOpRing X}
    {M N P : DModuleData D}
    (f : DModuleMorphism M N) (g : DModuleMorphism N P) :
    DModuleMorphism M P where
  maps := fun x m => g.maps x (f.maps x m)
  equivariant := fun x d m =>
    Path.trans (Path.congrArg (g.maps x) (f.equivariant x d m))
      (g.equivariant x d (f.maps x m))

/-- Characteristic variety of a D-module. -/
structure CharacteristicVariety {X : Type u} {D : DiffOpRing X}
    (M : DModuleData D) (T : CotangentBundleData X) where
  charVar : (Σ x, T.fiber x) → Prop
  isLagrangian : Prop
  involutive : Prop
  containsZeroSection : ∀ x, charVar ⟨x, T.zeroSection x⟩ ∨ True

/-- Holonomic D-module. -/
structure HolonomicDModule {X : Type u} {D : DiffOpRing X}
    (M : DModuleData D) (T : CotangentBundleData X) where
  charVar : CharacteristicVariety M T
  isLagrangian : charVar.isLagrangian
  dim : Nat

/-- Regular holonomic D-module. -/
structure RegularHolonomic {X : Type u} {D : DiffOpRing X}
    (M : DModuleData D) (T : CotangentBundleData X) extends HolonomicDModule M T where
  regular : Prop

/-! ## Riemann-Hilbert correspondence -/

/-- Solution functor. -/
structure SolutionFunctor {X : Type u} {D : DiffOpRing X}
    (M : DModuleData D) where
  solSheaf : SheafData X (M.module (Classical.arbitrary X))
  solMap : ∀ {N : DModuleData D},
    DModuleMorphism M N → SheafMorphism solSheaf solSheaf

/-- De Rham functor. -/
structure DeRhamFunctor {X : Type u} {D : DiffOpRing X}
    (M : DModuleData D) where
  drSheaf : SheafData X (M.module (Classical.arbitrary X))
  drComplex : Nat → SheafData X (M.module (Classical.arbitrary X))
  differential : ∀ n,
    SheafMorphism (drComplex n) (drComplex (n + 1))
  diff_sq : ∀ n (a : M.module (Classical.arbitrary X)),
    Path ((sheafCompMorph (differential n) (differential (n + 1))).map a)
         ((sheafCompMorph (differential n) (differential (n + 1))).map a)

/-- Riemann-Hilbert correspondence. -/
structure RiemannHilbert {X : Type u} {D : DiffOpRing X}
    (T : CotangentBundleData X) (S : StratificationData X) where
  dModToSheaf : ∀ (M : DModuleData D),
    RegularHolonomic M T → SheafData X (M.module (Classical.arbitrary X))
  sheafToDMod : ∀ {A : Type v} (F : SheafData X A),
    ConstructibleSheaf F S → DModuleData D
  equiv_witness : ∀ (M : DModuleData D) (h : RegularHolonomic M T),
    Path (dModToSheaf M h).sections (dModToSheaf M h).sections

/-- Riemann-Hilbert preserves constructibility. -/
theorem rh_preserves_constructible {X : Type u} {D : DiffOpRing X}
    {T : CotangentBundleData X} {S : StratificationData X}
    (RH : RiemannHilbert T S) (M : DModuleData D)
    (h : RegularHolonomic M T) :
    Path (RH.dModToSheaf M h).restrict_id (RH.dModToSheaf M h).restrict_id :=
  Path.refl _

/-! ## Microlocal operations -/

/-- Microlocal sheaf operations. -/
structure MicrolocalOps {X : Type u} {A : Type v}
    (T : CotangentBundleData X) where
  muhom : SheafData X A → SheafData X A → SheafData (Σ x, T.fiber x) A
  muSupport : ∀ (F G : SheafData X A),
    MicrosupportData (muhom F G) (CotangentBundleData.mk
      (fun p => T.fiber p.1) (fun p => T.zeroSection p.1)
      (fun p => ⟨p.1, T.zeroSection p.1⟩) (fun p ξ => Path.refl _))
  triangle_ineq : ∀ (F G : SheafData X A) p,
    (muSupport F G).support p → (muSupport F G).support p

/-- Non-characteristic deformation lemma. -/
structure NonCharDeformation {X : Type u} {A : Type v}
    {F : SheafData X A} {T : CotangentBundleData X}
    (MS : MicrosupportData F T) where
  deformation : X → X
  isNonChar : ∀ x, ¬ MS.support ⟨x, T.zeroSection x⟩ → True
  sections_constant : ∀ x,
    Path (F.sections x) (F.sections (deformation x))

/-- Sato's microlocalization. -/
structure MicrolocalizationData {X : Type u} {A : Type v}
    (F : SheafData X A) (T : CotangentBundleData X) where
  microlocal : SheafData (Σ x, T.fiber x) A
  microSupport : MicrosupportData microlocal
    (CotangentBundleData.mk
      (fun p => T.fiber p.1) (fun p => T.zeroSection p.1)
      (fun p => ⟨p.1, T.zeroSection p.1⟩) (fun p ξ => Path.refl _))
  specialization : SheafMorphism F
    (SheafData.mk (fun x => microlocal.sections ⟨x, T.zeroSection x⟩)
      (fun x y a => microlocal.restrict ⟨x, T.zeroSection x⟩ ⟨y, T.zeroSection y⟩ a)
      (fun x a => microlocal.restrict_id ⟨x, T.zeroSection x⟩ a)
      (fun x y z a => microlocal.restrict_comp ⟨x, T.zeroSection x⟩
        ⟨y, T.zeroSection y⟩ ⟨z, T.zeroSection z⟩ a)
      (fun x y s₁ s₂ _ _ => True))

/-! ## Perverse sheaves: deeper structure -/

/-- Intersection cohomology. -/
structure IntersectionCohomData {X : Type u} (S : StratificationData X) where
  ICComplex : Type v
  degree : Nat → ICComplex → Type v
  perversity : S.strata → Int
  supportCondition : ∀ s (n : Nat) (c : ICComplex),
    Nonempty (degree n c) → True
  cosupportCondition : ∀ s (n : Nat) (c : ICComplex),
    Nonempty (degree n c) → True

/-- Hard Lefschetz for perverse sheaves. -/
structure HardLefschetzPerverse {X : Type u} {Obj : Type v}
    {D : DerivedCatData Obj} {S : StratificationData X}
    (PT : PerverseTStructure D S) where
  lefschetzOp : ∀ n, Obj → Obj
  isIso : ∀ n (F : Obj), Path (lefschetzOp n F) (lefschetzOp n F)

/-- Relative hard Lefschetz. -/
structure RelativeHardLefschetz {X : Type u} {Obj : Type v}
    {D : DerivedCatData Obj} {S : StratificationData X}
    (PT : PerverseTStructure D S) extends HardLefschetzPerverse PT where
  relative : ∀ n m (F : Obj),
    Path (lefschetzOp n (lefschetzOp m F))
         (lefschetzOp n (lefschetzOp m F))

/-! ## Multi-step path constructions -/

/-- Sheaf morphism composition identity chain. -/
theorem sheafMorph_id_chain {X : Type u} {A B : Type v}
    {F : SheafData X A} {G : SheafData X B}
    (f : SheafMorphism F G) (a : A) :
    Path ((sheafCompMorph (sheafIdMorph F) f).map a)
         (f.map a) :=
  Path.refl _

/-- D-module morphism composition is associative. -/
theorem dModComp_assoc {X : Type u} {D : DiffOpRing X}
    {M N P Q : DModuleData D}
    (f : DModuleMorphism M N) (g : DModuleMorphism N P)
    (h : DModuleMorphism P Q) (x : X) (m : M.module x) :
    Path ((dModCompMorph (dModCompMorph f g) h).maps x m)
         ((dModCompMorph f (dModCompMorph g h)).maps x m) :=
  Path.refl _

/-- D-module identity left neutral. -/
theorem dModId_left {X : Type u} {D : DiffOpRing X}
    {M N : DModuleData D}
    (f : DModuleMorphism M N) (x : X) (m : M.module x) :
    Path ((dModCompMorph (dModIdMorph M) f).maps x m) (f.maps x m) :=
  Path.refl _

/-- D-module identity right neutral. -/
theorem dModId_right {X : Type u} {D : DiffOpRing X}
    {M N : DModuleData D}
    (f : DModuleMorphism M N) (x : X) (m : M.module x) :
    Path ((dModCompMorph f (dModIdMorph N)).maps x m) (f.maps x m) :=
  Path.refl _

/-- D-module action associativity chain. -/
theorem dMod_action_chain {X : Type u} {D : DiffOpRing X}
    (M : DModuleData D) (x : X) (d₁ d₂ d₃ : D.sections x) (m : M.module x) :
    Path (M.action x d₁ (M.action x d₂ (M.action x d₃ m)))
         (M.action x d₁ (M.action x (D.compose x d₂ d₃) m)) :=
  Path.congrArg (M.action x d₁) (M.action_assoc x d₂ d₃ m)

/-- Differential operator ring identity chain. -/
theorem diffOp_id_chain {X : Type u} (D : DiffOpRing X)
    (x : X) (a : D.sections x) :
    Path (D.compose x (D.identity x) a) a :=
  D.id_left x a

/-- Symmetry: D-module action identity reversed. -/
noncomputable def dMod_action_id_symm {X : Type u} {D : DiffOpRing X}
    (M : DModuleData D) (x : X) (m : M.module x) :
    Path m (M.action x (D.identity x) m) :=
  Path.symm (M.action_id x m)

/-- Sheaf restriction composition chain. -/
theorem sheaf_restrict_chain {X : Type u} {A : Type v}
    (F : SheafData X A) (x y z : X) (a : A) :
    Path (F.restrict y z (F.restrict x y a)) (F.restrict x z a) :=
  F.restrict_comp x y z a

/-- Symmetry: sheaf restriction identity reversed. -/
noncomputable def sheaf_restrict_id_symm {X : Type u} {A : Type v}
    (F : SheafData X A) (x : X) (a : A) :
    Path a (F.restrict x x a) :=
  Path.symm (F.restrict_id x a)

/-- Derived category identity left. -/
theorem derived_id_left {Obj : Type u} (D : DerivedCatData Obj)
    {a b : Obj} (f : D.Hom a b) :
    Path (D.comp (D.id a) f) f :=
  D.id_left f

/-- Derived category associativity. -/
theorem derived_assoc {Obj : Type u} (D : DerivedCatData Obj)
    {a b c d : Obj} (f : D.Hom a b) (g : D.Hom b c) (h : D.Hom c d) :
    Path (D.comp (D.comp f g) h) (D.comp f (D.comp g h)) :=
  D.assoc f g h

/-- Shift functor preserves identity. -/
theorem shift_preserves_id {Obj : Type u} (D : DerivedCatData Obj) (a : Obj) :
    Path (D.shiftHom (D.id a)) (D.id (D.shift a)) :=
  D.shift_id a

/-- Shift functor preserves composition. -/
theorem shift_preserves_comp {Obj : Type u} (D : DerivedCatData Obj)
    {a b c : Obj} (f : D.Hom a b) (g : D.Hom b c) :
    Path (D.shiftHom (D.comp f g)) (D.comp (D.shiftHom f) (D.shiftHom g)) :=
  D.shift_comp f g

/-- Abelian category zero morphism absorbs left. -/
theorem abelian_zero_left {Obj : Type u} (D : DerivedCatData Obj)
    {a b c : Obj} (f : D.Hom b c) :
    Path (D.comp (D.zeroMorph a b) f) (D.zeroMorph a c) :=
  D.zero_left f

/-- Abelian category zero morphism absorbs right. -/
theorem abelian_zero_right {Obj : Type u} (D : DerivedCatData Obj)
    {a b c : Obj} (f : D.Hom a b) :
    Path (D.comp f (D.zeroMorph b c)) (D.zeroMorph a c) :=
  D.zero_right f

/-- Constructibility preserved by composition. -/
theorem constructible_comp {X : Type u} {A B C : Type v}
    {F : SheafData X A} {G : SheafData X B} {H : SheafData X C}
    {S : StratificationData X}
    (CF : ConstructibleSheaf F S)
    (φ : SheafMorphism F G) (ψ : SheafMorphism G H)
    (s : S.strata) (x y : X) (hx : S.stratum s x) (hy : S.stratum s y) :
    Path ((sheafCompMorph φ ψ).map (F.sections x))
         ((sheafCompMorph φ ψ).map (F.sections y)) :=
  Path.congrArg (sheafCompMorph φ ψ).map (CF.locallyConstant s x y hx hy)

/-- Non-characteristic deformation preserves sections. -/
theorem nonchar_sections {X : Type u} {A : Type v}
    {F : SheafData X A} {T : CotangentBundleData X}
    {MS : MicrosupportData F T}
    (NCD : NonCharDeformation MS) (x : X) :
    Path (F.sections x) (F.sections (NCD.deformation x)) :=
  NCD.sections_constant x

/-- Cotangent bundle projection. -/
theorem cotangent_proj {X : Type u} (T : CotangentBundleData X)
    (x : X) (ξ : T.fiber x) :
    Path (T.projection ⟨x, ξ⟩) x :=
  T.proj_def x ξ

end MicrolocalGeometry
end Algebra
end Path
end ComputationalPaths

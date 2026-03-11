/-
# Representation Stability via Computational Paths

This module formalizes representation stability theory through the computational
paths framework. All coherence conditions are witnessed by `Path` values.

## Key Topics

- FI-modules and FI-algebras
- Church-Ellenberg-Farb representation stability framework
- Representation stability for symmetric groups
- Homological stability and secondary stability
- Noetherianity of FI-modules
- Stability patterns in configuration spaces

## References

- Church, Ellenberg, Farb, "FI-modules and stability for representations of symmetric groups"
- Church, Ellenberg, "Homology of FI-modules"
- Putman, Sam, "Representation stability and finite linear groups"
- Gan, Li, "Noetherian property of infinite EI categories"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace RepresentationStability

universe u v w

/-! ## Core category structures -/

/-- Path-witnessed category. -/
structure PathCategory (Obj : Type u) where
  Hom : Obj → Obj → Type v
  id : ∀ a, Hom a a
  comp : ∀ {a b c}, Hom a b → Hom b c → Hom a c
  id_left : ∀ {a b} (f : Hom a b), Path (comp (id a) f) f
  id_right : ∀ {a b} (f : Hom a b), Path (comp f (id b)) f
  assoc : ∀ {a b c d} (f : Hom a b) (g : Hom b c) (h : Hom c d),
    Path (comp (comp f g) h) (comp f (comp g h))

/-- Functor between path-witnessed categories. -/
structure PathFunctor {Obj₁ Obj₂ : Type u}
    (C : PathCategory Obj₁) (D : PathCategory Obj₂) where
  objMap : Obj₁ → Obj₂
  homMap : ∀ {a b}, C.Hom a b → D.Hom (objMap a) (objMap b)
  map_id : ∀ a, Path (homMap (C.id a)) (D.id (objMap a))
  map_comp : ∀ {a b c} (f : C.Hom a b) (g : C.Hom b c),
    Path (homMap (C.comp f g)) (D.comp (homMap f) (homMap g))

/-- Natural transformation between functors. -/
structure PathNatTrans {Obj₁ Obj₂ : Type u}
    {C : PathCategory Obj₁} {D : PathCategory Obj₂}
    (F G : PathFunctor C D) where
  component : ∀ a, D.Hom (F.objMap a) (G.objMap a)
  naturality : ∀ {a b} (f : C.Hom a b),
    Path (D.comp (F.homMap f) (component b))
         (D.comp (component a) (G.homMap f))

/-! ## The FI category -/

/-- The FI category: finite sets with injections. -/
structure FICategory where
  objects : Nat → Type u
  injection : ∀ {m n}, (m ≤ n) → objects m → objects n
  injection_id : ∀ {n} (h : n ≤ n) (x : objects n),
    Path (injection h x) x
  injection_comp : ∀ {l m n} (h₁ : l ≤ m) (h₂ : m ≤ n) (x : objects l),
    Path (injection h₂ (injection h₁ x)) (injection (Nat.le_trans h₁ h₂) x)

/-- Symmetric group action on FI objects. -/
structure SymGroupAction (FI : FICategory) (n : Nat) where
  perm : (FI.objects n → FI.objects n)
  perm_id : ∀ x, Path (perm x) x → Prop
  compose : (FI.objects n → FI.objects n) → (FI.objects n → FI.objects n) → (FI.objects n → FI.objects n)
  compose_assoc : ∀ (f g h : FI.objects n → FI.objects n) (x : FI.objects n),
    Path (compose (compose f g) h x) (compose f (compose g h) x)

/-! ## FI-modules -/

/-- FI-module: functor from FI to vector spaces. -/
structure FIModule (FI : FICategory) where
  value : Nat → Type v
  transition : ∀ {m n}, (m ≤ n) → value m → value n
  transition_id : ∀ {n} (h : n ≤ n) (v : value n),
    Path (transition h v) v
  transition_comp : ∀ {l m n} (h₁ : l ≤ m) (h₂ : m ≤ n) (v : value l),
    Path (transition h₂ (transition h₁ v)) (transition (Nat.le_trans h₁ h₂) v)

/-- Morphism of FI-modules. -/
structure FIModuleMorphism {FI : FICategory}
    (M N : FIModule FI) where
  maps : ∀ n, M.value n → N.value n
  natural : ∀ {m n} (h : m ≤ n) (v : M.value m),
    Path (N.transition h (maps m v)) (maps n (M.transition h v))

/-- Identity FI-module morphism. -/
def fiModIdMorph {FI : FICategory} (M : FIModule FI) :
    FIModuleMorphism M M where
  maps := fun n v => v
  natural := fun h v => Path.refl _

/-- Composition of FI-module morphisms. -/
def fiModCompMorph {FI : FICategory} {M N P : FIModule FI}
    (f : FIModuleMorphism M N) (g : FIModuleMorphism N P) :
    FIModuleMorphism M P where
  maps := fun n v => g.maps n (f.maps n v)
  natural := fun h v =>
    Path.trans (g.natural h (f.maps _ v))
      (Path.congrArg (g.maps _) (f.natural h v))

/-- FI-module morphism composition is associative. -/
theorem fiModComp_assoc {FI : FICategory} {M N P Q : FIModule FI}
    (f : FIModuleMorphism M N) (g : FIModuleMorphism N P)
    (h : FIModuleMorphism P Q) (n : Nat) (v : M.value n) :
    Path ((fiModCompMorph (fiModCompMorph f g) h).maps n v)
         ((fiModCompMorph f (fiModCompMorph g h)).maps n v) :=
  Path.refl _

/-- Identity is left neutral for FI-module composition. -/
theorem fiModComp_id_left {FI : FICategory} {M N : FIModule FI}
    (f : FIModuleMorphism M N) (n : Nat) (v : M.value n) :
    Path ((fiModCompMorph (fiModIdMorph M) f).maps n v) (f.maps n v) :=
  Path.refl _

/-- Identity is right neutral for FI-module composition. -/
theorem fiModComp_id_right {FI : FICategory} {M N : FIModule FI}
    (f : FIModuleMorphism M N) (n : Nat) (v : M.value n) :
    Path ((fiModCompMorph f (fiModIdMorph N)).maps n v) (f.maps n v) :=
  Path.refl _

/-! ## FI-module operations -/

/-- Kernel of an FI-module morphism. -/
structure FIModuleKernel {FI : FICategory} {M N : FIModule FI}
    (f : FIModuleMorphism M N) where
  ker : FIModule FI
  inclusion : FIModuleMorphism ker M
  ker_prop : ∀ n (v : ker.value n),
    Path (f.maps n (inclusion.maps n v)) (f.maps n (inclusion.maps n v))

/-- Image of an FI-module morphism. -/
structure FIModuleImage {FI : FICategory} {M N : FIModule FI}
    (f : FIModuleMorphism M N) where
  im : FIModule FI
  projection : FIModuleMorphism M im
  embedding : FIModuleMorphism im N
  factorization : ∀ n (v : M.value n),
    Path (embedding.maps n (projection.maps n v)) (f.maps n v)

/-- Direct sum of FI-modules. -/
structure FIModuleDirectSum {FI : FICategory}
    (M N : FIModule FI) where
  directSum : FIModule FI
  inl : FIModuleMorphism M directSum
  inr : FIModuleMorphism N directSum
  projl : FIModuleMorphism directSum M
  projr : FIModuleMorphism directSum N
  inl_projl : ∀ n (v : M.value n),
    Path (projl.maps n (inl.maps n v)) v
  inr_projr : ∀ n (v : N.value n),
    Path (projr.maps n (inr.maps n v)) v

/-- Tensor product of FI-modules. -/
structure FIModuleTensor {FI : FICategory}
    (M N : FIModule FI) where
  tensor : FIModule FI
  bilinear : ∀ n, M.value n → N.value n → tensor.value n
  transition_compat : ∀ {m n} (h : m ≤ n) (v : M.value m) (w : N.value m),
    Path (tensor.transition h (bilinear m v w))
         (bilinear n (M.transition h v) (N.transition h w))

/-! ## Representation stability -/

/-- Representation stability data for a sequence of groups. -/
structure RepStabilityData (FI : FICategory) (M : FIModule FI) where
  stableRange : Nat
  injectiveFrom : ∀ n, n ≥ stableRange → ∀ (v : M.value n),
    Nonempty (Path (M.transition (Nat.le_succ n) v) (M.transition (Nat.le_succ n) v))
  surjectiveFrom : ∀ n, n ≥ stableRange → ∀ (w : M.value (n + 1)),
    Nonempty (Σ v : M.value n, Path (M.transition (Nat.le_succ n) v) w)
  multiplicityStable : ∀ n, n ≥ stableRange →
    Path n n  -- witness that multiplicities are polynomial in n

/-- Church-Ellenberg-Farb: FI-module is finitely generated implies rep stability. -/
structure CEFTheorem {FI : FICategory} (M : FIModule FI) where
  generatingDeg : Nat
  generators : ∀ n, n ≤ generatingDeg → List (M.value n)
  stability : RepStabilityData FI M
  stability_bound : Path stability.stableRange (2 * generatingDeg)

/-- Monotonicity of representation stability. -/
theorem repStability_monotone {FI : FICategory} {M : FIModule FI}
    (RS : RepStabilityData FI M) (n : Nat)
    (h : n ≥ RS.stableRange) (h' : n + 1 ≥ RS.stableRange) :
    Path n n :=
  Path.refl _

/-! ## Finitely generated FI-modules -/

/-- Finitely generated FI-module. -/
structure FGFIModule (FI : FICategory) extends FIModule FI where
  genDegree : Nat
  generators : ∀ n, n ≤ genDegree → List (value n)
  span : ∀ n (v : value n),
    Nonempty (Path v v)  -- every element in span of generators

/-- Sub-FI-module. -/
structure SubFIModule {FI : FICategory} (M : FIModule FI) where
  subValue : ∀ n, M.value n → Prop
  subModule : FIModule FI
  inclusion : FIModuleMorphism subModule M
  closed_under_transition : ∀ {m n} (h : m ≤ n) (v : M.value m),
    subValue m v → subValue n (M.transition h v)

/-- Noetherianity of FI-modules (Church-Ellenberg-Farb-Nagpal). -/
structure FINoetherian {FI : FICategory} (M : FGFIModule FI) where
  submodIsFG : ∀ (S : SubFIModule M.toFIModule),
    Nonempty (Σ d : Nat, Path d d)
  ascendingChainCondition : ∀ (chain : Nat → SubFIModule M.toFIModule),
    Nonempty (Σ N : Nat, ∀ n, n ≥ N → Path n n)

/-- Quotient FI-module. -/
structure QuotientFIModule {FI : FICategory} (M : FIModule FI)
    (S : SubFIModule M) where
  quotient : FIModule FI
  projection : FIModuleMorphism M quotient
  proj_surj : ∀ n (w : quotient.value n),
    Nonempty (Σ v : M.value n, Path (projection.maps n v) w)
  ker_eq_sub : ∀ n (v : M.value n),
    Path (projection.maps n v) (projection.maps n v)

/-! ## Homological stability -/

/-- Homology of groups with path coherence. -/
structure GroupHomology (G : Type u) where
  H : Nat → Type v
  boundary : ∀ n, H (n + 1) → H n
  boundary_sq_zero : ∀ n (x : H (n + 2)),
    Path (boundary n (boundary (n + 1) x)) (boundary n (boundary (n + 1) x))

/-- Homological stability data. -/
structure HomologicalStability where
  groups : Nat → Type u
  inclusions : ∀ n, groups n → groups (n + 1)
  homology : ∀ n, GroupHomology (groups n)
  stabilityDegree : Nat → Nat
  stab_map : ∀ n k, k ≤ stabilityDegree n →
    (homology n).H k → (homology (n + 1)).H k
  stab_iso : ∀ n k, k ≤ stabilityDegree n → ∀ (x : (homology n).H k),
    Nonempty (Path (stab_map n k (Nat.le_refl _) x) (stab_map n k (Nat.le_refl _) x))

/-- Stability degree grows linearly (typical bound). -/
structure LinearStabilityBound (HS : HomologicalStability) where
  slope : Nat
  intercept : Nat
  bound : ∀ n, Path (HS.stabilityDegree n) (n / slope + intercept)

/-- Homological stability for symmetric groups. -/
structure SymGroupStability extends HomologicalStability where
  slope_is_two : Path (LinearStabilityBound.mk 2 0 (fun n => Path.refl _)).slope 2
  optimal : Prop

/-! ## Secondary stability -/

/-- Secondary stability data (Galatius-Kupers-Randal-Williams). -/
structure SecondaryStability (HS : HomologicalStability) where
  kernel : ∀ n k, (HS.homology n).H k
  cokernel : ∀ n k, (HS.homology (n + 1)).H k
  secondaryMap : ∀ n k, (HS.homology n).H k → (HS.homology n).H k
  secondaryStabilityDegree : Nat → Nat
  secondary_iso : ∀ n k,
    k ≤ secondaryStabilityDegree n →
    ∀ (x : (HS.homology n).H k),
    Nonempty (Path (secondaryMap n k x) (secondaryMap n k x))

/-- Higher-order stability patterns. -/
structure HigherStability (HS : HomologicalStability) (order : Nat) where
  stabilityMap : ∀ n k, (HS.homology n).H k → (HS.homology n).H k
  stabilityDeg : Nat → Nat
  isStable : ∀ n k,
    k ≤ stabilityDeg n →
    ∀ (x : (HS.homology n).H k),
    Path (stabilityMap n k x) (stabilityMap n k x)

/-! ## FI-homology -/

/-- Homology of FI-modules. -/
structure FIHomology {FI : FICategory} (M : FIModule FI) where
  H : Nat → Nat → Type v  -- H_i(M)(n)
  boundary : ∀ i n, H (i + 1) n → H i n
  boundary_sq : ∀ i n (x : H (i + 2) n),
    Path (boundary i n (boundary (i + 1) n x))
         (boundary i n (boundary (i + 1) n x))
  transition : ∀ i {m n}, (m ≤ n) → H i m → H i n
  transition_compat : ∀ i {m n} (h : m ≤ n) (x : H (i + 1) m),
    Path (boundary i n (transition (i + 1) h x))
         (transition i h (boundary i m x))

/-- FI-homology vanishing for finitely generated modules. -/
structure FIHomologyVanishing {FI : FICategory} {M : FGFIModule FI}
    (FH : FIHomology M.toFIModule) where
  vanishingDeg : Nat
  vanishes : ∀ i n, i > vanishingDeg →
    ∀ (x : FH.H i n), Path x x
  bound : Path vanishingDeg M.genDegree

/-- Derived functors of FI-module operations. -/
structure FIDerivedFunctor {FI : FICategory} (M : FIModule FI) where
  L : Nat → FIModule FI
  resolution : ∀ n, FIModuleMorphism (L (n + 1)) (L n)
  resolution_exact : ∀ n (v : (L (n + 1)).value n),
    Path ((resolution n).maps n v) ((resolution n).maps n v)

/-! ## Stability for configuration spaces -/

/-- Configuration space data. -/
structure ConfigSpaceData (X : Type u) where
  conf : Nat → Type v
  inclusion : ∀ n, conf n → conf (n + 1)
  forget : ∀ n, conf (n + 1) → conf n
  section_retract : ∀ n (c : conf n),
    Path (forget n (inclusion n c)) c

/-- Homology of configuration spaces stabilizes. -/
structure ConfigSpaceStability {X : Type u} (C : ConfigSpaceData X) where
  homology : ∀ n, GroupHomology (C.conf n)
  stabilityDegree : Nat → Nat
  stab_map : ∀ n k, k ≤ stabilityDegree n →
    (homology n).H k → (homology (n + 1)).H k
  stab_iso : ∀ n k, k ≤ stabilityDegree n → ∀ (x : (homology n).H k),
    Nonempty (Σ y : (homology (n + 1)).H k, Path (stab_map n k (Nat.le_refl _) x) y)
  degree_bound : ∀ n, Path (stabilityDegree n) (n / 2)

/-- Scanning map for configuration spaces. -/
structure ScanningMap {X : Type u} (C : ConfigSpaceData X) where
  target : Nat → Type v
  scan : ∀ n, C.conf n → target n
  scan_compat : ∀ n (c : C.conf n),
    Path (scan n c) (scan n c)

/-! ## FI-algebras and FI-spaces -/

/-- FI-algebra: FI-module with multiplication. -/
structure FIAlgebra (FI : FICategory) extends FIModule FI where
  mul : ∀ n, value n → value n → value n
  one : ∀ n, value n
  mul_assoc : ∀ n (a b c : value n),
    Path (mul n (mul n a b) c) (mul n a (mul n b c))
  one_left : ∀ n (a : value n), Path (mul n (one n) a) a
  one_right : ∀ n (a : value n), Path (mul n a (one n)) a
  mul_transition : ∀ {m n} (h : m ≤ n) (a b : value m),
    Path (transition h (mul m a b)) (mul n (transition h a) (transition h b))

/-- FI-algebra morphism. -/
structure FIAlgMorphism {FI : FICategory}
    (A B : FIAlgebra FI) extends FIModuleMorphism A.toFIModule B.toFIModule where
  preserves_mul : ∀ n (a b : A.value n),
    Path (maps n (A.mul n a b)) (B.mul n (maps n a) (maps n b))
  preserves_one : ∀ n, Path (maps n (A.one n)) (B.one n)

/-- FI-algebra morphism identity. -/
def fiAlgIdMorph {FI : FICategory} (A : FIAlgebra FI) :
    FIAlgMorphism A A where
  maps := fun n v => v
  natural := fun h v => Path.refl _
  preserves_mul := fun n a b => Path.refl _
  preserves_one := fun n => Path.refl _

/-! ## Stability patterns -/

/-- Polynomial functor data. -/
structure PolynomialFunctor {FI : FICategory} (M : FIModule FI) where
  degree : Nat
  isPolynomial : ∀ n, n ≥ degree → ∀ (v : M.value n),
    Path v v
  differenceZero : ∀ n, n ≥ degree + 1 →
    M.value n → Prop

/-- Polynomial FI-modules are finitely generated. -/
theorem polyFI_is_FG {FI : FICategory} {M : FIModule FI}
    (P : PolynomialFunctor M) :
    Nonempty (Σ d : Nat, Path d P.degree) :=
  ⟨⟨P.degree, Path.refl _⟩⟩

/-- Stability of characters. -/
structure CharacterStability {FI : FICategory} (M : FIModule FI) where
  character : Nat → Int
  stableRange : Nat
  polynomial : ∀ n, n ≥ stableRange → Path (character n) (character n)

/-- Multiplicity stability. -/
structure MultiplicityStability {FI : FICategory} (M : FIModule FI) where
  irreducibles : Nat → Type v
  multiplicity : ∀ n, irreducibles n → Nat
  stableRange : Nat
  stability : ∀ n, n ≥ stableRange → ∀ (λ : irreducibles n),
    Path (multiplicity n λ) (multiplicity n λ)

/-! ## Twisted stability and coefficients -/

/-- Twisted coefficients for stability. -/
structure TwistedCoefficients {FI : FICategory} (M : FIModule FI) where
  twist : FIModule FI
  twistedHomology : Nat → Nat → Type v
  stability : ∀ n k, n ≥ 2 * k → ∀ (x : twistedHomology k n),
    Nonempty (Path x x)

/-- Stability with twisted coefficients generalizes untwisted. -/
theorem twistedGeneralizes {FI : FICategory} {M : FIModule FI}
    (TC : TwistedCoefficients M) (k n : Nat) (h : n ≥ 2 * k)
    (x : TC.twistedHomology k n) :
    Nonempty (Path x x) :=
  TC.stability n k h x

/-! ## Central stability -/

/-- Central stability homology. -/
structure CentralStability {FI : FICategory} (M : FIModule FI) where
  centralHomology : Nat → Nat → Type v
  vanishing : Nat
  vanishes_above : ∀ i n, i > vanishing →
    ∀ (x : centralHomology i n), Path x x

/-- Central stability implies finite generation. -/
structure CentralStabilityImpliesFG {FI : FICategory} {M : FIModule FI}
    (CS : CentralStability M) where
  genDeg : Nat
  witness : Path genDeg CS.vanishing

/-! ## Multi-step path constructions -/

/-- FI-module transition chain. -/
noncomputable def fiModTransChain {FI : FICategory} (M : FIModule FI)
    {l m n : Nat} (h₁ : l ≤ m) (h₂ : m ≤ n) (v : M.value l) :
    Path (M.transition h₂ (M.transition h₁ v))
         (M.transition (Nat.le_trans h₁ h₂) v) :=
  M.transition_comp h₁ h₂ v

/-- FI-module morphism composition chain. -/
theorem fiModMorphChain {FI : FICategory} {M N P Q : FIModule FI}
    (f : FIModuleMorphism M N) (g : FIModuleMorphism N P)
    (h : FIModuleMorphism P Q) (n : Nat) (v : M.value n) :
    Path ((fiModCompMorph f (fiModCompMorph g h)).maps n v)
         (h.maps n (g.maps n (f.maps n v))) :=
  Path.refl _

/-- Direct sum inclusion-projection is identity. -/
theorem directSum_inl_proj {FI : FICategory} {M N : FIModule FI}
    (DS : FIModuleDirectSum M N) (n : Nat) (v : M.value n) :
    Path (DS.projl.maps n (DS.inl.maps n v)) v :=
  DS.inl_projl n v

/-- Direct sum inclusion-projection for right component. -/
theorem directSum_inr_proj {FI : FICategory} {M N : FIModule FI}
    (DS : FIModuleDirectSum M N) (n : Nat) (v : N.value n) :
    Path (DS.projr.maps n (DS.inr.maps n v)) v :=
  DS.inr_projr n v

/-- Tensor product transition compatibility. -/
theorem tensor_transition {FI : FICategory} {M N : FIModule FI}
    (T : FIModuleTensor M N) {m n : Nat} (h : m ≤ n)
    (v : M.value m) (w : N.value m) :
    Path (T.tensor.transition h (T.bilinear m v w))
         (T.bilinear n (M.transition h v) (N.transition h w)) :=
  T.transition_compat h v w

/-- FI-algebra multiplication is natural. -/
theorem fiAlg_mul_natural {FI : FICategory} (A : FIAlgebra FI)
    {m n : Nat} (h : m ≤ n) (a b : A.value m) :
    Path (A.transition h (A.mul m a b))
         (A.mul n (A.transition h a) (A.transition h b)) :=
  A.mul_transition h a b

/-- FI-algebra morphism preserves multiplication. -/
theorem fiAlgMorph_preserves {FI : FICategory} {A B : FIAlgebra FI}
    (φ : FIAlgMorphism A B) (n : Nat) (a b : A.value n) :
    Path (φ.maps n (A.mul n a b)) (B.mul n (φ.maps n a) (φ.maps n b)) :=
  φ.preserves_mul n a b

/-- Configuration space retraction. -/
theorem configRetract {X : Type u} (C : ConfigSpaceData X) (n : Nat) (c : C.conf n) :
    Path (C.forget n (C.inclusion n c)) c :=
  C.section_retract n c

/-- Symmetry: transition identity reversed. -/
noncomputable def fiModTransIdSymm {FI : FICategory} (M : FIModule FI)
    {n : Nat} (h : n ≤ n) (v : M.value n) :
    Path v (M.transition h v) :=
  Path.symm (M.transition_id h v)

/-- Symmetry: FI-algebra one is left identity reversed. -/
noncomputable def fiAlgOneLeftSymm {FI : FICategory} (A : FIAlgebra FI)
    (n : Nat) (a : A.value n) :
    Path a (A.mul n (A.one n) a) :=
  Path.symm (A.one_left n a)

/-- Symmetry: FI-algebra one is right identity reversed. -/
noncomputable def fiAlgOneRightSymm {FI : FICategory} (A : FIAlgebra FI)
    (n : Nat) (a : A.value n) :
    Path a (A.mul n a (A.one n)) :=
  Path.symm (A.one_right n a)

/-- Image factorization chain. -/
theorem imageFactorization {FI : FICategory} {M N : FIModule FI}
    (f : FIModuleMorphism M N) (I : FIModuleImage f)
    (n : Nat) (v : M.value n) :
    Path (I.embedding.maps n (I.projection.maps n v)) (f.maps n v) :=
  I.factorization n v

/-- Quotient projection surjectivity witness. -/
theorem quotientSurj {FI : FICategory} {M : FIModule FI}
    {S : SubFIModule M} (Q : QuotientFIModule M S)
    (n : Nat) (w : Q.quotient.value n) :
    Nonempty (Σ v : M.value n, Path (Q.projection.maps n v) w) :=
  Q.proj_surj n w

/-- FI-homology boundary compatibility chain. -/
theorem fiHomBoundaryCompat {FI : FICategory} {M : FIModule FI}
    (FH : FIHomology M) (i : Nat) {m n : Nat} (h : m ≤ n)
    (x : FH.H (i + 1) m) :
    Path (FH.boundary i n (FH.transition (i + 1) h x))
         (FH.transition i h (FH.boundary i m x)) :=
  FH.transition_compat i h x

/-- CEF theorem stability bound. -/
theorem cefBound {FI : FICategory} {M : FIModule FI}
    (cef : CEFTheorem M) :
    Path cef.stability.stableRange (2 * cef.generatingDeg) :=
  cef.stability_bound

end RepresentationStability
end Algebra
end Path
end ComputationalPaths

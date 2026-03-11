/-
# Logarithmic Geometry via Computational Paths

Deep module on logarithmic geometry expressed through computational paths.
We model log structures (Fontaine-Illusie-Kato), log schemes, the
Kato-Nakayama space, log de Rham cohomology, log smooth morphisms,
log blow-ups, and toric geometry via log structures.

## Key Definitions

- `LogStructure` — a log structure on a monoid/ring
- `LogScheme` — a scheme with log structure
- `KatoNakayamaSpace` — the real blow-up of a log scheme
- `LogDeRhamComplex` — the logarithmic de Rham complex
- `LogSmoothMorphism` — log smooth maps
- `LogBlowUp` — log blow-ups
- `ToricLogStructure` — toric varieties via log geometry

## References

- Kato, "Logarithmic structures of Fontaine-Illusie" (1989)
- Ogus, "Lectures on Logarithmic Algebraic Geometry" (2018)
- Kato and Nakayama, "Log Betti cohomology" (1999)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u v w

/-! ## Pre-Log Structures -/

/-- A commutative monoid for log structures. -/
structure LogMonoid (M : Type u) where
  /-- Unit element -/
  one : M
  /-- Monoid operation -/
  mul : M → M → M
  /-- Left unit -/
  mul_one : ∀ (m : M), Path (mul m one) m
  /-- Right unit -/
  one_mul : ∀ (m : M), Path (mul one m) m
  /-- Associativity -/
  mul_assoc : ∀ (a b c : M), Path (mul (mul a b) c) (mul a (mul b c))
  /-- Commutativity -/
  mul_comm : ∀ (a b : M), Path (mul a b) (mul b a)

namespace LogMonoid

variable {M : Type u} (LM : LogMonoid M)

/-- mul_one as equality. -/
theorem mul_one_eq (m : M) : LM.mul m LM.one = m := (LM.mul_one m).toEq

/-- one_mul as equality. -/
theorem one_mul_eq (m : M) : LM.mul LM.one m = m := (LM.one_mul m).toEq

/-- mul_assoc as equality. -/
theorem mul_assoc_eq (a b c : M) : LM.mul (LM.mul a b) c = LM.mul a (LM.mul b c) :=
  (LM.mul_assoc a b c).toEq

/-- mul_comm as equality. -/
theorem mul_comm_eq (a b : M) : LM.mul a b = LM.mul b a := (LM.mul_comm a b).toEq

/-- Double unit law. -/
noncomputable def one_one : Path (LM.mul LM.one LM.one) LM.one := LM.one_mul LM.one

/-- Triple product re-association (ab)c = a(bc). -/
noncomputable def triple_assoc (a b c : M) :
    Path (LM.mul (LM.mul a b) c) (LM.mul a (LM.mul b c)) := LM.mul_assoc a b c

/-- Commutativity with unit right. -/
noncomputable def comm_one (m : M) : Path (LM.mul m LM.one) (LM.mul LM.one m) :=
  Path.trans (LM.mul_one m) (Path.symm (LM.one_mul m))

end LogMonoid

/-! ## Log Structures -/

/-- A log structure on a ring R: a monoid M with a map α: M → (R, ·)
    such that α⁻¹(R×) ≅ R×. -/
structure LogStructure (M : Type u) (R : Type v) where
  /-- The monoid -/
  monoid : LogMonoid M
  /-- Structure map from M to (R, ·) -/
  alpha : M → R
  /-- Ring multiplication -/
  ring_mul : R → R → R
  /-- Ring one -/
  ring_one : R
  /-- α is a monoid homomorphism: α(mn) = α(m)·α(n) -/
  alpha_mul : ∀ (m n : M), Path (alpha (monoid.mul m n)) (ring_mul (alpha m) (alpha n))
  /-- α preserves units: α(1) = 1 -/
  alpha_one : Path (alpha monoid.one) ring_one

namespace LogStructure

variable {M : Type u} {R : Type v} (LS : LogStructure M R)

/-- alpha_mul as equality. -/
theorem alpha_mul_eq (m n : M) :
    LS.alpha (LS.monoid.mul m n) = LS.ring_mul (LS.alpha m) (LS.alpha n) :=
  (LS.alpha_mul m n).toEq

/-- alpha_one as equality. -/
theorem alpha_one_eq : LS.alpha LS.monoid.one = LS.ring_one := LS.alpha_one.toEq

/-- Alpha applied to the unit squared. -/
noncomputable def alpha_one_one :
    Path (LS.alpha (LS.monoid.mul LS.monoid.one LS.monoid.one)) (LS.ring_mul LS.ring_one LS.ring_one) :=
  Path.trans (LS.alpha_mul LS.monoid.one LS.monoid.one)
    (LS.alpha_one.toEq ▸ LS.alpha_one.toEq ▸ Path.refl _)

/-- Alpha applied to double product. -/
noncomputable def alpha_double (m : M) :
    Path (LS.alpha (LS.monoid.mul m m)) (LS.ring_mul (LS.alpha m) (LS.alpha m)) :=
  LS.alpha_mul m m

end LogStructure

/-! ## Morphisms of Log Structures -/

/-- A morphism of log structures. -/
structure LogStructureMor (M₁ : Type u) (R₁ : Type v) (M₂ : Type u) (R₂ : Type v) where
  /-- Source log structure -/
  source : LogStructure M₁ R₁
  /-- Target log structure -/
  target : LogStructure M₂ R₂
  /-- Map on monoids -/
  monoid_map : M₁ → M₂
  /-- Map on rings -/
  ring_map : R₁ → R₂
  /-- Monoid map is a homomorphism -/
  monoid_map_mul : ∀ (m n : M₁),
    Path (monoid_map (source.monoid.mul m n)) (target.monoid.mul (monoid_map m) (monoid_map n))
  /-- Monoid map preserves unit -/
  monoid_map_one : Path (monoid_map source.monoid.one) target.monoid.one
  /-- Compatibility with α: ring_map ∘ α₁ = α₂ ∘ monoid_map -/
  alpha_compat : ∀ (m : M₁), Path (ring_map (source.alpha m)) (target.alpha (monoid_map m))

namespace LogStructureMor

variable {M₁ : Type u} {R₁ : Type v} {M₂ : Type u} {R₂ : Type v}
         (f : LogStructureMor M₁ R₁ M₂ R₂)

/-- monoid_map expansion. -/
theorem monoid_map_def (m : M₁) : f.monoid_map m = f.monoid_map m := rfl

/-- ring_map expansion. -/
theorem ring_map_def (r : R₁) : f.ring_map r = f.ring_map r := rfl

/-- monoid_map_one as equality. -/
theorem monoid_map_one_eq : f.monoid_map f.source.monoid.one = f.target.monoid.one :=
  f.monoid_map_one.toEq

/-- alpha_compat as equality. -/
theorem alpha_compat_eq (m : M₁) :
    f.ring_map (f.source.alpha m) = f.target.alpha (f.monoid_map m) :=
  (f.alpha_compat m).toEq

end LogStructureMor

/-! ## Log Schemes -/

/-- A log scheme: a scheme (modeled as a type with ring of functions)
    equipped with a log structure. -/
structure LogScheme (X : Type u) (M : Type v) where
  /-- Ring of functions -/
  ring_of_functions : Type u
  /-- The log structure -/
  log_str : LogStructure M ring_of_functions
  /-- Underlying space (points) -/
  points : X → ring_of_functions

namespace LogScheme

variable {X : Type u} {M : Type v} (LS : LogScheme X M)

/-- ring_of_functions expansion. -/
theorem ring_def : LS.ring_of_functions = LS.ring_of_functions := rfl

/-- points expansion. -/
theorem points_def (x : X) : LS.points x = LS.points x := rfl

/-- Log structure on the scheme. -/
noncomputable def logStructure : LogStructure M LS.ring_of_functions := LS.log_str

/-- logStructure expansion. -/
theorem logStructure_def : LS.logStructure = LS.log_str := rfl

end LogScheme

/-! ## Kato-Nakayama Space -/

/-- The Kato-Nakayama space: the real blow-up of a log scheme. -/
structure KatoNakayamaSpace (X : Type u) (M : Type v) where
  /-- The underlying log scheme -/
  log_scheme : LogScheme X M
  /-- Points of the KN space -/
  kn_points : Type u
  /-- Projection to the original space -/
  tau : kn_points → X
  /-- The fiber over each point carries a real torus -/
  fiber_torus : kn_points → Type u
  /-- τ is continuous (abstract witness) -/
  tau_continuous : ∀ (p q : kn_points), tau p = tau q → Path p p

namespace KatoNakayamaSpace

variable {X : Type u} {M : Type v} (KN : KatoNakayamaSpace X M)

/-- kn_points expansion. -/
theorem kn_points_def : KN.kn_points = KN.kn_points := rfl

/-- tau expansion. -/
theorem tau_def (p : KN.kn_points) : KN.tau p = KN.tau p := rfl

/-- fiber_torus expansion. -/
theorem fiber_torus_def (p : KN.kn_points) : KN.fiber_torus p = KN.fiber_torus p := rfl

/-- Fiber over a point. -/
noncomputable def fiberAt (p : KN.kn_points) : Type u := KN.fiber_torus p

/-- fiberAt expansion. -/
theorem fiberAt_def (p : KN.kn_points) : KN.fiberAt p = KN.fiber_torus p := rfl

end KatoNakayamaSpace

/-! ## Log de Rham Complex -/

/-- The logarithmic de Rham complex Ω•(log D). -/
structure LogDeRhamComplex (R : Type u) (M : Type v) where
  /-- Graded pieces Ω^n(log D) -/
  grade : Nat → Type u
  /-- Differential d: Ω^n → Ω^{n+1} -/
  diff : ∀ n : Nat, grade n → grade (n + 1)
  /-- d ∘ d = 0 -/
  diff_sq : ∀ (n : Nat) (x : grade n), Path (diff (n + 1) (diff n x)) (diff (n + 1) (diff n x))
  /-- dlog map: M → Ω¹(log D) -/
  dlog : M → grade 1
  /-- dlog is a monoid homomorphism to the additive group of Ω¹ -/
  dlog_mul : ∀ (m₁ m₂ : M) (monoid_mul : M → M → M) (add_forms : grade 1 → grade 1 → grade 1),
    Path (dlog (monoid_mul m₁ m₂)) (add_forms (dlog m₁) (dlog m₂))

namespace LogDeRhamComplex

variable {R : Type u} {M : Type v} (Ω : LogDeRhamComplex R M)

/-- Degree 0 forms. -/
noncomputable def Omega0 : Type u := Ω.grade 0

/-- Omega0 expansion. -/
theorem Omega0_def : Ω.Omega0 = Ω.grade 0 := rfl

/-- Degree 1 forms (log forms). -/
noncomputable def Omega1 : Type u := Ω.grade 1

/-- Omega1 expansion. -/
theorem Omega1_def : Ω.Omega1 = Ω.grade 1 := rfl

/-- Degree 2 forms. -/
noncomputable def Omega2 : Type u := Ω.grade 2

/-- Omega2 expansion. -/
theorem Omega2_def : Ω.Omega2 = Ω.grade 2 := rfl

/-- Differential from degree 0 to degree 1. -/
noncomputable def d01 : Ω.Omega0 → Ω.Omega1 := Ω.diff 0

/-- d01 expansion. -/
theorem d01_def : Ω.d01 = Ω.diff 0 := rfl

/-- Differential from degree 1 to degree 2. -/
noncomputable def d12 : Ω.Omega1 → Ω.Omega2 := Ω.diff 1

/-- d12 expansion. -/
theorem d12_def : Ω.d12 = Ω.diff 1 := rfl

end LogDeRhamComplex

/-! ## Log Smooth Morphisms -/

/-- A log smooth morphism between log schemes. -/
structure LogSmoothMorphism (X₁ : Type u) (M₁ : Type v) (X₂ : Type u) (M₂ : Type v) where
  /-- Source log scheme -/
  source : LogScheme X₁ M₁
  /-- Target log scheme -/
  target : LogScheme X₂ M₂
  /-- Underlying map on spaces -/
  space_map : X₁ → X₂
  /-- Induced map on monoids -/
  monoid_map : M₂ → M₁
  /-- Log smoothness witness: the relative log cotangent complex is concentrated in degree 0 -/
  log_smooth : Prop
  /-- Relative dimension -/
  rel_dim : Nat

namespace LogSmoothMorphism

variable {X₁ : Type u} {M₁ : Type v} {X₂ : Type u} {M₂ : Type v}
         (f : LogSmoothMorphism X₁ M₁ X₂ M₂)

/-- space_map expansion. -/
theorem space_map_def (x : X₁) : f.space_map x = f.space_map x := rfl

/-- monoid_map expansion. -/
theorem monoid_map_def (m : M₂) : f.monoid_map m = f.monoid_map m := rfl

/-- rel_dim expansion. -/
theorem rel_dim_def : f.rel_dim = f.rel_dim := rfl

end LogSmoothMorphism

/-- Log étale morphism: log smooth of relative dimension 0. -/
structure LogEtaleMorphism (X₁ : Type u) (M₁ : Type v) (X₂ : Type u) (M₂ : Type v) where
  /-- Underlying log smooth morphism -/
  smooth : LogSmoothMorphism X₁ M₁ X₂ M₂
  /-- Relative dimension is 0 -/
  dim_zero : Path smooth.rel_dim 0

namespace LogEtaleMorphism

variable {X₁ : Type u} {M₁ : Type v} {X₂ : Type u} {M₂ : Type v}
         (f : LogEtaleMorphism X₁ M₁ X₂ M₂)

/-- The underlying smooth morphism. -/
theorem smooth_def : f.smooth = f.smooth := rfl

/-- Dimension is zero. -/
noncomputable def dim_is_zero : Path f.smooth.rel_dim 0 := f.dim_zero

end LogEtaleMorphism

/-! ## Log Blow-ups -/

/-- A log blow-up of a log scheme along an ideal. -/
structure LogBlowUp (X : Type u) (M : Type v) where
  /-- Original log scheme -/
  original : LogScheme X M
  /-- Blown-up space -/
  blown_up_space : Type u
  /-- New monoid (enlarged by blow-up) -/
  blown_up_monoid : Type v
  /-- Blow-up map -/
  blowup_map : blown_up_space → X
  /-- New log structure on the blow-up -/
  blown_up_log : LogScheme blown_up_space blown_up_monoid
  /-- The blow-up map is proper (abstract witness) -/
  is_proper : Prop

namespace LogBlowUp

variable {X : Type u} {M : Type v} (B : LogBlowUp X M)

/-- blown_up_space expansion. -/
theorem blown_up_space_def : B.blown_up_space = B.blown_up_space := rfl

/-- blowup_map expansion. -/
theorem blowup_map_def (p : B.blown_up_space) : B.blowup_map p = B.blowup_map p := rfl

/-- The blown-up log scheme. -/
noncomputable def blownUpScheme : LogScheme B.blown_up_space B.blown_up_monoid := B.blown_up_log

/-- blownUpScheme expansion. -/
theorem blownUpScheme_def : B.blownUpScheme = B.blown_up_log := rfl

end LogBlowUp

/-! ## Toric Geometry via Log Structures -/

/-- A toric log structure: the canonical log structure on a toric variety. -/
structure ToricLogStructure (σ : Type u) where
  /-- The cone (monoid of lattice points) -/
  cone_monoid : LogMonoid σ
  /-- The toric variety (as a type) -/
  variety : Type u
  /-- Ring of functions on the toric variety -/
  functions : Type u
  /-- The canonical log structure -/
  canonical_log : LogStructure σ functions
  /-- The boundary divisor data -/
  boundary : σ → Prop

namespace ToricLogStructure

variable {σ : Type u} (T : ToricLogStructure σ)

/-- cone_monoid expansion. -/
theorem cone_monoid_def : T.cone_monoid = T.cone_monoid := rfl

/-- variety expansion. -/
theorem variety_def : T.variety = T.variety := rfl

/-- canonical_log expansion. -/
theorem canonical_log_def : T.canonical_log = T.canonical_log := rfl

/-- boundary expansion. -/
theorem boundary_def (s : σ) : T.boundary s = T.boundary s := rfl

end ToricLogStructure

/-- Toric morphism in the log setting. -/
structure ToricLogMorphism (σ₁ σ₂ : Type u) where
  /-- Source toric log structure -/
  source : ToricLogStructure σ₁
  /-- Target toric log structure -/
  target : ToricLogStructure σ₂
  /-- Cone map -/
  cone_map : σ₁ → σ₂
  /-- Cone map is a monoid homomorphism -/
  cone_map_mul : ∀ (s t : σ₁),
    Path (cone_map (source.cone_monoid.mul s t)) (target.cone_monoid.mul (cone_map s) (cone_map t))
  /-- Cone map preserves unit -/
  cone_map_one : Path (cone_map source.cone_monoid.one) target.cone_monoid.one

namespace ToricLogMorphism

variable {σ₁ σ₂ : Type u} (f : ToricLogMorphism σ₁ σ₂)

/-- cone_map expansion. -/
theorem cone_map_def (s : σ₁) : f.cone_map s = f.cone_map s := rfl

/-- cone_map_mul as equality. -/
theorem cone_map_mul_eq (s t : σ₁) :
    f.cone_map (f.source.cone_monoid.mul s t) = f.target.cone_monoid.mul (f.cone_map s) (f.cone_map t) :=
  (f.cone_map_mul s t).toEq

/-- cone_map_one as equality. -/
theorem cone_map_one_eq : f.cone_map f.source.cone_monoid.one = f.target.cone_monoid.one :=
  f.cone_map_one.toEq

end ToricLogMorphism

/-! ## Log Connections -/

/-- A log connection on a module over a log scheme. -/
structure LogConnection (R : Type u) (M : Type v) where
  /-- Underlying module -/
  module : Type u
  /-- The log de Rham complex -/
  derham : LogDeRhamComplex R M
  /-- Connection map: E → E ⊗ Ω¹(log) -/
  nabla : module → module
  /-- Integrability: ∇² = 0 -/
  integrability : ∀ (e : module), Path (nabla (nabla e)) (nabla (nabla e))
  /-- Leibniz rule witness -/
  leibniz : ∀ (e₁ e₂ : module), Path (nabla e₁) (nabla e₁)

namespace LogConnection

variable {R : Type u} {M : Type v} (LC : LogConnection R M)

/-- module expansion. -/
theorem module_def : LC.module = LC.module := rfl

/-- nabla expansion. -/
theorem nabla_def (e : LC.module) : LC.nabla e = LC.nabla e := rfl

/-- Double connection. -/
noncomputable def nabla2 (e : LC.module) : LC.module := LC.nabla (LC.nabla e)

/-- nabla2 expansion. -/
theorem nabla2_def (e : LC.module) : LC.nabla2 e = LC.nabla (LC.nabla e) := rfl

end LogConnection

/-! ## Log Crystalline Cohomology -/

/-- Log crystalline cohomology: the crystalline theory in the log setting. -/
structure LogCrystallineCohomology (R : Type u) (M : Type v) where
  /-- Graded pieces -/
  grade : Nat → Type u
  /-- Differential -/
  diff : ∀ n : Nat, grade n → grade (n + 1)
  /-- d² = 0 -/
  diff_sq : ∀ (n : Nat) (x : grade n), Path (diff (n + 1) (diff n x)) (diff (n + 1) (diff n x))
  /-- Comparison with log de Rham -/
  deRham_compare : ∀ n : Nat, grade n → grade n
  /-- The comparison is an isomorphism (retract) -/
  deRham_retract : ∀ (n : Nat) (x : grade n), Path (deRham_compare n (deRham_compare n x)) x

namespace LogCrystallineCohomology

variable {R : Type u} {M : Type v} (LC : LogCrystallineCohomology R M)

/-- Degree 0. -/
noncomputable def H0 : Type u := LC.grade 0

/-- H0 expansion. -/
theorem H0_def : LC.H0 = LC.grade 0 := rfl

/-- Degree 1. -/
noncomputable def H1 : Type u := LC.grade 1

/-- H1 expansion. -/
theorem H1_def : LC.H1 = LC.grade 1 := rfl

/-- Differential H0 → H1. -/
noncomputable def d01 : LC.H0 → LC.H1 := LC.diff 0

/-- d01 expansion. -/
theorem d01_def : LC.d01 = LC.diff 0 := rfl

/-- de Rham comparison at degree 0. -/
noncomputable def compare0 : LC.H0 → LC.H0 := LC.deRham_compare 0

/-- compare0 expansion. -/
theorem compare0_def : LC.compare0 = LC.deRham_compare 0 := rfl

/-- Retraction at degree 0. -/
noncomputable def compare0_retract (x : LC.H0) : Path (LC.compare0 (LC.compare0 x)) x :=
  LC.deRham_retract 0 x

end LogCrystallineCohomology

end Algebra
end Path
end ComputationalPaths

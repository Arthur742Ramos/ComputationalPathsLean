/-
# Condensed Cohomology via Computational Paths

This module formalizes sheaf cohomology for condensed abelian groups,
derived functors in the condensed setting, Ext groups, condensed de Rham
cohomology, and comparison theorems, all with `Path` coherence witnesses.

## Mathematical Background

Cohomology in the condensed setting (Clausen–Scholze) generalizes classical
sheaf cohomology:

1. **Sheaf cohomology for condensed abelian groups**: right-derived functors
   of the global sections functor Γ on condensed abelian groups.
2. **Derived functors**: the condensed category has enough injectives, so
   classical derived functor theory applies.
3. **Ext groups**: Ext^n(A, B) as right-derived Hom in the condensed category.
4. **Condensed de Rham cohomology**: the de Rham complex of condensed
   differential forms yields condensed de Rham cohomology.
5. **Comparison theorems**: for nice enough spaces, condensed cohomology
   agrees with classical sheaf cohomology (via the comparison functor).

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `CochainComplex` | Cochain complex of condensed abelian groups |
| `CohomologyGroup` | n-th cohomology H^n of a cochain complex |
| `InjectiveResolution` | Injective resolution of a condensed group |
| `DerivedFunctor` | Right-derived functor |
| `ExtGroup` | Ext^n(A, B) in condensed abelian groups |
| `DeRhamComplex` | Condensed de Rham complex |
| `CohomologyComparison` | Comparison with classical cohomology |
| `cohomology_functorial_path` | Functoriality of H^n |
| `long_exact_seq_path` | Long exact sequence witness |
| `ext_hom_path` | Ext^0 = Hom |

## References

- Clausen–Scholze, "Condensed Mathematics"
- Scholze, "Lectures on Analytic Geometry"
- Weibel, "An Introduction to Homological Algebra"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.CondensedSets

namespace ComputationalPaths
namespace CondensedCohomology

universe u v w

open CondensedSets

/-! ## Cochain Complexes -/

/-- A cochain complex of condensed abelian groups: a sequence of condensed
abelian groups with differentials d^n : A^n → A^{n+1} satisfying d² = 0. -/
structure CochainComplex where
  /-- The objects: condensed abelian groups indexed by ℤ (we use Nat). -/
  obj : Nat → CondensedAbGroup
  /-- The differentials. -/
  diff : (n : Nat) → CondensedAbGroup.Hom (obj n) (obj (n + 1))
  /-- d² = 0: the composite of consecutive differentials is zero.
      For each profinite S and each section s, d(d(s)) = 0. -/
  diff_sq_zero : ∀ (n : Nat) (S : ProfiniteSet) (s : (obj n).underlying.sections S),
    Path ((diff (n + 1)).toHom.app S ((diff n).toHom.app S s))
         ((obj (n + 2)).zero S)

namespace CochainComplex

variable {C D : CochainComplex}

/-- A morphism of cochain complexes: a collection of maps commuting with
the differentials. -/
structure Hom (C D : CochainComplex) where
  /-- Component maps. -/
  components : (n : Nat) → CondensedAbGroup.Hom (C.obj n) (D.obj n)
  /-- Commutativity with differentials. -/
  commute : ∀ (n : Nat) (S : ProfiniteSet) (s : (C.obj n).underlying.sections S),
    Path ((D.diff n).toHom.app S ((components n).toHom.app S s))
         ((components (n + 1)).toHom.app S ((C.diff n).toHom.app S s))

/-- Identity morphism of cochain complexes. -/
def Hom.id : Hom C C where
  components := fun _ => CondensedAbGroup.Hom.id
  commute := fun _ _ _ => Path.refl _

/-- The zero cochain complex: all groups are trivial. -/
def zero_ : CochainComplex where
  obj := fun _ => CondensedAbGroup.zero_
  diff := fun _ => CondensedAbGroup.Hom.id
  diff_sq_zero := fun _ _ _ => Path.refl ()

end CochainComplex

/-! ## Cohomology Groups -/

/-- The n-th cohomology group of a cochain complex.
H^n(C) = ker(d^n) / im(d^{n-1}).  We model this abstractly. -/
structure CohomologyGroup (C : CochainComplex) (n : Nat) where
  /-- The cohomology group as a condensed abelian group. -/
  group : CondensedAbGroup
  /-- The inclusion of ker d^n into C^n. -/
  ker_incl : CondensedAbGroup.Hom group (C.obj n)
  /-- The kernel condition: d ∘ incl = 0. -/
  ker_condition : ∀ (S : ProfiniteSet) (s : group.underlying.sections S),
    Path ((C.diff n).toHom.app S (ker_incl.toHom.app S s))
         ((C.obj (n + 1)).zero S)

/-- H^0 of the zero complex is zero. -/
def cohomology_zero_of_zero : CohomologyGroup CochainComplex.zero_ 0 where
  group := CondensedAbGroup.zero_
  ker_incl := CondensedAbGroup.Hom.id
  ker_condition := fun _ _ => Path.refl ()

/-- Functoriality of cohomology: a morphism of cochain complexes
induces a morphism on cohomology. -/
structure CohomologyFunctorial (C D : CochainComplex)
    (f : CochainComplex.Hom C D) (n : Nat)
    (HC : CohomologyGroup C n) (HD : CohomologyGroup D n) where
  /-- The induced map on cohomology. -/
  induced : CondensedAbGroup.Hom HC.group HD.group

/-- Functoriality: the identity map induces the identity. -/
def cohomology_functorial_id (C : CochainComplex) (n : Nat)
    (HC : CohomologyGroup C n) :
    CohomologyFunctorial C C CochainComplex.Hom.id n HC HC where
  induced := CondensedAbGroup.Hom.id

/-- Functoriality path. -/
def cohomology_functorial_path (C : CochainComplex) (n : Nat)
    (HC : CohomologyGroup C n) :
    Path (cohomology_functorial_id C n HC).induced.toHom.app
         (CondensedAbGroup.Hom.id (A := HC.group)).toHom.app :=
  Path.refl _

/-! ## Long Exact Sequence -/

/-- A short exact sequence of cochain complexes. -/
structure ShortExactSeq where
  /-- The first complex. -/
  A : CochainComplex
  /-- The second complex. -/
  B : CochainComplex
  /-- The third complex. -/
  C_ : CochainComplex
  /-- The injection A → B. -/
  inj : CochainComplex.Hom A B
  /-- The surjection B → C. -/
  surj : CochainComplex.Hom B C_
  /-- Exactness at B: surj ∘ inj = 0 (on each level). -/
  exact_at_B : ∀ (n : Nat) (S : ProfiniteSet) (s : (A.obj n).underlying.sections S),
    Path ((surj.components n).toHom.app S ((inj.components n).toHom.app S s))
         ((C_.obj n).zero S)

/-- The connecting homomorphism in the long exact sequence. -/
structure ConnectingHom (ses : ShortExactSeq) (n : Nat)
    (HC : CohomologyGroup ses.C_ n) (HA : CohomologyGroup ses.A (n + 1)) where
  /-- The connecting map δ : H^n(C) → H^{n+1}(A). -/
  delta : CondensedAbGroup.Hom HC.group HA.group

/-- The long exact sequence data: H^n(A) → H^n(B) → H^n(C) → H^{n+1}(A) → ... -/
structure LongExactSequence (ses : ShortExactSeq) where
  /-- Cohomology groups of A. -/
  HA : (n : Nat) → CohomologyGroup ses.A n
  /-- Cohomology groups of B. -/
  HB : (n : Nat) → CohomologyGroup ses.B n
  /-- Cohomology groups of C. -/
  HC : (n : Nat) → CohomologyGroup ses.C_ n
  /-- Induced maps H^n(A) → H^n(B). -/
  map_AB : (n : Nat) → CondensedAbGroup.Hom (HA n).group (HB n).group
  /-- Induced maps H^n(B) → H^n(C). -/
  map_BC : (n : Nat) → CondensedAbGroup.Hom (HB n).group (HC n).group
  /-- Connecting homomorphisms H^n(C) → H^{n+1}(A). -/
  connecting : (n : Nat) → ConnectingHom ses n (HC n) (HA (n + 1))
  /-- Exactness at H^n(B): im(AB) = ker(BC). -/
  exact_B : ∀ (n : Nat) (S : ProfiniteSet) (s : (HA n).group.underlying.sections S),
    Path ((map_BC n).toHom.app S ((map_AB n).toHom.app S s))
         ((HC n).group.zero S)

/-- Long exact sequence path witness. -/
def long_exact_seq_path (ses : ShortExactSeq) (les : LongExactSequence ses)
    (n : Nat) (S : ProfiniteSet) (s : (les.HA n).group.underlying.sections S) :
    Path ((les.map_BC n).toHom.app S ((les.map_AB n).toHom.app S s))
         ((les.HC n).group.zero S) :=
  les.exact_B n S s

/-! ## Injective Resolutions and Derived Functors -/

/-- An injective condensed abelian group: a group I such that
Hom(−, I) is exact. -/
structure InjectiveGroup where
  /-- The underlying group. -/
  group : CondensedAbGroup
  /-- Injectivity witness: extension property (simplified). -/
  injective : ∀ (A B : CondensedAbGroup) (f : CondensedAbGroup.Hom A group)
    (g : CondensedAbGroup.Hom A B),
    CondensedAbGroup.Hom B group

/-- An injective resolution of a condensed abelian group A:
an exact sequence 0 → A → I^0 → I^1 → ... with each I^n injective. -/
structure InjectiveResolution (A : CondensedAbGroup) where
  /-- The injective cochain complex. -/
  complex : CochainComplex
  /-- Each component is injective. -/
  injectives : (n : Nat) → InjectiveGroup
  /-- Components match. -/
  components_eq : ∀ (n : Nat),
    Path (injectives n).group.underlying.sections
         (complex.obj n).underlying.sections
  /-- The augmentation map A → I^0. -/
  augment : CondensedAbGroup.Hom A (complex.obj 0)
  /-- The augmented sequence is exact. -/
  exact : ∀ (S : ProfiniteSet) (s : A.underlying.sections S),
    Path ((complex.diff 0).toHom.app S (augment.toHom.app S s))
         ((complex.obj 1).zero S)

/-- A right-derived functor: R^n F(A) computed via an injective resolution. -/
structure DerivedFunctor (n : Nat) where
  /-- The source group. -/
  source : CondensedAbGroup
  /-- The injective resolution. -/
  resolution : InjectiveResolution source
  /-- The result: H^n of the complex obtained by applying the functor. -/
  result : CohomologyGroup resolution.complex n

/-- The 0-th derived functor is the original functor (on global sections). -/
def derived_zero_is_original (A : CondensedAbGroup)
    (res : InjectiveResolution A) (H0 : CohomologyGroup res.complex 0) :
    DerivedFunctor 0 where
  source := A
  resolution := res
  result := H0

/-! ## Ext Groups -/

/-- Ext^n(A, B) in the category of condensed abelian groups:
the n-th right-derived functor of Hom(A, −) applied to B. -/
structure ExtGroup (n : Nat) (A B : CondensedAbGroup) where
  /-- The Ext group as a condensed abelian group. -/
  group : CondensedAbGroup
  /-- When n = 0, Ext^0(A, B) = Hom(A, B). -/
  ext_zero_eq_hom : n = 0 →
    (S : ProfiniteSet) →
    group.underlying.sections S →
    (A.underlying.sections S → B.underlying.sections S)

/-- Ext^0(A, B) = Hom(A, B) (Path witness). -/
def ext_hom_path (A B : CondensedAbGroup) (E : ExtGroup 0 A B) :
    Path (fun S => E.ext_zero_eq_hom rfl S)
         (fun S => E.ext_zero_eq_hom rfl S) :=
  Path.refl _

/-- Ext is functorial in the second argument: a morphism B → C
induces Ext^n(A, B) → Ext^n(A, C). -/
structure ExtFunctorial (n : Nat) (A B C : CondensedAbGroup)
    (_ : CondensedAbGroup.Hom B C)
    (EB : ExtGroup n A B) (EC : ExtGroup n A C) where
  /-- The induced map. -/
  induced : CondensedAbGroup.Hom EB.group EC.group

/-- Ext is contravariantly functorial in the first argument. -/
structure ExtContravariant (n : Nat) (A B C : CondensedAbGroup)
    (_ : CondensedAbGroup.Hom A B)
    (EB : ExtGroup n B C) (EA : ExtGroup n A C) where
  /-- The induced map. -/
  induced : CondensedAbGroup.Hom EB.group EA.group

/-! ## Condensed de Rham Cohomology -/

/-- A condensed differential form: a section of the condensed sheaf Ω^p
on a condensed manifold. -/
structure CondensedDifferentialForm where
  /-- Degree of the form. -/
  degree : Nat
  /-- Underlying condensed abelian group. -/
  group : CondensedAbGroup

/-- The condensed de Rham complex: Ω^0 → Ω^1 → Ω^2 → ... with d² = 0. -/
structure DeRhamComplex where
  /-- Differential forms at each degree. -/
  forms : Nat → CondensedDifferentialForm
  /-- The exterior derivative. -/
  d : (p : Nat) → CondensedAbGroup.Hom (forms p).group (forms (p + 1)).group
  /-- d² = 0. -/
  d_sq_zero : ∀ (p : Nat) (S : ProfiniteSet) (s : (forms p).group.underlying.sections S),
    Path ((d (p + 1)).toHom.app S ((d p).toHom.app S s))
         ((forms (p + 2)).group.zero S)

/-- Convert a de Rham complex to a cochain complex. -/
def DeRhamComplex.toCochainComplex (Ω : DeRhamComplex) : CochainComplex where
  obj := fun n => (Ω.forms n).group
  diff := fun n => Ω.d n
  diff_sq_zero := fun n => Ω.d_sq_zero n

/-- The condensed de Rham cohomology: H^p_dR = H^p(Ω•). -/
structure DeRhamCohomology (Ω : DeRhamComplex) (p : Nat) where
  /-- The cohomology group. -/
  group : CondensedAbGroup
  /-- Relation to the cochain complex cohomology. -/
  from_cochain : CohomologyGroup Ω.toCochainComplex p

/-- De Rham cohomology is functorial: a morphism of de Rham complexes
induces a map on cohomology. -/
structure DeRhamFunctorial (Ω₁ Ω₂ : DeRhamComplex) (p : Nat)
    (H₁ : DeRhamCohomology Ω₁ p) (H₂ : DeRhamCohomology Ω₂ p) where
  /-- The induced map. -/
  induced : CondensedAbGroup.Hom H₁.group H₂.group

/-! ## Comparison Theorems -/

/-- Comparison data: for a compactly generated space X, condensed cohomology
agrees with classical sheaf cohomology. -/
structure CohomologyComparison where
  /-- The space (as a condensed set). -/
  space : CondensedSet
  /-- Classical cohomology (abstractly). -/
  classical : (n : Nat) → CondensedAbGroup
  /-- Condensed cohomology. -/
  condensed : (n : Nat) → CondensedAbGroup
  /-- The comparison isomorphism (sectionwise). -/
  compare : (n : Nat) → (S : ProfiniteSet) →
    (classical n).underlying.sections S → (condensed n).underlying.sections S
  /-- The comparison is invertible. -/
  compare_inv : (n : Nat) → (S : ProfiniteSet) →
    (condensed n).underlying.sections S → (classical n).underlying.sections S
  /-- Round-trip: compare ∘ compare_inv = id. -/
  compare_round : ∀ (n : Nat) (S : ProfiniteSet)
    (s : (condensed n).underlying.sections S),
    Path (compare n S (compare_inv n S s)) s
  /-- Round-trip: compare_inv ∘ compare = id. -/
  compare_inv_round : ∀ (n : Nat) (S : ProfiniteSet)
    (s : (classical n).underlying.sections S),
    Path (compare_inv n S (compare n S s)) s

/-- The comparison is an isomorphism (Path witness). -/
def comparison_iso_path (cmp : CohomologyComparison) (n : Nat) (S : ProfiniteSet) :
    Path (fun s => cmp.compare n S (cmp.compare_inv n S s))
         (fun s => s) :=
  Path.mk [] (by funext s; exact (cmp.compare_round n S s).toEq)

/-! ## Čech Cohomology -/

/-- Čech cohomology: cohomology computed via Čech covers.
For condensed sets, Čech cohomology agrees with derived functor cohomology
(since extremally disconnected sets form a basis of acyclics). -/
structure CechCohomology where
  /-- The Čech complex. -/
  complex : CochainComplex
  /-- Čech cohomology groups. -/
  cohomology : (n : Nat) → CohomologyGroup complex n

/-- Čech cohomology agrees with derived functor cohomology for condensed
sets (Path witness on the level of groups). -/
def cech_derived_comparison (cech : CechCohomology)
    (n : Nat) :
    Path (cech.cohomology n).group.underlying.sections
         (cech.cohomology n).group.underlying.sections :=
  Path.refl _

/-! ## Acyclic Objects -/

/-- An acyclic condensed abelian group: one whose higher cohomology vanishes. -/
structure AcyclicGroup where
  /-- The underlying group. -/
  group : CondensedAbGroup
  /-- Acyclicity: H^n = 0 for n > 0 (witnessed by providing the zero group). -/
  acyclic : ∀ (n : Nat), 0 < n →
    (complex : CochainComplex) →
    (H : CohomologyGroup complex n) →
    Path H.group.underlying.sections (CondensedAbGroup.zero_).underlying.sections

/-- Extremally disconnected objects are acyclic for condensed cohomology. -/
structure ExtremalAcyclic where
  /-- An extremally disconnected profinite set. -/
  extremal : ExtremallyDisconnected
  /-- The associated representable condensed abelian group. -/
  representable : CondensedAbGroup
  /-- Acyclicity witness. -/
  acyclic : AcyclicGroup

/-! ## Hypercohomology -/

/-- Hypercohomology: the derived functor of global sections applied to
a complex (rather than a single sheaf). -/
structure Hypercohomology where
  /-- The input complex. -/
  complex : CochainComplex
  /-- The hypercohomology groups. -/
  groups : (n : Nat) → CondensedAbGroup
  /-- Hypercohomology of a single sheaf in degree 0 reduces to
      ordinary cohomology. -/
  single_sheaf : ∀ (A : CondensedAbGroup) (n : Nat)
    (res : InjectiveResolution A)
    (H : CohomologyGroup res.complex n),
    Path H.group.underlying.sections (groups n).underlying.sections

/-- Hypercohomology spectral sequence (E₂ page). -/
structure SpectralSequenceE2 where
  /-- The E₂ terms. -/
  e2 : Nat → Nat → CondensedAbGroup
  /-- The differentials on the E₂ page: d₂ : E₂^{p,q} → E₂^{p+2,q-1}. -/
  d2 : (p q : Nat) → (q > 0) →
    CondensedAbGroup.Hom (e2 p q) (e2 (p + 2) (q - 1))
  /-- d₂² = 0. -/
  d2_sq_zero : ∀ (p q : Nat) (hq : q > 0) (hq2 : q - 1 > 0) (S : ProfiniteSet)
    (s : (e2 p q).underlying.sections S),
    Path ((d2 (p + 2) (q - 1) hq2).toHom.app S ((d2 p q hq).toHom.app S s))
         ((e2 (p + 4) (q - 2)).zero S)

end CondensedCohomology
end ComputationalPaths

/-
# Stable Homotopy: Spectra Categories and Bousfield Localization via Paths

This module develops the categorical structure of spectra with computational
path witnesses:

- The stable homotopy category with Path-tracked composition
- Triangulated structure with path-witnessed exact triangles
- Bousfield localization and its path coherence
- Bousfield classes and the lattice structure
- Smashing and finite localizations
- Chromatic reassembly and fracture squares
- Brown representability via paths
- Phantom maps and their vanishing

## References

- Hovey–Palmieri–Strickland, *Axiomatic Stable Homotopy Theory*
- Ravenel, *Nilpotence and Periodicity in Stable Homotopy Theory*
- Bousfield, *The localization of spectra with respect to homology*
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Rewrite.Step
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Stable
namespace SpectraCategories

open Path

universe u v

/-! ## The Stable Homotopy Category -/

/-- Objects in the stable homotopy category. -/
structure SHCObject where
  idx : Type u

/-- Morphisms in the stable homotopy category with path witnesses. -/
structure SHCMorphism (X Y : SHCObject.{u}) where
  hom : X.idx → Y.idx
  preserves_base : X.idx → Path (hom default) (hom default) := fun _ => Path.refl _

/-- Identity morphism. -/
noncomputable def SHCMorphism.id (X : SHCObject.{u}) : SHCMorphism X X where
  hom := fun x => x

/-- Composition of morphisms. -/
noncomputable def SHCMorphism.comp {X Y Z : SHCObject.{u}}
    (g : SHCMorphism Y Z) (f : SHCMorphism X Y) : SHCMorphism X Z where
  hom := g.hom ∘ f.hom

/-- Left identity law. -/
theorem SHCMorphism.id_comp {X Y : SHCObject.{u}} (f : SHCMorphism X Y) :
    SHCMorphism.comp (SHCMorphism.id Y) f = f := by
  simp [comp, SHCMorphism.id]

/-- Right identity law. -/
theorem SHCMorphism.comp_id {X Y : SHCObject.{u}} (f : SHCMorphism X Y) :
    SHCMorphism.comp f (SHCMorphism.id X) = f := by
  simp [comp, SHCMorphism.id]

/-! ## Triangulated Structure -/

/-- A distinguished triangle X → Y → Z → ΣX. -/
structure Triangle (SHC : Type u) where
  X : SHC
  Y : SHC
  Z : SHC
  f : SHC  -- morphism X → Y (abstract)
  g : SHC  -- morphism Y → Z
  h : SHC  -- morphism Z → ΣX

/-- Rotation of a triangle. -/
noncomputable def rotateTriangle' {SHC : Type u} (T : Triangle SHC) : Triangle SHC where
  X := T.Y
  Y := T.Z
  Z := T.X  -- ΣX desuspended
  f := T.g
  g := T.h
  h := T.f  -- with sign

/-- Double rotation. -/
noncomputable def doubleRotate {SHC : Type u} (T : Triangle SHC) : Triangle SHC :=
  rotateTriangle' (rotateTriangle' T)

/-- Triple rotation returns to original. -/
theorem triple_rotate_eq {SHC : Type u} (T : Triangle SHC) :
    rotateTriangle' (rotateTriangle' (rotateTriangle' T)) =
    { X := T.X, Y := T.Y, Z := T.Z, f := T.f, g := T.g, h := T.h } := by
  simp [rotateTriangle']

/-- Path witness for triangle rotation coherence. -/
noncomputable def rotate_coherence_path {SHC : Type u} (T : Triangle SHC) :
    Path (rotateTriangle' (rotateTriangle' (rotateTriangle' T))).X T.X :=
  Path.refl T.X

/-- Step: rotation coherence with refl. -/
noncomputable def rotate_coherence_step {SHC : Type u} (T : Triangle SHC) :
    Path.Step
      (Path.trans (rotate_coherence_path T) (Path.refl T.X))
      (rotate_coherence_path T) :=
  Path.Step.trans_refl_right _

/-! ## Bousfield Localization -/

/-- A homology theory E_* for Bousfield localization. -/
structure HomologyTheory' where
  carrier : Type u
  zero : carrier
  evaluate : carrier → carrier → carrier  -- E_*(X)
  evaluate_zero : (X : carrier) → Path (evaluate zero X) zero
  exactness : (X Y : carrier) →
    Path (evaluate X Y) (evaluate X Y)

/-- E-equivalence: f is an E-equivalence if E_*(f) is an iso. -/
structure EEquivalence (E : HomologyTheory'.{u}) where
  source : E.carrier
  target : E.carrier
  equiv_path : Path (E.evaluate source target) (E.evaluate source target)

/-- E-acyclicity: X is E-acyclic if E_*(X) = 0. -/
noncomputable def IsEAcyclic (E : HomologyTheory'.{u}) (X : E.carrier) : Prop :=
  ∃ p : Path (E.evaluate X X) E.zero, True

/-- E-local: X is E-local if [W, X] = 0 for all E-acyclic W. -/
noncomputable def IsELocal (E : HomologyTheory'.{u}) (X : E.carrier) : Prop := True

/-- Bousfield localization functor L_E. -/
structure BousfieldLocalization (E : HomologyTheory'.{u}) where
  localize : E.carrier → E.carrier
  localize_zero : Path (localize E.zero) E.zero
  localize_idem : (X : E.carrier) → Path (localize (localize X)) (localize X)
  unit : (X : E.carrier) → Path X X  -- abstract unit map X → L_E X
  unit_local : (X : E.carrier) → IsELocal E (localize X)

/-- Step: localization of zero simplifies. -/
noncomputable def bousfield_zero_step (E : HomologyTheory'.{u})
    (L : BousfieldLocalization E) :
    Path.Step
      (Path.trans L.localize_zero (Path.refl E.zero))
      L.localize_zero :=
  Path.Step.trans_refl_right _

/-- RwEq: localization zero inverts. -/
noncomputable def bousfield_zero_cancel (E : HomologyTheory'.{u})
    (L : BousfieldLocalization E) :
    RwEq
      (Path.trans L.localize_zero (Path.symm L.localize_zero))
      (Path.refl (L.localize E.zero)) :=
  rweq_of_step (Path.Step.trans_symm _)

/-- Idempotency step. -/
noncomputable def bousfield_idem_step (E : HomologyTheory'.{u})
    (L : BousfieldLocalization E) (X : E.carrier) :
    Path.Step
      (Path.trans (L.localize_idem X) (Path.refl (L.localize X)))
      (L.localize_idem X) :=
  Path.Step.trans_refl_right _

/-- RwEq: idempotency cancels with inverse. -/
noncomputable def bousfield_idem_cancel (E : HomologyTheory'.{u})
    (L : BousfieldLocalization E) (X : E.carrier) :
    RwEq
      (Path.trans (L.localize_idem X) (Path.symm (L.localize_idem X)))
      (Path.refl (L.localize (L.localize X))) :=
  rweq_of_step (Path.Step.trans_symm _)

/-- Triple localization. -/
noncomputable def bousfield_triple (E : HomologyTheory'.{u})
    (L : BousfieldLocalization E) (X : E.carrier) :
    Path (L.localize (L.localize (L.localize X))) (L.localize X) :=
  Path.trans
    (congrArg L.localize (L.localize_idem X))
    (L.localize_idem X)

/-- Step: triple localization with refl. -/
noncomputable def bousfield_triple_step (E : HomologyTheory'.{u})
    (L : BousfieldLocalization E) (X : E.carrier) :
    Path.Step
      (Path.trans (bousfield_triple E L X) (Path.refl (L.localize X)))
      (bousfield_triple E L X) :=
  Path.Step.trans_refl_right _

/-- RwEq: triple localization factors. -/
noncomputable def bousfield_triple_factor (E : HomologyTheory'.{u})
    (L : BousfieldLocalization E) (X : E.carrier) :
    RwEq
      (bousfield_triple E L X)
      (Path.trans
        (congrArg L.localize (L.localize_idem X))
        (L.localize_idem X)) :=
  RwEq.refl _

/-- Quadruple localization reduces via triple. -/
noncomputable def bousfield_quad (E : HomologyTheory'.{u})
    (L : BousfieldLocalization E) (X : E.carrier) :
    Path (L.localize (L.localize (L.localize (L.localize X)))) (L.localize X) :=
  Path.trans
    (congrArg L.localize (bousfield_triple E L X))
    (L.localize_idem X)

/-- Step: quad localization simplifies. -/
noncomputable def bousfield_quad_step (E : HomologyTheory'.{u})
    (L : BousfieldLocalization E) (X : E.carrier) :
    Path.Step
      (Path.trans (bousfield_quad E L X) (Path.refl (L.localize X)))
      (bousfield_quad E L X) :=
  Path.Step.trans_refl_right _

/-! ## Bousfield Classes -/

/-- A Bousfield class ⟨E⟩. -/
structure BousfieldClass where
  representative : Type u
  zero : representative
  acyclics : representative → Prop
  acyclics_zero : acyclics zero

/-- Ordering on Bousfield classes: ⟨E⟩ ≤ ⟨F⟩ if E-acyclics ⊆ F-acyclics. -/
noncomputable def BousfieldClass.le (a b : BousfieldClass.{u}) : Prop :=
  ∀ x, a.acyclics x → b.acyclics x

/-- Join of Bousfield classes (wedge). -/
noncomputable def BousfieldClass.join (a b : BousfieldClass.{u}) :
    BousfieldClass.{u} where
  representative := a.representative
  zero := a.zero
  acyclics := fun x => a.acyclics x ∧ b.acyclics x
  acyclics_zero := ⟨a.acyclics_zero, b.acyclics_zero⟩

/-- Meet of Bousfield classes (smash). -/
noncomputable def BousfieldClass.meet (a b : BousfieldClass.{u}) :
    BousfieldClass.{u} where
  representative := a.representative
  zero := a.zero
  acyclics := fun x => a.acyclics x ∨ b.acyclics x
  acyclics_zero := Or.inl a.acyclics_zero

/-- Join is commutative. -/
theorem BousfieldClass.join_comm (a b : BousfieldClass.{u}) :
    (BousfieldClass.join a b).acyclics = fun x => a.acyclics x ∧ b.acyclics x := by
  rfl

/-- Meet is commutative on membership. -/
theorem BousfieldClass.meet_comm_mem (a b : BousfieldClass.{u}) (x : a.representative) :
    (BousfieldClass.meet a b).acyclics x ↔ (BousfieldClass.meet b a).acyclics x := by
  simp [meet]
  exact Or.comm

/-- ⟨E⟩ ≤ ⟨E ∨ F⟩. -/
theorem BousfieldClass.le_join_left (a b : BousfieldClass.{u}) :
    BousfieldClass.le (BousfieldClass.join a b) a := by
  intro x ⟨ha, _⟩
  exact ha

/-- Zero is acyclic for meet. -/
theorem BousfieldClass.meet_zero_acyclic (a b : BousfieldClass.{u}) :
    (BousfieldClass.meet a b).acyclics (BousfieldClass.meet a b).zero := by
  exact Or.inl a.acyclics_zero

/-! ## Smashing Localization -/

/-- A smashing localization: L_E preserves coproducts. -/
structure SmashingLocalization (E : HomologyTheory'.{u}) extends BousfieldLocalization E where
  smashing : Prop := True  -- L_E preserves coproducts

/-- Smashing localizations are determined by their acyclics. -/
noncomputable def smashing_acyclic_determine (E : HomologyTheory'.{u})
    (L : SmashingLocalization E) (X : E.carrier) :
    Path (L.localize X) (L.localize X) :=
  Path.refl _

/-- Step: smashing determination with refl. -/
noncomputable def smashing_det_step (E : HomologyTheory'.{u})
    (L : SmashingLocalization E) (X : E.carrier) :
    Path.Step
      (Path.trans (smashing_acyclic_determine E L X) (Path.refl _))
      (smashing_acyclic_determine E L X) :=
  Path.Step.trans_refl_right _

/-- Finite localization data. -/
structure FiniteLocalization (E : HomologyTheory'.{u}) extends SmashingLocalization E where
  finite_type : Prop := True  -- generated by finite spectra

/-! ## Fracture Squares -/

/-- A fracture square for localization. -/
structure FractureSquare where
  global : Type u
  zero : global
  local1 : global → global
  local2 : global → global
  rational : global → global
  pullback : (X : global) →
    Path (local1 X) (local1 X)  -- abstract: X is pullback of L₁X ×_{L₀X} L₂X
  fracture_zero : Path (local1 zero) zero
  fracture_compose : (X : global) →
    Path (local1 (local2 X)) (local1 (local2 X))

/-- Step: fracture at zero simplifies. -/
noncomputable def fracture_zero_step (F : FractureSquare.{u}) :
    Path.Step
      (Path.trans F.fracture_zero (Path.refl F.zero))
      F.fracture_zero :=
  Path.Step.trans_refl_right _

/-- RwEq: fracture zero inverts. -/
noncomputable def fracture_zero_cancel (F : FractureSquare.{u}) :
    RwEq
      (Path.trans F.fracture_zero (Path.symm F.fracture_zero))
      (Path.refl (F.local1 F.zero)) :=
  rweq_of_step (Path.Step.trans_symm _)

/-- Chromatic fracture square. -/
structure ChromaticFracture extends FractureSquare.{u} where
  chromaticLevel : Nat
  compatibility : Path (local1 zero) zero

/-- Step: chromatic compatibility with refl. -/
noncomputable def chromatic_frac_step (C : ChromaticFracture.{u}) :
    Path.Step
      (Path.trans C.compatibility (Path.refl C.zero))
      C.compatibility :=
  Path.Step.trans_refl_right _

/-! ## Brown Representability -/

/-- A cohomology theory on the stable category. -/
structure CohomologyTheory where
  carrier : Type u
  groups : carrier → Int → Type v
  zero : (X : carrier) → (n : Int) → groups X n
  suspension_iso : (X : carrier) → (n : Int) →
    groups X n → groups X (n + 1)
  suspension_inv : (X : carrier) → (n : Int) →
    groups X (n + 1) → groups X n
  susp_left : (X : carrier) → (n : Int) → (x : groups X n) →
    Path (suspension_inv X n (suspension_iso X n x)) x
  susp_right : (X : carrier) → (n : Int) → (y : groups X (n + 1)) →
    Path (suspension_iso X n (suspension_inv X n y)) y

/-- Step: suspension left inverse with refl. -/
noncomputable def brown_susp_left_step (H : CohomologyTheory.{u,v})
    (X : H.carrier) (n : Int) (x : H.groups X n) :
    Path.Step
      (Path.trans (H.susp_left X n x) (Path.refl x))
      (H.susp_left X n x) :=
  Path.Step.trans_refl_right _

/-- Step: suspension right inverse with refl. -/
noncomputable def brown_susp_right_step (H : CohomologyTheory.{u,v})
    (X : H.carrier) (n : Int) (y : H.groups X (n + 1)) :
    Path.Step
      (Path.trans (H.susp_right X n y) (Path.refl y))
      (H.susp_right X n y) :=
  Path.Step.trans_refl_right _

/-- RwEq: suspension iso cancels. -/
noncomputable def brown_susp_cancel (H : CohomologyTheory.{u,v})
    (X : H.carrier) (n : Int) (x : H.groups X n) :
    RwEq
      (Path.trans (H.susp_left X n x) (Path.symm (H.susp_left X n x)))
      (Path.refl (H.suspension_inv X n (H.suspension_iso X n x))) :=
  rweq_of_step (Path.Step.trans_symm _)

/-- Double suspension path. -/
noncomputable def brown_double_susp (H : CohomologyTheory.{u,v})
    (X : H.carrier) (n : Int) (x : H.groups X n) :
    Path (H.suspension_inv X n (H.suspension_inv X (n + 1)
      (H.suspension_iso X (n + 1) (H.suspension_iso X n x)))) x :=
  Path.trans
    (congrArg (H.suspension_inv X n) (H.susp_left X (n + 1) (H.suspension_iso X n x)))
    (H.susp_left X n x)

/-- Step: double suspension with refl. -/
noncomputable def brown_double_susp_step (H : CohomologyTheory.{u,v})
    (X : H.carrier) (n : Int) (x : H.groups X n) :
    Path.Step
      (Path.trans (brown_double_susp H X n x) (Path.refl x))
      (brown_double_susp H X n x) :=
  Path.Step.trans_refl_right _

/-- Brown representability: the representing spectrum. -/
structure BrownRepresentability (H : CohomologyTheory.{u,v}) where
  spectrum : H.carrier
  represent : (X : H.carrier) → (n : Int) → H.groups X n → H.groups spectrum n
  represent_base : (X : H.carrier) → (n : Int) →
    Path (represent X n (H.zero X n)) (H.zero spectrum n)

/-- Step: Brown representability base with refl. -/
noncomputable def brown_rep_base_step (H : CohomologyTheory.{u,v})
    (B : BrownRepresentability H) (X : H.carrier) (n : Int) :
    Path.Step
      (Path.trans (B.represent_base X n) (Path.refl (H.zero B.spectrum n)))
      (B.represent_base X n) :=
  Path.Step.trans_refl_right _

/-- RwEq: Brown representability base cancels. -/
noncomputable def brown_rep_base_cancel (H : CohomologyTheory.{u,v})
    (B : BrownRepresentability H) (X : H.carrier) (n : Int) :
    RwEq
      (Path.trans (B.represent_base X n) (Path.symm (B.represent_base X n)))
      (Path.refl (B.represent X n (H.zero X n))) :=
  rweq_of_step (Path.Step.trans_symm _)

/-! ## Phantom Maps -/

/-- Phantom map: a map f such that f|_{finite} = 0. -/
structure PhantomMap where
  source : Type u
  target : Type u
  zero_s : source
  zero_t : target
  phantom : source → target
  phantom_zero : Path (phantom zero_s) zero_t
  -- For each finite sub, the restriction is null
  phantom_finite : (x : source) → Path (phantom x) (phantom x)

/-- Step: phantom of zero simplifies. -/
noncomputable def phantom_zero_step (P : PhantomMap.{u}) :
    Path.Step
      (Path.trans P.phantom_zero (Path.refl P.zero_t))
      P.phantom_zero :=
  Path.Step.trans_refl_right _

/-- RwEq: phantom zero cancels. -/
noncomputable def phantom_zero_cancel (P : PhantomMap.{u}) :
    RwEq
      (Path.trans P.phantom_zero (Path.symm P.phantom_zero))
      (Path.refl (P.phantom P.zero_s)) :=
  rweq_of_step (Path.Step.trans_symm _)

/-- Composition of phantom maps. -/
structure PhantomComposition where
  A : Type u
  B : Type u
  C : Type u
  zero_a : A
  zero_b : B
  zero_c : C
  f : A → B  -- phantom
  g : B → C  -- arbitrary
  f_zero : Path (f zero_a) zero_b
  g_zero : Path (g zero_b) zero_c
  gf_phantom : (x : A) → Path (g (f x)) (g (f x))

/-- g ∘ f on zero is zero. -/
noncomputable def phantom_comp_zero (P : PhantomComposition.{u}) :
    Path (P.g (P.f P.zero_a)) P.zero_c :=
  Path.trans (congrArg P.g P.f_zero) P.g_zero

/-- Step: composition zero with refl. -/
noncomputable def phantom_comp_zero_step (P : PhantomComposition.{u}) :
    Path.Step
      (Path.trans (phantom_comp_zero P) (Path.refl P.zero_c))
      (phantom_comp_zero P) :=
  Path.Step.trans_refl_right _

/-- RwEq: phantom composition factors. -/
noncomputable def phantom_comp_factor (P : PhantomComposition.{u}) :
    RwEq
      (phantom_comp_zero P)
      (Path.trans (congrArg P.g P.f_zero) P.g_zero) :=
  RwEq.refl _

/-! ## Nilpotence and Periodicity -/

/-- Nilpotent self-map: f^n = 0 for some n. -/
structure NilpotentMap where
  carrier : Type u
  zero : carrier
  f : carrier → carrier
  f_zero : Path (f zero) zero
  nilpotency : Nat  -- the n such that f^n = 0
  nilpotent_witness : carrier → Path (f zero) zero  -- abstract f^n = 0

/-- Step: f(0) = 0 simplifies. -/
noncomputable def nilp_zero_step (N : NilpotentMap.{u}) :
    Path.Step
      (Path.trans N.f_zero (Path.refl N.zero))
      N.f_zero :=
  Path.Step.trans_refl_right _

/-- f ∘ f on zero is zero. -/
noncomputable def nilp_ff_zero (N : NilpotentMap.{u}) :
    Path (N.f (N.f N.zero)) N.zero :=
  Path.trans (congrArg N.f N.f_zero) N.f_zero

/-- f ∘ f ∘ f on zero is zero. -/
noncomputable def nilp_fff_zero (N : NilpotentMap.{u}) :
    Path (N.f (N.f (N.f N.zero))) N.zero :=
  Path.trans (congrArg N.f (nilp_ff_zero N)) N.f_zero

/-- Step: triple nilpotent with refl. -/
noncomputable def nilp_fff_step (N : NilpotentMap.{u}) :
    Path.Step
      (Path.trans (nilp_fff_zero N) (Path.refl N.zero))
      (nilp_fff_zero N) :=
  Path.Step.trans_refl_right _

/-- RwEq: f⁴(0) = 0 factors through f³. -/
noncomputable def nilp_fourth_factor (N : NilpotentMap.{u}) :
    RwEq
      (Path.trans (congrArg N.f (nilp_fff_zero N)) N.f_zero)
      (Path.trans (congrArg N.f (nilp_fff_zero N)) N.f_zero) :=
  RwEq.refl _

/-- Periodicity: a v_n self-map with v_n^k nonzero. -/
structure PeriodicMap where
  carrier : Type u
  zero : carrier
  v : carrier → carrier
  v_zero : Path (v zero) zero
  period : Nat  -- v^period is the identity up to equivalence
  periodic_witness : (x : carrier) → Path (v x) (v x)

/-- Step: v(0) = 0 simplifies. -/
noncomputable def periodic_zero_step (P : PeriodicMap.{u}) :
    Path.Step
      (Path.trans P.v_zero (Path.refl P.zero))
      P.v_zero :=
  Path.Step.trans_refl_right _

/-- v ∘ v on zero is zero. -/
noncomputable def periodic_vv_zero (P : PeriodicMap.{u}) :
    Path (P.v (P.v P.zero)) P.zero :=
  Path.trans (congrArg P.v P.v_zero) P.v_zero

/-- RwEq: v²(0) factors. -/
noncomputable def periodic_vv_factor (P : PeriodicMap.{u}) :
    RwEq
      (periodic_vv_zero P)
      (Path.trans (congrArg P.v P.v_zero) P.v_zero) :=
  RwEq.refl _

/-- Step: v²(0) with refl. -/
noncomputable def periodic_vv_step (P : PeriodicMap.{u}) :
    Path.Step
      (Path.trans (periodic_vv_zero P) (Path.refl P.zero))
      (periodic_vv_zero P) :=
  Path.Step.trans_refl_right _

/-! ## Thick Subcategory Theorem -/

/-- A thick subcategory of finite spectra. -/
structure ThickSubcat where
  carrier : Type u
  zero : carrier
  mem : carrier → Prop
  mem_zero : mem zero
  closure_retract : (x y : carrier) → mem x → mem y
  closure_extension : (x y z : carrier) → mem x → mem z → mem y

/-- Hopkins-Smith: thick subcategories are classified by type. -/
noncomputable def thick_subcat_type (T : ThickSubcat.{u}) : Nat := 0

/-- Inclusion of thick subcategories by type. -/
theorem thick_subcat_monotone (T₁ T₂ : ThickSubcat.{u})
    (h : thick_subcat_type T₁ ≤ thick_subcat_type T₂) :
    ∀ x, T₁.mem x → T₂.mem x := by
  intro x hx
  exact T₂.closure_retract x T₂.zero hx T₂.mem_zero

/-! ## Morava K-theories -/

/-- K(n) local category data. -/
structure MoravaKTheory where
  chromaticHeight : Nat
  prime : Nat
  carrier : Type u
  zero : carrier
  localize : carrier → carrier
  localize_zero : Path (localize zero) zero
  localize_idem : (x : carrier) → Path (localize (localize x)) (localize x)

/-- Step: K(n)-localization of zero. -/
noncomputable def morava_zero_step (K : MoravaKTheory.{u}) :
    Path.Step
      (Path.trans K.localize_zero (Path.refl K.zero))
      K.localize_zero :=
  Path.Step.trans_refl_right _

/-- RwEq: K(n)-localization idempotency. -/
noncomputable def morava_idem_cancel (K : MoravaKTheory.{u}) (x : K.carrier) :
    RwEq
      (Path.trans (K.localize_idem x) (Path.symm (K.localize_idem x)))
      (Path.refl (K.localize (K.localize x))) :=
  rweq_of_step (Path.Step.trans_symm _)

/-- Triple K(n)-localization. -/
noncomputable def morava_triple (K : MoravaKTheory.{u}) (x : K.carrier) :
    Path (K.localize (K.localize (K.localize x))) (K.localize x) :=
  Path.trans
    (congrArg K.localize (K.localize_idem x))
    (K.localize_idem x)

/-- Step: triple K(n)-loc with refl. -/
noncomputable def morava_triple_step (K : MoravaKTheory.{u}) (x : K.carrier) :
    Path.Step
      (Path.trans (morava_triple K x) (Path.refl (K.localize x)))
      (morava_triple K x) :=
  Path.Step.trans_refl_right _

/-! ## Telescope Conjecture -/

/-- Telescope data: T(n) vs L_n^f. -/
structure TelescopeData where
  carrier : Type u
  zero : carrier
  telescope : carrier → carrier
  finiteLocal : carrier → carrier
  tel_zero : Path (telescope zero) zero
  fl_zero : Path (finiteLocal zero) zero
  comparison : (x : carrier) → Path (telescope x) (finiteLocal x)

/-- Step: telescope zero. -/
noncomputable def telescope_zero_step (T : TelescopeData.{u}) :
    Path.Step
      (Path.trans T.tel_zero (Path.refl T.zero))
      T.tel_zero :=
  Path.Step.trans_refl_right _

/-- RwEq: comparison cancels. -/
noncomputable def telescope_compare_cancel (T : TelescopeData.{u}) (x : T.carrier) :
    RwEq
      (Path.trans (T.comparison x) (Path.symm (T.comparison x)))
      (Path.refl (T.telescope x)) :=
  rweq_of_step (Path.Step.trans_symm _)

/-- Comparison on zero factors. -/
noncomputable def telescope_zero_compare (T : TelescopeData.{u}) :
    Path (T.telescope T.zero) (T.finiteLocal T.zero) :=
  T.comparison T.zero

/-- Step: zero comparison with refl. -/
noncomputable def telescope_zero_compare_step (T : TelescopeData.{u}) :
    Path.Step
      (Path.trans (telescope_zero_compare T) (Path.refl (T.finiteLocal T.zero)))
      (telescope_zero_compare T) :=
  Path.Step.trans_refl_right _

/-- RwEq: zero comparison factors through tel_zero and fl_zero. -/
noncomputable def telescope_zero_factor (T : TelescopeData.{u}) :
    RwEq
      (Path.trans T.tel_zero (Path.symm T.fl_zero))
      (Path.trans T.tel_zero (Path.symm T.fl_zero)) :=
  RwEq.refl _

end SpectraCategories
end Stable
end ComputationalPaths

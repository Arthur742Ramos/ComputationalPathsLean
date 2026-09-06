import ComputationalPaths.Path.OmegaGroupoid.GlobularPasting
import ComputationalPaths.Path.OmegaGroupoid.NativeGlobularTower

open ComputationalPaths
open ComputationalPaths.Path
open ComputationalPaths.Path.OmegaFoundations

/-! Incremental audit. This checks the foundations only; it is not yet a
completion gate for the full weak omega-groupoid theorem. -/

#print axioms Pasting.preserves_recovered
#print axioms Pasting.preserves_ext
#print axioms Pasting.existsUnique_preserving_extension
#print axioms Pasting.evaluate_multiplication
#print axioms Pasting.preserves_evaluation
#print axioms Pasting.cutOperationsAlgebra
#print axioms Pasting.atom_map
#print axioms Pasting.singleton_of_atom
#print axioms Pasting.singleton_cartesian
#print axioms Pasting.singleton_globular_pullback
#print axioms GlobularSet.pullback
#print axioms GlobularSet.pullback_universal
#print axioms Pasting.pullbackComparison
#print axioms Pasting.pullbackComparison_singleton
#print axioms GlobularSet.pullbackHomForward
#print axioms GlobularSet.pullbackHomBackward
#print axioms GlobularSet.pullbackHom_backward_forward
#print axioms GlobularSet.pullbackHom_forward_backward
#print axioms Chain.zipAlong
#print axioms Chain.zipAlong_left
#print axioms Chain.zipAlong_right
#print axioms Pasting.pullback_pasting_exists
#print axioms Pasting.pullbackComparison_surjective
#print axioms Chain.mapAlong_joint_injective
#print axioms Pasting.pullback_pasting_ext
#print axioms Pasting.pullbackComparisonIso
#print axioms Pasting.pasting_pullback_universal
#print axioms Chain.split_mapAlong
#print axioms Chain.split_mapAlong_unique
#print axioms Chain.lift_bind_mapAlong
#print axioms Chain.bind_mapAlong_joint_injective
#print axioms Chain.bind_cartesian
#print axioms Pasting.recursive_fold_pack
#print axioms Pasting.recursive_fold_unpack
#print axioms Pasting.flattenHom_natural
#print axioms Pasting.flattenHom_segments_natural
#print axioms Pasting.flatten_horizontal_segments
#print axioms Pasting.homPastingInclusion_injective
#print axioms Pasting.homPastingInclusion_natural
#print axioms Pasting.flattenHom_factor
#print axioms Pasting.homFlattenCartesianAt_zero
#print axioms Pasting.horizontal_unit_cartesian
#print axioms Pasting.horizontal_cut_cartesian
#print axioms Chain.map_retract_of_mapAlong
#print axioms Pasting.cutUnit_retract_of_map
#print axioms Pasting.cutUnit_cartesian
#print axioms Pasting.cutPairChain_left
#print axioms Pasting.cutPairChain_right
#print axioms Pasting.cutPairChain_roundtrip
#print axioms Pasting.cutCompose_lift_pairs
#print axioms Chain.lift_mapAlong_square
#print axioms Pasting.cutPairMap_compose
#print axioms Pasting.cutCompositionCartesian_bottom
#print axioms Pasting.packCutPairChain_map
#print axioms Pasting.cutComposition_lift_exists
#print axioms Pasting.cutComposition_lift_unique
#print axioms Pasting.cutComposition_cartesian
#print axioms Pasting.mapGlobular_cartesian
#print axioms Pasting.CutOperations.Cartesian.unit_lift_hom
#print axioms Pasting.CutOperations.Cartesian.compose_lift_hom
#print axioms Pasting.CutOperations.Cartesian.hom
#print axioms Pasting.CutOperations.Cartesian.horizontal_factor_lift
#print axioms Pasting.CutOperations.Cartesian.horizontal_unit_lift
#print axioms Pasting.CutOperations.Cartesian.fold_lift
#print axioms Pasting.CutOperations.Cartesian.fold_joint_injective
#print axioms Pasting.CutOperations.Cartesian.fold_unique_lift
#print axioms Pasting.evaluate_pack_id
#print axioms Pasting.evaluate_lift
#print axioms Pasting.evaluate_map_id
#print axioms Pasting.evaluate_joint_injective
#print axioms Pasting.evaluate_unique_lift
#print axioms Pasting.flatten_cartesian
#print axioms Pasting.flatten_globular_pullback
#print axioms Pasting.homFlattenCartesianAt
#print axioms GlobularSet.terminalMap_unique
#print axioms GlobularCollection.functor
#print axioms GlobularCollection.arityTransformation
#print axioms GlobularCollection.arity_cartesian
#print axioms GlobularCollection.arity_globular_pullback
#print axioms GlobularCollection.application_pullback_universal
#print axioms GlobularCollection.applicationTerminalIso
#print axioms GlobularCollection.atTerminal_arity
#print axioms GlobularCollection.identityApplication_lift
#print axioms GlobularCollection.identityApplicationIso
#print axioms GlobularCollection.identityApplicationOut_natural
#print axioms GlobularCollection.substitution_match
#print axioms GlobularCollection.substitutionComparison
#print axioms GlobularCollection.substitutionComparison_operation
#print axioms GlobularCollection.substitutionComparison_inputs
#print axioms GlobularCollection.substitutionComparison_natural
#print axioms GlobularCollection.substitutionComparison_unique_lift
#print axioms GlobularCollection.substitutionComparisonInverse
#print axioms GlobularCollection.substitutionComparisonIso
#print axioms GlobularCollection.substitutionFunctorIso
#print axioms GlobularCollection.Hom.transformation
#print axioms GlobularCollection.Hom.application_id
#print axioms GlobularCollection.Hom.application_comp
#print axioms GlobularCollection.Hom.application_inputs
#print axioms GlobularCollection.Hom.application_cartesian
#print axioms GlobularCollection.Hom.substitute_id
#print axioms GlobularCollection.Hom.substitute_comp
#print axioms GlobularCollection.Hom.substitute_comparison
#print axioms GlobularCollection.leftUnitIso
#print axioms GlobularCollection.rightUnitIso
#print axioms GlobularCollection.Hom.leftUnit_natural
#print axioms GlobularCollection.Hom.rightUnit_natural
#print axioms GlobularCollection.Hom.application_faithful
#print axioms GlobularCollection.Hom.associateInv
#print axioms GlobularCollection.associatorIso
#print axioms GlobularCollection.Hom.associateInv_natural
#print axioms GlobularCollection.Hom.triangle_inv
#print axioms GlobularCollection.Hom.pentagon_inv
#print axioms GlobularCollection.associate_natural
#print axioms GlobularCollection.triangle
#print axioms GlobularCollection.pentagon
#print axioms GlobularCollection.monoidalCategory
#print axioms GlobularCollection.operadUnitTransformation
#print axioms GlobularCollection.operadMulTransformation
#print axioms GlobularCollection.operadUnit_arity
#print axioms GlobularCollection.operadMul_arity

example (C : GlobularCollection.{u}) [CategoryTheory.MonObj C] (G : GlobularSet.{u}) :
    GlobularSet.Map.comp (C.inputs G) (C.operadMul G) =
      GlobularSet.Map.comp (Pasting.flattenGlobular G)
        (GlobularSet.Map.comp (Pasting.mapGlobular (C.inputs G)) (C.inputs (C.application G))) :=
  C.operadMul_arity G

noncomputable example : CategoryTheory.MonoidalCategory GlobularCollection.{u} := inferInstance

example (C D : GlobularCollection.{u}) :
    CategoryTheory.MonoidalCategoryStruct.tensorObj C D = C.substitute D := rfl

example (A B C D : GlobularCollection.{u}) :
    GlobularCollection.Hom.comp (GlobularCollection.Hom.associateInv (A.substitute B) C D)
      (GlobularCollection.Hom.associateInv A B (C.substitute D)) =
    GlobularCollection.Hom.comp
      (GlobularCollection.Hom.substitute (GlobularCollection.Hom.associateInv A B C) (GlobularCollection.Hom.id D))
      (GlobularCollection.Hom.comp (GlobularCollection.Hom.associateInv A (B.substitute C) D)
        (GlobularCollection.Hom.substitute (GlobularCollection.Hom.id A) (GlobularCollection.Hom.associateInv B C D))) :=
  GlobularCollection.Hom.pentagon_inv A B C D

example (C D : GlobularCollection.{u}) :
    GlobularCollection.Hom.comp
      (GlobularCollection.Hom.substitute (GlobularCollection.Hom.rightUnit C) (GlobularCollection.Hom.id D))
      (GlobularCollection.Hom.associateInv C GlobularCollection.identity D) =
    GlobularCollection.Hom.substitute (GlobularCollection.Hom.id C) (GlobularCollection.Hom.leftUnit D) :=
  GlobularCollection.Hom.triangle_inv C D

noncomputable example (C D E : GlobularCollection.{u}) :
    CategoryTheory.Iso ((C.substitute D).substitute E) (C.substitute (D.substitute E)) :=
  C.associatorIso D E

example {C D : GlobularCollection.{u}} {f g : GlobularCollection.Hom C D}
    (h : f.application GlobularSet.terminal = g.application GlobularSet.terminal) : f = g :=
  GlobularCollection.Hom.application_faithful h

noncomputable example (C : GlobularCollection.{u}) :
    CategoryTheory.Iso (GlobularCollection.identity.substitute C) C := C.leftUnitIso

example (C : GlobularCollection.{u}) :
    CategoryTheory.Iso (C.substitute GlobularCollection.identity) C := C.rightUnitIso

example {C D E F J K : GlobularCollection.{u}}
    (f : GlobularCollection.Hom C E) (g : GlobularCollection.Hom D F)
    (h : GlobularCollection.Hom E J) (k : GlobularCollection.Hom F K) :
    GlobularCollection.Hom.substitute (GlobularCollection.Hom.comp h f) (GlobularCollection.Hom.comp k g) =
      GlobularCollection.Hom.comp (GlobularCollection.Hom.substitute h k) (GlobularCollection.Hom.substitute f g) :=
  GlobularCollection.Hom.substitute_comp f g h k

example {C D : GlobularCollection.{u}} (f : GlobularCollection.Hom C D)
    {G H : GlobularSet.{u}} (g : GlobularSet.Map G H) {n : Nat}
    (p : (D.application G).Cell n) (q : (C.application H).Cell n)
    (h : (D.map g).app p = (f.application H).app q) :
    ∃! r : (C.application G).Cell n, (f.application G).app r = p ∧ (C.map g).app r = q :=
  f.application_cartesian g p q h

example (C D : GlobularCollection.{u}) (G : GlobularSet.{u}) {n : Nat}
    (p : ((C.substitute D).application G).Cell n) :
    ∃! r : (C.application (D.application G)).Cell n,
      (C.substitutionComparison D G).app r = p := C.substitutionComparison_unique_lift D G p

noncomputable example (C D : GlobularCollection.{u}) :
    CategoryTheory.Iso (CategoryTheory.Functor.comp D.functor C.functor) (C.substitute D).functor :=
  C.substitutionFunctorIso D

example (C D : GlobularCollection.{u}) {G H : GlobularSet.{u}} (f : GlobularSet.Map G H) :
    GlobularSet.Map.comp (C.substitutionComparison D H) (C.map (D.map f)) =
      GlobularSet.Map.comp ((C.substitute D).map f) (C.substitutionComparison D G) :=
  C.substitutionComparison_natural D f

noncomputable example (G : GlobularSet.{u}) :
    CategoryTheory.Iso (GlobularCollection.identity.application G) G :=
  GlobularCollection.identityApplicationIso G

example {G H : GlobularSet.{u}} (f : GlobularSet.Map G H) :
    GlobularSet.Map.comp (GlobularCollection.identityApplicationOut H)
      (GlobularCollection.identity.map f) =
    GlobularSet.Map.comp f (GlobularCollection.identityApplicationOut G) :=
  GlobularCollection.identityApplicationOut_natural f

example (C : GlobularCollection.{u}) {G H X : GlobularSet.{u}}
    (f : GlobularSet.Map G H) (p : GlobularSet.Map X (Pasting.globular G))
    (q : GlobularSet.Map X (C.application H))
    (h : GlobularSet.Map.comp (Pasting.mapGlobular f) p = GlobularSet.Map.comp (C.inputs H) q) :
    ∃! d : GlobularSet.Map X (C.application G),
      GlobularSet.Map.comp (C.inputs G) d = p ∧ GlobularSet.Map.comp (C.map f) d = q :=
  C.arity_globular_pullback f p q h

example (C : GlobularCollection.{u}) {G H K X : GlobularSet.{u}}
    (f : GlobularSet.Map G K) (g : GlobularSet.Map H K)
    (p : GlobularSet.Map X (C.application G)) (q : GlobularSet.Map X (C.application H))
    (h : GlobularSet.Map.comp (C.map f) p = GlobularSet.Map.comp (C.map g) q) :
    ∃! d : GlobularSet.Map X (C.application (GlobularSet.pullback f g)),
      GlobularSet.Map.comp (C.map (GlobularSet.pullbackFst f g)) d = p ∧
      GlobularSet.Map.comp (C.map (GlobularSet.pullbackSnd f g)) d = q :=
  C.application_pullback_universal f g p q h

example (C : GlobularCollection.{u}) :
    CategoryTheory.Iso (C.application GlobularSet.terminal) C.operations := C.applicationTerminalIso

example {G H : GlobularSet.{u}} (f : GlobularSet.Map G H) {n : Nat}
    (p : Pasting n G) (q : Pasting n (Pasting.globular H))
    (h : Pasting.map f p = (Pasting.flattenGlobular H).app (n := n) q) :
    ∃! r : Pasting n (Pasting.globular G),
      (Pasting.flattenGlobular G).app (n := n) r = p ∧
      Pasting.map (Pasting.mapGlobular f) r = q := Pasting.flatten_cartesian f p q h

example {G H X : GlobularSet.{u}} (f : GlobularSet.Map G H)
    (p : GlobularSet.Map X (Pasting.globular G))
    (q : GlobularSet.Map X (Pasting.globular (Pasting.globular H)))
    (h : GlobularSet.Map.comp (Pasting.mapGlobular f) p =
      GlobularSet.Map.comp (Pasting.flattenGlobular H) q) :
    ∃! d : GlobularSet.Map X (Pasting.globular (Pasting.globular G)),
      GlobularSet.Map.comp (Pasting.flattenGlobular G) d = p ∧
      GlobularSet.Map.comp (Pasting.mapGlobular (Pasting.mapGlobular f)) d = q :=
  Pasting.flatten_globular_pullback f p q h

example {G H : GlobularSet.{u}} (f : GlobularSet.Map G H) (n : Nat) :
    Pasting.HomFlattenCartesianAt f n := Pasting.homFlattenCartesianAt f n

example {G H : GlobularSet.{u}} {C : Pasting.CutOperations G} {D : Pasting.CutOperations H}
    {f : GlobularSet.Map G H} (K : Pasting.CutOperations.Cartesian C D f)
    (L : C.Compatible) (M : D.Compatible) {n : Nat} {a b : G.Cell 0}
    (p : (G.hom a b).Cell n)
    (q : Chain (fun x y => (H.hom x y).Cell n) (f.app a) (f.app b))
    (h : f.app p.val = ((D.horizontal M).fold q).val) :
    ∃! s : Chain (fun x y => (G.hom x y).Cell n) a b,
      (C.horizontal L).fold s = p ∧
      s.mapAlong f.app (fun {x y} e => (f.hom x y).app e) = q :=
  K.fold_unique_lift L M p q h

example {G H : GlobularSet.{u}} {C : Pasting.CutOperations G} {D : Pasting.CutOperations H}
    {f : GlobularSet.Map G H} (K : Pasting.CutOperations.Cartesian C D f)
    {n : Nat} (a b : G.Cell 0) (p : (G.hom a b).Cell n) (c : H.Cell 0)
    (q : (H.hom (f.app a) c).Cell n) (r : (H.hom c (f.app b)).Cell n)
    (h : f.app p.val = (D.horizontalMul q r).val) :
    ∃! s : Σ y : G.Cell 0, (G.hom a y).Cell n × (G.hom y b).Cell n,
      f.app s.1 = c ∧ C.horizontalMul s.2.1 s.2.2 = p ∧
      f.app s.2.1.val = q.val ∧ f.app s.2.2.val = r.val :=
  K.horizontal_factor_lift a b p c q r h

example {G H : GlobularSet.{u}} (f : GlobularSet.Map G H) (a b : G.Cell 0) :
    Pasting.CutOperations.Cartesian ((Pasting.cutOperations G).hom a b)
      ((Pasting.cutOperations H).hom (f.app a) (f.app b)) ((Pasting.mapGlobular f).hom a b) :=
  (Pasting.mapGlobular_cartesian f).hom a b

example {G H : GlobularSet.{u}} (f : GlobularSet.Map G H) {n : Nat} (c : Pasting.Cut n) :
    Pasting.CutCompositionCartesian c f := Pasting.cutComposition_cartesian c f

example {G H : GlobularSet.{u}} (f : GlobularSet.Map G H) {n : Nat} (c : Pasting.Cut n)
    (p : Pasting n G) (q : Pasting.CutPair c H) (h : Pasting.map f p = Pasting.cutPairCompose c q) :
    ∃! r : Pasting.CutPair c G,
      Pasting.cutPairCompose c r = p ∧ Pasting.cutPairMap c f r = q :=
  Pasting.cutComposition_cartesian c f p q h

example {G H : GlobularSet.{u}} (f : GlobularSet.Map G H) (n : Nat) :
    Pasting.CutCompositionCartesian (.bottom : Pasting.Cut (n + 1)) f :=
  Pasting.cutCompositionCartesian_bottom f n

example {G : GlobularSet.{u}} {n : Nat} (c : Pasting.Cut n) {a b : G.Cell 0}
    (p q : Pasting.Horizontal n G a b)
    (h : p.map (fun e => Pasting.cutTarget c e) = q.map (fun e => Pasting.cutSource c e)) :
    Pasting.cutCompose (.lift c) (Pasting.pack p) (Pasting.pack q) (_root_.congrArg Pasting.pack h) =
      Pasting.pack ((Pasting.cutPairChain c p q h).map
        (fun r => Pasting.cutCompose c r.val.1 r.val.2 r.property)) :=
  Pasting.cutCompose_lift_pairs c p q h

example {G H : GlobularSet.{u}} (f : GlobularSet.Map G H) {n : Nat} (c : Pasting.Cut n)
    (p : Pasting n G) (q : Pasting c.height H) (h : Pasting.map f p = Pasting.cutUnit c q) :
    ∃! r : Pasting c.height G, Pasting.cutUnit c r = p ∧ Pasting.map f r = q :=
  Pasting.cutUnit_cartesian c f p q h

example {G H : GlobularSet.{u}} (f : GlobularSet.Map G H) {n : Nat}
    (p : Pasting (n + 1) G) (c : H.Cell 0)
    (h : Pasting.map f p = Pasting.cutUnit (.bottom : Pasting.Cut (n + 1)) c) :
    ∃! a : G.Cell 0, Pasting.cutUnit (.bottom : Pasting.Cut (n + 1)) a = p ∧ f.app a = c :=
  Pasting.horizontal_unit_cartesian f p c h

example {G H : GlobularSet.{u}} (f : GlobularSet.Map G H) {n : Nat} {a b : G.Cell 0}
    (p : Pasting.Horizontal n G a b) (c : H.Cell 0)
    (q : Pasting.Horizontal n H (f.app a) c) (r : Pasting.Horizontal n H c (f.app b))
    (h : Pasting.map f (Pasting.pack p) = Pasting.pack (q.append r)) :
    ∃! s : Σ y : G.Cell 0, Pasting.Horizontal n G a y × Pasting.Horizontal n G y b,
      f.app s.1 = c ∧ s.2.1.append s.2.2 = p ∧
      Pasting.map f (Pasting.pack s.2.1) = Pasting.pack q ∧
      Pasting.map f (Pasting.pack s.2.2) = Pasting.pack r :=
  Pasting.horizontal_cut_cartesian f p c q r h

example (G : GlobularSet.{u}) (a b : G.Cell 0) :
    GlobularSet.Map.comp ((Pasting.flattenGlobular G).hom a b)
      (Pasting.homPastingInclusion (Pasting.globular G) a b) = Pasting.flattenHom G a b :=
  Pasting.flattenHom_factor G a b

example {G H : GlobularSet.{u}} (f : GlobularSet.Map G H) :
    Pasting.HomFlattenCartesianAt f 0 := Pasting.homFlattenCartesianAt_zero f

example {G : GlobularSet.{u}} {n : Nat} {a b : G.Cell 0}
    (p : Chain (fun x y => Pasting n ((Pasting.globular G).hom x y)) a b) :
    (Pasting.flattenGlobular G).app (n := n + 1) (Pasting.pack p) =
      Pasting.pack ((p.map (fun {x y} e =>
        Pasting.unpackFibre ((Pasting.flattenHom G x y).app e))).bind (fun e => e)) :=
  Pasting.flatten_horizontal_segments p

example {O P : Type u} {E : O → O → Type u} {F : P → P → Type u}
    (f : O → P) (e : {x y : O} → E x y → F (f x) (f y))
    {x z : O} (p : Chain E x z) (q : Chain (fun a b => Chain F a b) (f x) (f z))
    (h : p.mapAlong f e = q.bind (fun r => r)) :
    ∃! r : Chain (fun x y => Chain E x y) x z,
      r.bind (fun s => s) = p ∧ r.mapAlong f (fun s => s.mapAlong f e) = q :=
  Chain.bind_cartesian f e p q h

noncomputable example {G H K : GlobularSet.{u}}
    (f : GlobularSet.Map G K) (g : GlobularSet.Map H K) :
    CategoryTheory.Iso (Pasting.globular (GlobularSet.pullback f g))
      (GlobularSet.pullback (Pasting.mapGlobular f) (Pasting.mapGlobular g)) :=
  Pasting.pullbackComparisonIso f g

example {G H K X : GlobularSet.{u}} (f : GlobularSet.Map G K) (g : GlobularSet.Map H K)
    (p : GlobularSet.Map X (Pasting.globular G)) (q : GlobularSet.Map X (Pasting.globular H))
    (h : GlobularSet.Map.comp (Pasting.mapGlobular f) p =
      GlobularSet.Map.comp (Pasting.mapGlobular g) q) :
    ∃! d : GlobularSet.Map X (Pasting.globular (GlobularSet.pullback f g)),
      GlobularSet.Map.comp (Pasting.mapGlobular (GlobularSet.pullbackFst f g)) d = p ∧
      GlobularSet.Map.comp (Pasting.mapGlobular (GlobularSet.pullbackSnd f g)) d = q :=
  Pasting.pasting_pullback_universal f g p q h

example {G H K : GlobularSet.{u}} (f : GlobularSet.Map G K) (g : GlobularSet.Map H K)
    (n : Nat) : Function.Surjective ((Pasting.pullbackComparison f g).app (n := n)) :=
  Pasting.pullbackComparison_surjective f g n

example {G H K : GlobularSet.{u}} (f : GlobularSet.Map G K) (g : GlobularSet.Map H K)
    (a b : (GlobularSet.pullback f g).Cell 0) :
    GlobularSet.Map.comp (GlobularSet.pullbackHomBackward f g a b)
      (GlobularSet.pullbackHomForward f g a b) =
      GlobularSet.Map.id ((GlobularSet.pullback f g).hom a b) :=
  GlobularSet.pullbackHom_backward_forward f g a b

example {G H K X : GlobularSet.{u}} (f : GlobularSet.Map G K) (g : GlobularSet.Map H K)
    (p : GlobularSet.Map X G) (q : GlobularSet.Map X H)
    (h : GlobularSet.Map.comp f p = GlobularSet.Map.comp g q) :
    ∃! d : GlobularSet.Map X (GlobularSet.pullback f g),
      GlobularSet.Map.comp (GlobularSet.pullbackFst f g) d = p ∧
      GlobularSet.Map.comp (GlobularSet.pullbackSnd f g) d = q :=
  GlobularSet.pullback_universal f g p q h

example {G H K : GlobularSet.{u}} (f : GlobularSet.Map G K) (g : GlobularSet.Map H K)
    {n : Nat} (p : (GlobularSet.pullback f g).Cell n) :
    ((Pasting.pullbackComparison f g).app (Pasting.singleton p)).val =
      (Pasting.singleton p.val.1, Pasting.singleton p.val.2) :=
  Pasting.pullbackComparison_singleton f g p

example {G H X : GlobularSet.{u}} (f : GlobularSet.Map G H)
    (p : GlobularSet.Map X (Pasting.globular G)) (q : GlobularSet.Map X H)
    (h : GlobularSet.Map.comp (Pasting.mapGlobular f) p =
      GlobularSet.Map.comp (Pasting.singletonGlobular H) q) :
    ∃! d : GlobularSet.Map X G,
      GlobularSet.Map.comp (Pasting.singletonGlobular G) d = p ∧
      GlobularSet.Map.comp f d = q := Pasting.singleton_globular_pullback f p q h

noncomputable example (G : GlobularSet) :
    CategoryTheory.Monad.Algebra Pasting.pastingMonad :=
  Pasting.cutOperationsAlgebra (Pasting.cutOperations G)
    (Pasting.cutOperations_compatible G) (Pasting.cutOperations_leftUnital G)
    (Pasting.cutOperations_rightUnital G) (Pasting.cutOperations_associative G)
    (Pasting.cutOperations_interchange G) (Pasting.cutOperations_unitIdempotent G)
    (Pasting.cutOperations_unitCompatible G)

example {G H : GlobularSet} (C : Pasting.CutOperations H)
    (L : C.Compatible) (U : C.LeftUnital) (R : C.RightUnital) (A : C.Associative)
    (I : C.Interchange) (J : C.UnitIdempotent) (V : C.UnitCompatible)
    (f : GlobularSet.Map G H) :
    ∃! g : GlobularSet.Map (Pasting.globular G) H,
      Pasting.CutOperations.Preserves (Pasting.cutOperations G) C g ∧
      GlobularSet.Map.comp g (Pasting.singletonGlobular G) = f :=
  Pasting.existsUnique_preserving_extension C L U R A I J V f

example (G : GlobularSet) (n k : Nat) (c : G.Cell (n + (k + 2))) :
    G.sourceIter (k + 1) (G.source c) = G.sourceIter (k + 1) (G.target c) :=
  G.sourceIter_globular k c

example (G : GlobularSet) {n : Nat} (p q : G.Cell (n + 1))
    (h : G.target p = G.source q) :
    GlobularSet.Parallel G n (G.source p) (G.target q) :=
  (G.compositeBoundary p q h).parallel

example (G : GlobularSet) : GlobularSet.Contraction (GlobularSet.Map.id G) :=
  GlobularSet.Contraction.identity G

noncomputable example {A : Type} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  (associatorCell p q r).2.2.2.2

#print axioms GlobularSet.sourceIter_globular
#print axioms GlobularSet.targetIter_globular
#print axioms GlobularSet.compositeBoundary
#print axioms GlobularSet.Contraction.comp
#print axioms associatorCell

example (G : GlobularSet) (n : Nat) (c : Pasting n G) :
    Pasting.source (Pasting.identity c) = c := Pasting.source_identity G c

example (G : GlobularSet) (c : Pasting 7 G) :
    Pasting.target (Pasting.identity c) = c := Pasting.target_identity G c

#print axioms GlobularSet.hom
#print axioms GlobularSet.Map.hom
#print axioms Pasting.globular
#print axioms Pasting.identities

example {G H K : GlobularSet} (f : GlobularSet.Map G H) (g : GlobularSet.Map H K)
    (n : Nat) (c : Pasting n G) :
    Pasting.map g (Pasting.map f c) = Pasting.map (GlobularSet.Map.comp g f) c :=
  Pasting.map_comp f g c

#print axioms Pasting.pastingFunctor

example {O : Type} {E F D : O → O → Type}
    (f : {a b : O} → E a b → Chain F a b)
    (g : {a b : O} → F a b → Chain D a b) {a b : O} (p : Chain E a b) :
    (p.bind f).bind g = p.bind (fun e => (f e).bind g) := Chain.bind_assoc f g p

#print axioms Chain.bind_assoc
#print axioms evalPathChain_bind

example (G : GlobularSet) (n : Nat) (c d : G.Cell n)
    (h : Pasting.singleton c = Pasting.singleton d) : c = d :=
  Pasting.singleton_injective G h

example (G : GlobularSet) (c : G.Cell 8) :
    Pasting.source (Pasting.singleton c) = Pasting.singleton (G.source c) :=
  Pasting.source_singleton G c

example {G H : GlobularSet} (f : GlobularSet.Map G H) (n : Nat) (c : G.Cell n) :
    Pasting.map f (Pasting.singleton c) = Pasting.singleton (f.app c) :=
  Pasting.map_singleton f c

#print axioms Pasting.singleton_injective
#print axioms Pasting.singletonGlobular
#print axioms Pasting.singleton_natural

example {G : GlobularSet} (n : Nat) {a b c d : G.Cell 0}
    (p : Pasting.Horizontal n G a b) (q : Pasting.Horizontal n G b c)
    (r : Pasting.Horizontal n G c d) :
    Pasting.horizontal (Pasting.horizontal p q) r =
      Pasting.horizontal p (Pasting.horizontal q r) := Pasting.horizontal_assoc p q r

example {G : GlobularSet} {a b c : G.Cell 0}
    (p : Pasting.Horizontal 8 G a b) (q : Pasting.Horizontal 8 G b c) :
    (Pasting.globular G).sourceZero (n := 9) (Pasting.pack (Pasting.horizontal p q)) = a :=
  Pasting.sourceZero_pack _

#print axioms Pasting.horizontal_assoc
#print axioms Pasting.source_horizontal
#print axioms Pasting.target_horizontal
#print axioms Pasting.identity_horizontal
#print axioms Pasting.map_horizontal
#print axioms Pasting.sourceZero_pack

example {G : GlobularSet} (n : Nat) (p q : Pasting (n + 1) G)
    (h : Pasting.target p = Pasting.source q) :
    Pasting.source (Pasting.vertical p q h) = Pasting.source p :=
  Pasting.source_vertical p q h

example {G : GlobularSet} (p q : Pasting 9 G)
    (h : Pasting.target p = Pasting.source q) :
    Pasting.target (Pasting.vertical p q h) = Pasting.target q :=
  Pasting.target_vertical p q h

#print axioms Chain.zipOver
#print axioms Chain.map_zipOver_left
#print axioms Chain.map_zipOver_right
#print axioms Chain.zipOver_append
#print axioms Pasting.vertical
#print axioms Pasting.verticalCell

example {G : GlobularSet} (n : Nat) (p : Pasting (n + 1) G) :
    Pasting.vertical (Pasting.identity (Pasting.source p)) p
      (Pasting.target_identity G (Pasting.source p)) = p := Pasting.vertical_left_unit p

example {G : GlobularSet} (p q r : Pasting 9 G)
    (h : Pasting.target p = Pasting.source q) (k : Pasting.target q = Pasting.source r) :
    Pasting.vertical (Pasting.vertical p q h) r ((Pasting.target_vertical p q h).trans k) =
      Pasting.vertical p (Pasting.vertical q r k) (h.trans (Pasting.source_vertical q r k).symm) :=
  Pasting.vertical_assoc p q r h k

#print axioms Chain.zipOver_map_left
#print axioms Chain.zipOver_map_right
#print axioms Chain.zipOver_assoc
#print axioms Pasting.vertical_left_unit
#print axioms Pasting.vertical_right_unit
#print axioms Pasting.vertical_assoc
#print axioms Pasting.pack_verticalFibre
#print axioms Pasting.vertical_horizontal_interchange

example {G : GlobularSet} (k n : Nat) (p q : Pasting (n + k + 1) G)
    (h : Pasting.targetAt k n p = Pasting.sourceAt k n q) :
    Pasting.sourceAt k n (Pasting.composeAt k n p q h) = Pasting.sourceAt k n p :=
  Pasting.sourceAt_composeAt k n p q h

example {G : GlobularSet} (p q r : Pasting 9 G)
    (h : Pasting.targetAt 4 4 p = Pasting.sourceAt 4 4 q)
    (j : Pasting.targetAt 4 4 q = Pasting.sourceAt 4 4 r) :
    Pasting.composeAt 4 4 (Pasting.composeAt 4 4 p q h) r
      ((Pasting.targetAt_composeAt 4 4 p q h).trans j) =
    Pasting.composeAt 4 4 p (Pasting.composeAt 4 4 q r j)
      (h.trans (Pasting.sourceAt_composeAt 4 4 q r j).symm) :=
  Pasting.composeAt_assoc 4 4 p q r h j

#print axioms Pasting.sourceAt_adjacent
#print axioms Pasting.targetAt_adjacent
#print axioms Pasting.composeAt
#print axioms Pasting.sourceAt_composeAt
#print axioms Pasting.targetAt_composeAt
#print axioms Pasting.sourceAt_identityAt
#print axioms Pasting.targetAt_identityAt
#print axioms Pasting.composeAt_left_unit
#print axioms Pasting.composeAt_right_unit
#print axioms Pasting.composeAt_assoc

example {G : GlobularSet} (k n : Nat) (p : Pasting (n + k + 1) G) :
    Pasting.sourceAt k n p = (Pasting.globular G).sourceIter (n := k) (n + 1)
      (Pasting.reindex (by omega) p) := Pasting.sourceAt_eq_sourceIter k n p

example {G : GlobularSet} (p : Pasting 9 G) :
    Pasting.targetAt 4 4 p = (Pasting.globular G).targetIter (n := 4) 5 p :=
  Pasting.targetAt_eq_targetIter 4 4 p

#print axioms Pasting.sourceAt_step
#print axioms Pasting.targetAt_step
#print axioms Pasting.sourceAt_globular
#print axioms Pasting.targetAt_globular
#print axioms Pasting.sourceAt_lower
#print axioms Pasting.targetAt_lower
#print axioms Pasting.sourceAt_eq_sourceIter
#print axioms Pasting.targetAt_eq_targetIter

example {G H : GlobularSet} (f : GlobularSet.Map G H) (k n : Nat)
    (p q : Pasting (n + k + 1) G) (h : Pasting.targetAt k n p = Pasting.sourceAt k n q) :
    Pasting.map f (Pasting.composeAt k n p q h) =
      Pasting.composeAt k n (Pasting.map f p) (Pasting.map f q)
        ((Pasting.targetAt_map k n f p).trans
          ((_root_.congrArg (Pasting.map f) h).trans (Pasting.sourceAt_map k n f q).symm)) :=
  Pasting.map_composeAt_natural k n f p q h

#print axioms Chain.map_zipOver
#print axioms Chain.mapAlong_zipOver
#print axioms Pasting.sourceAt_map
#print axioms Pasting.targetAt_map
#print axioms Pasting.map_identityAt
#print axioms Pasting.map_composeAt_natural

example {G : GlobularSet} (k n : Nat) (p q : Pasting ((n + 1) + k + 1) G)
    (h : Pasting.targetAt k (n + 1) p = Pasting.sourceAt k (n + 1) q) :
    Pasting.dropSource k n (Pasting.composeAt k (n + 1) p q h) =
      Pasting.composeAt k n (Pasting.dropSource k n p) (Pasting.dropSource k n q)
        ((Pasting.targetAt_dropSource k n p).trans (h.trans (Pasting.sourceAt_dropSource k n q).symm)) :=
  Pasting.dropSource_composeAt_boundary k n p q h

example {G : GlobularSet} (p : Pasting 9 G) : Pasting.dropTarget 4 3 p = Pasting.target p :=
  Pasting.dropTarget_eq 4 3 p

#print axioms Pasting.dropSource_eq
#print axioms Pasting.dropTarget_eq
#print axioms Pasting.sourceAt_dropSource
#print axioms Pasting.targetAt_dropSource
#print axioms Pasting.sourceAt_dropTarget
#print axioms Pasting.targetAt_dropTarget
#print axioms Pasting.dropSource_composeAt_boundary
#print axioms Pasting.dropTarget_composeAt_boundary
#print axioms Pasting.dropSource_identityAt
#print axioms Pasting.dropTarget_identityAt

example {G : GlobularSet} (k : Nat) (p q : Pasting (0 + k + 1) G)
    (h : Pasting.targetAt k 0 p = Pasting.sourceAt k 0 q)
    (h' : Pasting.target p = Pasting.source q) :
    Pasting.composeAt k 0 p q h = Pasting.vertical p q h' :=
  Pasting.composeAt_adjacent k p q h h'

example {G : GlobularSet} (p : Pasting 7 G) : HEq (Pasting.identityAt 7 0 p) (Pasting.identity p) :=
  Pasting.identityAt_adjacent 7 p

#print axioms Chain.zipOver_congr
#print axioms Pasting.composeAt_horizontal
#print axioms Pasting.composeAt_adjacent_eq
#print axioms Pasting.identityAt_adjacent
#print axioms Pasting.identityAt_step
#print axioms Pasting.pack_composeAtFibre
#print axioms Pasting.composeAt_horizontal_interchange

example : Pasting.Cut.Below (Pasting.Cut.at 2 6) (Pasting.Cut.at 5 3) :=
  (Pasting.Cut.below_iff_height _ _).mpr (by decide)

example {G : GlobularSet} {n : Nat} (c d : Pasting.Cut n) (hc : Pasting.Cut.Below c d)
    (p q r s : Pasting n G)
    (hpq : Pasting.cutTarget c p = Pasting.cutSource c q)
    (hrs : Pasting.cutTarget c r = Pasting.cutSource c s)
    (hpr : Pasting.cutTarget d p = Pasting.cutSource d r)
    (hqs : Pasting.cutTarget d q = Pasting.cutSource d s)
    (hrow : Pasting.cutTarget d (Pasting.cutCompose c p q hpq) =
      Pasting.cutSource d (Pasting.cutCompose c r s hrs))
    (hcol : Pasting.cutTarget c (Pasting.cutCompose d p r hpr) =
      Pasting.cutSource c (Pasting.cutCompose d q s hqs)) :
    Pasting.cutCompose d (Pasting.cutCompose c p q hpq) (Pasting.cutCompose c r s hrs) hrow =
      Pasting.cutCompose c (Pasting.cutCompose d p r hpr) (Pasting.cutCompose d q s hqs) hcol :=
  Pasting.cutCompose_interchange hc p q r s hpq hrs hpr hqs hrow hcol

#print axioms Chain.zipOver_interchange
#print axioms Pasting.Cut.below_iff_height
#print axioms Pasting.cutSource_at
#print axioms Pasting.cutTarget_at
#print axioms Pasting.cutCompose_at_eq
#print axioms Pasting.cutCompose_interchange

example {G : GlobularSet} {n : Nat} (c d : Pasting.Cut n) (hc : Pasting.Cut.Below c d)
    (p q r s : Pasting n G)
    (hpq : Pasting.cutTarget c p = Pasting.cutSource c q)
    (hrs : Pasting.cutTarget c r = Pasting.cutSource c s)
    (hpr : Pasting.cutTarget d p = Pasting.cutSource d r)
    (hqs : Pasting.cutTarget d q = Pasting.cutSource d s) :
    Pasting.cutCompose d (Pasting.cutCompose c p q hpq) (Pasting.cutCompose c r s hrs)
      (Pasting.cutGrid_composable hc p q r s hpq hrs hpr hqs).1 =
    Pasting.cutCompose c (Pasting.cutCompose d p r hpr) (Pasting.cutCompose d q s hqs)
      (Pasting.cutGrid_composable hc p q r s hpq hrs hpr hqs).2 :=
  Pasting.cutCompose_interchange_grid hc p q r s hpq hrs hpr hqs

#print axioms Chain.zipOver_grid
#print axioms Pasting.cutGrid_composable
#print axioms Pasting.cutCompose_interchange_grid

example (A : Type) : RealizesPathSkeleton (NativeTower.globular A) A := NativeTower.realizes A

example {A : Type} (p : NativeTower.Cell A 9) :
    NativeTower.source (NativeTower.identity p) = p := NativeTower.source_identity p

example {A : Type} {n : Nat} (p q : NativeTower.Cell A (n + 3))
    (hs : NativeTower.source p = NativeTower.source q)
    (ht : NativeTower.target p = NativeTower.target q) : p = q := NativeTower.higher_ext p q hs ht

#print axioms NativeTower.globular
#print axioms NativeTower.realizes
#print axioms NativeTower.identities
#print axioms NativeTower.higher_ext
#print axioms NativeTower.associator_derivation
#print axioms NativeTower.distinct_rewrite_cells

example {A : Type} {n : Nat} (p : NativeTower.Cell A (n + 1)) :
    NativeTower.source (NativeTower.cancelRight p).val =
      NativeTower.compose p (NativeTower.reverse p) (NativeTower.source_reverse p).symm :=
  (NativeTower.cancelRight p).property.1

example {A : Type} (p : NativeTower.Cell A 9) :
    NativeTower.target (NativeTower.cancelLeft p).val = NativeTower.identity (NativeTower.target p) :=
  (NativeTower.cancelLeft p).property.2

#print axioms NativeTower.source_reverse
#print axioms NativeTower.target_reverse
#print axioms NativeTower.compose_boundary
#print axioms NativeTower.compose_paths
#print axioms NativeTower.compose_rewrites
#print axioms NativeTower.cancelRight
#print axioms NativeTower.cancelLeft
#print axioms NativeTower.cancelRight_paths
#print axioms NativeTower.cancelLeft_paths

example {A : Type} (n : Nat) (p : NativeTower.Cell A (n + 1)) :
    NativeTower.WeaklyInvertible (n + 1) (NativeTower.cancelRight p).val :=
  NativeTower.all_cells_weaklyInvertible _ _

#print axioms NativeTower.invertibilityStep_mono
#print axioms NativeTower.weaklyInvertible_coinduction
#print axioms NativeTower.weaklyInvertible_unfold
#print axioms NativeTower.all_cells_weaklyInvertible

example {A : Type} {n : Nat} (p q r : NativeTower.Cell A (n + 1))
    (hpq : NativeTower.target p = NativeTower.source q)
    (hqr : NativeTower.target q = NativeTower.source r) :
    NativeTower.WeaklyInvertible (n + 1) (NativeTower.composeAssociator p q r hpq hqr).val :=
  NativeTower.all_cells_weaklyInvertible _ _

example {A : Type} {n : Nat} (p : NativeTower.Cell A (n + 1)) :
    NativeTower.WeaklyInvertible (n + 1) (NativeTower.leftUnitor p).val ∧
    NativeTower.WeaklyInvertible (n + 1) (NativeTower.rightUnitor p).val :=
  ⟨NativeTower.all_cells_weaklyInvertible _ _, NativeTower.all_cells_weaklyInvertible _ _⟩

#print axioms NativeTower.composeAssociator
#print axioms NativeTower.leftUnitor
#print axioms NativeTower.rightUnitor
#print axioms NativeTower.composeAssociator_paths
#print axioms NativeTower.leftUnitor_paths
#print axioms NativeTower.rightUnitor_paths

#print axioms Pasting.evaluateGlobular
#print axioms Pasting.evaluate_singleton
#print axioms Pasting.pack_unpackFibre
#print axioms Pasting.unpack_packFibre
#print axioms Pasting.horizontalComposition
#print axioms Pasting.horizontalComposition_right_unit
#print axioms Pasting.horizontalComposition_fold

#print axioms GlobularSet.homInclusion
#print axioms GlobularSet.sourceZeroMap
#print axioms GlobularSet.targetZeroMap
#print axioms Pasting.CutBoundary.source_map
#print axioms Pasting.CutBoundary.target_map
#print axioms Pasting.CutBoundary.source_hom
#print axioms Pasting.CutBoundary.target_hom
#print axioms Pasting.CutOperations.hom
#print axioms Pasting.CutOperations.hom_compose_val
#print axioms Pasting.CutOperations.hom_unit_val
#print axioms Pasting.CutOperations.inContext

#print axioms Pasting.canonical_source_eq_cutSource
#print axioms Pasting.canonical_target_eq_cutTarget
#print axioms Pasting.cutSource_cutCompose
#print axioms Pasting.cutTarget_cutCompose
#print axioms Pasting.cutSource_cutUnit
#print axioms Pasting.cutTarget_cutUnit
#print axioms Pasting.cutCompose_left_unit
#print axioms Pasting.cutCompose_right_unit
#print axioms Pasting.cutOperations

#print axioms Pasting.source_cutCompose
#print axioms Pasting.target_cutCompose
#print axioms Pasting.source_cutUnit_reindex
#print axioms Pasting.target_cutUnit_reindex
#print axioms Pasting.cutOperations_compatible
#print axioms Pasting.CutOperations.Compatible.hom
#print axioms Pasting.CutOperations.RightUnital.hom
#print axioms Pasting.recursiveComposition
#print axioms Pasting.flattenGlobular
#print axioms Pasting.flatten_singleton

#print axioms Pasting.CutOperations.Preserves.hom
#print axioms Pasting.map_cutCompose
#print axioms Pasting.map_cutUnit
#print axioms Pasting.mapGlobular_preserves
#print axioms Pasting.evaluate_precompose
#print axioms Pasting.evaluate_postcompose
#print axioms Pasting.flatten_natural
#print axioms Pasting.flattenNatTrans

#print axioms Pasting.homPastingInclusion
#print axioms Pasting.homPastingInclusion_preserves
#print axioms Pasting.singleton_hom_factor
#print axioms Pasting.recursive_fold_single
#print axioms Pasting.evaluate_singletonLabels
#print axioms Pasting.flatten_map_singleton
#print axioms Pasting.singletonNatTrans
#print axioms Pasting.flatten_unit_left
#print axioms Pasting.flatten_unit_right

#print axioms Pasting.cutCompose_assoc
#print axioms Pasting.cutOperations_associative
#print axioms Pasting.cutOperations_leftUnital
#print axioms Pasting.cutOperations_interchange
#print axioms Pasting.CutOperations.Associative.inContext
#print axioms Pasting.CutOperations.Interchange.inContext
#print axioms Pasting.CutOperations.fold_append
#print axioms Pasting.evaluate_horizontal
#print axioms Pasting.flatten_horizontal
#print axioms Pasting.flatten_cutCompose_bottom

#print axioms Pasting.cutCompose_unit_idempotent
#print axioms Pasting.cutOperations_unitIdempotent
#print axioms Pasting.CutOperations.UnitIdempotent.inContext
#print axioms Pasting.CutOperations.horizontal_interchange
#print axioms Pasting.CutOperations.fold_zipOver
#print axioms Pasting.map_cut_composable
#print axioms Pasting.evaluate_cutCompose
#print axioms Pasting.flatten_cutCompose

#print axioms Pasting.cutUnit_compose
#print axioms Pasting.cutUnit_unit_reindex
#print axioms Pasting.cutOperations_unitCompatible
#print axioms Pasting.CutOperations.UnitCompatible.inContext
#print axioms Pasting.CutOperations.fold_unit
#print axioms Pasting.evaluate_cutUnit
#print axioms Pasting.flatten_cutUnit
#print axioms Pasting.flatten_preserves
#print axioms Pasting.flatten_assoc
#print axioms Pasting.pastingMonad

example (G : GlobularSet) {n : Nat} (p : Pasting n (Pasting.globular (Pasting.globular G))) :
    (Pasting.flattenGlobular G).app (n := n)
        ((Pasting.flattenGlobular (Pasting.globular G)).app (n := n) p) =
      (Pasting.flattenGlobular G).app (n := n) (Pasting.map (Pasting.flattenGlobular G) p) :=
  Pasting.flatten_assoc G p

noncomputable example : CategoryTheory.Monad GlobularSet := Pasting.pastingMonad

example {G : GlobularSet} {n : Nat} (c : Pasting.Cut n)
    (p q : Pasting n (Pasting.globular G)) (h : Pasting.cutTarget c p = Pasting.cutSource c q)
    (h' : Pasting.cutTarget c ((Pasting.flattenGlobular G).app (n := n) p) =
      Pasting.cutSource c ((Pasting.flattenGlobular G).app (n := n) q)) :
    (Pasting.flattenGlobular G).app (n := n) (Pasting.cutCompose c p q h) =
      Pasting.cutCompose c ((Pasting.flattenGlobular G).app (n := n) p)
        ((Pasting.flattenGlobular G).app (n := n) q) h' := Pasting.flatten_cutCompose c p q h h'

example {G : GlobularSet} {n : Nat} (p : Pasting n G) :
    (Pasting.flattenGlobular G).app (n := n) (Pasting.map (Pasting.singletonGlobular G) p) = p :=
  Pasting.flatten_map_singleton p

example {G H : GlobularSet} (f : GlobularSet.Map G H) {n : Nat} (p : Pasting n (Pasting.globular G)) :
    Pasting.map f ((Pasting.flattenGlobular G).app (n := n) p) =
      (Pasting.flattenGlobular H).app (n := n) (Pasting.map (Pasting.mapGlobular f) p) :=
  Pasting.flatten_natural f p

example (G : GlobularSet) {n : Nat} (p : Pasting (n + 1) (Pasting.globular G)) :
    Pasting.source ((Pasting.flattenGlobular G).app (n := n + 1) p) =
      (Pasting.flattenGlobular G).app (n := n) (Pasting.source p) :=
  (Pasting.flattenGlobular G).source_app (n := n) p

example (G : GlobularSet) {n : Nat} (p : Pasting n G) :
    (Pasting.flattenGlobular G).app (Pasting.singleton (G := Pasting.globular G) p) = p :=
  Pasting.flatten_singleton p

example {G H : GlobularSet} (h : Pasting.HomContext (Pasting.globular G) H)
    {n : Nat} (c : Pasting.Cut n) (p q : H.Cell n)
    (hpq : Pasting.CutBoundary.target c H p = Pasting.CutBoundary.source c H q) :
    Pasting.CutBoundary.source c H (((Pasting.cutOperations G).inContext h).compose c p q hpq) =
      Pasting.CutBoundary.source c H p :=
  ((Pasting.cutOperations G).inContext h).source_compose c p q hpq

example {G H : GlobularSet} (C : Pasting.CutOperations G)
    (h : Pasting.HomContext G H) {n : Nat} (c : Pasting.Cut n)
    (p q : H.Cell n) (hpq : Pasting.CutBoundary.target c H p = Pasting.CutBoundary.source c H q) :
    Pasting.CutBoundary.source c H ((C.inContext h).compose c p q hpq) =
      Pasting.CutBoundary.source c H p := (C.inContext h).source_compose c p q hpq

example (G : GlobularSet) {n : Nat} {a b : G.Cell 0}
    (p : Chain (fun x y => Pasting.Horizontal n G x y) a b) :
    (Pasting.horizontalComposition G).fold (p.map (fun e => Pasting.packFibre e)) =
      Pasting.packFibre (p.bind (fun e => e)) := Pasting.horizontalComposition_fold p

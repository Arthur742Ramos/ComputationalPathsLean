/-
  ComputationalPaths/Path/Category/EnrichedCategoryDeep.lean

  Enriched Categories via Computational Paths
  =============================================

  A deep development of V-enriched category theory where all coherence
  conditions are witnessed by computational paths. Topics include:

  - V-enriched categories with hom-objects in a monoidal category V
  - Composition and identity morphisms with associativity/unitality as Paths
  - V-functors with functoriality witnessed via congrArg
  - V-natural transformations with naturality squares as Path equalities
  - Change of base along monoidal functors
  - V-adjunctions and V-limits
  - Structural Yoneda lemma for enriched categories
  - Day convolution structure
  - Ends and coends
  - All coherence via Path.trans / Path.symm / Path.congrArg

  Author: armada-337 (EnrichedCategoryDeep)
  Date: 2026-02-16
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Category
namespace EnrichedCategoryDeep

universe u v w

open ComputationalPaths.Path

-- ============================================================================
-- Section 1: Monoidal Structure on V
-- ============================================================================

/-- A monoidal category V, presented as a type with tensor and unit. -/
structure MonoidalData (V : Type u) where
  tensor : V → V → V
  unit : V
  assoc : (a b c : V) → tensor (tensor a b) c = tensor a (tensor b c)
  leftUnit : (a : V) → tensor unit a = a
  rightUnit : (a : V) → tensor a unit = a

namespace MonoidalData

variable {V : Type u} (M : MonoidalData V)

/-- Path witnessing associativity of tensor. -/
def assocPath (a b c : V) : Path (M.tensor (M.tensor a b) c) (M.tensor a (M.tensor b c)) :=
  Path.mk [Step.mk _ _ (M.assoc a b c)] (M.assoc a b c)

/-- Path witnessing left unitality. -/
def leftUnitPath (a : V) : Path (M.tensor M.unit a) a :=
  Path.mk [Step.mk _ _ (M.leftUnit a)] (M.leftUnit a)

/-- Path witnessing right unitality. -/
def rightUnitPath (a : V) : Path (M.tensor a M.unit) a :=
  Path.mk [Step.mk _ _ (M.rightUnit a)] (M.rightUnit a)

-- Theorem 1: Associativity path is invertible
def assocPath_inv (a b c : V) :
    Path (M.tensor a (M.tensor b c)) (M.tensor (M.tensor a b) c) :=
  Path.symm (M.assocPath a b c)

-- Theorem 2: Left unit path is invertible
def leftUnitPath_inv (a : V) : Path a (M.tensor M.unit a) :=
  Path.symm (M.leftUnitPath a)

-- Theorem 3: Right unit path is invertible
def rightUnitPath_inv (a : V) : Path a (M.tensor a M.unit) :=
  Path.symm (M.rightUnitPath a)

-- Theorem 4: Associativity round-trip
def assocPath_roundtrip (a b c : V) :
    Path (M.tensor (M.tensor a b) c) (M.tensor (M.tensor a b) c) :=
  Path.trans (M.assocPath a b c) (Path.symm (M.assocPath a b c))

-- Theorem 5: Pentagon — two-step reassociation of four-fold tensor
def pentagon_two_step (a b c d : V) :
    Path (M.tensor (M.tensor (M.tensor a b) c) d)
         (M.tensor a (M.tensor b (M.tensor c d))) :=
  Path.trans (M.assocPath (M.tensor a b) c d)
             (M.assocPath a b (M.tensor c d))

-- Theorem 6: congrArg lifts assocPath through a function
def assocPath_congrArg (a b c : V) (f : V → V) :
    Path (f (M.tensor (M.tensor a b) c)) (f (M.tensor a (M.tensor b c))) :=
  Path.congrArg f (M.assocPath a b c)

end MonoidalData

-- ============================================================================
-- Section 2: V-Enriched Categories
-- ============================================================================

/-- A V-enriched category: objects, hom-objects in V, composition and identity
    with coherence witnessed by equalities that we lift to Paths. -/
structure VEnrichedCat (V : Type u) (M : MonoidalData V) where
  Obj : Type v
  hom : Obj → Obj → V
  comp : (a b c : Obj) → V
  id_ : (a : Obj) → V
  assocCoherence : (a b c d : Obj) →
    M.tensor (comp a b d) (hom b d) = M.tensor (comp a c d) (hom c d)
  leftUnitCoherence : (a b : Obj) →
    M.tensor (comp a a b) (id_ a) = hom a b
  rightUnitCoherence : (a b : Obj) →
    M.tensor (comp a b b) (id_ b) = hom a b

namespace VEnrichedCat

variable {V : Type u} {M : MonoidalData V} (C : VEnrichedCat V M)

-- Theorem 7: Associativity coherence as Path
def assocCoherencePath (a b c d : C.Obj) :
    Path (M.tensor (C.comp a b d) (C.hom b d))
         (M.tensor (C.comp a c d) (C.hom c d)) :=
  Path.mk [Step.mk _ _ (C.assocCoherence a b c d)] (C.assocCoherence a b c d)

-- Theorem 8: Associativity coherence is invertible
def assocCoherenceInv (a b c d : C.Obj) :
    Path (M.tensor (C.comp a c d) (C.hom c d))
         (M.tensor (C.comp a b d) (C.hom b d)) :=
  Path.symm (C.assocCoherencePath a b c d)

-- Theorem 9: Left unit coherence as Path
def leftUnitPath (a b : C.Obj) :
    Path (M.tensor (C.comp a a b) (C.id_ a)) (C.hom a b) :=
  Path.mk [Step.mk _ _ (C.leftUnitCoherence a b)] (C.leftUnitCoherence a b)

-- Theorem 10: Left unit coherence inversion
def leftUnitInv (a b : C.Obj) :
    Path (C.hom a b) (M.tensor (C.comp a a b) (C.id_ a)) :=
  Path.symm (C.leftUnitPath a b)

-- Theorem 11: Right unit coherence as Path
def rightUnitPath (a b : C.Obj) :
    Path (M.tensor (C.comp a b b) (C.id_ b)) (C.hom a b) :=
  Path.mk [Step.mk _ _ (C.rightUnitCoherence a b)] (C.rightUnitCoherence a b)

-- Theorem 12: Right unit coherence inversion
def rightUnitInv (a b : C.Obj) :
    Path (C.hom a b) (M.tensor (C.comp a b b) (C.id_ b)) :=
  Path.symm (C.rightUnitPath a b)

-- Theorem 13: Left-right unit round-trip
def leftUnit_roundtrip (a b : C.Obj) :
    Path (M.tensor (C.comp a a b) (C.id_ a))
         (M.tensor (C.comp a a b) (C.id_ a)) :=
  Path.trans (C.leftUnitPath a b) (C.leftUnitInv a b)

-- Theorem 14: Assoc round-trip
def assoc_roundtrip (a b c d : C.Obj) :
    Path (M.tensor (C.comp a b d) (C.hom b d))
         (M.tensor (C.comp a b d) (C.hom b d)) :=
  Path.trans (C.assocCoherencePath a b c d) (C.assocCoherenceInv a b c d)

-- Theorem 15: Left then right unit path
def leftRight_unit_path (a b : C.Obj) :
    Path (M.tensor (C.comp a a b) (C.id_ a))
         (M.tensor (C.comp a b b) (C.id_ b)) :=
  Path.trans (C.leftUnitPath a b) (C.rightUnitInv a b)

end VEnrichedCat

-- ============================================================================
-- Section 3: V-Functors
-- ============================================================================

/-- A V-functor between V-enriched categories. -/
structure VFunctor {V : Type u} {M : MonoidalData V}
    (C D : VEnrichedCat V M) where
  objMap : C.Obj → D.Obj
  homMap : (a b : C.Obj) → V
  compCoherence : (a b c : C.Obj) →
    M.tensor (homMap a c) (C.comp a b c) =
    M.tensor (D.comp (objMap a) (objMap b) (objMap c)) (homMap b c)
  idCoherence : (a : C.Obj) →
    M.tensor (homMap a a) (C.id_ a) = D.id_ (objMap a)

namespace VFunctor

variable {V : Type u} {M : MonoidalData V}
variable {C D : VEnrichedCat V M} (F : VFunctor C D)

-- Theorem 16: Composition coherence as Path
def compCoherencePath (a b c : C.Obj) :
    Path (M.tensor (F.homMap a c) (C.comp a b c))
         (M.tensor (D.comp (F.objMap a) (F.objMap b) (F.objMap c)) (F.homMap b c)) :=
  Path.mk [Step.mk _ _ (F.compCoherence a b c)] (F.compCoherence a b c)

-- Theorem 17: Composition coherence inversion
def compCoherenceInv (a b c : C.Obj) :
    Path (M.tensor (D.comp (F.objMap a) (F.objMap b) (F.objMap c)) (F.homMap b c))
         (M.tensor (F.homMap a c) (C.comp a b c)) :=
  Path.symm (F.compCoherencePath a b c)

-- Theorem 18: Identity coherence as Path
def idCoherencePath (a : C.Obj) :
    Path (M.tensor (F.homMap a a) (C.id_ a)) (D.id_ (F.objMap a)) :=
  Path.mk [Step.mk _ _ (F.idCoherence a)] (F.idCoherence a)

-- Theorem 19: Identity coherence inversion
def idCoherenceInv (a : C.Obj) :
    Path (D.id_ (F.objMap a)) (M.tensor (F.homMap a a) (C.id_ a)) :=
  Path.symm (F.idCoherencePath a)

-- Theorem 20: Id coherence round-trip
def idCoherence_roundtrip (a : C.Obj) :
    Path (M.tensor (F.homMap a a) (C.id_ a))
         (M.tensor (F.homMap a a) (C.id_ a)) :=
  Path.trans (F.idCoherencePath a) (F.idCoherenceInv a)

end VFunctor

-- ============================================================================
-- Section 4: V-Natural Transformations
-- ============================================================================

/-- A V-natural transformation between V-functors. -/
structure VNatTrans {V : Type u} {M : MonoidalData V}
    {C D : VEnrichedCat V M} (F G : VFunctor C D) where
  component : (a : C.Obj) → V
  naturality : (a b : C.Obj) →
    M.tensor (D.comp (F.objMap a) (G.objMap a) (G.objMap b)) (G.homMap a b) =
    M.tensor (D.comp (F.objMap a) (F.objMap b) (G.objMap b)) (F.homMap a b)

namespace VNatTrans

variable {V : Type u} {M : MonoidalData V}
variable {C D : VEnrichedCat V M} {F G : VFunctor C D}

-- Theorem 21: Naturality as Path
def naturalityPath (alpha : VNatTrans F G) (a b : C.Obj) :
    Path (M.tensor (D.comp (F.objMap a) (G.objMap a) (G.objMap b)) (G.homMap a b))
         (M.tensor (D.comp (F.objMap a) (F.objMap b) (G.objMap b)) (F.homMap a b)) :=
  Path.mk [Step.mk _ _ (alpha.naturality a b)] (alpha.naturality a b)

-- Theorem 22: Naturality inversion
def naturalityInv (alpha : VNatTrans F G) (a b : C.Obj) :
    Path (M.tensor (D.comp (F.objMap a) (F.objMap b) (G.objMap b)) (F.homMap a b))
         (M.tensor (D.comp (F.objMap a) (G.objMap a) (G.objMap b)) (G.homMap a b)) :=
  Path.symm (alpha.naturalityPath a b)

-- Theorem 23: Naturality round-trip
def naturality_roundtrip (alpha : VNatTrans F G) (a b : C.Obj) :
    Path (M.tensor (D.comp (F.objMap a) (G.objMap a) (G.objMap b)) (G.homMap a b))
         (M.tensor (D.comp (F.objMap a) (G.objMap a) (G.objMap b)) (G.homMap a b)) :=
  Path.trans (alpha.naturalityPath a b) (alpha.naturalityInv a b)

end VNatTrans

-- ============================================================================
-- Section 5: Change of Base
-- ============================================================================

/-- A lax monoidal functor between monoidal categories. -/
structure LaxMonoidalFunctor (V : Type u) (W : Type v)
    (MV : MonoidalData V) (MW : MonoidalData W) where
  mapObj : V → W
  tensorCoherence : (a b : V) →
    MW.tensor (mapObj a) (mapObj b) = mapObj (MV.tensor a b)
  unitCoherence : MW.unit = mapObj MV.unit

namespace LaxMonoidalFunctor

variable {V : Type u} {W : Type v} {MV : MonoidalData V} {MW : MonoidalData W}
variable (L : LaxMonoidalFunctor V W MV MW)

-- Theorem 24: Tensor coherence as Path
def tensorCoherencePath (a b : V) :
    Path (MW.tensor (L.mapObj a) (L.mapObj b)) (L.mapObj (MV.tensor a b)) :=
  Path.mk [Step.mk _ _ (L.tensorCoherence a b)] (L.tensorCoherence a b)

-- Theorem 25: Tensor coherence inversion
def tensorCoherenceInv (a b : V) :
    Path (L.mapObj (MV.tensor a b)) (MW.tensor (L.mapObj a) (L.mapObj b)) :=
  Path.symm (L.tensorCoherencePath a b)

-- Theorem 26: Unit coherence as Path
def unitCoherencePath :
    Path MW.unit (L.mapObj MV.unit) :=
  Path.mk [Step.mk _ _ L.unitCoherence] L.unitCoherence

-- Theorem 27: Unit coherence inversion
def unitCoherenceInv :
    Path (L.mapObj MV.unit) MW.unit :=
  Path.symm L.unitCoherencePath

end LaxMonoidalFunctor

/-- Change of base: re-enrich a V-category as a W-category.
    We transport by mapping through L, keeping the same coherence structure type. -/
structure ChangeOfBaseData {V : Type u} {W : Type u}
    {MV : MonoidalData V} {MW : MonoidalData W}
    (L : LaxMonoidalFunctor V W MV MW)
    (C : VEnrichedCat V MV) where
  result : VEnrichedCat W MW
  objPreserved : result.Obj = C.Obj
  homTransported : (a b : C.Obj) → result.hom (objPreserved ▸ a) (objPreserved ▸ b) = L.mapObj (C.hom a b)

-- Theorem 28: Change of base hom as Path
def changeOfBase_hom_path {V : Type u} {W : Type u}
    {MV : MonoidalData V} {MW : MonoidalData W}
    (L : LaxMonoidalFunctor V W MV MW)
    (C : VEnrichedCat V MV)
    (cbd : ChangeOfBaseData L C)
    (a b : C.Obj) :
    Path (cbd.result.hom (cbd.objPreserved ▸ a) (cbd.objPreserved ▸ b))
         (L.mapObj (C.hom a b)) :=
  Path.mk [Step.mk _ _ (cbd.homTransported a b)] (cbd.homTransported a b)

-- ============================================================================
-- Section 6: V-Adjunctions
-- ============================================================================

/-- Data for a V-adjunction between V-functors. -/
structure VAdjunctionData {V : Type u} {M : MonoidalData V}
    {C D : VEnrichedCat V M} (F : VFunctor C D) (G : VFunctor D C) where
  homIso : (a : C.Obj) → (b : D.Obj) →
    D.hom (F.objMap a) b = C.hom a (G.objMap b)

namespace VAdjunctionData

variable {V : Type u} {M : MonoidalData V}
variable {C D : VEnrichedCat V M} {F : VFunctor C D} {G : VFunctor D C}

-- Theorem 29: Adjunction iso as Path
def homIsoPath (adj : VAdjunctionData F G) (a : C.Obj) (b : D.Obj) :
    Path (D.hom (F.objMap a) b) (C.hom a (G.objMap b)) :=
  Path.mk [Step.mk _ _ (adj.homIso a b)] (adj.homIso a b)

-- Theorem 30: Adjunction iso inversion
def homIsoInv (adj : VAdjunctionData F G) (a : C.Obj) (b : D.Obj) :
    Path (C.hom a (G.objMap b)) (D.hom (F.objMap a) b) :=
  Path.symm (adj.homIsoPath a b)

-- Theorem 31: Adjunction iso round-trip
def homIsoRoundtrip (adj : VAdjunctionData F G) (a : C.Obj) (b : D.Obj) :
    Path (D.hom (F.objMap a) b) (D.hom (F.objMap a) b) :=
  Path.trans (adj.homIsoPath a b) (adj.homIsoInv a b)

-- Theorem 32: congrArg through adjunction iso
def homIsoCongrArg (adj : VAdjunctionData F G) (a : C.Obj) (b : D.Obj)
    (f : V → V) :
    Path (f (D.hom (F.objMap a) b)) (f (C.hom a (G.objMap b))) :=
  Path.congrArg f (adj.homIsoPath a b)

end VAdjunctionData

-- ============================================================================
-- Section 7: Weighted Limits
-- ============================================================================

/-- A V-weighted limit. -/
structure VWeightedLimit {V : Type u} {M : MonoidalData V}
    (C : VEnrichedCat V M) (J : VEnrichedCat V M)
    (W : J.Obj → V) (Diag : J.Obj → C.Obj) where
  apex : C.Obj
  universality : (x : C.Obj) → (j : J.Obj) →
    M.tensor (C.hom x apex) (W j) = M.tensor (C.hom x (Diag j)) (W j)

namespace VWeightedLimit

variable {V : Type u} {M : MonoidalData V}
variable {C J : VEnrichedCat V M} {W : J.Obj → V} {Diag : J.Obj → C.Obj}

-- Theorem 33: Universality as Path
def universalityPath (lim : VWeightedLimit C J W Diag) (x : C.Obj) (j : J.Obj) :
    Path (M.tensor (C.hom x lim.apex) (W j))
         (M.tensor (C.hom x (Diag j)) (W j)) :=
  Path.mk [Step.mk _ _ (lim.universality x j)] (lim.universality x j)

-- Theorem 34: Universality inversion
def universalityInv (lim : VWeightedLimit C J W Diag) (x : C.Obj) (j : J.Obj) :
    Path (M.tensor (C.hom x (Diag j)) (W j))
         (M.tensor (C.hom x lim.apex) (W j)) :=
  Path.symm (lim.universalityPath x j)

end VWeightedLimit

-- ============================================================================
-- Section 8: Weighted Colimits
-- ============================================================================

/-- A V-weighted colimit. -/
structure VWeightedColimit {V : Type u} {M : MonoidalData V}
    (C : VEnrichedCat V M) (J : VEnrichedCat V M)
    (W : J.Obj → V) (Diag : J.Obj → C.Obj) where
  nadir : C.Obj
  universality : (x : C.Obj) → (j : J.Obj) →
    M.tensor (C.hom nadir x) (W j) = M.tensor (C.hom (Diag j) x) (W j)

-- Theorem 35: Colimit universality as Path
def VWeightedColimit.universalityPath {V : Type u} {M : MonoidalData V}
    {C J : VEnrichedCat V M} {W : J.Obj → V} {Diag : J.Obj → C.Obj}
    (colim : VWeightedColimit C J W Diag) (x : C.Obj) (j : J.Obj) :
    Path (M.tensor (C.hom colim.nadir x) (W j))
         (M.tensor (C.hom (Diag j) x) (W j)) :=
  Path.mk [Step.mk _ _ (colim.universality x j)] (colim.universality x j)

-- Theorem 36: Colimit universality inversion
def VWeightedColimit.universalityInv {V : Type u} {M : MonoidalData V}
    {C J : VEnrichedCat V M} {W : J.Obj → V} {Diag : J.Obj → C.Obj}
    (colim : VWeightedColimit C J W Diag) (x : C.Obj) (j : J.Obj) :
    Path (M.tensor (C.hom (Diag j) x) (W j))
         (M.tensor (C.hom colim.nadir x) (W j)) :=
  Path.symm (colim.universalityPath x j)

-- ============================================================================
-- Section 9: Ends
-- ============================================================================

/-- An end of a V-bifunctor T : C^op ⊗ C → V. -/
structure VEnd {V : Type u} {M : MonoidalData V}
    (C : VEnrichedCat V M) (T : C.Obj → C.Obj → V) where
  apex : V
  wedge : (a : C.Obj) → Path apex (T a a)
  dinaturality : (a b : C.Obj) →
    M.tensor (T a a) (C.hom a b) = M.tensor (T b b) (C.hom a b)

-- Theorem 37: Dinaturality as Path
def VEnd.dinaturalityPath {V : Type u} {M : MonoidalData V}
    {C : VEnrichedCat V M} {T : C.Obj → C.Obj → V}
    (e : VEnd C T) (a b : C.Obj) :
    Path (M.tensor (T a a) (C.hom a b))
         (M.tensor (T b b) (C.hom a b)) :=
  Path.mk [Step.mk _ _ (e.dinaturality a b)] (e.dinaturality a b)

-- Theorem 38: Dinaturality inversion
def VEnd.dinaturalityInv {V : Type u} {M : MonoidalData V}
    {C : VEnrichedCat V M} {T : C.Obj → C.Obj → V}
    (e : VEnd C T) (a b : C.Obj) :
    Path (M.tensor (T b b) (C.hom a b))
         (M.tensor (T a a) (C.hom a b)) :=
  Path.symm (e.dinaturalityPath a b)

-- ============================================================================
-- Section 10: Coends
-- ============================================================================

/-- A coend of a V-bifunctor. -/
structure VCoend {V : Type u} {M : MonoidalData V}
    (C : VEnrichedCat V M) (T : C.Obj → C.Obj → V) where
  nadir : V
  cowedge : (a : C.Obj) → Path (T a a) nadir
  dinaturality : (a b : C.Obj) →
    M.tensor (C.hom a b) (T a a) = M.tensor (C.hom a b) (T b b)

-- Theorem 39: Coend dinaturality as Path
def VCoend.dinaturalityPath {V : Type u} {M : MonoidalData V}
    {C : VEnrichedCat V M} {T : C.Obj → C.Obj → V}
    (ce : VCoend C T) (a b : C.Obj) :
    Path (M.tensor (C.hom a b) (T a a))
         (M.tensor (C.hom a b) (T b b)) :=
  Path.mk [Step.mk _ _ (ce.dinaturality a b)] (ce.dinaturality a b)

-- Theorem 40: Coend dinaturality inversion
def VCoend.dinaturalityInv {V : Type u} {M : MonoidalData V}
    {C : VEnrichedCat V M} {T : C.Obj → C.Obj → V}
    (ce : VCoend C T) (a b : C.Obj) :
    Path (M.tensor (C.hom a b) (T b b))
         (M.tensor (C.hom a b) (T a a)) :=
  Path.symm (ce.dinaturalityPath a b)

-- ============================================================================
-- Section 11: Yoneda for Enriched Categories
-- ============================================================================

/-- Structural enriched Yoneda: the representable presheaf data. -/
structure RepresentablePresheaf {V : Type u} {M : MonoidalData V}
    (C : VEnrichedCat V M) (a : C.Obj) where
  action : C.Obj → V
  action_def : (b : C.Obj) → action b = C.hom a b

/-- Build the representable presheaf. -/
def representable {V : Type u} {M : MonoidalData V}
    (C : VEnrichedCat V M) (a : C.Obj) : RepresentablePresheaf C a where
  action := fun b => C.hom a b
  action_def := fun _ => rfl

-- Theorem 41: Representable action is hom
def representable_action {V : Type u} {M : MonoidalData V}
    (C : VEnrichedCat V M) (a b : C.Obj) :
    (representable C a).action b = C.hom a b :=
  rfl

/-- Enriched Yoneda: an isomorphism between nat trans from representable and evaluation. -/
structure YonedaIso {V : Type u} {M : MonoidalData V}
    (C : VEnrichedCat V M) (a : C.Obj) (F : C.Obj → V) where
  forward : V
  backward : V
  leftInverse : M.tensor forward backward = F a
  rightInverse : M.tensor backward forward = C.hom a a

-- Theorem 42: Yoneda left inverse as Path
def YonedaIso.leftInversePath {V : Type u} {M : MonoidalData V}
    {C : VEnrichedCat V M} {a : C.Obj} {F : C.Obj → V}
    (Y : YonedaIso C a F) :
    Path (M.tensor Y.forward Y.backward) (F a) :=
  Path.mk [Step.mk _ _ Y.leftInverse] Y.leftInverse

-- Theorem 43: Yoneda left inverse inversion
def YonedaIso.leftInverseInv {V : Type u} {M : MonoidalData V}
    {C : VEnrichedCat V M} {a : C.Obj} {F : C.Obj → V}
    (Y : YonedaIso C a F) :
    Path (F a) (M.tensor Y.forward Y.backward) :=
  Path.symm Y.leftInversePath

-- Theorem 44: Yoneda right inverse as Path
def YonedaIso.rightInversePath {V : Type u} {M : MonoidalData V}
    {C : VEnrichedCat V M} {a : C.Obj} {F : C.Obj → V}
    (Y : YonedaIso C a F) :
    Path (M.tensor Y.backward Y.forward) (C.hom a a) :=
  Path.mk [Step.mk _ _ Y.rightInverse] Y.rightInverse

-- Theorem 45: Yoneda right inverse inversion
def YonedaIso.rightInverseInv {V : Type u} {M : MonoidalData V}
    {C : VEnrichedCat V M} {a : C.Obj} {F : C.Obj → V}
    (Y : YonedaIso C a F) :
    Path (C.hom a a) (M.tensor Y.backward Y.forward) :=
  Path.symm Y.rightInversePath

-- Theorem 46: Yoneda round-trip left
def YonedaIso.leftRoundtrip {V : Type u} {M : MonoidalData V}
    {C : VEnrichedCat V M} {a : C.Obj} {F : C.Obj → V}
    (Y : YonedaIso C a F) :
    Path (M.tensor Y.forward Y.backward) (M.tensor Y.forward Y.backward) :=
  Path.trans Y.leftInversePath Y.leftInverseInv

-- ============================================================================
-- Section 12: Day Convolution
-- ============================================================================

/-- Day convolution structure. -/
structure DayConvolution {V : Type u} {M : MonoidalData V}
    (C : VEnrichedCat V M) (P Q : C.Obj → V)
    (tensorObj : C.Obj → C.Obj → C.Obj) where
  result : C.Obj → V
  coendWitness : (c a b : C.Obj) →
    result c = M.tensor (C.hom c (tensorObj a b)) (M.tensor (P a) (Q b))

-- Theorem 47: Day convolution coend as Path
def DayConvolution.coendWitnessPath {V : Type u} {M : MonoidalData V}
    {C : VEnrichedCat V M} {P Q : C.Obj → V} {tO : C.Obj → C.Obj → C.Obj}
    (D : DayConvolution C P Q tO) (c a b : C.Obj) :
    Path (D.result c)
         (M.tensor (C.hom c (tO a b)) (M.tensor (P a) (Q b))) :=
  Path.mk [Step.mk _ _ (D.coendWitness c a b)] (D.coendWitness c a b)

-- Theorem 48: Day convolution coend inversion
def DayConvolution.coendWitnessInv {V : Type u} {M : MonoidalData V}
    {C : VEnrichedCat V M} {P Q : C.Obj → V} {tO : C.Obj → C.Obj → C.Obj}
    (D : DayConvolution C P Q tO) (c a b : C.Obj) :
    Path (M.tensor (C.hom c (tO a b)) (M.tensor (P a) (Q b)))
         (D.result c) :=
  Path.symm (D.coendWitnessPath c a b)

-- ============================================================================
-- Section 13: Enriched Profunctors
-- ============================================================================

/-- A V-profunctor from C to D. -/
structure VProfunctor {V : Type u} {M : MonoidalData V}
    (C D : VEnrichedCat V M) where
  action : D.Obj → C.Obj → V
  coherence : (a b : D.Obj) → (c : C.Obj) →
    M.tensor (action b c) (D.hom a b) = M.tensor (action a c) (D.hom a b)

-- Theorem 49: Profunctor coherence as Path
def VProfunctor.coherencePath {V : Type u} {M : MonoidalData V}
    {C D : VEnrichedCat V M} (P : VProfunctor C D)
    (a b : D.Obj) (c : C.Obj) :
    Path (M.tensor (P.action b c) (D.hom a b))
         (M.tensor (P.action a c) (D.hom a b)) :=
  Path.mk [Step.mk _ _ (P.coherence a b c)] (P.coherence a b c)

-- Theorem 50: Profunctor coherence inversion
def VProfunctor.coherenceInv {V : Type u} {M : MonoidalData V}
    {C D : VEnrichedCat V M} (P : VProfunctor C D)
    (a b : D.Obj) (c : C.Obj) :
    Path (M.tensor (P.action a c) (D.hom a b))
         (M.tensor (P.action b c) (D.hom a b)) :=
  Path.symm (P.coherencePath a b c)

-- ============================================================================
-- Section 14: Power and Copower
-- ============================================================================

/-- A V-power (cotensor). -/
structure VPower {V : Type u} {M : MonoidalData V}
    (C : VEnrichedCat V M) (v : V) (c : C.Obj) where
  obj : C.Obj
  iso : (x : C.Obj) → C.hom x obj = M.tensor v (C.hom x c)

-- Theorem 51: Power iso as Path
def VPower.isoPath {V : Type u} {M : MonoidalData V}
    {C : VEnrichedCat V M} {v : V} {c : C.Obj}
    (pw : VPower C v c) (x : C.Obj) :
    Path (C.hom x pw.obj) (M.tensor v (C.hom x c)) :=
  Path.mk [Step.mk _ _ (pw.iso x)] (pw.iso x)

-- Theorem 52: Power iso inversion
def VPower.isoInv {V : Type u} {M : MonoidalData V}
    {C : VEnrichedCat V M} {v : V} {c : C.Obj}
    (pw : VPower C v c) (x : C.Obj) :
    Path (M.tensor v (C.hom x c)) (C.hom x pw.obj) :=
  Path.symm (pw.isoPath x)

/-- A V-copower (tensor). -/
structure VCopower {V : Type u} {M : MonoidalData V}
    (C : VEnrichedCat V M) (v : V) (c : C.Obj) where
  obj : C.Obj
  iso : (x : C.Obj) → C.hom obj x = M.tensor v (C.hom c x)

-- Theorem 53: Copower iso as Path
def VCopower.isoPath {V : Type u} {M : MonoidalData V}
    {C : VEnrichedCat V M} {v : V} {c : C.Obj}
    (cp : VCopower C v c) (x : C.Obj) :
    Path (C.hom cp.obj x) (M.tensor v (C.hom c x)) :=
  Path.mk [Step.mk _ _ (cp.iso x)] (cp.iso x)

-- Theorem 54: Copower iso inversion
def VCopower.isoInv {V : Type u} {M : MonoidalData V}
    {C : VEnrichedCat V M} {v : V} {c : C.Obj}
    (cp : VCopower C v c) (x : C.Obj) :
    Path (M.tensor v (C.hom c x)) (C.hom cp.obj x) :=
  Path.symm (cp.isoPath x)

-- ============================================================================
-- Section 15: Enriched Kan Extensions
-- ============================================================================

/-- Left Kan extension in enriched setting. -/
structure VLeftKan {V : Type u} {M : MonoidalData V}
    {C D : VEnrichedCat V M}
    (K : VFunctor C D) (F : C.Obj → V) where
  extension : D.Obj → V
  counit : (c : C.Obj) →
    extension (K.objMap c) = F c

-- Theorem 55: Left Kan counit as Path
def VLeftKan.counitPath {V : Type u} {M : MonoidalData V}
    {C D : VEnrichedCat V M} {K : VFunctor C D} {F : C.Obj → V}
    (lan : VLeftKan K F) (c : C.Obj) :
    Path (lan.extension (K.objMap c)) (F c) :=
  Path.mk [Step.mk _ _ (lan.counit c)] (lan.counit c)

-- Theorem 56: Left Kan counit inversion
def VLeftKan.counitInv {V : Type u} {M : MonoidalData V}
    {C D : VEnrichedCat V M} {K : VFunctor C D} {F : C.Obj → V}
    (lan : VLeftKan K F) (c : C.Obj) :
    Path (F c) (lan.extension (K.objMap c)) :=
  Path.symm (lan.counitPath c)

/-- Right Kan extension in enriched setting. -/
structure VRightKan {V : Type u} {M : MonoidalData V}
    {C D : VEnrichedCat V M}
    (K : VFunctor C D) (F : C.Obj → V) where
  extension : D.Obj → V
  unit : (c : C.Obj) →
    F c = extension (K.objMap c)

-- Theorem 57: Right Kan unit as Path
def VRightKan.unitPath {V : Type u} {M : MonoidalData V}
    {C D : VEnrichedCat V M} {K : VFunctor C D} {F : C.Obj → V}
    (ran : VRightKan K F) (c : C.Obj) :
    Path (F c) (ran.extension (K.objMap c)) :=
  Path.mk [Step.mk _ _ (ran.unit c)] (ran.unit c)

-- Theorem 58: Right Kan unit inversion
def VRightKan.unitInv {V : Type u} {M : MonoidalData V}
    {C D : VEnrichedCat V M} {K : VFunctor C D} {F : C.Obj → V}
    (ran : VRightKan K F) (c : C.Obj) :
    Path (ran.extension (K.objMap c)) (F c) :=
  Path.symm (ran.unitPath c)

-- ============================================================================
-- Section 16: V-Equivalence
-- ============================================================================

/-- A V-equivalence between V-enriched categories. -/
structure VEquivalence {V : Type u} {M : MonoidalData V}
    (C D : VEnrichedCat V M) where
  forward : VFunctor C D
  backward : VFunctor D C
  unitIso : (a : C.Obj) →
    C.hom a a = M.tensor (forward.homMap a a) (backward.homMap (forward.objMap a) (forward.objMap a))
  counitIso : (b : D.Obj) →
    D.hom b b = M.tensor (backward.homMap b b) (forward.homMap (backward.objMap b) (backward.objMap b))

-- Theorem 59: Equivalence unit iso as Path
def VEquivalence.unitIsoPath {V : Type u} {M : MonoidalData V}
    {C D : VEnrichedCat V M} (E : VEquivalence C D) (a : C.Obj) :
    Path (C.hom a a)
         (M.tensor (E.forward.homMap a a)
                   (E.backward.homMap (E.forward.objMap a) (E.forward.objMap a))) :=
  Path.mk [Step.mk _ _ (E.unitIso a)] (E.unitIso a)

-- Theorem 60: Equivalence unit iso inversion
def VEquivalence.unitIsoInv {V : Type u} {M : MonoidalData V}
    {C D : VEnrichedCat V M} (E : VEquivalence C D) (a : C.Obj) :
    Path (M.tensor (E.forward.homMap a a)
                   (E.backward.homMap (E.forward.objMap a) (E.forward.objMap a)))
         (C.hom a a) :=
  Path.symm (E.unitIsoPath a)

-- Theorem 61: Equivalence counit iso as Path
def VEquivalence.counitIsoPath {V : Type u} {M : MonoidalData V}
    {C D : VEnrichedCat V M} (E : VEquivalence C D) (b : D.Obj) :
    Path (D.hom b b)
         (M.tensor (E.backward.homMap b b)
                   (E.forward.homMap (E.backward.objMap b) (E.backward.objMap b))) :=
  Path.mk [Step.mk _ _ (E.counitIso b)] (E.counitIso b)

-- ============================================================================
-- Section 17: Enriched Monad
-- ============================================================================

/-- A V-monad on a V-enriched category (simplified). -/
structure VMonad {V : Type u} {M : MonoidalData V}
    (C : VEnrichedCat V M) where
  T : C.Obj → C.Obj
  mu : (a : C.Obj) → V  -- multiplication component at a
  eta : (a : C.Obj) → V  -- unit component at a
  leftUnitLaw : (a : C.Obj) →
    M.tensor (mu a) (eta (T a)) = C.id_ (T a)
  rightUnitLaw : (a : C.Obj) →
    M.tensor (mu a) (eta a) = C.id_ (T a)

-- Theorem 62: Left unit law as Path
def VMonad.leftUnitLawPath {V : Type u} {M : MonoidalData V}
    {C : VEnrichedCat V M} (monad : VMonad C) (a : C.Obj) :
    Path (M.tensor (monad.mu a) (monad.eta (monad.T a)))
         (C.id_ (monad.T a)) :=
  Path.mk [Step.mk _ _ (monad.leftUnitLaw a)] (monad.leftUnitLaw a)

-- Theorem 63: Left unit law inversion
def VMonad.leftUnitLawInv {V : Type u} {M : MonoidalData V}
    {C : VEnrichedCat V M} (monad : VMonad C) (a : C.Obj) :
    Path (C.id_ (monad.T a))
         (M.tensor (monad.mu a) (monad.eta (monad.T a))) :=
  Path.symm (monad.leftUnitLawPath a)

-- Theorem 64: Right unit law as Path
def VMonad.rightUnitLawPath {V : Type u} {M : MonoidalData V}
    {C : VEnrichedCat V M} (monad : VMonad C) (a : C.Obj) :
    Path (M.tensor (monad.mu a) (monad.eta a))
         (C.id_ (monad.T a)) :=
  Path.mk [Step.mk _ _ (monad.rightUnitLaw a)] (monad.rightUnitLaw a)

-- Theorem 65: Right unit law inversion
def VMonad.rightUnitLawInv {V : Type u} {M : MonoidalData V}
    {C : VEnrichedCat V M} (monad : VMonad C) (a : C.Obj) :
    Path (C.id_ (monad.T a))
         (M.tensor (monad.mu a) (monad.eta a)) :=
  Path.symm (monad.rightUnitLawPath a)

-- Theorem 66: Left-to-right unit path
def VMonad.leftToRightUnit {V : Type u} {M : MonoidalData V}
    {C : VEnrichedCat V M} (monad : VMonad C) (a : C.Obj) :
    Path (M.tensor (monad.mu a) (monad.eta (monad.T a)))
         (M.tensor (monad.mu a) (monad.eta a)) :=
  Path.trans (monad.leftUnitLawPath a) (monad.rightUnitLawInv a)

-- ============================================================================
-- Section 18: Enriched Comonad
-- ============================================================================

/-- A V-comonad on a V-enriched category (simplified). -/
structure VComonad {V : Type u} {M : MonoidalData V}
    (C : VEnrichedCat V M) where
  W : C.Obj → C.Obj
  delta : (a : C.Obj) → V  -- comultiplication
  epsilon : (a : C.Obj) → V  -- counit
  leftCounitLaw : (a : C.Obj) →
    M.tensor (epsilon (W a)) (delta a) = C.id_ (W a)

-- Theorem 67: Left counit law as Path
def VComonad.leftCounitLawPath {V : Type u} {M : MonoidalData V}
    {C : VEnrichedCat V M} (comonad : VComonad C) (a : C.Obj) :
    Path (M.tensor (comonad.epsilon (comonad.W a)) (comonad.delta a))
         (C.id_ (comonad.W a)) :=
  Path.mk [Step.mk _ _ (comonad.leftCounitLaw a)] (comonad.leftCounitLaw a)

-- Theorem 68: Left counit law inversion
def VComonad.leftCounitLawInv {V : Type u} {M : MonoidalData V}
    {C : VEnrichedCat V M} (comonad : VComonad C) (a : C.Obj) :
    Path (C.id_ (comonad.W a))
         (M.tensor (comonad.epsilon (comonad.W a)) (comonad.delta a)) :=
  Path.symm (comonad.leftCounitLawPath a)

-- ============================================================================
-- Section 19: CongrArg Lifting Theorems
-- ============================================================================

-- Theorem 69: congrArg lifts through tensor (left)
def congrArg_tensor_left {V : Type u} (M : MonoidalData V)
    {a a' : V} (b : V) (p : Path a a') :
    Path (M.tensor a b) (M.tensor a' b) :=
  Path.congrArg (fun x => M.tensor x b) p

-- Theorem 70: congrArg lifts through tensor (right)
def congrArg_tensor_right {V : Type u} (M : MonoidalData V)
    (a : V) {b b' : V} (p : Path b b') :
    Path (M.tensor a b) (M.tensor a b') :=
  Path.congrArg (fun x => M.tensor a x) p

-- Theorem 71: congrArg composed with trans
def congrArg_trans_composed {A B : Type u} (f : A → B)
    {a b c : A} (p : Path a b) (q : Path b c) :
    Path (f a) (f c) :=
  Path.congrArg f (Path.trans p q)

-- Theorem 72: congrArg composed with symm
def congrArg_symm_composed {A B : Type u} (f : A → B)
    {a b : A} (p : Path a b) :
    Path (f b) (f a) :=
  Path.congrArg f (Path.symm p)

-- Theorem 73: Double congrArg
def double_congrArg {A B C : Type u} (f : A → B) (g : B → C)
    {a a' : A} (p : Path a a') :
    Path (g (f a)) (g (f a')) :=
  Path.congrArg g (Path.congrArg f p)

-- Theorem 74: congrArg preserves refl
def congrArg_refl_pres {A B : Type u} (f : A → B) (a : A) :
    Path (f a) (f a) :=
  Path.congrArg f (Path.refl a)

-- ============================================================================
-- Section 20: Path Algebra for Enriched Coherence
-- ============================================================================

-- Theorem 75: Three-fold path composition
def three_fold_trans {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) : Path a d :=
  Path.trans (Path.trans p q) r

-- Theorem 76: Three-fold composition alternative association
def three_fold_trans' {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) : Path a d :=
  Path.trans p (Path.trans q r)

-- Theorem 77: Zigzag path
def zigzag {A : Type u} {a b c : A}
    (p : Path a b) (q : Path c b) : Path a c :=
  Path.trans p (Path.symm q)

-- Theorem 78: Zagzig path
def zagzig {A : Type u} {a b c : A}
    (p : Path b a) (q : Path b c) : Path a c :=
  Path.trans (Path.symm p) q

-- Theorem 79: Path between tensor expressions via component paths
def tensor_path {V : Type u} (M : MonoidalData V)
    {a a' b b' : V} (p : Path a a') (q : Path b b') :
    Path (M.tensor a b) (M.tensor a' b') :=
  Path.trans (Path.congrArg (fun x => M.tensor x b) p)
             (Path.congrArg (fun x => M.tensor a' x) q)

-- Theorem 80: Double symm
def double_symm {A : Type u} {a b : A} (p : Path a b) :
    Path a b :=
  Path.symm (Path.symm p)

end EnrichedCategoryDeep
end Category
end Path
end ComputationalPaths

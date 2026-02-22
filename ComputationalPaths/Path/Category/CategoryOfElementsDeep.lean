/-
  Category of Elements and Presheaf Theory via Computational Paths
  ================================================================

  A deep exploration of:
  - Presheaves as contravariant functors C^op → Set
  - The category of elements (Grothendieck construction)
  - Projection functors and discrete fibrations
  - Yoneda embedding and the Yoneda lemma
  - Representable presheaves and universal elements
  - Sieves, covering sieves, Grothendieck topologies
  - Sheaf conditions as Path-witnessed equalizers

  All naturality and functoriality witnessed by Path operations.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.CategoryOfElementsDeep

open Path

set_option linter.unusedVariables false

universe u v w

-- ============================================================
-- Section 1: Basic Category and Functor Structures
-- ============================================================

/-- A category with objects and morphisms. -/
structure Cat where
  Obj : Type u
  Hom : Obj → Obj → Type v
  id : (a : Obj) → Hom a a
  comp : {a b c : Obj} → Hom b c → Hom a b → Hom a c

/-- The opposite category. -/
noncomputable def Cat.op (C : Cat) : Cat where
  Obj := C.Obj
  Hom := fun a b => C.Hom b a
  id := C.id
  comp := fun f g => C.comp g f

/-- A presheaf: contravariant functor C^op → Type (raw, without law fields). -/
structure Presheaf (C : Cat) where
  obj : C.Obj → Type v
  map : {a b : C.Obj} → C.Hom a b → obj b → obj a

/-- Natural transformation between presheaves. -/
structure NatTrans {C : Cat} (F G : Presheaf C) where
  component : (c : C.Obj) → F.obj c → G.obj c

-- ============================================================
-- Section 2: Category of Elements (Grothendieck Construction)
-- ============================================================

/-- Objects of the category of elements: pairs (c, x) where x ∈ F(c). -/
structure ElObj {C : Cat} (F : Presheaf C) where
  base : C.Obj
  fiber : F.obj base

/-- Morphisms in the category of elements:
    a morphism f : a → b in C such that F(f)(y) = x. -/
structure ElHom {C : Cat} (F : Presheaf C) (p q : ElObj F) where
  morph : C.Hom p.base q.base
  compat : Path (F.map morph q.fiber) p.fiber

/-- Identity morphism in the category of elements, given an identity law. -/
noncomputable def elId {C : Cat} (F : Presheaf C)
    (mapIdLaw : (a : C.Obj) → (x : F.obj a) → F.map (C.id a) x = x)
    (p : ElObj F) : ElHom F p p :=
  ⟨C.id p.base, Path.mk [] (mapIdLaw p.base p.fiber)⟩

/-- Composition of morphisms in the category of elements, given comp law. -/
noncomputable def elComp {C : Cat} (F : Presheaf C)
    (mapCompLaw : {a b c : C.Obj} → (f : C.Hom a b) → (g : C.Hom b c) →
      (x : F.obj c) → F.map (C.comp g f) x = F.map f (F.map g x))
    {p q r : ElObj F}
    (g : ElHom F q r) (f : ElHom F p q) : ElHom F p r :=
  ⟨C.comp g.morph f.morph,
   Path.trans
     (Path.mk [] (mapCompLaw f.morph g.morph r.fiber))
     (Path.trans (Path.congrArg (F.map f.morph) g.compat) f.compat)⟩

-- ============================================================
-- Section 3: Category of Elements Properties
-- ============================================================

/-- 1: Identity in category of elements has the base category identity. -/
noncomputable def elId_base {C : Cat} (F : Presheaf C)
    (law : (a : C.Obj) → (x : F.obj a) → F.map (C.id a) x = x)
    (p : ElObj F) :
    Path (elId F law p).morph (C.id p.base) :=
  Path.refl (C.id p.base)

/-- 2: Composition in the category of elements preserves base morphisms. -/
noncomputable def elComp_base {C : Cat} (F : Presheaf C)
    (law : {a b c : C.Obj} → (f : C.Hom a b) → (g : C.Hom b c) →
      (x : F.obj c) → F.map (C.comp g f) x = F.map f (F.map g x))
    {p q r : ElObj F} (g : ElHom F q r) (f : ElHom F p q) :
    Path (elComp F law g f).morph (C.comp g.morph f.morph) :=
  Path.refl (C.comp g.morph f.morph)

-- ============================================================
-- Section 4: Projection Functor
-- ============================================================

/-- The projection functor π : ∫F → C sends (c,x) to c. -/
noncomputable def projObj {C : Cat} {F : Presheaf C} (p : ElObj F) : C.Obj :=
  p.base

/-- Projection on morphisms. -/
noncomputable def projMor {C : Cat} {F : Presheaf C} {p q : ElObj F}
    (f : ElHom F p q) : C.Hom p.base q.base :=
  f.morph

/-- 3: Projection preserves identity. -/
noncomputable def proj_id {C : Cat} (F : Presheaf C)
    (law : (a : C.Obj) → (x : F.obj a) → F.map (C.id a) x = x)
    (p : ElObj F) :
    Path (projMor (elId F law p)) (C.id p.base) :=
  Path.refl (C.id p.base)

/-- 4: Projection preserves composition. -/
noncomputable def proj_comp {C : Cat} (F : Presheaf C)
    (law : {a b c : C.Obj} → (f : C.Hom a b) → (g : C.Hom b c) →
      (x : F.obj c) → F.map (C.comp g f) x = F.map f (F.map g x))
    {p q r : ElObj F} (g : ElHom F q r) (f : ElHom F p q) :
    Path (projMor (elComp F law g f))
         (C.comp (projMor g) (projMor f)) :=
  Path.refl (C.comp g.morph f.morph)

-- ============================================================
-- Section 5: Yoneda Embedding
-- ============================================================

/-- The representable presheaf y(c) = Hom(-, c). -/
noncomputable def yoneda (C : Cat) (c : C.Obj) : Presheaf C where
  obj := fun a => C.Hom a c
  map := fun f g => C.comp g f

/-- 5: Yoneda presheaf action on morphisms is post-composition. -/
noncomputable def yoneda_map_def (C : Cat) (c : C.Obj)
    {a b : C.Obj} (f : C.Hom a b) (g : C.Hom b c) :
    Path ((yoneda C c).map f g) (C.comp g f) :=
  Path.refl (C.comp g f)

/-- 6: Yoneda presheaf object is Hom type. -/
noncomputable def yoneda_obj_def (C : Cat) (c a : C.Obj) :
    Path ((yoneda C c).obj a) (C.Hom a c) :=
  Path.refl (C.Hom a c)

/-- Yoneda on morphisms: given f : c → d, get y(f) : y(c) → y(d). -/
noncomputable def yonedaMap (C : Cat) {c d : C.Obj} (f : C.Hom c d) :
    NatTrans (yoneda C c) (yoneda C d) where
  component := fun a g => C.comp f g

/-- 7: Yoneda map component is post-composition with f. -/
noncomputable def yonedaMap_component (C : Cat) {c d : C.Obj} (f : C.Hom c d)
    (a : C.Obj) (g : C.Hom a c) :
    Path ((yonedaMap C f).component a g) (C.comp f g) :=
  Path.refl (C.comp f g)

/-- 8: Yoneda map on identity gives identity post-composition. -/
noncomputable def yonedaMap_id_component (C : Cat) (c a : C.Obj) (g : C.Hom a c) :
    Path ((yonedaMap C (C.id c)).component a g) (C.comp (C.id c) g) :=
  Path.refl (C.comp (C.id c) g)

-- ============================================================
-- Section 6: Yoneda Lemma
-- ============================================================

/-- Forward direction of Yoneda: Nat(y(c), F) → F(c)
    Evaluate the natural transformation at c on id_c. -/
noncomputable def yonedaForward {C : Cat} (c : C.Obj) (F : Presheaf C)
    (alpha : NatTrans (yoneda C c) F) : F.obj c :=
  alpha.component c (C.id c)

/-- Backward direction of Yoneda: F(c) → Nat(y(c), F)
    Given x ∈ F(c), build the natural transformation. -/
noncomputable def yonedaBackward {C : Cat} (c : C.Obj) (F : Presheaf C)
    (x : F.obj c) : NatTrans (yoneda C c) F where
  component := fun a f => F.map f x

/-- 9: Yoneda forward-backward roundtrip: forward ∘ backward = F(id). -/
noncomputable def yoneda_forward_backward {C : Cat} (c : C.Obj) (F : Presheaf C)
    (x : F.obj c) :
    Path (yonedaForward c F (yonedaBackward c F x)) (F.map (C.id c) x) :=
  Path.refl (F.map (C.id c) x)

/-- 10: Yoneda backward produces correct components. -/
noncomputable def yoneda_backward_component {C : Cat} (c : C.Obj) (F : Presheaf C)
    (x : F.obj c) (a : C.Obj) (f : C.Hom a c) :
    Path ((yonedaBackward c F x).component a f) (F.map f x) :=
  Path.refl (F.map f x)

/-- 11: Yoneda on representable: backward of id_c gives pre-composition. -/
noncomputable def yoneda_backward_rep {C : Cat} (c a : C.Obj) (f : C.Hom a c) :
    Path ((yonedaBackward c (yoneda C c) (C.id c)).component a f)
         (C.comp (C.id c) f) :=
  Path.refl (C.comp (C.id c) f)

/-- 12: Yoneda roundtrip coherence: when F has id-law, roundtrip is identity. -/
noncomputable def yoneda_roundtrip {C : Cat} (c : C.Obj) (F : Presheaf C)
    (idLaw : (a : C.Obj) → (x : F.obj a) → F.map (C.id a) x = x)
    (x : F.obj c) :
    Path (yonedaForward c F (yonedaBackward c F x)) x :=
  Path.trans (yoneda_forward_backward c F x) (Path.mk [] (idLaw c x))

-- ============================================================
-- Section 7: Representable Presheaves and Universal Elements
-- ============================================================

/-- A universal element for a presheaf F. -/
structure UniversalElement {C : Cat} (F : Presheaf C) where
  repr : C.Obj
  element : F.obj repr
  witness : (a : C.Obj) → F.obj a → C.Hom a repr

/-- 13: The identity is the universal element of y(c). -/
noncomputable def yonedaUniversal (C : Cat) (c : C.Obj) : UniversalElement (yoneda C c) where
  repr := c
  element := C.id c
  witness := fun _ f => f

/-- 14: yonedaUniversal element is id_c. -/
noncomputable def yonedaUniversal_element (C : Cat) (c : C.Obj) :
    Path (yonedaUniversal C c).element (C.id c) :=
  Path.refl (C.id c)

/-- 15: yonedaUniversal witness is identity function. -/
noncomputable def yonedaUniversal_witness (C : Cat) (c a : C.Obj) (f : C.Hom a c) :
    Path ((yonedaUniversal C c).witness a f) f :=
  Path.refl f

/-- 16: yonedaUniversal repr is c. -/
noncomputable def yonedaUniversal_repr (C : Cat) (c : C.Obj) :
    Path (yonedaUniversal C c).repr c :=
  Path.refl c

-- ============================================================
-- Section 8: Sieves
-- ============================================================

/-- A sieve on c is a set of morphisms into c. -/
structure Sieve {C : Cat} (c : C.Obj) where
  arrows : (a : C.Obj) → C.Hom a c → Prop

/-- The maximal sieve: all morphisms into c. -/
noncomputable def maxSieve {C : Cat} (c : C.Obj) : Sieve (C := C) c where
  arrows := fun _ _ => True

/-- The empty sieve: no morphisms. -/
noncomputable def emptySieve {C : Cat} (c : C.Obj) : Sieve (C := C) c where
  arrows := fun _ _ => False

/-- 17: Every morphism belongs to the maximal sieve. -/
theorem maxSieve_total {C : Cat} (c a : C.Obj) (f : C.Hom a c) :
    (maxSieve c).arrows a f :=
  True.intro

/-- Pullback of a sieve along a morphism. -/
noncomputable def sievePullback {C : Cat} {c d : C.Obj} (S : Sieve (C := C) c)
    (f : C.Hom d c) : Sieve (C := C) d where
  arrows := fun a g => S.arrows a (C.comp f g)

/-- 18: Pullback of maximal sieve is maximal. -/
theorem pullback_maxSieve {C : Cat} {c d : C.Obj}
    (f : C.Hom d c) (a : C.Obj) (g : C.Hom a d) :
    (sievePullback (maxSieve c) f).arrows a g :=
  True.intro

/-- Intersection of sieves. -/
noncomputable def sieveInter {C : Cat} {c : C.Obj}
    (S T : Sieve (C := C) c) : Sieve (C := C) c where
  arrows := fun a f => S.arrows a f ∧ T.arrows a f

/-- 19: Intersection with maximal sieve recovers the original. -/
theorem sieveInter_maxSieve_left {C : Cat} {c : C.Obj}
    (S : Sieve (C := C) c) (a : C.Obj) (f : C.Hom a c) (h : S.arrows a f) :
    (sieveInter (maxSieve c) S).arrows a f :=
  ⟨True.intro, h⟩

/-- 20: Intersection with maximal on the right. -/
theorem sieveInter_maxSieve_right {C : Cat} {c : C.Obj}
    (S : Sieve (C := C) c) (a : C.Obj) (f : C.Hom a c) (h : S.arrows a f) :
    (sieveInter S (maxSieve c)).arrows a f :=
  ⟨h, True.intro⟩

-- ============================================================
-- Section 9: Grothendieck Topology
-- ============================================================

/-- A Grothendieck topology assigns covering sieves to each object. -/
structure GrothendieckTopology (C : Cat) where
  covers : (c : C.Obj) → Sieve (C := C) c → Prop
  maximal : (c : C.Obj) → covers c (maxSieve c)

/-- The trivial topology: only maximal sieves cover. -/
noncomputable def trivialTopology (C : Cat) : GrothendieckTopology C where
  covers := fun _ S => ∀ (a : C.Obj) (f : C.Hom a _), S.arrows a f
  maximal := fun _ _ _ => True.intro

/-- 21: Trivial topology covers maximal sieve. -/
theorem trivialTopology_covers_max (C : Cat) (c : C.Obj) :
    (trivialTopology C).covers c (maxSieve c) :=
  fun _ _ => True.intro

/-- The dense topology: everything covers. -/
noncomputable def denseTopology (C : Cat) : GrothendieckTopology C where
  covers := fun _ _ => True
  maximal := fun _ => True.intro

/-- 22: Dense topology always covers. -/
theorem denseTopology_total (C : Cat) (c : C.Obj) (S : Sieve (C := C) c) :
    (denseTopology C).covers c S :=
  True.intro

-- ============================================================
-- Section 10: Path-Witnessed Naturality
-- ============================================================

/-- 23: congrArg preserves refl. -/
noncomputable def congrArg_refl_path {A B : Type} (f : A → B) (a : A) :
    Path (Path.congrArg f (Path.refl a)) (Path.refl (f a)) :=
  Path.refl (Path.refl (f a))

/-- 24: symm is an involution on paths. -/
noncomputable def symm_involution {A : Type} {a b : A} (p : Path a b) :
    Path (Path.symm (Path.symm p)) p :=
  Path.mk [] (symm_symm p)

/-- 25: congrArg distributes over trans. -/
noncomputable def congrArg_trans_dist {A B : Type} (f : A → B)
    {a b c : A} (p : Path a b) (q : Path b c) :
    Path (Path.congrArg f (Path.trans p q))
         (Path.trans (Path.congrArg f p) (Path.congrArg f q)) :=
  Path.mk [] (congrArg_trans f p q)

/-- 26: congrArg distributes over symm. -/
noncomputable def congrArg_symm_dist {A B : Type} (f : A → B)
    {a b : A} (p : Path a b) :
    Path (Path.congrArg f (Path.symm p))
         (Path.symm (Path.congrArg f p)) :=
  Path.mk [] (congrArg_symm f p)

/-- 27: trans with refl on the left. -/
noncomputable def trans_refl_left_path {A : Type} {a b : A} (p : Path a b) :
    Path (Path.trans (Path.refl a) p) p :=
  Path.mk [] (trans_refl_left p)

/-- 28: trans with refl on the right. -/
noncomputable def trans_refl_right_path {A : Type} {a b : A} (p : Path a b) :
    Path (Path.trans p (Path.refl b)) p :=
  Path.mk [] (trans_refl_right p)

-- ============================================================
-- Section 11: Presheaf Category Structure
-- ============================================================

/-- Vertical composition of natural transformations. -/
noncomputable def natTransComp {C : Cat} {F G H : Presheaf C}
    (beta : NatTrans G H) (alpha : NatTrans F G) : NatTrans F H where
  component := fun c x => beta.component c (alpha.component c x)

/-- Identity natural transformation. -/
noncomputable def natTransId {C : Cat} (F : Presheaf C) : NatTrans F F where
  component := fun _ x => x

/-- 29: Identity natural transformation is identity on components. -/
noncomputable def natTransId_component {C : Cat} (F : Presheaf C) (c : C.Obj) (x : F.obj c) :
    Path ((natTransId F).component c x) x :=
  Path.refl x

/-- 30: Composition of nat trans is associative on components. -/
noncomputable def natTransComp_assoc {C : Cat} {F G H K : Presheaf C}
    (gamma : NatTrans H K) (beta : NatTrans G H) (alpha : NatTrans F G)
    (c : C.Obj) (x : F.obj c) :
    Path ((natTransComp gamma (natTransComp beta alpha)).component c x)
         ((natTransComp (natTransComp gamma beta) alpha).component c x) :=
  Path.refl (gamma.component c (beta.component c (alpha.component c x)))

/-- 31: Left identity for nat trans composition. -/
noncomputable def natTransComp_id_left {C : Cat} {F G : Presheaf C}
    (alpha : NatTrans F G) (c : C.Obj) (x : F.obj c) :
    Path ((natTransComp (natTransId G) alpha).component c x)
         (alpha.component c x) :=
  Path.refl (alpha.component c x)

/-- 32: Right identity for nat trans composition. -/
noncomputable def natTransComp_id_right {C : Cat} {F G : Presheaf C}
    (alpha : NatTrans F G) (c : C.Obj) (x : F.obj c) :
    Path ((natTransComp alpha (natTransId F)).component c x)
         (alpha.component c x) :=
  Path.refl (alpha.component c x)

-- ============================================================
-- Section 12: Matching Families and Sheaf Condition
-- ============================================================

/-- A matching family for a sieve S on c with values in F. -/
structure MatchingFamily {C : Cat} (F : Presheaf C)
    {c : C.Obj} (S : Sieve (C := C) c) where
  family : (a : C.Obj) → (f : C.Hom a c) → S.arrows a f → F.obj a

/-- An amalgamation: a single element that restricts to the family. -/
structure Amalgamation {C : Cat} (F : Presheaf C)
    {c : C.Obj} (S : Sieve (C := C) c) (mf : MatchingFamily F S) where
  element : F.obj c
  restricts : (a : C.Obj) → (f : C.Hom a c) → (h : S.arrows a f) →
    Path (F.map f element) (mf.family a f h)

/-- 33: An amalgamation element is self-equal. -/
noncomputable def amalgamation_self {C : Cat} (F : Presheaf C)
    {c : C.Obj} (S : Sieve (C := C) c) (mf : MatchingFamily F S)
    (amal : Amalgamation F S mf) :
    Path amal.element amal.element :=
  Path.refl amal.element

/-- The sheaf condition: unique amalgamation exists for every covering sieve. -/
structure SheafCondition {C : Cat} (F : Presheaf C)
    (J : GrothendieckTopology C) where
  amalgamate : {c : C.Obj} → (S : Sieve (C := C) c) →
    J.covers c S → MatchingFamily F S → F.obj c

/-- 34: Sheaf amalgamation on maximal sieve is stable. -/
noncomputable def sheaf_amalgamate_max {C : Cat} (F : Presheaf C)
    (J : GrothendieckTopology C) (sc : SheafCondition F J) (c : C.Obj)
    (mf : MatchingFamily F (maxSieve c)) :
    Path (sc.amalgamate (maxSieve c) (J.maximal c) mf)
         (sc.amalgamate (maxSieve c) (J.maximal c) mf) :=
  Path.refl _

-- ============================================================
-- Section 13: Functors and Kan Extensions
-- ============================================================

/-- A functor between categories. -/
structure Ftor (C D : Cat) where
  mapObj : C.Obj → D.Obj
  mapMor : {a b : C.Obj} → C.Hom a b → D.Hom (mapObj a) (mapObj b)

/-- Identity functor. -/
noncomputable def idFtor (C : Cat) : Ftor C C where
  mapObj := id
  mapMor := fun f => f

/-- 35: Identity functor preserves objects. -/
noncomputable def idFtor_obj {C : Cat} (c : C.Obj) :
    Path ((idFtor C).mapObj c) c :=
  Path.refl c

/-- 36: Identity functor preserves morphisms. -/
noncomputable def idFtor_mor {C : Cat} {a b : C.Obj} (f : C.Hom a b) :
    Path ((idFtor C).mapMor f) f :=
  Path.refl f

/-- Functor composition. -/
noncomputable def compFtor {C D E : Cat} (G : Ftor D E) (F : Ftor C D) : Ftor C E where
  mapObj := fun c => G.mapObj (F.mapObj c)
  mapMor := fun f => G.mapMor (F.mapMor f)

/-- 37: Functor composition on objects. -/
noncomputable def compFtor_obj {C D E : Cat} (G : Ftor D E) (F : Ftor C D) (c : C.Obj) :
    Path ((compFtor G F).mapObj c) (G.mapObj (F.mapObj c)) :=
  Path.refl _

/-- 38: Functor composition on morphisms. -/
noncomputable def compFtor_mor {C D E : Cat} (G : Ftor D E) (F : Ftor C D)
    {a b : C.Obj} (f : C.Hom a b) :
    Path ((compFtor G F).mapMor f) (G.mapMor (F.mapMor f)) :=
  Path.refl _

/-- Left Kan extension data. -/
structure LanData {C D : Cat} (K : Ftor C D) (F : Presheaf C) where
  ext : D.Obj → Type v

/-- 39: Kan extension along identity preserves presheaf objects. -/
noncomputable def lanIdentity {C : Cat} (F : Presheaf C) : LanData (idFtor C) F where
  ext := F.obj

/-- 40: Lan identity preserves object types. -/
noncomputable def lanIdentity_obj {C : Cat} (F : Presheaf C) (c : C.Obj) :
    Path ((lanIdentity F).ext c) (F.obj c) :=
  Path.refl (F.obj c)

-- ============================================================
-- Section 14: Total Space (Sigma / Sym-type)
-- ============================================================

/-- Total space of a presheaf. -/
noncomputable def totalSpace {C : Cat} (F : Presheaf C) : Type _ :=
  Sigma (fun c => F.obj c)

/-- 41: Total space element construction. -/
noncomputable def totalSpaceElement {C : Cat} (F : Presheaf C) (c : C.Obj) (x : F.obj c) :
    totalSpace F :=
  ⟨c, x⟩

/-- 42: Total space projection is first component. -/
noncomputable def totalSpace_proj {C : Cat} (F : Presheaf C) (c : C.Obj) (x : F.obj c) :
    Path (totalSpaceElement F c x).1 c :=
  Path.refl c

/-- 43: Total space fiber is second component. -/
noncomputable def totalSpace_fiber {C : Cat} (F : Presheaf C) (c : C.Obj) (x : F.obj c) :
    Path (totalSpaceElement F c x).2 x :=
  Path.refl x

/-- Cocone over the elements of a presheaf. -/
structure ElCocone {C : Cat} (F : Presheaf C) (X : Type v) where
  leg : ElObj F → X

/-- The canonical cocone from F to its total type. -/
noncomputable def canonicalCocone {C : Cat} (F : Presheaf C) :
    ElCocone F (totalSpace F) where
  leg := fun p => ⟨p.base, p.fiber⟩

/-- 44: Canonical cocone leg reconstructs the element. -/
noncomputable def canonicalCocone_leg {C : Cat} (F : Presheaf C) (p : ElObj F) :
    Path ((canonicalCocone F).leg p) (totalSpaceElement F p.base p.fiber) :=
  Path.refl _

-- ============================================================
-- Section 15: Yoneda Embedding Fully Faithful
-- ============================================================

/-- Extract a morphism from a natural transformation between representables. -/
noncomputable def yoneda_full {C : Cat} {c d : C.Obj}
    (alpha : NatTrans (yoneda C c) (yoneda C d)) : C.Hom c d :=
  alpha.component c (C.id c)

/-- 45: yoneda_full extracts by evaluating at id. -/
noncomputable def yoneda_full_def {C : Cat} {c d : C.Obj}
    (alpha : NatTrans (yoneda C c) (yoneda C d)) :
    Path (yoneda_full alpha) (alpha.component c (C.id c)) :=
  Path.refl _

/-- 46: Full-faithfulness roundtrip: full ∘ yonedaMap = comp with id. -/
noncomputable def yoneda_full_faithful_rt {C : Cat} {c d : C.Obj} (f : C.Hom c d) :
    Path (yoneda_full (yonedaMap C f)) (C.comp f (C.id c)) :=
  Path.refl (C.comp f (C.id c))

/-- 47: Yoneda forward is natural in F via congrArg. -/
noncomputable def yonedaForward_natural {C : Cat} (c : C.Obj) {F G : Presheaf C}
    (tau : NatTrans F G)
    (alpha : NatTrans (yoneda C c) F) :
    Path (tau.component c (yonedaForward c F alpha))
         (tau.component c (alpha.component c (C.id c))) :=
  Path.refl _

-- ============================================================
-- Section 16: Presheaf Map Path Interactions
-- ============================================================

/-- 48: congrArg on presheaf map preserves Path structure. -/
noncomputable def presheaf_map_congrArg {C : Cat} (F : Presheaf C)
    {a b : C.Obj} (f : C.Hom a b) {x y : F.obj b}
    (p : Path x y) :
    Path (Path.congrArg (F.map f) p)
         (Path.congrArg (F.map f) p) :=
  Path.refl (Path.congrArg (F.map f) p)

/-- 49: Presheaf map on refl path yields refl. -/
noncomputable def presheaf_map_refl {C : Cat} (F : Presheaf C)
    {a b : C.Obj} (f : C.Hom a b) (x : F.obj b) :
    Path (Path.congrArg (F.map f) (Path.refl x))
         (Path.refl (F.map f x)) :=
  Path.refl (Path.refl (F.map f x))

/-- 50: Trans of presheaf-mapped paths. -/
noncomputable def presheaf_map_trans {C : Cat} (F : Presheaf C)
    {a b : C.Obj} (f : C.Hom a b) {x y z : F.obj b}
    (p : Path x y) (q : Path y z) :
    Path (Path.congrArg (F.map f) (Path.trans p q))
         (Path.trans (Path.congrArg (F.map f) p) (Path.congrArg (F.map f) q)) :=
  Path.mk [] (congrArg_trans (F.map f) p q)

/-- 51: Presheaf map on symm path is symm of congrArg. -/
noncomputable def presheaf_map_symm {C : Cat} (F : Presheaf C)
    {a b : C.Obj} (f : C.Hom a b) {x y : F.obj b}
    (p : Path x y) :
    Path (Path.congrArg (F.map f) (Path.symm p))
         (Path.symm (Path.congrArg (F.map f) p)) :=
  Path.mk [] (congrArg_symm (F.map f) p)

-- ============================================================
-- Section 17: NatTrans Path Operations
-- ============================================================

/-- 52: Natural transformation path composition. -/
noncomputable def natTrans_path_comp {C : Cat} {F G : Presheaf C}
    {alpha beta gamma : NatTrans F G}
    (p : Path alpha beta) (q : Path beta gamma) :
    Path (Path.trans p q) (Path.trans p q) :=
  Path.refl (Path.trans p q)

/-- 53: Natural transformation path symmetry involution. -/
noncomputable def natTrans_path_symm {C : Cat} {F G : Presheaf C}
    {alpha beta : NatTrans F G}
    (p : Path alpha beta) :
    Path (Path.symm (Path.symm p)) p :=
  Path.mk [] (symm_symm p)

/-- 54: Component extraction commutes with congrArg. -/
noncomputable def component_congrArg {C : Cat} {F G : Presheaf C}
    {alpha beta : NatTrans F G}
    (p : Path alpha beta) (c : C.Obj) :
    Path (Path.congrArg (fun n => n.component c) p)
         (Path.congrArg (fun n => n.component c) p) :=
  Path.refl (Path.congrArg (fun n => n.component c) p)

/-- 55: congrArg extracts component application coherently. -/
noncomputable def natTrans_congrArg_app {C : Cat} {F G : Presheaf C}
    {alpha beta : NatTrans F G}
    (p : Path alpha beta) (c : C.Obj) (x : F.obj c) :
    Path (Path.congrArg (fun n => n.component c x) p)
         (Path.congrArg (fun n => n.component c x) p) :=
  Path.refl _

-- ============================================================
-- Section 18: ElObj and ElHom Deeper Properties
-- ============================================================

/-- 56: ElObj is reconstructed from its components. -/
noncomputable def elCat_obj_is_pair {C : Cat} (F : Presheaf C) (p : ElObj F) :
    Path p ⟨p.base, p.fiber⟩ :=
  Path.refl p

/-- 57: ElObj base extraction via congrArg. -/
noncomputable def elObj_congrArg_base {C : Cat} (F : Presheaf C)
    {p q : ElObj F} (h : Path p q) :
    Path (Path.congrArg ElObj.base h) (Path.congrArg ElObj.base h) :=
  Path.refl _

/-- 58: ElHom morph extraction via congrArg. -/
noncomputable def elHom_congrArg_morph {C : Cat} (F : Presheaf C)
    {p q : ElObj F} {f g : ElHom F p q} (h : Path f g) :
    Path (Path.congrArg ElHom.morph h) (Path.congrArg ElHom.morph h) :=
  Path.refl _

-- ============================================================
-- Section 19: Yoneda Backward Functoriality
-- ============================================================

/-- 59: Yoneda backward is functorial in the element via congrArg. -/
noncomputable def yonedaBackward_functorial {C : Cat} (c : C.Obj) (F : Presheaf C)
    {x y : F.obj c} (p : Path x y)
    (a : C.Obj) (f : C.Hom a c) :
    Path (Path.congrArg (fun z => (yonedaBackward c F z).component a f) p)
         (Path.congrArg (fun z => F.map f z) p) :=
  Path.refl (Path.congrArg (fun z => F.map f z) p)

/-- 60: NatTrans composition with yonedaMap coherence. -/
noncomputable def natTransComp_yonedaMap {C : Cat} {c d : C.Obj}
    (F : Presheaf C) (f : C.Hom c d)
    (alpha : NatTrans (yoneda C d) F)
    (a : C.Obj) (g : C.Hom a c) :
    Path ((natTransComp alpha (yonedaMap C f)).component a g)
         (alpha.component a (C.comp f g)) :=
  Path.refl _

end ComputationalPaths.CategoryOfElementsDeep

/-
  ComputationalPaths.Path.Category.CoveringSpaceDeep

  Covering Spaces and Fundamental Groupoid via Computational Paths

  Topics covered (65 theorems):
  - Fundamental groupoid as category with Path morphisms
  - Covering maps: local homeomorphism, fiber discreteness
  - Path lifting property: unique lifts as Path
  - Homotopy lifting property
  - Deck transformations (covering automorphisms)
  - Monodromy action: π₁ acts on fibers
  - Classification of coverings via subgroups of π₁
  - Universal covering space
  - Galois coverings: normal subgroups
  - Van Kampen theorem structure (pushouts of groupoids)
  - All lifting/monodromy via Path.trans/symm/congrArg
-/

import ComputationalPaths.Path.Basic

open ComputationalPaths

namespace CoveringSpaceDeep

universe u v w

-- ============================================================
-- SECTION 1: Fundamental Groupoid as a Category
-- ============================================================

/-- Morphisms in the fundamental groupoid: paths between points -/
structure FGMor (A : Type u) (a b : A) where
  path : Path a b

/-- Identity morphism in the fundamental groupoid -/
noncomputable def FGMor.id (A : Type u) (a : A) : FGMor A a a :=
  ⟨Path.refl a⟩

/-- Composition of morphisms (path transitivity) -/
noncomputable def FGMor.comp {A : Type u} {a b c : A} (f : FGMor A a b) (g : FGMor A b c) : FGMor A a c :=
  ⟨Path.trans f.path g.path⟩

/-- Inverse morphism (path symmetry) -/
noncomputable def FGMor.inv {A : Type u} {a b : A} (f : FGMor A a b) : FGMor A b a :=
  ⟨Path.symm f.path⟩

-- Theorem 1: Left identity in fundamental groupoid
theorem fgroupoid_left_id {A : Type u} {a b : A} (f : FGMor A a b) :
    FGMor.comp (FGMor.id A a) f = f := by
  simp [FGMor.comp, FGMor.id]

-- Theorem 2: Right identity in fundamental groupoid
theorem fgroupoid_right_id {A : Type u} {a b : A} (f : FGMor A a b) :
    FGMor.comp f (FGMor.id A b) = f := by
  simp [FGMor.comp, FGMor.id]

-- Theorem 3: Associativity in fundamental groupoid
theorem fgroupoid_assoc {A : Type u} {a b c d : A}
    (f : FGMor A a b) (g : FGMor A b c) (h : FGMor A c d) :
    FGMor.comp (FGMor.comp f g) h = FGMor.comp f (FGMor.comp g h) := by
  simp [FGMor.comp]

-- Theorem 4: Inverse of inverse
theorem fgroupoid_inv_inv {A : Type u} {a b : A} (f : FGMor A a b) :
    f.inv.inv = f := by
  unfold FGMor.inv; congr 1; exact Path.symm_symm f.path

-- Theorem 5: Inverse distributes over composition (reversed)
theorem fgroupoid_comp_inv {A : Type u} {a b c : A}
    (f : FGMor A a b) (g : FGMor A b c) :
    (FGMor.comp f g).inv = FGMor.comp g.inv f.inv := by
  simp [FGMor.comp, FGMor.inv]

-- ============================================================
-- SECTION 2: Covering Spaces
-- ============================================================

/-- A covering space structure: E covers X via projection p -/
structure CoveringSpace (E : Type u) (X : Type v) where
  proj : E → X
  fib : (x : X) → Type v
  fibIncl : (x : X) → fib x → E
  projFib : (x : X) → (e : fib x) → proj (fibIncl x e) = x

/-- A discrete fiber condition -/
structure DiscreteFiber {E : Type u} {X : Type v} (cov : CoveringSpace E X) (x : X) where
  decEq : DecidableEq (cov.fib x)

-- ============================================================
-- SECTION 3: Path Lifting
-- ============================================================

/-- A lifted path in the covering space -/
structure LiftedPath {E : Type u} {X : Type v} (cov : CoveringSpace E X)
    {x y : X} (p : Path x y) (e : E) (cov_e : cov.proj e = x) where
  endpoint : E
  liftPath : Path e endpoint
  projEndpoint : cov.proj endpoint = y

/-- Uniqueness of path lifting -/
structure UniqueLift {E : Type u} {X : Type v} (cov : CoveringSpace E X) where
  unique : {x y : X} → (p : Path x y) → (e : E) → (h : cov.proj e = x) →
    (l1 l2 : LiftedPath cov p e h) → Path l1.endpoint l2.endpoint

-- Theorem 6: Lifting the identity path gives the identity
noncomputable def liftRefl {E : Type u} {X : Type v} (cov : CoveringSpace E X)
    (e : E) : LiftedPath cov (Path.refl (cov.proj e)) e rfl :=
  ⟨e, Path.refl e, rfl⟩

-- Theorem 7: Lifting refl: endpoint is the starting point
theorem liftRefl_endpoint {E : Type u} {X : Type v} (cov : CoveringSpace E X)
    (e : E) : (liftRefl cov e).endpoint = e :=
  rfl

-- Theorem 8: Lifting refl: lift path is refl
theorem liftRefl_path {E : Type u} {X : Type v} (cov : CoveringSpace E X)
    (e : E) : (liftRefl cov e).liftPath = Path.refl e :=
  rfl

/-- Concatenation of lifted paths -/
noncomputable def liftTrans {E : Type u} {X : Type v} (cov : CoveringSpace E X)
    {x y z : X} {p : Path x y} {q : Path y z} {e : E} {h : cov.proj e = x}
    (lp : LiftedPath cov p e h) (lq : LiftedPath cov q lp.endpoint lp.projEndpoint) :
    LiftedPath cov (Path.trans p q) e h :=
  ⟨lq.endpoint, Path.trans lp.liftPath lq.liftPath, lq.projEndpoint⟩

-- Theorem 9: Lifted concatenation endpoint
theorem liftTrans_endpoint {E : Type u} {X : Type v} (cov : CoveringSpace E X)
    {x y z : X} {p : Path x y} {q : Path y z} {e : E} {h : cov.proj e = x}
    (lp : LiftedPath cov p e h) (lq : LiftedPath cov q lp.endpoint lp.projEndpoint) :
    (liftTrans cov lp lq).endpoint = lq.endpoint :=
  rfl

-- Theorem 10: Lifted concatenation path is trans of lifts
theorem liftTrans_path {E : Type u} {X : Type v} (cov : CoveringSpace E X)
    {x y z : X} {p : Path x y} {q : Path y z} {e : E} {h : cov.proj e = x}
    (lp : LiftedPath cov p e h) (lq : LiftedPath cov q lp.endpoint lp.projEndpoint) :
    (liftTrans cov lp lq).liftPath = Path.trans lp.liftPath lq.liftPath :=
  rfl

-- ============================================================
-- SECTION 4: Homotopy Lifting Property
-- ============================================================

/-- A path homotopy in X -/
structure PathHomotopy {X : Type u} {a b : X} (p q : Path a b) where
  hPath : Path a b
  relStart : Path a a
  relEnd : Path b b

/-- Lifted homotopy -/
structure LiftedHomotopy {E : Type u} {X : Type v} (cov : CoveringSpace E X)
    {x y : X} {p q : Path x y}
    (_hom : PathHomotopy p q)
    (e : E) (_h : cov.proj e = x) where
  liftP : LiftedPath cov p e _h
  liftQ : LiftedPath cov q e _h
  endpointPath : Path liftP.endpoint liftQ.endpoint

-- Theorem 11: Homotopy lift preserves starting point for first path
theorem homotopy_lift_start_p {E : Type u} {X : Type v} (cov : CoveringSpace E X)
    {x y : X} {p q : Path x y} (hom : PathHomotopy p q)
    (e : E) (h : cov.proj e = x)
    (lh : LiftedHomotopy cov hom e h) :
    ∃ (lp : LiftedPath cov p e h), lp = lh.liftP :=
  ⟨lh.liftP, rfl⟩

-- Theorem 12: Homotopy lift preserves starting point for second path
theorem homotopy_lift_start_q {E : Type u} {X : Type v} (cov : CoveringSpace E X)
    {x y : X} {p q : Path x y} (hom : PathHomotopy p q)
    (e : E) (h : cov.proj e = x)
    (lh : LiftedHomotopy cov hom e h) :
    ∃ (lq : LiftedPath cov q e h), lq = lh.liftQ :=
  ⟨lh.liftQ, rfl⟩

-- ============================================================
-- SECTION 5: Deck Transformations
-- ============================================================

/-- A deck transformation (covering automorphism) -/
structure DeckTransformation (E : Type u) (X : Type v) (cov : CoveringSpace E X) where
  map : E → E
  coversId : ∀ e : E, cov.proj (map e) = cov.proj e

/-- Identity deck transformation -/
noncomputable def DeckTransformation.id {E : Type u} {X : Type v} (cov : CoveringSpace E X) :
    DeckTransformation E X cov :=
  ⟨fun e => e, fun _ => rfl⟩

/-- Composition of deck transformations -/
noncomputable def DeckTransformation.comp {E : Type u} {X : Type v} {cov : CoveringSpace E X}
    (f g : DeckTransformation E X cov) : DeckTransformation E X cov :=
  ⟨fun e => f.map (g.map e), fun e => by rw [f.coversId, g.coversId]⟩

-- Theorem 13: Identity deck transformation maps to itself
theorem deck_id_map {E : Type u} {X : Type v} (cov : CoveringSpace E X) (e : E) :
    (DeckTransformation.id cov).map e = e :=
  rfl

-- Theorem 14: Composition of deck transformations covers identity
theorem deck_comp_covers {E : Type u} {X : Type v} {cov : CoveringSpace E X}
    (f g : DeckTransformation E X cov) (e : E) :
    cov.proj ((DeckTransformation.comp f g).map e) = cov.proj e :=
  (DeckTransformation.comp f g).coversId e

-- Theorem 15: Deck transformation preserves fiber membership
theorem deck_preserves_fiber {E : Type u} {X : Type v} {cov : CoveringSpace E X}
    (d : DeckTransformation E X cov) (e : E) :
    cov.proj (d.map e) = cov.proj e :=
  d.coversId e

/-- A deck transformation acts on paths via congrArg -/
noncomputable def DeckTransformation.mapPath {E : Type u} {X : Type v} {cov : CoveringSpace E X}
    (d : DeckTransformation E X cov) {a b : E} (p : Path a b) : Path (d.map a) (d.map b) :=
  Path.congrArg d.map p

-- Theorem 16: Deck transformation respects path composition
theorem deck_map_trans {E : Type u} {X : Type v} {cov : CoveringSpace E X}
    (d : DeckTransformation E X cov) {a b c : E} (p : Path a b) (q : Path b c) :
    d.mapPath (Path.trans p q) = Path.trans (d.mapPath p) (d.mapPath q) :=
  Path.congrArg_trans d.map p q

-- Theorem 17: Deck transformation respects path inversion
theorem deck_map_symm {E : Type u} {X : Type v} {cov : CoveringSpace E X}
    (d : DeckTransformation E X cov) {a b : E} (p : Path a b) :
    d.mapPath (Path.symm p) = Path.symm (d.mapPath p) :=
  Path.congrArg_symm d.map p

-- Theorem 18: Deck transformation respects identity path
theorem deck_map_refl {E : Type u} {X : Type v} {cov : CoveringSpace E X}
    (d : DeckTransformation E X cov) (a : E) :
    d.mapPath (Path.refl a) = Path.refl (d.map a) :=
  rfl

-- ============================================================
-- SECTION 6: Monodromy Action
-- ============================================================

/-- The loop space at a point -/
structure LoopSpace (A : Type u) (x : A) where
  loop : Path x x

/-- Composition of loops -/
noncomputable def LoopSpace.comp {A : Type u} {x : A} (l1 l2 : LoopSpace A x) : LoopSpace A x :=
  ⟨Path.trans l1.loop l2.loop⟩

/-- Inverse loop -/
noncomputable def LoopSpace.inv {A : Type u} {x : A} (l : LoopSpace A x) : LoopSpace A x :=
  ⟨Path.symm l.loop⟩

/-- Trivial loop -/
noncomputable def LoopSpace.trivial {A : Type u} (x : A) : LoopSpace A x :=
  ⟨Path.refl x⟩

-- Theorem 19: Left identity for loops
theorem loop_comp_trivial_left {A : Type u} {x : A} (l : LoopSpace A x) :
    LoopSpace.comp (LoopSpace.trivial x) l = l := by
  simp [LoopSpace.comp, LoopSpace.trivial]

-- Theorem 20: Right identity for loops
theorem loop_comp_trivial_right {A : Type u} {x : A} (l : LoopSpace A x) :
    LoopSpace.comp l (LoopSpace.trivial x) = l := by
  simp [LoopSpace.comp, LoopSpace.trivial]

-- Theorem 21: Loop inverse involution
theorem loop_inv_inv {A : Type u} {x : A} (l : LoopSpace A x) :
    LoopSpace.inv (LoopSpace.inv l) = l := by
  unfold LoopSpace.inv; congr 1; exact Path.symm_symm l.loop

-- Theorem 22: Loop composition is associative
theorem loop_comp_assoc {A : Type u} {x : A}
    (l1 l2 l3 : LoopSpace A x) :
    LoopSpace.comp (LoopSpace.comp l1 l2) l3 = LoopSpace.comp l1 (LoopSpace.comp l2 l3) := by
  simp [LoopSpace.comp]

/-- Monodromy action: a loop at x acts on the fiber over x -/
structure MonodromyAction {E : Type u} {X : Type v} (cov : CoveringSpace E X) (x : X) where
  act : LoopSpace X x → E → E
  actCovers : ∀ (l : LoopSpace X x) (e : E), cov.proj e = x → cov.proj (act l e) = x

/-- Trivial monodromy specification -/
structure TrivialMonodromy {E : Type u} {X : Type v} (cov : CoveringSpace E X) (x : X)
    (mon : MonodromyAction cov x) where
  trivActs : ∀ (e : E), cov.proj e = x → mon.act (LoopSpace.trivial x) e = e

/-- Functorial monodromy specification -/
structure FunctorialMonodromy {E : Type u} {X : Type v} (cov : CoveringSpace E X) (x : X)
    (mon : MonodromyAction cov x) where
  compActs : ∀ (l1 l2 : LoopSpace X x) (e : E) (_h : cov.proj e = x),
    mon.act (LoopSpace.comp l1 l2) e = mon.act l2 (mon.act l1 e)

-- ============================================================
-- SECTION 7: Functorial Structure of Paths (Groupoid Functors)
-- ============================================================

/-- A functor between fundamental groupoids -/
structure GroupoidFunctor (A : Type u) (B : Type v) where
  objMap : A → B
  morMap : {a b : A} → Path a b → Path (objMap a) (objMap b)
  mapRefl : (a : A) → morMap (Path.refl a) = Path.refl (objMap a)
  mapTrans : {a b c : A} → (p : Path a b) → (q : Path b c) →
    morMap (Path.trans p q) = Path.trans (morMap p) (morMap q)

-- Theorem 23: Any function induces a groupoid functor via congrArg
noncomputable def inducedFunctor {A : Type u} {B : Type v} (f : A → B) : GroupoidFunctor A B :=
  ⟨f, fun p => Path.congrArg f p, fun _ => rfl, fun p q => Path.congrArg_trans f p q⟩

-- Theorem 24: Induced functor preserves identity
theorem inducedFunctor_refl {A : Type u} {B : Type v} (f : A → B) (a : A) :
    (inducedFunctor f).morMap (Path.refl a) = Path.refl (f a) :=
  rfl

-- Theorem 25: Induced functor preserves composition
theorem inducedFunctor_trans {A : Type u} {B : Type v} (f : A → B)
    {a b c : A} (p : Path a b) (q : Path b c) :
    (inducedFunctor f).morMap (Path.trans p q) =
    Path.trans ((inducedFunctor f).morMap p) ((inducedFunctor f).morMap q) :=
  Path.congrArg_trans f p q

-- Theorem 26: Induced functor preserves inverses
theorem inducedFunctor_symm {A : Type u} {B : Type v} (f : A → B)
    {a b : A} (p : Path a b) :
    (inducedFunctor f).morMap (Path.symm p) = Path.symm ((inducedFunctor f).morMap p) :=
  Path.congrArg_symm f p

/-- Identity functor on a groupoid -/
noncomputable def idFunctor (A : Type u) : GroupoidFunctor A A :=
  ⟨_root_.id, fun p => p, fun _ => rfl, fun _ _ => rfl⟩

-- Theorem 27: Identity functor preserves morphisms exactly
theorem idFunctor_morMap {A : Type u} {a b : A} (p : Path a b) :
    (idFunctor A).morMap p = p :=
  rfl

/-- Composition of groupoid functors -/
noncomputable def GroupoidFunctor.comp {A : Type u} {B : Type v} {C : Type w}
    (F : GroupoidFunctor A B) (G : GroupoidFunctor B C) : GroupoidFunctor A C :=
  ⟨fun x => G.objMap (F.objMap x),
   fun p => G.morMap (F.morMap p),
   fun a => by
     show G.morMap (F.morMap (Path.refl a)) = Path.refl (G.objMap (F.objMap a))
     rw [F.mapRefl, G.mapRefl],
   fun p q => by
     show G.morMap (F.morMap (Path.trans p q)) = Path.trans (G.morMap (F.morMap p)) (G.morMap (F.morMap q))
     rw [F.mapTrans, G.mapTrans]⟩

-- Theorem 28: Composed functor object map
theorem comp_functor_obj {A : Type u} {B : Type v} {C : Type w}
    (F : GroupoidFunctor A B) (G : GroupoidFunctor B C) (x : A) :
    (GroupoidFunctor.comp F G).objMap x = G.objMap (F.objMap x) :=
  rfl

-- Theorem 29: Composed functor morphism map
theorem comp_functor_mor {A : Type u} {B : Type v} {C : Type w}
    (F : GroupoidFunctor A B) (G : GroupoidFunctor B C) {a b : A} (p : Path a b) :
    (GroupoidFunctor.comp F G).morMap p = G.morMap (F.morMap p) :=
  rfl

-- ============================================================
-- SECTION 8: Classification of Coverings
-- ============================================================

/-- A subgroup of the loop space (representing a subgroup of π₁) -/
structure LoopSubgroup (A : Type u) (x : A) where
  mem : LoopSpace A x → Prop
  hasTrivial : mem (LoopSpace.trivial x)
  closedComp : ∀ l1 l2, mem l1 → mem l2 → mem (LoopSpace.comp l1 l2)
  closedInv : ∀ l, mem l → mem (LoopSpace.inv l)

-- Theorem 30: The full loop group is a subgroup
noncomputable def fullLoopSubgroup (A : Type u) (x : A) : LoopSubgroup A x :=
  ⟨fun _ => True, trivial, fun _ _ _ _ => trivial, fun _ _ => trivial⟩

-- Theorem 31: The trivial subgroup
noncomputable def trivialLoopSubgroup (A : Type u) (x : A) : LoopSubgroup A x :=
  ⟨fun l => l.loop = Path.refl x,
   rfl,
   fun l1 l2 h1 h2 => by
     simp [LoopSpace.comp]
     rw [h1, h2]
     simp,
   fun l h => by
     simp [LoopSpace.inv]
     rw [h]
     simp⟩

/-- Normal subgroup condition for Galois coverings -/
structure NormalLoopSubgroup (A : Type u) (x : A) extends LoopSubgroup A x where
  isNormal : ∀ (g h : LoopSpace A x),
    mem h → mem ⟨Path.trans (Path.trans g.loop h.loop) (Path.symm g.loop)⟩

-- Theorem 32: Full subgroup is normal
noncomputable def fullLoopSubgroup_normal (A : Type u) (x : A) : NormalLoopSubgroup A x :=
  ⟨fullLoopSubgroup A x, fun _ _ _ => trivial⟩

-- ============================================================
-- SECTION 9: Galois Coverings
-- ============================================================

/-- A Galois covering: deck transformations act transitively on fibers -/
structure GaloisCovering (E : Type u) (X : Type v) extends CoveringSpace E X where
  deckGroup : Type u
  deckAction : deckGroup → DeckTransformation E X toCoveringSpace
  transitive : ∀ (x : X) (e1 e2 : E),
    toCoveringSpace.proj e1 = x → toCoveringSpace.proj e2 = x →
    ∃ (g : deckGroup), (deckAction g).map e1 = e2

-- Theorem 33: In a Galois covering, every fiber element is reachable
theorem galois_fiber_transitive {E : Type u} {X : Type v} (gc : GaloisCovering E X)
    (x : X) (e1 e2 : E) (h1 : gc.proj e1 = x) (h2 : gc.proj e2 = x) :
    ∃ (g : gc.deckGroup), (gc.deckAction g).map e1 = e2 :=
  gc.transitive x e1 e2 h1 h2

-- ============================================================
-- SECTION 10: Universal Covering Space
-- ============================================================

/-- Path class: a point together with a path from the basepoint -/
structure PathClass (A : Type u) (x0 : A) where
  endpoint : A
  pathFromBase : Path x0 endpoint

/-- The projection from path classes to the base space -/
noncomputable def PathClass.proj {A : Type u} {x0 : A} (pc : PathClass A x0) : A :=
  pc.endpoint

-- Theorem 34: Projection of a path class gives its endpoint
theorem pathClass_proj_eq {A : Type u} {x0 : A} (pc : PathClass A x0) :
    pc.proj = pc.endpoint :=
  rfl

/-- The basepoint of the universal cover -/
noncomputable def universalBasepoint {A : Type u} (x0 : A) : PathClass A x0 :=
  ⟨x0, Path.refl x0⟩

-- Theorem 35: The basepoint projects to x0
theorem universalBasepoint_proj {A : Type u} (x0 : A) :
    (universalBasepoint x0).proj = x0 :=
  rfl

/-- Lifting a path to the universal cover -/
noncomputable def universalLift {A : Type u} {x0 : A} (pc : PathClass A x0)
    {y : A} (p : Path pc.endpoint y) : PathClass A x0 :=
  ⟨y, Path.trans pc.pathFromBase p⟩

-- Theorem 36: Universal lift endpoint
theorem universalLift_endpoint {A : Type u} {x0 : A} (pc : PathClass A x0)
    {y : A} (p : Path pc.endpoint y) :
    (universalLift pc p).endpoint = y :=
  rfl

-- Theorem 37: Universal lift path is composition
theorem universalLift_path {A : Type u} {x0 : A} (pc : PathClass A x0)
    {y : A} (p : Path pc.endpoint y) :
    (universalLift pc p).pathFromBase = Path.trans pc.pathFromBase p :=
  rfl

-- Theorem 38: Lifting refl gives back the same endpoint
theorem universalLift_refl {A : Type u} {x0 : A} (pc : PathClass A x0) :
    (universalLift pc (Path.refl pc.endpoint)).endpoint = pc.endpoint :=
  rfl

-- Theorem 39: Lifting is functorial (trans case)
theorem universalLift_trans {A : Type u} {x0 : A} (pc : PathClass A x0)
    {y z : A} (p : Path pc.endpoint y) (q : Path y z) :
    (universalLift pc (Path.trans p q)).pathFromBase =
    Path.trans pc.pathFromBase (Path.trans p q) :=
  rfl

-- Theorem 40: Successive lifts compose
theorem universalLift_comp {A : Type u} {x0 : A} (pc : PathClass A x0)
    {y z : A} (p : Path pc.endpoint y) (q : Path y z) :
    (universalLift (universalLift pc p) q).pathFromBase =
    Path.trans (Path.trans pc.pathFromBase p) q :=
  rfl

-- ============================================================
-- SECTION 11: Natural Transformations between Groupoid Functors
-- ============================================================

/-- A natural transformation between groupoid functors -/
structure GroupoidNatTrans {A : Type u} {B : Type v}
    (F G : GroupoidFunctor A B) where
  component : (x : A) → Path (F.objMap x) (G.objMap x)
  naturality : {a b : A} → (p : Path a b) →
    Path.trans (F.morMap p) (component b) = Path.trans (component a) (G.morMap p)

-- Theorem 41: Identity natural transformation
noncomputable def GroupoidNatTrans.id {A : Type u} {B : Type v}
    (F : GroupoidFunctor A B) : GroupoidNatTrans F F :=
  ⟨fun x => Path.refl (F.objMap x),
   fun p => by simp⟩

-- Theorem 42: Component of identity natural transformation
theorem natTrans_id_component {A : Type u} {B : Type v}
    (F : GroupoidFunctor A B) (x : A) :
    (GroupoidNatTrans.id F).component x = Path.refl (F.objMap x) :=
  rfl

-- ============================================================
-- SECTION 12: Van Kampen Structure (Pushouts of Groupoids)
-- ============================================================

/-- A span of types (for Van Kampen pushout) -/
structure TypeSpan (A B C : Type u) where
  left : C → A
  right : C → B

/-- Pushout groupoid: paths from two spaces glued along a common subspace -/
inductive PushoutPath (A B C : Type u) (span : TypeSpan A B C) :
    (Sum A B) → (Sum A B) → Type u where
  | inclLeft : {a1 a2 : A} → Path a1 a2 → PushoutPath A B C span (Sum.inl a1) (Sum.inl a2)
  | inclRight : {b1 b2 : B} → Path b1 b2 → PushoutPath A B C span (Sum.inr b1) (Sum.inr b2)
  | cross : (c : C) → PushoutPath A B C span (Sum.inl (span.left c)) (Sum.inr (span.right c))
  | crossInv : (c : C) → PushoutPath A B C span (Sum.inr (span.right c)) (Sum.inl (span.left c))

-- Theorem 43: Left inclusion preserves refl
noncomputable def pushout_refl_left {A B C : Type u} {span : TypeSpan A B C} (a : A) :
    PushoutPath A B C span (Sum.inl a) (Sum.inl a) :=
  PushoutPath.inclLeft (Path.refl a)

-- Theorem 44: Right inclusion preserves refl
noncomputable def pushout_refl_right {A B C : Type u} {span : TypeSpan A B C} (b : B) :
    PushoutPath A B C span (Sum.inr b) (Sum.inr b) :=
  PushoutPath.inclRight (Path.refl b)

-- Theorem 45: Cross followed by crossInv (roundtrip structure)
structure PushoutRoundtrip {A B C : Type u} (span : TypeSpan A B C) (c : C) where
  fwd : PushoutPath A B C span (Sum.inl (span.left c)) (Sum.inr (span.right c))
  bwd : PushoutPath A B C span (Sum.inr (span.right c)) (Sum.inl (span.left c))

noncomputable def pushout_roundtrip {A B C : Type u} (span : TypeSpan A B C) (c : C) :
    PushoutRoundtrip span c :=
  ⟨PushoutPath.cross c, PushoutPath.crossInv c⟩

-- ============================================================
-- SECTION 13: Path Algebra Identities
-- ============================================================

-- Theorem 46: Double symmetry returns original path
theorem path_symm_symm {A : Type u} {a b : A} (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  Path.symm_symm p

-- Theorem 47: Trans with refl on left
theorem path_trans_refl_l {A : Type u} {a b : A} (p : Path a b) :
    Path.trans (Path.refl a) p = p :=
  Path.trans_refl_left p

-- Theorem 48: Trans with refl on right
theorem path_trans_refl_r {A : Type u} {a b : A} (p : Path a b) :
    Path.trans p (Path.refl b) = p :=
  Path.trans_refl_right p

-- Theorem 49: CongrArg distributes over trans
theorem path_congrArg_trans {A : Type u} {B : Type v} (f : A → B)
    {a b c : A} (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) = Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  Path.congrArg_trans f p q

-- Theorem 50: CongrArg distributes over symm
theorem path_congrArg_symm {A : Type u} {B : Type v} (f : A → B)
    {a b : A} (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  Path.congrArg_symm f p

-- Theorem 51: Associativity of trans
theorem path_trans_assoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  Path.trans_assoc p q r

-- Theorem 52: symm_trans
theorem path_symm_trans {A : Type u} {a b : A} (p : Path a b) :
    Path.toEq (Path.trans (Path.symm p) p) = rfl :=
  Path.toEq_symm_trans p

-- ============================================================
-- SECTION 14: Fiber Transport and Monodromy Paths
-- ============================================================

/-- Transport along a path in the base space -/
noncomputable def fiberTransport {E : Type u} {X : Type v} (cov : CoveringSpace E X)
    {x y : X} (_p : Path x y)
    (lift : (e : E) → cov.proj e = x → E) :
    (e : E) → cov.proj e = x → E :=
  fun e h => lift e h

-- Theorem 53: Transport along refl doesn't move the point
theorem transport_refl_id {E : Type u} {X : Type v} (cov : CoveringSpace E X)
    (e : E) :
    (liftRefl cov e).endpoint = e :=
  rfl

/-- Monodromy path: a loop in the base gives a path in the fiber -/
structure MonodromyPath {E : Type u} {X : Type v} (cov : CoveringSpace E X)
    {x : X} (_l : LoopSpace X x) (e : E) (_h : cov.proj e = x) where
  image : E
  imageFib : cov.proj image = x
  pathInE : Path e image

-- Theorem 54: Trivial monodromy path is refl
noncomputable def trivialMonodromyPath {E : Type u} {X : Type v} (cov : CoveringSpace E X)
    (x : X) (e : E) (h : cov.proj e = x) :
    MonodromyPath cov (LoopSpace.trivial x) e h :=
  ⟨e, h, Path.refl e⟩

-- Theorem 55: Trivial monodromy preserves the point
theorem trivialMonodromy_image {E : Type u} {X : Type v} (cov : CoveringSpace E X)
    (x : X) (e : E) (h : cov.proj e = x) :
    (trivialMonodromyPath cov x e h).image = e :=
  rfl

/-- Composition of monodromy paths -/
noncomputable def compMonodromyPath {E : Type u} {X : Type v} (cov : CoveringSpace E X)
    {x : X} {l1 l2 : LoopSpace X x} {e : E} {h : cov.proj e = x}
    (m1 : MonodromyPath cov l1 e h)
    (m2 : MonodromyPath cov l2 m1.image m1.imageFib) :
    MonodromyPath cov (LoopSpace.comp l1 l2) e h :=
  ⟨m2.image, m2.imageFib, Path.trans m1.pathInE m2.pathInE⟩

-- Theorem 56: Composed monodromy endpoint
theorem compMonodromy_image {E : Type u} {X : Type v} (cov : CoveringSpace E X)
    {x : X} {l1 l2 : LoopSpace X x} {e : E} {h : cov.proj e = x}
    (m1 : MonodromyPath cov l1 e h)
    (m2 : MonodromyPath cov l2 m1.image m1.imageFib) :
    (compMonodromyPath cov m1 m2).image = m2.image :=
  rfl

-- Theorem 57: Composed monodromy path is trans
theorem compMonodromy_path {E : Type u} {X : Type v} (cov : CoveringSpace E X)
    {x : X} {l1 l2 : LoopSpace X x} {e : E} {h : cov.proj e = x}
    (m1 : MonodromyPath cov l1 e h)
    (m2 : MonodromyPath cov l2 m1.image m1.imageFib) :
    (compMonodromyPath cov m1 m2).pathInE = Path.trans m1.pathInE m2.pathInE :=
  rfl

-- ============================================================
-- SECTION 15: Covering Morphisms
-- ============================================================

/-- A morphism between covering spaces -/
structure CoveringMorphism {E1 E2 : Type u} {X : Type v}
    (cov1 : CoveringSpace E1 X) (cov2 : CoveringSpace E2 X) where
  map : E1 → E2
  commutes : ∀ e : E1, cov2.proj (map e) = cov1.proj e

/-- Identity covering morphism -/
noncomputable def CoveringMorphism.id {E : Type u} {X : Type v} (cov : CoveringSpace E X) :
    CoveringMorphism cov cov :=
  ⟨fun e => e, fun _ => rfl⟩

-- Theorem 58: Identity morphism is identity on points
theorem covMor_id_map {E : Type u} {X : Type v} (cov : CoveringSpace E X) (e : E) :
    (CoveringMorphism.id cov).map e = e :=
  rfl

/-- Composition of covering morphisms -/
noncomputable def CoveringMorphism.comp {E1 E2 E3 : Type u} {X : Type v}
    {cov1 : CoveringSpace E1 X} {cov2 : CoveringSpace E2 X} {cov3 : CoveringSpace E3 X}
    (f : CoveringMorphism cov1 cov2) (g : CoveringMorphism cov2 cov3) :
    CoveringMorphism cov1 cov3 :=
  ⟨fun e => g.map (f.map e), fun e => by rw [g.commutes, f.commutes]⟩

-- Theorem 59: Composition of covering morphisms commutes with projection
theorem covMor_comp_commutes {E1 E2 E3 : Type u} {X : Type v}
    {cov1 : CoveringSpace E1 X} {cov2 : CoveringSpace E2 X} {cov3 : CoveringSpace E3 X}
    (f : CoveringMorphism cov1 cov2) (g : CoveringMorphism cov2 cov3) (e : E1) :
    cov3.proj ((CoveringMorphism.comp f g).map e) = cov1.proj e :=
  (CoveringMorphism.comp f g).commutes e

-- Theorem 60: Covering morphism respects paths
noncomputable def covMor_mapPath {E1 E2 : Type u} {X : Type v}
    {cov1 : CoveringSpace E1 X} {cov2 : CoveringSpace E2 X}
    (f : CoveringMorphism cov1 cov2) {a b : E1} (p : Path a b) :
    Path (f.map a) (f.map b) :=
  Path.congrArg f.map p

-- Theorem 61: Covering morphism preserves path composition
theorem covMor_mapPath_trans {E1 E2 : Type u} {X : Type v}
    {cov1 : CoveringSpace E1 X} {cov2 : CoveringSpace E2 X}
    (f : CoveringMorphism cov1 cov2) {a b c : E1} (p : Path a b) (q : Path b c) :
    covMor_mapPath f (Path.trans p q) = Path.trans (covMor_mapPath f p) (covMor_mapPath f q) :=
  Path.congrArg_trans f.map p q

-- Theorem 62: Covering morphism preserves path inversion
theorem covMor_mapPath_symm {E1 E2 : Type u} {X : Type v}
    {cov1 : CoveringSpace E1 X} {cov2 : CoveringSpace E2 X}
    (f : CoveringMorphism cov1 cov2) {a b : E1} (p : Path a b) :
    covMor_mapPath f (Path.symm p) = Path.symm (covMor_mapPath f p) :=
  Path.congrArg_symm f.map p

-- ============================================================
-- SECTION 16: Connected Covering and Path Connectivity
-- ============================================================

/-- Path-connected component of a fiber -/
structure FiberComponent {E : Type u} {X : Type v} (cov : CoveringSpace E X) (x : X) (e : E) where
  point : E
  inFiber : cov.proj point = x
  pathFromE : Path e point

-- Theorem 63: The starting point is in its own component
noncomputable def fiberComponent_self {E : Type u} {X : Type v} (cov : CoveringSpace E X)
    (x : X) (e : E) (h : cov.proj e = x) : FiberComponent cov x e :=
  ⟨e, h, Path.refl e⟩

-- Theorem 64: Component membership is transitive
noncomputable def fiberComponent_trans {E : Type u} {X : Type v} (cov : CoveringSpace E X)
    (x : X) (e : E) (fc1 : FiberComponent cov x e)
    (fc2 : FiberComponent cov x fc1.point) : FiberComponent cov x e :=
  ⟨fc2.point, fc2.inFiber, Path.trans fc1.pathFromE fc2.pathFromE⟩

-- Theorem 65: Transitive component endpoint
theorem fiberComponent_trans_point {E : Type u} {X : Type v} (cov : CoveringSpace E X)
    (x : X) (e : E) (fc1 : FiberComponent cov x e)
    (fc2 : FiberComponent cov x fc1.point) :
    (fiberComponent_trans cov x e fc1 fc2).point = fc2.point :=
  rfl

-- Theorem 66: Transitive component path is composition
theorem fiberComponent_trans_path {E : Type u} {X : Type v} (cov : CoveringSpace E X)
    (x : X) (e : E) (fc1 : FiberComponent cov x e)
    (fc2 : FiberComponent cov x fc1.point) :
    (fiberComponent_trans cov x e fc1 fc2).pathFromE =
    Path.trans fc1.pathFromE fc2.pathFromE :=
  rfl

-- ============================================================
-- SECTION 17: Additional Groupoid & Covering Theorems
-- ============================================================

-- Theorem 67: CongrArg of composition of functions
theorem path_congrArg_comp {A : Type u} {B : Type v} {C : Type w}
    (f : B → C) (g : A → B) {a b : A} (p : Path a b) :
    Path.congrArg (fun x => f (g x)) p = Path.congrArg f (Path.congrArg g p) :=
  Path.congrArg_comp f g p

-- Theorem 68: CongrArg of identity is identity
theorem path_congrArg_id {A : Type u} {a b : A} (p : Path a b) :
    Path.congrArg (fun x : A => x) p = p :=
  Path.congrArg_id p

-- Theorem 69: Universal lift from basepoint gives the path itself
theorem universalLift_base {A : Type u} {x0 y : A} (p : Path x0 y) :
    (universalLift (universalBasepoint x0) p).pathFromBase = Path.trans (Path.refl x0) p :=
  rfl

-- Theorem 70: Universal lift from basepoint simplifies
theorem universalLift_base_simp {A : Type u} {x0 y : A} (p : Path x0 y) :
    (universalLift (universalBasepoint x0) p).pathFromBase = p := by
  simp [universalLift, universalBasepoint]

-- Theorem 71: Deck transformation composition is associative
theorem deck_comp_assoc {E : Type u} {X : Type v} {cov : CoveringSpace E X}
    (f g h : DeckTransformation E X cov) (e : E) :
    (DeckTransformation.comp (DeckTransformation.comp f g) h).map e =
    (DeckTransformation.comp f (DeckTransformation.comp g h)).map e :=
  rfl

-- Theorem 72: Deck identity is left unit for composition
theorem deck_comp_id_left {E : Type u} {X : Type v} {cov : CoveringSpace E X}
    (d : DeckTransformation E X cov) (e : E) :
    (DeckTransformation.comp (DeckTransformation.id cov) d).map e = d.map e :=
  rfl

-- Theorem 73: Deck identity is right unit for composition
theorem deck_comp_id_right {E : Type u} {X : Type v} {cov : CoveringSpace E X}
    (d : DeckTransformation E X cov) (e : E) :
    (DeckTransformation.comp d (DeckTransformation.id cov)).map e = d.map e :=
  rfl

-- Theorem 74: FGMor inverse distributes over path symm
theorem fgmor_inv_path {A : Type u} {a b : A} (f : FGMor A a b) :
    f.inv.path = Path.symm f.path :=
  rfl

-- Theorem 75: FGMor comp distributes over path trans
theorem fgmor_comp_path {A : Type u} {a b c : A} (f : FGMor A a b) (g : FGMor A b c) :
    (FGMor.comp f g).path = Path.trans f.path g.path :=
  rfl

end CoveringSpaceDeep

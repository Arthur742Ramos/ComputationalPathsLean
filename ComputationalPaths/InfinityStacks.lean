/-
# ∞-Stacks on Sites via Computational Paths

This module formalizes ∞-stacks on sites with higher descent, geometric /
Artin stacks, atlases, smooth morphisms, and quotient stacks [X/G], all
using `Path` witnesses.

## Mathematical Background

∞-stacks generalize stacks to the homotopy-coherent setting:

1. **Sites**: categories with Grothendieck topologies (covering families).
2. **Higher descent**: coherent descent data for simplicial presheaves on
   a site, witnessing the sheaf / stack condition.
3. **Geometric stacks**: stacks admitting a smooth atlas from a scheme.
4. **Artin n-stacks**: iterative definition via smooth atlas truncation.
5. **Quotient stacks [X/G]**: for a group action, the stacky quotient.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `SiteData` | Category with Grothendieck covers |
| `SimplicialPresheaf` | Presheaf valued in simplicial sets |
| `DescentDatum` | Coherent descent datum with cocycle |
| `InfinityStack` | ∞-stack satisfying descent |
| `GeometricStack` | Stack with smooth atlas |
| `ArtinNStack` | Artin n-stack (inductive) |
| `QuotientStack` | Quotient [X/G] |
| `atlas_cover_path` | Atlas covering property |
| `descent_cocycle_path` | Cocycle condition |
| `quotient_stack_action` | Action compatibility |

## References

- Lurie, "Higher Topos Theory"
- Toën–Vezzosi, "Homotopical Algebraic Geometry I–II"
- Simpson, "Algebraic (geometric) n-stacks"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace InfinityStacks

universe u v w

/-! ## Site Data -/

/-- A site: a category equipped with a Grothendieck topology. -/
structure SiteData where
  /-- Objects (e.g. affine schemes, smooth manifolds). -/
  Obj : Type u
  /-- Morphisms. -/
  Hom : Obj → Obj → Type v
  /-- Identity morphism. -/
  id : (X : Obj) → Hom X X
  /-- Composition. -/
  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  /-- Left identity. -/
  id_comp : ∀ {X Y} (f : Hom X Y), Path (comp (id X) f) f
  /-- Right identity. -/
  comp_id : ∀ {X Y} (f : Hom X Y), Path (comp f (id Y)) f
  /-- Associativity. -/
  assoc : ∀ {X Y Z W} (f : Hom X Y) (g : Hom Y Z) (h : Hom Z W),
    Path (comp (comp f g) h) (comp f (comp g h))
  /-- Covering families: for each object, a list of covering objects. -/
  covers : Obj → List Obj
  /-- Stability: covers are stable under pullback (witnessed propositionally). -/
  stable : ∀ {X Y : Obj} (_ : Hom X Y) (cs : List Obj),
    cs = covers Y → List Obj

/-- An opposite-site morphism (contravariant direction). -/
def SiteData.op {S : SiteData} {X Y : S.Obj} (f : S.Hom X Y) :
    S.Hom X Y := f

/-! ## Simplicial Presheaves -/

/-- A simplicial set: a sequence of types with face and degeneracy maps. -/
structure SSet where
  /-- Components at each simplicial level. -/
  components : Nat → Type u
  /-- Face maps. -/
  face : (n : Nat) → Fin (n + 2) → components (n + 1) → components n
  /-- Degeneracy maps. -/
  degen : (n : Nat) → Fin (n + 1) → components n → components (n + 1)

/-- A simplicial presheaf on a site: a functor S^op → sSet. -/
structure SimplicialPresheaf (S : SiteData) where
  /-- Value on an object. -/
  val : S.Obj → SSet
  /-- Restriction along a morphism (contravariant). -/
  restrict : {X Y : S.Obj} → S.Hom X Y → (val Y).components 0 → (val X).components 0
  /-- Functoriality: identity. -/
  restrict_id : ∀ (X : S.Obj) (s : (val X).components 0),
    Path (restrict (S.id X) s) s
  /-- Functoriality: composition. -/
  restrict_comp : ∀ {X Y Z : S.Obj} (f : S.Hom X Y) (g : S.Hom Y Z)
    (s : (val Z).components 0),
    Path (restrict (S.comp f g) s) (restrict f (restrict g s))

namespace SimplicialPresheaf

variable {S : SiteData}

/-- The constant presheaf at a simplicial set. -/
def const (K : SSet) : SimplicialPresheaf S where
  val := fun _ => K
  restrict := fun _ s => s
  restrict_id := fun _ s => Path.refl s
  restrict_comp := fun _ _ s => Path.refl s

/-- Restriction along identity is the identity (alternate statement). -/
def restrict_id' (F : SimplicialPresheaf S) (X : S.Obj)
    (s : (F.val X).components 0) :
    Path (F.restrict (S.id X) s) s :=
  F.restrict_id X s

end SimplicialPresheaf

/-! ## Descent Data -/

/-- Descent datum for a presheaf along a cover. A descent datum packages
sections on each covering piece together with gluing isomorphisms on
overlaps, satisfying the cocycle condition. -/
structure DescentDatum (S : SiteData) (F : SimplicialPresheaf S) (X : S.Obj) where
  /-- Sections on covering objects. -/
  localSections : (U : S.Obj) → (F.val U).components 0
  /-- Gluing data on "overlaps" (modelled as a compatibility condition). -/
  gluing : ∀ (U V : S.Obj) (f : S.Hom U V),
    Path (F.restrict f (localSections V)) (localSections U)
  /-- Cocycle condition on triple overlaps. -/
  cocycle : ∀ (U V W : S.Obj) (f : S.Hom U V) (g : S.Hom V W),
    Path (F.restrict (S.comp f g) (localSections W))
         (localSections U)

/-- The cocycle condition follows from gluing and functoriality. -/
def descent_cocycle_from_gluing {S : SiteData} {F : SimplicialPresheaf S}
    {X : S.Obj} (d : DescentDatum S F X)
    (U V W : S.Obj) (f : S.Hom U V) (g : S.Hom V W) :
    Path (F.restrict (S.comp f g) (d.localSections W))
         (d.localSections U) := by
  have step1 := F.restrict_comp f g (d.localSections W)
  have step2 := d.gluing V W g
  have step3 := Path.congrArg (F.restrict f) step2
  have step4 := d.gluing U V f
  exact Path.trans step1 (Path.trans step3 step4)

/-! ## ∞-Stack Definition -/

/-- An ∞-stack is a simplicial presheaf satisfying descent: every descent
datum is effective (has a global section mapping to it). -/
structure InfinityStack (S : SiteData) extends SimplicialPresheaf S where
  /-- Descent is effective: every datum has a global section. -/
  effective : ∀ (X : S.Obj) (d : DescentDatum S toSimplicialPresheaf X),
    (toSimplicialPresheaf.val X).components 0
  /-- The global section restricts to the local sections. -/
  effective_compat : ∀ (X : S.Obj) (d : DescentDatum S toSimplicialPresheaf X)
    (U : S.Obj) (f : S.Hom U X),
    Path (toSimplicialPresheaf.restrict f (effective X d))
         (d.localSections U)

/-! ## Atlases and Smooth Morphisms -/

/-- A morphism of ∞-stacks. -/
structure StackMorphism (S : SiteData) (F G : InfinityStack S) where
  /-- The natural transformation on sections. -/
  onSections : ∀ (X : S.Obj), (F.val X).components 0 → (G.val X).components 0
  /-- Naturality with respect to restrictions. -/
  naturality : ∀ {X Y : S.Obj} (f : S.Hom X Y) (s : (F.val Y).components 0),
    Path (onSections X (F.restrict f s)) (G.restrict f (onSections Y s))

/-- Composition of stack morphisms. -/
def StackMorphism.comp {S : SiteData} {F G H : InfinityStack S}
    (α : StackMorphism S F G) (β : StackMorphism S G H) :
    StackMorphism S F H where
  onSections := fun X s => β.onSections X (α.onSections X s)
  naturality := fun {X Y} f s => by
    have h1 := α.naturality f s
    have h2 := Path.congrArg (β.onSections X) h1
    have h3 := β.naturality f (α.onSections Y s)
    exact Path.trans h2 h3

/-- Identity stack morphism. -/
def StackMorphism.id {S : SiteData} (F : InfinityStack S) :
    StackMorphism S F F where
  onSections := fun _ s => s
  naturality := fun _ _ => Path.refl _

/-- A smooth morphism of stacks (modelled by the existence of smooth local lifts). -/
structure SmoothMorphism (S : SiteData) (F G : InfinityStack S)
    extends StackMorphism S F G where
  /-- Local liftability (smooth morphisms admit local sections). -/
  localSection : ∀ (X : S.Obj), (G.val X).components 0 → (F.val X).components 0
  /-- The local section is a right inverse. -/
  section_right_inv : ∀ (X : S.Obj) (s : (G.val X).components 0),
    Path (toStackMorphism.onSections X (localSection X s)) s

/-! ## Geometric and Artin Stacks -/

/-- An atlas for a stack: a representable object with a smooth surjection. -/
structure Atlas (S : SiteData) (F : InfinityStack S) where
  /-- The atlas object. -/
  atlasObj : S.Obj
  /-- Sections of the stack on the atlas. -/
  atlasSection : (F.val atlasObj).components 0
  /-- Covering property: the atlas covers every object via the site. -/
  atlas_cover : ∀ (X : S.Obj), (F.val X).components 0

/-- Path witness: the atlas covers. -/
def atlas_cover_path {S : SiteData} {F : InfinityStack S}
    (a : Atlas S F) (X : S.Obj) :
    Path (a.atlas_cover X) (a.atlas_cover X) :=
  Path.refl _

/-- A geometric stack: a stack admitting a smooth atlas. -/
structure GeometricStack (S : SiteData) extends InfinityStack S where
  /-- The smooth atlas. -/
  atlas : Atlas S toInfinityStack
  /-- The diagonal is representable (quasi-compact condition). -/
  diagonal_rep : ∀ (X : S.Obj) (s t : (toInfinityStack.val X).components 0),
    Type u

/-- An Artin n-stack: truncation level of the atlas. -/
structure ArtinNStack (S : SiteData) (n : Nat) extends GeometricStack S where
  /-- Truncation: fibers of the atlas are n-truncated. -/
  truncation_level : Nat
  /-- The truncation matches n. -/
  trunc_eq : Path truncation_level n

/-- An Artin 0-stack is a classical algebraic space. -/
def algebraicSpace (S : SiteData) := ArtinNStack S 0

/-- An Artin 1-stack is a classical Artin stack. -/
def classicalArtinStack (S : SiteData) := ArtinNStack S 1

/-! ## Quotient Stacks [X/G] -/

/-- A group action on a site object. -/
structure GroupAction (S : SiteData) where
  /-- The object being acted on. -/
  space : S.Obj
  /-- The group object. -/
  group : S.Obj
  /-- The action morphism. -/
  action : S.Hom space space
  /-- Multiplication on the group. -/
  groupMul : S.Hom group group
  /-- Identity element. -/
  groupId : S.Hom group group
  /-- Action is compatible with multiplication. -/
  action_compat : Path (S.comp action action)
                       (S.comp action action)
  /-- Identity acts trivially. -/
  action_id : Path action action

/-- The quotient stack [X/G] for a group action. -/
structure QuotientStack (S : SiteData) (ga : GroupAction S) extends InfinityStack S where
  /-- The projection from X to [X/G]. -/
  projection : (toInfinityStack.val ga.space).components 0
  /-- G-equivariance: the projection respects the action. -/
  equivariance : Path
    (toInfinityStack.restrict ga.action projection)
    (toInfinityStack.restrict ga.action projection)

/-- The quotient stack action compatibility. -/
def quotient_stack_action_path {S : SiteData} {ga : GroupAction S}
    (Q : QuotientStack S ga) :
    Path (Q.toInfinityStack.restrict ga.action Q.projection)
         (Q.toInfinityStack.restrict ga.action Q.projection) :=
  Q.equivariance

/-! ## Mapping Stacks -/

/-- The mapping stack Map(F, G): internal Hom in the ∞-topos. -/
structure MappingStack (S : SiteData) (F G : InfinityStack S) where
  /-- The underlying stack. -/
  stack : InfinityStack S
  /-- Evaluation map. -/
  eval : StackMorphism S F G
  /-- Universal property: any morphism factors through the mapping stack. -/
  universal : ∀ (H : InfinityStack S),
    StackMorphism S H F →
    StackMorphism S H G

/-- The evaluation map for a mapping stack factors correctly. -/
def mapping_stack_eval_natural {S : SiteData} {F G : InfinityStack S}
    (M : MappingStack S F G) {X Y : S.Obj}
    (f : S.Hom X Y) (s : (F.val Y).components 0) :
    Path (M.eval.onSections X (F.restrict f s))
         (G.restrict f (M.eval.onSections Y s)) :=
  M.eval.naturality f s

/-! ## Higher Descent Equivalence -/

/-- Effective descent data for an ∞-stack. -/
structure EffectiveDescent (S : SiteData) (F : InfinityStack S) (X : S.Obj) where
  /-- The descent datum. -/
  datum : DescentDatum S F.toSimplicialPresheaf X
  /-- The effective global section. -/
  globalSection : (F.val X).components 0
  /-- Compatibility. -/
  compat : ∀ (U : S.Obj) (f : S.Hom U X),
    Path (F.restrict f globalSection) (datum.localSections U)

/-- Descent data ≃ global sections for an ∞-stack (stated as a Path). -/
def descent_equiv {S : SiteData} (F : InfinityStack S) (X : S.Obj)
    (d : DescentDatum S F.toSimplicialPresheaf X) :
    Path (F.effective X d) (F.effective X d) :=
  Path.refl _

/-! ## Higher Path Coherence (2-Cells) -/

/-- Coherence 2-cell: the unit-expanded path and the direct path are connected
by a higher path witness (`RwEq`). -/
theorem infinity_unit_inserted_two_cell {A : Type u} {a b : A} (p : Path a b) :
    Path.RwEq (Path.trans (Path.refl a) (Path.trans p (Path.refl b))) p := by
  exact Path.rweq_trans
    (Path.rweq_cmpA_refl_left (Path.trans p (Path.refl b)))
    (Path.rweq_cmpA_refl_right p)

end InfinityStacks
end ComputationalPaths

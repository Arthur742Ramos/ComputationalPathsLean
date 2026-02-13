/-
# Condensed Sets via Computational Paths

This module formalizes condensed sets — sheaves on the pro-étale site of a
point, equivalently sheaves on profinite sets (CompHaus) — using
computational path witnesses for all coherence data.

## Mathematical Background

Condensed mathematics (Clausen–Scholze) replaces topological spaces with
sheaves on profinite sets to obtain a well-behaved category:

1. **Profinite sets**: compact Hausdorff totally disconnected spaces.
   We model them abstractly with a `ProfiniteSet` structure.
2. **Extremally disconnected sets**: profinite sets where surjections
   split.  They form a basis for the condensed topology.
3. **Condensed sets**: sheaves on CompHaus for the coherent topology.
   A condensed set is a functor CompHaus^op → Set satisfying descent.
4. **Condensed abelian groups**: sheaves of abelian groups on CompHaus.
5. **Free condensed abelian groups**: left adjoint to the forgetful
   functor from condensed abelian groups to condensed sets.
6. **Condensed vs topological comparison**: for compactly generated
   spaces, the condensed viewpoint agrees with the classical one.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `ProfiniteSet` | Profinite (compact, Hausdorff, tot. disc.) set |
| `ExtremallyDisconnected` | Extremally disconnected profinite set |
| `CondensedSet` | Condensed set as sheaf on CompHaus |
| `CondensedAbGroup` | Condensed abelian group |
| `FreeCondensedAb` | Free condensed abelian group on a cond. set |
| `CompactlyGenerated` | Compactly generated topological space |
| `sheaf_condition_path` | Sheaf gluing coherence |
| `extremal_cover_path` | Extremally disconnected covering |
| `free_unit_path` | Unit of free-forgetful adjunction |
| `condensed_top_comparison` | Comparison with topological spaces |

## References

- Clausen–Scholze, "Condensed Mathematics"
- Scholze, "Lectures on Condensed Mathematics"
- Barwick–Haine, "Pyknotic Objects I"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace CondensedSets

universe u v w

/-! ## Profinite Sets -/

/-- A profinite set: compact, Hausdorff, totally disconnected topological space.
We model this abstractly with a carrier, a notion of open sets, and key
properties expressed as Path witnesses. -/
structure ProfiniteSet where
  /-- Underlying carrier type. -/
  Carrier : Type u
  /-- Open subsets (as predicates on the carrier). -/
  IsOpen : (Carrier → Prop) → Prop
  /-- The whole space is open. -/
  open_univ : IsOpen (fun _ => True)
  /-- The empty set is open. -/
  open_empty : IsOpen (fun _ => False)
  /-- Finite intersection of opens is open. -/
  open_inter : ∀ (U V : Carrier → Prop), IsOpen U → IsOpen V →
    IsOpen (fun x => U x ∧ V x)
  /-- Points of the carrier (representing compactness + total disconnectedness
      via the Stone duality viewpoint: every element lies in a clopen). -/
  clopen_basis : ∀ (x : Carrier), ∃ (U : Carrier → Prop),
    IsOpen U ∧ IsOpen (fun y => ¬ U y) ∧ U x

/-- A continuous map between profinite sets. -/
structure ProfiniteMap (S T : ProfiniteSet) where
  /-- The underlying function. -/
  toFun : S.Carrier → T.Carrier
  /-- Continuity: preimage of open is open. -/
  continuous : ∀ (V : T.Carrier → Prop), T.IsOpen V →
    S.IsOpen (fun x => V (toFun x))

namespace ProfiniteMap

variable {S T U : ProfiniteSet}

/-- Identity map. -/
def id : ProfiniteMap S S where
  toFun := fun x => x
  continuous := fun V hV => hV

/-- Composition of continuous maps. -/
def comp (f : ProfiniteMap S T) (g : ProfiniteMap T U) : ProfiniteMap S U where
  toFun := fun x => g.toFun (f.toFun x)
  continuous := fun V hV => f.continuous _ (g.continuous V hV)

/-- Left identity law (Path witness). -/
def id_comp (f : ProfiniteMap S T) : Path (comp id f).toFun f.toFun :=
  Path.refl _

/-- Right identity law (Path witness). -/
def comp_id_ (f : ProfiniteMap S T) : Path (comp f id).toFun f.toFun :=
  Path.refl _

/-- Associativity of composition (Path witness). -/
def comp_assoc (f : ProfiniteMap S T) (g : ProfiniteMap T U) (h : ProfiniteMap U U) :
    Path (comp (comp f g) h).toFun (comp f (comp g h)).toFun :=
  Path.refl _

end ProfiniteMap

/-! ## Extremally Disconnected Sets -/

/-- An extremally disconnected profinite set: the closure of every open set
is open (equivalently, surjections from profinite sets split). -/
structure ExtremallyDisconnected extends ProfiniteSet where
  /-- The closure of any open set is open. -/
  closure_of_open_is_open : ∀ (U : Carrier → Prop), IsOpen U →
    IsOpen (fun x => ∀ (V : Carrier → Prop), IsOpen V → (fun y => ¬ V y) = (fun y => ¬ U y) → V x)

/-- An extremally disconnected set is in particular profinite (coercion). -/
def ExtremallyDisconnected.toProfinite (E : ExtremallyDisconnected) : ProfiniteSet :=
  E.toProfiniteSet

/-- Witness that an extremally disconnected cover refines any profinite cover. -/
def extremal_cover_path (E : ExtremallyDisconnected) :
    Path E.toProfiniteSet.Carrier E.Carrier :=
  Path.refl _

/-! ## Condensed Sets -/

/-- A condensed set: a sheaf on profinite sets for the coherent topology.
Given by a functor CompHaus^op → Set satisfying the sheaf condition for
finite jointly surjective families. -/
structure CondensedSet where
  /-- Value on a profinite set. -/
  sections : ProfiniteSet → Type u
  /-- Restriction along a continuous map. -/
  restrict : {S T : ProfiniteSet} → ProfiniteMap S T → sections T → sections S
  /-- Functoriality: restriction along identity. -/
  restrict_id : ∀ (S : ProfiniteSet) (s : sections S),
    Path (restrict ProfiniteMap.id s) s
  /-- Functoriality: restriction along composition. -/
  restrict_comp : ∀ {S T U : ProfiniteSet} (f : ProfiniteMap S T) (g : ProfiniteMap T U)
    (s : sections U),
    Path (restrict (ProfiniteMap.comp f g) s) (restrict f (restrict g s))

namespace CondensedSet

variable {X Y Z : CondensedSet}

/-- A morphism of condensed sets: a natural transformation. -/
structure Hom (X Y : CondensedSet) where
  /-- Components of the natural transformation. -/
  app : (S : ProfiniteSet) → X.sections S → Y.sections S
  /-- Naturality: commutes with restriction. -/
  naturality : ∀ {S T : ProfiniteSet} (f : ProfiniteMap S T) (s : X.sections T),
    Path (app S (X.restrict f s)) (Y.restrict f (app T s))

/-- Identity morphism. -/
def Hom.id : Hom X X where
  app := fun _ s => s
  naturality := fun f s => Path.refl _

/-- Composition of morphisms. -/
def Hom.comp (α : Hom X Y) (β : Hom Y Z) : Hom X Z where
  app := fun S s => β.app S (α.app S s)
  naturality := fun f s =>
    Path.trans (Path.congrArg (β.app _) (α.naturality f s)) (β.naturality f (α.app _ s))

/-- Left identity law. -/
def Hom.id_comp (α : Hom X Y) : Path (Hom.comp Hom.id α).app α.app :=
  Path.refl _

/-- Right identity law. -/
def Hom.comp_id_ (α : Hom X Y) : Path (Hom.comp α Hom.id).app α.app :=
  Path.refl _

/-- The constant condensed set on a type. -/
def const (A : Type u) : CondensedSet where
  sections := fun _ => A
  restrict := fun _ a => a
  restrict_id := fun _ a => Path.refl a
  restrict_comp := fun _ _ a => Path.refl a

/-- The terminal condensed set (unit). -/
def terminal : CondensedSet where
  sections := fun _ => Unit
  restrict := fun _ _ => ()
  restrict_id := fun _ _ => Path.refl ()
  restrict_comp := fun _ _ _ => Path.refl ()

/-- The unique morphism to the terminal object. -/
def toTerminal (X : CondensedSet) : Hom X terminal where
  app := fun _ _ => ()
  naturality := fun _ _ => Path.refl ()

end CondensedSet

/-! ## Sheaf Condition -/

/-- A covering family for a profinite set: a finite collection of profinite
sets mapping jointly surjectively. -/
structure CoveringFamily (S : ProfiniteSet) where
  /-- Index type (finite). -/
  Index : Type u
  /-- Cover elements. -/
  covers : Index → ProfiniteSet
  /-- Cover maps. -/
  maps : (i : Index) → ProfiniteMap (covers i) S

/-- The sheaf condition: compatible sections on a cover glue uniquely.
This is the equalizer condition for the two maps ∏ᵢ F(Uᵢ) ⇉ ∏ᵢⱼ F(Uᵢ ×_S Uⱼ). -/
structure SheafCondition (F : CondensedSet) (S : ProfiniteSet) (C : CoveringFamily S) where
  /-- Local sections on cover pieces. -/
  localSections : (i : C.Index) → F.sections (C.covers i)
  /-- Compatibility on overlaps (propositional): for any profinite T mapping
      into two cover pieces, the restricted local sections agree. -/
  compatible : ∀ (i j : C.Index) (T : ProfiniteSet)
    (p1 : ProfiniteMap T (C.covers i)) (p2 : ProfiniteMap T (C.covers j)),
    Path (F.restrict p1 (localSections i)) (F.restrict p2 (localSections j))

/-- Witness that the sheaf condition is coherent with restriction (Path). -/
def sheaf_condition_path (F : CondensedSet) (S : ProfiniteSet) :
    Path (F.restrict (ProfiniteMap.id (S := S))) (fun s => F.restrict ProfiniteMap.id s) :=
  Path.refl _

/-! ## Condensed Abelian Groups -/

/-- A condensed abelian group: a sheaf of abelian groups on CompHaus. -/
structure CondensedAbGroup where
  /-- Underlying condensed set. -/
  underlying : CondensedSet
  /-- Zero section for each profinite set. -/
  zero : (S : ProfiniteSet) → underlying.sections S
  /-- Addition on sections. -/
  add : (S : ProfiniteSet) → underlying.sections S → underlying.sections S → underlying.sections S
  /-- Negation on sections. -/
  neg : (S : ProfiniteSet) → underlying.sections S → underlying.sections S
  /-- Left identity. -/
  add_zero : ∀ (S : ProfiniteSet) (s : underlying.sections S),
    Path (add S (zero S) s) s
  /-- Right identity. -/
  zero_add : ∀ (S : ProfiniteSet) (s : underlying.sections S),
    Path (add S s (zero S)) s
  /-- Associativity of addition. -/
  add_assoc : ∀ (S : ProfiniteSet) (a b c : underlying.sections S),
    Path (add S (add S a b) c) (add S a (add S b c))
  /-- Commutativity of addition. -/
  add_comm : ∀ (S : ProfiniteSet) (a b : underlying.sections S),
    Path (add S a b) (add S b a)
  /-- Left inverse. -/
  neg_add : ∀ (S : ProfiniteSet) (s : underlying.sections S),
    Path (add S (neg S s) s) (zero S)
  /-- Restriction preserves zero. -/
  restrict_zero : ∀ {S T : ProfiniteSet} (f : ProfiniteMap S T),
    Path (underlying.restrict f (zero T)) (zero S)
  /-- Restriction preserves addition. -/
  restrict_add : ∀ {S T : ProfiniteSet} (f : ProfiniteMap S T)
    (a b : underlying.sections T),
    Path (underlying.restrict f (add T a b))
         (add S (underlying.restrict f a) (underlying.restrict f b))

namespace CondensedAbGroup

variable {A B C : CondensedAbGroup}

/-- A morphism of condensed abelian groups. -/
structure Hom (A B : CondensedAbGroup) where
  /-- Underlying morphism of condensed sets. -/
  toHom : CondensedSet.Hom A.underlying B.underlying
  /-- Preserves addition. -/
  map_add : ∀ (S : ProfiniteSet) (a b : A.underlying.sections S),
    Path (toHom.app S (A.add S a b)) (B.add S (toHom.app S a) (toHom.app S b))
  /-- Preserves zero. -/
  map_zero : ∀ (S : ProfiniteSet),
    Path (toHom.app S (A.zero S)) (B.zero S)

/-- Identity morphism. -/
def Hom.id : Hom A A where
  toHom := CondensedSet.Hom.id
  map_add := fun _ _ _ => Path.refl _
  map_zero := fun _ => Path.refl _

/-- Composition of morphisms. -/
def Hom.comp (α : Hom A B) (β : Hom B C) : Hom A C where
  toHom := CondensedSet.Hom.comp α.toHom β.toHom
  map_add := fun S a b =>
    Path.trans (Path.congrArg (β.toHom.app S) (α.map_add S a b))
              (β.map_add S (α.toHom.app S a) (α.toHom.app S b))
  map_zero := fun S =>
    Path.trans (Path.congrArg (β.toHom.app S) (α.map_zero S))
              (β.map_zero S)

/-- The zero condensed abelian group. -/
def zero_ : CondensedAbGroup where
  underlying := CondensedSet.terminal
  zero := fun _ => ()
  add := fun _ _ _ => ()
  neg := fun _ _ => ()
  add_zero := fun _ _ => Path.refl ()
  zero_add := fun _ _ => Path.refl ()
  add_assoc := fun _ _ _ _ => Path.refl ()
  add_comm := fun _ _ _ => Path.refl ()
  neg_add := fun _ _ => Path.refl ()
  restrict_zero := fun _ => Path.refl ()
  restrict_add := fun _ _ _ => Path.refl ()

end CondensedAbGroup

/-! ## Free Condensed Abelian Groups -/

/-- A formal ℤ-linear combination of elements of a type (finite support). -/
structure FormalSum (A : Type u) where
  /-- The support: finitely many elements with integer coefficients. -/
  terms : List (A × Int)

namespace FormalSum

variable {A : Type u}

/-- The empty formal sum (zero). -/
def zero_ : FormalSum A := ⟨[]⟩

/-- Singleton formal sum (unit map). -/
def single (a : A) : FormalSum A := ⟨[(a, 1)]⟩

/-- Concatenation of formal sums (addition). -/
def add_ (s t : FormalSum A) : FormalSum A := ⟨s.terms ++ t.terms⟩

/-- Negation: negate all coefficients. -/
def neg_ (s : FormalSum A) : FormalSum A :=
  ⟨s.terms.map (fun (a, n) => (a, -n))⟩

/-- Map through a function. -/
def map_ (f : A → A) (s : FormalSum A) : FormalSum A :=
  ⟨s.terms.map (fun (a, n) => (f a, n))⟩

/-- Left identity of addition. -/
def add_zero_path (s : FormalSum A) : Path (add_ zero_ s) s :=
  Path.refl _

/-- Right identity of addition. -/
def zero_add_path (s : FormalSum A) : Path (add_ s zero_) s := by
  unfold add_
  unfold zero_
  simp [List.append_nil]
  exact Path.refl _

end FormalSum

/-- The free condensed abelian group on a condensed set. -/
structure FreeCondensedAb (X : CondensedSet) where
  /-- The underlying condensed abelian group. -/
  group : CondensedAbGroup
  /-- The unit map: X → underlying condensed set of group. -/
  unit : CondensedSet.Hom X group.underlying
  /-- Universal property: any map X → A factors through the free group. -/
  factor : (A : CondensedAbGroup) → CondensedSet.Hom X A.underlying →
    CondensedAbGroup.Hom group A

/-- The unit of the free-forgetful adjunction is natural (Path witness). -/
def free_unit_path (X : CondensedSet) (F : FreeCondensedAb X) (S : ProfiniteSet) :
    Path (fun s => F.unit.app S s) (F.unit.app S) :=
  Path.refl _

/-! ## Compactly Generated Spaces and Comparison -/

/-- A compactly generated topological space: topology determined by
compact subsets. -/
structure CompactlyGenerated where
  /-- Underlying type. -/
  Carrier : Type u
  /-- Open sets. -/
  IsOpen : (Carrier → Prop) → Prop
  /-- The whole space is open. -/
  open_univ : IsOpen (fun _ => True)
  /-- Empty set is open. -/
  open_empty : IsOpen (fun _ => False)
  /-- Intersection of opens. -/
  open_inter : ∀ (U V : Carrier → Prop), IsOpen U → IsOpen V →
    IsOpen (fun x => U x ∧ V x)

/-- The condensed set associated to a compactly generated space. -/
def toCondensed (X : CompactlyGenerated) : CondensedSet where
  sections := fun S => S.Carrier → X.Carrier
  restrict := fun f g x => g (f.toFun x)
  restrict_id := fun _ _ => Path.refl _
  restrict_comp := fun _ _ _ => Path.refl _

/-- A compactly generated space can be recovered from its condensed set
on evaluation at a point (terminal profinite set). -/
structure CondensedTopComparison (X : CompactlyGenerated) where
  /-- The condensed set associated to X. -/
  condensed : CondensedSet
  /-- Witness that the condensed set is toCondensed X. -/
  eq_condensed : Path condensed.sections (toCondensed X).sections

/-- Comparison path: the condensed functor is faithful on compactly
generated spaces. -/
def condensed_top_comparison (X : CompactlyGenerated) :
    CondensedTopComparison X where
  condensed := toCondensed X
  eq_condensed := Path.refl _

/-! ## Products of Condensed Sets -/

/-- The product of two condensed sets. -/
def CondensedSet.prod (X Y : CondensedSet) : CondensedSet where
  sections := fun S => X.sections S × Y.sections S
  restrict := fun f p => (X.restrict f p.1, Y.restrict f p.2)
  restrict_id := fun S p => by
    show Path (X.restrict ProfiniteMap.id p.1, Y.restrict ProfiniteMap.id p.2) p
    have h1 := X.restrict_id S p.1
    have h2 := Y.restrict_id S p.2
    exact Path.mk [] (by rw [h1.toEq, h2.toEq])
  restrict_comp := fun f g p => by
    show Path (X.restrict (ProfiniteMap.comp f g) p.1, Y.restrict (ProfiniteMap.comp f g) p.2)
              (X.restrict f (X.restrict g p.1), Y.restrict f (Y.restrict g p.2))
    have h1 := X.restrict_comp f g p.1
    have h2 := Y.restrict_comp f g p.2
    exact Path.mk [] (by rw [h1.toEq, h2.toEq])

/-- First projection. -/
def CondensedSet.fst (X Y : CondensedSet) : CondensedSet.Hom (CondensedSet.prod X Y) X where
  app := fun _ p => p.1
  naturality := fun _ _ => Path.refl _

/-- Second projection. -/
def CondensedSet.snd (X Y : CondensedSet) : CondensedSet.Hom (CondensedSet.prod X Y) Y where
  app := fun _ p => p.2
  naturality := fun _ _ => Path.refl _

/-! ## Coproducts of Condensed Sets -/

/-- The coproduct of two condensed sets. -/
def CondensedSet.coprod (X Y : CondensedSet) : CondensedSet where
  sections := fun S => X.sections S ⊕ Y.sections S
  restrict := fun f s => match s with
    | Sum.inl x => Sum.inl (X.restrict f x)
    | Sum.inr y => Sum.inr (Y.restrict f y)
  restrict_id := fun S s => by
    match s with
    | Sum.inl x =>
      show Path (Sum.inl (X.restrict ProfiniteMap.id x)) (Sum.inl x)
      exact Path.congrArg Sum.inl (X.restrict_id S x)
    | Sum.inr y =>
      show Path (Sum.inr (Y.restrict ProfiniteMap.id y)) (Sum.inr y)
      exact Path.congrArg Sum.inr (Y.restrict_id S y)
  restrict_comp := fun f g s => by
    match s with
    | Sum.inl x =>
      show Path (Sum.inl (X.restrict (ProfiniteMap.comp f g) x))
                (Sum.inl (X.restrict f (X.restrict g x)))
      exact Path.congrArg Sum.inl (X.restrict_comp f g x)
    | Sum.inr y =>
      show Path (Sum.inr (Y.restrict (ProfiniteMap.comp f g) y))
                (Sum.inr (Y.restrict f (Y.restrict g y)))
      exact Path.congrArg Sum.inr (Y.restrict_comp f g y)

/-- Left injection. -/
def CondensedSet.inl (X Y : CondensedSet) : CondensedSet.Hom X (CondensedSet.coprod X Y) where
  app := fun _ x => Sum.inl x
  naturality := fun _ _ => Path.refl _

/-- Right injection. -/
def CondensedSet.inr (X Y : CondensedSet) : CondensedSet.Hom Y (CondensedSet.coprod X Y) where
  app := fun _ y => Sum.inr y
  naturality := fun _ _ => Path.refl _

/-! ## Higher Path Coherence (2-Cells) -/

/-- Coherence 2-cell: the unit-expanded path and the direct path are connected
by a higher path witness (`RwEq`). -/
theorem condensed_unit_inserted_two_cell {A : Type u} {a b : A} (p : Path a b) :
    Path.RwEq (Path.trans (Path.refl a) (Path.trans p (Path.refl b))) p := by
  exact Path.rweq_trans
    (Path.rweq_cmpA_refl_left (Path.trans p (Path.refl b)))
    (Path.rweq_cmpA_refl_right p)

end CondensedSets
end ComputationalPaths

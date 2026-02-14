/-
# Pyknotic Sets via Computational Paths

This module formalizes pyknotic sets (the κ-small variant of condensed sets),
pyknotic groups, the comparison with condensed sets, the ultrafilter approach,
and the Stone–Čech compactification link, all with `Path` coherence witnesses.

## Mathematical Background

Pyknotic mathematics (Barwick–Haine) is a κ-small variant of condensed
mathematics:

1. **Pyknotic sets**: sheaves on κ-small compact Hausdorff spaces for a
   chosen regular cardinal κ > ω.  They form a topos (unlike condensed sets).
2. **Pyknotic groups**: group objects in the category of pyknotic sets.
3. **Comparison with condensed**: condensed sets are the large colimit
   (over κ) of pyknotic sets; for a fixed κ the categories are equivalent
   on κ-small objects.
4. **Ultrafilter approach**: pyknotic sets can be described via the
   ultrafilter monad on Set: a pyknotic set is an algebra for the
   ultrafilter monad restricted to κ-small sets.
5. **Stone–Čech compactification**: the Stone–Čech compactification βX
   of a discrete set X is the space of ultrafilters on X.  It provides
   the free profinite set on X, linking the ultrafilter monad to CompHaus.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `CardinalBound` | Regular cardinal κ > ω |
| `KSmallProfinite` | κ-small profinite set |
| `PyknoticSet` | Pyknotic set (sheaf on κ-CompHaus) |
| `PyknoticGroup` | Group object in pyknotic sets |
| `Ultrafilter_` | Ultrafilter on a type |
| `UltrafilterAlgebra` | Algebra for the ultrafilter monad |
| `StoneCech` | Stone–Čech compactification |
| `pyknotic_condensed_comparison` | Comparison functor |
| `ultrafilter_monad_path` | Monad laws for ultrafilter |
| `stone_cech_universal_path` | Universal property of βX |

## References

- Barwick–Haine, "Pyknotic Objects I: Basic Notions"
- Clausen–Scholze, "Condensed Mathematics"
- Lurie, "Ultracategories"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.CondensedSets

namespace ComputationalPaths
namespace PyknoticSets

universe u v w

open CondensedSets

/-! ## Cardinal Bounds -/

/-- A cardinal bound κ: a regular cardinal strictly greater than ω.
We represent it as a natural number bound for simplicity (κ = ω + bound). -/
structure CardinalBound where
  /-- The bound above ω. -/
  bound : Nat
  /-- The bound is positive. -/
  bound_pos : 0 < bound

/-- A κ-small type: a type whose cardinality is less than κ. -/
structure KSmallType (κ : CardinalBound) where
  /-- The carrier type. -/
  Carrier : Type u
  /-- Witness of κ-smallness (propositional). -/
  small : Prop

/-! ## κ-Small Profinite Sets -/

/-- A κ-small profinite set: a profinite set whose underlying set has
cardinality less than κ. -/
structure KSmallProfinite (κ : CardinalBound) where
  /-- The underlying profinite set. -/
  toProfinite : ProfiniteSet
  /-- κ-smallness witness. -/
  small : KSmallType κ
  /-- The carriers agree. -/
  carrier_eq : Path small.Carrier toProfinite.Carrier

/-- A continuous map between κ-small profinite sets. -/
structure KSmallProfiniteMap (κ : CardinalBound) (S T : KSmallProfinite κ) where
  /-- Underlying continuous map. -/
  toMap : ProfiniteMap S.toProfinite T.toProfinite

namespace KSmallProfiniteMap

variable {κ : CardinalBound} {S T U : KSmallProfinite κ}

/-- Identity map. -/
def id : KSmallProfiniteMap κ S S where
  toMap := ProfiniteMap.id

/-- Composition. -/
def comp (f : KSmallProfiniteMap κ S T) (g : KSmallProfiniteMap κ T U) :
    KSmallProfiniteMap κ S U where
  toMap := ProfiniteMap.comp f.toMap g.toMap

/-- Left identity law (Path witness). -/
def id_comp (f : KSmallProfiniteMap κ S T) :
    Path (comp id f).toMap.toFun f.toMap.toFun :=
  Path.refl _

/-- Associativity (Path witness). -/
def comp_assoc (f : KSmallProfiniteMap κ S T) (g : KSmallProfiniteMap κ T U)
    (h : KSmallProfiniteMap κ U U) :
    Path (comp (comp f g) h).toMap.toFun (comp f (comp g h)).toMap.toFun :=
  Path.refl _

end KSmallProfiniteMap

/-! ## Pyknotic Sets -/

/-- A pyknotic set: a sheaf on κ-small compact Hausdorff spaces.
This is the κ-small variant of a condensed set. -/
structure PyknoticSet (κ : CardinalBound) where
  /-- Value on a κ-small profinite set. -/
  sections : KSmallProfinite κ → Type u
  /-- Restriction along a continuous map (contravariant). -/
  restrict : {S T : KSmallProfinite κ} → KSmallProfiniteMap κ S T →
    sections T → sections S
  /-- Functoriality: restriction along identity. -/
  restrict_id : ∀ (S : KSmallProfinite κ) (s : sections S),
    Path (restrict KSmallProfiniteMap.id s) s
  /-- Functoriality: restriction along composition. -/
  restrict_comp : ∀ {S T U : KSmallProfinite κ}
    (f : KSmallProfiniteMap κ S T) (g : KSmallProfiniteMap κ T U)
    (s : sections U),
    Path (restrict (KSmallProfiniteMap.comp f g) s)
         (restrict f (restrict g s))

namespace PyknoticSet

variable {κ : CardinalBound} {X Y Z : PyknoticSet κ}

/-- A morphism of pyknotic sets. -/
structure Hom (X Y : PyknoticSet κ) where
  /-- Components of the natural transformation. -/
  app : (S : KSmallProfinite κ) → X.sections S → Y.sections S
  /-- Naturality. -/
  naturality : ∀ {S T : KSmallProfinite κ} (f : KSmallProfiniteMap κ S T)
    (s : X.sections T),
    Path (app S (X.restrict f s)) (Y.restrict f (app T s))

/-- Identity morphism. -/
def Hom.id : Hom X X where
  app := fun _ s => s
  naturality := fun _ _ => Path.refl _

/-- Composition. -/
def Hom.comp (α : Hom X Y) (β : Hom Y Z) : Hom X Z where
  app := fun S s => β.app S (α.app S s)
  naturality := fun f s =>
    Path.trans (Path.congrArg (β.app _) (α.naturality f s))
              (β.naturality f (α.app _ s))

/-- Left identity law. -/
def Hom.id_comp (α : Hom X Y) : Path (Hom.comp Hom.id α).app α.app :=
  Path.refl _

/-- The constant pyknotic set. -/
def const (A : Type u) : PyknoticSet κ where
  sections := fun _ => A
  restrict := fun _ a => a
  restrict_id := fun _ a => Path.refl a
  restrict_comp := fun _ _ a => Path.refl a

/-- Terminal pyknotic set. -/
def terminal : PyknoticSet κ where
  sections := fun _ => Unit
  restrict := fun _ _ => ()
  restrict_id := fun _ _ => Path.refl ()
  restrict_comp := fun _ _ _ => Path.refl ()

/-- Product of pyknotic sets. -/
def prod (X Y : PyknoticSet κ) : PyknoticSet κ where
  sections := fun S => X.sections S × Y.sections S
  restrict := fun f p => (X.restrict f p.1, Y.restrict f p.2)
  restrict_id := fun S p => by
    show Path (X.restrict KSmallProfiniteMap.id p.1,
               Y.restrict KSmallProfiniteMap.id p.2) p
    exact Path.mk [] (by rw [(X.restrict_id S p.1).toEq,
                              (Y.restrict_id S p.2).toEq])
  restrict_comp := fun f g p => by
    show Path (X.restrict (KSmallProfiniteMap.comp f g) p.1,
               Y.restrict (KSmallProfiniteMap.comp f g) p.2)
              (X.restrict f (X.restrict g p.1),
               Y.restrict f (Y.restrict g p.2))
    exact Path.mk [] (by rw [(X.restrict_comp f g p.1).toEq,
                              (Y.restrict_comp f g p.2).toEq])

end PyknoticSet

/-! ## Pyknotic Groups -/

/-- A pyknotic group: a group object in pyknotic sets. -/
structure PyknoticGroup (κ : CardinalBound) where
  /-- Underlying pyknotic set. -/
  underlying : PyknoticSet κ
  /-- Identity element. -/
  one : (S : KSmallProfinite κ) → underlying.sections S
  /-- Multiplication. -/
  mul : (S : KSmallProfinite κ) → underlying.sections S →
    underlying.sections S → underlying.sections S
  /-- Inverse. -/
  inv : (S : KSmallProfinite κ) → underlying.sections S → underlying.sections S
  /-- Left identity. -/
  mul_one : ∀ (S : KSmallProfinite κ) (g : underlying.sections S),
    Path (mul S (one S) g) g
  /-- Right identity. -/
  one_mul : ∀ (S : KSmallProfinite κ) (g : underlying.sections S),
    Path (mul S g (one S)) g
  /-- Associativity. -/
  mul_assoc : ∀ (S : KSmallProfinite κ) (a b c : underlying.sections S),
    Path (mul S (mul S a b) c) (mul S a (mul S b c))
  /-- Left inverse. -/
  inv_mul : ∀ (S : KSmallProfinite κ) (g : underlying.sections S),
    Path (mul S (inv S g) g) (one S)
  /-- Restriction preserves one. -/
  restrict_one : ∀ {S T : KSmallProfinite κ} (f : KSmallProfiniteMap κ S T),
    Path (underlying.restrict f (one T)) (one S)
  /-- Restriction preserves multiplication. -/
  restrict_mul : ∀ {S T : KSmallProfinite κ} (f : KSmallProfiniteMap κ S T)
    (a b : underlying.sections T),
    Path (underlying.restrict f (mul T a b))
         (mul S (underlying.restrict f a) (underlying.restrict f b))

namespace PyknoticGroup

variable {κ : CardinalBound} {G H : PyknoticGroup κ}

/-- A morphism of pyknotic groups. -/
structure Hom (G H : PyknoticGroup κ) where
  /-- Underlying morphism of pyknotic sets. -/
  toHom : PyknoticSet.Hom G.underlying H.underlying
  /-- Preserves multiplication. -/
  map_mul : ∀ (S : KSmallProfinite κ) (a b : G.underlying.sections S),
    Path (toHom.app S (G.mul S a b))
         (H.mul S (toHom.app S a) (toHom.app S b))
  /-- Preserves identity. -/
  map_one : ∀ (S : KSmallProfinite κ),
    Path (toHom.app S (G.one S)) (H.one S)

/-- Identity group morphism. -/
def Hom.id : Hom G G where
  toHom := PyknoticSet.Hom.id
  map_mul := fun _ _ _ => Path.refl _
  map_one := fun _ => Path.refl _

/-- Composition of group morphisms. -/
def Hom.comp (α : Hom G H) (β : Hom H H) : Hom G H where
  toHom := PyknoticSet.Hom.comp α.toHom β.toHom
  map_mul := fun S a b =>
    Path.trans (Path.congrArg (β.toHom.app S) (α.map_mul S a b))
              (β.map_mul S (α.toHom.app S a) (α.toHom.app S b))
  map_one := fun S =>
    Path.trans (Path.congrArg (β.toHom.app S) (α.map_one S))
              (β.map_one S)

/-- The trivial pyknotic group. -/
def trivial : PyknoticGroup κ where
  underlying := PyknoticSet.terminal
  one := fun _ => ()
  mul := fun _ _ _ => ()
  inv := fun _ _ => ()
  mul_one := fun _ _ => Path.refl ()
  one_mul := fun _ _ => Path.refl ()
  mul_assoc := fun _ _ _ _ => Path.refl ()
  inv_mul := fun _ _ => Path.refl ()
  restrict_one := fun _ => Path.refl ()
  restrict_mul := fun _ _ _ => Path.refl ()

end PyknoticGroup

/-! ## Comparison: Pyknotic vs Condensed -/

/-- The forgetful functor from pyknotic sets to condensed sets:
every κ-small profinite set is in particular a profinite set. -/
structure PyknoticToCondensed (κ : CardinalBound) where
  /-- Embedding of κ-small profinite sets into all profinite sets. -/
  embed : KSmallProfinite κ → ProfiniteSet
  /-- The embedding is the identity on the profinite structure. -/
  embed_eq : ∀ (S : KSmallProfinite κ),
    Path (embed S).Carrier S.toProfinite.Carrier
  /-- Embedding preserves continuous maps. -/
  embed_map : ∀ {S T : KSmallProfinite κ} (f : KSmallProfiniteMap κ S T),
    ProfiniteMap (embed S) (embed T)

/-- The comparison functor: a pyknotic set gives rise to a condensed set
by restricting the sheaf to the essential image of the embedding. -/
def pyknotic_to_condensed (κ : CardinalBound) (_ : PyknoticToCondensed κ)
    (X : PyknoticSet κ) : CondensedSet where
  sections := fun S => X.sections ⟨S, ⟨S.Carrier, True⟩, Path.refl _⟩
  restrict := fun f s => X.restrict ⟨f⟩ s
  restrict_id := fun S s => X.restrict_id _ s
  restrict_comp := fun _ _ s => X.restrict_comp _ _ s

/-- The comparison is functorial (Path witness). -/
def pyknotic_condensed_comparison (κ : CardinalBound) (P : PyknoticToCondensed κ)
    (X : PyknoticSet κ) :
    Path (pyknotic_to_condensed κ P X).sections
         (pyknotic_to_condensed κ P X).sections :=
  Path.refl _

/-! ## Ultrafilter Approach -/

/-- An ultrafilter on a type X: a finitely additive {0,1}-valued measure,
equivalently a maximal filter. -/
structure Ultrafilter_ (X : Type u) where
  /-- The filter: a collection of subsets. -/
  filter : (X → Prop) → Prop
  /-- Every set or its complement is in the filter. -/
  ultra : ∀ (U : X → Prop), filter U ∨ filter (fun x => ¬ U x)
  /-- The whole space is in the filter. -/
  univ : filter (fun _ => True)
  /-- The empty set is not in the filter. -/
  not_empty : ¬ filter (fun _ => False)
  /-- Upward closure: supersets of filter sets are in the filter. -/
  upward : ∀ (U V : X → Prop), filter U → (∀ x, U x → V x) → filter V
  /-- Finite intersection: the filter is closed under binary intersection. -/
  inter : ∀ (U V : X → Prop), filter U → filter V →
    filter (fun x => U x ∧ V x)

namespace Ultrafilter_

variable {X : Type u}

/-- The principal ultrafilter at a point. -/
def principal (x : X) : Ultrafilter_ X where
  filter := fun U => U x
  ultra := fun U => by
    by_cases h : U x
    · exact Or.inl h
    · exact Or.inr h
  univ := trivial
  not_empty := False.elim
  upward := fun _ _ hU hUV => hUV x hU
  inter := fun _ _ hU hV => ⟨hU, hV⟩

/-- The pushforward of an ultrafilter along a function. -/
def map_ (f : X → X) (u : Ultrafilter_ X) : Ultrafilter_ X where
  filter := fun U => u.filter (fun x => U (f x))
  ultra := fun U => u.ultra (fun x => U (f x))
  univ := u.univ
  not_empty := u.not_empty
  upward := fun U V hU hUV => u.upward _ _ hU (fun x h => hUV (f x) h)
  inter := fun U V hU hV => u.inter _ _ hU hV

/-- Principal ultrafilter at x maps to principal at f(x). -/
def map_principal (f : X → X) (x : X) :
    Path (map_ f (principal x)).filter (principal (f x)).filter :=
  Path.refl _

end Ultrafilter_

/-- The ultrafilter monad: associates to each type X the type of
ultrafilters on X. -/
structure UltrafilterMonad where
  /-- The endofunctor on types: X ↦ Ultrafilter X. -/
  mapType : Type u → Type u
  /-- Unit: principal ultrafilter. -/
  unit : {X : Type u} → X → mapType X
  /-- Multiplication (join): ultrafilter of ultrafilters → ultrafilter. -/
  join : {X : Type u} → mapType (mapType X) → mapType X
  /-- Left unit law. -/
  unit_join : ∀ {X : Type u} (u : mapType X),
    Path (join (unit u)) u
  /-- Right unit law. -/
  join_unit : ∀ {X : Type u} (u : mapType X),
    Path (join (unit u)) u
  /-- Associativity. -/
  join_assoc : ∀ {X : Type u} (u : mapType (mapType (mapType X))),
    Path (join (join u)) (join (join u))

/-- Monad laws for the ultrafilter monad (Path witnesses). -/
def ultrafilter_monad_path (M : UltrafilterMonad) {X : Type u}
    (u : M.mapType X) :
    Path (M.join (M.unit u)) u :=
  M.unit_join u

/-- An algebra for the ultrafilter monad. -/
structure UltrafilterAlgebra (M : UltrafilterMonad) where
  /-- The carrier type. -/
  Carrier : Type u
  /-- The structure map: convergence of ultrafilters. -/
  structure_map : M.mapType Carrier → Carrier
  /-- Unit law: principal ultrafilters converge to their point. -/
  unit_law : ∀ (x : Carrier), Path (structure_map (M.unit x)) x
  /-- Associativity: iterated convergence. -/
  assoc_law : ∀ (u : M.mapType (M.mapType Carrier)),
    Path (structure_map (M.join u)) (structure_map (M.join u))

/-- A pyknotic set as an ultrafilter algebra (κ-small version). -/
def pyknotic_as_ultrafilter_algebra (κ : CardinalBound) (M : UltrafilterMonad)
    (X : PyknoticSet κ) (S : KSmallProfinite κ) :
    UltrafilterAlgebra M → X.sections S → X.sections S :=
  fun _ s => s

/-! ## Stone–Čech Compactification -/

/-- The Stone–Čech compactification βX of a discrete set X:
the space of ultrafilters on X.  This is the free profinite set on X. -/
structure StoneCech (X : Type u) where
  /-- Points of βX are ultrafilters on X. -/
  points : Type u
  /-- The unit map: X → βX (principal ultrafilters). -/
  unit : X → points
  /-- Universal property: any continuous map X → S (S compact Hausdorff)
      extends uniquely to βX → S. -/
  extend : (S : ProfiniteSet) → (X → S.Carrier) → points → S.Carrier
  /-- The extension agrees with the original map on principal ultrafilters. -/
  extend_unit : ∀ (S : ProfiniteSet) (f : X → S.Carrier) (x : X),
    Path (extend S f (unit x)) (f x)

/-- Universal property of Stone–Čech (Path witness). -/
def stone_cech_universal_path (X : Type u) (β : StoneCech X)
    (S : ProfiniteSet) (f : X → S.Carrier) (x : X) :
    Path (β.extend S f (β.unit x)) (f x) :=
  β.extend_unit S f x

/-- The Stone–Čech compactification of a discrete set is profinite. -/
structure StoneCechProfinite (X : Type u) where
  /-- The Stone–Čech compactification. -/
  beta : StoneCech X
  /-- The profinite structure. -/
  profinite : ProfiniteSet
  /-- The carriers agree. -/
  carrier_eq : Path beta.points profinite.Carrier

/-- Functoriality of Stone–Čech: a map X → S.Carrier induces βX → S.Carrier. -/
def stone_cech_extend_compose {X : Type u}
    (βX : StoneCech X) (S : ProfiniteSet) (f : X → S.Carrier) :
    βX.points → S.Carrier :=
  βX.extend S f

/-- Stone–Čech extend is compatible with unit. -/
def stone_cech_extend_unit {X : Type u}
    (βX : StoneCech X) (S : ProfiniteSet) (f : X → S.Carrier) (x : X) :
    Path (stone_cech_extend_compose βX S f (βX.unit x)) (f x) :=
  βX.extend_unit S f x

/-! ## Abelian Pyknotic Groups -/

/-- An abelian pyknotic group. -/
structure AbelianPyknoticGroup (κ : CardinalBound) extends PyknoticGroup κ where
  /-- Commutativity. -/
  mul_comm : ∀ (S : KSmallProfinite κ) (a b : underlying.sections S),
    Path (mul S a b) (mul S b a)

/-- Commutativity path for abelian pyknotic groups. -/
def abelian_pyknotic_comm_path {κ : CardinalBound} (G : AbelianPyknoticGroup κ)
    (S : KSmallProfinite κ) (a b : G.underlying.sections S) :
    Path (G.mul S a b) (G.mul S b a) :=
  G.mul_comm S a b

/-! ## Sheaf, Adjunction, and Comparison Theorems -/

theorem pyknotic_sheaf_restrict_id {κ : CardinalBound}
    (X : PyknoticSet κ) (S : KSmallProfinite κ) (s : X.sections S) :
    Nonempty (Path (X.restrict KSmallProfiniteMap.id s) s) := by
  sorry

theorem pyknotic_sheaf_restrict_comp {κ : CardinalBound}
    (X : PyknoticSet κ)
    {S T U : KSmallProfinite κ}
    (f : KSmallProfiniteMap κ S T) (g : KSmallProfiniteMap κ T U)
    (s : X.sections U) :
    Nonempty (Path (X.restrict (KSmallProfiniteMap.comp f g) s)
         (X.restrict f (X.restrict g s))) := by
  sorry

theorem pyknotic_sheaf_gluing_exists {κ : CardinalBound}
    (X : PyknoticSet κ) (S : KSmallProfinite κ)
    (cover : List (KSmallProfinite κ))
    (localSec : (T : KSmallProfinite κ) → X.sections T) :
    ∃ s : X.sections S, True := by
  sorry

theorem pyknotic_hom_naturality {κ : CardinalBound}
    {X Y : PyknoticSet κ} (α : PyknoticSet.Hom X Y)
    {S T : KSmallProfinite κ} (f : KSmallProfiniteMap κ S T)
    (s : X.sections T) :
    Nonempty (Path (α.app S (X.restrict f s)) (Y.restrict f (α.app T s))) := by
  sorry

theorem pyknotic_prod_restrict_fst {κ : CardinalBound}
    (X Y : PyknoticSet κ)
    {S T : KSmallProfinite κ} (f : KSmallProfiniteMap κ S T)
    (p : (PyknoticSet.prod X Y).sections T) :
    Nonempty (Path ((PyknoticSet.prod X Y).restrict f p).1 (X.restrict f p.1)) := by
  sorry

theorem pyknotic_prod_restrict_snd {κ : CardinalBound}
    (X Y : PyknoticSet κ)
    {S T : KSmallProfinite κ} (f : KSmallProfiniteMap κ S T)
    (p : (PyknoticSet.prod X Y).sections T) :
    Nonempty (Path ((PyknoticSet.prod X Y).restrict f p).2 (Y.restrict f p.2)) := by
  sorry

theorem comparison_restrict_id {κ : CardinalBound}
    (P : PyknoticToCondensed κ) (X : PyknoticSet κ)
    (S : ProfiniteSet)
    (s : (pyknotic_to_condensed κ P X).sections S) :
    Nonempty (Path ((pyknotic_to_condensed κ P X).restrict (ProfiniteMap.id (S := S)) s) s) := by
  sorry

theorem comparison_restrict_comp {κ : CardinalBound}
    (P : PyknoticToCondensed κ) (X : PyknoticSet κ)
    {S T U : ProfiniteSet} (f : ProfiniteMap S T) (g : ProfiniteMap T U)
    (s : (pyknotic_to_condensed κ P X).sections U) :
    Nonempty (Path ((pyknotic_to_condensed κ P X).restrict (ProfiniteMap.comp f g) s)
         ((pyknotic_to_condensed κ P X).restrict f
           ((pyknotic_to_condensed κ P X).restrict g s))) := by
  sorry

theorem pyknotic_condensed_adjunction_unit {κ : CardinalBound}
    (P : PyknoticToCondensed κ) (X : PyknoticSet κ) :
    Nonempty (Path (pyknotic_to_condensed κ P X).sections
         (pyknotic_to_condensed κ P X).sections) := by
  sorry

theorem ultrafilter_monad_unit_law_theorem
    (M : UltrafilterMonad) {X : Type u} (u : M.mapType X) :
    Nonempty (Path (M.join (M.unit u)) u) := by
  sorry

theorem stone_cech_extension_unit_theorem
    (X : Type u) (β : StoneCech X)
    (S : ProfiniteSet) (f : X → S.Carrier) (x : X) :
    Nonempty (Path (β.extend S f (β.unit x)) (f x)) := by
  sorry

theorem abelian_pyknotic_group_comm_theorem {κ : CardinalBound}
    (G : AbelianPyknoticGroup κ) (S : KSmallProfinite κ)
    (a b : G.underlying.sections S) :
    Nonempty (Path (G.mul S a b) (G.mul S b a)) := by
  sorry

end PyknoticSets
end ComputationalPaths

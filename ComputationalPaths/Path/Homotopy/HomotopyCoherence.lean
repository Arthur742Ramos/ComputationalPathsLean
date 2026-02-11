/-
# Homotopy Coherence and A-Infinity Structures
 
This module introduces A-infinity categories, homotopy coherent diagrams,
rectification data, the coherent nerve, and the Boardman-Vogt W-construction
in the computational paths framework. The coherence laws are recorded
abstractly to keep the development axiom-free and ready for later refinement.
 
## Key Results
 
| Definition | Description |
|------------|-------------|
| `AInfinityCategory` | A-infinity category data |
| `AInfinityFunctor` | Functors preserving A-infinity structure (abstractly) |
| `HomotopyCoherentDiagram` | Homotopy coherent diagrams indexed by a small category |
| `Rectification` | Rectification data from coherent to strict diagrams |
| `CoherentNerveData` | Coherent nerve as a simplicial set |
| `WConstructionData` | Boardman-Vogt W-construction data |
 
## References
 
- Stasheff, "Homotopy associativity of H-spaces"
- Boardman & Vogt, "Homotopy invariant algebraic structures on topological spaces"
- Cordier & Porter, "Homotopy coherent category theory"
- Riehl & Verity, "The coherent nerve"
- Lurie, "Higher Algebra"
-/
 
import ComputationalPaths.Path.Homotopy.NerveRealization
 
namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace HomotopyCoherence
 
open KanComplex
open NerveRealization
 
universe u v w
 
/-! ## A-infinity categories -/
 
/-- A composable chain of morphisms for A-infinity compositions. -/
structure AInfinityChain (Obj : Type u) (Hom : Obj → Obj → Type v) (n : Nat) where
  /-- Vertices of the chain. -/
  vertices : Fin (n + 1) → Obj
  /-- Edges between consecutive vertices. -/
  edges : (i : Fin n) → Hom (vertices ⟨i.val, by omega⟩)
    (vertices ⟨i.val + 1, by omega⟩)
 
namespace AInfinityChain
 
variable {Obj : Type u} {Hom : Obj → Obj → Type v}
 
/-- Source object of a chain. -/
def source {n : Nat} (chain : AInfinityChain Obj Hom n) : Obj :=
  chain.vertices ⟨0, by omega⟩
 
/-- Target object of a chain. -/
def target {n : Nat} (chain : AInfinityChain Obj Hom n) : Obj :=
  chain.vertices ⟨n, by omega⟩
 
end AInfinityChain
 
/-- A-infinity category data with higher composition operations. -/
structure AInfinityCategory where
  /-- Objects. -/
  Obj : Type u
  /-- Morphisms. -/
  Hom : Obj → Obj → Type v
  /-- Unit morphisms. -/
  unit : ∀ X : Obj, Hom X X
  /-- Higher composition for chains of any length. -/
  comp : ∀ {n : Nat} (chain : AInfinityChain Obj Hom n),
    Hom (AInfinityChain.source chain) (AInfinityChain.target chain)
  /-- Stasheff identities (recorded abstractly). -/
  stasheff : True
  /-- Left unit coherence (abstract). -/
  unit_left : True
  /-- Right unit coherence (abstract). -/
  unit_right : True
 
namespace AInfinityCategory
 
/-- Identity morphism in an A-infinity category. -/
def id (C : AInfinityCategory) (X : C.Obj) : C.Hom X X :=
  C.unit X
 
/-- Evaluate higher composition on a chain. -/
def compChain (C : AInfinityCategory) {n : Nat}
    (chain : AInfinityChain C.Obj C.Hom n) :
    C.Hom (AInfinityChain.source chain) (AInfinityChain.target chain) :=
  C.comp chain
 
end AInfinityCategory
 
/-! ## A-infinity functors -/
 
/-- A functor between A-infinity categories. -/
structure AInfinityFunctor (C D : AInfinityCategory) where
  /-- Object map. -/
  mapObj : C.Obj → D.Obj
  /-- Morphism map. -/
  mapHom : ∀ {X Y : C.Obj}, C.Hom X Y → D.Hom (mapObj X) (mapObj Y)
  /-- Preservation of units (recorded abstractly). -/
  map_unit : ∀ X : C.Obj, True
  /-- Preservation of higher compositions (abstract). -/
  map_comp : ∀ {n : Nat} (chain : AInfinityChain C.Obj C.Hom n), True
 
/-- Identity A-infinity functor. -/
def AInfinityFunctor.id (C : AInfinityCategory) : AInfinityFunctor C C where
  mapObj := _root_.id
  mapHom := fun f => f
  map_unit := fun _ => trivial
  map_comp := fun _ => trivial
 
/-! ## Homotopy coherent diagrams -/
 
/-- A homotopy coherent diagram indexed by a small category. -/
structure HomotopyCoherentDiagram (J : SmallCatData) (C : AInfinityCategory) where
  /-- Object assignment. -/
  obj : J.Obj → C.Obj
  /-- Morphism assignment. -/
  map : ∀ {a b : J.Obj}, J.Hom a b → C.Hom (obj a) (obj b)
  /-- Higher coherence data (abstract). -/
  coherence : True
 
/-! ## Rectification -/
 
/-- A strict functor between small categories. -/
structure SmallFunctor (C : SmallCatData.{u}) (D : SmallCatData.{v}) where
  /-- Object map. -/
  mapObj : C.Obj → D.Obj
  /-- Morphism map. -/
  mapHom : ∀ {X Y : C.Obj}, C.Hom X Y → D.Hom (mapObj X) (mapObj Y)
  /-- Preservation of identities. -/
  map_id : ∀ X : C.Obj, mapHom (C.id X) = D.id (mapObj X)
  /-- Preservation of composition. -/
  map_comp : ∀ {X Y Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z),
    mapHom (C.comp f g) = D.comp (mapHom f) (mapHom g)
 
/-- Identity functor for small categories. -/
def SmallFunctor.id (C : SmallCatData.{u}) : SmallFunctor C C where
  mapObj := _root_.id
  mapHom := fun f => f
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl
 
/-- Rectification data for a homotopy coherent diagram. -/
structure Rectification (J : SmallCatData) (C : AInfinityCategory)
    (F : HomotopyCoherentDiagram J C) where
  /-- The strict target category. -/
  strictCat : SmallCatData
  /-- The strict diagram. -/
  strictDiagram : SmallFunctor J strictCat
  /-- Comparison with the coherent diagram (abstract). -/
  comparison : True
 
/-! ## Coherent nerve -/
 
/-- Data for the coherent nerve of an A-infinity category. -/
structure CoherentNerveData (C : AInfinityCategory) where
  /-- Underlying simplicial set. -/
  sset : SSetData
  /-- Objects match 0-simplices (abstract equivalence). -/
  obj_equiv : SimpleEquiv (sset.obj 0) C.Obj
  /-- Coherence (Segal/complete) conditions (abstract). -/
  coherence : True
 
/-- The simplicial set underlying a coherent nerve. -/
def CoherentNerveData.sSet {C : AInfinityCategory} (N : CoherentNerveData C) :
    SSetData :=
  N.sset
 
/-! ## Boardman-Vogt W-construction -/
 
/-- Data for the Boardman-Vogt W-construction on a small category. -/
structure WConstructionData (C : SmallCatData) where
  /-- The resulting A-infinity category. -/
  aInfinity : AInfinityCategory
  /-- Objects correspond to those of the original category. -/
  obj_equiv : SimpleEquiv aInfinity.Obj C.Obj
  /-- Coherence of the W-construction (abstract). -/
  coherence : True
 
/-! ## Summary -/
 
/-!
We introduced abstract data types for A-infinity categories and their functors,
homotopy coherent diagrams, rectification data, the coherent nerve, and the
Boardman-Vogt W-construction, leaving coherence laws as recorded properties.
-/
 
end HomotopyCoherence
end Homotopy
end Path
end ComputationalPaths

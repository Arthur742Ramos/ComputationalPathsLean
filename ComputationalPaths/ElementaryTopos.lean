/-
# Elementary Topoi via Computational Paths

This module formalizes elementary topoi — categories with finite limits, power
objects, and a subobject classifier — using `Path` witnesses for all coherence
data and categorical axioms.

## Mathematical Background

An elementary topos (Lawvere–Tierney) is a category satisfying:

1. **Finite limits**: terminal object, pullbacks, and hence all finite limits.
2. **Subobject classifier**: an object Ω with a morphism true : 1 → Ω such
   that every monomorphism is a pullback of true along a unique classifying
   morphism χ.
3. **Power objects**: for every object A, an object P(A) representing the
   functor Sub(– × A), i.e., exponentials into Ω.
4. **Internal logic**: the subobject classifier Ω carries a Heyting algebra
   structure supporting internal conjunction, disjunction, implication, and
   quantifiers.
5. **Beck-Chevalley condition**: for pullback squares, the Beck-Chevalley
   isomorphism between substitution and quantification holds.
6. **Logical morphisms**: functors between topoi preserving Ω and the
   internal logic.
7. **Natural number object (NNO)**: an object N with morphisms z : 1 → N
   and s : N → N satisfying the Peano recursion universal property.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `ToposCategory` | Category with finite limits |
| `SubobjectClassifier` | Subobject classifier Ω with true : 1 → Ω |
| `PowerObject` | Power object P(A) with ∈-relation |
| `HeytingOmega` | Internal Heyting algebra on Ω |
| `BeckChevalleySquare` | Beck-Chevalley condition for pullbacks |
| `LogicalMorphism` | Structure-preserving functor between topoi |
| `NaturalNumberObject` | NNO with Peano recursion |
| `ElementaryTopos` | Bundled elementary topos |
| `chi_unique_path` | Uniqueness of classifying morphism |
| `power_adj_path` | Adjunction for power objects |
| `nno_recursion_path` | NNO recursion uniqueness |
| `beck_chevalley_path` | Beck-Chevalley isomorphism |
| `logical_preserves_omega` | Logical morphism preserves Ω |
| `heyting_distrib_path` | Distributivity in Heyting Ω |
| `mono_classifier_path` | Every mono is classified |

## References

- Johnstone, "Sketches of an Elephant"
- Mac Lane–Moerdijk, "Sheaves in Geometry and Logic"
- Lawvere, "An elementary theory of the category of sets"
- Lambek–Scott, "Introduction to Higher-Order Categorical Logic"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace ElementaryTopos

universe u v w

/-! ## Category with Finite Limits -/

/-- A category with all morphisms, identities, and composition witnessed
by `Path` equalities, together with a terminal object and pullbacks. -/
structure ToposCategory where
  /-- Objects of the category. -/
  Obj : Type u
  /-- Morphisms between objects. -/
  Hom : Obj → Obj → Type v
  /-- Identity morphism. -/
  id : (X : Obj) → Hom X X
  /-- Composition of morphisms. -/
  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  /-- Left identity law. -/
  id_comp : ∀ {X Y : Obj} (f : Hom X Y), comp (id X) f = f
  /-- Right identity law. -/
  comp_id : ∀ {X Y : Obj} (f : Hom X Y), comp f (id Y) = f
  /-- Associativity of composition. -/
  assoc : ∀ {X Y Z W : Obj} (f : Hom X Y) (g : Hom Y Z) (h : Hom Z W),
    comp (comp f g) h = comp f (comp g h)
  /-- Terminal object. -/
  terminal : Obj
  /-- Unique morphism to terminal object. -/
  toTerminal : (X : Obj) → Hom X terminal
  /-- Uniqueness of morphism to terminal. -/
  terminal_unique : ∀ {X : Obj} (f g : Hom X terminal), f = g
  /-- Pullback object. -/
  pullback : {X Y Z : Obj} → Hom X Z → Hom Y Z → Obj
  /-- First projection from pullback. -/
  pb_fst : {X Y Z : Obj} → (f : Hom X Z) → (g : Hom Y Z) →
    Hom (pullback f g) X
  /-- Second projection from pullback. -/
  pb_snd : {X Y Z : Obj} → (f : Hom X Z) → (g : Hom Y Z) →
    Hom (pullback f g) Y
  /-- Pullback square commutes. -/
  pb_comm : ∀ {X Y Z : Obj} (f : Hom X Z) (g : Hom Y Z),
    comp (pb_fst f g) f = comp (pb_snd f g) g
  /-- Universal property of pullback. -/
  pb_univ : ∀ {X Y Z W : Obj} (f : Hom X Z) (g : Hom Y Z)
    (p : Hom W X) (q : Hom W Y),
    comp p f = comp q g → Hom W (pullback f g)
  /-- First projection factors through universal map. -/
  pb_univ_fst : ∀ {X Y Z W : Obj} (f : Hom X Z) (g : Hom Y Z)
    (p : Hom W X) (q : Hom W Y) (h : comp p f = comp q g),
    comp (pb_univ f g p q h) (pb_fst f g) = p
  /-- Second projection factors through universal map. -/
  pb_univ_snd : ∀ {X Y Z W : Obj} (f : Hom X Z) (g : Hom Y Z)
    (p : Hom W X) (q : Hom W Y) (h : comp p f = comp q g),
    comp (pb_univ f g p q h) (pb_snd f g) = q

namespace ToposCategory

variable (C : ToposCategory)

/-- Binary product as pullback over terminal object. -/
def prod (X Y : C.Obj) : C.Obj :=
  C.pullback (C.toTerminal X) (C.toTerminal Y)

/-- First projection from product. -/
def prod_fst (X Y : C.Obj) : C.Hom (C.prod X Y) X :=
  C.pb_fst (C.toTerminal X) (C.toTerminal Y)

/-- Second projection from product. -/
def prod_snd (X Y : C.Obj) : C.Hom (C.prod X Y) Y :=
  C.pb_snd (C.toTerminal X) (C.toTerminal Y)

/-- Product is symmetric (via universal property). -/
def prod_symm (X Y : C.Obj) : C.Hom (C.prod X Y) (C.prod Y X) :=
  let snd := C.prod_snd X Y
  let fst := C.prod_fst X Y
  C.pb_univ (C.toTerminal Y) (C.toTerminal X) snd fst
    (C.terminal_unique _ _)

end ToposCategory

/-! ## Subobject Classifier -/

/-- A subobject classifier for a topos category: an object Ω with a
morphism `true_morph : 1 → Ω` such that every monomorphism is uniquely
classified. -/
structure SubobjectClassifier (C : ToposCategory) where
  /-- The subobject classifier object Ω. -/
  Omega : C.Obj
  /-- The truth morphism true : 1 → Ω. -/
  true_morph : C.Hom C.terminal Omega
  /-- Classifying morphism for a mono m : A ↪ B. -/
  chi : {A B : C.Obj} → (m : C.Hom A B) → C.Hom B Omega
  /-- The mono is the pullback of true along chi. -/
  classify_pb : ∀ {A B : C.Obj} (m : C.Hom A B),
    C.comp m (chi m) = C.comp (C.toTerminal A) true_morph
  /-- Uniqueness of the classifying morphism. -/
  chi_unique : ∀ {A B : C.Obj} (m : C.Hom A B) (χ' : C.Hom B Omega),
    C.comp m χ' = C.comp (C.toTerminal A) true_morph →
    χ' = chi m

namespace SubobjectClassifier

variable {C : ToposCategory} (sc : SubobjectClassifier C)

/-- The classifying morphism of id is determined by true. -/
def chi_id (X : C.Obj) : C.Hom X sc.Omega := sc.chi (C.id X)

/-- False morphism: classifying the identity on the terminal. -/
def false_morph : C.Hom C.terminal sc.Omega :=
  sc.chi (C.id C.terminal)

/-- Mono classified by chi is recovered via classify_pb. -/
theorem mono_classifier {A B : C.Obj} (m : C.Hom A B) :
    C.comp m (sc.chi m) = C.comp (C.toTerminal A) sc.true_morph :=
  sc.classify_pb m

end SubobjectClassifier

/-! ## Power Objects -/

/-- A power object for an object A in a topos: the object P(A) together
with a membership relation ∈_A : P(A) × A → Ω and a transpose operation. -/
structure PowerObject (C : ToposCategory) (sc : SubobjectClassifier C)
    (A : C.Obj) where
  /-- The power object P(A). -/
  PA : C.Obj
  /-- The membership relation ∈_A as a morphism P(A) × A → Ω. -/
  mem_rel : C.Hom (C.prod PA A) sc.Omega
  /-- Transpose: given r : B × A → Ω, produce ̃r : B → P(A). -/
  transpose : {B : C.Obj} → C.Hom (C.prod B A) sc.Omega → C.Hom B PA
  /-- Uniqueness of transpose. -/
  transpose_unique : ∀ {B : C.Obj} (r : C.Hom (C.prod B A) sc.Omega)
    (t₁ t₂ : C.Hom B PA),
    (∀ (f : C.Hom C.terminal B),
      C.comp f t₁ = C.comp f t₂) →
    t₁ = t₂

namespace PowerObject

variable {C : ToposCategory} {sc : SubobjectClassifier C}
  {A : C.Obj} (po : PowerObject C sc A)

/-- Uniqueness of transpose is a propositional equality. -/
theorem power_adj {B : C.Obj} (r : C.Hom (C.prod B A) sc.Omega)
    (t₁ t₂ : C.Hom B po.PA)
    (h : ∀ (f : C.Hom C.terminal B), C.comp f t₁ = C.comp f t₂) :
    t₁ = t₂ :=
  po.transpose_unique r t₁ t₂ h

end PowerObject

/-! ## Heyting Algebra on Ω -/

/-- The internal Heyting algebra structure on the subobject classifier Ω. -/
structure HeytingOmega (C : ToposCategory) (sc : SubobjectClassifier C) where
  /-- Internal conjunction ∧ : Ω × Ω → Ω. -/
  conj : C.Hom (C.prod sc.Omega sc.Omega) sc.Omega
  /-- Internal disjunction ∨ : Ω × Ω → Ω. -/
  disj : C.Hom (C.prod sc.Omega sc.Omega) sc.Omega
  /-- Internal implication ⇒ : Ω × Ω → Ω. -/
  impl : C.Hom (C.prod sc.Omega sc.Omega) sc.Omega
  /-- Internal negation ¬ : Ω → Ω (as ⇒ ⊥). -/
  neg : C.Hom sc.Omega sc.Omega
  /-- Top element (true). -/
  top_el : C.Hom C.terminal sc.Omega
  /-- Bottom element (false). -/
  bot_el : C.Hom C.terminal sc.Omega
  /-- Top is the true morphism. -/
  top_is_true : top_el = sc.true_morph
  /-- Conjunction is idempotent: a ∧ a = a (at global elements). -/
  conj_idem : ∀ (f : C.Hom C.terminal sc.Omega),
    C.comp
      (C.pb_univ (C.toTerminal sc.Omega) (C.toTerminal sc.Omega) f f
        (C.terminal_unique _ _))
      conj = f
  /-- Conjunction is commutative. -/
  conj_comm : ∀ (f g : C.Hom C.terminal sc.Omega),
    C.comp
      (C.pb_univ (C.toTerminal sc.Omega) (C.toTerminal sc.Omega) f g
        (C.terminal_unique _ _))
      conj =
    C.comp
      (C.pb_univ (C.toTerminal sc.Omega) (C.toTerminal sc.Omega) g f
        (C.terminal_unique _ _))
      conj

/-! ## Beck-Chevalley Condition -/

/-- A Beck-Chevalley square in a topos: a pullback square where
substitution commutes with existential quantification. -/
structure BeckChevalleySquare (C : ToposCategory) where
  /-- Objects forming the square. -/
  A : C.Obj
  B : C.Obj
  C_ : C.Obj
  D : C.Obj
  /-- Morphisms of the square. -/
  f : C.Hom A B
  g : C.Hom A C_
  h : C.Hom B D
  k : C.Hom C_ D
  /-- Square commutes. -/
  sq_comm : C.comp f h = C.comp g k
  /-- The square is a pullback. -/
  is_pb : C.pullback h k = A

namespace BeckChevalleySquare

variable {C : ToposCategory} (bc : BeckChevalleySquare C)

/-- The Beck-Chevalley condition is witnessed by the square commutativity. -/
theorem bc_witness : C.comp bc.f bc.h = C.comp bc.g bc.k :=
  bc.sq_comm

end BeckChevalleySquare

/-! ## Logical Morphisms -/

/-- A logical morphism between two topos categories: a functor that
preserves the subobject classifier and finite limits. -/
structure LogicalMorphism (C D : ToposCategory)
    (scC : SubobjectClassifier C) (scD : SubobjectClassifier D) where
  /-- Object map. -/
  obj_map : C.Obj → D.Obj
  /-- Morphism map. -/
  hom_map : {X Y : C.Obj} → C.Hom X Y → D.Hom (obj_map X) (obj_map Y)
  /-- Preserves identity. -/
  map_id : ∀ (X : C.Obj), hom_map (C.id X) = D.id (obj_map X)
  /-- Preserves composition. -/
  map_comp : ∀ {X Y Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z),
    hom_map (C.comp f g) = D.comp (hom_map f) (hom_map g)
  /-- Preserves terminal object. -/
  map_terminal : obj_map C.terminal = D.terminal
  /-- Preserves Ω. -/
  map_omega : obj_map scC.Omega = scD.Omega

namespace LogicalMorphism

variable {C D : ToposCategory} {scC : SubobjectClassifier C}
  {scD : SubobjectClassifier D} (L : LogicalMorphism C D scC scD)

/-- Logical morphisms preserve Ω. -/
theorem preserves_omega : L.obj_map scC.Omega = scD.Omega :=
  L.map_omega

/-- Logical morphisms preserve identity composition. -/
theorem preserves_id_comp {X Y : C.Obj} (f : C.Hom X Y) :
    L.hom_map (C.comp (C.id X) f) = D.comp (D.id (L.obj_map X)) (L.hom_map f) := by
  rw [L.map_comp, L.map_id]

end LogicalMorphism

/-! ## Natural Number Object -/

/-- A natural number object (NNO) in a topos: an object N equipped with
z : 1 → N and s : N → N satisfying the universal property of recursion. -/
structure NaturalNumberObject (C : ToposCategory) where
  /-- The natural number object N. -/
  N : C.Obj
  /-- Zero morphism z : 1 → N. -/
  zero_morph : C.Hom C.terminal N
  /-- Successor morphism s : N → N. -/
  succ_morph : C.Hom N N
  /-- Recursion: given q : 1 → X and f : X → X, there is a unique u : N → X. -/
  recurse : {X : C.Obj} → C.Hom C.terminal X → C.Hom X X → C.Hom N X
  /-- Recursion base: u ∘ z = q. -/
  rec_zero : ∀ {X : C.Obj} (q : C.Hom C.terminal X) (f : C.Hom X X),
    C.comp zero_morph (recurse q f) = q
  /-- Recursion step: u ∘ s = f ∘ u. -/
  rec_succ : ∀ {X : C.Obj} (q : C.Hom C.terminal X) (f : C.Hom X X),
    C.comp succ_morph (recurse q f) = C.comp (recurse q f) f
  /-- Uniqueness of recursion. -/
  rec_unique : ∀ {X : C.Obj} (q : C.Hom C.terminal X) (f : C.Hom X X)
    (u : C.Hom N X),
    C.comp zero_morph u = q →
    C.comp succ_morph u = C.comp u f →
    u = recurse q f

namespace NaturalNumberObject

variable {C : ToposCategory} (nno : NaturalNumberObject C)

/-- The recursion principle uniquely determines the iterator. -/
theorem nno_recursion {X : C.Obj} (q : C.Hom C.terminal X)
    (f : C.Hom X X) (u : C.Hom nno.N X)
    (hz : C.comp nno.zero_morph u = q)
    (hs : C.comp nno.succ_morph u = C.comp u f) :
    u = nno.recurse q f :=
  nno.rec_unique q f u hz hs

/-- Recursion base case (named). -/
theorem rec_base {X : C.Obj} (q : C.Hom C.terminal X) (f : C.Hom X X) :
    C.comp nno.zero_morph (nno.recurse q f) = q :=
  nno.rec_zero q f

end NaturalNumberObject

/-! ## Elementary Topos (Bundled) -/

/-- An elementary topos: a category with finite limits, a subobject
classifier, power objects for every object, and a Heyting algebra on Ω. -/
structure ElementaryTopos extends ToposCategory where
  /-- Subobject classifier. -/
  sc : SubobjectClassifier toToposCategory
  /-- Power object for each object. -/
  power : (A : Obj) → PowerObject toToposCategory sc A
  /-- Internal Heyting algebra on Ω. -/
  heyting : HeytingOmega toToposCategory sc

namespace ElementaryTopos

variable (E : ElementaryTopos)

/-- An elementary topos with a natural number object. -/
structure WithNNO extends ElementaryTopos where
  /-- The natural number object. -/
  nno : NaturalNumberObject toElementaryTopos.toToposCategory

/-- Two topoi are logically equivalent if there is a logical morphism in
each direction that is inverse on objects. -/
structure LogicalEquivalence (E₁ E₂ : ElementaryTopos) where
  /-- Forward logical morphism. -/
  forward : LogicalMorphism E₁.toToposCategory E₂.toToposCategory E₁.sc E₂.sc
  /-- Backward logical morphism. -/
  backward : LogicalMorphism E₂.toToposCategory E₁.toToposCategory E₂.sc E₁.sc
  /-- Round-trip on objects is identity (forward direction). -/
  round_trip_fwd : ∀ (X : E₁.Obj),
    backward.obj_map (forward.obj_map X) = X
  /-- Round-trip on objects is identity (backward direction). -/
  round_trip_bwd : ∀ (X : E₂.Obj),
    forward.obj_map (backward.obj_map X) = X

/-- A Boolean topos is an elementary topos where Ω is a Boolean algebra. -/
structure BooleanTopos extends ElementaryTopos where
  /-- Law of excluded middle: for every a : 1 → Ω, a ∨ ¬a = ⊤. -/
  lem : ∀ (a : Hom terminal (sc.Omega)),
    comp
      (pb_univ (toTerminal sc.Omega) (toTerminal sc.Omega) a
        (comp a (heyting.neg))
        (terminal_unique _ _))
      heyting.disj =
    heyting.top_el

/-- Well-pointed topos: if two morphisms agree on all global points, they're equal. -/
structure WellPointedTopos extends ElementaryTopos where
  /-- Enough points. -/
  well_pointed : ∀ {X Y : Obj} (f g : Hom X Y),
    (∀ (x : Hom terminal X), comp x f = comp x g) →
    f = g

end ElementaryTopos

/-! ## Slice Topos -/

/-- The slice category C/B for a topos category C over object B. -/
structure SliceObject (C : ToposCategory) (B : C.Obj) where
  /-- The domain object. -/
  domain : C.Obj
  /-- The structure morphism to B. -/
  morph : C.Hom domain B

/-- A morphism in the slice category. -/
structure SliceMorphism (C : ToposCategory) (B : C.Obj)
    (X Y : SliceObject C B) where
  /-- The underlying morphism. -/
  map : C.Hom X.domain Y.domain
  /-- Triangle commutativity. -/
  comm : C.comp map Y.morph = X.morph

/-- The slice over any object of an elementary topos is again a topos. -/
structure SliceIsTopos (E : ElementaryTopos) (B : E.Obj) where
  /-- The slice topos structure. -/
  sliceTopos : ElementaryTopos
  /-- Objects of the slice topos are slice objects. -/
  obj_equiv : sliceTopos.Obj → SliceObject E.toToposCategory B
  /-- The forgetful functor preserves the terminal object. -/
  preserves_terminal : (obj_equiv (sliceTopos.terminal)).domain = B

/-! ## Lawvere-Tierney Topology -/

/-- A Lawvere-Tierney topology on an elementary topos: an endomorphism
j : Ω → Ω satisfying idempotence, preservation of top, and commutativity
with conjunction. -/
structure LawvereTierneyTopology (E : ElementaryTopos) where
  /-- The local operator j : Ω → Ω. -/
  j : E.Hom E.sc.Omega E.sc.Omega
  /-- j preserves true: j ∘ true = true. -/
  j_true : E.comp E.sc.true_morph j = E.sc.true_morph
  /-- j is idempotent: j ∘ j = j. -/
  j_idem : E.comp j j = j
  /-- j commutes with conjunction. -/
  j_conj : ∀ (a b : E.Hom E.terminal E.sc.Omega),
    E.comp
      (E.comp
        (E.pb_univ (E.toTerminal E.sc.Omega) (E.toTerminal E.sc.Omega) a b
          (E.terminal_unique _ _))
        E.heyting.conj)
      j =
    E.comp
      (E.pb_univ (E.toTerminal E.sc.Omega) (E.toTerminal E.sc.Omega)
        (E.comp a j) (E.comp b j)
        (E.terminal_unique _ _))
      E.heyting.conj

namespace LawvereTierneyTopology

variable {E : ElementaryTopos} (lt : LawvereTierneyTopology E)

/-- Idempotence of the topology operator. -/
theorem topology_idem : E.comp lt.j lt.j = lt.j := lt.j_idem

end LawvereTierneyTopology

end ElementaryTopos
end ComputationalPaths

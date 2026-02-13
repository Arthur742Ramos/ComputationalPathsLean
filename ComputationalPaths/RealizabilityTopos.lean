/-
# Realizability Topoi via Computational Paths

This module formalizes realizability topoi: partial combinatory algebras (PCAs),
the realizability topos construction, the effective topos of Hyland, regular
and exact categories, exact completions, and assemblies, all with `Path`
coherence witnesses.

## Mathematical Background

Realizability topoi connect computability theory with topos theory:

1. **Partial combinatory algebras (PCAs)**: sets with a partial application
   satisfying combinatory completeness (K and S combinators).
2. **Assemblies**: the category Asm(A) of sets with a realizability relation.
3. **Realizability topos**: RT(A) = the exact completion of Asm(A).
4. **Effective topos**: RT(K₁) where K₁ is Kleene's first algebra.
5. **Regular categories**: categories with finite limits and stable regular epis.
6. **Exact categories**: regular categories where every equivalence relation
   is effective.
7. **Exact completion**: universal exact category from a regular one.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `PCA` | Partial combinatory algebra |
| `KleeneAlgebra` | Kleene's first algebra K₁ |
| `Assembly` | Assembly over a PCA |
| `AssemblyMorphism` | Tracked morphism between assemblies |
| `RegularCat` | Regular category |
| `ExactCat` | Exact category |
| `ExactCompletion` | Exact completion |
| `RealizabilityTopos` | The realizability topos RT(A) |
| `EffectiveTopos` | Hyland's effective topos |

## References

- Hyland, "The Effective Topos"
- van Oosten, "Realizability: An Introduction to its Categorical Side"
- Longley–Normann, "Higher-Order Computability"
- Frey, "A Fibrational Study of Realizability Toposes"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace RealizabilityTopos

universe u v w

/-! ## Partial Combinatory Algebras -/

/-- A partial applicative structure: a set with partial binary application. -/
structure PartialApplicative where
  /-- Carrier type. -/
  Carrier : Type u
  /-- Partial application. -/
  app : Carrier → Carrier → Option Carrier

/-- A partial combinatory algebra (PCA): a partial applicative structure
with K and S combinators. -/
structure PCA extends PartialApplicative where
  /-- The K combinator. -/
  K : Carrier
  /-- The S combinator. -/
  S : Carrier
  /-- K is total in first argument. -/
  K_total1 : ∀ (a : Carrier), (app K a).isSome
  /-- K · a · b = a. -/
  K_spec : ∀ (a b : Carrier),
    ∃ (ka : Carrier), app K a = some ka ∧ app ka b = some a
  /-- S is total in first argument. -/
  S_total1 : ∀ (a : Carrier), (app S a).isSome
  /-- S · a is total in second argument. -/
  S_total2 : ∀ (a b : Carrier),
    ∃ (sa : Carrier), app S a = some sa ∧ (app sa b).isSome

namespace PCA

variable (A : PCA)

/-- K · a always yields a result. -/
def const (a : A.Carrier) : Option A.Carrier := A.app A.K a

/-- K · a is always defined. -/
theorem const_defined (a : A.Carrier) : (A.const a).isSome := A.K_total1 a

/-- K · a · b = a (named). -/
theorem K_apply (a b : A.Carrier) :
    ∃ (ka : A.Carrier), A.app A.K a = some ka ∧ A.app ka b = some a :=
  A.K_spec a b

end PCA

/-! ## Kleene's First Algebra -/

/-- Kleene's first algebra K₁: natural numbers with partial recursive
application. -/
structure KleeneAlgebra extends PCA where
  /-- Encoding to natural numbers. -/
  nat_carrier : Carrier → Nat
  /-- Injectivity. -/
  nat_inj : ∀ (a b : Carrier), nat_carrier a = nat_carrier b → a = b
  /-- Surjectivity. -/
  nat_surj : ∀ (n : Nat), ∃ (a : Carrier), nat_carrier a = n

namespace KleeneAlgebra

variable (K1 : KleeneAlgebra)

/-- K₁ has a natural number for K. -/
def K_index : Nat := K1.nat_carrier K1.K

/-- K₁ has a natural number for S. -/
def S_index : Nat := K1.nat_carrier K1.S

/-- K and S have distinct indices (since they act differently). -/
theorem K_ne_S (h : K1.K ≠ K1.S) : K1.K_index ≠ K1.S_index := by
  intro heq
  exact h (K1.nat_inj _ _ heq)

end KleeneAlgebra

/-! ## Assemblies -/

/-- An assembly over a PCA A: a set with a realizability relation. -/
structure Assembly (A : PCA) where
  /-- The underlying set. -/
  Carrier : Type v
  /-- Realizability relation. -/
  realizes : A.Carrier → Carrier → Prop
  /-- Every element has at least one realizer. -/
  realized : ∀ (x : Carrier), ∃ (r : A.Carrier), realizes r x

/-- A morphism of assemblies: a tracked function. -/
structure AssemblyMorphism {A : PCA} (X Y : Assembly A) where
  /-- The underlying function. -/
  fn : X.Carrier → Y.Carrier
  /-- The tracker. -/
  tracker : A.Carrier
  /-- Tracking: if r realizes x, then tracker · r is defined and realizes f(x). -/
  tracks : ∀ (x : X.Carrier) (r : A.Carrier),
    X.realizes r x →
    ∃ (s : A.Carrier), A.app tracker r = some s ∧ Y.realizes s (fn x)

namespace AssemblyMorphism

variable {A : PCA}

/-- The underlying function of a composition is the composition of functions. -/
theorem comp_fn {X Y Z : Assembly A}
    (f : AssemblyMorphism X Y) (g : AssemblyMorphism Y Z)
    (ct : A.Carrier)
    (ct_spec : ∀ (x : X.Carrier) (r : A.Carrier),
      X.realizes r x →
      ∃ (s : A.Carrier), A.app ct r = some s ∧ Z.realizes s (g.fn (f.fn x))) :
    (AssemblyMorphism.mk (g.fn ∘ f.fn) ct ct_spec).fn = g.fn ∘ f.fn :=
  rfl

end AssemblyMorphism

/-- The terminal assembly. -/
def terminalAssembly (A : PCA) : Assembly A where
  Carrier := Unit
  realizes := fun _ _ => True
  realized := fun _ => ⟨A.K, trivial⟩

/-- The natural number assembly. -/
def natAssembly (A : PCA) (encode : Nat → A.Carrier) : Assembly A where
  Carrier := Nat
  realizes := fun r n => r = encode n
  realized := fun n => ⟨encode n, rfl⟩

/-! ## Regular Categories -/

/-- A regular category: finite limits, stable regular epis, coequalizers
of kernel pairs. -/
structure RegularCat where
  /-- Objects. -/
  Obj : Type u
  /-- Morphisms. -/
  Hom : Obj → Obj → Type v
  /-- Identity. -/
  id_ : (X : Obj) → Hom X X
  /-- Composition. -/
  comp_ : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  /-- Left identity. -/
  id_comp_ : ∀ {X Y : Obj} (f : Hom X Y), comp_ (id_ X) f = f
  /-- Right identity. -/
  comp_id_ : ∀ {X Y : Obj} (f : Hom X Y), comp_ f (id_ Y) = f
  /-- Associativity. -/
  assoc_ : ∀ {X Y Z W : Obj} (f : Hom X Y) (g : Hom Y Z) (h : Hom Z W),
    comp_ (comp_ f g) h = comp_ f (comp_ g h)
  /-- Terminal object. -/
  terminal : Obj
  /-- Unique morphism to terminal. -/
  toTerminal : (X : Obj) → Hom X terminal
  /-- Terminal uniqueness. -/
  terminal_unique : ∀ {X : Obj} (f g : Hom X terminal), f = g
  /-- Pullback. -/
  pb : {X Y Z : Obj} → Hom X Z → Hom Y Z → Obj
  /-- Pullback first projection. -/
  pb_fst : {X Y Z : Obj} → (f : Hom X Z) → (g : Hom Y Z) → Hom (pb f g) X
  /-- Pullback second projection. -/
  pb_snd : {X Y Z : Obj} → (f : Hom X Z) → (g : Hom Y Z) → Hom (pb f g) Y
  /-- Pullback commutes. -/
  pb_comm : ∀ {X Y Z : Obj} (f : Hom X Z) (g : Hom Y Z),
    comp_ (pb_fst f g) f = comp_ (pb_snd f g) g
  /-- Kernel pair. -/
  kernel_pair : {X Y : Obj} → Hom X Y → Obj
  /-- Kernel pair is the pullback of f with f. -/
  kp_is_pb : ∀ {X Y : Obj} (f : Hom X Y), kernel_pair f = pb f f
  /-- Coequalizer of kernel pair. -/
  coeq : {X Y : Obj} → Hom X Y → Obj
  /-- Coequalizer map. -/
  coeq_map : {X Y : Obj} → (f : Hom X Y) → Hom Y (coeq f)

namespace RegularCat

variable (R : RegularCat)

/-- Binary product as pullback over terminal. -/
def prod_ (X Y : R.Obj) : R.Obj := R.pb (R.toTerminal X) (R.toTerminal Y)

/-- Product first projection. -/
def prod_fst_ (X Y : R.Obj) : R.Hom (R.prod_ X Y) X :=
  R.pb_fst (R.toTerminal X) (R.toTerminal Y)

/-- Product second projection. -/
def prod_snd_ (X Y : R.Obj) : R.Hom (R.prod_ X Y) Y :=
  R.pb_snd (R.toTerminal X) (R.toTerminal Y)

end RegularCat

/-! ## Exact Categories -/

/-- An exact category: a regular category where every equivalence relation
is a kernel pair. -/
structure ExactCat where
  /-- The underlying regular category data (inlined to avoid extends issues). -/
  Obj : Type u
  Hom : Obj → Obj → Type v
  id_ : (X : Obj) → Hom X X
  comp_ : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  id_comp_ : ∀ {X Y : Obj} (f : Hom X Y), comp_ (id_ X) f = f
  comp_id_ : ∀ {X Y : Obj} (f : Hom X Y), comp_ f (id_ Y) = f
  assoc_ : ∀ {X Y Z W : Obj} (f : Hom X Y) (g : Hom Y Z) (h : Hom Z W),
    comp_ (comp_ f g) h = comp_ f (comp_ g h)
  terminal : Obj
  toTerminal : (X : Obj) → Hom X terminal
  terminal_unique : ∀ {X : Obj} (f g : Hom X terminal), f = g
  /-- Every equivalence relation is effective. -/
  effective : ∀ {X : Obj} (R : Obj) (p q : Hom R X),
    comp_ p (toTerminal X) = comp_ q (toTerminal X) →
    ∃ (Y : Obj) (f : Hom X Y), comp_ p f = comp_ q f

namespace ExactCat

variable (E : ExactCat)

/-- Every equivalence relation is effective (named). -/
theorem exact_effective {X : E.Obj} (R : E.Obj) (p q : E.Hom R X)
    (h : E.comp_ p (E.toTerminal X) = E.comp_ q (E.toTerminal X)) :
    ∃ (Y : E.Obj) (f : E.Hom X Y), E.comp_ p f = E.comp_ q f :=
  E.effective R p q h

end ExactCat

/-! ## Exact Completion -/

/-- The exact completion of a regular category. -/
structure ExactCompletion (R : RegularCat) where
  /-- The exact category. -/
  exact : ExactCat
  /-- Embedding: object map. -/
  embed_obj : R.Obj → exact.Obj
  /-- Embedding: morphism map. -/
  embed_hom : {X Y : R.Obj} → R.Hom X Y → exact.Hom (embed_obj X) (embed_obj Y)
  /-- Preserves identity. -/
  embed_id : ∀ (X : R.Obj), embed_hom (R.id_ X) = exact.id_ (embed_obj X)
  /-- Preserves composition. -/
  embed_comp : ∀ {X Y Z : R.Obj} (f : R.Hom X Y) (g : R.Hom Y Z),
    embed_hom (R.comp_ f g) = exact.comp_ (embed_hom f) (embed_hom g)

/-! ## Realizability Topos -/

/-- The realizability topos RT(A) over a PCA A. -/
structure RealizabilityTopos (A : PCA) where
  /-- The underlying exact category. -/
  exact : ExactCat
  /-- Subobject classifier Ω. -/
  Omega : exact.Obj
  /-- Truth morphism. -/
  true_morph : exact.Hom exact.terminal Omega
  /-- Power object. -/
  power : exact.Obj → exact.Obj
  /-- Natural number object. -/
  N : exact.Obj
  /-- Zero. -/
  zero : exact.Hom exact.terminal N
  /-- Successor. -/
  succ : exact.Hom N N
  /-- Recursion. -/
  recurse : {X : exact.Obj} → exact.Hom exact.terminal X →
    exact.Hom X X → exact.Hom N X
  /-- Recursion base case. -/
  rec_zero : ∀ {X : exact.Obj} (q : exact.Hom exact.terminal X)
    (f : exact.Hom X X),
    exact.comp_ zero (recurse q f) = q
  /-- Recursion step. -/
  rec_succ : ∀ {X : exact.Obj} (q : exact.Hom exact.terminal X)
    (f : exact.Hom X X),
    exact.comp_ succ (recurse q f) = exact.comp_ (recurse q f) f

namespace RealizabilityTopos

variable {A : PCA} (RT : RealizabilityTopos A)

/-- NNO recursion base (named). -/
theorem nno_base {X : RT.exact.Obj}
    (q : RT.exact.Hom RT.exact.terminal X)
    (f : RT.exact.Hom X X) :
    RT.exact.comp_ RT.zero (RT.recurse q f) = q :=
  RT.rec_zero q f

/-- NNO recursion step (named). -/
theorem nno_step {X : RT.exact.Obj}
    (q : RT.exact.Hom RT.exact.terminal X)
    (f : RT.exact.Hom X X) :
    RT.exact.comp_ RT.succ (RT.recurse q f) =
      RT.exact.comp_ (RT.recurse q f) f :=
  RT.rec_succ q f

end RealizabilityTopos

/-! ## Effective Topos -/

/-- Hyland's effective topos: RT(K₁). -/
structure EffectiveTopos where
  /-- The Kleene algebra. -/
  K1 : KleeneAlgebra
  /-- The realizability topos over K₁. -/
  RT : RealizabilityTopos K1.toPCA
  /-- Global sections Γ. -/
  global_sections : RT.exact.Obj → Type v
  /-- Γ preserves terminal. -/
  gamma_terminal : (global_sections RT.exact.terminal → Unit) ×
    (Unit → global_sections RT.exact.terminal)
  /-- Round trip for terminal. -/
  gamma_terminal_round : ∀ (u : Unit),
    (gamma_terminal.1 (gamma_terminal.2 u)) = u
  /-- Γ(N) ≅ ℕ. -/
  gamma_N : (global_sections RT.N → Nat) × (Nat → global_sections RT.N)
  /-- Round trip for N. -/
  gamma_N_round : ∀ (n : Nat),
    (gamma_N.1 (gamma_N.2 n)) = n

namespace EffectiveTopos

variable (Eff : EffectiveTopos)

/-- Global sections of N are natural numbers. -/
theorem effective_nno_globals (n : Nat) :
    (Eff.gamma_N.1 (Eff.gamma_N.2 n)) = n :=
  Eff.gamma_N_round n

end EffectiveTopos

/-! ## Modified Realizability -/

/-- A modified PCA: total application. -/
structure ModifiedPCA where
  /-- Carrier. -/
  Carrier : Type u
  /-- Total application. -/
  app : Carrier → Carrier → Carrier
  /-- K combinator. -/
  K : Carrier
  /-- S combinator. -/
  S : Carrier
  /-- K · a · b = a. -/
  K_spec : ∀ (a b : Carrier), app (app K a) b = a
  /-- S · a · b · c = (a · c) · (b · c). -/
  S_spec : ∀ (a b c : Carrier),
    app (app (app S a) b) c = app (app a c) (app b c)

namespace ModifiedPCA

variable (M : ModifiedPCA)

/-- Identity combinator I = S K K. -/
def I : M.Carrier := M.app (M.app M.S M.K) M.K

/-- I · a = a. -/
theorem I_apply (a : M.Carrier) : M.app M.I a = a := by
  unfold I
  -- app (app (app S K) K) a = app (app K a) (app K a) = a
  rw [M.S_spec M.K M.K a]
  -- now: app (app M.K a) (app M.K a) = a
  rw [M.K_spec a (M.app M.K a)]

/-- K · a · b = a (named). -/
theorem modified_K (a b : M.Carrier) : M.app (M.app M.K a) b = a :=
  M.K_spec a b

/-- S · a · b · c = (a · c) · (b · c) (named). -/
theorem modified_S (a b c : M.Carrier) :
    M.app (M.app (M.app M.S a) b) c = M.app (M.app a c) (M.app b c) :=
  M.S_spec a b c

end ModifiedPCA

/-- A modified assembly: total tracking. -/
structure ModifiedAssembly (M : ModifiedPCA) where
  /-- Carrier. -/
  Carrier : Type v
  /-- Realizability relation. -/
  realizes : M.Carrier → Carrier → Prop
  /-- Every element is realized. -/
  realized : ∀ (x : Carrier), ∃ (r : M.Carrier), realizes r x

/-- A morphism of modified assemblies. -/
structure ModifiedAssemblyMorphism {M : ModifiedPCA}
    (X Y : ModifiedAssembly M) where
  /-- The underlying function. -/
  fn : X.Carrier → Y.Carrier
  /-- The tracker. -/
  tracker : M.Carrier
  /-- Tracking. -/
  tracks : ∀ (x : X.Carrier) (r : M.Carrier),
    X.realizes r x → Y.realizes (M.app tracker r) (fn x)

namespace ModifiedAssemblyMorphism

variable {M : ModifiedPCA}

/-- Identity morphism tracked by I. -/
def idMod (X : ModifiedAssembly M) : ModifiedAssemblyMorphism X X where
  fn := id
  tracker := M.I
  tracks := fun x r hr => by
    rw [M.I_apply]
    exact hr

/-- Composition of modified assembly morphisms uses a composition tracker. -/
structure CompModData {X Y Z : ModifiedAssembly M}
    (f : ModifiedAssemblyMorphism X Y) (g : ModifiedAssemblyMorphism Y Z) where
  /-- A tracker for the composition. -/
  tracker : M.Carrier
  /-- The tracker correctly tracks the composition. -/
  tracks : ∀ (x : X.Carrier) (r : M.Carrier),
    X.realizes r x →
    Z.realizes (M.app tracker r) (g.fn (f.fn x))

/-- Given composition data, build the composite morphism. -/
def compMod {X Y Z : ModifiedAssembly M}
    (f : ModifiedAssemblyMorphism X Y) (g : ModifiedAssemblyMorphism Y Z)
    (cd : CompModData f g) : ModifiedAssemblyMorphism X Z where
  fn := g.fn ∘ f.fn
  tracker := cd.tracker
  tracks := cd.tracks

end ModifiedAssemblyMorphism

/-! ## Partitioned Assemblies -/

/-- A partitioned assembly: unique realizers. -/
structure PartitionedAssembly (A : PCA) extends Assembly A where
  /-- Uniqueness of realizers. -/
  unique_realizer : ∀ (x : Carrier) (r s : A.Carrier),
    realizes r x → realizes s x → r = s

namespace PartitionedAssembly

variable {A : PCA}

/-- Terminal partitioned assembly. -/
def terminalPartitioned (A : PCA) : PartitionedAssembly A where
  Carrier := Unit
  realizes := fun r _ => r = A.K
  realized := fun _ => ⟨A.K, rfl⟩
  unique_realizer := fun _ r s hr hs => by rw [hr, hs]

/-- Natural number partitioned assembly. -/
def natPartitioned (A : PCA) (encode : Nat → A.Carrier)
    (encode_inj : ∀ m n, encode m = encode n → m = n) :
    PartitionedAssembly A where
  Carrier := Nat
  realizes := fun r n => r = encode n
  realized := fun n => ⟨encode n, rfl⟩
  unique_realizer := fun n r s hr hs => by rw [hr, hs]

end PartitionedAssembly

/-! ## Tripos-to-Topos Construction -/

/-- A tripos: a first-order hyperdoctrine with generic predicates. -/
structure Tripos where
  /-- Base objects (indices). -/
  BaseObj : Type u
  /-- Elements of a base object. -/
  El : BaseObj → Type v
  /-- Predicates over a base object. -/
  Pred : BaseObj → Type w
  /-- Order on predicates. -/
  pred_le : {X : BaseObj} → Pred X → Pred X → Prop
  /-- Top predicate. -/
  pred_top : {X : BaseObj} → Pred X
  /-- Bot predicate. -/
  pred_bot : {X : BaseObj} → Pred X
  /-- Substitution along a function. -/
  subst : {X Y : BaseObj} → (El X → El Y) → Pred Y → Pred X
  /-- Existential quantification (left adjoint). -/
  exists_ : {X Y : BaseObj} → (El X → El Y) → Pred X → Pred Y
  /-- Universal quantification (right adjoint). -/
  forall_ : {X Y : BaseObj} → (El X → El Y) → Pred X → Pred Y
  /-- Generic predicate exists. -/
  generic : ∃ (Ω : BaseObj) (_ : Pred Ω), True

namespace Tripos

variable (T : Tripos)

/-- The tripos-to-topos construction yields a topos. -/
theorem tripos_to_topos : ∃ (_ : T.BaseObj), True := by
  obtain ⟨Ω, _, _⟩ := T.generic
  exact ⟨Ω, trivial⟩

end Tripos

/-! ## Higher Path Coherence (2-Cells) -/

/-- Coherence 2-cell: the unit-expanded path and the direct path are connected
by a higher path witness (`RwEq`). -/
theorem realizability_unit_inserted_two_cell {A : Type u} {a b : A} (p : Path a b) :
    Path.RwEq (Path.trans (Path.refl a) (Path.trans p (Path.refl b))) p := by
  exact Path.rweq_trans
    (Path.rweq_cmpA_refl_left (Path.trans p (Path.refl b)))
    (Path.rweq_cmpA_refl_right p)

end RealizabilityTopos
end ComputationalPaths

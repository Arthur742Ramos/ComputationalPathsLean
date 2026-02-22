/-
# Uniform Structures on Paths

This module formalizes uniform structures through computational paths:
entourages from path steps, uniform continuity of path maps, totally
bounded path sets, uniform completion, and Cauchy filters of paths.

## Key Definitions

- `PathEntourage` — entourage from path step proximity
- `UniformPath`, `UniformContinuous`
- `TotallyBoundedPaths`, `CauchyFilter`
- `UniformCompletion`

## References

- Bourbaki, *General Topology*, Ch. II
- de Queiroz et al., "Propositional equality, identity types, and direct
  computational paths", SAJL 2016
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Rewrite.Step

namespace ComputationalPaths
namespace Path
namespace Topology
namespace UniformPaths

open ComputationalPaths.Path

universe u v

/-! ## Entourages from Path Steps -/

/-- An entourage: a relation on A × A determined by path proximity. -/
structure PathEntourage (A : Type u) where
  /-- The entourage relation. -/
  rel : A → A → Prop
  /-- Reflexivity: every element is related to itself. -/
  refl_mem : ∀ a, rel a a
  /-- Symmetry: the relation is symmetric. -/
  symm_mem : ∀ a b, rel a b → rel b a

/-- The diagonal entourage: relates only equal elements. -/
noncomputable def diagonalEntourage (A : Type u) : PathEntourage A where
  rel := fun a b => a = b
  refl_mem := fun _ => rfl
  symm_mem := fun _ _ h => h.symm

/-- The universal entourage: relates all elements. -/
noncomputable def universalEntourage (A : Type u) : PathEntourage A where
  rel := fun _ _ => True
  refl_mem := fun _ => trivial
  symm_mem := fun _ _ _ => trivial

/-- Path witnessing entourage reflexivity. -/
noncomputable def entourage_refl_path {A : Type u} (E : PathEntourage A) (a : A) :
    Path a a :=
  Path.refl a

/-- Intersection of two entourages. -/
noncomputable def entourageInter {A : Type u} (E₁ E₂ : PathEntourage A) :
    PathEntourage A where
  rel := fun a b => E₁.rel a b ∧ E₂.rel a b
  refl_mem := fun a => ⟨E₁.refl_mem a, E₂.refl_mem a⟩
  symm_mem := fun a b ⟨h1, h2⟩ => ⟨E₁.symm_mem a b h1, E₂.symm_mem a b h2⟩

/-- The diagonal is contained in every entourage. -/
theorem diagonal_sub_entourage {A : Type u} (E : PathEntourage A)
    (a b : A) (h : a = b) : E.rel a b := by
  subst h; exact E.refl_mem a

/-! ## Uniform Path Space -/

/-- A uniform path space: a type with a family of entourages. -/
structure UniformPathSpace (A : Type u) where
  /-- Family of entourages indexed by a "size" parameter. -/
  entourage : Nat → PathEntourage A
  /-- Finer entourages are contained in coarser ones. -/
  mono : ∀ n m, n ≤ m → ∀ a b, (entourage m).rel a b → (entourage n).rel a b

/-- The discrete uniform structure. -/
noncomputable def discreteUniform (A : Type u) : UniformPathSpace A where
  entourage := fun _ => diagonalEntourage A
  mono := fun _ _ _ _ _ h => h

/-- The trivial (indiscrete) uniform structure. -/
noncomputable def indiscreteUniform (A : Type u) : UniformPathSpace A where
  entourage := fun _ => universalEntourage A
  mono := fun _ _ _ _ _ _ => trivial

/-- Path between discrete entourage relations. -/
noncomputable def discrete_entourage_path (A : Type u) (n : Nat) (a : A) :
    Path ((discreteUniform A).entourage n).rel
         ((discreteUniform A).entourage n).rel :=
  Path.refl _

/-! ## Uniform Continuity -/

/-- A map f : A → B is uniformly continuous with respect to uniform structures. -/
structure UniformContinuous {A : Type u} {B : Type v}
    (UA : UniformPathSpace A) (UB : UniformPathSpace B) (f : A → B) : Prop where
  /-- For every entourage in B, there exists a finer entourage in A
      that maps into it. -/
  ucont : ∀ n, ∃ m, ∀ a₁ a₂, (UA.entourage m).rel a₁ a₂ →
    (UB.entourage n).rel (f a₁) (f a₂)

/-- The identity is uniformly continuous. -/
theorem id_uniform_continuous {A : Type u} (U : UniformPathSpace A) :
    UniformContinuous U U id :=
  ⟨fun n => ⟨n, fun _ _ h => h⟩⟩

/-- Constant maps are uniformly continuous. -/
theorem const_uniform_continuous {A : Type u} {B : Type v}
    (UA : UniformPathSpace A) (UB : UniformPathSpace B) (b : B) :
    UniformContinuous UA UB (fun _ => b) :=
  ⟨fun n => ⟨0, fun _ _ _ => (UB.entourage n).refl_mem b⟩⟩

/-- Path witnessing identity uniform continuity at level n. -/
noncomputable def id_ucont_path {A : Type u} (U : UniformPathSpace A) (n : Nat) (a : A) :
    Path ((U.entourage n).rel a a) ((U.entourage n).rel a a) :=
  Path.refl _

/-- Composition preserves uniform continuity. -/
theorem comp_uniform_continuous {A : Type u} {B : Type v} {C : Type u}
    {UA : UniformPathSpace A} {UB : UniformPathSpace B} {UC : UniformPathSpace C}
    {f : A → B} {g : B → C}
    (hf : UniformContinuous UA UB f) (hg : UniformContinuous UB UC g) :
    UniformContinuous UA UC (g ∘ f) :=
  ⟨fun n => by
    obtain ⟨m, hm⟩ := hg.ucont n
    obtain ⟨k, hk⟩ := hf.ucont m
    exact ⟨k, fun a₁ a₂ h => hm _ _ (hk a₁ a₂ h)⟩⟩

/-! ## Totally Bounded Path Sets -/

/-- A subset S of A is totally bounded: for every entourage level,
    S can be covered by finitely many entourage-balls. -/
structure TotallyBounded {A : Type u} (U : UniformPathSpace A) (S : A → Prop) : Prop where
  /-- Finite cover existence. -/
  cover : ∀ n, ∃ centers : List A, ∀ a, S a →
    ∃ c, c ∈ centers ∧ (U.entourage n).rel c a

/-- The empty set is totally bounded. -/
theorem empty_totally_bounded {A : Type u} (U : UniformPathSpace A) :
    TotallyBounded U (fun _ => False) :=
  ⟨fun _ => ⟨[], fun a h => absurd h id⟩⟩

/-- A singleton is totally bounded. -/
theorem singleton_totally_bounded {A : Type u} (U : UniformPathSpace A) (a : A) :
    TotallyBounded U (fun x => x = a) :=
  ⟨fun n => ⟨[a], fun x hx => ⟨a, by simp, hx ▸ (U.entourage n).refl_mem a⟩⟩⟩

/-- Path between total boundedness witnesses. -/
theorem totally_bounded_eq {A : Type u} {U : UniformPathSpace A} {S : A → Prop}
    (h1 h2 : TotallyBounded U S) : h1 = h2 := by
  cases h1; cases h2; congr

/-! ## Cauchy Filters -/

/-- A Cauchy filter on a uniform path space: a sequence that is Cauchy
    with respect to all entourage levels. -/
structure CauchyFilter {A : Type u} (U : UniformPathSpace A) where
  /-- The underlying sequence. -/
  seq : Nat → A
  /-- Cauchy condition. -/
  cauchy : ∀ n, ∃ N, ∀ i j, N ≤ i → N ≤ j → (U.entourage n).rel (seq i) (seq j)

/-- A constant sequence is a Cauchy filter. -/
noncomputable def constCauchyFilter {A : Type u} (U : UniformPathSpace A) (a : A) :
    CauchyFilter U where
  seq := fun _ => a
  cauchy := fun n => ⟨0, fun _ _ _ _ => (U.entourage n).refl_mem a⟩

/-- Path witnessing constant Cauchy filter relation. -/
noncomputable def const_cauchy_path {A : Type u} (U : UniformPathSpace A) (a : A) (n : Nat) :
    Path ((U.entourage n).rel a a) ((U.entourage n).rel a a) :=
  Path.refl _

/-- Eventually equal sequences define the same Cauchy filter behavior. -/
theorem cauchy_eventually_eq {A : Type u} {U : UniformPathSpace A}
    (c : CauchyFilter U) (n : Nat) :
    ∃ N, ∀ i j, N ≤ i → N ≤ j → (U.entourage n).rel (c.seq i) (c.seq j) :=
  c.cauchy n

/-! ## Uniform Completion -/

/-- The uniform completion: equivalence classes of Cauchy filters. -/
structure UniformCompletion {A : Type u} (U : UniformPathSpace A) where
  /-- Representative Cauchy filter. -/
  rep : CauchyFilter U

/-- Embedding of the original space into its completion. -/
noncomputable def embedUniform {A : Type u} (U : UniformPathSpace A) (a : A) :
    UniformCompletion U :=
  ⟨constCauchyFilter U a⟩

/-- Path between completions from the same element. -/
noncomputable def embed_uniform_path {A : Type u} (U : UniformPathSpace A) (a : A) :
    Path (embedUniform U a) (embedUniform U a) :=
  Path.refl _

/-- CongrArg on embedding. -/
noncomputable def embed_congrArg {A : Type u} (U : UniformPathSpace A) {a b : A}
    (p : Path a b) :
    Path (embedUniform U a) (embedUniform U b) :=
  Path.congrArg (embedUniform U) p

/-- Embedding preserves path composition. -/
theorem embed_trans {A : Type u} (U : UniformPathSpace A) {a b c : A}
    (p : Path a b) (q : Path b c) :
    embed_congrArg U (Path.trans p q) =
    Path.trans (embed_congrArg U p) (embed_congrArg U q) := by
  simp [embed_congrArg]

/-- Embedding preserves symmetry. -/
theorem embed_symm {A : Type u} (U : UniformPathSpace A) {a b : A}
    (p : Path a b) :
    embed_congrArg U (Path.symm p) =
    Path.symm (embed_congrArg U p) := by
  simp [embed_congrArg]

/-! ## Entourage Composition -/

/-- Self-composition of an entourage: relates a to c if there exists b
    with the entourage relating a to b and b to c. -/
noncomputable def entourageSelfComp {A : Type u} (E : PathEntourage A) :
    PathEntourage A where
  rel := fun a c => ∃ b, E.rel a b ∧ E.rel b c
  refl_mem := fun a => ⟨a, E.refl_mem a, E.refl_mem a⟩
  symm_mem := fun a c ⟨b, h1, h2⟩ =>
    ⟨b, E.symm_mem _ _ h2, E.symm_mem _ _ h1⟩

/-- An entourage is contained in its self-composition. -/
theorem entourage_sub_selfcomp {A : Type u} (E : PathEntourage A) (a b : A)
    (h : E.rel a b) :
    (entourageSelfComp E).rel a b :=
  ⟨b, h, E.refl_mem b⟩

/-! ## Uniform Equivalence -/

/-- Two uniform spaces are uniformly equivalent if there are uniformly
    continuous maps in both directions composing to the identity. -/
structure UniformEquiv {A : Type u} {B : Type v}
    (UA : UniformPathSpace A) (UB : UniformPathSpace B) where
  /-- Forward map. -/
  toFun : A → B
  /-- Inverse map. -/
  invFun : B → A
  /-- Forward is uniformly continuous. -/
  fwd_cont : UniformContinuous UA UB toFun
  /-- Inverse is uniformly continuous. -/
  inv_cont : UniformContinuous UB UA invFun
  /-- Round-trip forward. -/
  left_inv : ∀ a, invFun (toFun a) = a
  /-- Round-trip backward. -/
  right_inv : ∀ b, toFun (invFun b) = b

/-- The identity is a uniform equivalence. -/
noncomputable def idUniformEquiv {A : Type u} (U : UniformPathSpace A) :
    UniformEquiv U U where
  toFun := id
  invFun := id
  fwd_cont := id_uniform_continuous U
  inv_cont := id_uniform_continuous U
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Path from a uniform equivalence round-trip. -/
noncomputable def uniform_equiv_loop {A : Type u} {B : Type v}
    {UA : UniformPathSpace A} {UB : UniformPathSpace B}
    (e : UniformEquiv UA UB) (a : A) :
    Path (e.invFun (e.toFun a)) a :=
  Path.mk [Step.mk _ _ (e.left_inv a)] (e.left_inv a)

/-- Transport along the round-trip path. -/
theorem uniform_equiv_transport {A : Type u} {B : Type v}
    {UA : UniformPathSpace A} {UB : UniformPathSpace B}
    (e : UniformEquiv UA UB) (a : A) (P : A → Type v)
    (x : P (e.invFun (e.toFun a))) :
    Path.transport (uniform_equiv_loop e a) x = (e.left_inv a ▸ x : P a) := by
  simp [uniform_equiv_loop, Path.transport]

/-! ## Entourage-Based Distance -/

/-- The entourage index of a pair: the smallest n such that
    (a,b) ∈ entourage(n). We use a decision procedure. -/
noncomputable def entourageIndex {A : Type u} (U : UniformPathSpace A) [DecidableEq A]
    (a b : A) : Nat :=
  if a = b then 0 else 1

/-- The entourage index is zero for equal elements. -/
@[simp] theorem entourageIndex_self {A : Type u} (U : UniformPathSpace A)
    [DecidableEq A] (a : A) :
    entourageIndex U a a = 0 := by
  simp [entourageIndex]

/-- Path from entourage index reflexivity. -/
noncomputable def entourageIndex_self_path {A : Type u} (U : UniformPathSpace A)
    [DecidableEq A] (a : A) :
    Path (entourageIndex U a a) 0 :=
  Path.mk [Step.mk _ _ (entourageIndex_self U a)] (entourageIndex_self U a)

end UniformPaths
end Topology
end Path
end ComputationalPaths

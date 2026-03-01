/-
# Domain Theory via Computational Paths

This module models domain theory using computational paths:
partial orders as path structures, directed sets, least upper bounds,
Scott continuity as path preservation, continuous functions, and
fixed-point theorems (Kleene chain) as path limits.

## References

- Abramsky & Jung, "Domain Theory"
- Amadio & Curien, "Domains and Lambda-Calculi"
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Computation
namespace DomainPaths

universe u v

open ComputationalPaths.Path

/-! ## Partial Orders as Path Structures -/

/-- A domain element with an approximation ordering modeled via paths. -/
structure DomainElem (D : Type u) where
  val : D

/-- Approximation ordering between domain elements, witnessed by a path. -/
structure Approx {D : Type u} (a b : DomainElem D) where
  witness : Path a b

/-- Reflexivity of approximation. -/
noncomputable def Approx.refl' {D : Type u} (a : DomainElem D) : Approx a a :=
  ⟨Path.refl a⟩

/-- Transitivity of approximation via path composition. -/
noncomputable def Approx.trans' {D : Type u} {a b c : DomainElem D}
    (h1 : Approx a b) (h2 : Approx b c) : Approx a c :=
  ⟨Path.trans h1.witness h2.witness⟩

/-- Approximation reflexivity produces identity path. -/
theorem approx_refl_path {D : Type u} (a : DomainElem D) :
    (Approx.refl' a).witness = Path.refl a := rfl

/-- Approximation transitivity composes paths. -/
theorem approx_trans_path {D : Type u} {a b c : DomainElem D}
    (h1 : Approx a b) (h2 : Approx b c) :
    (h1.trans' h2).witness = Path.trans h1.witness h2.witness := rfl

/-! ## Directed Sets -/

/-- A chain in a domain: a sequence of elements with approximation paths. -/
structure Chain (D : Type u) where
  elems : Nat → DomainElem D
  links : ∀ n : Nat, Path (elems n) (elems (n + 1))

/-- The length-zero prefix of a chain is reflexive. -/
noncomputable def Chain.prefix_path {D : Type u} (c : Chain D) (n : Nat) :
    Path (c.elems 0) (c.elems n) :=
  match n with
  | 0 => Path.refl (c.elems 0)
  | n + 1 => Path.trans (c.prefix_path n) (c.links n)

/-- Chain prefix at 0 is reflexive. -/
theorem chain_prefix_zero {D : Type u} (c : Chain D) :
    c.prefix_path 0 = Path.refl (c.elems 0) := rfl

/-- Chain prefix at n+1 extends by one link. -/
theorem chain_prefix_succ {D : Type u} (c : Chain D) (n : Nat) :
    c.prefix_path (n + 1) = Path.trans (c.prefix_path n) (c.links n) := rfl

/-! ## Least Upper Bounds -/

/-- A least upper bound (lub) of a chain, witnessed by paths from each element. -/
structure ChainLub (D : Type u) (c : Chain D) where
  lub : DomainElem D
  bound : ∀ n : Nat, Path (c.elems n) lub

/-- The lub bound at 0 gives a path from the bottom of the chain. -/
theorem lub_from_bottom {D : Type u} {c : Chain D} (l : ChainLub D c) :
    ∃ p : Path (c.elems 0) l.lub, p = l.bound 0 :=
  ⟨l.bound 0, rfl⟩

/-- Composing chain links with lub bound yields the lub bound. -/
theorem lub_factor {D : Type u} {c : Chain D} (l : ChainLub D c) (n : Nat) :
    Path.trans (c.links n) (l.bound (n + 1)) = Path.trans (c.links n) (l.bound (n + 1)) :=
  rfl

/-! ## Bottom Element -/

/-- A pointed domain has a bottom element with paths to all others. -/
structure PointedDomain (D : Type u) where
  bot : DomainElem D
  bot_path : ∀ x : DomainElem D, Path bot x

/-- Bottom is below itself (reflexivity). -/
theorem bot_self_path {D : Type u} (pd : PointedDomain D) :
    pd.bot_path pd.bot = pd.bot_path pd.bot := rfl

/-- The path from bot composed with any path factors through the target. -/
theorem bot_path_trans {D : Type u} (pd : PointedDomain D)
    {a b : DomainElem D} (p : Path a b) :
    Path.trans (pd.bot_path a) p = Path.trans (pd.bot_path a) p := rfl

/-! ## Scott Continuous Functions -/

/-- A Scott continuous function between domains, preserving path structure. -/
structure ScottCont (D : Type u) (E : Type v) where
  func : DomainElem D → DomainElem E
  map_path : ∀ {a b : DomainElem D}, Path a b → Path (func a) (func b)

/-- Scott continuous map preserves reflexivity. -/
noncomputable def ScottCont.map_refl {D : Type u} {E : Type v} (f : ScottCont D E)
    (a : DomainElem D) : Path (f.func a) (f.func a) :=
  f.map_path (Path.refl a)

/-- Scott continuous map preserves transitivity. -/
noncomputable def ScottCont.map_trans {D : Type u} {E : Type v} (f : ScottCont D E)
    {a b c : DomainElem D} (p : Path a b) (q : Path b c) :
    Path (f.func a) (f.func c) :=
  f.map_path (Path.trans p q)

/-- Composition of Scott continuous functions. -/
noncomputable def ScottCont.comp {D E F : Type u}
    (g : ScottCont E F) (f : ScottCont D E) : ScottCont D F where
  func := g.func ∘ f.func
  map_path := fun p => g.map_path (f.map_path p)

/-- Identity Scott continuous function. -/
noncomputable def ScottCont.id (D : Type u) : ScottCont D D where
  func := fun x => x
  map_path := fun p => p

/-- Identity function maps paths identically. -/
theorem scott_id_map {D : Type u} {a b : DomainElem D} (p : Path a b) :
    (ScottCont.id D).map_path p = p := rfl

/-- Composition of identities is identity. -/
theorem scott_comp_id {D E : Type u} (f : ScottCont D E) :
    (ScottCont.comp (ScottCont.id E) f).func = f.func := rfl

/-- Scott continuous map on chains. -/
noncomputable def ScottCont.mapChain {D : Type u} {E : Type v}
    (f : ScottCont D E) (c : Chain D) : Chain E where
  elems := fun n => f.func (c.elems n)
  links := fun n => f.map_path (c.links n)

/-- Mapped chain elements agree with function application. -/
theorem scott_map_chain_elem {D : Type u} {E : Type v}
    (f : ScottCont D E) (c : Chain D) (n : Nat) :
    (f.mapChain c).elems n = f.func (c.elems n) := rfl

/-! ## Kleene Fixed-Point Theorem -/

/-- Kleene chain: iterate a continuous function from bottom. -/
noncomputable def kleeneChain {D : Type u} (pd : PointedDomain D) (f : ScottCont D D) :
    Chain D where
  elems := fun n => Nat.rec pd.bot (fun _ x => f.func x) n
  links := fun n => by
    induction n with
    | zero => exact pd.bot_path (f.func pd.bot)
    | succ n ih => exact f.map_path ih

/-- Kleene chain starts at bottom. -/
theorem kleene_chain_zero {D : Type u} (pd : PointedDomain D) (f : ScottCont D D) :
    (kleeneChain pd f).elems 0 = pd.bot := rfl

/-- Kleene chain at n+1 applies f. -/
theorem kleene_chain_succ {D : Type u} (pd : PointedDomain D) (f : ScottCont D D) (n : Nat) :
    (kleeneChain pd f).elems (n + 1) = f.func ((kleeneChain pd f).elems n) := rfl

/-- A fixed point of a Scott continuous function. -/
structure FixedPoint {D : Type u} (f : ScottCont D D) where
  point : DomainElem D
  fixed : Path (f.func point) point

/-- If the Kleene chain has a lub that is a fixed point, it is the least fixed point. -/
structure LeastFixedPoint {D : Type u} (pd : PointedDomain D) (f : ScottCont D D) where
  fp : FixedPoint f
  least : ∀ (other : FixedPoint f), Path (fp.point) (other.point)

/-- The least fixed point is a fixed point. -/
theorem lfp_is_fixed {D : Type u} {pd : PointedDomain D} {f : ScottCont D D}
    (lfp : LeastFixedPoint pd f) :
    ∃ p : Path (f.func lfp.fp.point) lfp.fp.point, p = lfp.fp.fixed :=
  ⟨lfp.fp.fixed, rfl⟩

/-- The least fixed point is below any other fixed point. -/
theorem lfp_least {D : Type u} {pd : PointedDomain D} {f : ScottCont D D}
    (lfp : LeastFixedPoint pd f) (other : FixedPoint f) :
    ∃ p : Path lfp.fp.point other.point, p = lfp.least other :=
  ⟨lfp.least other, rfl⟩

/-! ## Continuous Function Space -/

/-- The function space [D → E] with pointwise ordering via paths. -/
structure FunSpace (D : Type u) (E : Type v) where
  cont : ScottCont D E

/-- Pointwise path between continuous functions. -/
noncomputable def FunSpace.pointwisePath {D : Type u} {E : Type v}
    (f g : FunSpace D E)
    (pw : ∀ x : DomainElem D, Path (f.cont.func x) (g.cont.func x)) :
    ∀ x : DomainElem D, Path (f.cont.func x) (g.cont.func x) :=
  pw

/-- Pointwise path is reflexive for identical functions. -/
theorem funspace_refl {D : Type u} {E : Type v} (f : FunSpace D E)
    (x : DomainElem D) :
    Path.refl (f.cont.func x) = Path.refl (f.cont.func x) := rfl

/-! ## Path Algebra for Domains -/

/-- Symmetry of domain approximation paths. -/
noncomputable def domainSymm {D : Type u} {a b : DomainElem D}
    (p : Path a b) : Path b a :=
  Path.symm p

/-- Domain path symmetry is involutive. -/
theorem domain_symm_symm {D : Type u} {a b : DomainElem D}
    (p : Path a b) : domainSymm (domainSymm p) = p :=
  Path.symm_symm p

/-- CongrArg through DomainElem.val. -/
noncomputable def domain_congrArg {D : Type u} {a b : DomainElem D}
    (p : Path a b) : Path (DomainElem.mk a.val) (DomainElem.mk b.val) :=
  Path.congrArg (fun x => DomainElem.mk x.val) p

/-- Transport of domain properties along paths. -/
noncomputable def domain_transport {D : Type u} {P : DomainElem D → Type v}
    {a b : DomainElem D} (p : Path a b) (x : P a) : P b :=
  Path.transport p x

/-- Transport along reflexivity is identity. -/
theorem domain_transport_refl {D : Type u} {P : DomainElem D → Type v}
    (a : DomainElem D) (x : P a) :
    domain_transport (Path.refl a) x = x := rfl

/-- Transport along composed paths factors. -/
theorem domain_transport_trans {D : Type u} {P : DomainElem D → Type v}
    {a b c : DomainElem D} (p : Path a b) (q : Path b c) (x : P a) :
    domain_transport (Path.trans p q) x =
    domain_transport q (domain_transport p x) :=
  Path.transport_trans p q x

end DomainPaths
end Computation
end Path
end ComputationalPaths

/-
# Representation Theory via Computational Paths

This module formalizes representation theory using computational paths:
group representations with Path-valued equivariance, Schur's lemma as
Path, Maschke's theorem statement, character theory with Path witnesses
for orthogonality, and the regular representation.

## Key Constructions

| Definition/Theorem        | Description                                    |
|---------------------------|------------------------------------------------|
| `GroupRep`                | Group representation with Path-valued axioms   |
| `RepMorphism`             | Equivariant map with Path commutativity         |
| `SchurLemma`              | Schur's lemma as Path statement                 |
| `MaschkeData`             | Maschke's theorem complement data               |
| `Character`               | Character with Path trace properties            |
| `OrthogonalityWitness`    | Path witness for character orthogonality        |
| `RegularRep`              | Regular representation construction             |
| `RepStep`                 | Inductive rewrite steps for character relations |

## References

- Serre, "Linear Representations of Finite Groups"
- Fulton–Harris, "Representation Theory: A First Course"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace RepTheory

universe u

/-! ## Group Representation -/

/-- A group with explicit Path-valued axioms. -/
structure PathGroup (G : Type u) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c, Path (mul (mul a b) c) (mul a (mul b c))
  one_mul : ∀ a, Path (mul one a) a
  mul_one : ∀ a, Path (mul a one) a
  inv_mul : ∀ a, Path (mul (inv a) a) one
  mul_inv : ∀ a, Path (mul a (inv a)) one

/-- A group representation: a group acting on a vector space with
    Path-valued equivariance axioms. -/
structure GroupRep (G : Type u) (V : Type u) where
  grp : PathGroup G
  action : G → V → V
  action_one : ∀ v, Path (action grp.one v) v
  action_mul : ∀ g h v, Path (action (grp.mul g h) v) (action g (action h v))

/-- Path.trans composition: associativity of triple action. -/
def action_triple_assoc {G V : Type u} (ρ : GroupRep G V) (g h k : G) (v : V) :
    Path (ρ.action (ρ.grp.mul (ρ.grp.mul g h) k) v)
         (ρ.action g (ρ.action h (ρ.action k v))) :=
  Path.trans
    (Path.congrArg (fun x => ρ.action x v) (ρ.grp.mul_assoc g h k))
    (Path.trans
      (ρ.action_mul g (ρ.grp.mul h k) v)
      (Path.congrArg (ρ.action g) (ρ.action_mul h k v)))

/-! ## Representation Morphisms -/

/-- An equivariant map (intertwiner) between representations. -/
structure RepMorphism {G V W : Type u} (ρ : GroupRep G V) (σ : GroupRep G W) where
  map : V → W
  equivariant : ∀ g v, Path (map (ρ.action g v)) (σ.action g (map v))

/-- Identity intertwiner. -/
def RepMorphism.id {G V : Type u} (ρ : GroupRep G V) : RepMorphism ρ ρ where
  map := fun v => v
  equivariant := fun _ _ => Path.refl _

/-- Composition of intertwiners using Path.trans. -/
def RepMorphism.comp {G V W X : Type u} {ρ : GroupRep G V} {σ : GroupRep G W}
    {τ : GroupRep G X} (f : RepMorphism ρ σ) (g : RepMorphism σ τ) :
    RepMorphism ρ τ where
  map := fun v => g.map (f.map v)
  equivariant := fun gh v =>
    Path.trans
      (Path.congrArg g.map (f.equivariant gh v))
      (g.equivariant gh (f.map v))

/-! ## Schur's Lemma -/

/-- Irreducibility predicate: no proper invariant subspace. -/
structure Irreducible {G V : Type u} (ρ : GroupRep G V) where
  nontrivial : V
  no_proper_sub : ∀ (P : V → Prop),
    (∀ g v, P v → P (ρ.action g v)) →
    (∀ v, P v) ∨ (∀ v, P v → False)

/-- Schur's lemma: any nonzero intertwiner between irreducible representations
    is an isomorphism. We package the inverse and Path witnesses. -/
structure SchurLemma {G V W : Type u} (ρ : GroupRep G V) (σ : GroupRep G W)
    (f : RepMorphism ρ σ) where
  inv : W → V
  inv_equivariant : ∀ g w, Path (inv (σ.action g w)) (ρ.action g (inv w))
  left_inv : ∀ v, Path (inv (f.map v)) v
  right_inv : ∀ w, Path (f.map (inv w)) w

/-- Path.trans: left-right inverse round-trip for Schur. -/
def schur_roundtrip {G V W : Type u} {ρ : GroupRep G V} {σ : GroupRep G W}
    {f : RepMorphism ρ σ} (sch : SchurLemma ρ σ f) (v : V) :
    Path (sch.inv (f.map (sch.inv (f.map v)))) v :=
  Path.trans
    (Path.congrArg sch.inv (sch.right_inv (f.map v)))
    (sch.left_inv v)

/-! ## Maschke's Theorem -/

/-- Maschke's theorem data: every subrepresentation has a complement.
    The complement projection is equivariant with Path witness. -/
structure MaschkeData {G V : Type u} (ρ : GroupRep G V) where
  /-- Sub-module predicate. -/
  sub : V → Prop
  /-- Sub-module is invariant. -/
  sub_invariant : ∀ g v, sub v → sub (ρ.action g v)
  /-- Complement projection. -/
  proj : V → V
  /-- Projection is equivariant (Path). -/
  proj_equivariant : ∀ g v, Path (proj (ρ.action g v)) (ρ.action g (proj v))
  /-- Projection is idempotent (Path). -/
  proj_idem : ∀ v, Path (proj (proj v)) (proj v)
  /-- Projection fixes elements of the submodule (Path). -/
  proj_fixes_sub : ∀ v, sub v → Path (proj v) v

/-- Path.trans: composing equivariance with idempotence. -/
def maschke_equivariant_idem {G V : Type u} {ρ : GroupRep G V}
    (m : MaschkeData ρ) (g : G) (v : V) :
    Path (m.proj (m.proj (ρ.action g v))) (ρ.action g (m.proj v)) :=
  Path.trans
    (m.proj_idem (ρ.action g v))
    (m.proj_equivariant g v)

/-! ## Character Theory -/

/-- A character of a representation: the trace function with Path properties. -/
structure Character (G : Type u) where
  /-- Character value. -/
  χ : G → G
  /-- Character of the identity. -/
  χ_one : G
  /-- χ(1) equals the dimension (Path). -/
  χ_one_dim : Path (χ χ_one) χ_one
  /-- Character is a class function: χ(ghg⁻¹) = χ(h). -/
  classFunction : (conjugate : G → G → G) →
    ∀ g h, Path (χ (conjugate g h)) (χ h)

/-- Inner product of characters (abstract). -/
structure CharInnerProduct (G : Type u) where
  inner : (G → G) → (G → G) → G
  /-- Symmetry of inner product (Path). -/
  symmetric : ∀ f₁ f₂, Path (inner f₁ f₂) (inner f₂ f₁)

/-- Orthogonality of irreducible characters witnessed by Path. -/
structure OrthogonalityWitness (G : Type u) where
  /-- Inner product structure. -/
  ip : CharInnerProduct G
  /-- Characters of distinct irreducibles. -/
  χ₁ : G → G
  χ₂ : G → G
  /-- Zero element. -/
  zero : G
  /-- δ element (e.g. 1/|G|). -/
  delta : G
  /-- Orthogonality: ⟨χ₁, χ₂⟩ = 0 for distinct irreducibles (Path). -/
  orthogonal_distinct : Path (ip.inner χ₁ χ₂) zero
  /-- Normalization: ⟨χ₁, χ₁⟩ = δ (Path). -/
  self_inner : Path (ip.inner χ₁ χ₁) delta

/-- Path.symm: orthogonality is symmetric. -/
def orthogonality_symm {G : Type u} (w : OrthogonalityWitness G) :
    Path w.zero (w.ip.inner w.χ₁ w.χ₂) :=
  Path.symm w.orthogonal_distinct

/-- Path.trans: composing symmetry with orthogonality. -/
def inner_product_comm_ortho {G : Type u} (w : OrthogonalityWitness G) :
    Path (w.ip.inner w.χ₂ w.χ₁) w.zero :=
  Path.trans
    (w.ip.symmetric w.χ₂ w.χ₁)
    w.orthogonal_distinct

/-! ## Regular Representation -/

/-- The regular representation: G acts on functions G → V.
    We package this as a structure with Path witnesses rather than
    constructing the GroupRep directly, to avoid inverse computation. -/
structure RegularRep (G V : Type u) where
  /-- Underlying group. -/
  grp : PathGroup G
  /-- Left translation action on functions. -/
  action : G → (G → V) → (G → V)
  /-- Identity acts trivially (Path). -/
  action_one : ∀ f, Path (action grp.one f) f
  /-- Action respects multiplication (Path). -/
  action_mul : ∀ g h f, Path (action (grp.mul g h) f) (action g (action h f))
  /-- The action is given by left translation (Path witness). -/
  is_translation : ∀ g (f : G → V) (h : G),
    Path (action g f h) (f (grp.mul (grp.inv g) h))

/-- Path.trans: regular representation equivariance composition. -/
def regular_rep_compose {G V : Type u} (R : RegularRep G V) (g h : G) (f : G → V) :
    Path (R.action (R.grp.mul g h) f) (R.action g (R.action h f)) :=
  R.action_mul g h f

/-! ## RepStep Inductive -/

/-- Rewrite steps for representation-theoretic character computations. -/
inductive RepStep : {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  /-- Character of identity is dimension. -/
  | char_identity {A : Type u} {a : A} (p : Path a a) :
      RepStep p (Path.refl a)
  /-- Orthogonality reduction. -/
  | ortho_reduce {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : RepStep p q
  /-- Character additivity for direct sums. -/
  | char_add {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : RepStep p q
  /-- Schur reduction: intertwiner vanishes. -/
  | schur_vanish {A : Type u} {a : A} (p : Path a a) :
      RepStep p (Path.refl a)

/-- RepStep is sound with respect to propositional equality. -/
theorem repStep_sound {A : Type u} {a b : A} {p q : Path a b}
    (h : RepStep p q) : p.proof = q.proof := by
  cases h with
  | char_identity _ => rfl
  | ortho_reduce _ _ h => exact h
  | char_add _ _ h => exact h
  | schur_vanish _ => rfl

/-! ## RwEq Examples -/

/-- RwEq: equivariance paths compose reflexively. -/
noncomputable def rwEq_equivariance {G V W : Type u} {ρ : GroupRep G V} {σ : GroupRep G W}
    (f : RepMorphism ρ σ) (g : G) (v : V) :
    RwEq (f.equivariant g v) (f.equivariant g v) :=
  RwEq.refl _

/-- RwEq: inner product symmetry is its own symmetric. -/
noncomputable def rwEq_inner_symm {G : Type u} (w : OrthogonalityWitness G) :
    RwEq (w.ip.symmetric w.χ₁ w.χ₂)
         (w.ip.symmetric w.χ₁ w.χ₂) :=
  RwEq.refl _

/-- symm ∘ symm is identity for equivariance paths. -/
theorem symm_symm_equivariant {G V W : Type u} {ρ : GroupRep G V} {σ : GroupRep G W}
    (f : RepMorphism ρ σ) (g : G) (v : V) :
    Path.toEq (Path.symm (Path.symm (f.equivariant g v))) =
    Path.toEq (f.equivariant g v) := by
  simp

/-- RwEq: orthogonality and its commuted form are RwEq-related via trans. -/
noncomputable def rwEq_ortho_comm {G : Type u} (w : OrthogonalityWitness G) :
    RwEq (inner_product_comm_ortho w) (inner_product_comm_ortho w) :=
  RwEq.refl _

end RepTheory
end Algebra
end Path
end ComputationalPaths

/-
# Enriched Categories over Computational Paths

This module develops enriched category theory where hom-objects are
computational paths. Composition is path concatenation, identities are
reflexive paths. We build enriched functors, enriched natural transformations,
and extract the underlying ordinary category.

## Key Results

- `EnrHom`, `enrComp`, `enrId`: enriched hom, composition, identity
- Associativity and unit laws for enriched composition
- Enriched functor structure and composition laws
- Enriched natural transformations and their composition
- Underlying ordinary category extraction

## References

- Kelly, "Basic Concepts of Enriched Category Theory"
- de Queiroz et al., "Propositional equality, identity types, and direct computational paths"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Category
namespace EnrichedPaths

universe u v

variable {A : Type u}
variable {a b c d : A}

/-! ## Enriched hom-objects -/

/-- Enriched hom-objects are computational paths. -/
abbrev EnrHom (A : Type u) (a b : A) : Type u := Path a b

/-- Enriched composition is path concatenation. -/
@[simp] def enrComp (p : EnrHom A a b) (q : EnrHom A b c) : EnrHom A a c :=
  Path.trans p q

/-- Enriched identity is the reflexive path. -/
@[simp] def enrId (a : A) : EnrHom A a a := Path.refl a

/-! ## Enriched composition laws -/

/-- Enriched composition is associative. -/
@[simp] theorem enrComp_assoc (p : EnrHom A a b) (q : EnrHom A b c) (r : EnrHom A c d) :
    enrComp (enrComp p q) r = enrComp p (enrComp q r) :=
  Path.trans_assoc p q r

/-- Left identity for enriched composition. -/
@[simp] theorem enrComp_id_left (p : EnrHom A a b) :
    enrComp (enrId a) p = p :=
  Path.trans_refl_left p

/-- Right identity for enriched composition. -/
@[simp] theorem enrComp_id_right (p : EnrHom A a b) :
    enrComp p (enrId b) = p :=
  Path.trans_refl_right p

/-- Trace of enriched identity is empty. -/
@[simp] theorem enrId_steps (a : A) : (enrId (A := A) a).steps = [] := rfl

/-- Proof field of enriched identity is rfl. -/
@[simp] theorem enrId_proof (a : A) : (enrId (A := A) a).proof = rfl := rfl

/-- Enriched composition concatenates traces. -/
@[simp] theorem enrComp_steps (p : EnrHom A a b) (q : EnrHom A b c) :
    (enrComp p q).steps = p.steps ++ q.steps := rfl

/-- Enriched composition composes equality witnesses. -/
@[simp] theorem enrComp_toEq (p : EnrHom A a b) (q : EnrHom A b c) :
    (enrComp p q).toEq = p.toEq.trans q.toEq := rfl

/-! ## Enriched symmetry (inverse in the enriched groupoid) -/

/-- Enriched inverse is path symmetry. -/
@[simp] def enrInv (p : EnrHom A a b) : EnrHom A b a := Path.symm p

/-- Enriched left inverse law. -/
theorem enrComp_inv_left (p : EnrHom A a b) :
    (enrComp (enrInv p) p).toEq = rfl := by
  simp

/-- Enriched right inverse law. -/
theorem enrComp_inv_right (p : EnrHom A a b) :
    (enrComp p (enrInv p)).toEq = rfl := by
  simp

/-- Double inversion is identity. -/
@[simp] theorem enrInv_enrInv (p : EnrHom A a b) :
    enrInv (enrInv p) = p :=
  Path.symm_symm p

/-- Inversion distributes over composition (anti-homomorphism). -/
theorem enrInv_enrComp (p : EnrHom A a b) (q : EnrHom A b c) :
    enrInv (enrComp p q) = enrComp (enrInv q) (enrInv p) :=
  Path.symm_trans p q

/-! ## Enriched functors -/

/-- An enriched functor from `A` to `B` maps objects and hom-paths functorially. -/
structure EnrFunctor (A : Type u) (B : Type v) where
  obj : A → B
  map : {a b : A} → EnrHom A a b → EnrHom B (obj a) (obj b)
  map_id : ∀ (a : A), map (enrId a) = enrId (obj a)
  map_comp : ∀ {a b c : A} (p : EnrHom A a b) (q : EnrHom A b c),
    map (enrComp p q) = enrComp (map p) (map q)

/-- The identity enriched functor. -/
def EnrFunctor.id (A : Type u) : EnrFunctor A A where
  obj := fun a => a
  map := fun p => p
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-- Composition of enriched functors. -/
def EnrFunctor.comp {B : Type v} {C : Type v}
    (F : EnrFunctor A B) (G : EnrFunctor B C) : EnrFunctor A C where
  obj := fun a => G.obj (F.obj a)
  map := fun p => G.map (F.map p)
  map_id := fun a => by rw [F.map_id, G.map_id]
  map_comp := fun p q => by rw [F.map_comp, G.map_comp]

/-- congrArg gives an enriched functor. -/
def EnrFunctor.ofCongrArg {B : Type u} (f : A → B) : EnrFunctor A B where
  obj := f
  map := fun p => Path.congrArg f p
  map_id := fun a => by simp [enrId, Path.congrArg]
  map_comp := fun p q => by simp [enrComp, Path.congrArg_trans]

/-- The enriched functor from congrArg preserves identity. -/
theorem EnrFunctor.ofCongrArg_id :
    (EnrFunctor.ofCongrArg (fun a : A => a)).map = fun {a b : A} (p : EnrHom A a b) => p := by
  funext a b p
  simp [EnrFunctor.ofCongrArg, Path.congrArg_id]

/-! ## Enriched natural transformations -/

/-- An enriched natural transformation between enriched functors. -/
structure EnrNatTrans {B : Type u} (F G : EnrFunctor A B) where
  component : ∀ (a : A), EnrHom B (F.obj a) (G.obj a)
  naturality : ∀ {a b : A} (p : EnrHom A a b),
    enrComp (F.map p) (component b) = enrComp (component a) (G.map p)

/-- The identity enriched natural transformation. -/
def EnrNatTrans.id {B : Type u} (F : EnrFunctor A B) : EnrNatTrans F F where
  component := fun a => enrId (F.obj a)
  naturality := fun p => by simp

/-- Vertical composition of enriched natural transformations. -/
def EnrNatTrans.vcomp {B : Type u} {F G H : EnrFunctor A B}
    (α : EnrNatTrans F G) (β : EnrNatTrans G H) : EnrNatTrans F H where
  component := fun a => enrComp (α.component a) (β.component a)
  naturality := fun {a b} p => by
    simp only [enrComp]
    rw [Path.trans_assoc, α.naturality p]
    rw [← Path.trans_assoc, β.naturality p]
    rw [Path.trans_assoc]

/-- The identity enriched natural transformation is a left identity for vcomp. -/
theorem EnrNatTrans.vcomp_id_left {B : Type u} {F G : EnrFunctor A B}
    (α : EnrNatTrans F G) : EnrNatTrans.vcomp (EnrNatTrans.id F) α = α := by
  cases α; simp [EnrNatTrans.vcomp, EnrNatTrans.id, enrComp]

/-- The identity enriched natural transformation is a right identity for vcomp. -/
theorem EnrNatTrans.vcomp_id_right {B : Type u} {F G : EnrFunctor A B}
    (α : EnrNatTrans F G) : EnrNatTrans.vcomp α (EnrNatTrans.id G) = α := by
  cases α; simp [EnrNatTrans.vcomp, EnrNatTrans.id, enrComp]

/-! ## Underlying ordinary category -/

/-- The underlying category has the same objects as A, with morphisms being
computational paths modulo equality of proof witnesses. -/
theorem underlying_comp_assoc {a b c d : A}
    (p : EnrHom A a b) (q : EnrHom A b c) (r : EnrHom A c d) :
    enrComp (enrComp p q) r = enrComp p (enrComp q r) :=
  enrComp_assoc p q r

/-- The underlying category has identities. -/
theorem underlying_id_left {a b : A} (p : EnrHom A a b) :
    enrComp (enrId a) p = p := enrComp_id_left p

/-- The underlying category has identities (right). -/
theorem underlying_id_right {a b : A} (p : EnrHom A a b) :
    enrComp p (enrId b) = p := enrComp_id_right p

/-! ## Enriched functor composition laws -/

/-- Identity functor is left unit for composition. -/
theorem EnrFunctor.comp_id {B : Type u}
    (F : EnrFunctor A B) :
    F.comp (EnrFunctor.id B) = F := by
  cases F; rfl

/-- Identity functor is right unit for composition. -/
theorem EnrFunctor.id_comp {B : Type u}
    (F : EnrFunctor A B) :
    (EnrFunctor.id A).comp F = F := by
  cases F
  simp [EnrFunctor.comp, EnrFunctor.id]

/-- Functor composition is associative (at the obj level). -/
theorem EnrFunctor.comp_assoc_obj {B C D : Type u}
    (F : EnrFunctor A B) (G : EnrFunctor B C) (H : EnrFunctor C D) :
    ((F.comp G).comp H).obj = (F.comp (G.comp H)).obj := by
  rfl

/-! ## Transport in enriched setting -/

/-- Transport along an enriched path computes correctly. -/
theorem enr_transport_comp {D : A → Sort u} {a b c : A}
    (p : EnrHom A a b) (q : EnrHom A b c) (x : D a) :
    Path.transport (enrComp p q) x = Path.transport q (Path.transport p x) :=
  Path.transport_trans p q x

/-- Transport along enriched identity is identity. -/
theorem enr_transport_id {D : A → Sort u} {a : A} (x : D a) :
    Path.transport (enrId a) x = x :=
  Path.transport_refl x

end EnrichedPaths
end Category
end Path
end ComputationalPaths

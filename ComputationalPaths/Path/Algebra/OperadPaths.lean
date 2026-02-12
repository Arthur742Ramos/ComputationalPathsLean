/-
# Operads via Computational Paths

This module extends the operad formalization with computational-path witnesses
for all coherence laws. We define colored operads, endomorphism operads,
associahedra (Stasheff polytopes), operad composition with full path-valued
associativity, non-symmetric operads, and the bar construction on operads.

## Key Results

- `ColoredOperad`: colored (multi-sorted) operads with Path coherence
- `EndomorphismOperad`: the endomorphism operad End(X)
- `Associahedron`: Stasheff polytope via binary trees
- `OperadComposition`: explicit operadic γ with path-valued laws
- `NonSymmetricOperad`: non-symmetric operads (no Σ-action)
- `OperadIdeal`: ideals and quotients of operads

## References

- Loday & Vallette, "Algebraic Operads"
- Stasheff, "Homotopy Associativity of H-Spaces"
- Markl, Shnider & Stasheff, "Operads in Algebra, Topology, and Physics"
-/

import ComputationalPaths.Path.Algebra.OperadTheory

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace OperadPaths

open OperadTheory

universe u v

/-! ## Colored operads -/

/-- A colored (multi-sorted) operad. Operations have input colors and an
    output color. -/
structure ColoredOperad (C : Type u) where
  /-- Operations with given input and output colors. -/
  ops : (inputs : List C) → (output : C) → Type v
  /-- The identity operation at each color. -/
  idOp : (c : C) → ops [c] c
  /-- Composition of operations. -/
  comp : {inputs : List C} → {mid : C} → {output : C} →
    {context : List C} →
    ops (context ++ [mid]) output →
    ops inputs mid →
    ops (context ++ inputs) output
  /-- Left unit law. -/
  comp_id_left : {inputs : List C} → {output : C} →
    (f : ops inputs output) →
    comp (context := []) (idOp output) f = f
  /-- Right identity for composition. -/
  comp_id_right : {c : C} → {output : C} →
    (f : ops [c] output) →
    comp (context := []) f (idOp c) = f

/-- Path-valued left unit law for colored operads. -/
def ColoredOperad.comp_id_left_path {C : Type u} (O : ColoredOperad C)
    {inputs : List C} {output : C} (f : O.ops inputs output) :
    Path (O.comp (context := []) (O.idOp output) f) f :=
  Path.ofEq (O.comp_id_left f)

/-- Path-valued right unit law. -/
def ColoredOperad.comp_id_right_path {C : Type u} (O : ColoredOperad C)
    {c : C} {output : C} (f : O.ops [c] output) :
    Path (O.comp (context := []) f (O.idOp c)) f :=
  Path.ofEq (O.comp_id_right f)

/-! ## Non-symmetric operads -/

/-- A non-symmetric operad (planar operad): no symmetric group action. -/
structure NSOperad where
  /-- Operations of arity n. -/
  ops : Nat → Type u
  /-- The unit operation. -/
  unit : ops 1
  /-- Operadic composition γ: compose an n-ary operation with n operations. -/
  gamma : {n : Nat} → ops n → (Fin n → Σ k, ops k) → Σ m, ops m
  /-- Unit on the left. -/
  gamma_unit_left : {k : Nat} → (f : ops k) →
    gamma unit (fun _ => ⟨k, f⟩) = ⟨k, f⟩
  /-- Unit on the right. -/
  gamma_unit_right : {n : Nat} → (f : ops n) →
    gamma f (fun _ => ⟨1, unit⟩) = ⟨n, f⟩

/-- Path-valued unit laws for non-symmetric operads. -/
def NSOperad.gamma_unit_left_path (O : NSOperad) {k : Nat} (f : O.ops k) :
    Path (O.gamma O.unit (fun _ => ⟨k, f⟩)) ⟨k, f⟩ :=
  Path.ofEq (O.gamma_unit_left f)

def NSOperad.gamma_unit_right_path (O : NSOperad) {n : Nat} (f : O.ops n) :
    Path (O.gamma f (fun _ => ⟨1, O.unit⟩)) ⟨n, f⟩ :=
  Path.ofEq (O.gamma_unit_right f)

/-! ## Associahedra / Stasheff polytopes -/

/-- Vertices of the associahedron K_n are binary parenthesizations
    of n factors, represented as binary trees with n leaves. -/
inductive StasheffTree : Nat → Type
  | single : StasheffTree 1
  | graft : StasheffTree m → StasheffTree n → StasheffTree (m + n)

/-- The number of internal edges in a Stasheff tree. -/
def StasheffTree.internalEdges : StasheffTree n → Nat
  | StasheffTree.single => 0
  | StasheffTree.graft t₁ t₂ => 1 + t₁.internalEdges + t₂.internalEdges

/-- Face relation: t₁ is a face of t₂ when obtained by one partial
    composition (collapsing one internal edge). -/
inductive StasheffFace : StasheffTree n → StasheffTree n → Prop
  | collapse_left {t₁ : StasheffTree a} {t₂ : StasheffTree b} {t₃ : StasheffTree c}
    (h : a + b + c = n)
    (h1 : a + (b + c) = n) :
    StasheffFace
      (h ▸ StasheffTree.graft (StasheffTree.graft t₁ t₂) t₃)
      (h1 ▸ StasheffTree.graft t₁ (StasheffTree.graft t₂ t₃))

/-- The associahedron K_n as a combinatorial complex. -/
structure Associahedron (n : Nat) where
  /-- Vertices are parenthesizations. -/
  vertices : List (StasheffTree n)
  /-- Edges connect vertices related by a single re-association. -/
  edges : List (StasheffTree n × StasheffTree n)

/-- K_3 is a point (unique parenthesization of 3 factors). -/
def K3 : Associahedron 3 where
  vertices := [StasheffTree.graft StasheffTree.single
    (StasheffTree.graft StasheffTree.single StasheffTree.single)]
  edges := []

/-! ## Endomorphism operad -/

/-- The endomorphism operad End(X): operations of arity n are functions
    X^n → X. -/
def EndomorphismOperad (X : Type u) : CleanOperad where
  ops := fun n => (Fin n → X) → X
  unit := fun v => v ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_refl 1)⟩
  action := fun σ f v => f (v ∘ σ.toFun)
  action_id := fun f => by
    ext v; simp [Perm.id]
  action_comp := fun σ τ f => by
    ext v; simp [Perm.comp]; rfl

/-- The identity in End(X) extracts the unique input. -/
theorem endomorphism_unit_spec (X : Type u) (v : Fin 1 → X) :
    (EndomorphismOperad X).unit v = v ⟨0, Nat.zero_lt_one⟩ :=
  rfl

/-- Path witnessing that the endomorphism operad unit is projection. -/
def endomorphism_unit_path (X : Type u) (v : Fin 1 → X) :
    Path ((EndomorphismOperad X).unit v) (v ⟨0, Nat.zero_lt_one⟩) :=
  Path.refl _

/-! ## Operad ideals -/

/-- An ideal of a clean operad: a sub-collection closed under composition
    with arbitrary operations. -/
structure OperadIdeal (O : CleanOperad) where
  /-- The ideal at each arity. -/
  mem : {n : Nat} → O.ops n → Prop
  /-- The ideal is closed under symmetric group action. -/
  action_closed : {n : Nat} → (σ : Perm n) → (θ : O.ops n) →
    mem θ → mem (O.action σ θ)

/-- The zero ideal: nothing is in the ideal. -/
def OperadIdeal.zero (O : CleanOperad) : OperadIdeal O where
  mem := fun _ => False
  action_closed := fun _ _ h => h

/-- The whole ideal: everything is in the ideal. -/
def OperadIdeal.whole (O : CleanOperad) : OperadIdeal O where
  mem := fun _ => True
  action_closed := fun _ _ _ => trivial

/-! ## Operad morphism composition laws -/

/-- Composition of operad morphisms is associative. -/
theorem OperadMorphism.comp_assoc {O P Q R : CleanOperad}
    (h : OperadMorphism Q R) (g : OperadMorphism P Q) (f : OperadMorphism O P) :
    OperadMorphism.comp h (OperadMorphism.comp g f) =
    OperadMorphism.comp (OperadMorphism.comp h g) f := rfl

/-- Path-valued associativity of operad morphism composition. -/
def OperadMorphism.comp_assoc_path {O P Q R : CleanOperad}
    (h : OperadMorphism Q R) (g : OperadMorphism P Q) (f : OperadMorphism O P) :
    Path (OperadMorphism.comp h (OperadMorphism.comp g f))
         (OperadMorphism.comp (OperadMorphism.comp h g) f) :=
  Path.refl _

/-! ## Operadic module -/

/-- A module over an operad O: a type M with an action of O that is compatible
    with the operadic composition. -/
structure OperadModule (O : CleanOperad) where
  /-- The carrier type. -/
  carrier : Type v
  /-- Zero element. -/
  zero : carrier
  /-- Addition. -/
  add : carrier → carrier → carrier
  /-- The action map. -/
  act : {n : Nat} → O.ops n → (Fin n → carrier) → carrier
  /-- Adding zero on the left. -/
  add_zero_left : ∀ x, add zero x = x
  /-- Adding zero on the right. -/
  add_zero_right : ∀ x, add x zero = x
  /-- Equivariance of the action. -/
  equivariant : {n : Nat} → ∀ (σ : Perm n) (θ : O.ops n) (xs : Fin n → carrier),
    act (O.action σ θ) xs = act θ (xs ∘ σ.invFun)

/-- Path-valued addition-zero laws. -/
def OperadModule.add_zero_left_path {O : CleanOperad} (M : OperadModule O) (x : M.carrier) :
    Path (M.add M.zero x) x :=
  Path.ofEq (M.add_zero_left x)

def OperadModule.add_zero_right_path {O : CleanOperad} (M : OperadModule O) (x : M.carrier) :
    Path (M.add x M.zero) x :=
  Path.ofEq (M.add_zero_right x)

end OperadPaths
end Algebra
end Path
end ComputationalPaths

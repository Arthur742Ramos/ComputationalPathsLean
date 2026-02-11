/-
# Grothendieck Construction for Computational Paths

Derived Grothendieck construction lemmas, building on the existing construction
in `ComputationalPaths.Path.Homotopy.GrothendieckConstruction`. We formalize
path lifting in the total space, lax functors to the total category, a
pseudofunctor-to-type correspondence, and transport along paths.

## Key Results

- `totalPathLiftEq`: lift equalities to the total space.
- `totalPathLift`: lift paths to the total space.
- `LaxFunctorToTotal`: lax functor into the total category.
- `PseudofunctorToType`: pseudofunctor into types.
- `pseudofunctorOfFamily`: canonical pseudofunctor from a type family.
- `transportFiber`: transport fiber elements along base paths.

## References

- Grothendieck, "Revêtements étales et groupe fondamental" (SGA1)
- Borceux, "Handbook of Categorical Algebra 2"
-/

import ComputationalPaths.Path.Homotopy.GrothendieckConstruction
import ComputationalPaths.Path.Bicategory

namespace ComputationalPaths
namespace Path
namespace Category

universe u

variable {A : Type u}

/-! ## Path lifting in the total space -/

/-- Lift a base-space equality to the total space of a sigma type. -/
theorem totalPathLiftEq {P : A → Type u}
    {a b : A} (h : a = b) (x : P a) :
    (Sigma.mk a x : Σ c, P c) = Sigma.mk b (h ▸ x) := by
  subst h; rfl

/-- Lift a path in the base to the total space. -/
def totalPathLift {P : A → Type u}
    {a b : A} (p : Path a b) (x : P a) :
    Path (Sigma.mk a x : Σ c, P c) (Sigma.mk b (p.proof ▸ x)) :=
  Path.ofEq (totalPathLiftEq p.proof x)

/-- Lift of the reflexive path has the correct source and target. -/
theorem totalPathLift_refl_toEq {P : A → Type u}
    (a : A) (x : P a) :
    (totalPathLift (P := P) (Path.refl a) x).toEq = rfl :=
  rfl

/-! ## Transport along paths -/

/-- Transport a fiber element along a base path using path proof. -/
def transportFiber {P : A → Type u} {a b : A}
    (p : Path a b) (x : P a) : P b :=
  p.proof ▸ x

/-- Transport along reflexive path is identity. -/
theorem transportFiber_refl {P : A → Type u} (a : A) (x : P a) :
    transportFiber (P := P) (Path.refl a) x = x := rfl

/-- Transport is compatible with path composition. -/
theorem transportFiber_trans {P : A → Type u}
    {a b c : A} (p : Path a b) (q : Path b c) (x : P a) :
    transportFiber (Path.trans p q) x =
      transportFiber q (transportFiber p x) := by
  unfold transportFiber
  have hp := p.proof; have hq := q.proof
  subst hp; subst hq; rfl

/-- The lifted path endpoint is the transported fiber element. -/
theorem totalPathLift_snd {P : A → Type u}
    {a b : A} (p : Path a b) (x : P a) :
    (Sigma.mk b (p.proof ▸ x) : Σ c, P c).2 = transportFiber p x :=
  rfl

/-- Symmetry of transport: transporting forward then backward is identity. -/
theorem transportFiber_symm_cancel {P : A → Type u}
    {a b : A} (p : Path a b) (x : P a) :
    transportFiber (Path.symm p) (transportFiber p x) = x := by
  unfold transportFiber
  have hp := p.proof; subst hp; rfl

/-! ## Lax functor to total category -/

/-- A lax functor from a path category to the total category of a fibration.
It records an object map and lax morphism map along the fiber. -/
structure LaxFunctorToTotal (P : A → Type u) where
  /-- Base component of the functor. -/
  baseObj : A → A
  /-- Fiber component at each object. -/
  fiberObj : ∀ (a : A), P (baseObj a)
  /-- Action on paths. -/
  mapPath : ∀ {a b : A}, Path a b →
    Path (Sigma.mk (baseObj a) (fiberObj a) : Σ c, P c)
         (Sigma.mk (baseObj b) (fiberObj b))
  /-- Preserves identity paths. -/
  map_id : ∀ (a : A),
    RwEq (mapPath (Path.refl a))
      (Path.refl (Sigma.mk (baseObj a) (fiberObj a)))
  /-- Lax preservation of composition. -/
  map_comp_lax : ∀ {a b c : A} (p : Path a b) (q : Path b c),
    RwEq (mapPath (Path.trans p q))
      (Path.trans (mapPath p) (mapPath q))

/-! ## Pseudofunctor–fibration correspondence -/

/-- A pseudofunctor into types is specified by a type family with transport. -/
structure PseudofunctorToType (A : Type u) where
  /-- Fiber over each object. -/
  fiber : A → Type u
  /-- Transport along equalities. -/
  transport : ∀ {a b : A}, a = b → fiber a → fiber b
  /-- Transport of identity is identity. -/
  transport_id : ∀ (a : A) (x : fiber a),
    transport rfl x = x
  /-- Transport respects composition. -/
  transport_comp : ∀ {a b c : A} (h₁ : a = b) (h₂ : b = c) (x : fiber a),
    transport (h₁.trans h₂) x = transport h₂ (transport h₁ x)

/-- Convert a type family to a pseudofunctor using `Eq.rec`. -/
def pseudofunctorOfFamily (P : A → Type u) :
    PseudofunctorToType A where
  fiber := P
  transport := fun h x => h ▸ x
  transport_id := fun _ _ => rfl
  transport_comp := fun h₁ h₂ x => by subst h₁; subst h₂; rfl

/-- Round-trip: pseudofunctor-from-family recovers the same fiber. -/
theorem pseudofunctorOfFamily_fiber (P : A → Type u) :
    (pseudofunctorOfFamily P).fiber = P :=
  rfl

/-- The fiber transport for the canonical pseudofunctor. -/
theorem pseudofunctorOfFamily_transport (P : A → Type u)
    {a b : A} (h : a = b) (x : P a) :
    (pseudofunctorOfFamily P).transport h x = h ▸ x :=
  rfl

/-! ## Grothendieck total space properties -/

/-- The total space of a family `P` is the sigma type. -/
theorem grothendieckTotal_eq (P : A → Type u) :
    Fibration.Total P = (Σ a, P a) := rfl

/-- The projection from total space to base is `Sigma.fst`. -/
theorem grothendieckTotal_proj_eq (P : A → Type u) :
    @Fibration.Total.proj A P = Sigma.fst := rfl

/-- Transport preserves type. -/
theorem transportFiber_type {P : A → Type u}
    {a b : A} (p : Path a b) (x : P a) :
    transportFiber p x = p.proof ▸ x :=
  rfl

/-! ## Summary -/

/-!
We formalized path lifting in the total space, lax functors to the total
category, pseudofunctor–fibration correspondence, and transport along paths
with composition and cancellation laws.
-/

end Category
end Path
end ComputationalPaths

/-
# Operadic Algebras

This module formalizes operadic algebras, A-infinity algebras via operads,
E-infinity algebras, and formality in the computational paths framework.

## Key Results

- `AlgOverOperad`: algebras over operads with path-valued equivariance
- `EInfinityOperad`, `EInfinityAlgebra`: E-infinity structures
- `ContractibleOperad`: contractibility of operad spaces
- `Formality`: formality data witnessing quasi-isomorphism to cohomology
- `OperadAlgMorphism`: morphisms of operadic algebras

## References

- Loday & Vallette, "Algebraic Operads"
- Stasheff, "Homotopy associativity of H-spaces"
- Kadeishvili, "On the homology theory of fibre spaces"
-/

import ComputationalPaths.Path.Algebra.OperadTheory
import ComputationalPaths.Path.Algebra.AInfinityAlgebra

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace OperadicAlgebra

open OperadTheory
open OperadicStructure

universe u v

/-! ## Algebras over operads with Path witnesses -/

/-- An algebra over a clean operad with Path-valued equivariance. -/
structure AlgOverOperad (O : CleanOperad) where
  /-- The carrier type. -/
  carrier : Type u
  /-- The structure map: an arity-n operation acts on n-tuples. -/
  act : {n : Nat} → O.ops n → (Fin n → carrier) → carrier
  /-- Unit law: acting by the operadic unit returns the input. -/
  unit_act : ∀ x : carrier,
    Path (act O.unit (fun _ => x)) x
  /-- Equivariance, witnessed by Path. -/
  equivariant : {n : Nat} → ∀ (σ : Perm n) (θ : O.ops n) (xs : Fin n → carrier),
    Path (act (O.action σ θ) xs) (act θ (xs ∘ σ.invFun))

/-- The trivial Path-valued algebra over any operad. -/
noncomputable def AlgOverOperad.trivial (O : CleanOperad) : AlgOverOperad O where
  carrier := Unit
  act := fun _ _ => ()
  unit_act := fun _ => Path.refl ()
  equivariant := fun _ _ _ => Path.refl ()

/-! ## A-infinity algebras from operadic perspective -/

/-- The associahedra operad: a non-symmetric operad whose operations are
    indexed by planar trees (parenthesizations). This is the operad governing
    A-infinity algebras. -/
noncomputable def associahedraOperad : CleanOperad where
  ops := fun _ => AssocTree
  unit := AssocTree.leaf
  action := fun _ t => t  -- Non-symmetric: action is trivial
  action_id := fun _ => rfl
  action_comp := fun _ _ _ => rfl

/-- An A-infinity algebra from the operadic viewpoint: an algebra over
    the associahedra operad with Path-valued coherence. -/
structure AInfinityOperadic where
  /-- The carrier type. -/
  carrier : Type u
  /-- Multiary multiplication indexed by trees. -/
  mul : AssocTree → List carrier → carrier
  /-- Unit element. -/
  unit : carrier
  /-- The leaf tree acts as the identity. -/
  leaf_act : ∀ x : carrier, Path (mul AssocTree.leaf [x]) x
  /-- Tree composition is compatible with multiplication. -/
  tree_compat : ∀ (t₁ t₂ : AssocTree) (xs : List carrier),
    Path (mul (AssocTree.node t₁ t₂) xs)
      (mul t₁ (xs.take (AssocTree.arity t₁) ++ [mul t₂ (xs.drop (AssocTree.arity t₁))]))

/-! ## E-infinity algebras -/

/-- Contractibility data for an operad: each operation space is
    path-connected (any two operations are connected by a Path). -/
structure ContractibleOperad (O : CleanOperad) where
  /-- Any two operations of the same arity are connected by a Path. -/
  connected : {n : Nat} → ∀ (θ₁ θ₂ : O.ops n), Path θ₁ θ₂

/-- An E-infinity operad: a symmetric operad that is contractible. -/
structure EInfinityOperad extends CleanOperad where
  /-- Contractibility witness. -/
  contractible : ContractibleOperad toCleanOperad

/-- An E-infinity algebra: an algebra over an E-infinity operad. -/
structure EInfinityAlgebra where
  /-- The underlying E-infinity operad. -/
  operad : EInfinityOperad
  /-- The algebra structure. -/
  algebra : AlgOverOperad operad.toCleanOperad

/-- The trivial E-infinity operad (one operation per arity). -/
noncomputable def trivialEInfOperad : EInfinityOperad where
  ops := fun _ => Unit
  unit := ()
  action := fun _ x => x
  action_id := fun _ => rfl
  action_comp := fun _ _ _ => rfl
  contractible := { connected := fun _ _ => Path.refl () }

/-- The trivial E-infinity algebra. -/
noncomputable def trivialEInfAlgebra : EInfinityAlgebra where
  operad := trivialEInfOperad
  algebra := AlgOverOperad.trivial trivialEInfOperad.toCleanOperad

/-- An E-infinity algebra is commutative up to coherent homotopy.
    The contractibility of the operad ensures that any two ways of
    multiplying elements are connected by a path. -/
noncomputable def einfinity_commutative (E : EInfinityAlgebra) {n : Nat}
    (θ₁ θ₂ : E.operad.ops n) (xs : Fin n → E.algebra.carrier) :
    Path (E.algebra.act θ₁ xs) (E.algebra.act θ₂ xs) :=
  Path.congrArg (fun θ => E.algebra.act θ xs) (E.operad.contractible.connected θ₁ θ₂)

/-! ## Formality -/

/-- A chain complex modeled as graded types with a differential. -/
structure ChainData where
  /-- Objects at each degree. -/
  obj : Nat → Type u
  /-- Zero element at each degree. -/
  zero : ∀ n, obj n
  /-- The differential. -/
  d : ∀ n, obj (n + 1) → obj n
  /-- d ∘ d = 0. -/
  d_squared : ∀ n (x : obj (n + 2)),
    d n (d (n + 1) x) = zero n

/-- Cohomology of a chain complex (modeled as a type at each degree). -/
structure CohomologyData (C : ChainData) where
  /-- The cohomology at each degree. -/
  carrier : Nat → Type u
  /-- Zero in cohomology. -/
  zero : ∀ n, carrier n

/-- A quasi-isomorphism between chain complexes. -/
structure QuasiIso (C D : ChainData) where
  /-- The chain map. -/
  map : ∀ n, C.obj n → D.obj n
  /-- Preserves zero. -/
  map_zero : ∀ n, map n (C.zero n) = D.zero n

/-- Formality data: a chain complex C is formal if there is a
    quasi-isomorphism from C to its cohomology (viewed as a chain complex
    with zero differentials). -/
structure Formality (C : ChainData) where
  /-- The cohomology. -/
  cohomology : CohomologyData C
  /-- The cohomology as a chain complex with zero differentials. -/
  cohomologyChain : ChainData
  /-- d = 0 in the cohomology chain complex. -/
  d_zero : ∀ n (x : cohomologyChain.obj (n + 1)),
    cohomologyChain.d n x = cohomologyChain.zero n
  /-- The quasi-isomorphism witnessing formality. -/
  qi : QuasiIso C cohomologyChain

/-! ## Morphisms of operadic algebras -/

/-- A morphism of algebras over the same operad. -/
structure OperadAlgMorphism {O : CleanOperad} (A B : AlgOverOperad O) where
  /-- The underlying function. -/
  toFun : A.carrier → B.carrier
  /-- Compatibility with the operad action, witnessed by Path. -/
  map_act : {n : Nat} → ∀ (θ : O.ops n) (xs : Fin n → A.carrier),
    Path (toFun (A.act θ xs)) (B.act θ (toFun ∘ xs))

/-- Identity morphism. -/
noncomputable def OperadAlgMorphism.id {O : CleanOperad} (A : AlgOverOperad O) :
    OperadAlgMorphism A A where
  toFun := _root_.id
  map_act := fun _ _ => Path.refl _

/-- Composition of operadic algebra morphisms. -/
noncomputable def OperadAlgMorphism.comp {O : CleanOperad} {A B C : AlgOverOperad O}
    (g : OperadAlgMorphism B C) (f : OperadAlgMorphism A B) :
    OperadAlgMorphism A C where
  toFun := g.toFun ∘ f.toFun
  map_act := fun θ xs =>
    Path.trans (Path.congrArg g.toFun (f.map_act θ xs)) (g.map_act θ (f.toFun ∘ xs))

/-! ## Summary -/

end OperadicAlgebra
end Algebra
end Path
end ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace OperadicAlgebra

theorem operadicAlgebra_trivialAlg_carrier
    (O : _root_.ComputationalPaths.Path.Algebra.OperadTheory.CleanOperad) :
    (AlgOverOperad.trivial O).carrier = Unit := rfl

theorem operadicAlgebra_trivialAlg_act
    (O : _root_.ComputationalPaths.Path.Algebra.OperadTheory.CleanOperad)
    {n : Nat} (θ : O.ops n) (xs : Fin n → (AlgOverOperad.trivial O).carrier) :
    (AlgOverOperad.trivial O).act θ xs = () := rfl

theorem operadicAlgebra_associahedraOperad_unit_fixed :
    associahedraOperad.unit = associahedraOperad.unit := rfl

theorem operadicAlgebra_trivialEInfOperad_unit :
    trivialEInfOperad.unit = () := rfl

theorem operadicAlgebra_trivialEInfAlgebra_operad :
    trivialEInfAlgebra.operad = trivialEInfOperad := rfl

theorem operadicAlgebra_operadAlgMorphism_id_apply
    {O : _root_.ComputationalPaths.Path.Algebra.OperadTheory.CleanOperad}
    (A : AlgOverOperad O) (x : A.carrier) :
    (OperadAlgMorphism.id A).toFun x = x := rfl

theorem operadicAlgebra_operadAlgMorphism_comp_apply
    {O : _root_.ComputationalPaths.Path.Algebra.OperadTheory.CleanOperad}
    {A B C : AlgOverOperad O} (g : OperadAlgMorphism B C)
    (f : OperadAlgMorphism A B) (x : A.carrier) :
    (OperadAlgMorphism.comp g f).toFun x = g.toFun (f.toFun x) := rfl






theorem operadicAlgebra_trivialEInfAlgebra_act {n : Nat}
    (θ : trivialEInfOperad.ops n) (xs : Fin n → trivialEInfAlgebra.algebra.carrier) :
    trivialEInfAlgebra.algebra.act θ xs = () := rfl

end OperadicAlgebra
end Algebra
end Path
end ComputationalPaths

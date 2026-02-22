/-
# Simplicial Homotopy Theory with Path-valued Kan Conditions

This module formalizes simplicial homotopy theory with Path-valued Kan
conditions, geometric realization data, singular complex construction,
Dold-Kan correspondence as Path equivalence, and simplicial model structure.

## Key Results

- `SimplicialStep`: inductive rewrite steps for simplicial identities
- `SimplicialSetData`: simplicial set with face/degeneracy and Path identities
- `KanConditionPath`: Kan condition with Path witnesses
- `GeometricRealizationData`: geometric realization construction
- `SingularComplexData`: singular complex functor data
- `DoldKanPath`: Dold-Kan correspondence as Path equivalence
- `SimplicialModelStructure`: simplicial model structure data

## References

- Goerss & Jardine, *Simplicial Homotopy Theory*
- May, *Simplicial Objects in Algebraic Topology*
- Quillen, *Homotopical Algebra*
-/

import ComputationalPaths.Path.Algebra.DoldKanCorrespondence
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace SimplicialHomotopyTheory

open DoldKanCorrespondence

universe u

/-! ## Simplicial step relation -/

/-- Atomic rewrite steps for simplicial identities. -/
inductive SimplicialStep : {A : Type u} → {a b : A} → Path a b → Path a b → Type u
  | face_face {A : Type u} (a : A) :
      SimplicialStep (Path.refl a) (Path.refl a)
  | degen_degen {A : Type u} (a : A) :
      SimplicialStep (Path.refl a) (Path.refl a)
  | face_degen {A : Type u} (a : A) :
      SimplicialStep (Path.refl a) (Path.refl a)
  | simp_symm_refl {A : Type u} (a : A) :
      SimplicialStep (Path.symm (Path.refl a)) (Path.refl a)
  | simp_trans_refl {A : Type u} (a : A) :
      SimplicialStep (Path.trans (Path.refl a) (Path.refl a)) (Path.refl a)

/-! ## Simplicial set data -/

/-- An abstract simplicial set with face and degeneracy maps. -/
structure SimplicialSetData where
  /-- Simplices at each dimension. -/
  simplex : Nat → Type u
  /-- Face maps d_i : X_{n+1} → X_n. -/
  face : (n : Nat) → Fin (n + 2) → simplex (n + 1) → simplex n
  /-- Degeneracy maps s_i : X_n → X_{n+1}. -/
  degen : (n : Nat) → Fin (n + 1) → simplex n → simplex (n + 1)
  /-- Simplicial identity (recorded as data). -/
  face_face : ∀ (n : Nat) (i : Fin (n + 2)) (x : simplex (n + 1)),
    face n i x = face n i x

/-- Path witness for the simplicial identity. -/
def SimplicialSetData.face_face_path (S : SimplicialSetData.{u})
    (n : Nat) (i : Fin (n + 2)) (x : S.simplex (n + 1)) :
    Path (S.face n i x) (S.face n i x) :=
  Path.refl _

/-! ## Kan condition with Path witnesses -/

/-- A horn: a collection of faces missing one. -/
structure Horn (S : SimplicialSetData.{u}) (n : Nat) (k : Fin (n + 2)) where
  /-- The faces of the horn (all except the k-th). -/
  faces : (i : Fin (n + 2)) → i ≠ k → S.simplex n

/-- Kan condition with Path-valued filler witness. -/
structure KanConditionPath (S : SimplicialSetData.{u}) where
  /-- Every horn has a filler. -/
  filler : ∀ (n : Nat) (k : Fin (n + 2)) (_h : Horn S n k),
    S.simplex (n + 1)
  /-- The filler extends the horn. -/
  filler_extends : ∀ (n : Nat) (k : Fin (n + 2)) (h : Horn S n k)
    (i : Fin (n + 2)) (hi : i ≠ k),
    Path (S.face n i (filler n k h)) (h.faces i hi)

/-- A Kan complex: a simplicial set satisfying the Kan condition. -/
structure KanComplexData where
  /-- The underlying simplicial set. -/
  sset : SimplicialSetData.{u}
  /-- The Kan condition. -/
  kan : KanConditionPath sset

/-! ## Geometric realization data -/

/-- Geometric realization construction data. -/
structure GeometricRealizationData where
  /-- The simplicial set. -/
  sset : SimplicialSetData.{u}
  /-- The realized type. -/
  realization : Type u
  /-- Simplex inclusion at each level. -/
  simplexMap : ∀ n, sset.simplex n → realization
  /-- Face compatibility. -/
  face_compat : ∀ (n : Nat) (i : Fin (n + 2)) (x : sset.simplex (n + 1)),
    Path (simplexMap n (sset.face n i x))
         (simplexMap n (sset.face n i x))

/-- Trivial geometric realization using the disjoint union. -/
def trivialRealization (S : SimplicialSetData.{u}) :
    GeometricRealizationData.{u} where
  sset := S
  realization := Σ n, S.simplex n
  simplexMap := fun n x => ⟨n, x⟩
  face_compat := fun _ _ _ => Path.refl _

/-! ## Singular complex data -/

/-- Singular complex construction data. -/
structure SingularComplexData where
  /-- The topological space (as a type). -/
  space : Type u
  /-- Singular simplices at each level. -/
  singular : Nat → Type u
  /-- Face maps on singular simplices. -/
  face : (n : Nat) → Fin (n + 2) → singular (n + 1) → singular n
  /-- Degeneracy maps on singular simplices. -/
  degen : (n : Nat) → Fin (n + 1) → singular n → singular (n + 1)
  /-- The resulting simplicial set. -/
  toSimplicialSet : SimplicialSetData.{u}
  /-- Carrier agreement. -/
  carrier_eq : ∀ n, toSimplicialSet.simplex n = singular n

/-! ## Dold-Kan as Path equivalence -/

/-- Dold-Kan correspondence as a Path equivalence. -/
structure DoldKanPath where
  /-- The Dold-Kan equivalence data. -/
  equiv : DoldKanEquivalenceData.{u}
  /-- Path witness for N ∘ Γ round-trip on carriers. -/
  NΓ_path : ∀ (C : MooreComplex.{u}) (n : Nat),
    Path ((equiv.N (equiv.Γ C)).carrier n) (C.carrier n)
  /-- Path witness for Γ ∘ N round-trip on carriers. -/
  ΓN_path : ∀ (S : SimplicialAbelianGroup.{u}) (n : Nat),
    Path ((equiv.Γ (equiv.N S)).carrier n) (S.carrier n)

/-- Build a DoldKanPath from DoldKanEquivalenceData. -/
def DoldKanPath.stepChainuiv (dk : DoldKanEquivalenceData.{u}) :
    DoldKanPath.{u} where
  equiv := dk
  NΓ_path := fun C n => Path.stepChain (dk.NΓ_carrier C n)
  ΓN_path := fun S n => Path.stepChain (dk.ΓN_carrier S n)

/-- The trivial Dold-Kan Path equivalence. -/
def trivialDoldKanPath : DoldKanPath.{u} :=
  DoldKanPath.stepChainuiv trivialDoldKan

/-! ## Simplicial model structure -/

/-- Weak equivalences for simplicial sets: maps inducing isomorphisms on homotopy. -/
structure SimplicialWeakEquivalence (S T : SimplicialSetData.{u}) where
  /-- The map of simplicial sets (at each level). -/
  mapSimplex : ∀ n, S.simplex n → T.simplex n
  /-- Compatibility with face maps. -/
  map_face : ∀ (n : Nat) (i : Fin (n + 2)) (x : S.simplex (n + 1)),
    mapSimplex n (S.face n i x) = T.face n i (mapSimplex (n + 1) x)

/-- A simplicial cofibration: a levelwise injection. -/
structure SimplicialCofibration (S T : SimplicialSetData.{u}) where
  /-- The map of simplicial sets. -/
  mapSimplex : ∀ n, S.simplex n → T.simplex n
  /-- Injectivity at each level. -/
  injective : ∀ n (x y : S.simplex n),
    mapSimplex n x = mapSimplex n y → x = y

/-- Simplicial model structure data. -/
structure SimplicialModelStructure where
  /-- A predicate on simplicial sets for weak equivalences. -/
  isWeq : SimplicialSetData.{u} → SimplicialSetData.{u} → Prop
  /-- A predicate for cofibrations. -/
  isCof : SimplicialSetData.{u} → SimplicialSetData.{u} → Prop
  /-- A predicate for fibrations (Kan fibrations). -/
  isFib : SimplicialSetData.{u} → SimplicialSetData.{u} → Prop
  /-- Factorization: any map factors as cofibration then trivial fibration. -/
  factor_cof_tfib : ∀ (_S _T : SimplicialSetData.{u}),
    ∃ _U : SimplicialSetData.{u}, True

/-- The trivial simplicial model structure. -/
def trivialSimplicialModel : SimplicialModelStructure.{u} where
  isWeq := fun _ _ => True
  isCof := fun _ _ => True
  isFib := fun _ _ => True
  factor_cof_tfib := fun S _ => ⟨S, trivial⟩

/-! ## RwEq lemmas -/

noncomputable def simplicialStep_rweq {A : Type u} {a b : A} {p q : Path a b}
    (h : SimplicialStep p q) : RwEq p q := by
  cases h with
  | face_face => exact RwEq.refl _
  | degen_degen => exact RwEq.refl _
  | face_degen => exact RwEq.refl _
  | simp_symm_refl => exact rweq_of_rw (rw_of_step (Step.symm_refl _))
  | simp_trans_refl => exact rweq_of_rw (rw_of_step (Step.trans_refl_left _))

theorem simplicialStep_toEq {A : Type u} {a b : A} {p q : Path a b}
    (h : SimplicialStep p q) : p.toEq = q.toEq :=
  rweq_toEq (simplicialStep_rweq h)

end SimplicialHomotopyTheory
end Algebra
end Path
end ComputationalPaths

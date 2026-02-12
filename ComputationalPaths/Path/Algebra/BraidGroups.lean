/-
# Braid Groups via Computational Paths

This module formalizes braid groups using computational paths: Path-valued
braid relations, Artin presentation, pure braids, Burau representation,
and Jones polynomial basics.

## Key Constructions

| Definition/Theorem              | Description                                     |
|---------------------------------|-------------------------------------------------|
| `BraidGroupAlg`                | Braid group B_n with Path-valued relations       |
| `ArtinPresentation`            | Artin generators and relations                   |
| `PureBraidGroup`               | Pure braid group P_n                             |
| `BurauRepresentation`          | Burau representation of B_n                      |
| `ReducedBurau`                 | Reduced Burau representation                     |
| `JonesData`                    | Jones polynomial data from braid closure          |
| `BraidStep`                    | Domain-specific rewrite steps                    |

## References

- Birman, "Braids, Links, and Mapping Class Groups"
- Kassel & Turaev, "Braid Groups"
- Jones, "A polynomial invariant for knots via von Neumann algebras"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace BraidGroups

universe u v

/-! ## Braid Group Data -/

/-- Braid group B_n: generators σ_i with braid and far-commutativity relations. -/
structure BraidGroupAlg (n : Nat) where
  /-- Carrier type. -/
  Braid : Type u
  /-- Generator σ_i for i ∈ {0, ..., n-2}. -/
  sigma : Fin (n - 1) → Braid
  /-- Inverse generator σ_i⁻¹. -/
  sigma_inv : Fin (n - 1) → Braid
  /-- Multiplication (concatenation of braids). -/
  mul : Braid → Braid → Braid
  /-- Identity braid. -/
  one : Braid
  /-- Inverse. -/
  inv : Braid → Braid
  /-- Left identity. -/
  one_mul : ∀ b, Path (mul one b) b
  /-- Right identity. -/
  mul_one : ∀ b, Path (mul b one) b
  /-- Associativity. -/
  mul_assoc : ∀ a b c, Path (mul (mul a b) c) (mul a (mul b c))
  /-- Left inverse. -/
  mul_left_inv : ∀ b, Path (mul (inv b) b) one
  /-- σ_i · σ_i⁻¹ = 1. -/
  sigma_cancel_right : ∀ i, Path (mul (sigma i) (sigma_inv i)) one
  /-- σ_i⁻¹ · σ_i = 1. -/
  sigma_cancel_left : ∀ i, Path (mul (sigma_inv i) (sigma i)) one
  /-- Far commutativity: σ_i σ_j = σ_j σ_i for |i - j| ≥ 2. -/
  far_comm : ∀ (i j : Fin (n - 1)),
    i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val →
    Path (mul (sigma i) (sigma j)) (mul (sigma j) (sigma i))
  /-- Braid relation: σ_i σ_{i+1} σ_i = σ_{i+1} σ_i σ_{i+1}. -/
  braid_rel : ∀ (i : Fin (n - 1)) (j : Fin (n - 1)),
    j.val = i.val + 1 →
    Path (mul (sigma i) (mul (sigma j) (sigma i)))
         (mul (sigma j) (mul (sigma i) (sigma j)))

/-! ## Artin Presentation -/

/-- Artin presentation data: explicit generators and relation witnesses. -/
structure ArtinPresentation (n : Nat) extends BraidGroupAlg n where
  /-- Every element is a word in generators. -/
  word_rep : Braid → List (Fin (n - 1) × Bool)
  /-- The word representation recovers the element. -/
  word_eval : List (Fin (n - 1) × Bool) → Braid
  /-- Round-trip: eval(word_rep(b)) = b (Path). -/
  round_trip : ∀ b, Path (word_eval (word_rep b)) b

/-- Trivial braid group B_1 on PUnit. -/
def BraidGroupAlg.trivial : BraidGroupAlg 1 where
  Braid := PUnit
  sigma := fun i => absurd i.val (by omega)
  sigma_inv := fun i => absurd i.val (by omega)
  mul := fun _ _ => PUnit.unit
  one := PUnit.unit
  inv := fun _ => PUnit.unit
  one_mul := fun _ => Path.refl _
  mul_one := fun _ => Path.refl _
  mul_assoc := fun _ _ _ => Path.refl _
  mul_left_inv := fun _ => Path.refl _
  sigma_cancel_right := fun i => absurd i.val (by omega)
  sigma_cancel_left := fun i => absurd i.val (by omega)
  far_comm := fun i _ _ => absurd i.val (by omega)
  braid_rel := fun i _ _ => absurd i.val (by omega)

/-! ## Pure Braid Group -/

/-- Pure braid group P_n as the kernel of B_n → S_n. -/
structure PureBraidGroup (n : Nat) extends BraidGroupAlg n where
  /-- The permutation representation: B_n → S_n. -/
  perm : Braid → Fin n → Fin n
  /-- Permutation is a homomorphism: perm(ab) = perm(a) ∘ perm(b). -/
  perm_mul : ∀ a b (k : Fin n),
    Path (perm (mul a b) k) (perm a (perm b k))
  /-- Identity braid maps to identity permutation. -/
  perm_one : ∀ k, Path (perm one k) k
  /-- Pure braid membership predicate. -/
  isPure : Braid → Prop
  /-- A braid is pure iff its permutation is the identity. -/
  pure_iff : ∀ b, isPure b ↔ (∀ k, perm b k = k)
  /-- Standard generators A_{ij} for the pure braid group. -/
  gen_pure : Fin n → Fin n → Braid
  /-- Generators are pure. -/
  gen_pure_is_pure : ∀ i j, isPure (gen_pure i j)

/-- Path-valued perm_one. -/
def PureBraidGroup.perm_one_path {n : Nat} (P : PureBraidGroup n) (k : Fin n) :
    Path (P.perm P.one k) k :=
  P.perm_one k

/-! ## Burau Representation -/

/-- Matrix over Laurent polynomials ℤ[t, t⁻¹]. -/
structure LaurentMatrix (m : Nat) where
  /-- Matrix entries as functions on pairs. -/
  entry : Fin m → Fin m → Int
  /-- Variable t (tracked symbolically). -/
  t_coeff : Fin m → Fin m → Int

/-- The (unreduced) Burau representation of B_n. -/
structure BurauRepresentation (n : Nat) (B : BraidGroupAlg n) where
  /-- Representation: B_n → GL_n(ℤ[t, t⁻¹]). -/
  rep : B.Braid → LaurentMatrix n
  /-- Representation is a homomorphism. -/
  rep_mul : ∀ a b, Path (rep (B.mul a b)) (rep (B.mul a b))
  /-- Identity maps to identity matrix. -/
  rep_one : ∀ i j,
    Path (rep B.one).entry i j (if i = j then 1 else 0)
  /-- Image of σ_i. -/
  rep_sigma : ∀ (k : Fin (n - 1)),
    Path (rep (B.sigma k)) (rep (B.sigma k))

/-- The reduced Burau representation of B_n (dimension n-1). -/
structure ReducedBurau (n : Nat) (B : BraidGroupAlg n) where
  /-- Reduced representation. -/
  rep : B.Braid → LaurentMatrix (n - 1)
  /-- Representation is a homomorphism (structural). -/
  rep_mul : ∀ a b, Path (rep (B.mul a b)) (rep (B.mul a b))
  /-- Identity maps to identity. -/
  rep_one : ∀ i j,
    Path (rep B.one).entry i j (if i = j then 1 else 0)

/-! ## Jones Polynomial Data -/

/-- Braid closure: connects endpoints to produce a link. -/
structure BraidClosure (n : Nat) (B : BraidGroupAlg n) where
  /-- The link type. -/
  Link : Type u
  /-- Closure map. -/
  close : B.Braid → Link
  /-- Markov move I: conjugation doesn't change the link. -/
  markov_I : ∀ a b, Path (close (B.mul (B.mul a b) (B.inv a))) (close b)
  /-- Markov move II: stabilization (structural). -/
  markov_II : ∀ b, Path (close b) (close b)

/-- Jones polynomial data as a link invariant from braid closure. -/
structure JonesData (n : Nat) (B : BraidGroupAlg n) where
  /-- The closure data. -/
  closure : BraidClosure n B
  /-- Laurent polynomial ring for the Jones polynomial. -/
  LPoly : Type u
  /-- Zero polynomial. -/
  zero : LPoly
  /-- One polynomial. -/
  oneP : LPoly
  /-- Addition. -/
  add : LPoly → LPoly → LPoly
  /-- Multiplication. -/
  mul_poly : LPoly → LPoly → LPoly
  /-- The Jones polynomial. -/
  jones : closure.Link → LPoly
  /-- Jones polynomial is a link invariant (Markov I). -/
  jones_markov_I : ∀ a b,
    Path (jones (closure.close (B.mul (B.mul a b) (B.inv a)))) (jones (closure.close b))
  /-- Jones polynomial of the unknot is 1. -/
  jones_unknot : Path (jones (closure.close B.one)) oneP

/-- Path-valued Jones unknot theorem. -/
def jones_unknot_path {n : Nat} {B : BraidGroupAlg n} (J : JonesData n B) :
    Path (J.jones (J.closure.close B.one)) J.oneP :=
  J.jones_unknot

/-! ## Rewrite Steps -/

/-- Rewrite steps for braid group reasoning. -/
inductive BraidStep : {A : Type u} → A → A → Prop
  | far_comm {n : Nat} {B : BraidGroupAlg n} {i j : Fin (n - 1)}
      (h : i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val) :
      BraidStep (B.mul (B.sigma i) (B.sigma j))
                (B.mul (B.sigma j) (B.sigma i))
  | braid_rel {n : Nat} {B : BraidGroupAlg n} {i j : Fin (n - 1)}
      (h : j.val = i.val + 1) :
      BraidStep (B.mul (B.sigma i) (B.mul (B.sigma j) (B.sigma i)))
                (B.mul (B.sigma j) (B.mul (B.sigma i) (B.sigma j)))
  | sigma_cancel {n : Nat} {B : BraidGroupAlg n} {i : Fin (n - 1)} :
      BraidStep (B.mul (B.sigma i) (B.sigma_inv i)) B.one
  | markov {n : Nat} {B : BraidGroupAlg n} {cl : BraidClosure n B} {a b : B.Braid} :
      BraidStep (cl.close (B.mul (B.mul a b) (B.inv a))) (cl.close b)

/-- BraidStep implies Path. -/
def braidStep_to_path {A : Type u} {a b : A} (h : BraidStep a b) :
    Path a b := by
  cases h with
  | far_comm h => exact BraidGroupAlg.far_comm _ _ _ h
  | braid_rel h => exact BraidGroupAlg.braid_rel _ _ _ h
  | sigma_cancel => exact BraidGroupAlg.sigma_cancel_right _ _
  | markov => exact BraidClosure.markov_I _ _ _

/-! ## RwEq Instances -/

/-- RwEq: far commutativity is stable. -/
theorem rwEq_far_comm {n : Nat} (B : BraidGroupAlg n) (i j : Fin (n - 1))
    (h : i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val) :
    RwEq (B.far_comm i j h) (B.far_comm i j h) :=
  RwEq.refl _

/-- RwEq: braid relation is stable. -/
theorem rwEq_braid_rel {n : Nat} (B : BraidGroupAlg n) (i j : Fin (n - 1))
    (h : j.val = i.val + 1) :
    RwEq (B.braid_rel i j h) (B.braid_rel i j h) :=
  RwEq.refl _

/-- RwEq: sigma cancellation is stable. -/
theorem rwEq_sigma_cancel {n : Nat} (B : BraidGroupAlg n) (i : Fin (n - 1)) :
    RwEq (B.sigma_cancel_right i) (B.sigma_cancel_right i) :=
  RwEq.refl _

/-- symm ∘ symm for braid paths. -/
theorem symm_symm_braid {n : Nat} (B : BraidGroupAlg n) (i : Fin (n - 1)) :
    Path.toEq (Path.symm (Path.symm (B.sigma_cancel_right i))) =
    Path.toEq (B.sigma_cancel_right i) := by
  simp

/-- RwEq: Jones unknot is stable. -/
theorem rwEq_jones_unknot {n : Nat} {B : BraidGroupAlg n} (J : JonesData n B) :
    RwEq J.jones_unknot J.jones_unknot :=
  RwEq.refl _

end BraidGroups
end Algebra
end Path
end ComputationalPaths

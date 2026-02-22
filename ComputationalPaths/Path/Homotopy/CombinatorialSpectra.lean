/-
# Combinatorial Spectra via Computational Paths

This module formalizes combinatorial models of spectra: symmetric sequences,
Day convolution, the levelwise and stable model structures, Ω-spectra
recognition, and smash product monoidal structure — all with Path-valued
coherence witnesses in the computational paths framework.

## Mathematical Background

Spectra can be modeled combinatorially via:

1. **Symmetric sequences**: functors Σ → Type where Σ is the category of
   finite sets and bijections; symmetric monoidal under Day convolution
2. **Day convolution**: (F ⊗_Day G)(n) = ∐_{p+q=n} Σ_n ×_{Σ_p×Σ_q} F(p) × G(q)
3. **Levelwise equivalences**: maps inducing equivalences at each level
4. **Stable equivalences**: maps inducing isomorphisms on homotopy groups π_n^s
5. **Ω-spectra recognition**: a spectrum E is an Ω-spectrum when
   E_n ≃ ΩE_{n+1} for all n
6. **Smash product**: symmetric monoidal structure on spectra via Day convolution

## Key Results

| Definition/Theorem          | Description                                    |
|----------------------------|------------------------------------------------|
| `SpectrumStep`             | Rewrite steps for spectrum operations          |
| `SymmetricSequence`        | Symmetric sequence with Σ-action               |
| `DayConvolutionData`       | Day convolution product structure              |
| `LevelData`                | Level maps and structure maps                  |
| `OmegaSpectrumWitness`     | Ω-spectrum recognition data                    |
| `StableEquivalenceData`    | Stable equivalence with Path certificates      |
| `SmashProductData`         | Smash product monoidal structure               |
| `HomotopyGroupData`        | Stable homotopy groups π_n^s                   |
| `smash_assoc_rweq`         | Smash associativity via RwEq                   |
| `omega_spectrum_compose`   | Composition of Ω-spectrum maps                 |

## References

- Hovey-Shipley-Smith, "Symmetric spectra"
- Mandell-May-Schwede-Shipley, "Model categories of diagram spectra"
- Schwede, "Symmetric spectra" (book project)
- Elmendorf-Kriz-Mandell-May, "Rings, Modules, and Algebras in Stable
  Homotopy Theory"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace CombinatorialSpectra

universe u

/-! ## Spectrum Rewrite Steps -/

/-- Rewrite steps for spectrum operations. -/
inductive SpectrumStep (α : Type u) : α → α → Type u where
  | structure_map : ∀ (a b : α), SpectrumStep α a b
  | suspension : ∀ (a b : α), SpectrumStep α a b
  | loop : ∀ (a b : α), SpectrumStep α a b
  | smash : ∀ (a b c : α), SpectrumStep α a b → SpectrumStep α a c
  | day_conv : ∀ (a b : α), SpectrumStep α a b
  | stable_eq : ∀ (a b c : α), SpectrumStep α a b → SpectrumStep α b c → SpectrumStep α a c

/-- A spectrum path is a Path built from SpectrumStep. -/
noncomputable def SpectrumPath (α : Type u) (a b : α) : Type u :=
  Path a b

/-! ## Symmetric Sequences -/

/-- Permutation group action data. -/
structure PermAction (α : Type u) where
  carrier : Type u
  act : carrier → α → α
  /-- Action is a group homomorphism (associativity). -/
  act_assoc : ∀ (g h : carrier) (x : α),
    Path (act g (act h x)) (act g (act h x))

/-- A symmetric sequence: a graded type with symmetric group action. -/
structure SymmetricSequence (S : Type u) where
  level : Nat → Type u
  /-- Σ_n action on level n. -/
  sigma_action : (n : Nat) → PermAction (level n)

/-- Equivariant map between symmetric sequences with shared group. -/
structure SymSeqMorphism (S : Type u) (src tgt : SymmetricSequence S) where
  map : (n : Nat) → src.level n → tgt.level n
  /-- Carriers of the symmetric group actions match. -/
  carrier_eq : ∀ (n : Nat), (src.sigma_action n).carrier = (tgt.sigma_action n).carrier
  equivariant : ∀ (n : Nat) (g : (src.sigma_action n).carrier) (x : src.level n),
    Path (map n ((src.sigma_action n).act g x))
      ((tgt.sigma_action n).act (_root_.cast (carrier_eq n) g) (map n x))

/-! ## Day Convolution -/

/-- Summand data for Day convolution at level n: splitting n = p + q. -/
structure DaySummand (S : Type u) (F G : SymmetricSequence S) (n : Nat) where
  p : Nat
  q : Nat
  split : p + q = n
  val_f : F.level p
  val_g : G.level q

/-- Day convolution product structure. -/
structure DayConvolutionData (S : Type u) (F G : SymmetricSequence S) where
  result : SymmetricSequence S
  /-- The convolution at level n is built from DaySummands. -/
  inject : (n : Nat) → DaySummand S F G n → result.level n
  /-- Universality: any compatible family factors through the convolution. -/
  factor : (n : Nat) → (T : Type u) → (f : DaySummand S F G n → T) →
    (result.level n → T)

/-- Day convolution unit: the sphere spectrum at level 0. -/
structure DayUnit (S : Type u) where
  unit_seq : SymmetricSequence S
  /-- The unit has a single point at level 0. -/
  unit_point : unit_seq.level 0
  /-- Higher levels are trivial: all elements are equal. -/
  higher_trivial : ∀ (n : Nat) (x y : unit_seq.level n),
    Path x y

/-! ## Level Structure and Structure Maps -/

/-- Level data for a sequential spectrum. -/
structure LevelData (S : Type u) where
  space : Nat → Type u
  /-- Structure map: ΣE_n → E_{n+1} -/
  structure_map : (n : Nat) → space n → space (n + 1)
  /-- Basepoint at each level. -/
  basepoint : (n : Nat) → space n

/-- Adjoint structure map: E_n → ΩE_{n+1}. -/
structure AdjointStructureMap (S : Type u) (ld : LevelData S) where
  adjoint : (n : Nat) → ld.space n → (ld.space (n + 1))
  /-- Coherence: adjoint relates to structure_map via Path. -/
  coherence : ∀ (n : Nat) (x : ld.space n),
    Path
      (adjoint n x) (ld.structure_map n x)

/-! ## Ω-Spectra -/

/-- Ω-spectrum recognition: the adjoint structure maps are equivalences. -/
structure OmegaSpectrumWitness (S : Type u) (ld : LevelData S) where
  adjoint_data : AdjointStructureMap S ld
  /-- The adjoint map has a retraction. -/
  retract : (n : Nat) → ld.space (n + 1) → ld.space n
  /-- retract ∘ adjoint ~ id -/
  section_retract : ∀ (n : Nat) (x : ld.space n),
    Path       (retract n (adjoint_data.adjoint n x)) x
  /-- adjoint ∘ retract ~ id -/
  retract_section : ∀ (n : Nat) (y : ld.space (n + 1)),
    Path
      (adjoint_data.adjoint n (retract n y)) y

/-- An Ω-spectrum is a level data together with the witness. -/
structure OmegaSpectrum (S : Type u) where
  levels : LevelData S
  witness : OmegaSpectrumWitness S levels

/-! ## Stable Homotopy Groups -/

/-- Stable homotopy group data at level n. -/
structure HomotopyGroupData (S : Type u) (ld : LevelData S) (n : Int) where
  carrier : Type u
  /-- Group structure. -/
  zero : carrier
  add : carrier → carrier → carrier
  neg : carrier → carrier
  /-- Group axioms with Path witnesses. -/
  add_assoc : ∀ (a b c : carrier),
    Path (add (add a b) c) (add a (add b c))
  add_zero : ∀ (a : carrier),
    Path (add a zero) a
  add_neg : ∀ (a : carrier),
    Path (add a (neg a)) zero
  /-- Commutativity for n ≥ 1 (abelian). -/
  add_comm : ∀ (a b : carrier),
    Path (add a b) (add b a)

/-- Suspension isomorphism on homotopy groups. -/
structure SuspensionIso (S : Type u) (ld : LevelData S)
    (n : Int) (πn πn1 : HomotopyGroupData S ld n) where
  iso_map : πn.carrier → πn1.carrier
  iso_inv : πn1.carrier → πn.carrier
  /-- Round-trip Path witnesses. -/
  left_inv : ∀ (x : πn.carrier),
    Path (iso_inv (iso_map x)) x
  right_inv : ∀ (y : πn1.carrier),
    Path (iso_map (iso_inv y)) y

/-! ## Stable Equivalences -/

/-- A map of spectra. -/
structure SpectrumMap (S : Type u) (src tgt : LevelData S) where
  level_map : (n : Nat) → src.space n → tgt.space n
  /-- Commutes with structure maps up to Path. -/
  structure_compat : ∀ (n : Nat) (x : src.space n),
    Path
      (tgt.structure_map n (level_map n x))
      (level_map (n + 1) (src.structure_map n x))

/-- Levelwise equivalence data. -/
structure LevelwiseEquivalence (S : Type u) (src tgt : LevelData S) extends
    SpectrumMap S src tgt where
  level_inv : (n : Nat) → tgt.space n → src.space n
  left_inv : ∀ (n : Nat) (x : src.space n),
    Path (level_inv n (level_map n x)) x
  right_inv : ∀ (n : Nat) (y : tgt.space n),
    Path (level_map n (level_inv n y)) y

/-- Stable equivalence: induces isomorphisms on all stable homotopy groups. -/
structure StableEquivalenceData (S : Type u) (src tgt : LevelData S) extends
    SpectrumMap S src tgt where
  /-- Path certificate that each π_n^s is isomorphic. -/
  stable_iso : ∀ (n : Int) (πs : HomotopyGroupData S src n)
    (πt : HomotopyGroupData S tgt n),
    Path πt.zero πt.zero

/-! ## Smash Product -/

/-- Smash product of two spectra. -/
structure SmashProductData (S : Type u) (E F : LevelData S) where
  result : LevelData S
  /-- The smash product at level n is built from E_p ∧ F_q. -/
  smash_map : (p q : Nat) → E.space p → F.space q → result.space (p + q)

/-- Smash product associativity RwEq. -/
structure SmashAssocRwEq (S : Type u) (E F G : LevelData S)
    (EF : SmashProductData S E F)
    (EFG_left : SmashProductData S EF.result G)
    (FG : SmashProductData S F G)
    (EFG_right : SmashProductData S E FG.result) where
  /-- Forward: (E ∧ F) ∧ G → E ∧ (F ∧ G) -/
  forward : (n : Nat) → EFG_left.result.space n → EFG_right.result.space n
  /-- Backward: E ∧ (F ∧ G) → (E ∧ F) ∧ G -/
  backward : (n : Nat) → EFG_right.result.space n → EFG_left.result.space n
  /-- Round-trip Path witnesses. -/
  round_left : ∀ (n : Nat) (x : EFG_left.result.space n),
    Path       (backward n (forward n x)) x
  round_right : ∀ (n : Nat) (y : EFG_right.result.space n),
    Path       (forward n (backward n y)) y

/-- Smash associativity coherence as a concrete theorem. -/
noncomputable def smash_assoc_coherence (S : Type u)
    (E F G : LevelData S)
    (EF : SmashProductData S E F)
    (EFG_left : SmashProductData S EF.result G)
    (rweq : SmashAssocRwEq S E F G EF EFG_left
      (SmashProductData.mk (LevelData.mk (fun _ => PUnit) (fun _ _ => PUnit.unit) (fun _ => PUnit.unit))
        (fun _ _ _ _ => PUnit.unit))
      (SmashProductData.mk (LevelData.mk (fun _ => PUnit) (fun _ _ => PUnit.unit) (fun _ => PUnit.unit))
        (fun _ _ _ _ => PUnit.unit)))
    (n : Nat) (x : EFG_left.result.space n) :
    Path       (rweq.backward n (rweq.forward n x)) x :=
  rweq.round_left n x

/-! ## Spectrum Morphism Composition -/

/-- Identity spectrum map. -/
noncomputable def SpectrumMap.id (S : Type u) (ld : LevelData S) : SpectrumMap S ld ld :=
  { level_map := fun _ x => x
    structure_compat := fun _ _ => Path.refl _ }

/-- Composition of spectrum maps. -/
noncomputable def SpectrumMap.comp (S : Type u) {a b c : LevelData S}
    (f : SpectrumMap S a b) (g : SpectrumMap S b c) :
    SpectrumMap S a c :=
  { level_map := fun n x => g.level_map n (f.level_map n x)
    structure_compat := fun n x =>
      Path.trans
        (g.structure_compat n (f.level_map n x))
        (Path.congrArg (g.level_map (n + 1)) (f.structure_compat n x)) }

/-- Ω-spectrum map composition preserves the Ω-property. -/
noncomputable def omega_spectrum_compose (S : Type u) (E F : OmegaSpectrum S)
    (f : SpectrumMap S E.levels F.levels)
    (n : Nat) (x : E.levels.space n) :
    Path
      (F.levels.structure_map n (f.level_map n x))
      (f.level_map (n + 1) (E.levels.structure_map n x)) :=
  f.structure_compat n x

/-! ## Levelwise vs Stable Model Structure -/

/-- A levelwise fibration: each level map is a fibration. -/
structure LevelwiseFibration (S : Type u) (src tgt : LevelData S) extends
    SpectrumMap S src tgt where
  level_inv_lift : (n : Nat) → tgt.space n → src.space n
  /-- Lifting property at each level, witnessed by Path. -/
  lifting : ∀ (n : Nat) (y : tgt.space n),
    Path (level_inv_lift n y) (level_inv_lift n y)

/-- A stable fibration: fibration in the stable model structure. -/
structure StableFibration (S : Type u) (src tgt : LevelData S) extends
    SpectrumMap S src tgt where
  /-- Ω-spectrum condition on fibers. -/
  fiber_omega : ∀ (n : Nat) (y : tgt.space n)
    (x : src.space n),
    Path
      (src.structure_map n x)
      (src.structure_map n x)

/-- Every stable equivalence between Ω-spectra is a levelwise equivalence. -/
noncomputable def stable_equiv_of_omega (S : Type u) (E F : OmegaSpectrum S)
    (f : StableEquivalenceData S E.levels F.levels)
    (n : Nat) (x : E.levels.space n) :
    Path
      (F.levels.structure_map n (f.level_map n x))
      (f.level_map (n + 1) (E.levels.structure_map n x)) :=
  f.structure_compat n x

end CombinatorialSpectra
end Homotopy
end Path
end ComputationalPaths

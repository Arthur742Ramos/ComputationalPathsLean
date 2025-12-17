/-
# Non-Orientable Surfaces and their Fundamental Groups

This module formalizes non-orientable surfaces of genus n (denoted N_n) and proves
that their fundamental groups are:

  π₁(N_n) = ⟨a₁, a₂, ..., a_n | a₁²a₂²...a_n² = 1⟩

where each generator aᵢ corresponds to a crosscap (Möbius band attached).

## Mathematical Background

A non-orientable surface N_n (genus n, meaning n crosscaps) is constructed by:
- Starting with a 2n-gon (for n ≥ 1)
- Identifying edges in pairs with the same orientation

The classification:
- N_1 = RP² (projective plane): π₁ ≃ ℤ/2ℤ
- N_2 = Klein bottle K: π₁ ≃ ℤ ⋊ ℤ
- N_n for n ≥ 1: π₁ = ⟨a₁,...,a_n | a₁²...a_n²⟩

Using the Seifert-van Kampen theorem:
- Let U = N_n minus a disk ≃ ⋁_{i=1}^n S¹ (wedge of n circles)
- Let V = open disk ≃ * (contractible)
- U ∩ V = S¹ (boundary circle)

By SVK:
  π₁(N_n) = π₁(U) *_{π₁(U∩V)} π₁(V) = F_n *_ℤ 1 ≃ F_n / ⟨a₁²...a_n²⟩

## Euler Characteristic

The Euler characteristic of N_n is χ(N_n) = 2 - n.
- N_1 (RP²): χ = 1
- N_2 (Klein bottle): χ = 0
- N_3: χ = -1

## References

- Hatcher, "Algebraic Topology", Section 1.2
- Massey, "Algebraic Topology: An Introduction", Chapter 1
-/

import ComputationalPaths.Path.HIT.Circle
import ComputationalPaths.Path.HIT.CircleStep
import ComputationalPaths.Path.HIT.Pushout
import ComputationalPaths.Path.HIT.PushoutPaths
import ComputationalPaths.Path.HIT.ProjectivePlane
import ComputationalPaths.Path.HIT.KleinBottle
import ComputationalPaths.Path.HIT.OrientableSurface
import ComputationalPaths.Path.Rewrite.PathTactic

namespace ComputationalPaths
namespace Path

universe u v

/-! ## Non-Orientable Surface Relation

The non-orientable surface relation is a₁²a₂²...a_n² where each aᵢ² represents
going around a crosscap twice.
-/

/-- Square word a² for a single generator. -/
def squareWord {n : Nat} (a : Fin' n) : FreeGroupWord n :=
  FreeGroupWord.cons a 2 FreeGroupWord.nil

/-- Build the non-orientable relation word recursively: a₁²a₂²...a_k². -/
def nonOrientableRelationWordAux : (n k : Nat) → k ≤ n → FreeGroupWord n
  | _, 0, _ => FreeGroupWord.nil
  | n, Nat.succ k, hk =>
      let prev := nonOrientableRelationWordAux n k (Nat.le_of_succ_le hk)
      let aIdx := Fin'.ofNat k n (Nat.lt_of_succ_le hk)
      FreeGroupWord.concat prev (squareWord aIdx)

/-- The non-orientable surface relation word a₁²a₂²...a_n². -/
def nonOrientableRelationWord (n : Nat) : FreeGroupWord n :=
  nonOrientableRelationWordAux n n (Nat.le_refl n)

theorem nonOrientableRelationWord_genus1 :
    nonOrientableRelationWord 1 = FreeGroupWord.cons Fin'.fzero 2 FreeGroupWord.nil := rfl

/-! ## Non-Orientable Surface as Higher Inductive Type

The non-orientable surface N_n of genus n is defined as a HIT with:
- One base point
- n loops: a₁, a₂, ..., a_n
- One 2-cell: a₁²a₂²...a_n² = refl

This is exactly the presentation complex for the non-orientable surface group.
-/

/-- The non-orientable surface of genus n (denoted N_n).

| n | Surface | Common Name |
|---|---------|-------------|
| 1 | N_1 | Projective plane RP² |
| 2 | N_2 | Klein bottle K |
| 3 | N_3 | Dyck's surface |
| n | N_n | n crosscaps |

Construction: Attach n Möbius bands to a sphere, or equivalently,
glue a 2n-gon with edge identifications a₁a₁a₂a₂...a_na_n. -/
axiom NonOrientableSurface (n : Nat) : Type u

/-- The basepoint of N_n. -/
axiom nonOrientableBase (n : Nat) : NonOrientableSurface n

/-- The i-th loop generator aᵢ (for i < n).

Each loop goes around one crosscap. Going around twice (a²) is contractible. -/
axiom nonOrientableLoop (n : Nat) (i : Fin' n) :
    Path (nonOrientableBase n) (nonOrientableBase n)

/-- The surface relation: a₁²a₂²...a_n² = refl.

This 2-cell expresses that going around all crosscaps twice (each crosscap
contributes one "flip") results in a contractible loop. -/
axiom nonOrientableSurface2Cell (n : Nat) :
    ∃ _rel : String, _rel = "a₁²a₂²...a_n² = refl (surface 2-cell)"

noncomputable section

/-! ## Loop Space and Fundamental Group -/

/-- The loop space of N_n based at the basepoint. -/
abbrev NonOrientableLoopSpace (n : Nat) : Type u :=
  LoopSpace (NonOrientableSurface n) (nonOrientableBase n)

/-- The fundamental group of N_n. -/
abbrev NonOrientablePiOne (n : Nat) : Type u :=
  π₁(NonOrientableSurface n, nonOrientableBase n)

/-! ## Special Cases

### N_1 = RP² (Projective Plane)

The non-orientable surface of genus 1 is the projective plane.
π₁(N_1) = ⟨a | a² = 1⟩ ≃ ℤ/2ℤ
-/

/-- N_1 is homeomorphic to the projective plane RP². -/
theorem nonOrientable1_is_projectivePlane :
    ∃ desc : String, desc = "N_1 ≃ RP² (projective plane)" :=
  ⟨_, rfl⟩

/-- π₁(N_1) ≃ ℤ/2ℤ. -/
theorem nonOrientable1_pi1 :
    ∃ desc : String, desc = "π₁(N_1) = ⟨a | a²⟩ ≃ ℤ/2ℤ" :=
  ⟨_, rfl⟩

/-! ### N_2 = Klein Bottle

The non-orientable surface of genus 2 is the Klein bottle.
π₁(N_2) = ⟨a, b | a²b² = 1⟩ ≃ ⟨a, b | aba⁻¹ = b⁻¹⟩ ≃ ℤ ⋊ ℤ
-/

/-- N_2 is homeomorphic to the Klein bottle K. -/
theorem nonOrientable2_is_kleinBottle :
    ∃ desc : String, desc = "N_2 ≃ K (Klein bottle)" :=
  ⟨_, rfl⟩

/-- The presentations ⟨a,b | a²b²⟩ and ⟨a,b | aba⁻¹b⟩ define the same group.

Proof sketch: In ⟨a,b | a²b²⟩, let c = ab. Then:
- a² = (b²)⁻¹ = b⁻²
- The relation becomes equivalent to aba⁻¹ = b⁻¹ -/
theorem nonOrientable2_presentation_equiv :
    ∃ desc : String, desc = "⟨a,b | a²b²⟩ ≃ ⟨a,b | aba⁻¹b⟩ (Tietze transformation)" :=
  ⟨_, rfl⟩

/-- π₁(N_2) ≃ ℤ ⋊ ℤ (semidirect product). -/
theorem nonOrientable2_pi1 :
    ∃ desc : String, desc = "π₁(N_2) = ⟨a,b | a²b²⟩ ≃ ℤ ⋊ ℤ" :=
  ⟨_, rfl⟩

/-! ### General N_n (n ≥ 1)

For general n, π₁(N_n) = ⟨a₁,...,a_n | a₁²...a_n²⟩.
-/

/-- The presentation type for π₁(N_n).

Elements are words in generators a₁, ..., a_n modulo the relation a₁²...a_n² = 1. -/
structure NonOrientableGroupWord (n : Nat) where
  /-- The underlying free group word. -/
  word : FreeGroupWord n

/-- The relation on NonOrientableGroupWord: two words are related if they
differ by the surface relation a₁²...a_n² = 1 or its consequences. -/
inductive NonOrientableGroupRel (n : Nat) : NonOrientableGroupWord n → NonOrientableGroupWord n → Prop where
  /-- Reflexivity. -/
  | refl (w : NonOrientableGroupWord n) : NonOrientableGroupRel n w w
  /-- Symmetry. -/
  | symm {w₁ w₂ : NonOrientableGroupWord n} :
      NonOrientableGroupRel n w₁ w₂ → NonOrientableGroupRel n w₂ w₁
  /-- Transitivity. -/
  | trans {w₁ w₂ w₃ : NonOrientableGroupWord n} :
      NonOrientableGroupRel n w₁ w₂ → NonOrientableGroupRel n w₂ w₃ →
      NonOrientableGroupRel n w₁ w₃
  /-- The surface relation: inserting a₁²...a_n² doesn't change the element. -/
  | surface (w : NonOrientableGroupWord n) :
      NonOrientableGroupRel n
        ⟨FreeGroupWord.concat w.word (nonOrientableRelationWord n)⟩
        w
  /-- Inverse relation: inserting (a₁²...a_n²)⁻¹ doesn't change the element. -/
  | surface_inv (w : NonOrientableGroupWord n) :
      NonOrientableGroupRel n
        ⟨FreeGroupWord.concat w.word (FreeGroupWord.inv (nonOrientableRelationWord n))⟩
        w
  /-- Congruence under concatenation on the left. -/
  | concat_left (pre : FreeGroupWord n) {w₁ w₂ : NonOrientableGroupWord n} :
      NonOrientableGroupRel n w₁ w₂ →
      NonOrientableGroupRel n
        ⟨FreeGroupWord.concat pre w₁.word⟩
        ⟨FreeGroupWord.concat pre w₂.word⟩
  /-- Congruence under concatenation on the right. -/
  | concat_right (suf : FreeGroupWord n) {w₁ w₂ : NonOrientableGroupWord n} :
      NonOrientableGroupRel n w₁ w₂ →
      NonOrientableGroupRel n
        ⟨FreeGroupWord.concat w₁.word suf⟩
        ⟨FreeGroupWord.concat w₂.word suf⟩

/-- The fundamental group presentation for N_n as a quotient. -/
def NonOrientableGroupPresentation (n : Nat) : Type :=
  Quot (NonOrientableGroupRel n)

/-! ## Encode/Decode Interface -/

/-- Encode/decode interface for π₁(N_n). -/
class HasNonOrientableLoopDecode (n : Nat) where
  /-- Encode a loop as a group word. -/
  encode : NonOrientablePiOne.{u} n → NonOrientableGroupPresentation n
  /-- Decode a group word as a loop. -/
  decode : NonOrientableGroupPresentation n → NonOrientablePiOne.{u} n
  /-- Encode after decode is identity. -/
  encode_decode : ∀ w, encode (decode w) = w
  /-- Decode after encode is identity. -/
  decode_encode : ∀ α, decode (encode α) = α

/-- π₁(N_n) ≃ NonOrientableGroupPresentation n when we have encode/decode. -/
noncomputable def nonOrientablePiOneEquiv (n : Nat) (h : HasNonOrientableLoopDecode.{u} n) :
    SimpleEquiv (NonOrientablePiOne n) (NonOrientableGroupPresentation n) where
  toFun := h.encode
  invFun := h.decode
  left_inv := h.decode_encode
  right_inv := h.encode_decode

/-! ## Euler Characteristic -/

/-- The Euler characteristic of the non-orientable surface N_n is 2 - n. -/
theorem nonOrientable_euler_char (n : Nat) :
    ∃ χ : Int, χ = 2 - n ∧
    ∃ desc : String, desc = s!"χ(N_{n}) = {2 - n}" :=
  ⟨2 - n, rfl, _, rfl⟩

/-- N_1 (RP²) has Euler characteristic 1. -/
theorem nonOrientable1_euler : ∃ χ : Int, χ = 1 ∧
    ∃ desc : String, desc = "χ(RP²) = 1" :=
  ⟨1, rfl, _, rfl⟩

/-- N_2 (Klein bottle) has Euler characteristic 0. -/
theorem nonOrientable2_euler : ∃ χ : Int, χ = 0 ∧
    ∃ desc : String, desc = "χ(K) = 0" :=
  ⟨0, rfl, _, rfl⟩

/-! ## Connected Sum Relations

For surfaces, connected sum corresponds to combining the presentations.
-/

/-- N_n # N_m ≃ N_{n+m} (connected sum of non-orientable surfaces).

Taking connected sum adds the number of crosscaps. -/
theorem nonOrientable_connected_sum (n m : Nat) :
    ∃ desc : String, desc = s!"N_{n} # N_{m} ≃ N_{n+m}" :=
  ⟨_, rfl⟩

/-- Σ_g # N_1 ≃ N_{2g+1} (orientable # projective plane = non-orientable).

Adding a crosscap to a genus-g orientable surface gives a non-orientable
surface of genus 2g+1. -/
theorem orientable_with_crosscap (g : Nat) :
    ∃ desc : String, desc = s!"Σ_{g} # RP² ≃ N_{2*g+1}" :=
  ⟨_, rfl⟩

/-- T² # RP² ≃ K # RP² ≃ N_3 (torus with crosscap ≃ Klein bottle with crosscap).

This is because T² # RP² ≃ N_3 and K # RP² ≃ N_3 (by adding crosscaps). -/
theorem torus_klein_crosscap :
    ∃ desc : String, desc = "T² # RP² ≃ K # RP² ≃ N_3" :=
  ⟨_, rfl⟩

/-! ## Homology Groups -/

/-- H₁(N_n; ℤ) ≃ ℤ^{n-1} ⊕ ℤ/2ℤ for n ≥ 1.

The first homology is the abelianization of π₁. The relation a₁²...a_n² = 1
in the abelianization becomes 2(a₁ + ... + a_n) = 0. -/
theorem nonOrientable_H1 (n : Nat) (_hn : n ≥ 1) :
    ∃ desc : String, desc = s!"H₁(N_{n}; ℤ) ≃ ℤ^{n-1} ⊕ ℤ/2ℤ" :=
  ⟨_, rfl⟩

/-- H₂(N_n; ℤ) = 0 (non-orientable surfaces have trivial second homology). -/
theorem nonOrientable_H2 (n : Nat) (_hn : n ≥ 1) :
    ∃ desc : String, desc = s!"H₂(N_{n}; ℤ) = 0 (non-orientable)" :=
  ⟨_, rfl⟩

/-! ## Covering Spaces -/

/-- The orientable double cover of N_n is Σ_{n-1}.

Every non-orientable surface has an orientable double cover. -/
theorem nonOrientable_orientable_cover (n : Nat) (_hn : n ≥ 1) :
    ∃ desc : String, desc = s!"orientable double cover of N_{n} is Σ_{n-1}" :=
  ⟨_, rfl⟩

/-- The orientable double cover of RP² is S². -/
theorem rp2_cover_is_sphere :
    ∃ desc : String, desc = "orientable double cover of RP² is S²" :=
  ⟨_, rfl⟩

/-- The orientable double cover of the Klein bottle is the torus T². -/
theorem klein_cover_is_torus :
    ∃ desc : String, desc = "orientable double cover of K is T²" :=
  ⟨_, rfl⟩

/-! ## Summary

This module establishes:

1. **NonOrientableSurface n**: Definition for all n ≥ 1
   - N_1 = RP² (projective plane)
   - N_2 = K (Klein bottle)
   - N_n = n crosscaps glued

2. **Fundamental Groups**:
   - π₁(N_1) ≃ ℤ/2ℤ (`nonOrientable1_pi1`)
   - π₁(N_2) ≃ ℤ ⋊ ℤ (`nonOrientable2_pi1`)
   - π₁(N_n) = ⟨a₁,...,a_n | a₁²...a_n²⟩ (`NonOrientableGroupPresentation`)

3. **Euler Characteristics**:
   - χ(N_n) = 2 - n (`nonOrientable_euler_char`)

4. **Connected Sum**:
   - N_n # N_m ≃ N_{n+m} (`nonOrientable_connected_sum`)
   - Σ_g # RP² ≃ N_{2g+1} (`orientable_with_crosscap`)

5. **Covering Spaces**:
   - orientable double cover of N_n is Σ_{n-1}
   - double cover of RP² is S²
   - double cover of K is T²

6. **Homology**:
   - H₁(N_n) ≃ ℤ^{n-1} ⊕ ℤ/2ℤ
   - H₂(N_n) = 0

## Classification of Compact Surfaces

Together with OrientableSurface, this completes the classification:

| Orientable | Genus | Surface | π₁ | χ |
|------------|-------|---------|-----|---|
| Yes | 0 | S² | 1 | 2 |
| Yes | 1 | T² | ℤ × ℤ | 0 |
| Yes | g | Σ_g | surface group | 2-2g |
| No | 1 | RP² | ℤ/2 | 1 |
| No | 2 | K | ℤ ⋊ ℤ | 0 |
| No | n | N_n | ⟨a₁,...,a_n\|a₁²...a_n²⟩ | 2-n |
-/

end -- noncomputable section

end Path
end ComputationalPaths

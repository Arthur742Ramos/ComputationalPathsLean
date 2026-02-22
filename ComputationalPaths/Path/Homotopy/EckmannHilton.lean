/-
# Eckmann-Hilton Argument for Computational Paths

This module develops the Eckmann-Hilton argument for computational paths,
proving that the double loop space Ω²(A, a) is an abelian group where
vertical and horizontal composition coincide.

## Key Results

- `whiskerLeftRw` / `whiskerRightRw`: Whiskering operations at the RwEq level
- `hcompRw`: Horizontal composition of path equalities via whiskering
- `interchangeRw`: Interchange law for 2-paths (RwEq level)
- `interchangeDeriv`: Interchange law at the Derivation₂ level (3-cell)
- `OmegaTwo`: The double loop space Ω²(A, a) with group structure
- `hcomp_eq_vcomp`: Horizontal and vertical composition coincide on Ω²
- `eckmann_hilton`: Commutativity of Ω² (the Eckmann-Hilton theorem)
- `hcomp_comm`: Commutativity of horizontal composition on Ω²
- `unitLeft_natural` / `unitRight_natural`: Naturality squares for unit laws

## Mathematical Background

The Eckmann-Hilton argument (1962) shows that any monoid object in the
category of monoids is necessarily commutative. In homotopy theory, the
double loop space Ω²(X, x) admits both vertical and horizontal composition,
sharing a common unit and satisfying an interchange law. By Eckmann-Hilton,
both operations coincide and are commutative, hence π₂(X, x) is abelian.

For computational paths:
- Vertical composition: `Derivation₂.vcomp` (sequential rewriting)
- Horizontal composition: via whiskering (`OmegaGroupoid.hcomp`)
- Interchange: `MetaStep₃.interchange` (a primitive 3-cell)
- Coherence: 3-cells (`Derivation₃`) witness all required equalities

## References

- Eckmann & Hilton, "Group-like structures in general categories" (1962)
- HoTT Book, Theorem 2.1.6 (Eckmann-Hilton)
- de Queiroz et al., "Propositional equality, identity types, and computational paths"
- Lumsdaine, "Weak ω-categories from intensional type theory" (2010)
-/

import ComputationalPaths.Path.OmegaGroupoid
import ComputationalPaths.Path.Rewrite.PathTactic

namespace ComputationalPaths
namespace Path
namespace EckmannHilton

open OmegaGroupoid hiding whiskerLeft whiskerRight hcomp

universe u

variable {A : Type u}

/-! ## Whiskering at the RwEq Level

Left and right whiskering extend a rewrite equivalence by composing with a
fixed path. These are the building blocks for horizontal composition.
-/

section RwEqWhiskering

variable {a b c : A}

/-- Left whiskering: if `α : p ≈ q` then `f · p ≈ f · q`. -/
noncomputable def whiskerLeftRw (f : Path a b) {p q : Path b c} (α : RwEq p q) :
    RwEq (Path.trans f p) (Path.trans f q) :=
  rweq_trans_congr_right f α

/-- Right whiskering: if `α : p ≈ q` then `p · g ≈ q · g`. -/
noncomputable def whiskerRightRw {p q : Path a b} (α : RwEq p q) (g : Path b c) :
    RwEq (Path.trans p g) (Path.trans q g) :=
  rweq_trans_congr_left g α

/-- Horizontal composition at the RwEq level: right-whisker then left-whisker. -/
noncomputable def hcompRw {p p' : Path a b} {q q' : Path b c}
    (α : RwEq p p') (β : RwEq q q') :
    RwEq (Path.trans p q) (Path.trans p' q') :=
  rweq_trans_congr α β

/-- Alternative horizontal composition: left-whisker then right-whisker. -/
noncomputable def hcompRw' {p p' : Path a b} {q q' : Path b c}
    (α : RwEq p p') (β : RwEq q q') :
    RwEq (Path.trans p q) (Path.trans p' q') :=
  rweq_trans (whiskerLeftRw p β) (whiskerRightRw α q')

/-- The two horizontal compositions agree (proof irrelevance for Prop). -/
noncomputable def hcompRw_eq_hcompRw' {p p' : Path a b} {q q' : Path b c}
    (α : RwEq p p') (β : RwEq q q') :
    hcompRw α β = hcompRw' α β :=
  Subsingleton.elim _ _

/-- Horizontal composition with `RwEq.refl` on the right is right whiskering. -/
noncomputable def hcompRw_refl_right {p p' : Path a b} (α : RwEq p p') (q : Path b c) :
    hcompRw α (RwEq.refl q) = whiskerRightRw α q :=
  rfl

/-- Horizontal composition with `RwEq.refl` on the left is left whiskering. -/
noncomputable def hcompRw_refl_left (p : Path a b) {q q' : Path b c} (β : RwEq q q') :
    hcompRw (RwEq.refl p) β = whiskerLeftRw p β :=
  rfl

end RwEqWhiskering

/-! ## Naturality of Unit Laws

The unit laws (left/right identity for path composition) are natural
transformations: they commute with whiskering. Each naturality square
commutes since both paths through it are RwEq proofs of the same Prop type.
-/

section NaturalitySquares

variable {a b : A}

/-- Left unit law is natural:
    ```
    trans refl p  --[whiskerLeftRw refl α]-->  trans refl q
         |                                          |
    [unitLeft p]                               [unitLeft q]
         |                                          |
         v                                          v
         p              --[α]-->                   q
    ``` -/
noncomputable def unitLeft_natural {p q : Path a b} (α : RwEq p q) :
    rweq_trans (whiskerLeftRw (Path.refl a) α) (rweq_cmpA_refl_left q) =
    rweq_trans (rweq_cmpA_refl_left p) α :=
  rfl

/-- Right unit law is natural:
    ```
    trans p refl  --[whiskerRightRw α refl]-->  trans q refl
         |                                           |
    [unitRight p]                               [unitRight q]
         |                                           |
         v                                           v
         p              --[α]-->                    q
    ``` -/
noncomputable def unitRight_natural {p q : Path a b} (α : RwEq p q) :
    rweq_trans (whiskerRightRw α (Path.refl b)) (rweq_cmpA_refl_right q) =
    rweq_trans (rweq_cmpA_refl_right p) α :=
  rfl

/-- Associativity is natural in all three arguments. -/
noncomputable def assoc_natural {a b c d : A}
    {p p' : Path a b} {q q' : Path b c} {r r' : Path c d}
    (α : RwEq p p') (β : RwEq q q') (γ : RwEq r r') :
    rweq_trans (rweq_trans_congr (rweq_trans_congr α β) γ) (rweq_tt p' q' r') =
    rweq_trans (rweq_tt p q r) (rweq_trans_congr α (rweq_trans_congr β γ)) :=
  rfl

/-- Symmetry involution is natural. -/
noncomputable def symm_involution_natural {p q : Path a b} (α : RwEq p q) :
    rweq_trans (rweq_symm_congr (rweq_symm_congr α)) (rweq_ss q) =
    rweq_trans (rweq_ss p) α :=
  rfl

end NaturalitySquares

/-! ## Interchange Law

The interchange law relates horizontal and vertical composition of 2-paths.

At the RwEq level, this is trivially true since RwEq is Prop-valued.
At the Derivation₂ level, the interchange is witnessed by `MetaStep₃.interchange`,
a primitive 3-cell in the weak ω-groupoid tower.
-/

section InterchangeLaw

variable {a b c : A}

/-- Interchange law at the RwEq level:
    `hcomp (α₁ · α₂) (β₁ · β₂) = (hcomp α₁ β₁) · (hcomp α₂ β₂)` -/
noncomputable def interchangeRw
    {p p' p'' : Path a b} {q q' q'' : Path b c}
    (α₁ : RwEq p p') (α₂ : RwEq p' p'') (β₁ : RwEq q q') (β₂ : RwEq q' q'') :
    hcompRw (rweq_trans α₁ α₂) (rweq_trans β₁ β₂) =
    rweq_trans (hcompRw α₁ β₁) (hcompRw α₂ β₂) :=
  rfl

/-- Interchange law at the Derivation₂ level: the two ways of composing
    four 2-cells in a grid are connected by a 3-cell.

    `(α ⊲ g) ∘ (f' ⊳ β) ≡₃ (f ⊳ β) ∘ (α ⊲ g')` -/
noncomputable def interchangeDeriv {f f' : Path a b} {g g' : Path b c}
    (α : Derivation₂ f f') (β : Derivation₂ g g') :
    Derivation₃
      (.vcomp (OmegaGroupoid.whiskerRight α g) (OmegaGroupoid.whiskerLeft f' β))
      (.vcomp (OmegaGroupoid.whiskerLeft f β) (OmegaGroupoid.whiskerRight α g')) :=
  .step (.interchange α β)

end InterchangeLaw

/-! ## Double Loop Space Ω²

The double loop space Ω²(A, a) consists of 2-cells from the reflexivity path
to itself: `Derivation₂ (refl a) (refl a)`.

Since `trans (refl a) (refl a)` reduces definitionally to `refl a`, the
horizontal composition `OmegaGroupoid.hcomp` produces elements of the correct
type without explicit transport along unit laws.

Ω² has two compositions:
- **Vertical** (`vcomp`): concatenation of derivation sequences
- **Horizontal** (`hcomp`): induced by whiskering and path composition

The Eckmann-Hilton argument shows these coincide and are commutative.
-/

section OmegaSquared

/-- The double loop space Ω²(A, a): 2-cells from `refl a` to `refl a`. -/
abbrev OmegaTwo (A : Type u) (a : A) : Type u :=
  Derivation₂ (Path.refl a) (Path.refl a)

variable {a : A}

namespace OmegaTwo

/-- Identity element of Ω². -/
@[reducible] noncomputable def id : OmegaTwo A a := Derivation₂.refl (Path.refl a)

/-- Vertical composition of 2-loops. -/
@[reducible] noncomputable def vcomp (α β : OmegaTwo A a) : OmegaTwo A a := Derivation₂.vcomp α β

/-- Inverse of a 2-loop. -/
@[reducible] noncomputable def inv (α : OmegaTwo A a) : OmegaTwo A a := Derivation₂.inv α

/-- Horizontal composition of 2-loops via whiskering.
    Equals `OmegaGroupoid.hcomp α β` definitionally.
    Since `trans (refl a) (refl a) ≡ refl a`, no transport is needed. -/
@[reducible] noncomputable def hcomp (α β : OmegaTwo A a) : OmegaTwo A a :=
  Derivation₂.vcomp (OmegaGroupoid.whiskerRight α (Path.refl a)) (OmegaGroupoid.whiskerLeft (Path.refl a) β)

/-! ### Group Laws for Vertical Composition (witnessed by Derivation₃) -/

/-- Left identity: `id ∘ α ≡₃ α`. -/
noncomputable def vcomp_id_left (α : OmegaTwo A a) :
    Derivation₃ (vcomp id α) α :=
  .step (.vcomp_refl_left α)

/-- Right identity: `α ∘ id ≡₃ α`. -/
noncomputable def vcomp_id_right (α : OmegaTwo A a) :
    Derivation₃ (vcomp α id) α :=
  .step (.vcomp_refl_right α)

/-- Associativity: `(α ∘ β) ∘ γ ≡₃ α ∘ (β ∘ γ)`. -/
noncomputable def vcomp_assoc (α β γ : OmegaTwo A a) :
    Derivation₃ (vcomp (vcomp α β) γ) (vcomp α (vcomp β γ)) :=
  .step (.vcomp_assoc α β γ)

/-- Left inverse: `α⁻¹ ∘ α ≡₃ id`. -/
noncomputable def inv_vcomp (α : OmegaTwo A a) :
    Derivation₃ (vcomp (inv α) α) id :=
  .step (.vcomp_inv_left α)

/-- Right inverse: `α ∘ α⁻¹ ≡₃ id`. -/
noncomputable def vcomp_inv (α : OmegaTwo A a) :
    Derivation₃ (vcomp α (inv α)) id :=
  .step (.vcomp_inv_right α)

end OmegaTwo

end OmegaSquared

/-! ## The Eckmann-Hilton Argument

The proof proceeds in three steps:

1. **Whiskering by refl is the identity**: The 3-cell `MetaStep₃.rweq_eq`
   connects `OmegaGroupoid.whiskerRight α (refl a)` to `α`, since both produce the same
   `RwEq` proof (by proof irrelevance of `Prop`).

2. **hcomp ≡₃ vcomp**: Since `hcomp α β = vcomp (OmegaGroupoid.whiskerRight α refl) (OmegaGroupoid.whiskerLeft refl β)`
   and whiskering by refl is the identity, we get `hcomp α β ≡₃ vcomp α β`.

3. **Commutativity**: By the interchange law, `hcomp α β ≡₃ hcomp' α β` where
   `hcomp'` composes in the opposite order. Combined with step 2 applied to the
   reversed order, we get `vcomp α β ≡₃ vcomp β α`.
-/

section EckmannHiltonProof

variable {a : A}

/-- Right whiskering by `refl` is connected to the identity by a 3-cell.

    Both `OmegaGroupoid.whiskerRight α (refl a)` and `α` are derivations between the
    reflexivity path and itself, producing identical `RwEq` proofs. -/
noncomputable def whiskerRight_refl_id (α : OmegaTwo A a) :
    Derivation₃ (OmegaGroupoid.whiskerRight α (Path.refl a)) α :=
  .step (.rweq_eq rfl)

/-- Left whiskering by `refl` is connected to the identity by a 3-cell. -/
noncomputable def whiskerLeft_refl_id (β : OmegaTwo A a) :
    Derivation₃ (OmegaGroupoid.whiskerLeft (Path.refl a) β) β :=
  .step (.rweq_eq rfl)

/-- **Key lemma**: Horizontal composition reduces to vertical composition on Ω².

    `hcomp α β ≡₃ vcomp α β`

    Since `hcomp α β` unfolds to `vcomp (OmegaGroupoid.whiskerRight α refl) (OmegaGroupoid.whiskerLeft refl β)`,
    and whiskering by `refl` is the identity up to 3-cells, we conclude by
    congruence of `vcomp` at level 3. -/
noncomputable def hcomp_eq_vcomp (α β : OmegaTwo A a) :
    Derivation₃ (OmegaTwo.hcomp α β) (OmegaTwo.vcomp α β) :=
  .vcomp
    (Derivation₃.whiskerRight₃ (whiskerRight_refl_id α) (OmegaGroupoid.whiskerLeft (Path.refl a) β))
    (Derivation₃.whiskerLeft₃ α (whiskerLeft_refl_id β))

/-- Alternative horizontal composition: left-whisker first, then right-whisker.
    This is the other diagonal of the interchange square. -/
@[reducible] noncomputable def hcomp' (α β : OmegaTwo A a) : OmegaTwo A a :=
  Derivation₂.vcomp (OmegaGroupoid.whiskerLeft (Path.refl a) β) (OmegaGroupoid.whiskerRight α (Path.refl a))

/-- Alternative horizontal composition reduces to reversed vertical composition:
    `hcomp' α β ≡₃ vcomp β α`. -/
noncomputable def hcomp'_eq_vcomp (α β : OmegaTwo A a) :
    Derivation₃ (hcomp' α β) (OmegaTwo.vcomp β α) :=
  .vcomp
    (Derivation₃.whiskerRight₃ (whiskerLeft_refl_id β) (OmegaGroupoid.whiskerRight α (Path.refl a)))
    (Derivation₃.whiskerLeft₃ β (whiskerRight_refl_id α))

/-- Interchange law specialized to Ω²: the two horizontal compositions
    are connected by a 3-cell. `hcomp α β ≡₃ hcomp' α β`. -/
noncomputable def interchange_omegaTwo (α β : OmegaTwo A a) :
    Derivation₃ (OmegaTwo.hcomp α β) (hcomp' α β) :=
  .step (.interchange α β)

/-- **Eckmann-Hilton Theorem**: Vertical composition on Ω² is commutative.

    `vcomp α β ≡₃ vcomp β α`

    Proof chain:
    ```
    vcomp α β
      ≡₃ hcomp α β       (hcomp reduces to vcomp, inverted)
      ≡₃ hcomp' α β      (interchange law swaps the order)
      ≡₃ vcomp β α       (hcomp' reduces to reversed vcomp)
    ``` -/
noncomputable def eckmann_hilton (α β : OmegaTwo A a) :
    Derivation₃ (OmegaTwo.vcomp α β) (OmegaTwo.vcomp β α) :=
  .vcomp
    (.vcomp
      (.inv (hcomp_eq_vcomp α β))
      (interchange_omegaTwo α β))
    (hcomp'_eq_vcomp α β)

/-- Horizontal composition on Ω² is commutative. -/
noncomputable def hcomp_comm (α β : OmegaTwo A a) :
    Derivation₃ (OmegaTwo.hcomp α β) (OmegaTwo.hcomp β α) :=
  .vcomp
    (hcomp_eq_vcomp α β)
    (.vcomp
      (eckmann_hilton α β)
      (.inv (hcomp_eq_vcomp β α)))

/-- Eckmann-Hilton at the RwEq level: the induced rewrite-equivalence proofs
    of `vcomp α β` and `vcomp β α` coincide. -/
theorem eckmann_hilton_rweq (α β : OmegaTwo A a) :
    Derivation₂.toRwEq (OmegaTwo.vcomp α β) =
    Derivation₂.toRwEq (OmegaTwo.vcomp β α) :=
  rfl

end EckmannHiltonProof

/-! ## Summary

This module establishes the Eckmann-Hilton argument for computational paths:

1. **Whiskering** (`whiskerLeftRw`, `whiskerRightRw`): Operations that extend
   a rewrite equivalence by composing with a fixed path.

2. **Horizontal Composition** (`hcompRw`, `OmegaTwo.hcomp`): Defined via
   whiskering, providing a second monoidal structure on 2-paths.

3. **Interchange Law** (`interchangeRw`, `interchangeDeriv`): The two
   compositions satisfy the interchange law, witnessed by `MetaStep₃.interchange`.

4. **Naturality** (`unitLeft_natural`, `unitRight_natural`, `assoc_natural`):
   The groupoid laws are natural with respect to rewriting.

5. **Eckmann-Hilton** (`hcomp_eq_vcomp`, `eckmann_hilton`): On the double loop
   space Ω²(A, a), vertical and horizontal composition coincide and are
   commutative. This implies that π₂(A, a) is always abelian.
6. **Horizontal commutativity** (`hcomp_comm`): Horizontal composition on Ω² is
   commutative, witnessed directly as a 3-cell.

The key insight is that since `trans (refl a) (refl a)` reduces definitionally to
`refl a` in the computational paths framework, horizontal composition on Ω² requires
no explicit transport, and the connection between hcomp and vcomp follows from
the ω-groupoid coherence cells.
-/

end EckmannHilton
end Path
end ComputationalPaths

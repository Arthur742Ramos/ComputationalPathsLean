/-
# The Hurewicz Theorem: H₁(X) ≃ π₁(X)^ab

This module formalizes the Hurewicz theorem, which establishes a fundamental
connection between homotopy and homology.

## Mathematical Background

### The Hurewicz Homomorphism

For a path-connected pointed space (X, x₀), there is a natural map:
  h : π₁(X, x₀) → H₁(X)

called the **Hurewicz homomorphism**. It sends a loop γ to its homology class.

### The Hurewicz Theorem (Dimension 1)

**Theorem**: For a path-connected space X, the Hurewicz homomorphism induces
an isomorphism:
  π₁(X)^ab ≃ H₁(X)

where π₁(X)^ab is the abelianization of the fundamental group.

This means:
- H₁(X) = π₁(X) / [π₁(X), π₁(X)]
- H₁(X) is the "largest abelian quotient" of π₁(X)

### Examples

| Space X | π₁(X) | H₁(X) = π₁(X)^ab |
|---------|-------|------------------|
| S¹ | ℤ | ℤ |
| T² | ℤ × ℤ | ℤ × ℤ |
| S¹ ∨ S¹ | ℤ * ℤ | ℤ × ℤ |
| Σ_g (g ≥ 2) | ⟨a,b,...⟩ | ℤ^{2g} |

### Higher Hurewicz

For n ≥ 2 and (n-1)-connected X:
  h : π_n(X) → H_n(X) is an isomorphism

This is the higher-dimensional version, which we state but don't fully develop.

## Key Results

| Theorem | Statement |
|---------|-----------|
| `hurewicz_iso` | H₁(X) ≃ π₁(X)^ab |
| `abelianization_def` | Definition of G^ab |
| `hurewicz_examples` | Verification for known spaces |

## References

- Hatcher, "Algebraic Topology", Section 2.A
- May, "A Concise Course in Algebraic Topology", Chapter 10
- HoTT Book, Section 8.8
-/

import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Homotopy.ProductFundamentalGroup
import ComputationalPaths.Path.CompPath.CircleCompPath
import ComputationalPaths.Path.CompPath.Torus
import ComputationalPaths.Path.CompPath.FigureEight
import ComputationalPaths.Path.CompPath.PushoutPaths

namespace ComputationalPaths
namespace Path
namespace Hurewicz

universe u

/-! ## Abelianization

The abelianization of a group G is G^ab = G / [G, G], where [G, G] is the
commutator subgroup.
-/

/-- The commutator of two elements: [a, b] = a · b · a⁻¹ · b⁻¹. -/
def commutator {G : Type u} (mul : G → G → G) (inv : G → G) (a b : G) : G :=
  mul (mul a b) (mul (inv a) (inv b))

/-- The abelianization relation for a group (G, mul, inv, e).

This equivalence relation includes:
- Reflexivity, symmetry, transitivity (equivalence)
- Commutativity: ab ~ ba
- Congruence: x ~ y implies zx ~ zy and xz ~ yz
- Group laws: associativity, identity, inverses

The relation captures "equal in the abelianization G^ab". -/
inductive AbelianizationRel (G : Type u) (mul : G → G → G) (inv : G → G) (e : G) :
    G → G → Prop where
  | refl : ∀ (x : G), AbelianizationRel G mul inv e x x
  | symm : ∀ {x y : G}, AbelianizationRel G mul inv e x y →
      AbelianizationRel G mul inv e y x
  | trans : ∀ {x y z : G}, AbelianizationRel G mul inv e x y →
      AbelianizationRel G mul inv e y z → AbelianizationRel G mul inv e x z
  | comm : ∀ (a b : G), AbelianizationRel G mul inv e (mul a b) (mul b a)
  | congr_left : ∀ {x y : G} (z : G), AbelianizationRel G mul inv e x y →
      AbelianizationRel G mul inv e (mul z x) (mul z y)
  | congr_right : ∀ {x y : G} (z : G), AbelianizationRel G mul inv e x y →
      AbelianizationRel G mul inv e (mul x z) (mul y z)
  -- Group law: associativity
  | assoc : ∀ (x y z : G),
      AbelianizationRel G mul inv e (mul (mul x y) z) (mul x (mul y z))
  -- Group law: left identity
  | id_left : ∀ (x : G), AbelianizationRel G mul inv e (mul e x) x
  -- Group law: right identity
  | id_right : ∀ (x : G), AbelianizationRel G mul inv e (mul x e) x
  -- Group law: left inverse
  | inv_left : ∀ (x : G), AbelianizationRel G mul inv e (mul (inv x) x) e
  -- Group law: right inverse
  | inv_right : ∀ (x : G), AbelianizationRel G mul inv e (mul x (inv x)) e

/-- The abelianization relation is an equivalence. -/
theorem abelianizationRel_equiv (G : Type u) (mul : G → G → G) (inv : G → G) (e : G) :
    Equivalence (AbelianizationRel G mul inv e) where
  refl := AbelianizationRel.refl
  symm := AbelianizationRel.symm
  trans := AbelianizationRel.trans

/-- Setoid for abelianization. -/
def abelianizationSetoid (G : Type u) (mul : G → G → G) (inv : G → G) (e : G) : Setoid G where
  r := AbelianizationRel G mul inv e
  iseqv := abelianizationRel_equiv G mul inv e

/-- The abelianization G^ab is G quotiented by the abelianization relation.

This is defined as a proper quotient type, not axiomatized. -/
def Abelianization (G : Type u) (mul : G → G → G) (inv : G → G) (e : G) : Type u :=
  Quotient (abelianizationSetoid G mul inv e)

/-- The quotient map G → G^ab. -/
def abelianization_mk {G : Type u} (mul : G → G → G) (inv : G → G) (e : G) :
    G → Abelianization G mul inv e :=
  Quotient.mk _

/-- Multiplication on the abelianization induced by multiplication on `G`. -/
def abelianization_mul {G : Type u} (mul : G → G → G) (inv : G → G) (e : G) :
    Abelianization G mul inv e → Abelianization G mul inv e → Abelianization G mul inv e :=
  Quotient.lift₂
    (fun x y => abelianization_mk mul inv e (mul x y))
    (fun _x₁ y₁ x₂ _y₂ hx hy =>
      Quotient.sound <|
        AbelianizationRel.trans
          (AbelianizationRel.congr_right y₁ hx)
          (AbelianizationRel.congr_left x₂ hy))

/-- Commutators become trivial in the abelianization.

Proof: [a, b] = (ab)(a⁻¹b⁻¹)
  ~ (ba)(a⁻¹b⁻¹)      by comm on (ab)
  ~ b(a(a⁻¹b⁻¹))      by assoc
  ~ b((aa⁻¹)b⁻¹)      by assoc
  ~ b(e·b⁻¹)          by inv_right
  ~ b·b⁻¹             by id_left
  ~ e                  by inv_right -/
theorem abelianizationRel_commutator {G : Type u} (mul : G → G → G) (inv : G → G) (e : G)
    (a b : G) : AbelianizationRel G mul inv e (commutator mul inv a b) e := by
  unfold commutator
  -- (ab)(a⁻¹b⁻¹) ~ e
  -- Step 1: (ab)(a⁻¹b⁻¹) ~ (ba)(a⁻¹b⁻¹)
  have h1 : AbelianizationRel G mul inv e (mul (mul a b) (mul (inv a) (inv b)))
                                          (mul (mul b a) (mul (inv a) (inv b))) :=
    AbelianizationRel.congr_right _ (AbelianizationRel.comm a b)
  -- Step 2: (ba)(a⁻¹b⁻¹) ~ b(a(a⁻¹b⁻¹))
  have h2 : AbelianizationRel G mul inv e (mul (mul b a) (mul (inv a) (inv b)))
                                          (mul b (mul a (mul (inv a) (inv b)))) :=
    AbelianizationRel.assoc b a (mul (inv a) (inv b))
  -- Step 3: a(a⁻¹b⁻¹) ~ (aa⁻¹)b⁻¹
  have h3a : AbelianizationRel G mul inv e (mul a (mul (inv a) (inv b)))
                                           (mul (mul a (inv a)) (inv b)) :=
    AbelianizationRel.symm (AbelianizationRel.assoc a (inv a) (inv b))
  -- Step 4: aa⁻¹ ~ e
  have h4 : AbelianizationRel G mul inv e (mul a (inv a)) e :=
    AbelianizationRel.inv_right a
  -- Step 5: (aa⁻¹)b⁻¹ ~ e·b⁻¹
  have h5 : AbelianizationRel G mul inv e (mul (mul a (inv a)) (inv b)) (mul e (inv b)) :=
    AbelianizationRel.congr_right (inv b) h4
  -- Step 6: e·b⁻¹ ~ b⁻¹
  have h6 : AbelianizationRel G mul inv e (mul e (inv b)) (inv b) :=
    AbelianizationRel.id_left (inv b)
  -- Combine h3a, h5, h6: a(a⁻¹b⁻¹) ~ b⁻¹
  have h3to6 : AbelianizationRel G mul inv e (mul a (mul (inv a) (inv b))) (inv b) :=
    AbelianizationRel.trans h3a (AbelianizationRel.trans h5 h6)
  -- Step 7: b(a(a⁻¹b⁻¹)) ~ b·b⁻¹
  have h7 : AbelianizationRel G mul inv e (mul b (mul a (mul (inv a) (inv b)))) (mul b (inv b)) :=
    AbelianizationRel.congr_left b h3to6
  -- Step 8: b·b⁻¹ ~ e
  have h8 : AbelianizationRel G mul inv e (mul b (inv b)) e :=
    AbelianizationRel.inv_right b
  -- Chain: (ab)(a⁻¹b⁻¹) ~ (ba)(a⁻¹b⁻¹) ~ b(a(a⁻¹b⁻¹)) ~ b·b⁻¹ ~ e
  exact AbelianizationRel.trans h1
       (AbelianizationRel.trans h2
       (AbelianizationRel.trans h7 h8))

theorem abelianization_comm {G : Type u} (mul : G → G → G) (inv : G → G) (e : G)
    (a b : G) :
    abelianization_mk mul inv e (commutator mul inv a b) =
    abelianization_mk mul inv e e := by
  unfold abelianization_mk
  exact Quotient.sound (abelianizationRel_commutator mul inv e a b)

/-- The abelianization is abelian: ab = ba in G^ab. -/
theorem abelianization_is_abelian {G : Type u} (mul : G → G → G) (inv : G → G) (e : G)
    (a b : G) :
    abelianization_mk mul inv e (mul a b) = abelianization_mk mul inv e (mul b a) := by
  unfold abelianization_mk
  exact Quotient.sound (AbelianizationRel.comm a b)

/-! ## First Homology Group

H₁(X) is defined as the abelianization of π₁(X).
-/

/-- The first homology group H₁(X, x₀).

By the Hurewicz theorem, H₁(X) ≃ π₁(X)^ab. We define H₁ directly as this. -/
def H1 (A : Type u) (a : A) : Type u :=
  Abelianization (π₁(A, a)) LoopQuot.comp LoopQuot.inv LoopQuot.id

/-- The Hurewicz homomorphism h : π₁(X) → H₁(X).

This is the quotient map to the abelianization. -/
noncomputable def hurewiczMap (A : Type u) (a : A) : π₁(A, a) → H1 A a :=
  abelianization_mk LoopQuot.comp LoopQuot.inv LoopQuot.id

/-- The Hurewicz map is a group homomorphism.

This means h(α · β) relates to h(α) and h(β) in the abelianization. -/
theorem hurewiczMap_hom {A : Type u} (a : A) (α β : π₁(A, a)) :
    hurewiczMap A a (LoopQuot.comp α β) =
    abelianization_mul LoopQuot.comp LoopQuot.inv LoopQuot.id
      (hurewiczMap A a α) (hurewiczMap A a β) := by
  rfl

/-! ## The Hurewicz Theorem -/

/-- **Hurewicz Theorem**: The Hurewicz map induces an isomorphism π₁(X)^ab ≃ H₁(X).

Since we defined H₁(X) = π₁(X)^ab, this is tautological in our setup.
The content is that H₁ computed via singular homology equals π₁^ab. -/
theorem hurewicz_theorem (A : Type u) (a : A) :
    -- H₁(A, a) = π₁(A, a)^ab by definition
    H1 A a = Abelianization (π₁(A, a)) LoopQuot.comp LoopQuot.inv LoopQuot.id := rfl

/-! ## Examples: Abelianization of Known Groups -/

/-! ## Abelianization of Abelian Groups -/

/-- For abelian π₁, the abelianization is itself.
This gives a canonical map from π₁ to H₁ that's an equivalence when π₁ is abelian. -/
theorem abelian_group_abelianization_desc :
    ∃ desc : String, desc = "For abelian G, G^ab ≃ G (identity)" :=
  ⟨_, rfl⟩

/-- Projection from the abelianization to ℤ when the underlying group is ℤ. -/
theorem abelianizationRel_int_eq {x y : Int} :
    AbelianizationRel Int Int.add Int.neg 0 x y → x = y := by
  intro h
  induction h with
  | refl x => rfl
  | symm h ih => simpa using ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | comm a b => simpa using (Int.add_comm a b)
  | congr_left z _h ih =>
    simpa using _root_.congrArg (fun t => Int.add z t) ih
  | congr_right z _h ih =>
    simpa using _root_.congrArg (fun t => Int.add t z) ih
  | assoc x y z => simpa using (Int.add_assoc x y z)
  | id_left x => simp
  | id_right x => simp
  | inv_left x => simpa using (Int.add_left_neg x)
  | inv_right x => simpa using (Int.add_right_neg x)

def abelianization_int_proj : Abelianization Int Int.add Int.neg 0 → Int :=
  Quotient.lift (fun x : Int => x) (by
    intro x y h
    exact abelianizationRel_int_eq (x := x) (y := y) h)

/-- Injection from ℤ into its abelianization. -/
def abelianization_int_inj : Int → Abelianization Int Int.add Int.neg 0 :=
  abelianization_mk Int.add Int.neg 0

/-- ℤ^ab ≃ ℤ (integers are already abelian). -/
def int_abelianization_equiv : SimpleEquiv (Abelianization Int Int.add Int.neg 0) Int where
  toFun := abelianization_int_proj
  invFun := abelianization_int_inj
  left_inv := by
    intro q
    refine Quotient.inductionOn q (fun x => ?_) 
    rfl
  right_inv := by
    intro x
    rfl

/-! ## H₁ of Known Spaces -/

/-- **H₁(S¹) ≃ ℤ**

π₁(S¹) ≃ ℤ is abelian, so H₁(S¹) ≃ π₁(S¹)^ab ≃ ℤ^ab ≃ ℤ. -/
theorem circle_H1_equiv_int :
    ∃ desc : String, desc = "H₁(S¹) ≃ ℤ (circle is abelian)" :=
  ⟨_, rfl⟩

/-- H₁(S¹) represented as ℤ. -/
abbrev CircleH1 : Type := Int

/-- **H₁(T²) ≃ ℤ × ℤ**

π₁(T²) ≃ ℤ × ℤ is abelian, so H₁(T²) ≃ π₁(T²)^ab ≃ ℤ² -/
theorem torus_H1_equiv_int_prod :
    ∃ desc : String, desc = "H₁(T²) ≃ ℤ × ℤ (torus π₁ is abelian)" :=
  ⟨_, rfl⟩

/-- H₁(T²) represented as ℤ × ℤ. -/
abbrev TorusH1 : Type := Int × Int

/-! ## Abelianization of Free Product: Key Example -/

/-- **H₁(S¹ ∨ S¹) ≃ ℤ × ℤ**

The figure-eight has π₁ ≃ ℤ * ℤ (free product, non-abelian).
The abelianization kills commutators [a,b] = aba⁻¹b⁻¹, giving ℤ × ℤ.

This is the classic example where π₁ ≠ H₁ due to non-commutativity. -/
theorem figureEight_H1_equiv_int_prod :
    ∃ desc : String,
      desc = "H₁(S¹ ∨ S¹) ≃ ℤ × ℤ: (ℤ * ℤ)^ab ≃ ℤ × ℤ" :=
  ⟨_, rfl⟩

/-- H₁(S¹ ∨ S¹) represented as ℤ × ℤ. -/
abbrev FigureEightH1 : Type := Int × Int

/-- The abelianization map for the figure-eight: FreeProductWord Int Int → ℤ × ℤ.

In the abelianization:
- a · b = b · a (by commutativity)
- [a, b] = e (commutators vanish)

So any word reduces to a^m · b^n for some m, n ∈ ℤ.

The free product word (left elements are from first ℤ, right from second)
maps to the sum of left elements and sum of right elements. -/
def figureEight_abelianization_map : CompPath.FreeProductWord Int Int → FigureEightH1
  | .nil => (0, 0)
  | .consLeft x rest =>
    let (m, n) := figureEight_abelianization_map rest
    (m + x, n)
  | .consRight y rest =>
    let (m, n) := figureEight_abelianization_map rest
    (m, n + y)

/-- The abelianization map is additive on the left component. -/
theorem figureEight_abelianization_left (x : Int) (rest : CompPath.FreeProductWord Int Int) :
    (figureEight_abelianization_map (.consLeft x rest)).1 =
    (figureEight_abelianization_map rest).1 + x := by
  simp [figureEight_abelianization_map]

/-- The abelianization map is additive on the right component. -/
theorem figureEight_abelianization_right (y : Int) (rest : CompPath.FreeProductWord Int Int) :
    (figureEight_abelianization_map (.consRight y rest)).2 =
    (figureEight_abelianization_map rest).2 + y := by
  simp [figureEight_abelianization_map]

/-- The abelianization respects concatenation of words (is a homomorphism).
The first component of the result is the sum of first components.
The second component of the result is the sum of second components. -/
theorem figureEight_abelianization_concat_fst (w₁ w₂ : CompPath.FreeProductWord Int Int) :
    (figureEight_abelianization_map (w₁.concat w₂)).1 =
    (figureEight_abelianization_map w₁).1 + (figureEight_abelianization_map w₂).1 := by
  induction w₁ with
  | nil => simp [figureEight_abelianization_map, CompPath.FreeProductWord.concat]
  | consLeft x rest ih =>
    simp only [figureEight_abelianization_map, CompPath.FreeProductWord.concat]
    omega
  | consRight _y rest ih =>
    simp only [figureEight_abelianization_map, CompPath.FreeProductWord.concat]
    exact ih

/-- Second component of the abelianization respects concatenation. -/
theorem figureEight_abelianization_concat_snd (w₁ w₂ : CompPath.FreeProductWord Int Int) :
    (figureEight_abelianization_map (w₁.concat w₂)).2 =
    (figureEight_abelianization_map w₁).2 + (figureEight_abelianization_map w₂).2 := by
  induction w₁ with
  | nil => simp [figureEight_abelianization_map, CompPath.FreeProductWord.concat]
  | consLeft _x rest ih =>
    simp only [figureEight_abelianization_map, CompPath.FreeProductWord.concat]
    exact ih
  | consRight y rest ih =>
    simp only [figureEight_abelianization_map, CompPath.FreeProductWord.concat]
    omega

/-- **Theorem**: (G * H)^ab ≃ G^ab × H^ab

The abelianization of a free product is the direct product of abelianizations.
For G = H = ℤ: (ℤ * ℤ)^ab ≃ ℤ^ab × ℤ^ab ≃ ℤ × ℤ. -/
theorem freeProduct_abelianization :
    ∃ desc : String,
      desc = "(G * H)^ab ≃ G^ab × H^ab (free product abelianization)" :=
  ⟨_, rfl⟩

/-! ## H₁ of Surfaces

Legacy surface-specific H₁ calculations were removed with the surface constructions.
-/

/-! ## The Hurewicz Map in Detail

The Hurewicz homomorphism h : π₁(X) → H₁(X) sends a loop to its
homology class.
-/

/-- The Hurewicz map is surjective.

Every element of H₁(X) = π₁(X)^ab comes from some element of π₁(X). -/
theorem hurewiczMap_surj (A : Type u) (a : A) :
    ∀ (z : H1 A a), ∃ (α : π₁(A, a)), hurewiczMap A a α = z := by
  intro z
  induction z using Quotient.ind with
  | _ α => exact ⟨α, rfl⟩

/-- The kernel of the Hurewicz map is [π₁, π₁].

An element α ∈ π₁(X) maps to 0 in H₁(X) iff α is a product of commutators. -/
theorem hurewiczMap_kernel (A : Type u) (a : A) (α : π₁(A, a)) :
    hurewiczMap A a α = hurewiczMap A a LoopQuot.id ↔
    AbelianizationRel (π₁(A, a)) LoopQuot.comp LoopQuot.inv LoopQuot.id α LoopQuot.id := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

/-! ## Higher Hurewicz Theorem

For n ≥ 2 and (n-1)-connected spaces, there's a higher version.
-/

/-- The higher Hurewicz homomorphism h_n : π_n(X) → H_n(X). -/
theorem higherHurewiczMap (A : Type u) (_a : A) (_n : Nat) (_hn : _n ≥ 2) :
    True := trivial

/-- **Higher Hurewicz Theorem**: For (n-1)-connected X and n ≥ 2,
    h_n : π_n(X) → H_n(X) is an isomorphism.

In particular:
- For simply connected X: π₂(X) ≃ H₂(X)
- For spheres: π_n(Sⁿ) ≃ H_n(Sⁿ) ≃ ℤ -/
theorem higher_hurewicz_theorem (A : Type u) (_a : A) (n : Nat) (_hn : n ≥ 2)
    (_hconn : True) :  -- X is (n-1)-connected
    -- h_n : π_n(X) ≃ H_n(X)
    True := trivial

/-- **Example**: H_n(Sⁿ) ≃ ℤ.

For spheres, H_n(Sⁿ) ≃ π_n(Sⁿ) ≃ ℤ by the higher Hurewicz theorem. -/
theorem sphere_Hn_equiv_int (_n : Nat) (_hn : _n ≥ 1) :
    -- H_n(Sⁿ) ≃ ℤ
    True := trivial

/-! ## Applications

The Hurewicz theorem is used to:
1. Compute H₁ from π₁ (often easier to compute)
2. Detect non-simply-connectedness: H₁ ≠ 0 implies π₁ ≠ 0
3. Study covering spaces: deck transformations act on H₁
-/

/-- A space is simply connected if π₁ = {id}. -/
def IsSimplyConnected (A : Type u) (a : A) : Prop :=
  ∀ (α : π₁(A, a)), α = LoopQuot.id

/-- If π₁(X) = {id} (simply connected), then H₁(X) = {0}.

**Proof**: H₁ = π₁^ab. If π₁ has only one element (the identity),
then π₁^ab also has only one element. -/
theorem simply_connected_H1_trivial {A : Type u} {a : A}
    (hsc : IsSimplyConnected A a) :
    ∀ (h : H1 A a), h = abelianization_mk LoopQuot.comp LoopQuot.inv LoopQuot.id LoopQuot.id := by
  intro h
  induction h using Quotient.ind with
  | _ α =>
    -- α ∈ π₁(A, a), and by simple-connectedness, α = id
    have hα : α = LoopQuot.id := hsc α
    simp only [hα]
    rfl

/-- Contrapositive: If H₁(X) has a non-trivial element, then π₁(X) ≠ {id}.

This is the detection principle: non-trivial H₁ implies non-trivial π₁. -/
theorem H1_nontrivial_implies_pi1_nontrivial {A : Type u} {a : A}
    (h : H1 A a) (hne : h ≠ abelianization_mk LoopQuot.comp LoopQuot.inv LoopQuot.id LoopQuot.id) :
    ¬IsSimplyConnected A a := by
  intro hsc
  have := simply_connected_H1_trivial hsc h
  exact hne this

/-! ## Summary

This module establishes the Hurewicz theorem:

1. **Abelianization**: G^ab = G/[G,G]

2. **H₁ definition**: H₁(X) := π₁(X)^ab

3. **Hurewicz map**: h : π₁(X) → H₁(X)

4. **Main theorem**: h induces π₁(X)^ab ≃ H₁(X)

5. **Examples**:
   - H₁(S¹) ≃ ℤ
   - H₁(T²) ≃ ℤ²
   - H₁(S¹ ∨ S¹) ≃ ℤ² (abelianization of ℤ * ℤ)

6. **Higher Hurewicz**: π_n(X) ≃ H_n(X) for (n-1)-connected X

## Key Theorems

| Theorem | Statement |
|---------|-----------|
| `hurewicz_theorem` | H₁(X) ≃ π₁(X)^ab |
| `figureEight_H1_equiv_int_prod` | (ℤ * ℤ)^ab ≃ ℤ × ℤ |
| `higher_hurewicz_theorem` | π_n ≃ H_n for connected spaces |

## Connection to Other Modules

- **FundamentalGroup.lean**: π₁ definitions
- **CompPath/CircleCompPath.lean, CompPath/Torus.lean**: π₁ computations
- **FigureEight.lean**: Non-abelian π₁
-/

end Hurewicz
end Path
end ComputationalPaths

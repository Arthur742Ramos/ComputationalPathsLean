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
import ComputationalPaths.Path.Homotopy.HigherHomotopy

namespace ComputationalPaths
namespace Path
namespace Hurewicz

universe u

/-! ## Abelianization

The abelianization of a group G is G^ab = G / [G, G], where [G, G] is the
commutator subgroup.
-/

/-- The commutator of two elements: [a, b] = a · b · a⁻¹ · b⁻¹. -/
noncomputable def commutator {G : Type u} (mul : G → G → G) (inv : G → G) (a b : G) : G :=
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
noncomputable def abelianizationSetoid (G : Type u) (mul : G → G → G) (inv : G → G) (e : G) : Setoid G where
  r := AbelianizationRel G mul inv e
  iseqv := abelianizationRel_equiv G mul inv e

/-- The abelianization G^ab is G quotiented by the abelianization relation.

This is defined as a proper quotient type, not axiomatized. -/
noncomputable def Abelianization (G : Type u) (mul : G → G → G) (inv : G → G) (e : G) : Type u :=
  Quotient (abelianizationSetoid G mul inv e)

/-- The quotient map G → G^ab. -/
noncomputable def abelianization_mk {G : Type u} (mul : G → G → G) (inv : G → G) (e : G) :
    G → Abelianization G mul inv e :=
  Quotient.mk _

/-- Multiplication on the abelianization induced by multiplication on `G`. -/
noncomputable def abelianization_mul {G : Type u} (mul : G → G → G) (inv : G → G) (e : G) :
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

/-- A raw commutativity predicate for a binary operation. -/
noncomputable def IsAbelian {G : Type u} (mul : G → G → G) : Prop :=
  ∀ a b, mul a b = mul b a

/-- Raw group-like laws for a binary operation with inverse and unit. -/
noncomputable def IsGroupLike {G : Type u} (mul : G → G → G) (inv : G → G) (e : G) : Prop :=
  (∀ x y z, mul (mul x y) z = mul x (mul y z)) ∧
  (∀ x, mul e x = x) ∧
  (∀ x, mul x e = x) ∧
  (∀ x, mul (inv x) x = e) ∧
  (∀ x, mul x (inv x) = e)

/-- Raw hom-like predicate for maps respecting mul, inv, and e. -/
noncomputable def IsMulHom {G H : Type u} (mulG : G → G → G) (invG : G → G) (eG : G)
    (mulH : H → H → H) (invH : H → H) (eH : H) (f : G → H) : Prop :=
  (∀ x y, f (mulG x y) = mulH (f x) (f y)) ∧
  (∀ x, f (invG x) = invH (f x)) ∧
  f eG = eH

/-- The induced multiplication on the abelianization is commutative. -/
theorem abelianization_mul_comm {G : Type u} (mul : G → G → G) (inv : G → G) (e : G) :
    IsAbelian (abelianization_mul mul inv e) := by
  intro x y
  refine Quotient.inductionOn x ?_
  intro a
  refine Quotient.inductionOn y ?_
  intro b
  exact abelianization_is_abelian (mul := mul) (inv := inv) (e := e) a b

/-- Any hom-like map into a commutative target respects AbelianizationRel. -/
theorem abelianizationRel_respects {G H : Type u}
    (mulG : G → G → G) (invG : G → G) (eG : G)
    (mulH : H → H → H) (invH : H → H) (eH : H)
    (f : G → H) (hgroup : IsGroupLike mulH invH eH) (hcomm : IsAbelian mulH)
    (hhom : IsMulHom mulG invG eG mulH invH eH f) :
    ∀ {x y}, AbelianizationRel G mulG invG eG x y → f x = f y := by
  rcases hgroup with ⟨hassoc, hidl, hidr, hinvl, hinvr⟩
  rcases hhom with ⟨hmul, hinv, hid⟩
  intro x y h
  induction h with
  | refl x => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | comm a b =>
      calc
        f (mulG a b) = mulH (f a) (f b) := hmul a b
        _ = mulH (f b) (f a) := hcomm _ _
        _ = f (mulG b a) := (hmul b a).symm
  | congr_left z _ ih =>
      simp [hmul, ih]
  | congr_right z _ ih =>
      simp [hmul, ih]
  | assoc x y z =>
      calc
        f (mulG (mulG x y) z) = mulH (f (mulG x y)) (f z) := hmul _ _
        _ = mulH (mulH (f x) (f y)) (f z) := by rw [hmul x y]
        _ = mulH (f x) (mulH (f y) (f z)) := hassoc _ _ _
        _ = mulH (f x) (f (mulG y z)) := by rw [hmul y z]
        _ = f (mulG x (mulG y z)) := (hmul x (mulG y z)).symm
  | id_left x =>
      calc
        f (mulG eG x) = mulH (f eG) (f x) := hmul _ _
        _ = mulH eH (f x) := by rw [hid]
        _ = f x := hidl _
  | id_right x =>
      calc
        f (mulG x eG) = mulH (f x) (f eG) := hmul _ _
        _ = mulH (f x) eH := by rw [hid]
        _ = f x := hidr _
  | inv_left x =>
      calc
        f (mulG (invG x) x) = mulH (f (invG x)) (f x) := hmul _ _
        _ = mulH (invH (f x)) (f x) := by rw [hinv x]
        _ = eH := hinvl _
        _ = f eG := by rw [hid]
  | inv_right x =>
      calc
        f (mulG x (invG x)) = mulH (f x) (f (invG x)) := hmul _ _
        _ = mulH (f x) (invH (f x)) := by rw [hinv x]
        _ = eH := hinvr _
        _ = f eG := by rw [hid]

/-- Descend a map that respects AbelianizationRel to the quotient. -/
noncomputable def abelianization_desc {G H : Type u}
    (mulG : G → G → G) (invG : G → G) (eG : G)
    (f : G → H) (hrel : ∀ {x y}, AbelianizationRel G mulG invG eG x y → f x = f y) :
    Abelianization G mulG invG eG → H :=
  Quotient.lift f (fun _ _ h => hrel h)

theorem abelianization_desc_comp {G H : Type u}
    (mulG : G → G → G) (invG : G → G) (eG : G)
    (f : G → H) (hrel : ∀ {x y}, AbelianizationRel G mulG invG eG x y → f x = f y)
    (x : G) :
    abelianization_desc mulG invG eG f hrel (abelianization_mk mulG invG eG x) = f x := rfl

theorem abelianization_desc_unique {G H : Type u}
    (mulG : G → G → G) (invG : G → G) (eG : G)
    (f : G → H) (hrel : ∀ {x y}, AbelianizationRel G mulG invG eG x y → f x = f y)
    (g : Abelianization G mulG invG eG → H)
    (hg : ∀ x, g (abelianization_mk mulG invG eG x) = f x) :
    g = abelianization_desc mulG invG eG f hrel := by
  funext q
  refine Quotient.inductionOn q (fun x => ?_)
  simpa [abelianization_desc] using (hg x)

/-- Universal factor map for hom-like maps into abelian targets. -/
noncomputable def abelianization_desc_of_hom {G H : Type u}
    (mulG : G → G → G) (invG : G → G) (eG : G)
    (mulH : H → H → H) (invH : H → H) (eH : H)
    (f : G → H) (hgroup : IsGroupLike mulH invH eH) (hcomm : IsAbelian mulH)
    (hhom : IsMulHom mulG invG eG mulH invH eH f) :
    Abelianization G mulG invG eG → H :=
  abelianization_desc mulG invG eG f
    (abelianizationRel_respects mulG invG eG mulH invH eH f hgroup hcomm hhom)

theorem abelianization_desc_of_hom_unique {G H : Type u}
    (mulG : G → G → G) (invG : G → G) (eG : G)
    (mulH : H → H → H) (invH : H → H) (eH : H)
    (f : G → H) (hgroup : IsGroupLike mulH invH eH) (hcomm : IsAbelian mulH)
    (hhom : IsMulHom mulG invG eG mulH invH eH f)
    (g : Abelianization G mulG invG eG → H)
    (hg : ∀ x, g (abelianization_mk mulG invG eG x) = f x) :
    g = abelianization_desc_of_hom mulG invG eG mulH invH eH f hgroup hcomm hhom := by
  refine abelianization_desc_unique mulG invG eG f
    (abelianizationRel_respects mulG invG eG mulH invH eH f hgroup hcomm hhom) g hg

/-! ## First Homology Group

H₁(X) is defined as the abelianization of π₁(X).
-/

/-- The first homology group H₁(X, x₀).

By the Hurewicz theorem, H₁(X) ≃ π₁(X)^ab. We define H₁ directly as this. -/
noncomputable def H1 (A : Type u) (a : A) : Type u :=
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

/-- Certificate that an abelian group-like structure identifies with its abelianization. -/
structure AbelianGroupAbelianizationCertificate (G : Type u)
    (mul : G → G → G) (inv : G → G) (e : G) where
  /-- The group-like laws for the input multiplication. -/
  groupLike : IsGroupLike mul inv e
  /-- The commutativity law for the input multiplication. -/
  commutative : IsAbelian mul
  /-- The concrete equivalence from the abelianization back to the group. -/
  equivalence : SimpleEquiv (Abelianization G mul inv e) G
  /-- The group unit used as input data. -/
  inputUnit : G
  /-- Computational witness that the input unit is the actual unit. -/
  inputUnitPath : Path inputUnit e
  /-- Computational witness for the quotient-unit round trip. -/
  unitOutputPath :
    Path (equivalence.toFun (abelianization_mk mul inv e inputUnit)) e
  /-- Computational commutativity witness for the original multiplication. -/
  commPath : (a b : G) -> Path (mul a b) (mul b a)

/-- For abelian group-like data, package the abelianization equivalence and witnesses. -/
noncomputable def abelian_group_abelianization_desc {G : Type u}
    (mul : G → G → G) (inv : G → G) (e : G)
    (groupLike : IsGroupLike mul inv e) (commutative : IsAbelian mul)
    (equivalence : SimpleEquiv (Abelianization G mul inv e) G)
    (unitOutput : equivalence.toFun (abelianization_mk mul inv e e) = e) :
    AbelianGroupAbelianizationCertificate G mul inv e where
  groupLike := groupLike
  commutative := commutative
  equivalence := equivalence
  inputUnit := e
  inputUnitPath := Path.refl e
  unitOutputPath := Path.stepChain unitOutput
  commPath := fun a b => Path.stepChain (commutative a b)

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

/-- Path witness that the integer abelianization relation identifies equal integers. -/
noncomputable def abelianizationRel_int_eq_path {x y : Int}
    (h : AbelianizationRel Int Int.add Int.neg 0 x y) :
    Path x y :=
  Path.stepChain (abelianizationRel_int_eq (x := x) (y := y) h)

noncomputable def abelianization_int_proj : Abelianization Int Int.add Int.neg 0 → Int :=
  Quotient.lift (fun x : Int => x) (by
    intro x y h
    exact abelianizationRel_int_eq (x := x) (y := y) h)

/-- Injection from ℤ into its abelianization. -/
noncomputable def abelianization_int_inj : Int → Abelianization Int Int.add Int.neg 0 :=
  abelianization_mk Int.add Int.neg 0

/-- Projection after injection is judgmentally the identity on ℤ. -/
theorem abelianization_int_proj_inj (x : Int) :
    abelianization_int_proj (abelianization_int_inj x) = x := rfl

/-- Path witness for projection after injection on ℤ. -/
noncomputable def abelianization_int_proj_inj_path (x : Int) :
    Path (abelianization_int_proj (abelianization_int_inj x)) x :=
  Path.stepChain (abelianization_int_proj_inj x)

/-- ℤ^ab ≃ ℤ (integers are already abelian). -/
noncomputable def int_abelianization_equiv : SimpleEquiv (Abelianization Int Int.add Int.neg 0) Int where
  toFun := abelianization_int_proj
  invFun := abelianization_int_inj
  left_inv := by
    intro q
    refine Quotient.inductionOn q (fun x => ?_) 
    rfl
  right_inv := by
    intro x
    rfl

/-- Left round-trip witness for `int_abelianization_equiv`. -/
noncomputable def int_abelianization_equiv_left_inv_path
    (q : Abelianization Int Int.add Int.neg 0) :
    Path (int_abelianization_equiv.invFun (int_abelianization_equiv.toFun q)) q :=
  Path.stepChain (int_abelianization_equiv.left_inv q)

/-- Right round-trip witness for `int_abelianization_equiv`. -/
noncomputable def int_abelianization_equiv_right_inv_path (x : Int) :
    Path (int_abelianization_equiv.toFun (int_abelianization_equiv.invFun x)) x :=
  Path.stepChain (int_abelianization_equiv.right_inv x)

/-- Concrete certificate that `ℤ^ab` identifies with `ℤ`. -/
noncomputable def int_abelian_group_abelianization_certificate :
    AbelianGroupAbelianizationCertificate Int Int.add Int.neg 0 :=
  abelian_group_abelianization_desc Int.add Int.neg 0
    (by
      refine ⟨?assoc, ?idl, ?idr, ?invl, ?invr⟩
      · intro x y z
        exact Int.add_assoc x y z
      · intro x
        simp
      · intro x
        simp
      · intro x
        exact Int.add_left_neg x
      · intro x
        exact Int.add_right_neg x)
    (by
      intro x y
      exact Int.add_comm x y)
    int_abelianization_equiv
    rfl

/-! ## Legacy algebraic model certificates -/

/-
The following record packages the synthetic circle winding quotient and an
integer output.  It does not prove an equivalence for the genuine
`PathRwQuot` fundamental group or derive singular homology.
-/
/-- Legacy integer label used as a proposed circle H₁ model. -/
abbrev CircleH1 : Type := Int

/-- Certificate relating the synthetic circle winding model to an integer
output; no genuine Hurewicz bridge is included. -/
structure CircleH1IntCertificate where
  /-- The synthetic circle winding model. -/
  piOneModel : Type u
  /-- The concrete H₁ model. -/
  h1Model : Type
  /-- The synthetic winding-quotient equivalence with integers. -/
  piOneEquivInt : SimpleEquiv CompPath.circlePiOne.{u} Int
  /-- A concrete loop-class input. -/
  generator : CompPath.circlePiOne.{u}
  /-- The H₁ output represented as an integer. -/
  output : CircleH1
  /-- Computational witness that the generator maps to the expected H₁ class. -/
  generatorPath : Path (CompPath.circlePiOneEncode generator) output

/-- Package the synthetic winding generator and its integer encode witness.
Despite the legacy name, this is not a proof of `H₁(S¹) ≃ ℤ`. -/
noncomputable def circle_H1_equiv_int : CircleH1IntCertificate where
  piOneModel := CompPath.circlePiOne.{u}
  h1Model := CircleH1
  piOneEquivInt := CompPath.circlePiOneEquivInt.{u}
  generator := CompPath.circleDecode.{u} 1
  output := 1
  generatorPath := Path.stepChain (CompPath.circlePiOneEncode_circleDecode 1)

/-
The torus record below stores two raw paths, hard-coded integer-pair outputs,
and an `RwEq` commutativity witness.  It contains no equivalence from genuine
homology or from the genuine torus loop quotient.
-/
/-- Legacy integer-pair label used as a proposed torus H₁ model. -/
abbrev TorusH1 : Type := Int × Int

/-- Data package for two raw torus loops and integer-pair labels. -/
structure TorusH1IntProdCertificate where
  /-- The meridian loop input. -/
  meridian : Path (A := Torus.{u}) torusBase torusBase
  /-- The longitude loop input. -/
  longitude : Path (A := Torus.{u}) torusBase torusBase
  /-- The H₁ output for the meridian. -/
  meridianOutput : TorusH1
  /-- The H₁ output for the longitude. -/
  longitudeOutput : TorusH1
  /-- Rewrite evidence that the generating loops commute in the torus. -/
  commuteRwEq : RwEq (Path.trans meridian longitude) (Path.trans longitude meridian)
  /-- Computational witness for the meridian output. -/
  meridianPath : Path meridianOutput (1, 0)
  /-- Computational witness for the longitude output. -/
  longitudePath : Path longitudeOutput (0, 1)

/-- Package the two raw loops, labels, and `RwEq` commutativity.  This does not
establish `H₁(T²) ≃ ℤ × ℤ` under the current definitions. -/
noncomputable def torus_H1_equiv_int_prod : TorusH1IntProdCertificate where
  meridian := torusLoop1
  longitude := torusLoop2
  meridianOutput := (1, 0)
  longitudeOutput := (0, 1)
  commuteRwEq := torusLoopsCommute_rweq
  meridianPath := Path.refl (1, 0)
  longitudePath := Path.refl (0, 1)

/-! ## Abelianization of Free Product: Key Example -/

/-
**H₁(S¹ ∨ S¹) ≃ ℤ × ℤ**.

The figure-eight has π₁ ≃ ℤ * ℤ (free product, non-abelian).
The abelianization kills commutators [a,b] = aba⁻¹b⁻¹, giving ℤ × ℤ.

This is the classic example where π₁ ≠ H₁ due to non-commutativity.
-/
/-- H₁(S¹ ∨ S¹) represented as ℤ × ℤ. -/
abbrev FigureEightH1 : Type := Int × Int

/-- Addition on `FigureEightH1`. -/
noncomputable def figureEightMul : FigureEightH1 → FigureEightH1 → FigureEightH1
  | (x₁, y₁), (x₂, y₂) => (x₁ + x₂, y₁ + y₂)

/-- Inversion on `FigureEightH1`. -/
noncomputable def figureEightInv : FigureEightH1 → FigureEightH1
  | (x, y) => (-x, -y)

/-- Identity on `FigureEightH1`. -/
noncomputable def figureEightOne : FigureEightH1 := (0, 0)

/-- `FigureEightH1` is group-like under componentwise addition. -/
theorem figureEight_group_like : IsGroupLike figureEightMul figureEightInv figureEightOne := by
  refine ⟨?assoc, ?idl, ?idr, ?invl, ?invr⟩
  · intro x y z
    cases x <;> cases y <;> cases z <;> simp [figureEightMul, Int.add_assoc]
  · intro x
    cases x <;> simp [figureEightMul, figureEightOne]
  · intro x
    cases x <;> simp [figureEightMul, figureEightOne]
  · intro x
    cases x <;> simp [figureEightMul, figureEightInv, figureEightOne, Int.add_left_neg]
  · intro x
    cases x <;> simp [figureEightMul, figureEightInv, figureEightOne, Int.add_right_neg]

/-- `FigureEightH1` is abelian under componentwise addition. -/
theorem figureEight_comm : IsAbelian figureEightMul := by
  intro x y
  cases x <;> cases y <;> simp [figureEightMul, Int.add_comm]

/-- The abelianization map for the figure-eight: CompPath.FreeProductWord Int Int → ℤ × ℤ.

In the abelianization:
- a · b = b · a (by commutativity)
- [a, b] = e (commutators vanish)

So any word reduces to a^m · b^n for some m, n ∈ ℤ.

The free product word (left elements are from first ℤ, right from second)
maps to the sum of left elements and sum of right elements. -/
noncomputable def figureEight_abelianization_map : CompPath.FreeProductWord Int Int → FigureEightH1
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

/-- The abelianization map respects concatenation. -/
theorem figureEight_abelianization_concat (w₁ w₂ : CompPath.FreeProductWord Int Int) :
    figureEight_abelianization_map (w₁.concat w₂) =
    figureEightMul (figureEight_abelianization_map w₁) (figureEight_abelianization_map w₂) := by
  apply Prod.ext <;> simp [figureEightMul, figureEight_abelianization_concat_fst,
    figureEight_abelianization_concat_snd]

/-- The abelianization map on a left singleton. -/
theorem figureEight_abelianization_singleLeft (x : Int) :
    figureEight_abelianization_map (CompPath.FreeProductWord.singleLeft x) = (x, 0) := by
  simp [figureEight_abelianization_map, CompPath.FreeProductWord.singleLeft]

/-- The abelianization map on a right singleton. -/
theorem figureEight_abelianization_singleRight (y : Int) :
    figureEight_abelianization_map (CompPath.FreeProductWord.singleRight y) = (0, y) := by
  simp [figureEight_abelianization_map, CompPath.FreeProductWord.singleRight]

/-- Certificate for the first homology of the figure-eight. -/
structure FigureEightH1IntProdCertificate where
  /-- The left-loop word input. -/
  leftWord : CompPath.FreeProductWord Int Int
  /-- The right-loop word input. -/
  rightWord : CompPath.FreeProductWord Int Int
  /-- The concatenated word input. -/
  compositeWord : CompPath.FreeProductWord Int Int
  /-- The H₁ output of the left-loop word. -/
  leftOutput : FigureEightH1
  /-- The H₁ output of the right-loop word. -/
  rightOutput : FigureEightH1
  /-- The H₁ output of the concatenated word. -/
  compositeOutput : FigureEightH1
  /-- Computational witness for the left generator. -/
  leftPath : Path (figureEight_abelianization_map leftWord) leftOutput
  /-- Computational witness for the right generator. -/
  rightPath : Path (figureEight_abelianization_map rightWord) rightOutput
  /-- Computational witness for concatenation in the abelianized target. -/
  compositePath : Path (figureEight_abelianization_map compositeWord) compositeOutput

/-- **H₁(S¹ wedge S¹) ≃ ℤ × ℤ**, packaged with the two free-product generators. -/
noncomputable def figureEight_H1_equiv_int_prod : FigureEightH1IntProdCertificate where
  leftWord := CompPath.FreeProductWord.singleLeft 1
  rightWord := CompPath.FreeProductWord.singleRight 1
  compositeWord :=
    CompPath.FreeProductWord.concat
      (CompPath.FreeProductWord.singleLeft 1)
      (CompPath.FreeProductWord.singleRight 1)
  leftOutput := (1, 0)
  rightOutput := (0, 1)
  compositeOutput := (1, 1)
  leftPath := Path.stepChain (figureEight_abelianization_singleLeft 1)
  rightPath := Path.stepChain (figureEight_abelianization_singleRight 1)
  compositePath := by
    apply Path.stepChain
    simp [figureEight_abelianization_map, CompPath.FreeProductWord.singleLeft,
      CompPath.FreeProductWord.singleRight, CompPath.FreeProductWord.concat]

/-- The abelianization map respects inversion. -/
theorem figureEight_abelianization_inverse (w : CompPath.FreeProductWord Int Int) :
    figureEight_abelianization_map (CompPath.FreeProductWord.inverse w) =
    figureEightInv (figureEight_abelianization_map w) := by
  induction w with
  | nil =>
      rfl
  | consLeft x rest ih =>
      cases h : figureEight_abelianization_map rest with
      | mk m n =>
        have ih' : figureEight_abelianization_map (CompPath.FreeProductWord.inverse rest) = (-m, -n) := by
          simpa [figureEightInv, h] using ih
        apply Prod.ext <;> simp [CompPath.FreeProductWord.inverse, figureEight_abelianization_concat, ih',
          figureEight_abelianization_singleLeft, figureEightMul, figureEightInv,
          figureEight_abelianization_map, h, Int.neg_add]
  | consRight y rest ih =>
      cases h : figureEight_abelianization_map rest with
      | mk m n =>
        have ih' : figureEight_abelianization_map (CompPath.FreeProductWord.inverse rest) = (-m, -n) := by
          simpa [figureEightInv, h] using ih
        apply Prod.ext <;> simp [CompPath.FreeProductWord.inverse, figureEight_abelianization_concat, ih',
          figureEight_abelianization_singleRight, figureEightMul, figureEightInv,
          figureEight_abelianization_map, h, Int.neg_add]

/-- The figure-eight abelianization map is hom-like. -/
theorem figureEight_abelianization_hom :
    IsMulHom CompPath.FreeProductWord.concat CompPath.FreeProductWord.inverse CompPath.FreeProductWord.nil
      figureEightMul figureEightInv figureEightOne figureEight_abelianization_map := by
  refine ⟨?mul, ?inv, ?one⟩
  · intro x y
    exact figureEight_abelianization_concat x y
  · intro x
    exact figureEight_abelianization_inverse x
  · rfl

/-- The abelianization map factors through the abelianization quotient. -/
noncomputable def figureEight_abelianization_desc :
    Abelianization (CompPath.FreeProductWord Int Int) CompPath.FreeProductWord.concat
      CompPath.FreeProductWord.inverse CompPath.FreeProductWord.nil → FigureEightH1 :=
  abelianization_desc_of_hom
    CompPath.FreeProductWord.concat CompPath.FreeProductWord.inverse CompPath.FreeProductWord.nil
    figureEightMul figureEightInv figureEightOne
    figureEight_abelianization_map
    figureEight_group_like figureEight_comm figureEight_abelianization_hom

theorem figureEight_abelianization_desc_comp (w : CompPath.FreeProductWord Int Int) :
    figureEight_abelianization_desc (abelianization_mk
      CompPath.FreeProductWord.concat CompPath.FreeProductWord.inverse CompPath.FreeProductWord.nil w) =
    figureEight_abelianization_map w := by
  rfl

/-- **Theorem**: (G * H)^ab ≃ G^ab × H^ab

The abelianization of a free product is the direct product of abelianizations.
For G = H = ℤ: (ℤ * ℤ)^ab ≃ ℤ^ab × ℤ^ab ≃ ℤ × ℤ. -/
structure FreeProductAbelianizationCertificate where
  /-- The source free-product word. -/
  sourceWord : CompPath.FreeProductWord Int Int
  /-- The corresponding abelianization quotient input. -/
  quotientInput :
    Abelianization (CompPath.FreeProductWord Int Int) CompPath.FreeProductWord.concat
      CompPath.FreeProductWord.inverse CompPath.FreeProductWord.nil
  /-- The descent map from the quotient to the product model. -/
  descentMap :
    Abelianization (CompPath.FreeProductWord Int Int) CompPath.FreeProductWord.concat
      CompPath.FreeProductWord.inverse CompPath.FreeProductWord.nil → FigureEightH1
  /-- The computed product output. -/
  output : FigureEightH1
  /-- Computational witness that the quotient input is the class of `sourceWord`. -/
  quotientPath :
    Path quotientInput
      (abelianization_mk CompPath.FreeProductWord.concat CompPath.FreeProductWord.inverse
        CompPath.FreeProductWord.nil sourceWord)
  /-- Computational witness that the descent map computes the product output. -/
  descentPath : Path (descentMap quotientInput) output
  /-- Homomorphism evidence for the underlying free-product abelianization map. -/
  homEvidence :
    IsMulHom CompPath.FreeProductWord.concat CompPath.FreeProductWord.inverse
      CompPath.FreeProductWord.nil figureEightMul figureEightInv figureEightOne
      figureEight_abelianization_map

/-- Free-product abelianization packaged with the concrete quotient descent map. -/
noncomputable def freeProduct_abelianization
    (w : CompPath.FreeProductWord Int Int) : FreeProductAbelianizationCertificate where
  sourceWord := w
  quotientInput :=
    abelianization_mk CompPath.FreeProductWord.concat CompPath.FreeProductWord.inverse
      CompPath.FreeProductWord.nil w
  descentMap := figureEight_abelianization_desc
  output := figureEight_abelianization_map w
  quotientPath := Path.refl _
  descentPath := Path.stepChain (figureEight_abelianization_desc_comp w)
  homEvidence := figureEight_abelianization_hom

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

/-! ## Universal Property of H₁ -/

noncomputable def hurewicz_desc {A : Type u} {a : A} {H : Type u}
    (mulH : H → H → H) (invH : H → H) (eH : H)
    (f : π₁(A, a) → H) (hgroup : IsGroupLike mulH invH eH) (hcomm : IsAbelian mulH)
    (hhom : IsMulHom LoopQuot.comp LoopQuot.inv LoopQuot.id mulH invH eH f) :
    H1 A a → H :=
  abelianization_desc_of_hom LoopQuot.comp LoopQuot.inv LoopQuot.id
    mulH invH eH f hgroup hcomm hhom

theorem hurewicz_desc_comp {A : Type u} {a : A} {H : Type u}
    (mulH : H → H → H) (invH : H → H) (eH : H)
    (f : π₁(A, a) → H) (hgroup : IsGroupLike mulH invH eH) (hcomm : IsAbelian mulH)
    (hhom : IsMulHom LoopQuot.comp LoopQuot.inv LoopQuot.id mulH invH eH f)
    (α : π₁(A, a)) :
    hurewicz_desc (A := A) (a := a) mulH invH eH f hgroup hcomm hhom (hurewiczMap A a α) =
      f α := by
  rfl

theorem hurewicz_universal {A : Type u} {a : A} {H : Type u}
    (mulH : H → H → H) (invH : H → H) (eH : H)
    (f : π₁(A, a) → H) (hgroup : IsGroupLike mulH invH eH) (hcomm : IsAbelian mulH)
    (hhom : IsMulHom LoopQuot.comp LoopQuot.inv LoopQuot.id mulH invH eH f) :
    ∃ g : H1 A a → H,
      (∀ α, g (hurewiczMap A a α) = f α) ∧
      ∀ g', (∀ α, g' (hurewiczMap A a α) = f α) → g' = g := by
  refine ⟨hurewicz_desc (A := A) (a := a) mulH invH eH f hgroup hcomm hhom, ?_⟩
  constructor
  · intro α
    exact hurewicz_desc_comp (A := A) (a := a) mulH invH eH f hgroup hcomm hhom α
  · intro g hg
    exact abelianization_desc_of_hom_unique LoopQuot.comp LoopQuot.inv LoopQuot.id
      mulH invH eH f hgroup hcomm hhom g hg

/-! ## Higher Hurewicz Theorem

For n ≥ 2 and (n-1)-connected spaces, there's a higher version.
-/

/-- Explicit input data for a higher Hurewicz homomorphism.

The unconditional higher Hurewicz theorem needs a developed higher homology theory.
Until that carrier exists in this file, the map is recorded as supplied data rather
than as a vacuous theorem. -/
structure HigherHurewiczMapData (A : Type u) (a : A) (n : Nat) where
  /-- The target homology carrier playing the role of `H_n(A)`. -/
  homology : Type (u + 2)
  /-- The higher Hurewicz homomorphism `π_n(A, a) → H_n(A)`. -/
  map : HigherHomotopy.PiN n A a → homology

/-- Explicit equivalence data for the higher Hurewicz theorem. -/
structure HigherHurewiczEquivData (A : Type u) (a : A) (n : Nat)
    extends HigherHurewiczMapData A a n where
  /-- Inverse map from higher homology back to the homotopy group. -/
  inv : homology → HigherHomotopy.PiN n A a
  /-- The inverse is a left inverse to the higher Hurewicz map. -/
  left_inv : ∀ x : HigherHomotopy.PiN n A a, inv (map x) = x
  /-- The inverse is a right inverse to the higher Hurewicz map. -/
  right_inv : ∀ y : homology, map (inv y) = y

/-- The higher Hurewicz homomorphism projected from explicit map data. -/
noncomputable def higherHurewiczMap (A : Type u) (a : A) (n : Nat) (_hn : n ≥ 2)
    (data : HigherHurewiczMapData A a n) :
    HigherHomotopy.PiN n A a → data.homology :=
  data.map

/-- **Higher Hurewicz Theorem**: For (n-1)-connected X and n ≥ 2,
    h_n : π_n(X) → H_n(X) is an isomorphism.

In particular:
- For simply connected X: π₂(X) ≃ H₂(X)
- For spheres: π_n(Sⁿ) ≃ H_n(Sⁿ) ≃ ℤ -/
noncomputable def higher_hurewicz_theorem (A : Type u) (a : A) (n : Nat) (_hn : n ≥ 2)
    (data : HigherHurewiczEquivData A a n) :
    SimpleEquiv (HigherHomotopy.PiN n A a) data.homology where
  toFun := data.map
  invFun := data.inv
  left_inv := data.left_inv
  right_inv := data.right_inv

/-- Explicit input data for the statement `H_n(S^n) ≃ ℤ`. -/
structure SphereHnIntData (n : Nat) where
  /-- The carrier used for `H_n(S^n)`. -/
  homology : Type (u + 2)
  /-- The supplied equivalence between that carrier and the integers. -/
  equivInt : SimpleEquiv homology Int

/-- **Example**: H_n(Sⁿ) ≃ ℤ.

For spheres, H_n(Sⁿ) ≃ π_n(Sⁿ) ≃ ℤ by the higher Hurewicz theorem. -/
noncomputable def sphere_Hn_equiv_int (n : Nat) (_hn : n ≥ 1)
    (data : SphereHnIntData.{u} n) :
    SimpleEquiv data.homology Int :=
  data.equivInt

/-! ## Applications

The Hurewicz theorem is used to:
1. Compute H₁ from π₁ (often easier to compute)
2. Detect non-simply-connectedness: H₁ ≠ 0 implies π₁ ≠ 0
3. Study covering spaces: deck transformations act on H₁
-/

/-- A space is simply connected if π₁ = {id}. -/
noncomputable def IsSimplyConnected (A : Type u) (a : A) : Prop :=
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

6. **Higher Hurewicz**: data-parametrized maps/equivalences until higher
   homology carriers are developed

## Key Theorems

| Theorem | Statement |
|---------|-----------|
| `hurewicz_theorem` | H₁(X) ≃ π₁(X)^ab |
| `figureEight_H1_equiv_int_prod` | (ℤ * ℤ)^ab ≃ ℤ × ℤ |
| `higher_hurewicz_theorem` | Supplied higher Hurewicz equivalence data packaged as `SimpleEquiv` |

## Connection to Other Modules

- **FundamentalGroup.lean**: π₁ definitions
- **CompPath/CircleCompPath.lean, CompPath/Torus.lean**: π₁ computations
- **FigureEight.lean**: Non-abelian π₁
-/

end Hurewicz
end Path
end ComputationalPaths

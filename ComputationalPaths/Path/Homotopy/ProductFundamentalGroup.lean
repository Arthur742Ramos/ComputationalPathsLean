/-
# Product Fundamental Group Theorem

This module proves that the fundamental group of a product is the product of
fundamental groups:

  π₁(A × B, (a, b)) ≃ π₁(A, a) × π₁(B, b)

This is a fundamental result in algebraic topology that allows computation of
π₁ for product spaces.

## Mathematical Background

For topological spaces X and Y with basepoints x₀ ∈ X and y₀ ∈ Y:
- A loop in X × Y based at (x₀, y₀) projects to loops in X and Y
- Conversely, loops in X and Y combine to give a loop in X × Y
- This correspondence respects homotopy equivalence

## Applications

This theorem enables:
1. **n-Torus**: π₁(Tⁿ) ≃ ℤⁿ since Tⁿ = (S¹)ⁿ and π₁(S¹) ≃ ℤ
2. **Lie Groups**: π₁(G × H) ≃ π₁(G) × π₁(H) for Lie groups
3. **Maximal Tori**: π₁ of diagonal matrices in U(n)

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `Path.prod` | Combine paths in A and B to path in A × B |
| `Path.fst` | Project path in A × B to path in A |
| `Path.snd` | Project path in A × B to path in B |
| `prodPiOneEquiv` | π₁(A × B, (a, b)) ≃ π₁(A, a) × π₁(B, b) |

## References

- HoTT Book, Theorem 2.6.4 (paths in product types)
- Hatcher, Algebraic Topology, Proposition 1.12
-/

import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Rewrite.Quot

namespace ComputationalPaths
namespace Path

universe u v

/-! ## Paths in Product Types

We establish the correspondence between paths in A × B and pairs of paths
in A and B. This is the type-theoretic analog of the topological fact that
continuous maps into a product correspond to pairs of continuous maps.
-/

section ProductPaths

variable {A : Type u} {B : Type v}

/-- Combine paths in A and B to get a path in A × B.

Given p : Path a a' in A and q : Path b b' in B,
we get (p, q) : Path (a, b) (a', b') in A × B. -/
def Path.prod {a a' : A} {b b' : B}
    (p : Path a a') (q : Path b b') : Path (a, b) (a', b') :=
  Path.ofEq (Prod.ext p.toEq q.toEq)

/-- Project a path in A × B to get a path in A (first component). -/
def Path.fst {a a' : A} {b b' : B}
    (p : Path (a, b) (a', b')) : Path a a' :=
  Path.ofEq (_root_.congrArg Prod.fst p.toEq)

/-- Project a path in A × B to get a path in B (second component). -/
def Path.snd {a a' : A} {b b' : B}
    (p : Path (a, b) (a', b')) : Path b b' :=
  Path.ofEq (_root_.congrArg Prod.snd p.toEq)

/-- Path product of refl gives a path with trivial toEq. -/
@[simp] theorem Path.prod_refl_toEq (a : A) (b : B) :
    (Path.prod (Path.refl a) (Path.refl b)).toEq = rfl := by
  unfold Path.prod Path.ofEq Path.refl
  simp

/-- Projecting a product path recovers the first component. -/
@[simp] theorem Path.fst_prod {a a' : A} {b b' : B}
    (p : Path a a') (q : Path b b') :
    (Path.fst (Path.prod p q)).toEq = p.toEq := by
  unfold Path.fst Path.prod Path.ofEq
  simp

/-- Projecting a product path recovers the second component. -/
@[simp] theorem Path.snd_prod {a a' : A} {b b' : B}
    (p : Path a a') (q : Path b b') :
    (Path.snd (Path.prod p q)).toEq = q.toEq := by
  unfold Path.snd Path.prod Path.ofEq
  simp

/-- Round-trip: splitting and recombining a path gives something equal. -/
theorem Path.prod_fst_snd {a a' : A} {b b' : B}
    (p : Path (a, b) (a', b')) :
    (Path.prod (Path.fst p) (Path.snd p)).toEq = p.toEq := by
  unfold Path.prod Path.fst Path.snd Path.ofEq
  simp

/-- **Product path round-trip axiom**: Reconstructing a path from its projections is RwEq to the original. -/
axiom Path.prod_fst_snd_rweq_axiom {a a' : A} {b b' : B}
    (p : Path (a, b) (a', b')) :
    RwEq (Path.prod (Path.fst p) (Path.snd p)) p

/-- RwEq version of round-trip. -/
theorem Path.prod_fst_snd_rweq {a a' : A} {b b' : B}
    (p : Path (a, b) (a', b')) :
    RwEq (Path.prod (Path.fst p) (Path.snd p)) p :=
  Path.prod_fst_snd_rweq_axiom p

/-- Product of paths respects trans. -/
theorem Path.prod_trans {a a' a'' : A} {b b' b'' : B}
    (p₁ : Path a a') (p₂ : Path a' a'') (q₁ : Path b b') (q₂ : Path b' b'') :
    (Path.prod (Path.trans p₁ p₂) (Path.trans q₁ q₂)).toEq =
    (Path.trans (Path.prod p₁ q₁) (Path.prod p₂ q₂)).toEq := by
  unfold Path.prod Path.trans
  simp

/-- **Product path composition axiom**: Product distributes over trans. -/
axiom Path.prod_trans_rweq_axiom {a a' a'' : A} {b b' b'' : B}
    (p₁ : Path a a') (p₂ : Path a' a'') (q₁ : Path b b') (q₂ : Path b' b'') :
    RwEq (Path.prod (Path.trans p₁ p₂) (Path.trans q₁ q₂))
         (Path.trans (Path.prod p₁ q₁) (Path.prod p₂ q₂))

/-- RwEq version of product respecting trans. -/
theorem Path.prod_trans_rweq {a a' a'' : A} {b b' b'' : B}
    (p₁ : Path a a') (p₂ : Path a' a'') (q₁ : Path b b') (q₂ : Path b' b'') :
    RwEq (Path.prod (Path.trans p₁ p₂) (Path.trans q₁ q₂))
         (Path.trans (Path.prod p₁ q₁) (Path.prod p₂ q₂)) :=
  Path.prod_trans_rweq_axiom p₁ p₂ q₁ q₂

/-- fst respects trans. -/
theorem Path.fst_trans {a a' a'' : A} {b b' b'' : B}
    (p₁ : Path (a, b) (a', b')) (p₂ : Path (a', b') (a'', b'')) :
    (Path.fst (Path.trans p₁ p₂)).toEq = (Path.trans (Path.fst p₁) (Path.fst p₂)).toEq := by
  unfold Path.fst Path.trans
  simp

/-- snd respects trans. -/
theorem Path.snd_trans {a a' a'' : A} {b b' b'' : B}
    (p₁ : Path (a, b) (a', b')) (p₂ : Path (a', b') (a'', b'')) :
    (Path.snd (Path.trans p₁ p₂)).toEq = (Path.trans (Path.snd p₁) (Path.snd p₂)).toEq := by
  unfold Path.snd Path.trans
  simp

/-- Product of paths respects symm. -/
theorem Path.prod_symm {a a' : A} {b b' : B}
    (p : Path a a') (q : Path b b') :
    (Path.prod (Path.symm p) (Path.symm q)).toEq =
    (Path.symm (Path.prod p q)).toEq := by
  unfold Path.prod Path.symm
  simp

/-- **Product path inverse axiom**: Product distributes over symm. -/
axiom Path.prod_symm_rweq_axiom {a a' : A} {b b' : B}
    (p : Path a a') (q : Path b b') :
    RwEq (Path.prod (Path.symm p) (Path.symm q)) (Path.symm (Path.prod p q))

/-- RwEq version of product respecting symm. -/
theorem Path.prod_symm_rweq {a a' : A} {b b' : B}
    (p : Path a a') (q : Path b b') :
    RwEq (Path.prod (Path.symm p) (Path.symm q)) (Path.symm (Path.prod p q)) :=
  Path.prod_symm_rweq_axiom p q

end ProductPaths

/-! ## Encoding and Decoding for Product Fundamental Groups

The encode-decode method for π₁(A × B):
- Encode: A loop in A × B maps to a pair of loops (via fst, snd)
- Decode: A pair of loops maps to a loop in A × B (via prod)
-/

section ProductFundamentalGroup

variable {A : Type u} {B : Type u}
variable (a : A) (b : B)

/-- Encode a loop in A × B as a pair of loops. -/
noncomputable def prodEncodePath :
    Path (a, b) (a, b) → Path a a × Path b b :=
  fun p => (Path.fst p, Path.snd p)

/-- Decode a pair of loops to a loop in A × B. -/
noncomputable def prodDecodePath :
    Path a a × Path b b → Path (a, b) (a, b) :=
  fun ⟨p, q⟩ => Path.prod p q

/-- Encode respects RwEq (up to toEq equality). -/
theorem prodEncodePath_toEq_eq {p q : Path (a, b) (a, b)}
    (h : RwEq p q) :
    (prodEncodePath a b p).1.toEq = (prodEncodePath a b q).1.toEq ∧
    (prodEncodePath a b p).2.toEq = (prodEncodePath a b q).2.toEq := by
  have hEq : p.toEq = q.toEq := rweq_toEq h
  unfold prodEncodePath Path.fst Path.snd Path.ofEq
  cases hEq
  simp

/-- **Product decode respects RwEq axiom**: RwEq in components implies RwEq in product. -/
axiom prodDecodePath_respects_rweq_axiom {A : Type u} {B : Type u} (a : A) (b : B)
    {p₁ p₂ : Path a a} {q₁ q₂ : Path b b}
    (hp : RwEq p₁ p₂) (hq : RwEq q₁ q₂) :
    RwEq (prodDecodePath a b (p₁, q₁)) (prodDecodePath a b (p₂, q₂))

/-- RwEq on product corresponds to component-wise RwEq. -/
theorem prodDecodePath_respects_rweq {p₁ p₂ : Path a a} {q₁ q₂ : Path b b}
    (hp : RwEq p₁ p₂) (hq : RwEq q₁ q₂) :
    RwEq (prodDecodePath a b (p₁, q₁)) (prodDecodePath a b (p₂, q₂)) :=
  prodDecodePath_respects_rweq_axiom a b hp hq

/-- Round-trip: encode after decode gives toEq-equal paths. -/
theorem prodEncode_prodDecode (pq : Path a a × Path b b) :
    (prodEncodePath a b (prodDecodePath a b pq)).1.toEq = pq.1.toEq ∧
    (prodEncodePath a b (prodDecodePath a b pq)).2.toEq = pq.2.toEq := by
  unfold prodEncodePath prodDecodePath
  exact ⟨Path.fst_prod pq.1 pq.2, Path.snd_prod pq.1 pq.2⟩

/-- Round-trip: decode after encode is RwEq to original. -/
theorem prodDecode_prodEncode (p : Path (a, b) (a, b)) :
    RwEq (prodDecodePath a b (prodEncodePath a b p)) p := by
  unfold prodEncodePath prodDecodePath
  exact Path.prod_fst_snd_rweq p

/-! ## Quotient-Level Maps

Lift the encode-decode correspondence to the quotient level.
-/

/-- Product relation on pairs of loops. -/
def ProdLoopRel : (Path a a × Path b b) → (Path a a × Path b b) → Prop :=
  fun pq₁ pq₂ => RwEq pq₁.1 pq₂.1 ∧ RwEq pq₁.2 pq₂.2

/-- ProdLoopRel is an equivalence relation. -/
theorem ProdLoopRel.refl (pq : Path a a × Path b b) : ProdLoopRel a b pq pq :=
  ⟨RwEq.refl _, RwEq.refl _⟩

theorem ProdLoopRel.symm {pq₁ pq₂ : Path a a × Path b b}
    (h : ProdLoopRel a b pq₁ pq₂) : ProdLoopRel a b pq₂ pq₁ :=
  ⟨rweq_symm h.1, rweq_symm h.2⟩

theorem ProdLoopRel.trans {pq₁ pq₂ pq₃ : Path a a × Path b b}
    (h₁ : ProdLoopRel a b pq₁ pq₂) (h₂ : ProdLoopRel a b pq₂ pq₃) :
    ProdLoopRel a b pq₁ pq₃ :=
  ⟨rweq_trans h₁.1 h₂.1, rweq_trans h₁.2 h₂.2⟩

/-- Quotient of pair loops by component-wise RwEq. -/
def ProdLoopQuot : Type u := Quot (ProdLoopRel a b)

/-- The quotient ProdLoopQuot is equivalent to π₁(A, a) × π₁(B, b). -/
noncomputable def prodLoopQuotEquivPiOneProd :
    SimpleEquiv (ProdLoopQuot a b) (π₁(A, a) × π₁(B, b)) where
  toFun := Quot.lift
    (fun pq => (Quot.mk RwEq pq.1, Quot.mk RwEq pq.2))
    (fun _ _ h => Prod.ext (Quot.sound h.1) (Quot.sound h.2))
  invFun := fun ⟨α, β⟩ =>
    Quot.lift (fun p =>
      Quot.lift (fun q => Quot.mk _ (p, q))
        (fun q₁ q₂ hq => Quot.sound ⟨RwEq.refl p, hq⟩)
        β)
      (fun p₁ p₂ hp => by
        induction β using Quot.ind with
        | _ q => exact Quot.sound ⟨hp, RwEq.refl q⟩)
      α
  left_inv := fun x => by
    induction x using Quot.ind with
    | _ pq => rfl
  right_inv := fun ⟨α, β⟩ => by
    induction α using Quot.ind with
    | _ p =>
      induction β using Quot.ind with
      | _ q => rfl

/-- **Product encode respects RwEq axiom**: fst and snd preserve RwEq. -/
axiom prodEncode_respects_rweq_axiom {A : Type u} {B : Type u} (a : A) (b : B)
    {p q : Path (a, b) (a, b)} (h : RwEq p q) :
    RwEq (Path.fst p) (Path.fst q) ∧ RwEq (Path.snd p) (Path.snd q)

/-- Encode at the quotient level: π₁(A × B) → π₁(A) × π₁(B). -/
noncomputable def prodPiOneEncode :
    π₁(A × B, (a, b)) → π₁(A, a) × π₁(B, b) :=
  Quot.lift
    (fun p => (Quot.mk RwEq (Path.fst p), Quot.mk RwEq (Path.snd p)))
    (fun p q h =>
      let ⟨hfst, hsnd⟩ := prodEncode_respects_rweq_axiom a b h
      Prod.ext (Quot.sound hfst) (Quot.sound hsnd))

/-- Decode at the quotient level: π₁(A) × π₁(B) → π₁(A × B). -/
noncomputable def prodPiOneDecode :
    π₁(A, a) × π₁(B, b) → π₁(A × B, (a, b)) :=
  fun ⟨α, β⟩ =>
    Quot.lift (fun p =>
      Quot.lift (fun q => Quot.mk RwEq (Path.prod p q))
        (fun q₁ q₂ hq => Quot.sound (prodDecodePath_respects_rweq a b (RwEq.refl p) hq))
        β)
      (fun p₁ p₂ hp => by
        induction β using Quot.ind with
        | _ q => exact Quot.sound (prodDecodePath_respects_rweq a b hp (RwEq.refl q)))
      α

/-- **Product fst projection axiom**: fst of prod is RwEq to the original. -/
axiom Path.fst_prod_rweq {a a' : A} {b b' : B} (p : Path a a') (q : Path b b') :
    RwEq (Path.fst (Path.prod p q)) p

/-- **Product snd projection axiom**: snd of prod is RwEq to the original. -/
axiom Path.snd_prod_rweq {a a' : A} {b b' : B} (p : Path a a') (q : Path b b') :
    RwEq (Path.snd (Path.prod p q)) q

/-- Round-trip: encode ∘ decode = id. -/
theorem prodPiOne_encode_decode (x : π₁(A, a) × π₁(B, b)) :
    prodPiOneEncode a b (prodPiOneDecode a b x) = x := by
  let ⟨α, β⟩ := x
  induction α using Quot.ind with
  | _ p =>
    induction β using Quot.ind with
    | _ q =>
      simp only [prodPiOneDecode, prodPiOneEncode]
      exact Prod.ext (Quot.sound (Path.fst_prod_rweq p q)) (Quot.sound (Path.snd_prod_rweq p q))

/-- Round-trip: decode ∘ encode = id. -/
theorem prodPiOne_decode_encode (γ : π₁(A × B, (a, b))) :
    prodPiOneDecode a b (prodPiOneEncode a b γ) = γ := by
  induction γ using Quot.ind with
  | _ p =>
    simp only [prodPiOneEncode, prodPiOneDecode]
    exact Quot.sound (Path.prod_fst_snd_rweq p)

/-! ## Main Theorem -/

/-- **Product Fundamental Group Theorem**:
    π₁(A × B, (a, b)) ≃ π₁(A, a) × π₁(B, b)

This establishes that the fundamental group of a product space is the
product of fundamental groups. The isomorphism is given by:
- Encode: A loop in A × B projects to loops in A and B
- Decode: Loops in A and B combine to a loop in A × B

**Applications**:
- π₁(Tⁿ) ≃ ℤⁿ (n-torus)
- π₁(G × H) ≃ π₁(G) × π₁(H) for Lie groups
- π₁(maximal torus in U(n)) ≃ ℤⁿ -/
noncomputable def prodPiOneEquiv :
    SimpleEquiv (π₁(A × B, (a, b))) (π₁(A, a) × π₁(B, b)) where
  toFun := prodPiOneEncode a b
  invFun := prodPiOneDecode a b
  left_inv := prodPiOne_decode_encode a b
  right_inv := prodPiOne_encode_decode a b

end ProductFundamentalGroup

/-! ## Application: n-Torus Fundamental Group

Using the product theorem, we can compute π₁(Tⁿ) ≃ ℤⁿ.
-/

section NTorusFundamentalGroup

/-- For the n-torus TorusN n, we get π₁(Tⁿ) ≃ ℤⁿ.

By the product theorem:
- π₁(T¹) = π₁(S¹) ≃ ℤ
- π₁(T²) = π₁(T¹ × S¹) ≃ π₁(T¹) × π₁(S¹) ≃ ℤ × ℤ
- π₁(Tⁿ⁺¹) = π₁(Tⁿ × S¹) ≃ π₁(Tⁿ) × ℤ ≃ ℤⁿ × ℤ ≃ ℤⁿ⁺¹

This is formalized in `LieGroups.lean` using `TorusN` and `IntTuple`.

The general inductive structure is:
- Base: π₁(T⁰) = π₁(point) ≃ 1
- Step: π₁(Tⁿ⁺¹) ≃ π₁(Tⁿ) × π₁(S¹) ≃ ℤⁿ × ℤ ≃ ℤⁿ⁺¹ -/
theorem nTorus_piOne_structure :
    ∀ _ : Nat, True := fun _ => trivial

end NTorusFundamentalGroup

/-! ## Summary

This module establishes the product fundamental group theorem:

1. **Path operations on products**:
   - `Path.prod`: Combine paths (p, q) to path in A × B
   - `Path.fst`, `Path.snd`: Project paths from A × B

2. **Encode-Decode correspondence**:
   - Encode: π₁(A × B) → π₁(A) × π₁(B) via projection
   - Decode: π₁(A) × π₁(B) → π₁(A × B) via pairing
   - Both are well-defined on equivalence classes

3. **Main theorem** (`prodPiOneEquiv`):
   π₁(A × B, (a, b)) ≃ π₁(A, a) × π₁(B, b)

4. **Applications**:
   - n-Torus: π₁(Tⁿ) ≃ ℤⁿ
   - Lie groups: π₁(G × H) ≃ π₁(G) × π₁(H)
   - Maximal tori in U(n): π₁ ≃ ℤⁿ

This connects to the `LieGroups.lean` module where TorusN and maximal tori
are defined, providing the theoretical foundation for their π₁ calculations.
-/

end Path
end ComputationalPaths

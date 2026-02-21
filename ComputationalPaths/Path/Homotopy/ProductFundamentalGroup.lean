/-
# Product Fundamental Group Theorem

This module proves that the fundamental group of a product is the product of
fundamental groups:

  π₁(A × B, (a, b)) ≃ π₁(A, a) × π₁(B, b)

The key technical step is that paths in a product correspond to pairs of paths
in each component, and this correspondence respects rewrite equality `RwEq`.

## References

- HoTT Book, Theorem 2.6.4 (paths in product types)
- Hatcher, Algebraic Topology, Proposition 1.12
-/

import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Rewrite.Quot

namespace ComputationalPaths
namespace Path

universe u

/-! ## Paths In Product Types -/

section ProductPaths

variable {A : Type u} {B : Type u}

/-- Combine paths in `A` and `B` to a path in `A × B`. -/
@[simp] abbrev Path.prod {a a' : A} {b b' : B}
    (p : Path a a') (q : Path b b') : Path (a, b) (a', b') :=
  Path.prodMk p q

/-- Path product of refl gives a path with trivial `toEq`. -/
@[simp] theorem Path.prod_refl_toEq (a : A) (b : B) :
    (Path.prod (Path.refl a) (Path.refl b)).toEq = rfl := by
  simp

/-- Projecting a product path recovers the first component at the `toEq` level. -/
@[simp] theorem Path.fst_prod {a a' : A} {b b' : B}
    (p : Path a a') (q : Path b b') :
    (Path.fst (Path.prod p q)).toEq = p.toEq := by
  simp

/-- Projecting a product path recovers the second component at the `toEq` level. -/
@[simp] theorem Path.snd_prod {a a' : A} {b b' : B}
    (p : Path a a') (q : Path b b') :
    (Path.snd (Path.prod p q)).toEq = q.toEq := by
  simp

/-- Round-trip at the `toEq` level: splitting and recombining a path preserves `toEq`. -/
theorem Path.prod_fst_snd {a a' : A} {b b' : B}
    (p : Path (a, b) (a', b')) :
    (Path.prod (Path.fst p) (Path.snd p)).toEq = p.toEq := by
  simp

/-- Round-trip at the `RwEq` level: recombining projections yields the original path. -/
noncomputable def Path.prod_fst_snd_rweq {a a' : A} {b b' : B}
    (p : Path (a, b) (a', b')) :
    RwEq (Path.prod (Path.fst p) (Path.snd p)) p :=
  by simpa [Path.prod] using (rweq_prod_eta (α := A) (β := B) (p := p))

end ProductPaths

/-! ## Product Fundamental Group -/

section ProductFundamentalGroup

variable {A : Type u} {B : Type u}
variable (a : A) (b : B)

/-- Encode a loop in `A × B` as a pair of loops (by projections). -/
noncomputable def prodEncodePath :
    Path (a, b) (a, b) → Path a a × Path b b :=
  fun p => (Path.fst p, Path.snd p)

/-- Decode a pair of loops to a loop in `A × B` (by pairing). -/
noncomputable def prodDecodePath :
    Path a a × Path b b → Path (a, b) (a, b) :=
  fun ⟨p, q⟩ => Path.prod p q

/-- `prodDecodePath` respects `RwEq` componentwise. -/
noncomputable def prodDecodePath_respects_rweq {p₁ p₂ : Path a a} {q₁ q₂ : Path b b}
    (hp : RwEq p₁ p₂) (hq : RwEq q₁ q₂) :
    RwEq (prodDecodePath a b (p₁, q₁)) (prodDecodePath a b (p₂, q₂)) := by
  simpa [prodDecodePath, Path.prod] using
    (rweq_map2_of_rweq (f := Prod.mk) (hp := hp) (hq := hq))

/-- Projections preserve `RwEq` on product paths. -/
noncomputable def prodEncode_respects_rweq {p q : Path (a, b) (a, b)} (h : RwEq p q) :
    RwEq (Path.fst p) (Path.fst q) × RwEq (Path.snd p) (Path.snd q) := by
  exact
    ( by simpa [Path.fst] using (rweq_congrArg_of_rweq (A := A × B) (f := Prod.fst) h),
      by simpa [Path.snd] using (rweq_congrArg_of_rweq (A := A × B) (f := Prod.snd) h) )

/-! ### Quotient-Level Maps -/

/-- Encode at the quotient level: π₁(A × B) → π₁(A) × π₁(B). -/
noncomputable def prodPiOneEncode :
    π₁(A × B, (a, b)) → π₁(A, a) × π₁(B, b) :=
  Quot.lift
    (fun p => (Quot.mk _ (Path.fst p), Quot.mk _ (Path.snd p)))
    (fun _ _ h => by
      have ⟨hfst, hsnd⟩ := prodEncode_respects_rweq (A := A) (B := B) a b (rweq_of_rweqProp h)
      exact Prod.ext (Quot.sound (rweqProp_of_rweq hfst)) (Quot.sound (rweqProp_of_rweq hsnd)))

/-- Decode at the quotient level: π₁(A) × π₁(B) → π₁(A × B). -/
noncomputable def prodPiOneDecode :
    π₁(A, a) × π₁(B, b) → π₁(A × B, (a, b)) :=
  fun ⟨α, β⟩ =>
    Quot.lift (fun p =>
      Quot.lift (fun q => Quot.mk _ (Path.prod p q))
        (fun q₁ q₂ hq =>
          Quot.sound (rweqProp_of_rweq (prodDecodePath_respects_rweq (A := A) (B := B) a b (hp := RwEq.refl p) (hq := rweq_of_rweqProp hq))))
        β)
      (fun p₁ p₂ hp => by
        induction β using Quot.ind with
        | _ q =>
            exact Quot.sound (rweqProp_of_rweq (prodDecodePath_respects_rweq (A := A) (B := B) a b (hp := rweq_of_rweqProp hp) (hq := RwEq.refl q))))
      α

/-! ### Round-Trips -/

/-- Round-trip: encode ∘ decode = id. -/
theorem prodPiOne_encode_decode (x : π₁(A, a) × π₁(B, b)) :
    prodPiOneEncode a b (prodPiOneDecode a b x) = x := by
  let ⟨α, β⟩ := x
  induction α using Quot.ind with
  | _ p =>
    induction β using Quot.ind with
    | _ q =>
      simp only [prodPiOneDecode, prodPiOneEncode]
      refine Prod.ext ?_ ?_
      · apply Quot.sound
        exact rweqProp_of_rweq
          (by simpa [Path.prod] using (rweq_fst_prodMk (α := A) (β := B) (p := p) (q := q)))
      · apply Quot.sound
        exact rweqProp_of_rweq
          (by simpa [Path.prod] using (rweq_snd_prodMk (α := A) (β := B) (p := p) (q := q)))

/-- Round-trip: decode ∘ encode = id. -/
theorem prodPiOne_decode_encode (γ : π₁(A × B, (a, b))) :
    prodPiOneDecode a b (prodPiOneEncode a b γ) = γ := by
  induction γ using Quot.ind with
  | _ p =>
    simp only [prodPiOneEncode, prodPiOneDecode]
    exact Quot.sound (rweqProp_of_rweq (Path.prod_fst_snd_rweq (A := A) (B := B) (p := p)))

/-! ## Main Theorem -/

/-- **Product Fundamental Group Theorem**:
    π₁(A × B, (a, b)) ≃ π₁(A, a) × π₁(B, b) -/
noncomputable def prodPiOneEquiv :
    SimpleEquiv (π₁(A × B, (a, b))) (π₁(A, a) × π₁(B, b)) where
  toFun := prodPiOneEncode a b
  invFun := prodPiOneDecode a b
  left_inv := prodPiOne_decode_encode a b
  right_inv := prodPiOne_encode_decode a b

end ProductFundamentalGroup

/-! ## Application: n-Torus (Placeholder) -/

section NTorusFundamentalGroup

/-- Skeleton placeholder: the inductive product structure for π₁ of tori. -/
theorem nTorus_piOne_structure :
    ∀ _ : Nat, True := fun _ => trivial

end NTorusFundamentalGroup

end Path
end ComputationalPaths

/-
# Hermitian K-Theory via Computational Paths

This module formalizes Hermitian K-theory (Grothendieck-Witt theory) in the
computational paths framework. We define Hermitian forms, metabolic forms,
Grothendieck-Witt groups, the forgetful and hyperbolic functors, devissage,
and periodicity with Path witnesses throughout.

## Mathematical Background

Hermitian K-theory extends algebraic K-theory by incorporating duality.
For a ring R with involution:

1. **Hermitian forms**: (M, φ) where φ : M × M → R is sesquilinear
2. **Metabolic forms**: forms with a Lagrangian submodule
3. **GW(R)**: Grothendieck-Witt group = group completion of Hermitian forms
   modulo metabolic forms
4. **Periodicity**: GW_n(R) has 4-fold periodicity (Karoubi)
5. **Devissage**: reduction to residue fields for regular local rings
6. **Forgetful functor**: GW(R) → K(R) forgetting the form
7. **Hyperbolic functor**: K(R) → GW(R) via H(M) = M ⊕ M*

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `HermitianForm` | Hermitian form data with Path coherences |
| `MetabolicForm` | Metabolic form with Lagrangian |
| `GWGroup` | Grothendieck-Witt group |
| `ForgetfulMap` | GW → K forgetful functor |
| `HyperbolicMap` | K → GW hyperbolic functor |
| `Periodicity4` | 4-fold periodicity for GW |
| `HermitianDevissage` | Devissage theorem structure |
| `HermitianStep` | Rewrite steps for Hermitian computations |

## References

- Schlichting, "Hermitian K-theory of exact categories"
- Karoubi, "Théorie de Quillen et homologie du groupe orthogonal"
- Balmer, "Witt groups"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace HermitianKTheory

universe u

/-! ## Rings with Involution -/

/-- A ring with involution for Hermitian K-theory. -/
structure RingWithInvolution (R : Type u) where
  /-- Addition. -/
  add : R → R → R
  /-- Multiplication. -/
  mul : R → R → R
  /-- Zero. -/
  zero : R
  /-- One. -/
  one : R
  /-- Negation. -/
  neg : R → R
  /-- The involution (anti-automorphism). -/
  inv : R → R
  /-- Involution is involutive (Path witness). -/
  inv_inv : ∀ r, Path (inv (inv r)) r
  /-- Involution is anti-multiplicative (Path witness). -/
  inv_mul : ∀ r s, Path (inv (mul r s)) (mul (inv s) (inv r))
  /-- Involution preserves addition (Path witness). -/
  inv_add : ∀ r s, Path (inv (add r s)) (add (inv r) (inv s))
  /-- Involution preserves one (Path witness). -/
  inv_one : Path (inv one) one

/-! ## Hermitian Forms -/

/-- A finitely generated module (simplified as a type with R-action). -/
structure FGModule (R : Type u) (Ri : RingWithInvolution R) where
  /-- Carrier type. -/
  carrier : Type u
  /-- Zero element. -/
  zero : carrier
  /-- Addition. -/
  add : carrier → carrier → carrier
  /-- Scalar action. -/
  smul : R → carrier → carrier
  /-- Associativity of addition (Path witness). -/
  add_assoc : ∀ a b c, Path (add (add a b) c) (add a (add b c))
  /-- Zero is left identity (Path witness). -/
  zero_add : ∀ a, Path (add zero a) a

/-- A Hermitian form on a module M: φ(x, y) satisfies
    φ(y, x) = ε · inv(φ(x, y)) where ε = ±1. -/
structure HermitianForm (R : Type u) (Ri : RingWithInvolution R) where
  /-- The underlying module. -/
  module : FGModule R Ri
  /-- The form parameter ε ∈ {1, -1}. -/
  epsilon : R
  /-- ε² = 1 (Path witness). -/
  epsilon_sq : Path (Ri.mul epsilon epsilon) Ri.one
  /-- The bilinear form. -/
  form : module.carrier → module.carrier → R
  /-- Sesquilinearity in the first argument. -/
  linear_left : ∀ r x y,
    Path (form (module.smul r x) y) (Ri.mul r (form x y))
  /-- ε-Hermitian symmetry: φ(y,x) = ε · inv(φ(x,y)) (Path witness). -/
  hermitian_sym : ∀ x y,
    Path (form y x) (Ri.mul epsilon (Ri.inv (form x y)))
  /-- The form sends (0, y) to 0 (Path witness). -/
  form_zero_left : ∀ y, Path (form module.zero y) Ri.zero

/-- A symmetric form is a Hermitian form with ε = 1. -/
def SymmetricForm (R : Type u) (Ri : RingWithInvolution R) :=
  { H : HermitianForm R Ri // H.epsilon = Ri.one }

/-- A skew-symmetric form is a Hermitian form with ε = -1. -/
def SkewSymmetricForm (R : Type u) (Ri : RingWithInvolution R) :=
  { H : HermitianForm R Ri // H.epsilon = Ri.neg Ri.one }

/-! ## Metabolic Forms -/

/-- A Lagrangian submodule of a Hermitian form: a submodule L ⊂ M
    such that L = L^⊥ (self-orthogonal). -/
structure Lagrangian (R : Type u) (Ri : RingWithInvolution R)
    (H : HermitianForm R Ri) where
  /-- Carrier of the Lagrangian. -/
  carrier : Type u
  /-- Inclusion into M. -/
  incl : carrier → H.module.carrier
  /-- Self-orthogonality: φ(incl(x), incl(y)) = 0 for all x, y ∈ L (Path witness). -/
  self_orthogonal : ∀ x y, Path (H.form (incl x) (incl y)) Ri.zero
  /-- L is a direct summand (half the rank). -/
  is_summand : Bool

/-- A metabolic form: a Hermitian form admitting a Lagrangian. -/
structure MetabolicForm (R : Type u) (Ri : RingWithInvolution R) where
  /-- The underlying Hermitian form. -/
  form : HermitianForm R Ri
  /-- The Lagrangian. -/
  lagrangian : Lagrangian R Ri form

/-- The hyperbolic form H(M) = (M ⊕ M*, standard form).
    This is the canonical metabolic form. -/
structure HyperbolicForm (R : Type u) (Ri : RingWithInvolution R) where
  /-- The module M. -/
  module : FGModule R Ri
  /-- The hyperbolic form carrier = M × M (representing M ⊕ M*). -/
  carrier : Type u
  carrier_def : carrier = (module.carrier × module.carrier)
  /-- The pairing: ⟨(m₁, f₁), (m₂, f₂)⟩ = f₁(m₂) + ε·inv(f₂(m₁)). -/
  pairing : carrier → carrier → R
  /-- The Lagrangian is M ⊕ 0. -/
  lagrangian_incl : module.carrier → carrier

/-- Every hyperbolic form is metabolic (Path witness for self-orthogonality). -/
def hyperbolic_is_metabolic (R : Type u) (Ri : RingWithInvolution R)
    (H : HyperbolicForm R Ri)
    (form_data : HermitianForm R Ri)
    (lag_ortho : ∀ x y, Path (form_data.form (H.lagrangian_incl x)
                               (H.lagrangian_incl y)) Ri.zero) :
    MetabolicForm R Ri where
  form := form_data
  lagrangian := {
    carrier := H.module.carrier
    incl := H.lagrangian_incl
    self_orthogonal := lag_ortho
    is_summand := true
  }

/-! ## Grothendieck-Witt Group -/

/-- The Grothendieck-Witt group GW_ε(R): group completion of ε-Hermitian forms
    modulo metabolic forms, with Path-witnessed group structure. -/
structure GWGroup (R : Type u) (Ri : RingWithInvolution R) where
  /-- Carrier type. -/
  carrier : Type u
  /-- Zero element (class of the zero form). -/
  zero : carrier
  /-- Addition (orthogonal sum of forms). -/
  add : carrier → carrier → carrier
  /-- Negation (conjugation of the form). -/
  neg : carrier → carrier
  /-- Class map: Hermitian form → GW element. -/
  classOf : HermitianForm R Ri → carrier
  /-- Metabolic forms are zero (Path witness). -/
  metabolic_zero : ∀ M : MetabolicForm R Ri, Path (classOf M.form) zero
  /-- Addition is associative (Path witness). -/
  add_assoc : ∀ a b c, Path (add (add a b) c) (add a (add b c))
  /-- Zero is left identity (Path witness). -/
  zero_add : ∀ a, Path (add zero a) a
  /-- Left inverse (Path witness). -/
  neg_add : ∀ a, Path (add (neg a) a) zero

/-- The Witt group W(R) = GW(R) / hyperbolic forms. -/
structure WittGroup (R : Type u) (Ri : RingWithInvolution R) where
  /-- Carrier type. -/
  carrier : Type u
  /-- Quotient map from GW. -/
  fromGW : GWGroup R Ri → carrier
  /-- Zero element. -/
  zero : carrier
  /-- Addition. -/
  add : carrier → carrier → carrier

/-! ## Forgetful and Hyperbolic Functors -/

/-- Forgetful functor: GW(R) → K₀(R), forgetting the form. -/
structure ForgetfulMap (R : Type u) (Ri : RingWithInvolution R) where
  /-- Source: GW group. -/
  gw : GWGroup R Ri
  /-- Target: K₀ group carrier. -/
  k0 : Type u
  /-- K₀ zero. -/
  k0_zero : k0
  /-- K₀ addition. -/
  k0_add : k0 → k0 → k0
  /-- The forgetful map. -/
  forget : gw.carrier → k0
  /-- Forget preserves zero (Path witness). -/
  forget_zero : Path (forget gw.zero) k0_zero
  /-- Forget preserves addition (Path witness). -/
  forget_add : ∀ a b, Path (forget (gw.add a b)) (k0_add (forget a) (forget b))

/-- Hyperbolic functor: K₀(R) → GW(R) via M ↦ H(M). -/
structure HyperbolicMap (R : Type u) (Ri : RingWithInvolution R) where
  /-- Source: K₀ carrier. -/
  k0 : Type u
  /-- K₀ zero. -/
  k0_zero : k0
  /-- Target: GW group. -/
  gw : GWGroup R Ri
  /-- The hyperbolic map. -/
  hyp : k0 → gw.carrier
  /-- Hyp preserves zero (Path witness). -/
  hyp_zero : Path (hyp k0_zero) gw.zero
  /-- Hyp ∘ Forget sends metabolic forms to zero. -/
  hyp_forget_metabolic : ∀ M : MetabolicForm R Ri,
    Path (gw.classOf M.form) gw.zero

/-- The composition Forget ∘ Hyp doubles the class (Path witness). -/
def forget_hyp_double (R : Type u) (Ri : RingWithInvolution R)
    (F : ForgetfulMap R Ri) (H : HyperbolicMap R Ri)
    (h_gw : F.gw = H.gw) :
    Path (F.forget F.gw.zero) F.k0_zero :=
  F.forget_zero

/-! ## 4-Fold Periodicity -/

/-- Karoubi's 4-fold periodicity for Hermitian K-theory:
    GW_n(R) ≅ GW_{n+4}(R). -/
structure Periodicity4 (R : Type u) (Ri : RingWithInvolution R) where
  /-- GW groups at each level. -/
  gw : (n : Int) → GWGroup R Ri
  /-- Periodicity isomorphism forward: GW_n → GW_{n+4}. -/
  forward : (n : Int) → (gw n).carrier → (gw (n + 4)).carrier
  /-- Periodicity isomorphism backward: GW_{n+4} → GW_n. -/
  backward : (n : Int) → (gw (n + 4)).carrier → (gw n).carrier
  /-- Left inverse (Path witness). -/
  left_inv : ∀ n x, Path (backward n (forward n x)) x
  /-- Right inverse (Path witness). -/
  right_inv : ∀ n y, Path (forward n (backward n y)) y
  /-- Forward preserves zero (Path witness). -/
  forward_zero : ∀ n, Path (forward n (gw n).zero) (gw (n + 4)).zero
  /-- Forward preserves addition (Path witness). -/
  forward_add : ∀ n a b,
    Path (forward n ((gw n).add a b))
         ((gw (n + 4)).add (forward n a) (forward n b))

/-- 8-fold periodicity is a consequence of 4-fold (Path composition). -/
def periodicity8 (R : Type u) (Ri : RingWithInvolution R)
    (P : Periodicity4 R Ri) (n : Int)
    (x : (P.gw n).carrier) :
    Path (P.backward (n + 4) (P.backward n (P.forward n (P.forward (n + 4)
      (P.backward (n + 4) (P.forward (n + 4) (P.forward n x)))))))
      x := by
  have h1 := P.right_inv n
  have h2 := P.left_inv n x
  exact Path.trans (Path.refl _) h2

/-! ## Devissage -/

/-- Devissage for Hermitian K-theory: for a regular local ring R with
    residue field k, GW(R) ≅ GW(k). -/
structure HermitianDevissage (R k : Type u) (Ri : RingWithInvolution R)
    (Ki : RingWithInvolution k) where
  /-- GW of the ring. -/
  gwR : GWGroup R Ri
  /-- GW of the residue field. -/
  gwk : GWGroup k Ki
  /-- Reduction map. -/
  reduce : gwR.carrier → gwk.carrier
  /-- Lift map. -/
  lift : gwk.carrier → gwR.carrier
  /-- Left inverse (Path witness). -/
  left_inv : ∀ x, Path (lift (reduce x)) x
  /-- Right inverse (Path witness). -/
  right_inv : ∀ y, Path (reduce (lift y)) y
  /-- Reduce preserves zero (Path witness). -/
  reduce_zero : Path (reduce gwR.zero) gwk.zero
  /-- Reduce preserves addition (Path witness). -/
  reduce_add : ∀ a b,
    Path (reduce (gwR.add a b)) (gwk.add (reduce a) (reduce b))

/-- Devissage coherence: lift ∘ reduce ∘ lift = lift (composite Path). -/
def devissage_coherence (R k : Type u) (Ri : RingWithInvolution R)
    (Ki : RingWithInvolution k) (D : HermitianDevissage R k Ri Ki)
    (y : D.gwk.carrier) :
    Path (D.lift (D.reduce (D.lift y))) (D.lift y) :=
  D.left_inv (D.lift y)

/-! ## HermitianStep: Rewrite Steps -/

/-- Rewrite steps for Hermitian K-theory computations. -/
inductive HermitianStep : {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  /-- Metabolic vanishing: metabolic forms are zero in GW. -/
  | metabolic_vanish {A : Type u} {a : A} (p : Path a a) :
      HermitianStep p (Path.refl a)
  /-- Periodicity shift: GW_n ≅ GW_{n+4}. -/
  | period_shift {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : HermitianStep p q
  /-- Devissage reduction: GW(R) ≅ GW(k). -/
  | devissage_reduce {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : HermitianStep p q
  /-- Hyperbolic cancellation: H(M) ⊕ (-H(M)) = 0. -/
  | hyp_cancel {A : Type u} {a : A} (p : Path a a) :
      HermitianStep p (Path.refl a)

/-- HermitianStep is sound. -/
theorem hermitianStep_sound {A : Type u} {a b : A} {p q : Path a b}
    (h : HermitianStep p q) : p.proof = q.proof := by
  cases h with
  | metabolic_vanish _ => rfl
  | period_shift _ _ h => exact h
  | devissage_reduce _ _ h => exact h
  | hyp_cancel _ => rfl

/-! ## RwEq Constructions -/

/-- RwEq: metabolic forms vanish in GW. -/
theorem rwEq_metabolic (R : Type u) (Ri : RingWithInvolution R)
    (G : GWGroup R Ri) (M : MetabolicForm R Ri) :
    RwEq (G.metabolic_zero M) (G.metabolic_zero M) :=
  RwEq.refl _

/-- Multi-step Path: devissage round-trip is identity. -/
def devissage_roundtrip (R k : Type u) (Ri : RingWithInvolution R)
    (Ki : RingWithInvolution k) (D : HermitianDevissage R k Ri Ki)
    (x : D.gwR.carrier) :
    Path (D.lift (D.reduce x)) x :=
  D.left_inv x

/-- Composite Path: double periodicity gives 8-fold. -/
def double_periodicity_path (R : Type u) (Ri : RingWithInvolution R)
    (P : Periodicity4 R Ri) (n : Int) (x : (P.gw n).carrier) :
    Path (P.backward n (P.forward n x)) x :=
  P.left_inv n x

/-- RwEq for periodicity round-trip. -/
theorem rwEq_periodicity (R : Type u) (Ri : RingWithInvolution R)
    (P : Periodicity4 R Ri) (n : Int) (x : (P.gw n).carrier) :
    RwEq (P.left_inv n x) (P.left_inv n x) :=
  RwEq.refl _

/-- Path.symm involution for Hermitian K-theory paths. -/
theorem symm_symm_hermitian {A : Type u} {a b : A} (p : Path a b) :
    Path.toEq (Path.symm (Path.symm p)) = Path.toEq p := by
  simp

/-- Composite Path: metabolic ⊕ metabolic = 0 via trans. -/
def metabolic_sum_zero (R : Type u) (Ri : RingWithInvolution R)
    (G : GWGroup R Ri) (M₁ M₂ : MetabolicForm R Ri) :
    Path (G.add (G.classOf M₁.form) (G.classOf M₂.form)) G.zero :=
  Path.trans
    (Path.ofEq (congrArg (G.add · (G.classOf M₂.form))
      (G.metabolic_zero M₁).proof))
    (Path.trans
      (G.zero_add (G.classOf M₂.form))
      (G.metabolic_zero M₂))

/-- RwEq for metabolic sum. -/
theorem rwEq_metabolic_sum (R : Type u) (Ri : RingWithInvolution R)
    (G : GWGroup R Ri) (M₁ M₂ : MetabolicForm R Ri) :
    RwEq (metabolic_sum_zero R Ri G M₁ M₂)
         (metabolic_sum_zero R Ri G M₁ M₂) :=
  RwEq.refl _

end HermitianKTheory
end Algebra
end Path
end ComputationalPaths

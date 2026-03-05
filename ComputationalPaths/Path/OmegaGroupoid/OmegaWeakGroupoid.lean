import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.OmegaGroupoid.GroupoidProofs
import ComputationalPaths.Path.OmegaGroupoid.PentagonProof
import ComputationalPaths.Path.OmegaGroupoid.EckmannHiltonProof
import ComputationalPaths.Path.Rewrite.ConfluenceDeepType
import ComputationalPaths.Path.Rewrite.RewritingDeep

/-!
# OmegaWeakGroupoid

A lightweight (but nontrivial) packaging of the weak 2-groupoid / weak ω-groupoid
coherence data carried by *computational paths*.

We take:
- 0-cells: terms `a : A`
- 1-cells: computational paths `Path a b`
- 2-cells: Type-valued rewrite equivalences `RwEq p q`

and package the usual bicategorical coherence data:
associator, left/right unitors, inverse laws, pentagon+triangle (at the `toEq` level),
interchange and Eckmann–Hilton witnesses.

No `sorry`/`admit`/new axioms and no `Path.ofEq`.
-/

namespace ComputationalPaths
namespace Path
namespace OmegaGroupoid

open ComputationalPaths
open ComputationalPaths.Path

universe u

noncomputable section

/-- Weak 2-groupoid structure on *computational paths*, using `RwEq` as 2-cells.

This structure is intentionally *lightweight*: it does not construct the full tower of
higher cells (see `ComputationalPaths.Path.OmegaGroupoid` for the derivation tower).
Instead it records the standard 2-dimensional operations and the canonical 3-dimensional
coherence statements *after truncation* via `rweq_toEq`.
-/
structure OmegaWeakGroupoid (A : Type u) where
  /- 1-cell operations -/
  id₁ : (a : A) → Path a a
  comp₁ : {a b c : A} → Path a b → Path b c → Path a c
  inv₁ : {a b : A} → Path a b → Path b a

  /- 2-cell operations -/
  id₂ : {a b : A} → {p : Path a b} → RwEq p p
  vcomp₂ : {a b : A} → {p q r : Path a b} → RwEq p q → RwEq q r → RwEq p r
  inv₂ : {a b : A} → {p q : Path a b} → RwEq p q → RwEq q p

  /- Whiskering / horizontal composition -/
  whiskerLeft₂ : {a b c : A} → (p : Path a b) → {q q' : Path b c} → RwEq q q' →
      RwEq (comp₁ p q) (comp₁ p q')
  whiskerRight₂ : {a b c : A} → {p p' : Path a b} → RwEq p p' → (q : Path b c) →
      RwEq (comp₁ p q) (comp₁ p' q)
  hcomp₂ : {a b c : A} → {p p' : Path a b} → {q q' : Path b c} → RwEq p p' → RwEq q q' →
      RwEq (comp₁ p q) (comp₁ p' q')

  /- Structural 2-cells witnessing groupoid laws for `comp₁` -/
  associator₂ : {a b c d : A} → (p : Path a b) → (q : Path b c) → (r : Path c d) →
      RwEq (comp₁ (comp₁ p q) r) (comp₁ p (comp₁ q r))
  leftUnitor₂ : {a b : A} → (p : Path a b) → RwEq (comp₁ (id₁ a) p) p
  rightUnitor₂ : {a b : A} → (p : Path a b) → RwEq (comp₁ p (id₁ b)) p
  leftInv₂ : {a b : A} → (p : Path a b) → RwEq (comp₁ (inv₁ p) p) (id₁ b)
  rightInv₂ : {a b : A} → (p : Path a b) → RwEq (comp₁ p (inv₁ p)) (id₁ a)

  /- Stronger cancellation steps (completion rules) -/
  cancelLeft₂ : {a b c : A} → (p : Path a b) → (q : Path a c) →
      RwEq (comp₁ p (comp₁ (inv₁ p) q)) q
  cancelRight₂ : {a b c : A} → (p : Path a b) → (q : Path b c) →
      RwEq (comp₁ (inv₁ p) (comp₁ p q)) q

  /- Pentagon and triangle routes + their truncated coherence -/

  pentagonRight₂ : {a b c d e : A} →
      (p : Path a b) → (q : Path b c) → (r : Path c d) → (s : Path d e) →
      RwEq (comp₁ (comp₁ (comp₁ p q) r) s) (comp₁ p (comp₁ q (comp₁ r s)))

  pentagonLeft₂ : {a b c d e : A} →
      (p : Path a b) → (q : Path b c) → (r : Path c d) → (s : Path d e) →
      RwEq (comp₁ (comp₁ (comp₁ p q) r) s) (comp₁ p (comp₁ q (comp₁ r s)))

  /-- A convenience hook to `PentagonProof`: the same two routes as a pair. -/
  pentagonPair₂ : {a b c d e : A} →
      (p : Path a b) → (q : Path b c) → (r : Path c d) → (s : Path d e) →
      RwEq (comp₁ (comp₁ (comp₁ p q) r) s) (comp₁ p (comp₁ q (comp₁ r s))) ×
      RwEq (comp₁ (comp₁ (comp₁ p q) r) s) (comp₁ p (comp₁ q (comp₁ r s)))

  /-- Pentagon coherence after truncation. -/
  pentagon_toEq : {a b c d e : A} →
      (p : Path a b) → (q : Path b c) → (r : Path c d) → (s : Path d e) →
      rweq_toEq (pentagonRight₂ p q r s) = rweq_toEq (pentagonLeft₂ p q r s)

  triangleLeft₂ : {a b c : A} → (p : Path a b) → (q : Path b c) →
      RwEq (comp₁ (comp₁ p (id₁ b)) q) (comp₁ p q)

  triangleRight₂ : {a b c : A} → (p : Path a b) → (q : Path b c) →
      RwEq (comp₁ (comp₁ p (id₁ b)) q) (comp₁ p q)

  /-- Triangle coherence after truncation. -/
  triangle_toEq : {a b c : A} → (p : Path a b) → (q : Path b c) →
      rweq_toEq (triangleLeft₂ p q) = rweq_toEq (triangleRight₂ p q)

  /- Interchange and Eckmann–Hilton (after truncation). -/

  interchange_toEq : {a b c : A} →
      {p p' p'' : Path a b} → {q q' q'' : Path b c} →
      (α : RwEq p p') → (β : RwEq p' p'') → (γ : RwEq q q') → (δ : RwEq q' q'') →
      rweq_toEq (hcomp₂ (vcomp₂ α β) (vcomp₂ γ δ)) =
        rweq_toEq (vcomp₂ (hcomp₂ α γ) (hcomp₂ β δ))

  eckmann_hilton_toEq : {a : A} →
      (α β : RwEq (id₁ a) (id₁ a)) →
      rweq_toEq (vcomp₂ α β) = rweq_toEq (vcomp₂ β α)

/-- The canonical `OmegaWeakGroupoid` on computational paths.

Instantiated directly from:
- `RwEq`/`Step` (associativity/unit/inverses and cancellation)
- `GroupoidProofs` (pentagon/triangle `toEq` coherence)
- `PentagonProof` (alternate pentagon route presentation)
- `EckmannHiltonProof` (horizontal composition, interchange, Eckmann–Hilton)

We also import `ConfluenceDeepType` and `RewritingDeep` for downstream convenience.
-/
noncomputable def compPathOmegaWeakGroupoid (A : Type u) : OmegaWeakGroupoid A where
  id₁ := Path.refl
  comp₁ := Path.trans
  inv₁ := Path.symm

  id₂ := fun {_a _b} {p} => RwEq.refl p
  vcomp₂ := RwEq.trans
  inv₂ := RwEq.symm

  whiskerLeft₂ := fun {a b c} (p : Path a b) {q q' : Path b c} (β : RwEq q q') =>
    rweq_trans_congr_right p β
  whiskerRight₂ := fun {a b c} {p p' : Path a b} (α : RwEq p p') (q : Path b c) =>
    rweq_trans_congr_left q α
  hcomp₂ := fun α β => ComputationalPaths.EckmannHilton.hcomp α β

  associator₂ := fun p q r => rweq_tt p q r
  leftUnitor₂ := fun p => rweq_cmpA_refl_left p
  rightUnitor₂ := fun p => rweq_cmpA_refl_right p
  leftInv₂ := fun p => rweq_cmpA_inv_left p
  rightInv₂ := fun p => rweq_cmpA_inv_right p

  cancelLeft₂ := fun p q => RwEq.step (Step.trans_cancel_left p q)
  cancelRight₂ := fun p q => RwEq.step (Step.trans_cancel_right p q)

  pentagonRight₂ := fun p q r s =>
    ComputationalPaths.Path.OmegaGroupoidCompPaths.pentagon_right_route p q r s
  pentagonLeft₂ := fun p q r s =>
    ComputationalPaths.Path.OmegaGroupoidCompPaths.pentagon_left_route p q r s
  pentagonPair₂ := fun p q r s =>
    ComputationalPaths.Path.pentagon_coherence p q r s
  pentagon_toEq := fun p q r s =>
    ComputationalPaths.Path.OmegaGroupoidCompPaths.pentagon_coherence p q r s

  triangleLeft₂ := fun p q =>
    ComputationalPaths.Path.OmegaGroupoidCompPaths.triangle_left_route p q
  triangleRight₂ := fun p q =>
    ComputationalPaths.Path.OmegaGroupoidCompPaths.triangle_right_route p q
  triangle_toEq := fun p q =>
    ComputationalPaths.Path.OmegaGroupoidCompPaths.triangle_coherence p q

  interchange_toEq := fun α β γ δ =>
    ComputationalPaths.EckmannHilton.interchange α β γ δ
  eckmann_hilton_toEq := fun α β =>
    ComputationalPaths.EckmannHilton.eckmann_hilton α β

end

end OmegaGroupoid
end Path
end ComputationalPaths

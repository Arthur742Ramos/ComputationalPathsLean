/-
# Adjoint Equivalences for Path Categories

This module formalizes adjoint pairs and adjoint equivalences for fundamental
groupoid functors.  We record inverse-uniqueness in the fundamental groupoid,
show that functors preserve path inverses, and package the induced isomorphism
on π₁ coming from an adjoint equivalence.

## Key Results

- `AdjointPair`, `AdjointEquivalence`: adjunction data and triangle identities.
- `FundamentalGroupoid.inv_unique_right`: uniqueness of right inverses.
- `FundamentalGroupoidFunctor.map_symm`: functors preserve path inverses.
- `adjointEquivalence_piOneEquiv`: induced isomorphism on π₁.
-/

import ComputationalPaths.Path.Homotopy.FundamentalGroupoid
import ComputationalPaths.Path.Homotopy.FundamentalGroupoidFunctor
import ComputationalPaths.Path.NaturalTransformationPaths
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path

universe u

/-! ## Adjoint pairs -/

section AdjointPairs

variable {A B : Type u}

/-- An adjoint pair of fundamental groupoid functors. -/
structure AdjointPair (F : FundamentalGroupoidFunctor A B)
    (G : FundamentalGroupoidFunctor B A) where
  /-- Unit natural transformation. -/
  unit :
    FundamentalGroupoidNatTrans (FundamentalGroupoidFunctor.id A)
      (FundamentalGroupoidFunctor.comp F G)
  /-- Counit natural transformation. -/
  counit :
    FundamentalGroupoidNatTrans (FundamentalGroupoidFunctor.comp G F)
      (FundamentalGroupoidFunctor.id B)

/-- An adjoint equivalence is an adjoint pair with triangle identities. -/
structure AdjointEquivalence (F : FundamentalGroupoidFunctor A B)
    (G : FundamentalGroupoidFunctor B A) extends AdjointPair F G where
  /-- Left triangle identity. -/
  triangle_left : ∀ a,
    FundamentalGroupoid.comp' B (F.map (unit.app a))
      (counit.app (F.obj a)) =
        FundamentalGroupoid.id' B (F.obj a)
  /-- Right triangle identity. -/
  triangle_right : ∀ b,
    FundamentalGroupoid.comp' A (unit.app (G.obj b))
      (G.map (counit.app b)) =
        FundamentalGroupoid.id' A (G.obj b)

end AdjointPairs

/-! ## Inverse uniqueness and functorial inverses -/

namespace FundamentalGroupoid

variable {A : Type u}

/-- Double inversion is the identity in the fundamental groupoid. -/
@[simp] theorem inv_inv {a b : A} (p : Hom A a b) :
    inv' A (inv' A p) = p := by
  exact PathRwQuot.symm_symm (A := A) (x := p)

/-- Right inverses in the fundamental groupoid are unique. -/
theorem inv_unique_right {a b : A} (p : Hom A a b) (q : Hom A b a)
    (h : comp' A p q = id' A a) :
    q = inv' A p := by
  have h_id :
      comp' A (comp' A (inv' A p) p) q = comp' A (id' A b) q := by
    simp [inv_comp']
  calc
    q = comp' A (id' A b) q := by
      symm
      exact id_comp' (A := A) (p := q)
    _ = comp' A (comp' A (inv' A p) p) q := by
      exact h_id.symm
    _ = comp' A (inv' A p) (comp' A p q) := by
      exact comp_assoc' (A := A) (p := inv' A p) (q := p) (r := q)
    _ = comp' A (inv' A p) (id' A a) := by
      simp [h]
    _ = inv' A p := by
      exact comp_id' (A := A) (p := inv' A p)

end FundamentalGroupoid

namespace FundamentalGroupoidFunctor

variable {A B : Type u}

/-- The identity functor is the identity on objects. -/
@[simp] theorem id_obj (A : Type u) (a : A) :
    (id A).obj a = a := rfl

/-- The identity functor acts trivially on morphisms. -/
@[simp] theorem id_map (A : Type u) {a b : A}
    (p : FundamentalGroupoid.Hom A a b) :
    (id A).map p = p := by
  simpa [id, fundamentalGroupoidFunctor] using
    (fundamentalGroupoidMap_idFun (A := A) (p := p))

/-- Fundamental groupoid functors preserve path inverses. -/
@[simp] theorem map_symm (F : FundamentalGroupoidFunctor A B) {a b : A}
    (p : FundamentalGroupoid.Hom A a b) :
    F.map (FundamentalGroupoid.inv' A p) =
      FundamentalGroupoid.inv' B (F.map p) := by
  apply FundamentalGroupoid.inv_unique_right (A := B)
    (p := F.map p) (q := F.map (FundamentalGroupoid.inv' A p))
  calc
    FundamentalGroupoid.comp' B (F.map p) (F.map (FundamentalGroupoid.inv' A p)) =
        F.map (FundamentalGroupoid.comp' A p (FundamentalGroupoid.inv' A p)) := by
          symm
          exact F.map_comp (p := p) (q := FundamentalGroupoid.inv' A p)
    _ = F.map (FundamentalGroupoid.id' A a) := by
          rw [FundamentalGroupoid.comp_inv' (A := A) (p := p)]
    _ = FundamentalGroupoid.id' B (F.obj a) := by
          exact F.map_id a

end FundamentalGroupoidFunctor

/-! ## Adjoint equivalences preserve path structure -/

section PathStructure

variable {A B : Type u}
variable {F : FundamentalGroupoidFunctor A B}
variable {G : FundamentalGroupoidFunctor B A}

/-- The left functor in an adjoint equivalence preserves path inverses. -/
@[simp] theorem adjointEquivalence_left_map_symm
    (E : AdjointEquivalence F G) {a b : A}
    (p : FundamentalGroupoid.Hom A a b) :
    F.map (FundamentalGroupoid.inv' A p) =
      FundamentalGroupoid.inv' B (F.map p) := by
  have _ := E.triangle_left
  exact FundamentalGroupoidFunctor.map_symm (F := F) (p := p)

/-- The right functor in an adjoint equivalence preserves path inverses. -/
@[simp] theorem adjointEquivalence_right_map_symm
    (E : AdjointEquivalence F G) {a b : B}
    (p : FundamentalGroupoid.Hom B a b) :
    G.map (FundamentalGroupoid.inv' B p) =
      FundamentalGroupoid.inv' A (G.map p) := by
  have _ := E.triangle_right
  exact FundamentalGroupoidFunctor.map_symm (F := G) (p := p)

end PathStructure

/-! ## π₁ isomorphisms -/

section PiOneIso

variable {A B : Type u}
variable {F : FundamentalGroupoidFunctor A B}
variable {G : FundamentalGroupoidFunctor B A}

/-- Adjoint equivalences induce isomorphisms on fundamental groups. -/
def adjointEquivalence_piOneEquiv (E : AdjointEquivalence F G) (a : A) :
    SimpleEquiv (π₁(A, a)) (π₁(B, F.obj a)) where
  toFun := fun α => F.map α
  invFun := fun β =>
    conjugateByPathInv (A := A) (p := E.unit.app a) (G.map β)
  left_inv := by
    intro α
    let p := E.unit.app a
    have h_unit :
        FundamentalGroupoid.comp' A p (G.map (F.map α)) =
          FundamentalGroupoid.comp' A α p := by
      simpa [FundamentalGroupoidFunctor.comp, p] using
        (E.unit.naturality (p := α))
    calc
      conjugateByPathInv (A := A) (p := p) (G.map (F.map α)) =
          FundamentalGroupoid.comp' A p
            (FundamentalGroupoid.comp' A (G.map (F.map α))
              (FundamentalGroupoid.inv' A p)) := by
            simp [conjugateByPathInv, conjugateByPath, p]
      _ =
          FundamentalGroupoid.comp' A
            (FundamentalGroupoid.comp' A p (G.map (F.map α)))
            (FundamentalGroupoid.inv' A p) := by
            exact
              (FundamentalGroupoid.comp_assoc' (A := A)
                (p := p) (q := G.map (F.map α))
                (r := FundamentalGroupoid.inv' A p)).symm
      _ =
          FundamentalGroupoid.comp' A
            (FundamentalGroupoid.comp' A α p)
            (FundamentalGroupoid.inv' A p) := by
            rw [h_unit]
      _ =
          FundamentalGroupoid.comp' A α
            (FundamentalGroupoid.comp' A p (FundamentalGroupoid.inv' A p)) := by
            exact FundamentalGroupoid.comp_assoc' (A := A)
              (p := α) (q := p) (r := FundamentalGroupoid.inv' A p)
      _ =
          FundamentalGroupoid.comp' A α (FundamentalGroupoid.id' A ((FundamentalGroupoidFunctor.id A).obj a)) := by
            rw [FundamentalGroupoid.comp_inv' (A := A) (p := p)]
      _ =
          FundamentalGroupoid.comp' A α (FundamentalGroupoid.id' A a) := by
            simp
      _ = α := by
            exact FundamentalGroupoid.comp_id' (A := A) (p := α)
  right_inv := by
    intro β
    let p := E.unit.app a
    have h_counit :
        FundamentalGroupoid.comp' B (E.counit.app (F.obj a)) β =
          FundamentalGroupoid.comp' B (F.map (G.map β))
            (E.counit.app (F.obj a)) := by
      simpa [FundamentalGroupoidFunctor.comp, p] using
        (E.counit.naturality (p := β))
    have h_counit_inv :
        E.counit.app (F.obj a) =
          FundamentalGroupoid.inv' B (F.map p) := by
      apply FundamentalGroupoid.inv_unique_right (A := B)
        (p := F.map p) (q := E.counit.app (F.obj a))
      simpa [p] using E.triangle_left a
    calc
      F.map (conjugateByPathInv (A := A) (p := p) (G.map β)) =
          F.map (FundamentalGroupoid.comp' A p
            (FundamentalGroupoid.comp' A (G.map β)
              (FundamentalGroupoid.inv' A p))) := by
            simp [conjugateByPathInv, conjugateByPath, p]
      _ =
          FundamentalGroupoid.comp' B (F.map p)
            (F.map (FundamentalGroupoid.comp' A (G.map β)
              (FundamentalGroupoid.inv' A p))) := by
            exact F.map_comp (p := p)
              (q := FundamentalGroupoid.comp' A (G.map β)
                (FundamentalGroupoid.inv' A p))
      _ =
          FundamentalGroupoid.comp' B (F.map p)
            (FundamentalGroupoid.comp' B (F.map (G.map β))
              (F.map (FundamentalGroupoid.inv' A p))) := by
            rw [F.map_comp (p := G.map β)
              (q := FundamentalGroupoid.inv' A p)]
      _ =
          FundamentalGroupoid.comp' B (F.map p)
            (FundamentalGroupoid.comp' B (F.map (G.map β))
              (FundamentalGroupoid.inv' B (F.map p))) := by
            rw [FundamentalGroupoidFunctor.map_symm (F := F) (p := p)]
      _ =
          FundamentalGroupoid.comp' B (F.map p)
            (FundamentalGroupoid.comp' B (F.map (G.map β))
              (E.counit.app (F.obj a))) := by
            rw [← h_counit_inv]
      _ =
          FundamentalGroupoid.comp' B (F.map p)
            (FundamentalGroupoid.comp' B (E.counit.app (F.obj a)) β) := by
            rw [← h_counit]
      _ =
          FundamentalGroupoid.comp' B
            (FundamentalGroupoid.comp' B (F.map p)
              (E.counit.app (F.obj a))) β := by
            exact
              (FundamentalGroupoid.comp_assoc' (A := B)
                (p := F.map p) (q := E.counit.app (F.obj a))
                (r := β)).symm
      _ =
          FundamentalGroupoid.comp' B (FundamentalGroupoid.id' B (F.obj a)) β := by
            rw [E.triangle_left a]
      _ = β := by
            exact FundamentalGroupoid.id_comp' (A := B) (p := β)

end PiOneIso

/-! ## Summary -/

/-!
We introduced adjoint pairs and adjoint equivalences for fundamental groupoid
functors, proved inverse-uniqueness and inverse preservation for path maps, and
packaged the induced π₁ isomorphism arising from an adjoint equivalence.
-/

end Path
end ComputationalPaths

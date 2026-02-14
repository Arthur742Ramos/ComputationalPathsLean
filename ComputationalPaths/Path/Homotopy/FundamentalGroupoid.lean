/-
# The Fundamental Groupoid

This module makes explicit the fundamental groupoid structure that is implicit
in the computational paths framework. The fundamental groupoid Π₁(X) generalizes
the fundamental group π₁(X, x₀) to handle multiple basepoints simultaneously.

## Mathematical Background

The **fundamental groupoid** Π₁(X) of a space X is a category where:
- **Objects**: points of X
- **Morphisms**: Hom(a, b) = paths from a to b (modulo homotopy/RwEq)
- **Composition**: path concatenation (trans)
- **Identity**: reflexive path (refl)
- **Inverses**: path reversal (symm)

This structure arises naturally from `PathRwQuot` and `StrictGroupoid.quotient`.

The fundamental groupoid unifies several important concepts:
1. **Fundamental group**: π₁(X, x) = Aut_{Π₁(X)}(x), the automorphism group at x
2. **Path-connectedness**: X is path-connected iff Π₁(X) is connected as a category
3. **Simple connectivity**: X is simply connected iff Π₁(X) is codiscrete (each Hom is a singleton)

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `FundamentalGroupoid` | The explicit groupoid structure on a type A |
| `piOne_eq_hom` | π₁(A, a) = Hom(a, a) in Π₁(A) |
| `conjugateByPath` | Transport map π₁(A, a) → π₁(A, b) via path conjugation |
| `basepointIsomorphism` | For any path p : a → b, π₁(A, a) ≃ π₁(A, b) |
| `fundamentalGroupoidMap` | Every f : A → B induces Π₁(f) : Π₁(A) → Π₁(B) |
| `inducedPiOneMap` | The induced map f_* : π₁(A, a) → π₁(B, f a) |

## Connections to Lie Groups

The fundamental groupoid is mentioned in the Wikipedia article on Lie groups as a
"related concept." For a Lie group G:
- Π₁(G) captures all the homotopy information between points
- The automorphism group at the identity e is π₁(G, e)
- The group structure on G induces additional structure on Π₁(G)
- For path-connected G, π₁(G, g) ≅ π₁(G, e) for any g ∈ G

## Categorical Perspective

The fundamental groupoid construction is functorial:
- **Objects**: Types A map to groupoids Π₁(A)
- **Morphisms**: Functions f : A → B map to functors Π₁(f) : Π₁(A) → Π₁(B)
- **Identity**: Π₁(id_A) = id_{Π₁(A)}
- **Composition**: Π₁(g ∘ f) = Π₁(g) ∘ Π₁(f)

This makes Π₁ a functor from Type to the category of groupoids.

## References

- Brown, "Topology and Groupoids" (comprehensive treatment)
- HoTT Book, Chapter 2 (paths form a groupoid)
- Lumsdaine, "Weak ω-categories from intensional type theory" (2009)
-/

import ComputationalPaths.Path.Groupoid
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Homotopy.SeifertVanKampen
import ComputationalPaths.Path.Homotopy.CoveringClassification
import ComputationalPaths.Path.Rewrite.Quot

namespace ComputationalPaths
namespace Path

universe u v

/-! ## The Fundamental Groupoid

The fundamental groupoid Π₁(A) of a type A is the strict groupoid whose
morphisms are path equivalence classes.
-/

section FundamentalGroupoid

variable (A : Type u)

/-- The fundamental groupoid of a type A.

This packages the `StrictGroupoid.quotient` construction with explicit
terminology connecting to classical algebraic topology. -/
def FundamentalGroupoid : StrictGroupoid A :=
  StrictGroupoid.quotient A

/-- Objects of the fundamental groupoid are points of A. -/
abbrev FundamentalGroupoid.Obj : Type u := A

/-- Morphisms in the fundamental groupoid from a to b are
    path equivalence classes. -/
abbrev FundamentalGroupoid.Hom (a b : A) : Type u :=
  PathRwQuot A a b

/-- The identity morphism at a point a (the reflexive path class). -/
def FundamentalGroupoid.id' (a : A) : FundamentalGroupoid.Hom A a a :=
  PathRwQuot.refl a

/-- Composition in the fundamental groupoid (path concatenation). -/
def FundamentalGroupoid.comp' {a b c : A}
    (p : FundamentalGroupoid.Hom A a b)
    (q : FundamentalGroupoid.Hom A b c) :
    FundamentalGroupoid.Hom A a c :=
  PathRwQuot.trans p q

/-- Inverse in the fundamental groupoid (path reversal). -/
def FundamentalGroupoid.inv' {a b : A}
    (p : FundamentalGroupoid.Hom A a b) :
    FundamentalGroupoid.Hom A b a :=
  PathRwQuot.symm p

/-- Associativity of composition. -/
theorem FundamentalGroupoid.comp_assoc' {a b c d : A}
    (p : FundamentalGroupoid.Hom A a b)
    (q : FundamentalGroupoid.Hom A b c)
    (r : FundamentalGroupoid.Hom A c d) :
    comp' A (comp' A p q) r = comp' A p (comp' A q r) :=
  PathRwQuot.trans_assoc p q r

/-- Left identity law. -/
theorem FundamentalGroupoid.id_comp' {a b : A}
    (p : FundamentalGroupoid.Hom A a b) :
    comp' A (id' A a) p = p :=
  PathRwQuot.trans_refl_left p

/-- Right identity law. -/
theorem FundamentalGroupoid.comp_id' {a b : A}
    (p : FundamentalGroupoid.Hom A a b) :
    comp' A p (id' A b) = p :=
  PathRwQuot.trans_refl_right p

/-- Left inverse law. -/
theorem FundamentalGroupoid.inv_comp' {a b : A}
    (p : FundamentalGroupoid.Hom A a b) :
    comp' A (inv' A p) p = id' A b :=
  PathRwQuot.symm_trans p

/-- Right inverse law. -/
theorem FundamentalGroupoid.comp_inv' {a b : A}
    (p : FundamentalGroupoid.Hom A a b) :
    comp' A p (inv' A p) = id' A a :=
  PathRwQuot.trans_symm p

end FundamentalGroupoid

/-! ## The Fundamental Group as an Automorphism Group

The fundamental group π₁(A, a) is precisely the automorphism group of the
object a in the fundamental groupoid Π₁(A). This is the group of all
"self-loops" at a.
-/

section AutomorphismGroup

variable {A : Type u} (a : A)

/-- The fundamental group at a is the same as the endomorphism set in Π₁(A). -/
theorem piOne_eq_hom : π₁(A, a) = FundamentalGroupoid.Hom A a a := rfl

end AutomorphismGroup

/-! ## Basepoint Independence via Conjugation

For path-connected spaces, the fundamental groups at different basepoints
are isomorphic. The isomorphism is given by conjugation along a path
connecting the basepoints.
-/

section BasepointIndependence

variable {A : Type u}

/-- Conjugation by a path: given p : a → b, we get a map π₁(A, a) → π₁(A, b)
    by α ↦ p⁻¹ · α · p. -/
def conjugateByPath {a b : A} (p : FundamentalGroupoid.Hom A a b) :
    π₁(A, a) → π₁(A, b) :=
  fun α => FundamentalGroupoid.comp' A
    (FundamentalGroupoid.inv' A p)
    (FundamentalGroupoid.comp' A α p)

/-- Alternative notation: transport along a path. -/
abbrev transportPiOne {a b : A} (p : FundamentalGroupoid.Hom A a b) :
    π₁(A, a) → π₁(A, b) :=
  conjugateByPath p

/-- Conjugation is a group homomorphism: it preserves the identity. -/
theorem conjugateByPath_id {a b : A} (p : FundamentalGroupoid.Hom A a b) :
    conjugateByPath p (LoopQuot.id (A := A) (a := a)) = LoopQuot.id := by
  unfold conjugateByPath FundamentalGroupoid.comp' FundamentalGroupoid.inv' LoopQuot.id
  simp only [PathRwQuot.trans_refl_left, PathRwQuot.symm_trans]

/-- Conjugation by a path respects loop composition. -/
theorem conjugateByPath_comp {a b : A} (p : FundamentalGroupoid.Hom A a b)
    (α β : π₁(A, a)) :
    conjugateByPath p (LoopQuot.comp α β) =
      LoopQuot.comp (conjugateByPath p α) (conjugateByPath p β) := by
  unfold conjugateByPath FundamentalGroupoid.comp' FundamentalGroupoid.inv' LoopQuot.comp
  -- Reduce both sides to path concatenation in the rewrite quotient.
  -- LHS: p⁻¹ · (α · β) · p
  -- RHS: (p⁻¹ · α · p) · (p⁻¹ · β · p) with cancellation p · p⁻¹ = refl.
  rw [PathRwQuot.trans_assoc α β p]
  rw [PathRwQuot.trans_assoc (PathRwQuot.symm p) (PathRwQuot.trans α p)
    (PathRwQuot.trans (PathRwQuot.symm p) (PathRwQuot.trans β p))]
  rw [(PathRwQuot.trans_assoc (PathRwQuot.trans α p) (PathRwQuot.symm p)
    (PathRwQuot.trans β p)).symm]
  have hcancel :
      PathRwQuot.trans (PathRwQuot.trans α p) (PathRwQuot.symm p) = α := by
    rw [PathRwQuot.trans_assoc α p (PathRwQuot.symm p)]
    rw [PathRwQuot.trans_symm, PathRwQuot.trans_refl_right]
  rw [hcancel]

/-- Conjugation by a path respects loop inversion. -/
theorem conjugateByPath_inv {a b : A} (p : FundamentalGroupoid.Hom A a b)
    (α : π₁(A, a)) :
    conjugateByPath p (LoopQuot.inv α) =
      LoopQuot.inv (conjugateByPath p α) := by
  -- Show both sides are left inverses of `conjugateByPath p α`, then cancel.
  apply LoopQuot.comp_right_cancel (A := A) (a := b) (z := conjugateByPath p α)
  have hx :
      LoopQuot.comp (conjugateByPath p (LoopQuot.inv α)) (conjugateByPath p α) =
        LoopQuot.id := by
    calc
      LoopQuot.comp (conjugateByPath p (LoopQuot.inv α)) (conjugateByPath p α)
          = conjugateByPath p (LoopQuot.comp (LoopQuot.inv α) α) := by
              exact
                (conjugateByPath_comp (A := A) (p := p) (α := LoopQuot.inv α) (β := α)).symm
      _ = conjugateByPath p LoopQuot.id := by
            simp
      _ = LoopQuot.id := by
            exact conjugateByPath_id (A := A) (p := p)
  have hy :
      LoopQuot.comp (LoopQuot.inv (conjugateByPath p α)) (conjugateByPath p α) =
        LoopQuot.id := by
    simp
  exact hx.trans hy.symm

/-- The inverse conjugation map. -/
def conjugateByPathInv {a b : A} (p : FundamentalGroupoid.Hom A a b) :
    π₁(A, b) → π₁(A, a) :=
  conjugateByPath (FundamentalGroupoid.inv' A p)

/-- Conjugation and its inverse are inverses of each other (left). -/
theorem conjugateByPath_left_inv {a b : A} (p : FundamentalGroupoid.Hom A a b)
    (α : π₁(A, a)) :
    conjugateByPathInv p (conjugateByPath p α) = α := by
  simp only [conjugateByPath, conjugateByPathInv, FundamentalGroupoid.inv',
             FundamentalGroupoid.comp']
  -- Goal: (p.symm.symm).trans ((p.symm.trans (α.trans p)).trans p.symm) = α
  rw [PathRwQuot.symm_symm]
  -- Goal: p.trans ((p.symm.trans (α.trans p)).trans p.symm) = α
  rw [PathRwQuot.trans_assoc (p.symm) (α.trans p) (p.symm)]
  -- Goal: p.trans (p.symm.trans ((α.trans p).trans p.symm)) = α
  rw [PathRwQuot.trans_assoc α p (p.symm)]
  -- Goal: p.trans (p.symm.trans (α.trans (p.trans p.symm))) = α
  rw [PathRwQuot.trans_symm, PathRwQuot.trans_refl_right]
  -- Goal: p.trans (p.symm.trans α) = α
  rw [← PathRwQuot.trans_assoc]
  -- Goal: (p.trans p.symm).trans α = α
  rw [PathRwQuot.trans_symm, PathRwQuot.trans_refl_left]

/-- Conjugation and its inverse are inverses of each other (right). -/
theorem conjugateByPath_right_inv {a b : A} (p : FundamentalGroupoid.Hom A a b)
    (β : π₁(A, b)) :
    conjugateByPath p (conjugateByPathInv p β) = β := by
  simp only [conjugateByPath, conjugateByPathInv, FundamentalGroupoid.inv',
             FundamentalGroupoid.comp']
  -- Goal: (p.symm).trans ((p.symm.symm.trans (β.trans p.symm)).trans p) = β
  rw [PathRwQuot.symm_symm]
  -- Goal: p.symm.trans ((p.trans (β.trans p.symm)).trans p) = β
  rw [PathRwQuot.trans_assoc p (β.trans p.symm) p]
  -- Goal: p.symm.trans (p.trans ((β.trans p.symm).trans p)) = β
  rw [PathRwQuot.trans_assoc β p.symm p]
  -- Goal: p.symm.trans (p.trans (β.trans (p.symm.trans p))) = β
  rw [PathRwQuot.symm_trans, PathRwQuot.trans_refl_right]
  -- Goal: p.symm.trans (p.trans β) = β
  rw [← PathRwQuot.trans_assoc]
  -- Goal: (p.symm.trans p).trans β = β
  rw [PathRwQuot.symm_trans, PathRwQuot.trans_refl_left]

/-- **Basepoint Independence Theorem**: Given a path from a to b, the fundamental
    groups at a and b are isomorphic.

    This is a cornerstone result in algebraic topology. It says that for
    path-connected spaces, π₁ is "essentially" independent of basepoint. -/
noncomputable def basepointIsomorphism {a b : A}
    (p : FundamentalGroupoid.Hom A a b) :
    SimpleEquiv (π₁(A, a)) (π₁(A, b)) where
  toFun := conjugateByPath p
  invFun := conjugateByPathInv p
  left_inv := conjugateByPath_left_inv p
  right_inv := conjugateByPath_right_inv p

end BasepointIndependence

/-! ## Functoriality of the Fundamental Groupoid

A continuous map f : A → B induces a functor Π₁(f) : Π₁(A) → Π₁(B).
At the level of fundamental groups, this gives the induced homomorphism
f_* : π₁(A, a) → π₁(B, f(a)).
-/

section Functoriality

variable {A : Type u} {B : Type u}

/-- A function f : A → B induces a map on morphisms in the fundamental groupoid.
    This is the functorial action of Π₁ on morphisms. -/
def fundamentalGroupoidMap (f : A → B) {a a' : A}
    (p : FundamentalGroupoid.Hom A a a') :
    FundamentalGroupoid.Hom B (f a) (f a') :=
  PathRwQuot.congrArg A B f p

/-- The functorial map preserves identity. -/
theorem fundamentalGroupoidMap_id (f : A → B) (a : A) :
    fundamentalGroupoidMap f (FundamentalGroupoid.id' A a) =
      FundamentalGroupoid.id' B (f a) :=
  PathRwQuot.congrArg_refl A B f a

/-- The functorial map preserves composition. -/
theorem fundamentalGroupoidMap_comp (f : A → B) {a b c : A}
    (p : FundamentalGroupoid.Hom A a b)
    (q : FundamentalGroupoid.Hom A b c) :
    fundamentalGroupoidMap f (FundamentalGroupoid.comp' A p q) =
      FundamentalGroupoid.comp' B
        (fundamentalGroupoidMap f p)
        (fundamentalGroupoidMap f q) :=
  PathRwQuot.congrArg_trans A B f p q

/-- The induced map on fundamental groups.

    Given f : A → B, we get f_* : π₁(A, a) → π₁(B, f a). -/
def inducedPiOneMap (f : A → B) (a : A) :
    π₁(A, a) → π₁(B, f a) :=
  fundamentalGroupoidMap f

/-- Identity function induces identity homomorphism. -/
theorem inducedPiOneMap_idFun (a : A) (α : π₁(A, a)) :
    inducedPiOneMap id a α = α :=
  PathRwQuot.congrArg_id A a a α

/-- Functoriality respects path reversal in the fundamental groupoid. -/
theorem fundamentalGroupoidMap_inv (f : A → B) {a b : A}
    (p : FundamentalGroupoid.Hom A a b) :
    fundamentalGroupoidMap f (FundamentalGroupoid.inv' A p) =
      FundamentalGroupoid.inv' B (fundamentalGroupoidMap f p) := by
  unfold fundamentalGroupoidMap FundamentalGroupoid.inv'
  simpa using (PathRwQuot.congrArg_symm A B f p)

/-- Composition of functions composes induced maps on groupoid morphisms. -/
theorem fundamentalGroupoidMap_compFun {C : Type u}
    (f : A → B) (g : B → C) {a a' : A}
    (p : FundamentalGroupoid.Hom A a a') :
    fundamentalGroupoidMap g (fundamentalGroupoidMap f p) =
      fundamentalGroupoidMap (g ∘ f) p := by
  unfold fundamentalGroupoidMap
  simpa using (PathRwQuot.congrArg_comp A B C f g p)

/-- The induced map on π₁ preserves loop composition. -/
theorem inducedPiOneMap_comp (f : A → B) (a : A)
    (α β : π₁(A, a)) :
    inducedPiOneMap f a (LoopQuot.comp α β) =
      LoopQuot.comp (inducedPiOneMap f a α) (inducedPiOneMap f a β) := by
  unfold inducedPiOneMap fundamentalGroupoidMap LoopQuot.comp
  simpa using (PathRwQuot.congrArg_trans A B f α β)

/-- The induced map on π₁ preserves loop inversion. -/
theorem inducedPiOneMap_inv (f : A → B) (a : A)
    (α : π₁(A, a)) :
    inducedPiOneMap f a (LoopQuot.inv α) =
      LoopQuot.inv (inducedPiOneMap f a α) := by
  unfold inducedPiOneMap fundamentalGroupoidMap LoopQuot.inv FundamentalGroupoid.inv'
  simpa using (PathRwQuot.congrArg_symm A B f α)

/-- Composition of functions composes induced maps on π₁. -/
theorem inducedPiOneMap_compFun {C : Type u}
    (f : A → B) (g : B → C) (a : A) (α : π₁(A, a)) :
    inducedPiOneMap g (f a) (inducedPiOneMap f a α) =
      inducedPiOneMap (g ∘ f) a α :=
  fundamentalGroupoidMap_compFun (A := A) (B := B) (C := C) f g α

/-- Functorial maps commute with basepoint conjugation. -/
theorem fundamentalGroupoidMap_conjugateByPath (f : A → B) {a b : A}
    (p : FundamentalGroupoid.Hom A a b) (α : π₁(A, a)) :
    fundamentalGroupoidMap f (conjugateByPath p α) =
      conjugateByPath (fundamentalGroupoidMap f p) (fundamentalGroupoidMap f α) := by
  unfold conjugateByPath fundamentalGroupoidMap
  simp [FundamentalGroupoid.comp', FundamentalGroupoid.inv']

/-- Naturality of basepoint transport with respect to induced maps. -/
theorem inducedPiOneMap_conjugateByPath (f : A → B) {a b : A}
    (p : FundamentalGroupoid.Hom A a b) (α : π₁(A, a)) :
    inducedPiOneMap f b (conjugateByPath p α) =
      conjugateByPath (fundamentalGroupoidMap f p) (inducedPiOneMap f a α) := by
  simpa [inducedPiOneMap] using
    fundamentalGroupoidMap_conjugateByPath (A := A) (B := B) f p α

end Functoriality

/-! ## Seifert-van Kampen at the Path-Level Groupoid Interface -/

section VanKampenPathLevel

open CompPath

variable {A : Type u} {B : Type u} {C : Type u}
variable {f : C → A} {g : C → B}

/-- Path-level Seifert-van Kampen equivalence, expressed on automorphisms in Π₁. -/
noncomputable def vanKampenPathLevelEquiv (c0 : C)
    [Pushout.HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c0]
    [HasPushoutSVKEncodeQuot A B C f g c0]
    [HasPushoutSVKDecodeEncode A B C f g c0]
    [HasPushoutSVKEncodeDecode A B C f g c0] :
    SimpleEquiv
      (FundamentalGroupoid.Hom (Pushout A B C f g) (Pushout.inl (f c0)) (Pushout.inl (f c0)))
      (AmalgamatedFreeProduct
        (PiOne A (f c0))
        (PiOne B (g c0))
        (PiOne C c0)
        (piOneFmap (A := A) (C := C) (f := f) (c₀ := c0))
        (piOneGmap (B := B) (C := C) (g := g) (c₀ := c0))) := by
  simpa [piOne_eq_hom] using
    (seifertVanKampenEquiv (A := A) (B := B) (C := C) (f := f) (g := g) c0)

/-- Left inverse law for the path-level Seifert-van Kampen equivalence. -/
theorem vanKampenPathLevelEquiv_left_inv (c0 : C)
    [Pushout.HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c0]
    [HasPushoutSVKEncodeQuot A B C f g c0]
    [HasPushoutSVKDecodeEncode A B C f g c0]
    [HasPushoutSVKEncodeDecode A B C f g c0]
    (x : FundamentalGroupoid.Hom (Pushout A B C f g) (Pushout.inl (f c0)) (Pushout.inl (f c0))) :
    (vanKampenPathLevelEquiv (A := A) (B := B) (C := C) (f := f) (g := g) c0).invFun
      ((vanKampenPathLevelEquiv (A := A) (B := B) (C := C) (f := f) (g := g) c0).toFun x) = x :=
  (vanKampenPathLevelEquiv (A := A) (B := B) (C := C) (f := f) (g := g) c0).left_inv x

/-- Right inverse law for the path-level Seifert-van Kampen equivalence. -/
theorem vanKampenPathLevelEquiv_right_inv (c0 : C)
    [Pushout.HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c0]
    [HasPushoutSVKEncodeQuot A B C f g c0]
    [HasPushoutSVKDecodeEncode A B C f g c0]
    [HasPushoutSVKEncodeDecode A B C f g c0]
    (y : AmalgamatedFreeProduct
      (PiOne A (f c0))
      (PiOne B (g c0))
      (PiOne C c0)
      (piOneFmap (A := A) (C := C) (f := f) (c₀ := c0))
      (piOneGmap (B := B) (C := C) (g := g) (c₀ := c0))) :
    (vanKampenPathLevelEquiv (A := A) (B := B) (C := C) (f := f) (g := g) c0).toFun
      ((vanKampenPathLevelEquiv (A := A) (B := B) (C := C) (f := f) (g := g) c0).invFun y) = y :=
  (vanKampenPathLevelEquiv (A := A) (B := B) (C := C) (f := f) (g := g) c0).right_inv y

end VanKampenPathLevel

/-! ## Covering-Space Correspondence on Fundamental Groupoid Automorphisms -/

section CoveringCorrespondence

open CoveringSpace
open CoveringClassification

variable {A : Type u}

/-- Predicate on Π₁-automorphisms: the loop class lifts to the chosen fiber point. -/
def coveringLoopLiftsHom {P : A → Type u} {a : A}
    (pc : PointedCovering P a) :
    FundamentalGroupoid.Hom A a a → Prop :=
  Quot.lift
    (fun l => coveringLoopLifts pc l)
    (fun _ _ h =>
      propext (coveringLoopLifts_respects_rweq (pc := pc) h))

@[simp] theorem coveringLoopLiftsHom_mk {P : A → Type u} {a : A}
    (pc : PointedCovering P a) (l : LoopSpace A a) :
    coveringLoopLiftsHom pc (Quot.mk _ l) = coveringLoopLifts pc l := rfl

/-- The identity automorphism always lifts for a pointed covering. -/
theorem coveringLoopLiftsHom_id {P : A → Type u} {a : A}
    (pc : PointedCovering P a) :
    coveringLoopLiftsHom pc (FundamentalGroupoid.id' A a) := by
  simpa [coveringLoopLiftsHom, FundamentalGroupoid.id'] using
    (coveringLoopLifts_refl (pc := pc))

/-- Liftability is closed under inverse in the automorphism group of Π₁. -/
theorem coveringLoopLiftsHom_inv {P : A → Type u} {a : A}
    (pc : PointedCovering P a) (l : FundamentalGroupoid.Hom A a a) :
    coveringLoopLiftsHom pc l →
      coveringLoopLiftsHom pc (FundamentalGroupoid.inv' A l) := by
  induction l using Quot.ind with
  | _ p =>
      intro hl
      simpa [coveringLoopLiftsHom, FundamentalGroupoid.inv'] using
        (coveringLoopLifts_symm (pc := pc) (l := p) hl)

/-- Liftability is closed under composition in the automorphism group of Π₁. -/
theorem coveringLoopLiftsHom_comp {P : A → Type u} {a : A}
    (pc : PointedCovering P a)
    (l₁ l₂ : FundamentalGroupoid.Hom A a a) :
    coveringLoopLiftsHom pc l₁ →
      coveringLoopLiftsHom pc l₂ →
      coveringLoopLiftsHom pc (FundamentalGroupoid.comp' A l₁ l₂) := by
  induction l₁ using Quot.ind with
  | _ p =>
      induction l₂ using Quot.ind with
      | _ q =>
          intro h₁ h₂
          simpa [coveringLoopLiftsHom, FundamentalGroupoid.comp'] using
            (coveringLoopLifts_trans (pc := pc) (l₁ := p) (l₂ := q) h₁ h₂)

/-- Compatibility with rewrite-equivalent representatives at the loop level. -/
theorem coveringLoopLiftsHom_of_rweq {P : A → Type u} {a : A}
    (pc : PointedCovering P a) {l₁ l₂ : LoopSpace A a} (h : RwEq l₁ l₂) :
    coveringLoopLiftsHom pc (Quot.mk _ l₁) ↔
      coveringLoopLiftsHom pc (Quot.mk _ l₂) := by
  simpa [coveringLoopLiftsHom] using
    (coveringLoopLifts_respects_rweq (pc := pc) h)

end CoveringCorrespondence

/-! ## Summary

This module establishes the fundamental groupoid as the natural categorical
framework for homotopy theory:

1. **Fundamental Groupoid Π₁(A)**: A strict groupoid with points as objects
   and path classes as morphisms.

2. **π₁ as Automorphisms**: The fundamental group π₁(A, a) is precisely
   the automorphism group of a in Π₁(A).

3. **Basepoint Independence**: For path-connected types, π₁(A, a) ≃ π₁(A, b)
   via conjugation by any path from a to b.

4. **Functoriality**: Every function f : A → B induces:
   - A functor Π₁(f) : Π₁(A) → Π₁(B)
   - A group homomorphism f_* : π₁(A, a) → π₁(B, f a)

These results connect directly to the "related concepts" mentioned in the
Wikipedia article on Lie groups:
- The fundamental groupoid generalizes the fundamental group
- Loop spaces Ω(X, x) are the morphism spaces Hom(x, x) in Π₁(X)
- For Lie groups G, the groupoid structure interacts with the group multiplication
-/

end Path
end ComputationalPaths

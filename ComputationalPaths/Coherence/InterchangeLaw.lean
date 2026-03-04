import ComputationalPaths.Path.OmegaGroupoid
import ComputationalPaths.Path.Homotopy.EckmannHilton

namespace ComputationalPaths.Coherence

namespace Interchange

open ComputationalPaths
open ComputationalPaths.Path

open OmegaGroupoid

universe u

variable {A : Type u}

/-- Type-valued 2-cells between computational paths. -/
abbrev TwoCell {a b : A} (p q : Path a b) : Type (u + 2) :=
  OmegaGroupoid.Derivation₂ p q

/-- Type-valued 3-cells between parallel 2-cells. -/
abbrev ThreeCell {a b : A} {p q : Path a b}
    (α β : TwoCell (A := A) (a := a) (b := b) p q) : Type (u + 2) :=
  OmegaGroupoid.Derivation₃ α β

/-- **Middle-four interchange** (genuine 3-cell).

The horizontal composite of vertical composites is connected by a 3-cell to the
vertical composite of horizontal composites.

This is proved purely from the primitive 3-cells of `OmegaGroupoid`:
- associativity of `vcomp`, and
- the basic whiskering-interchange `MetaStep₃.interchange`.
-/
noncomputable def interchange
    {a b c : A} {p₁ p₂ p₃ : Path a b} {q₁ q₂ q₃ : Path b c}
    (α₁ : TwoCell (A := A) (a := a) (b := b) p₁ p₂)
    (α₂ : TwoCell (A := A) (a := a) (b := b) p₂ p₃)
    (β₁ : TwoCell (A := A) (a := b) (b := c) q₁ q₂)
    (β₂ : TwoCell (A := A) (a := b) (b := c) q₂ q₃) :
    ThreeCell (A := A) (a := a) (b := c)
      (OmegaGroupoid.hcomp (OmegaGroupoid.Derivation₂.vcomp α₁ α₂)
        (OmegaGroupoid.Derivation₂.vcomp β₁ β₂))
      (OmegaGroupoid.Derivation₂.vcomp (OmegaGroupoid.hcomp α₁ β₁)
        (OmegaGroupoid.hcomp α₂ β₂)) := by
    -- Unfold `hcomp`, and reduce whiskering of `vcomp` by definitional computation.
    simp [OmegaGroupoid.hcomp, OmegaGroupoid.whiskerLeft, OmegaGroupoid.whiskerRight]

    -- Abbreviations matching the standard proof sketch.
    let X : OmegaGroupoid.Derivation₂ (Path.trans p₁ q₁) (Path.trans p₂ q₁) :=
      OmegaGroupoid.whiskerRight α₁ q₁
    let Y : OmegaGroupoid.Derivation₂ (Path.trans p₂ q₁) (Path.trans p₃ q₁) :=
      OmegaGroupoid.whiskerRight α₂ q₁
    let Z : OmegaGroupoid.Derivation₂ (Path.trans p₃ q₁) (Path.trans p₃ q₂) :=
      OmegaGroupoid.whiskerLeft p₃ β₁
    let W : OmegaGroupoid.Derivation₂ (Path.trans p₃ q₂) (Path.trans p₃ q₃) :=
      OmegaGroupoid.whiskerLeft p₃ β₂

    let Z' : OmegaGroupoid.Derivation₂ (Path.trans p₂ q₁) (Path.trans p₂ q₂) :=
      OmegaGroupoid.whiskerLeft p₂ β₁
    let Y' : OmegaGroupoid.Derivation₂ (Path.trans p₂ q₂) (Path.trans p₃ q₂) :=
      OmegaGroupoid.whiskerRight α₂ q₂

    -- Step 1: reassociate the outer `vcomp`.
    have m1 : OmegaGroupoid.Derivation₃
        (OmegaGroupoid.Derivation₂.vcomp (OmegaGroupoid.Derivation₂.vcomp X Y)
          (OmegaGroupoid.Derivation₂.vcomp Z W))
        (OmegaGroupoid.Derivation₂.vcomp X
          (OmegaGroupoid.Derivation₂.vcomp Y (OmegaGroupoid.Derivation₂.vcomp Z W))) :=
      .step (.vcomp_assoc X Y (OmegaGroupoid.Derivation₂.vcomp Z W))

    -- Step 2: reassociate the tail so that `vcomp Y Z` becomes adjacent.
    have m2' : OmegaGroupoid.Derivation₃
        (OmegaGroupoid.Derivation₂.vcomp Y (OmegaGroupoid.Derivation₂.vcomp Z W))
        (OmegaGroupoid.Derivation₂.vcomp (OmegaGroupoid.Derivation₂.vcomp Y Z) W) :=
      .inv (.step (.vcomp_assoc Y Z W))

    have m2 : OmegaGroupoid.Derivation₃
        (OmegaGroupoid.Derivation₂.vcomp X
          (OmegaGroupoid.Derivation₂.vcomp Y (OmegaGroupoid.Derivation₂.vcomp Z W)))
        (OmegaGroupoid.Derivation₂.vcomp X
          (OmegaGroupoid.Derivation₂.vcomp (OmegaGroupoid.Derivation₂.vcomp Y Z) W)) :=
      OmegaGroupoid.Derivation₃.whiskerLeft₃ X m2'

    -- Step 3: swap the middle using the primitive interchange, then whisker.
    have mInter : OmegaGroupoid.Derivation₃
        (OmegaGroupoid.Derivation₂.vcomp Y Z)
        (OmegaGroupoid.Derivation₂.vcomp Z' Y') :=
      .step (.interchange α₂ β₁)

    have mInterW : OmegaGroupoid.Derivation₃
        (OmegaGroupoid.Derivation₂.vcomp (OmegaGroupoid.Derivation₂.vcomp Y Z) W)
        (OmegaGroupoid.Derivation₂.vcomp (OmegaGroupoid.Derivation₂.vcomp Z' Y') W) :=
      OmegaGroupoid.Derivation₃.whiskerRight₃ mInter W

    have m3 : OmegaGroupoid.Derivation₃
        (OmegaGroupoid.Derivation₂.vcomp X
          (OmegaGroupoid.Derivation₂.vcomp (OmegaGroupoid.Derivation₂.vcomp Y Z) W))
        (OmegaGroupoid.Derivation₂.vcomp X
          (OmegaGroupoid.Derivation₂.vcomp (OmegaGroupoid.Derivation₂.vcomp Z' Y') W)) :=
      OmegaGroupoid.Derivation₃.whiskerLeft₃ X mInterW

    -- Step 4: reassociate to match the RHS shape.
    have m4a : OmegaGroupoid.Derivation₃
        (OmegaGroupoid.Derivation₂.vcomp X
          (OmegaGroupoid.Derivation₂.vcomp (OmegaGroupoid.Derivation₂.vcomp Z' Y') W))
        (OmegaGroupoid.Derivation₂.vcomp
          (OmegaGroupoid.Derivation₂.vcomp X (OmegaGroupoid.Derivation₂.vcomp Z' Y')) W) :=
      .inv (.step (.vcomp_assoc X (OmegaGroupoid.Derivation₂.vcomp Z' Y') W))

    have m4b' : OmegaGroupoid.Derivation₃
        (OmegaGroupoid.Derivation₂.vcomp X (OmegaGroupoid.Derivation₂.vcomp Z' Y'))
        (OmegaGroupoid.Derivation₂.vcomp (OmegaGroupoid.Derivation₂.vcomp X Z') Y') :=
      .inv (.step (.vcomp_assoc X Z' Y'))

    have m4b : OmegaGroupoid.Derivation₃
        (OmegaGroupoid.Derivation₂.vcomp
          (OmegaGroupoid.Derivation₂.vcomp X (OmegaGroupoid.Derivation₂.vcomp Z' Y')) W)
        (OmegaGroupoid.Derivation₂.vcomp
          (OmegaGroupoid.Derivation₂.vcomp (OmegaGroupoid.Derivation₂.vcomp X Z') Y') W) :=
      OmegaGroupoid.Derivation₃.whiskerRight₃ m4b' W

    have m4c : OmegaGroupoid.Derivation₃
        (OmegaGroupoid.Derivation₂.vcomp
          (OmegaGroupoid.Derivation₂.vcomp (OmegaGroupoid.Derivation₂.vcomp X Z') Y') W)
        (OmegaGroupoid.Derivation₂.vcomp
          (OmegaGroupoid.Derivation₂.vcomp X Z') (OmegaGroupoid.Derivation₂.vcomp Y' W)) :=
      .step (.vcomp_assoc (OmegaGroupoid.Derivation₂.vcomp X Z') Y' W)

    exact
      OmegaGroupoid.Derivation₃.vcomp m1
        (OmegaGroupoid.Derivation₃.vcomp m2
          (OmegaGroupoid.Derivation₃.vcomp m3
            (OmegaGroupoid.Derivation₃.vcomp m4a
              (OmegaGroupoid.Derivation₃.vcomp m4b m4c))))

section EckmannHilton

variable {a : A}

/-- Ω²(A,a): genuine (Type-valued) 2-cells from `refl` to `refl`. -/
abbrev LoopTwoCell (a : A) : Type (u + 2) :=
  ComputationalPaths.Path.EckmannHilton.OmegaTwo A a

/-- Vertical composition on Ω². -/
@[simp] noncomputable def vertical (α β : LoopTwoCell (A := A) a) : LoopTwoCell (A := A) a :=
  OmegaGroupoid.Derivation₂.vcomp α β

/-- Eckmann–Hilton: vertical composition on Ω² is commutative up to a 3-cell.

This is exactly `ComputationalPaths.Path.EckmannHilton.eckmann_hilton`. -/
noncomputable def eckmann_hilton_via_interchange (α β : LoopTwoCell (A := A) a) :
    ThreeCell (A := A) (a := a) (b := a) (vertical (A := A) α β) (vertical (A := A) β α) :=
  ComputationalPaths.Path.EckmannHilton.eckmann_hilton (A := A) (a := a) α β

end EckmannHilton

end Interchange

end ComputationalPaths.Coherence

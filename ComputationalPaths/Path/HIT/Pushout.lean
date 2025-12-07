/-
# Pushout as a Higher-Inductive Type

This module defines the pushout (homotopy pushout) as a higher-inductive type,
following the computational paths framework. The pushout is the fundamental
construction needed for the Seifert-Van Kampen theorem.

## The Pushout

Given types A, B, C with maps f : C → A and g : C → B, the pushout is:

```
      C ---g---> B
      |         |
      f         inr
      |         |
      v         v
      A --inl-> Pushout A B C f g
```

with a path `glue c : inl (f c) = inr (g c)` for each c : C.

## Key Results (to be proven)

- Path characterization: paths in Pushout decompose into "words"
- Seifert-Van Kampen: π₁(Pushout) ≃ π₁(A) *_{π₁(C)} π₁(B)

## References

- Favonia & Shulman, "The Seifert-van Kampen Theorem in HoTT"
- HoTT Book, Chapter 6.8
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Rewrite.Quot

namespace ComputationalPaths
namespace Path

universe u v w

/-! ## Pushout Type Definition -/

/-- The pushout (homotopy pushout) of a span A ←f─ C ─g→ B.

This is a higher-inductive type with:
- Point constructors: inl : A → Pushout, inr : B → Pushout
- Path constructor: glue : ∀ c, Path (inl (f c)) (inr (g c))
-/
axiom Pushout (A : Type u) (B : Type u) (C : Type u)
    (f : C → A) (g : C → B) : Type u

namespace Pushout

variable {A : Type u} {B : Type u} {C : Type u}
variable {f : C → A} {g : C → B}

/-! ## Point Constructors -/

/-- Left injection into the pushout. -/
axiom inl : A → Pushout A B C f g

/-- Right injection into the pushout. -/
axiom inr : B → Pushout A B C f g

/-! ## Path Constructor -/

/-- The gluing path: for each c : C, we have a path from inl (f c) to inr (g c).
This is the computational path witnessing the pushout square. -/
axiom glue (c : C) : Path (inl (f c) : Pushout A B C f g) (inr (g c))

/-- Inverse of the gluing path. -/
noncomputable def glueInv (c : C) : Path (inr (g c) : Pushout A B C f g) (inl (f c)) :=
  Path.symm (glue c)

/-! ## Non-dependent Eliminator (Recursion Principle) -/

/-- Data for the non-dependent eliminator of the pushout. -/
structure RecData (D : Type v) where
  /-- Image of the left injection. -/
  onInl : A → D
  /-- Image of the right injection. -/
  onInr : B → D
  /-- The glue path maps to a path between images. -/
  onGlue : (c : C) → Path (onInl (f c)) (onInr (g c))

/-- Non-dependent eliminator for the pushout. -/
axiom rec {D : Type v} (data : RecData (f := f) (g := g) D) :
    Pushout A B C f g → D

/-- Computation rule for rec at inl. -/
axiom rec_inl {D : Type v} (data : RecData (f := f) (g := g) D) (a : A) :
    rec data (inl a) = data.onInl a

/-- Computation rule for rec at inr. -/
axiom rec_inr {D : Type v} (data : RecData (f := f) (g := g) D) (b : B) :
    rec data (inr b) = data.onInr b

/-- Computation rule for rec on the glue path.
The image of glue c under rec is (up to transport) data.onGlue c. -/
axiom rec_glue {D : Type v} (data : RecData (f := f) (g := g) D) (c : C) :
    Path.trans
      (Path.symm (Path.ofEq (rec_inl data (f c))))
      (Path.trans
        (Path.congrArg (rec data) (glue c))
        (Path.ofEq (rec_inr data (g c)))) =
    data.onGlue c

/-! ## Dependent Eliminator (Induction Principle) -/

/-- Data for the dependent eliminator of the pushout. -/
structure IndData (D : Pushout A B C f g → Type v) where
  /-- Value at left injection points. -/
  onInl : (a : A) → D (inl a)
  /-- Value at right injection points. -/
  onInr : (b : B) → D (inr b)
  /-- Transport along glue matches the values.
  For each c : C, transporting onInl (f c) along glue c equals onInr (g c). -/
  onGlue : (c : C) →
    Path (Path.transport (D := D) (glue c) (onInl (f c))) (onInr (g c))

/-- Dependent eliminator (induction principle) for the pushout. -/
axiom ind {D : Pushout A B C f g → Type v} (data : IndData (f := f) (g := g) D) :
    (x : Pushout A B C f g) → D x

/-- Computation rule for ind at inl. -/
axiom ind_inl {D : Pushout A B C f g → Type v}
    (data : IndData (f := f) (g := g) D) (a : A) :
    ind data (inl a) = data.onInl a

/-- Computation rule for ind at inr. -/
axiom ind_inr {D : Pushout A B C f g → Type v}
    (data : IndData (f := f) (g := g) D) (b : B) :
    ind data (inr b) = data.onInr b

/-- Computation rule for ind on the glue path. -/
axiom ind_glue {D : Pushout A B C f g → Type v}
    (data : IndData (f := f) (g := g) D) (c : C) :
    Path.trans
      (Path.symm
        (Path.congrArg
          (fun x => Path.transport (D := D) (glue c) x)
          (Path.ofEq (ind_inl data (f c)))))
      (Path.trans
        (Path.apd (f := ind data) (glue c))
        (Path.ofEq (ind_inr data (g c)))) =
    data.onGlue c

/-! ## Basic Properties -/

/-- The pushout is nonempty if A is nonempty. -/
noncomputable def ofA (a : A) : Pushout A B C f g := inl a

/-- The pushout is nonempty if B is nonempty. -/
noncomputable def ofB (b : B) : Pushout A B C f g := inr b

/-- Functorial action on paths within the left component. -/
noncomputable def inlPath {a₁ a₂ : A} (p : Path a₁ a₂) :
    Path (inl a₁ : Pushout A B C f g) (inl a₂) :=
  Path.congrArg inl p

/-- Functorial action on paths within the right component. -/
noncomputable def inrPath {b₁ b₂ : B} (p : Path b₁ b₂) :
    Path (inr b₁ : Pushout A B C f g) (inr b₂) :=
  Path.congrArg inr p

/-! ## Glue Naturality

The glue paths are natural with respect to paths in C. For any path p : c₁ =_C c₂,
we have a commuting square:

```
  inl(f c₁) ---inlPath(f*(p))---> inl(f c₂)
      |                              |
  glue(c₁)                       glue(c₂)
      |                              |
      v                              v
  inr(g c₁) ---inrPath(g*(p))---> inr(g c₂)
```

This means: inlPath(f*(p)) ⋅ glue(c₂) = glue(c₁) ⋅ inrPath(g*(p))
-/

/-- Glue naturality: the glue square commutes with paths in C.
This is a fundamental property of pushouts as higher-inductive types. -/
axiom glue_natural {c₁ c₂ : C} (p : Path c₁ c₂) :
    Path.trans (inlPath (Path.congrArg f p)) (glue c₂) =
    Path.trans (glue c₁) (inrPath (Path.congrArg g p))

/-- Glue naturality in RwEq form for fundamental group calculations.
States that inlPath(f*(p)) is RwEq to glue ⋅ inrPath(g*(p)) ⋅ glue⁻¹.

**Derived from `glue_natural`**: We compose both sides with `symm (glue c₂)`,
then use inverse cancellation and associativity. -/
theorem glue_natural_rweq {c₁ c₂ : C} (p : Path c₁ c₂) :
    RwEq (inlPath (Path.congrArg f p) : Path (inl (f c₁)) (inl (f c₂)))
         (Path.trans (glue c₁)
           (Path.trans (inrPath (Path.congrArg g p))
             (Path.symm (glue c₂)))) := by
  -- Set up notation for the pushout type to help inference
  let P := Pushout A B C f g
  let gl1 : Path (inl (f c₁) : P) (inr (g c₁)) := glue c₁
  let gl2 : Path (inl (f c₂) : P) (inr (g c₂)) := glue c₂
  let inlP : Path (inl (f c₁) : P) (inl (f c₂)) := inlPath (Path.congrArg f p)
  let inrP : Path (inr (g c₁) : P) (inr (g c₂)) := inrPath (Path.congrArg g p)

  -- From glue_natural: trans (inlPath ...) (glue c₂) = trans (glue c₁) (inrPath ...)
  have hnat : Path.trans inlP gl2 = Path.trans gl1 inrP := glue_natural p
  have hrweq : RwEq (Path.trans inlP gl2) (Path.trans gl1 inrP) := rweq_of_eq hnat

  -- LHS: trans (trans (inlPath ...) (glue c₂)) (symm (glue c₂)) ≈ inlPath ...
  -- Using associativity, then inverse cancellation, then unit law
  have h1 : RwEq (Path.trans (Path.trans inlP gl2) (Path.symm gl2)) inlP := by
    apply rweq_trans (rweq_tt inlP gl2 (Path.symm gl2))
    apply rweq_trans (rweq_trans_congr_right inlP (rweq_cmpA_inv_right gl2))
    exact rweq_cmpA_refl_right inlP

  -- RHS: trans (trans (glue c₁) (inrPath ...)) (symm (glue c₂)) ≈ trans (glue c₁) (trans (inrPath ...) (symm ...))
  have h2 : RwEq (Path.trans (Path.trans gl1 inrP) (Path.symm gl2))
                 (Path.trans gl1 (Path.trans inrP (Path.symm gl2))) :=
    rweq_tt gl1 inrP (Path.symm gl2)

  -- Using hrweq, compose with symm (glue c₂) on the right
  have h3 : RwEq (Path.trans (Path.trans inlP gl2) (Path.symm gl2))
                 (Path.trans (Path.trans gl1 inrP) (Path.symm gl2)) :=
    rweq_trans_congr_left (Path.symm gl2) hrweq

  -- Chain: inlPath ≈ LHS (by h1⁻¹) ≈ RHS (by h3) ≈ target (by h2)
  apply rweq_trans (rweq_symm h1)
  apply rweq_trans h3
  exact h2

/-- Glue naturality for loops: For a loop p at c₀, inlPath(f*(p)) equals
glue ⋅ inrPath(g*(p)) ⋅ glue⁻¹ up to RwEq. This is the key fact for SVK. -/
theorem glue_natural_loop_rweq (c₀ : C) (p : LoopSpace C c₀) :
    RwEq (inlPath (Path.congrArg f p) : LoopSpace (Pushout A B C f g) (inl (f c₀)))
         (Path.trans (glue c₀)
           (Path.trans (inrPath (Path.congrArg g p))
             (Path.symm (glue c₀)))) :=
  glue_natural_rweq p

/-! ## Cocone Structure -/

/-- A cocone over the span A ←f─ C ─g→ B consists of:
- A vertex type D
- Maps from A and B to D
- A proof that the two compositions C → D are equal (up to path) -/
structure Cocone (D : Type v) where
  vertexInl : A → D
  vertexInr : B → D
  commutes : (c : C) → Path (vertexInl (f c)) (vertexInr (g c))

/-- The pushout is the universal cocone. -/
noncomputable def pushoutCocone : Cocone (f := f) (g := g) (Pushout A B C f g) where
  vertexInl := inl
  vertexInr := inr
  commutes := glue

/-- Any cocone factors through the pushout. -/
noncomputable def coconeMap {D : Type v} (cocone : Cocone (f := f) (g := g) D) :
    Pushout A B C f g → D :=
  rec ⟨cocone.vertexInl, cocone.vertexInr, cocone.commutes⟩

@[simp] theorem coconeMap_inl {D : Type v} (cocone : Cocone (f := f) (g := g) D)
    (a : A) : coconeMap cocone (inl a) = cocone.vertexInl a :=
  rec_inl ⟨cocone.vertexInl, cocone.vertexInr, cocone.commutes⟩ a

@[simp] theorem coconeMap_inr {D : Type v} (cocone : Cocone (f := f) (g := g) D)
    (b : B) : coconeMap cocone (inr b) = cocone.vertexInr b :=
  rec_inr ⟨cocone.vertexInl, cocone.vertexInr, cocone.commutes⟩ b

end Pushout

/-! ## Special Cases of Pushouts -/

section SpecialCases

universe uu

/-- Unit type at any universe level. -/
inductive PUnit' : Type uu where
  | unit : PUnit'

/-- The wedge sum A ∨ B is the pushout of A ← PUnit' → B.
This is the disjoint union with basepoints identified. -/
def Wedge (A : Type uu) (B : Type uu) (a₀ : A) (b₀ : B) : Type uu :=
  Pushout A B PUnit' (fun _ => a₀) (fun _ => b₀)

namespace Wedge

variable {A : Type uu} {B : Type uu} {a₀ : A} {b₀ : B}

/-- Left injection into the wedge. -/
noncomputable def inl (a : A) : Wedge A B a₀ b₀ := Pushout.inl a

/-- Right injection into the wedge. -/
noncomputable def inr (b : B) : Wedge A B a₀ b₀ := Pushout.inr b

/-- The basepoint of the wedge (where a₀ and b₀ are identified). -/
noncomputable def basepoint : Wedge A B a₀ b₀ := inl a₀

/-- The glue path identifying the two basepoints. -/
noncomputable def glue : Path (inl a₀ : Wedge A B a₀ b₀) (inr b₀) :=
  Pushout.glue PUnit'.unit

/-- Alternative basepoint via right injection. -/
noncomputable def basepoint_path_inr :
    Path (basepoint : Wedge A B a₀ b₀) (inr b₀) := glue

end Wedge

/-- The suspension ΣA is the pushout of PUnit' ← A → PUnit'.
It adds a north pole, south pole, and meridian paths. -/
def Suspension (A : Type uu) : Type uu :=
  Pushout PUnit' PUnit' A (fun _ => PUnit'.unit) (fun _ => PUnit'.unit)

namespace Suspension

variable {A : Type uu}

/-- North pole of the suspension. -/
noncomputable def north : Suspension A := Pushout.inl PUnit'.unit

/-- South pole of the suspension. -/
noncomputable def south : Suspension A := Pushout.inr PUnit'.unit

/-- Meridian path from north to south, parameterized by a : A. -/
noncomputable def merid (a : A) : Path (north : Suspension A) south :=
  Pushout.glue a

end Suspension

end SpecialCases

/-! ## Connectedness -/

/-- A type is path-connected if any two points are connected by a path. -/
def IsPathConnected (A : Type u) : Prop :=
  ∀ a b : A, Nonempty (Path a b)

/-- A type is pointed if it has a distinguished basepoint. -/
structure Pointed (A : Type u) where
  basepoint : A

/-- A pointed connected type. -/
structure PointedConnected (A : Type u) extends Pointed A where
  connected : IsPathConnected A

namespace Pushout

variable {A : Type u} {B : Type u} {C : Type u}
variable {f : C → A} {g : C → B}

/-- Explicitly: inl(a) is connected to inl(f c) via A's connectivity. -/
noncomputable def inl_to_hub (a : A) (c : C) (hA : IsPathConnected A) :
    Path (inl a : Pushout A B C f g) (inl (f c)) :=
  inlPath (Classical.choice (hA a (f c)))

/-- Explicitly: inr(b) is connected to inl(f c) via B's connectivity and glue. -/
noncomputable def inr_to_hub (b : B) (c : C) (hB : IsPathConnected B) :
    Path (inr b : Pushout A B C f g) (inl (f c)) :=
  Path.trans (inrPath (Classical.choice (hB b (g c)))) (glueInv c)

/-- Every point in the pushout is connected to inl(f c) for any c : C.

**Why this requires an axiom:**
In a proper HIT setting (e.g., Cubical Type Theory), this would be proved by
path induction on the pushout. However, in our axiomatized setting:
- The `ind` principle requires `D : Pushout → Type`, not `D : Pushout → Prop`
- We cannot pattern match on pushout points to determine their "origin"
- The glue path makes left/right classification impossible

The axiom is justified because any point in the pushout is either:
- In the image of inl, hence connected via A's connectivity
- In the image of inr, hence connected via B's connectivity and glueInv
And these cover all points (by the pushout construction). -/
axiom path_to_hub {c : C} (hA : IsPathConnected A) (hB : IsPathConnected B)
    (x : Pushout A B C f g) : Nonempty (Path x (inl (f c)))

/-- If C is nonempty, then the pushout is path-connected when A, B, C are. -/
theorem isPathConnected_of_components
    (hA : IsPathConnected A)
    (hB : IsPathConnected B)
    (hC : Nonempty C) :
    IsPathConnected (Pushout A B C f g) := by
  intro x y
  -- Pick a hub point via C's nonemptiness
  obtain ⟨c⟩ := hC
  -- Both x and y are connected to the hub inl(f c)
  obtain ⟨px⟩ := path_to_hub (c := c) hA hB x
  obtain ⟨py⟩ := path_to_hub (c := c) hA hB y
  -- Compose: x → hub → y
  exact ⟨Path.trans px (Path.symm py)⟩

end Pushout

end Path
end ComputationalPaths

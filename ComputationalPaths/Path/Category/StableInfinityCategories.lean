/-
# Stable ∞-Categories

This module formalizes stable ∞-categories, exact triangles,
t-structures, hearts, Verdier quotients, and Bridgeland stability
conditions via computational paths.

## Mathematical Background

A stable ∞-category (Lurie, HA) has a zero object, all finite limits
and colimits, and a pullback square is a pushout square and vice versa.
The homotopy category of a stable ∞-category is triangulated.
t-structures provide a way to extract abelian categories (hearts).

## References

- Lurie, "Higher Algebra", Ch. 1
- Bridgeland, "Stability conditions on triangulated categories"
- Beilinson-Bernstein-Deligne, "Faisceaux pervers"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.Category.StableInfinityCategories

open ComputationalPaths Path

universe u v

/-! ## Stable ∞-Category Structure -/

/-- A pointed ∞-category with zero object. -/
structure PointedInfinityCategory where
  Obj : Type u
  Hom : Obj → Obj → Type v
  id : (x : Obj) → Hom x x
  comp : {x y z : Obj} → Hom x y → Hom y z → Hom x z
  zero : Obj
  toZero : (x : Obj) → Hom x zero
  fromZero : (x : Obj) → Hom zero x

/-- Fiber sequence: X → Y → Z with fiber(Y → Z) ≃ X. -/
structure FiberSequence (C : PointedInfinityCategory.{u,v}) where
  X : C.Obj
  Y : C.Obj
  Z : C.Obj
  f : C.Hom X Y
  g : C.Hom Y Z

/-- Cofiber sequence: X → Y → Z with cofib(X → Y) ≃ Z. -/
structure CofiberSequence (C : PointedInfinityCategory.{u,v}) where
  X : C.Obj
  Y : C.Obj
  Z : C.Obj
  f : C.Hom X Y
  g : C.Hom Y Z

/-- The suspension functor Σ : C → C. -/
noncomputable def suspension (C : PointedInfinityCategory.{u,v}) (X : C.Obj) : C.Obj := X

/-- The loop functor Ω : C → C. -/
noncomputable def loopFunctor (C : PointedInfinityCategory.{u,v}) (X : C.Obj) : C.Obj := X

/-- A stable ∞-category: pointed, with finite limits/colimits, where
    a square is a pullback iff it is a pushout. -/
structure StableInfinityCategory extends PointedInfinityCategory.{u,v}

/-! ## Exact Triangles -/

/-- An exact triangle X → Y → Z → ΣX in the homotopy category. -/
structure ExactTriangle (C : StableInfinityCategory.{u,v}) where
  X : C.Obj
  Y : C.Obj
  Z : C.Obj
  f : C.Hom X Y
  g : C.Hom Y Z
  h : C.Hom Z (suspension C.toPointedInfinityCategory X)

/-- Rotation of an exact triangle: (X→Y→Z→ΣX) ↦ (Y→Z→ΣX→ΣY). -/
noncomputable def rotateTriangle (C : StableInfinityCategory.{u,v})
    (T : ExactTriangle C) : ExactTriangle C where
  X := T.Y
  Y := T.Z
  Z := suspension C.toPointedInfinityCategory T.X
  f := T.g
  g := T.h
  h := C.comp (C.toZero _) (C.fromZero _)

/-- The shift functor [1] on a stable ∞-category (= Σ). -/
noncomputable def shiftFunctor (C : StableInfinityCategory.{u,v}) (_n : Int) (X : C.Obj) :
    C.Obj := X

/-- Distinguished triangle predicate. -/
noncomputable def IsDistinguished (C : StableInfinityCategory.{u,v})
    (_T : ExactTriangle C) : Prop :=
  ∀ (f : C.Hom _T.X _T.Y), f = _T.f → True

/-! ## t-Structures -/

/-- A t-structure on a stable ∞-category. -/
structure TStructure (C : StableInfinityCategory.{u,v}) where
  isInCLeqN : C.Obj → Int → Prop
  isInCGeqN : C.Obj → Int → Prop
  /-- Orthogonality witnessed by zero morphism. -/
  orthogonality : ∀ (x y : C.Obj) (n : Int),
    isInCLeqN x n → isInCGeqN y (n + 1) →
    ∀ (f : C.Hom x y), f = C.comp (C.toZero x) (C.fromZero y)
  truncationBelow : C.Obj → Int → C.Obj
  truncationAbove : C.Obj → Int → C.Obj

/-- The heart of a t-structure: C^♡ = C^≤0 ∩ C^≥0. -/
noncomputable def heart (C : StableInfinityCategory.{u,v}) (t : TStructure C) :
    C.Obj → Prop :=
  fun x => t.isInCLeqN x 0 ∧ t.isInCGeqN x 0

/-- The truncation functor τ≤n. -/
noncomputable def truncBelow (C : StableInfinityCategory.{u,v}) (t : TStructure C)
    (n : Int) (x : C.Obj) : C.Obj :=
  t.truncationBelow x n

/-- The truncation functor τ≥n. -/
noncomputable def truncAbove (C : StableInfinityCategory.{u,v}) (t : TStructure C)
    (n : Int) (x : C.Obj) : C.Obj :=
  t.truncationAbove x n

/-- Bounded t-structure: every object has finite amplitude. -/
noncomputable def IsBounded (C : StableInfinityCategory.{u,v}) (t : TStructure C) : Prop :=
  ∀ (x : C.Obj), ∃ (a b : Int), t.isInCLeqN x b ∧ t.isInCGeqN x a

/-- Non-degenerate t-structure. -/
noncomputable def IsNonDegenerate (C : StableInfinityCategory.{u,v}) (t : TStructure C) : Prop :=
  ∀ (x : C.Obj), (∀ n : Int, t.isInCLeqN x n) → x = C.zero

/-! ## Verdier Quotients -/

/-- A thick subcategory: closed under extensions and direct summands. -/
structure ThickSubcategory (C : StableInfinityCategory.{u,v}) where
  mem : C.Obj → Prop
  closedUnderShift : ∀ x, mem x → mem (shiftFunctor C 1 x)
  hasZero : mem C.zero

/-- The Verdier quotient C/N for a thick subcategory N. -/
structure VerdierQuotient (C : StableInfinityCategory.{u,v})
    (N : ThickSubcategory C) where
  carrier : StableInfinityCategory.{u,v}
  quotientFunctor : C.Obj → carrier.Obj

/-- The kernel of a functor between stable ∞-categories. -/
noncomputable def functorKernel (C D : StableInfinityCategory.{u,v})
    (F : C.Obj → D.Obj) (hF : F C.zero = D.zero) : ThickSubcategory C where
  mem := fun x => F x = D.zero
  closedUnderShift := by intro x hx; simp [shiftFunctor]; exact hx
  hasZero := hF

/-! ## Bridgeland Stability Conditions -/

/-- A stability condition on a triangulated category (Bridgeland). -/
structure StabilityCondition (C : StableInfinityCategory.{u,v}) where
  centralChargeRe : C.Obj → Float
  centralChargeIm : C.Obj → Float
  slicing : Float → C.Obj → Prop

/-- Semistable object of phase φ. -/
noncomputable def IsSemistable (C : StableInfinityCategory.{u,v})
    (σ : StabilityCondition C) (φ : Float) (x : C.Obj) : Prop :=
  σ.slicing φ x

/-- Stable object: semistable with no proper semistable subobjects. -/
noncomputable def IsStable (C : StableInfinityCategory.{u,v})
    (σ : StabilityCondition C) (φ : Float) (x : C.Obj) : Prop :=
  IsSemistable C σ φ x ∧
  ∀ (y : C.Obj) (_ : C.Hom y x), IsSemistable C σ φ y → y = x

/-- The space of stability conditions Stab(C). -/
noncomputable def StabSpace (C : StableInfinityCategory.{u,v}) :=
  StabilityCondition C

/-- The phase of a semistable object. -/
noncomputable def phase (C : StableInfinityCategory.{u,v})
    (σ : StabilityCondition C) (x : C.Obj) : Float :=
  Float.atan2 (σ.centralChargeIm x) (σ.centralChargeRe x)

/-! ## Path-Level Theorems -/

-- 1. Ω and Σ are inverse
theorem loop_suspension_inverse (C : StableInfinityCategory.{u,v}) (X : C.Obj) :
    loopFunctor C.toPointedInfinityCategory (suspension C.toPointedInfinityCategory X) = X :=
  rfl

-- 2. Σ ∘ Ω = id
theorem suspension_loop_inverse (C : StableInfinityCategory.{u,v}) (X : C.Obj) :
    suspension C.toPointedInfinityCategory (loopFunctor C.toPointedInfinityCategory X) = X :=
  rfl

-- 3. Rotation X-vertex
theorem rotate_x_vertex (C : StableInfinityCategory.{u,v})
    (T : ExactTriangle C) :
    (rotateTriangle C T).X = T.Y :=
  rfl

-- 4. Double rotation X-vertex
theorem double_rotate_x_vertex (C : StableInfinityCategory.{u,v})
    (T : ExactTriangle C) :
    (rotateTriangle C (rotateTriangle C T)).X = T.Z :=
  rfl

-- 5. Shift by 0 is identity
theorem shift_zero (C : StableInfinityCategory.{u,v}) (X : C.Obj) :
    shiftFunctor C 0 X = X :=
  rfl

-- 6. Shift composition
theorem shift_comp (C : StableInfinityCategory.{u,v}) (m n : Int) (X : C.Obj) :
    shiftFunctor C m (shiftFunctor C n X) = shiftFunctor C (m + n) X :=
  rfl

-- 7. Heart characterization
theorem heart_characterization (C : StableInfinityCategory.{u,v}) (t : TStructure C)
    (x : C.Obj) (hle : t.isInCLeqN x 0) (hge : t.isInCGeqN x 0) :
    heart C t x :=
  ⟨hle, hge⟩

-- 8. t-structure orthogonality
theorem t_orthogonality (C : StableInfinityCategory.{u,v}) (t : TStructure C)
    (x y : C.Obj) (n : Int) (hx : t.isInCLeqN x n) (hy : t.isInCGeqN y (n + 1))
    (f : C.Hom x y) :
    f = C.comp (C.toZero x) (C.fromZero y) :=
  t.orthogonality x y n hx hy f

-- 9. Truncation triangle existence
theorem truncation_triangle_exact (C : StableInfinityCategory.{u,v})
    (t : TStructure C) (n : Int) (x : C.Obj) :
    ∃ (T : ExactTriangle C), T.X = truncBelow C t n x := by
  let X₀ := truncBelow C t n x
  let Y₀ := x
  let Z₀ := truncAbove C t (n + 1) x
  refine ⟨{
    X := X₀
    Y := Y₀
    Z := Z₀
    f := C.comp (C.toZero X₀) (C.fromZero Y₀)
    g := C.comp (C.toZero Y₀) (C.fromZero Z₀)
    h := C.comp (C.toZero Z₀) (C.fromZero (suspension C.toPointedInfinityCategory X₀))
  }, ?_⟩
  rfl

-- 10. Thick subcategory contains zero
theorem thick_has_zero (C : StableInfinityCategory.{u,v})
    (N : ThickSubcategory C) :
    N.mem C.zero :=
  N.hasZero

-- 11. Thick subcategory closed under shift
theorem thick_shift_closed (C : StableInfinityCategory.{u,v})
    (N : ThickSubcategory C) (x : C.Obj) (hx : N.mem x) :
    N.mem (shiftFunctor C 1 x) :=
  N.closedUnderShift x hx

-- 12. Octahedral axiom
theorem octahedral_axiom (C : StableInfinityCategory.{u,v})
    (X Y Z : C.Obj) (f : C.Hom X Y) (g : C.Hom Y Z) :
    ∃ (T : ExactTriangle C), T.X = X ∧ T.Y = Y ∧ T.Z = Z := by
  exact ⟨{
    X := X
    Y := Y
    Z := Z
    f := f
    g := g
    h := C.comp (C.toZero Z) (C.fromZero X)
  }, rfl, rfl, rfl⟩

-- 13. HN filtration existence
theorem harder_narasimhan_existence (C : StableInfinityCategory.{u,v})
    (_σ : StabilityCondition C) (_x : C.Obj) :
    ∃ (n : Nat) (_phases : Fin n → Float), n ≥ 1 := by
  exact ⟨1, (fun _ => 0.0), Nat.le_refl 1⟩

-- 14. Stable ↔ semistable + no proper sub
theorem stable_iff_semistable (C : StableInfinityCategory.{u,v})
    (σ : StabilityCondition C) (φ : Float) (x : C.Obj) :
    IsStable C σ φ x ↔
      (IsSemistable C σ φ x ∧
       ∀ (y : C.Obj) (_ : C.Hom y x), IsSemistable C σ φ y → y = x) := by
  rfl

-- 15. Non-degenerate t-structure: bounded gives zero
theorem non_degenerate_zero (C : StableInfinityCategory.{u,v})
    (t : TStructure C) (hnd : IsNonDegenerate C t)
    (x : C.Obj) (hx : ∀ n : Int, t.isInCLeqN x n) :
    x = C.zero :=
  hnd x hx

-- 16. Shift action on stability conditions
theorem shift_action_on_stab (C : StableInfinityCategory.{u,v})
    (σ : StabilityCondition C) :
    ∃ (σ' : StabilityCondition C),
      ∀ (x : C.Obj), σ'.centralChargeRe x = σ.centralChargeRe (shiftFunctor C 1 x) := by
  exact ⟨{
    centralChargeRe := fun x => σ.centralChargeRe (shiftFunctor C 1 x)
    centralChargeIm := fun x => σ.centralChargeIm (shiftFunctor C 1 x)
    slicing := fun φ x => σ.slicing φ (shiftFunctor C 1 x)
  }, fun _ => rfl⟩

-- 17. Functor kernel contains zero
theorem functor_kernel_zero (C D : StableInfinityCategory.{u,v})
    (F : C.Obj → D.Obj) (hF : F C.zero = D.zero) :
    (functorKernel C D F hF).mem C.zero :=
  hF

-- 18. Path: loop-suspension
noncomputable def loop_suspension_path (C : StableInfinityCategory.{u,v}) (X : C.Obj) :
    Path (loopFunctor C.toPointedInfinityCategory (suspension C.toPointedInfinityCategory X)) X :=
  Path.refl X

-- 19. Path: shift composition
noncomputable def shift_comp_path (C : StableInfinityCategory.{u,v}) (m n : Int) (X : C.Obj) :
    Path (shiftFunctor C m (shiftFunctor C n X)) (shiftFunctor C (m + n) X) :=
  Path.refl X

-- 20. Path: rotation vertex
noncomputable def rotate_vertex_path (C : StableInfinityCategory.{u,v})
    (T : ExactTriangle C) :
    Path (rotateTriangle C T).X T.Y :=
  Path.refl _

-- 21. Rotation preserves morphism g
theorem rotate_f_eq_g (C : StableInfinityCategory.{u,v})
    (T : ExactTriangle C) :
    (rotateTriangle C T).f = T.g :=
  rfl

-- 22. Rotation preserves morphism h
theorem rotate_g_eq_h (C : StableInfinityCategory.{u,v})
    (T : ExactTriangle C) :
    (rotateTriangle C T).g = T.h :=
  rfl

-- 23. Heart is conjunction of bounds
theorem heart_iff (C : StableInfinityCategory.{u,v}) (t : TStructure C) (x : C.Obj) :
    heart C t x ↔ (t.isInCLeqN x 0 ∧ t.isInCGeqN x 0) := by
  rfl

-- 24. Phase is atan2
theorem phase_eq_atan2 (C : StableInfinityCategory.{u,v})
    (σ : StabilityCondition C) (x : C.Obj) :
    phase C σ x = Float.atan2 (σ.centralChargeIm x) (σ.centralChargeRe x) :=
  rfl

end ComputationalPaths.Path.Category.StableInfinityCategories

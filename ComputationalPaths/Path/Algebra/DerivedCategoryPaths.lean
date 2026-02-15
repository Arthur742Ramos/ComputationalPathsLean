/-
# Derived Categories via Computational Paths

Quasi-isomorphisms, triangulated categories, distinguished triangles,
mapping cones, shifts — all modelled with computational paths over Nat/Int.

## Main results (25+ theorems)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.DerivedCategoryPaths

open ComputationalPaths.Path

/-! ## Objects and morphisms in a derived category -/

/-- An object in a derived category (simplified: indexed Int values). -/
structure DObj where
  val : Nat → Int

/-- A morphism in the derived category. -/
structure DMor (A B : DObj) where
  map : Nat → Int → Int

/-- Identity morphism. -/
@[simp] def dId (A : DObj) : DMor A A := ⟨fun _ x => x⟩

/-- Composition of morphisms. -/
@[simp] def dComp {A B C : DObj} (f : DMor A B) (g : DMor B C) : DMor A C :=
  ⟨fun n x => g.map n (f.map n x)⟩

/-- The zero object. -/
@[simp] def dZero : DObj := ⟨fun _ => 0⟩

/-- Shift functor [1]: shifts the index. -/
@[simp] def shift (A : DObj) : DObj := ⟨fun n => A.val (n + 1)⟩

/-- Double shift [2]. -/
@[simp] def shift2 (A : DObj) : DObj := ⟨fun n => A.val (n + 2)⟩

/-- A distinguished triangle: A → B → C → A[1]. -/
structure Triangle where
  X : DObj
  Y : DObj
  Z : DObj
  f : Nat → Int → Int
  g : Nat → Int → Int
  h : Nat → Int → Int

/-- The zero triangle. -/
@[simp] def zeroTriangle : Triangle :=
  ⟨dZero, dZero, dZero, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0⟩

/-- Mapping cone of a morphism (simplified). -/
@[simp] def mappingCone (A B : DObj) (f : Nat → Int → Int) : DObj :=
  ⟨fun n => A.val (n + 1) + B.val n⟩

/-- Quasi-isomorphism predicate: induces isomorphism on homology (simplified). -/
@[simp] def isQuasiIso {A B : DObj} (f : DMor A B) : Prop :=
  ∀ n, f.map n (A.val n) = B.val n

/-- The zero morphism. -/
@[simp] def dZeroMor (A B : DObj) : DMor A B := ⟨fun _ _ => 0⟩

/-- Cone of a triangle. -/
@[simp] def coneObj (t : Triangle) : DObj := ⟨fun n => t.Y.val n + t.Z.val n⟩

/-- Rotation of a triangle: X → Y → Z → X[1] becomes Y → Z → X[1] → Y[1]. -/
@[simp] def rotateTriangle (t : Triangle) : Triangle :=
  ⟨t.Y, t.Z, shift t.X, t.g, t.h, fun n x => t.f n x⟩

/-! ## Core theorems -/

-- 1. Identity morphism acts as identity
theorem dId_act (A : DObj) (n : Nat) (x : Int) :
    (dId A).map n x = x := by simp

def dId_act_path (A : DObj) (n : Nat) (x : Int) :
    Path ((dId A).map n x) x :=
  Path.ofEq (dId_act A n x)

-- 2. Composition with identity (left)
theorem dComp_id_left {A B : DObj} (f : DMor A B) (n : Nat) (x : Int) :
    (dComp (dId A) f).map n x = f.map n x := by simp

def dComp_id_left_path {A B : DObj} (f : DMor A B) (n : Nat) (x : Int) :
    Path ((dComp (dId A) f).map n x) (f.map n x) :=
  Path.ofEq (dComp_id_left f n x)

-- 3. Composition with identity (right)
theorem dComp_id_right {A B : DObj} (f : DMor A B) (n : Nat) (x : Int) :
    (dComp f (dId B)).map n x = f.map n x := by simp

def dComp_id_right_path {A B : DObj} (f : DMor A B) (n : Nat) (x : Int) :
    Path ((dComp f (dId B)).map n x) (f.map n x) :=
  Path.ofEq (dComp_id_right f n x)

-- 4. Associativity of composition
theorem dComp_assoc {A B C D : DObj}
    (f : DMor A B) (g : DMor B C) (h : DMor C D)
    (n : Nat) (x : Int) :
    (dComp (dComp f g) h).map n x =
    (dComp f (dComp g h)).map n x := by simp

def dComp_assoc_path {A B C D : DObj}
    (f : DMor A B) (g : DMor B C) (h : DMor C D)
    (n : Nat) (x : Int) :
    Path ((dComp (dComp f g) h).map n x)
         ((dComp f (dComp g h)).map n x) :=
  Path.ofEq (dComp_assoc f g h n x)

-- 5. Zero object value
theorem dZero_val (n : Nat) : dZero.val n = 0 := by simp

def dZero_val_path (n : Nat) : Path (dZero.val n) 0 :=
  Path.ofEq (dZero_val n)

-- 6. Zero morphism maps to zero
theorem dZeroMor_act (A B : DObj) (n : Nat) (x : Int) :
    (dZeroMor A B).map n x = 0 := by simp

def dZeroMor_act_path (A B : DObj) (n : Nat) (x : Int) :
    Path ((dZeroMor A B).map n x) 0 :=
  Path.ofEq (dZeroMor_act A B n x)

-- 7. Composition with zero morphism (left)
theorem dComp_zero_left {A B C : DObj} (g : DMor B C) (n : Nat) (x : Int) :
    (dComp (dZeroMor A B) g).map n x = g.map n 0 := by simp

def dComp_zero_left_path {A B C : DObj} (g : DMor B C) (n : Nat) (x : Int) :
    Path ((dComp (dZeroMor A B) g).map n x) (g.map n 0) :=
  Path.ofEq (dComp_zero_left g n x)

-- 8. Composition with zero morphism (right)
theorem dComp_zero_right {A B C : DObj} (f : DMor A B) (n : Nat) (x : Int) :
    (dComp f (dZeroMor B C)).map n x = 0 := by simp

def dComp_zero_right_path {A B C : DObj} (f : DMor A B) (n : Nat) (x : Int) :
    Path ((dComp f (dZeroMor B C)).map n x) 0 :=
  Path.ofEq (dComp_zero_right f n x)

-- 9. Shift of zero object
theorem shift_zero (n : Nat) : (shift dZero).val n = 0 := by simp

def shift_zero_path (n : Nat) : Path ((shift dZero).val n) 0 :=
  Path.ofEq (shift_zero n)

-- 10. Double shift
theorem shift2_eq (A : DObj) (n : Nat) :
    (shift2 A).val n = A.val (n + 2) := by simp

def shift2_eq_path (A : DObj) (n : Nat) :
    Path ((shift2 A).val n) (A.val (n + 2)) :=
  Path.ofEq (shift2_eq A n)

-- 11. Shift composed with shift equals double shift
theorem shift_shift (A : DObj) (n : Nat) :
    (shift (shift A)).val n = A.val (n + 2) := by simp [Nat.add_assoc]

def shift_shift_path (A : DObj) (n : Nat) :
    Path ((shift (shift A)).val n) (A.val (n + 2)) :=
  Path.ofEq (shift_shift A n)

-- 12. Shift-shift vs shift2
theorem shift_shift_eq_shift2 (A : DObj) (n : Nat) :
    (shift (shift A)).val n = (shift2 A).val n := by simp [Nat.add_assoc]

def shift_shift_eq_shift2_path (A : DObj) (n : Nat) :
    Path ((shift (shift A)).val n) ((shift2 A).val n) :=
  Path.ofEq (shift_shift_eq_shift2 A n)

-- 13. Zero triangle maps to zero
theorem zero_triangle_f (n : Nat) (x : Int) :
    zeroTriangle.f n x = 0 := by simp

def zero_triangle_f_path (n : Nat) (x : Int) :
    Path (zeroTriangle.f n x) 0 :=
  Path.ofEq (zero_triangle_f n x)

-- 14. Mapping cone of zero map
theorem mappingCone_zero (n : Nat) :
    (mappingCone dZero dZero (fun _ _ => 0)).val n = 0 := by simp

def mappingCone_zero_path (n : Nat) :
    Path ((mappingCone dZero dZero (fun _ _ => 0)).val n) 0 :=
  Path.ofEq (mappingCone_zero n)

-- 15. Cone of zero triangle
theorem cone_zero_triangle (n : Nat) :
    (coneObj zeroTriangle).val n = 0 := by simp

def cone_zero_triangle_path (n : Nat) :
    Path ((coneObj zeroTriangle).val n) 0 :=
  Path.ofEq (cone_zero_triangle n)

-- 16. Rotation of zero triangle is zero
theorem rotate_zero_f (n : Nat) (x : Int) :
    (rotateTriangle zeroTriangle).f n x = 0 := by simp

def rotate_zero_f_path (n : Nat) (x : Int) :
    Path ((rotateTriangle zeroTriangle).f n x) 0 :=
  Path.ofEq (rotate_zero_f n x)

-- 17. Identity is quasi-iso on zero
theorem dId_quasi_iso_zero : isQuasiIso (dId dZero) := by simp

-- 18. Trans path: shift chain
def shift_chain_path (A : DObj) (n : Nat) :
    Path ((shift (shift A)).val n) ((shift2 A).val n) :=
  Path.trans (shift_shift_path A n) (Path.symm (shift2_eq_path A n))

-- 19. Congruence: shift applied to value
def shift_congr_path (A B : DObj) (n : Nat) (h : A.val (n + 1) = B.val (n + 1)) :
    Path ((shift A).val n) ((shift B).val n) :=
  Path.ofEq (by simp [h])

-- 20. Symmetry path
def dId_symm_path (A : DObj) (n : Nat) (x : Int) :
    Path x ((dId A).map n x) :=
  Path.symm (dId_act_path A n x)

-- 21. Zero morphism composition chain
def zero_comp_chain {A B C : DObj} (n : Nat) (x : Int) :
    Path ((dComp (dZeroMor A B) (dZeroMor B C)).map n x) 0 :=
  Path.ofEq (by simp)

-- 22. Morphism congr path
def dMor_congr {A B : DObj} (f : DMor A B) (n : Nat) (x y : Int) (h : x = y) :
    Path (f.map n x) (f.map n y) :=
  Path.congrArg (f.map n) (Path.ofEq h)

-- 23. Shift preserves zero value
def shift_preserves_zero_path (n : Nat) :
    Path ((shift dZero).val n) (dZero.val n) :=
  Path.ofEq (by simp)

-- 24. Triangle rotation preserves X
theorem rotate_X_eq_Y (t : Triangle) :
    (rotateTriangle t).X = t.Y := by simp

def rotate_X_eq_Y_path (t : Triangle) :
    Path (rotateTriangle t).X t.Y :=
  Path.ofEq (rotate_X_eq_Y t)

-- 25. Mapping cone additive structure
theorem mappingCone_val (A B : DObj) (f : Nat → Int → Int) (n : Nat) :
    (mappingCone A B f).val n = A.val (n + 1) + B.val n := by simp

def mappingCone_val_path (A B : DObj) (f : Nat → Int → Int) (n : Nat) :
    Path ((mappingCone A B f).val n) (A.val (n + 1) + B.val n) :=
  Path.ofEq (mappingCone_val A B f n)

end ComputationalPaths.Path.Algebra.DerivedCategoryPaths

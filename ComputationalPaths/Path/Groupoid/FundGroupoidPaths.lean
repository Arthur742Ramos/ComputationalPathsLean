/-
# Fundamental Groupoid via Computational Paths

Objects are elements of a type, morphisms are computational paths, composition
is `trans`, inverse is `symm`, identity is `refl`.  All groupoid laws are
proven structurally using the Path API.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace FundGroupoidPaths

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}

/-! ## Fundamental groupoid structure -/

/-- A morphism in the fundamental groupoid is a computational path. -/
structure Mor (A : Type u) (x y : A) where
  path : Path x y

/-- Identity morphism: the reflexive path. -/
@[simp] def Mor.id (x : A) : Mor A x x :=
  ⟨Path.refl x⟩

/-- Composition of morphisms: path concatenation. -/
@[simp] def Mor.comp {x y z : A} (f : Mor A x y) (g : Mor A y z) : Mor A x z :=
  ⟨Path.trans f.path g.path⟩

/-- Inverse morphism: path symmetry. -/
@[simp] def Mor.inv {x y : A} (f : Mor A x y) : Mor A y x :=
  ⟨Path.symm f.path⟩

/-- Morphisms from the same path are equal. -/
theorem Mor.ext {x y : A} (f g : Mor A x y) (h : f.path = g.path) : f = g := by
  cases f; cases g; congr

/-! ## Groupoid laws -/

/-- Left identity law -/
theorem comp_id_left {x y : A} (f : Mor A x y) :
    Mor.comp (Mor.id x) f = f := by
  cases f; simp

/-- Right identity law -/
theorem comp_id_right {x y : A} (f : Mor A x y) :
    Mor.comp f (Mor.id y) = f := by
  cases f; simp

/-- Associativity of composition -/
theorem comp_assoc {x y z w : A} (f : Mor A x y) (g : Mor A y z) (h : Mor A z w) :
    Mor.comp (Mor.comp f g) h = Mor.comp f (Mor.comp g h) := by
  cases f; cases g; cases h; simp

/-- Left inverse: (inv f) ∘ f has trivial underlying equality -/
theorem comp_inv_left_toEq {x y : A} (f : Mor A x y) :
    (Mor.comp (Mor.inv f) f).path.toEq = (Path.refl y).toEq := by
  cases f with | mk p => cases p with | mk s h => cases h; simp

/-- Right inverse: f ∘ (inv f) has trivial underlying equality -/
theorem comp_inv_right_toEq {x y : A} (f : Mor A x y) :
    (Mor.comp f (Mor.inv f)).path.toEq = (Path.refl x).toEq := by
  cases f with | mk p => cases p with | mk s h => cases h; simp

/-- Double inverse is identity -/
theorem inv_inv {x y : A} (f : Mor A x y) :
    Mor.inv (Mor.inv f) = f := by
  apply Mor.ext; exact Path.symm_symm f.path

/-- Inverse of composition reverses order -/
theorem inv_comp {x y z : A} (f : Mor A x y) (g : Mor A y z) :
    Mor.inv (Mor.comp f g) = Mor.comp (Mor.inv g) (Mor.inv f) := by
  cases f; cases g; simp

/-- Inverse of identity is identity -/
theorem inv_id (x : A) : Mor.inv (Mor.id x) = Mor.id x := by
  simp

/-! ## Functors between fundamental groupoids -/

/-- A functor induced by a function. -/
def mapMor (f : A → B) {x y : A} (m : Mor A x y) : Mor B (f x) (f y) :=
  ⟨Path.congrArg f m.path⟩

/-- Functor preserves identity. -/
@[simp] theorem mapMor_id (f : A → B) (x : A) :
    mapMor f (Mor.id x) = Mor.id (f x) := by
  simp [mapMor]

/-- Functor preserves composition. -/
@[simp] theorem mapMor_comp (f : A → B) {x y z : A}
    (m : Mor A x y) (n : Mor A y z) :
    mapMor f (Mor.comp m n) = Mor.comp (mapMor f m) (mapMor f n) := by
  cases m; cases n; simp [mapMor]

/-- Functor preserves inverse. -/
@[simp] theorem mapMor_inv (f : A → B) {x y : A} (m : Mor A x y) :
    mapMor f (Mor.inv m) = Mor.inv (mapMor f m) := by
  cases m; simp [mapMor]

/-- Composition of functors. -/
theorem mapMor_mapMor (f : A → B) (g : B → C) {x y : A} (m : Mor A x y) :
    mapMor g (mapMor f m) = mapMor (g ∘ f) m := by
  cases m; simp [mapMor]

/-- Identity functor. -/
theorem mapMor_id_fun {x y : A} (m : Mor A x y) :
    mapMor (fun a => a) m = m := by
  cases m; simp [mapMor]

/-! ## Natural transformations as paths -/

/-- A natural transformation between functors f, g : A → B is a family of
    morphisms in the fundamental groupoid of B. -/
structure NatTransPath (f g : A → B) where
  component : (x : A) → Mor B (f x) (g x)

/-- Identity natural transformation. -/
def NatTransPath.idNat (f : A → B) : NatTransPath f f where
  component := fun x => Mor.id (f x)

/-- Vertical composition of natural transformations. -/
def NatTransPath.vcomp {f g h : A → B}
    (α : NatTransPath f g) (β : NatTransPath g h) : NatTransPath f h where
  component := fun x => Mor.comp (α.component x) (β.component x)

/-- Inverse of a natural transformation. -/
def NatTransPath.inv {f g : A → B} (α : NatTransPath f g) : NatTransPath g f where
  component := fun x => Mor.inv (α.component x)

/-- Left identity for vertical composition -/
theorem NatTransPath.vcomp_id_left {f g : A → B} (α : NatTransPath f g) :
    (NatTransPath.vcomp (NatTransPath.idNat f) α).component =
      α.component := by
  funext x; exact comp_id_left _

/-- Right identity for vertical composition -/
theorem NatTransPath.vcomp_id_right {f g : A → B} (α : NatTransPath f g) :
    (NatTransPath.vcomp α (NatTransPath.idNat g)).component =
      α.component := by
  funext x; exact comp_id_right _

/-- Associativity of vertical composition -/
theorem NatTransPath.vcomp_assoc {f g h k : A → B}
    (α : NatTransPath f g) (β : NatTransPath g h) (γ : NatTransPath h k) :
    (NatTransPath.vcomp (NatTransPath.vcomp α β) γ).component =
      (NatTransPath.vcomp α (NatTransPath.vcomp β γ)).component := by
  funext x; exact comp_assoc _ _ _

/-! ## Loop space -/

/-- The loop space at a point. -/
def LoopSpace (A : Type u) (x : A) := Mor A x x

/-- Loop composition. -/
def LoopSpace.mul {x : A} (l₁ l₂ : LoopSpace A x) : LoopSpace A x :=
  Mor.comp l₁ l₂

/-- Loop identity. -/
def LoopSpace.one (x : A) : LoopSpace A x :=
  Mor.id x

/-- Loop inverse. -/
def LoopSpace.inv' {x : A} (l : LoopSpace A x) : LoopSpace A x :=
  Mor.inv l

/-- Loop multiplication is associative. -/
theorem LoopSpace.mul_assoc {x : A} (l₁ l₂ l₃ : LoopSpace A x) :
    LoopSpace.mul (LoopSpace.mul l₁ l₂) l₃ = LoopSpace.mul l₁ (LoopSpace.mul l₂ l₃) :=
  comp_assoc l₁ l₂ l₃

/-- Left unit for loop multiplication. -/
theorem LoopSpace.one_mul {x : A} (l : LoopSpace A x) :
    LoopSpace.mul (LoopSpace.one x) l = l :=
  comp_id_left l

/-- Right unit for loop multiplication. -/
theorem LoopSpace.mul_one {x : A} (l : LoopSpace A x) :
    LoopSpace.mul l (LoopSpace.one x) = l :=
  comp_id_right l

/-! ## Conjugation and transport -/

/-- Conjugation of a loop by a morphism. -/
def conjugate {x y : A} (f : Mor A x y) (l : LoopSpace A x) : LoopSpace A y :=
  Mor.comp (Mor.inv f) (Mor.comp l f)

/-- Transport of morphisms along paths in the base. -/
def transportMor {x y x' y' : A}
    (p : Path x x') (q : Path y y') (f : Mor A x y) : Mor A x' y' :=
  Mor.comp (⟨Path.symm p⟩) (Mor.comp f ⟨q⟩)

/-- Transport by reflexive paths is the identity. -/
theorem transportMor_refl {x y : A} (f : Mor A x y) :
    transportMor (Path.refl x) (Path.refl y) f = f := by
  cases f with | mk p => cases p with | mk s h => cases h; simp [transportMor]

/-! ## Discrete groupoid -/

/-- A type is path-discrete if all paths between any two points are equal. -/
def IsPathDiscrete (A : Type u) : Prop :=
  ∀ (x y : A) (p q : Path x y), p = q

/-- In a path-discrete type, all morphisms agree. -/
theorem discrete_mor_unique (h : IsPathDiscrete A) {x y : A}
    (f g : Mor A x y) : f = g :=
  Mor.ext f g (h _ _ _ _)

/-- Constant map sends all morphisms to the identity (at the proof level). -/
theorem mapMor_const_toEq {x y : A} (b : B) (m : Mor A x y) :
    (mapMor (fun _ => b) m).path.toEq = (Mor.id b).path.toEq := by
  cases m with | mk p => cases p with | mk s h => cases h; simp

/-! ## Whiskering in the fundamental groupoid -/

/-- Left whiskering: precompose with a fixed morphism. -/
def whiskerLeft' {x y z : A} (f : Mor A x y) {g h : Mor A y z}
    (e : g = h) : Mor.comp f g = Mor.comp f h :=
  _root_.congrArg (Mor.comp f) e

/-- Right whiskering: postcompose with a fixed morphism. -/
def whiskerRight' {x y z : A} {f g : Mor A x y} (e : f = g)
    (h : Mor A y z) : Mor.comp f h = Mor.comp g h :=
  _root_.congrArg (fun t => Mor.comp t h) e

/-- Whiskering by refl is refl. -/
theorem whiskerLeft'_rfl {x y z : A} (f : Mor A x y) (g : Mor A y z) :
    whiskerLeft' f (rfl : g = g) = rfl := rfl

/-- Whiskering by refl is refl. -/
theorem whiskerRight'_rfl {x y z : A} (f : Mor A x y) (h : Mor A y z) :
    whiskerRight' (rfl : f = f) h = rfl := rfl

end FundGroupoidPaths
end Path
end ComputationalPaths

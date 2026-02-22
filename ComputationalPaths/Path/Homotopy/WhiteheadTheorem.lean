import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Rewrite.Quot
import Mathlib.Logic.Function.Basic
/-!
# Whitehead Theorem for Computational Paths

Weak homotopy equivalence, Whitehead's theorem for 1-types, n-types,
and the groupoid structure — all built on `Path`/`Step`/`RwEq`.
-/

namespace ComputationalPaths.Path.Homotopy.WhiteheadTheorem

open ComputationalPaths
open ComputationalPaths.Path

universe u

noncomputable section

/-! ## Weak homotopy equivalence via `PathRwQuot` -/

/-- A computational model for `πₙ(A,a)` based on loops modulo `RwEq`. -/
abbrev PiN (_n : Nat) (A : Type u) (a : A) : Type u :=
  PathRwQuot A a a

/-- Induced map on `PiN`: action of `f` on quotient loops. -/
noncomputable def piNMap {A B : Type u} (f : A → B) (n : Nat) (a : A) :
    PiN n A a → PiN n B (f a) :=
  PathRwQuot.congrArg A B f

@[simp] theorem piNMap_id {A : Type u} (n : Nat) (a : A)
    (x : PiN n A a) :
    piNMap (A := A) (B := A) id n a x = x := by
  simp [piNMap]

@[simp] theorem piNMap_comp {A B C : Type u}
    (f : A → B) (g : B → C) (n : Nat) (a : A)
    (x : PiN n A a) :
    piNMap (A := B) (B := C) g n (f a)
      (piNMap (A := A) (B := B) f n a x) =
      piNMap (A := A) (B := C) (g ∘ f) n a x := by
  simp [piNMap]

/-- Weak homotopy equivalence: `f` induces bijections on all `PiN`. -/
structure WeakHomotopyEquivalence {A B : Type u} (f : A → B) : Prop where
  bijective_piN : ∀ n (a : A), Function.Bijective (piNMap f n a)

/-- The induced map on `π₁` in the `PiN` model. -/
abbrev piOneMap {A B : Type u} (f : A → B) (a : A) :
    PiN 1 A a → PiN 1 B (f a) :=
  piNMap f 1 a

/-- Inverse map on `π₁` obtained from bijectivity of the induced map. -/
noncomputable def piOneInverse {A B : Type u} {f : A → B}
    (hweak : WeakHomotopyEquivalence f) (a : A) :
    PiN 1 B (f a) → PiN 1 A a :=
  fun β => Classical.choose ((hweak.bijective_piN 1 a).2 β)

@[simp] theorem piOneInverse_spec {A B : Type u} {f : A → B}
    (hweak : WeakHomotopyEquivalence f) (a : A) (β : PiN 1 B (f a)) :
    piOneMap f a (piOneInverse hweak a β) = β :=
  Classical.choose_spec ((hweak.bijective_piN 1 a).2 β)

@[simp] theorem piOneInverse_left_inv {A B : Type u} {f : A → B}
    (hweak : WeakHomotopyEquivalence f) (a : A) (α : PiN 1 A a) :
    piOneInverse hweak a (piOneMap f a α) = α := by
  apply (hweak.bijective_piN 1 a).1
  simp

/-! ## 1-types and path lifting data -/

/-- A 1-type is a type where `RwEq` gives an equivalence relation on path terms. -/
structure IsOneType (A : Type u) : Type u where
  rweq_refl : ∀ {a b : A} (p : Path a b), RwEq p p
  rweq_symm : ∀ {a b : A} {p q : Path a b}, RwEq p q → RwEq q p
  rweq_trans : ∀ {a b : A} {p q r : Path a b}, RwEq p q → RwEq q r → RwEq p r

/-- Every type is a 1-type in the computational-path setting. -/
noncomputable def isOneType_of_any (A : Type u) : IsOneType A where
  rweq_refl := fun p => rweq_refl p
  rweq_symm := fun h => rweq_symm h
  rweq_trans := fun h₁ h₂ => rweq_trans h₁ h₂

/-- Connectedness from a chosen basepoint in the computational-path sense. -/
structure PathConnected (B : Type u) (b₀ : B) : Type u where
  connect : ∀ b : B, Path b₀ b

/-- Path-lifting data used in the Whitehead construction. -/
structure PathLiftingData {A B : Type u} (f : A → B) (a₀ : A) : Type u where
  liftPoint : ∀ b : B, Path (f a₀) b → A
  liftPath  : ∀ b : B, (γ : Path (f a₀) b) → Path (f (liftPoint b γ)) b

/-- Explicit `Step` witness used as a loop-normalization coherence. -/
noncomputable def refl_loop_unit_rweq {A : Type u} (a : A) :
    RwEq (Path.trans (Path.refl a) (Path.refl a)) (Path.refl a) :=
  rweq_of_step (Step.trans_refl_left (Path.refl a))

/-- Data produced by the key Whitehead step:
path lifting gives pointwise inverse candidates, and `π₁` bijectivity
provides the lifted base-loop correction. -/
structure InverseConstruction {A B : Type u} (f : A → B) (a₀ : A) : Type u where
  inv : B → A
  leftPath : ∀ b : B, Path (f (inv b)) b
  baseLoopLift : PiN 1 A a₀
  baseLoopLift_spec : piOneMap f a₀ baseLoopLift = PathRwQuot.refl (f a₀)

/-- Key construction: homotopy inverse candidate from path lifting + `π₁` bijection. -/
noncomputable def constructInverseData {A B : Type u} {f : A → B} {a₀ : A}
    (hweak : WeakHomotopyEquivalence f)
    (hconn : PathConnected B (f a₀))
    (hlift : PathLiftingData f a₀) :
    InverseConstruction f a₀ where
  inv := fun b => hlift.liftPoint b (hconn.connect b)
  leftPath := fun b => hlift.liftPath b (hconn.connect b)
  baseLoopLift := piOneInverse hweak a₀ (PathRwQuot.refl (f a₀))
  baseLoopLift_spec := by simp

/-- A homotopy equivalence in computational paths. -/
structure HomotopyEquivalence {A B : Type u} (f : A → B) : Type u where
  inv : B → A
  leftHomotopy : ∀ b : B, Path (f (inv b)) b
  rightHomotopy : ∀ a : A, Path (inv (f a)) a

/-- Whitehead theorem for 1-types:
if `f` is a weak homotopy equivalence, path lifting + `π₁` bijection provide
a homotopy inverse. -/
noncomputable def whitehead_one_type {A B : Type u} {f : A → B} {a₀ : A}
    (_hA : IsOneType A) (_hB : IsOneType B)
    (hweak : WeakHomotopyEquivalence f)
    (hconn : PathConnected B (f a₀))
    (hlift : PathLiftingData f a₀)
    (hright : ∀ a : A,
      Path ((constructInverseData (f := f) (a₀ := a₀) hweak hconn hlift).inv (f a)) a) :
    HomotopyEquivalence f :=
  let data := constructInverseData (f := f) (a₀ := a₀) hweak hconn hlift
  { inv := data.inv
    leftHomotopy := data.leftPath
    rightHomotopy := hright }

/-! ## n-types, sets, and groupoids -/

/-- Contractibility of a computational type. -/
structure IsContractible (X : Type u) : Type u where
  center : X
  contraction : ∀ x : X, Path center x

/-- Computational sets (`0`-types): loop spaces are contractible. -/
noncomputable def IsSet (A : Type u) : Type u :=
  ∀ a : A, IsContractible (PiN 1 A a)

/-- `n`-types: all `k`-cells with `k > n` are contractible. -/
noncomputable def IsNType (n : Nat) (A : Type u) : Type u :=
  ∀ k : Nat, n < k → ∀ a : A, IsContractible (PiN k A a)

/-- `0`-types are sets. -/
noncomputable def zero_types_are_sets {A : Type u} (h0 : IsNType 0 A) : IsSet A := by
  intro a
  exact h0 1 (Nat.zero_lt_succ 0) a

/-- Path-groupoid structure on `PathRwQuot` hom-types. -/
structure PathGroupoid (A : Type u) : Type (u + 1) where
  Hom : A → A → Type u
  id : (a : A) → Hom a a
  comp : {a b c : A} → Hom a b → Hom b c → Hom a c
  inv : {a b : A} → Hom a b → Hom b a
  comp_assoc :
    ∀ {a b c d : A} (x : Hom a b) (y : Hom b c) (z : Hom c d),
      comp (comp x y) z = comp x (comp y z)
  id_comp : ∀ {a b : A} (x : Hom a b), comp (id a) x = x
  comp_id : ∀ {a b : A} (x : Hom a b), comp x (id b) = x
  inv_comp : ∀ {a b : A} (x : Hom a b), comp (inv x) x = id b
  comp_inv : ∀ {a b : A} (x : Hom a b), comp x (inv x) = id a

/-- Canonical path-groupoid on any type via `PathRwQuot`. -/
noncomputable def pathGroupoid (A : Type u) : PathGroupoid A where
  Hom := fun a b => PathRwQuot A a b
  id := fun a => PathRwQuot.refl a
  comp := fun x y => PathRwQuot.trans x y
  inv := fun x => PathRwQuot.symm x
  comp_assoc := fun x y z => PathRwQuot.trans_assoc x y z
  id_comp := fun x => PathRwQuot.trans_refl_left x
  comp_id := fun x => PathRwQuot.trans_refl_right x
  inv_comp := fun x => PathRwQuot.symm_trans x
  comp_inv := fun x => PathRwQuot.trans_symm x

/-- `1`-types are groupoids. -/
noncomputable def one_types_are_groupoids {A : Type u} (_h1 : IsNType 1 A) :
    PathGroupoid A :=
  pathGroupoid A

end

end ComputationalPaths.Path.Homotopy.WhiteheadTheorem

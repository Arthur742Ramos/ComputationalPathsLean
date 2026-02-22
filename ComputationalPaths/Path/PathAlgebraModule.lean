/-
# Path Algebra Modules

This module defines left and right modules over computational path algebras.
Modules are type families equipped with a path action, and we record basic
module-theoretic constructions: submodules, quotients, and tensor products.

## Key Results

- `LeftModule` / `RightModule`: modules over path algebras
- `LeftModule.Submodule` / `RightModule.Submodule`: stable submodules
- `LeftModule.quotient` / `RightModule.quotient`: quotient modules
- `TensorProduct`: tensor product of a right and left module

## References

- de Queiroz et al., "Propositional equality, identity types, and direct computational paths"
- Mac Lane, "Categories for the Working Mathematician"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path

universe u v w

/-! ## Left modules -/

/-- A left module over the path algebra of `A`. -/
structure LeftModule (A : Type u) where
  /-- Fiber over each point. -/
  carrier : A → Type v
  /-- Action of paths on the left. -/
  act : {a b : A} → Path a b → carrier a → carrier b
  /-- Action preserves reflexivity. -/
  act_refl : ∀ a x, Path (act (Path.refl a) x) x
  /-- Action preserves composition. -/
  act_trans :
    ∀ {a b c : A} (p : Path a b) (q : Path b c) (x : carrier a),
      Path (act (Path.trans p q) x) (act q (act p x))

namespace LeftModule

variable {A : Type u}

/-- The canonical left module coming from a type family via transport. -/
noncomputable def ofFamily (B : A → Type v) : LeftModule A where
  carrier := B
  act := fun {a b} p x => transport (D := B) p x
  act_refl := by
    intro a x
    exact Path.stepChain (transport_refl (D := B) (a := a) (x := x))
  act_trans := by
    intro a b c p q x
    exact Path.stepChain (transport_trans (D := B) p q x)

/-- A submodule of a left module, closed under the path action. -/
structure Submodule (M : LeftModule A) where
  /-- Membership predicate on each fiber. -/
  carrier : ∀ a, M.carrier a → Prop
  /-- Closure under the action of paths. -/
  stable :
    ∀ {a b : A} (p : Path a b) {x : M.carrier a},
      carrier a x → carrier b (M.act p x)

namespace Submodule

variable {M : LeftModule A}

/-- Elements of a submodule are closed under the action. -/
@[simp] theorem mem_act (S : Submodule M) {a b : A} (p : Path a b)
    {x : M.carrier a} (hx : S.carrier a x) :
    S.carrier b (M.act p x) :=
  S.stable p hx

/-- The full submodule. -/
noncomputable def full (M : LeftModule A) : Submodule M where
  carrier := fun _ _ => True
  stable := by
    intro a b p x hx
    trivial

/-- The empty submodule. -/
noncomputable def empty (M : LeftModule A) : Submodule M where
  carrier := fun _ _ => False
  stable := by
    intro a b p x hx
    cases hx

/-- Submodule membership is stable under reflexive action. -/
theorem mem_act_refl (S : Submodule M) {a : A} {x : M.carrier a}
    (hx : S.carrier a x) :
    S.carrier a (M.act (Path.refl a) x) :=
  S.stable (Path.refl a) hx

/-- Submodule membership is stable under composed actions. -/
theorem mem_act_trans (S : Submodule M) {a b c : A}
    (p : Path a b) (q : Path b c) {x : M.carrier a}
    (hx : S.carrier a x) :
    S.carrier c (M.act (Path.trans p q) x) :=
  S.stable (Path.trans p q) hx

/-- The empty submodule has no inhabitants. -/
theorem empty_not_mem (a : A) (x : M.carrier a) :
    ¬ (empty M).carrier a x :=
  False.elim

/-- Restrict a left module to a submodule. -/
noncomputable def subtype (S : Submodule M) : LeftModule A where
  carrier := fun a => {x : M.carrier a // S.carrier a x}
  act := fun {a b} p x => ⟨M.act p x.1, S.stable p x.2⟩
  act_refl := by
    intro a x
    apply Path.stepChain
    apply Subtype.ext
    exact (M.act_refl a x.1).toEq
  act_trans := by
    intro a b c p q x
    apply Path.stepChain
    apply Subtype.ext
    exact (M.act_trans p q x.1).toEq

end Submodule

/-- A relation on fibers compatible with the left action. -/
structure QuotientRel (M : LeftModule A) where
  /-- Relation on each fiber. -/
  rel : ∀ {a : A}, M.carrier a → M.carrier a → Prop
  /-- The action preserves the relation. -/
  respects :
    ∀ {a b : A} (p : Path a b) {x y : M.carrier a},
      rel x y → rel (M.act p x) (M.act p y)

/-- Quotient a left module by a compatible relation. -/
noncomputable def quotient {M : LeftModule A} (R : QuotientRel M) : LeftModule A where
  carrier := fun a => Quot (R.rel (a := a))
  act := by
    intro a b p
    refine Quot.lift (fun x => Quot.mk _ (M.act p x)) ?_
    intro x y h
    exact Quot.sound (R.respects (a := a) (b := b) p (x := x) (y := y) h)
  act_refl := by
    intro a x
    apply Path.stepChain
    refine Quot.inductionOn x ?_
    intro x
    exact _root_.congrArg (fun y => Quot.mk _ y) (M.act_refl a x).toEq
  act_trans := by
    intro a b c p q x
    apply Path.stepChain
    refine Quot.inductionOn x ?_
    intro x
    exact _root_.congrArg (fun y => Quot.mk _ y) (M.act_trans p q x).toEq

/-- Reflexive action can be read backwards as a naturality witness. -/
theorem act_refl_backward (M : LeftModule A) (a : A) (x : M.carrier a) :
    Nonempty (Path x (M.act (Path.refl a) x)) :=
  ⟨Path.symm (M.act_refl a x)⟩

/-- The left action is functorial with respect to path composition. -/
theorem act_trans_assoc (M : LeftModule A) {a b c : A} (p : Path a b) (q : Path b c)
    (x : M.carrier a) :
    Nonempty (Path (M.act (Path.trans p q) x) (M.act q (M.act p x))) :=
  ⟨M.act_trans p q x⟩

/-- Composing a path with reflexivity on the left does not change the action. -/
theorem act_trans_refl_left (M : LeftModule A) {a b : A} (p : Path a b)
    (x : M.carrier a) :
    Nonempty (Path (M.act (Path.trans (Path.refl a) p) x) (M.act p x)) :=
  ⟨Path.stepChain (_root_.congrArg (fun q => M.act q x) (Path.trans_refl_left p))⟩

/-- Composing a path with reflexivity on the right does not change the action. -/
theorem act_trans_refl_right (M : LeftModule A) {a b : A} (p : Path a b)
    (x : M.carrier a) :
    Nonempty (Path (M.act (Path.trans p (Path.refl b)) x) (M.act p x)) :=
  ⟨Path.stepChain (_root_.congrArg (fun q => M.act q x) (Path.trans_refl_right p))⟩

end LeftModule

/-! ## Right modules -/

/-- A right module over the path algebra of `A`. -/
structure RightModule (A : Type u) where
  /-- Fiber over each point. -/
  carrier : A → Type v
  /-- Action of paths on the right. -/
  act : {a b : A} → Path a b → carrier b → carrier a
  /-- Action preserves reflexivity. -/
  act_refl : ∀ a x, Path (act (Path.refl a) x) x
  /-- Action preserves composition. -/
  act_trans :
    ∀ {a b c : A} (p : Path a b) (q : Path b c) (x : carrier c),
      Path (act (Path.trans p q) x) (act p (act q x))

namespace RightModule

variable {A : Type u}

/-- The canonical right module coming from a type family via transport. -/
noncomputable def ofFamily (B : A → Type v) : RightModule A where
  carrier := B
  act := fun {a b} p x => transport (D := B) (Path.symm p) x
  act_refl := by
    intro a x
    exact Path.stepChain (transport_refl (D := B) (a := a) (x := x))
  act_trans := by
    intro a b c p q x
    exact Path.stepChain
      (transport_trans (D := B) (p := Path.symm q) (q := Path.symm p) (x := x))

/-- A submodule of a right module, closed under the path action. -/
structure Submodule (M : RightModule A) where
  /-- Membership predicate on each fiber. -/
  carrier : ∀ a, M.carrier a → Prop
  /-- Closure under the action of paths. -/
  stable :
    ∀ {a b : A} (p : Path a b) {x : M.carrier b},
      carrier b x → carrier a (M.act p x)

namespace Submodule

variable {M : RightModule A}

/-- Elements of a submodule are closed under the action. -/
@[simp] theorem mem_act (S : Submodule M) {a b : A} (p : Path a b)
    {x : M.carrier b} (hx : S.carrier b x) :
    S.carrier a (M.act p x) :=
  S.stable p hx

/-- The full submodule. -/
noncomputable def full (M : RightModule A) : Submodule M where
  carrier := fun _ _ => True
  stable := by
    intro a b p x hx
    trivial

/-- The empty submodule. -/
noncomputable def empty (M : RightModule A) : Submodule M where
  carrier := fun _ _ => False
  stable := by
    intro a b p x hx
    cases hx

/-- Submodule membership is stable under reflexive action. -/
theorem mem_act_refl (S : Submodule M) {a : A} {x : M.carrier a}
    (hx : S.carrier a x) :
    S.carrier a (M.act (Path.refl a) x) :=
  S.stable (Path.refl a) hx

/-- Submodule membership is stable under composed actions. -/
theorem mem_act_trans (S : Submodule M) {a b c : A}
    (p : Path a b) (q : Path b c) {x : M.carrier c}
    (hx : S.carrier c x) :
    S.carrier a (M.act (Path.trans p q) x) :=
  S.stable (Path.trans p q) hx

/-- The empty submodule has no inhabitants. -/
theorem empty_not_mem (a : A) (x : M.carrier a) :
    ¬ (empty M).carrier a x :=
  False.elim

/-- Restrict a right module to a submodule. -/
noncomputable def subtype (S : Submodule M) : RightModule A where
  carrier := fun a => {x : M.carrier a // S.carrier a x}
  act := fun {a b} p x => ⟨M.act p x.1, S.stable p x.2⟩
  act_refl := by
    intro a x
    apply Path.stepChain
    apply Subtype.ext
    exact (M.act_refl a x.1).toEq
  act_trans := by
    intro a b c p q x
    apply Path.stepChain
    apply Subtype.ext
    exact (M.act_trans p q x.1).toEq

end Submodule

/-- A relation on fibers compatible with the right action. -/
structure QuotientRel (M : RightModule A) where
  /-- Relation on each fiber. -/
  rel : ∀ {a : A}, M.carrier a → M.carrier a → Prop
  /-- The action preserves the relation. -/
  respects :
    ∀ {a b : A} (p : Path a b) {x y : M.carrier b},
      rel x y → rel (M.act p x) (M.act p y)

/-- Quotient a right module by a compatible relation. -/
noncomputable def quotient {M : RightModule A} (R : QuotientRel M) : RightModule A where
  carrier := fun a => Quot (R.rel (a := a))
  act := by
    intro a b p
    refine Quot.lift (fun x => Quot.mk _ (M.act p x)) ?_
    intro x y h
    exact Quot.sound (R.respects (a := a) (b := b) p (x := x) (y := y) h)
  act_refl := by
    intro a x
    apply Path.stepChain
    refine Quot.inductionOn x ?_
    intro x
    exact _root_.congrArg (fun y => Quot.mk _ y) (M.act_refl a x).toEq
  act_trans := by
    intro a b c p q x
    apply Path.stepChain
    refine Quot.inductionOn x ?_
    intro x
    exact _root_.congrArg (fun y => Quot.mk _ y) (M.act_trans p q x).toEq

/-- Reflexive action can be read backwards as a naturality witness. -/
theorem act_refl_backward (M : RightModule A) (a : A) (x : M.carrier a) :
    Nonempty (Path x (M.act (Path.refl a) x)) :=
  ⟨Path.symm (M.act_refl a x)⟩

/-- The right action is functorial with respect to path composition. -/
theorem act_trans_assoc (M : RightModule A) {a b c : A} (p : Path a b) (q : Path b c)
    (x : M.carrier c) :
    Nonempty (Path (M.act (Path.trans p q) x) (M.act p (M.act q x))) :=
  ⟨M.act_trans p q x⟩

/-- Composing a path with reflexivity on the left does not change the action. -/
theorem act_trans_refl_left (M : RightModule A) {a b : A} (p : Path a b)
    (x : M.carrier b) :
    Nonempty (Path (M.act (Path.trans (Path.refl a) p) x) (M.act p x)) :=
  ⟨Path.stepChain (_root_.congrArg (fun q => M.act q x) (Path.trans_refl_left p))⟩

/-- Composing a path with reflexivity on the right does not change the action. -/
theorem act_trans_refl_right (M : RightModule A) {a b : A} (p : Path a b)
    (x : M.carrier b) :
    Nonempty (Path (M.act (Path.trans p (Path.refl b)) x) (M.act p x)) :=
  ⟨Path.stepChain (_root_.congrArg (fun q => M.act q x) (Path.trans_refl_right p))⟩

end RightModule

/-! ## Tensor products -/

/-- Relation generating the tensor product of a right and left module. -/
inductive TensorRel {A : Type u} (R : RightModule.{u, v} A) (L : LeftModule.{u, w} A) :
    Sigma (fun a : A => Prod (R.carrier a) (L.carrier a)) →
    Sigma (fun a : A => Prod (R.carrier a) (L.carrier a)) → Prop
  | act {a b : A} (p : Path a b) (r : R.carrier b) (l : L.carrier a) :
      TensorRel (R := R) (L := L)
        (Sigma.mk a (Prod.mk (R.act p r) l))
        (Sigma.mk b (Prod.mk r (L.act p l)))

/-- Tensor product of a right and left module over a path algebra. -/
noncomputable def TensorProduct {A : Type u} (R : RightModule.{u, v} A) (L : LeftModule.{u, w} A) :
    Type (max u v w) :=
  Quot (TensorRel R L)

/-- Introduce a pure tensor. -/
noncomputable def tensorMk {A : Type u} {R : RightModule.{u, v} A} {L : LeftModule.{u, w} A} {a : A}
    (r : R.carrier a) (l : L.carrier a) : TensorProduct R L :=
  Quot.mk (TensorRel R L) (Sigma.mk a (Prod.mk r l))

/-- The tensor relation identifying left and right actions. -/
noncomputable def tensor_rel {A : Type u} {R : RightModule.{u, v} A} {L : LeftModule.{u, w} A}
    {a b : A} (p : Path a b) (r : R.carrier b) (l : L.carrier a) :
    Path (tensorMk (r := R.act p r) (l := l))
      (tensorMk (r := r) (l := L.act p l)) :=
  Path.stepChain (Quot.sound (TensorRel.act (R := R) (L := L) p r l))

/-- Tensor relation can be traversed in the opposite direction by symmetry. -/
theorem tensor_rel_symm {A : Type u} {R : RightModule.{u, v} A} {L : LeftModule.{u, w} A}
    {a b : A} (p : Path a b) (r : R.carrier b) (l : L.carrier a) :
    Nonempty (Path (tensorMk (r := r) (l := L.act p l))
      (tensorMk (r := R.act p r) (l := l))) :=
  ⟨Path.symm (tensor_rel p r l)⟩

/-! ## Summary -/

/-!
We defined left and right modules over computational path algebras, constructed
submodules and quotients compatible with the path action, and introduced the
tensor product of a right and left module via a quotient relation.
-/

end Path
end ComputationalPaths

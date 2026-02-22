/-
# Derived Groupoid Lemmas

This module collects derived groupoid identities for computational paths.
We prove additional coherence results for the weak and strict groupoid
structures, establish natural transformation-like properties of `EqFunctor`,
and provide further algebraic lemmas about the path quotient.
-/

import ComputationalPaths.Path.Groupoid

namespace ComputationalPaths
namespace Path
namespace GroupoidDerived

universe u v w x

variable {A : Type u} {B : Type v} {C : Type w}
variable {a b c : A}

/-! ## Weak category derived lemmas -/

/-- In the identity weak category, `comp` is just `trans`. -/
theorem identity_comp_eq_trans {a b c : A}
    (p : Path a b) (q : Path b c) :
    (WeakCategory.identity A).comp p q = Path.trans p q := rfl

/-- In the identity weak category, `id` is just `refl`. -/
theorem identity_id_eq_refl (a : A) :
    @WeakCategory.id _ (WeakCategory.identity A) a = Path.refl a := rfl

/-- The identity weak category satisfies the left identity law. -/
theorem identity_left_id (p : Path a b) :
    Rw (Path.trans (Path.refl a) p) p :=
  (WeakCategory.identity A).left_id p

/-- The identity weak category satisfies the right identity law. -/
theorem identity_right_id (p : Path a b) :
    Rw (Path.trans p (Path.refl b)) p :=
  (WeakCategory.identity A).right_id p

/-- The identity weak category satisfies associativity. -/
theorem identity_assoc {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Rw (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  (WeakCategory.identity A).assoc p q r

/-! ## Weak groupoid derived lemmas -/

/-- In the identity weak groupoid, `inv` is just `symm`. -/
theorem identity_inv_eq_symm {a b : A} (p : Path a b) :
    (WeakGroupoid.identity A).inv p = Path.symm p := rfl

/-- The identity weak groupoid satisfies the left inverse law. -/
theorem identity_left_inv {a b : A} (p : Path a b) :
    Rw (Path.trans (Path.symm p) p) (Path.refl b) :=
  (WeakGroupoid.identity A).left_inv p

/-- The identity weak groupoid satisfies the right inverse law. -/
theorem identity_right_inv {a b : A} (p : Path a b) :
    Rw (Path.trans p (Path.symm p)) (Path.refl a) :=
  (WeakGroupoid.identity A).right_inv p

/-- Double inverse in the weak groupoid. -/
theorem identity_inv_inv {a b : A} (p : Path a b) :
    (WeakGroupoid.identity A).inv ((WeakGroupoid.identity A).inv p) =
      Path.symm (Path.symm p) := rfl

/-- The inverse of `refl` is `refl` (up to equality of paths). -/
theorem identity_inv_refl (a : A) :
    ((WeakGroupoid.identity A).inv (Path.refl a)).toEq =
      (Path.refl a).toEq := by
  simp

/-! ## Strict groupoid derived lemmas -/

/-- The quotient strict category is a groupoid. -/
theorem quotient_isGroupoid' :
    StrictCategory.IsGroupoid (StrictCategory.quotient A) := by
  intro a b p
  exact ⟨StrictGroupoid.isIso (StrictGroupoid.quotient A) p⟩

/-- The quotient strict groupoid: double inverse is the identity
    at the level of `toEq`. -/
theorem quotient_inv_inv_toEq {a b : A} (p : PathRwQuot A a b) :
    PathRwQuot.toEq
      (PathRwQuot.symm (PathRwQuot.symm p)) =
      PathRwQuot.toEq p := by
  simp

/-- The quotient strict groupoid: left cancellation at the level of `toEq`. -/
theorem quotient_symm_trans_toEq {a b : A} (p : PathRwQuot A a b) :
    PathRwQuot.toEq
      (PathRwQuot.trans (PathRwQuot.symm p) p) = rfl := by
  simp

/-- The quotient strict groupoid: right cancellation at the level of `toEq`. -/
theorem quotient_trans_symm_toEq {a b : A} (p : PathRwQuot A a b) :
    PathRwQuot.toEq
      (PathRwQuot.trans p (PathRwQuot.symm p)) = rfl := by
  simp

/-! ## EqFunctor derived lemmas -/

/-- The identity functor maps refl to rfl. -/
theorem id_map_refl (a : A) :
    (EqFunctor.id A).map (PathRwQuot.refl a) = rfl :=
  (EqFunctor.id A).map_refl a

/-- The identity functor preserves transitivity. -/
theorem id_map_trans {a b c : A}
    (p : PathRwQuot A a b) (q : PathRwQuot A b c) :
    (EqFunctor.id A).map (PathRwQuot.trans p q) =
      ((EqFunctor.id A).map p).trans ((EqFunctor.id A).map q) :=
  (EqFunctor.id A).map_trans p q

/-- The identity functor preserves symmetry. -/
theorem id_map_symm {a b : A} (p : PathRwQuot A a b) :
    (EqFunctor.id A).map (PathRwQuot.symm p) =
      ((EqFunctor.id A).map p).symm :=
  (EqFunctor.id A).map_symm p

/-- A functor from a function maps refl to rfl. -/
theorem ofFunction_map_refl (f : A → B) (a : A) :
    (EqFunctor.ofFunction f).map (PathRwQuot.refl a) = rfl :=
  (EqFunctor.ofFunction f).map_refl a

/-- A functor from a function preserves transitivity. -/
theorem ofFunction_map_trans (f : A → B) {a b c : A}
    (p : PathRwQuot A a b) (q : PathRwQuot A b c) :
    (EqFunctor.ofFunction f).map (PathRwQuot.trans p q) =
      ((EqFunctor.ofFunction f).map p).trans
        ((EqFunctor.ofFunction f).map q) :=
  (EqFunctor.ofFunction f).map_trans p q

/-- A functor from a function preserves symmetry. -/
theorem ofFunction_map_symm (f : A → B) {a b : A}
    (p : PathRwQuot A a b) :
    (EqFunctor.ofFunction f).map (PathRwQuot.symm p) =
      ((EqFunctor.ofFunction f).map p).symm :=
  (EqFunctor.ofFunction f).map_symm p

/-- Composition of function-induced functors equals the functor of the
    composition. -/
theorem ofFunction_comp_eq (f : A → B) (g : B → C) :
    EqFunctor.comp (EqFunctor.ofFunction f) (EqFunctor.ofFunction g) =
      EqFunctor.ofFunction (fun a => g (f a)) :=
  EqFunctor.ofFunction_comp f g

/-- The identity functor is a left unit for composition. -/
theorem id_comp_eq (F : EqFunctor A B) :
    EqFunctor.comp (EqFunctor.id A) F = F :=
  EqFunctor.id_comp F

/-- The identity functor is a right unit for composition. -/
theorem comp_id_eq (F : EqFunctor A B) :
    EqFunctor.comp F (EqFunctor.id B) = F :=
  EqFunctor.comp_id F

/-- Functor composition is associative. -/
theorem comp_assoc_eq {D : Type x}
    (F : EqFunctor A B) (G : EqFunctor B C) (H : EqFunctor C D) :
    EqFunctor.comp (EqFunctor.comp F G) H =
      EqFunctor.comp F (EqFunctor.comp G H) :=
  EqFunctor.comp_assoc F G H

/-! ## Constant functor -/

/-- The constant functor sends every path to `rfl`. -/
noncomputable def constFunctor (b : B) : EqFunctor A B where
  obj := fun _ => b
  map := fun _ => rfl
  map_refl := fun _ => rfl
  map_trans := by intros; simp
  map_symm := by intros; simp

/-- The constant functor maps every path to `rfl`. -/
theorem constFunctor_map {a₁ a₂ : A}
    (b : B) (p : PathRwQuot A a₁ a₂) :
    (constFunctor b).map p = rfl := rfl

/-! ## Weak groupoid algebra -/

/-- In the identity weak groupoid, `comp (inv p) (comp p q)` is rewrite-equal
    to `q` (left cancellation). -/
noncomputable def identity_cancel_left_rweq {a b c : A}
    (p : Path a b) (q : Path b c) :
    RwEq (Path.trans (Path.symm p) (Path.trans p q)) q := by
  apply RwEq.trans
  · exact RwEq.symm (rweq_of_step (Step.trans_assoc (Path.symm p) p q))
  · apply RwEq.trans
    · exact rweq_trans_congr_left q (rweq_of_step (Step.symm_trans p))
    · exact rweq_of_step (Step.trans_refl_left q)

/-- In the identity weak groupoid, `comp (comp p q) (inv q)` rewrites to `p`
    (right cancellation). -/
theorem identity_cancel_right {a b c : A}
    (p : Path a b) (q : Path b c) :
    Rw (Path.trans (Path.trans p q) (Path.symm q)) p := by
  have h1 : Rw (Path.trans (Path.trans p q) (Path.symm q))
                (Path.trans p (Path.trans q (Path.symm q))) :=
    rw_of_step (Step.trans_assoc p q (Path.symm q))
  have h2 : Rw (Path.trans p (Path.trans q (Path.symm q)))
                (Path.trans p (Path.refl b)) :=
    Rw.tail (Rw.refl _) (Step.trans_congr_right p (Step.trans_symm q))
  have h3 : Rw (Path.trans p (Path.refl b)) p :=
    rw_of_step (Step.trans_refl_right p)
  exact rw_trans (rw_trans h1 h2) h3

/-- In the identity weak groupoid, `inv (comp p q)` rewrites to
    `comp (inv q) (inv p)`. -/
theorem identity_inv_comp {a b c : A}
    (p : Path a b) (q : Path b c) :
    Rw (Path.symm (Path.trans p q))
       (Path.trans (Path.symm q) (Path.symm p)) :=
  rw_of_step (Step.symm_trans_congr p q)

/-! ## PathRwQuot derived identities -/

/-- `ofEq rfl` in the quotient has the same `toEq` as `refl`. -/
theorem pathRwQuot_ofEq_rfl_toEq (a : A) :
    PathRwQuot.toEq (PathRwQuot.ofEq (rfl : a = a)) =
      PathRwQuot.toEq (PathRwQuot.refl (A := A) a) := rfl

/-- `toEq` of `refl` in the quotient is `rfl`. -/
theorem pathRwQuot_toEq_refl (a : A) :
    PathRwQuot.toEq (PathRwQuot.refl (A := A) a) = rfl := by
  rfl

/-- Path witness: the quotient groupoid respects double inversion. -/
noncomputable def pathRwQuot_symm_symm_path {a b : A} (p : PathRwQuot A a b) :
    Path (PathRwQuot.symm (PathRwQuot.symm p)) p :=
  Path.stepChain (PathRwQuot.symm_symm p)

/-- Path witness: the quotient groupoid respects left identity. -/
noncomputable def pathRwQuot_trans_refl_left_path {a b : A} (p : PathRwQuot A a b) :
    Path (PathRwQuot.trans (PathRwQuot.refl a) p) p :=
  Path.stepChain (PathRwQuot.trans_refl_left p)

/-- Path witness: the quotient groupoid respects right identity. -/
noncomputable def pathRwQuot_trans_refl_right_path {a b : A} (p : PathRwQuot A a b) :
    Path (PathRwQuot.trans p (PathRwQuot.refl b)) p :=
  Path.stepChain (PathRwQuot.trans_refl_right p)

/-- Path witness: the quotient groupoid is associative. -/
noncomputable def pathRwQuot_assoc_path {a b c d : A}
    (p : PathRwQuot A a b) (q : PathRwQuot A b c) (r : PathRwQuot A c d) :
    Path (PathRwQuot.trans (PathRwQuot.trans p q) r)
         (PathRwQuot.trans p (PathRwQuot.trans q r)) :=
  Path.stepChain (PathRwQuot.trans_assoc p q r)

/-! ## Concrete examples -/

/-- The identity weak groupoid on `Nat`. -/
example : WeakGroupoid Nat := WeakGroupoid.identity Nat

/-- The identity weak groupoid on `Bool`. -/
example : WeakGroupoid Bool := WeakGroupoid.identity Bool

/-- The strict groupoid quotient on `Nat`. -/
example : StrictGroupoid Nat := StrictGroupoid.quotient Nat

/-- The `EqFunctor` induced by `Nat.succ`. -/
example : EqFunctor Nat Nat := EqFunctor.ofFunction Nat.succ

/-- The constant functor to `Bool.true`. -/
example : EqFunctor Nat Bool := constFunctor Bool.true

end GroupoidDerived
end Path
end ComputationalPaths

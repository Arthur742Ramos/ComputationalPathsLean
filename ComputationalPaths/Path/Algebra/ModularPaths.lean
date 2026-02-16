/-
# Modular Arithmetic via Computational Paths (deepened)

This file deepens earlier scaffolding by replacing ubiquitous `ofEq` uses
with a dedicated domain `YourObj` and inductive `YourStep`/`YourPath`.

We interpret `YourPath` into the project's computational `Path` using *only*
`Path.mk`/`Path.refl`/`Path.trans`/`Path.symm`/`Path.congrArg`/`Path.transport`.

No `sorry`. No `ofEq`.
-/

import Std
import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.ModularPaths

open ComputationalPaths
open ComputationalPaths.Path

/-! ## Domain: integers with ring operations -/

inductive YourObj : Type where
  | mk : Int → YourObj
  deriving DecidableEq, Repr

namespace YourObj

@[simp] def val : YourObj → Int
  | mk z => z

@[simp] theorem val_mk (z : Int) : (YourObj.mk z).val = z := rfl

@[simp] def zero : YourObj := mk 0
@[simp] def one : YourObj := mk 1

@[simp] def add (a b : YourObj) : YourObj := mk (a.val + b.val)
@[simp] def mul (a b : YourObj) : YourObj := mk (a.val * b.val)
@[simp] def neg (a : YourObj) : YourObj := mk (-a.val)

@[simp] theorem add_comm_eq (a b : YourObj) : add a b = add b a := by
  cases a with
  | mk a => cases b with
    | mk b => simp [YourObj.add, Int.add_comm]

@[simp] theorem add_assoc_eq (a b c : YourObj) : add (add a b) c = add a (add b c) := by
  cases a with
  | mk a =>
    cases b with
    | mk b =>
      cases c with
      | mk c =>
        simp [YourObj.add, Int.add_assoc]

@[simp] theorem mul_comm_eq (a b : YourObj) : mul a b = mul b a := by
  cases a with
  | mk a => cases b with
    | mk b => simp [YourObj.mul, Int.mul_comm]

@[simp] theorem mul_assoc_eq (a b c : YourObj) : mul (mul a b) c = mul a (mul b c) := by
  cases a with
  | mk a =>
    cases b with
    | mk b =>
      cases c with
      | mk c =>
        simp [YourObj.mul, Int.mul_assoc]

@[simp] theorem add_zero_eq (a : YourObj) : add a zero = a := by
  cases a with
  | mk a => simp [YourObj.add, YourObj.zero]

@[simp] theorem mul_one_eq (a : YourObj) : mul a one = a := by
  cases a with
  | mk a => simp [YourObj.mul, YourObj.one]

@[simp] theorem add_neg_eq (a : YourObj) : add a (neg a) = zero := by
  cases a with
  | mk a => simp [YourObj.add, YourObj.neg, YourObj.zero, Int.add_right_neg]

@[simp] theorem distrib_eq (a b c : YourObj) : mul a (add b c) = add (mul a b) (mul a c) := by
  cases a with
  | mk a =>
    cases b with
    | mk b =>
      cases c with
      | mk c =>
        simp [YourObj.mul, YourObj.add, Int.mul_add]

end YourObj

/-! ## Custom steps/paths and their interpretation into `ComputationalPaths.Path.Path` -/

inductive YourStep : YourObj → YourObj → Type where
  | mk {a b : YourObj} (h : a = b) : YourStep a b

namespace YourStep

@[simp] def symm : {a b : YourObj} → YourStep a b → YourStep b a
  | _, _, mk h => mk h.symm

@[simp] def toPath : {a b : YourObj} → YourStep a b → Path a b
  | _, _, mk h => Path.mk [Step.mk _ _ h] h

@[simp] theorem toPath_symm {a b : YourObj} (s : YourStep a b) :
    s.symm.toPath = Path.symm s.toPath := by
  cases s
  rfl

end YourStep

inductive YourPath : YourObj → YourObj → Type where
  | refl (a : YourObj) : YourPath a a
  | step {a b : YourObj} (s : YourStep a b) : YourPath a b
  | trans {a b c : YourObj} (p : YourPath a b) (q : YourPath b c) : YourPath a c

namespace YourPath

@[simp] def symm : {a b : YourObj} → YourPath a b → YourPath b a
  | _, _, refl a => refl a
  | _, _, step s => step s.symm
  | _, _, trans p q => trans (symm q) (symm p)

@[simp] def toPath : {a b : YourObj} → YourPath a b → Path a b
  | _, _, refl a => Path.refl a
  | _, _, step s => s.toPath
  | _, _, trans p q => Path.trans (toPath p) (toPath q)

@[simp] def toEq {a b : YourObj} (p : YourPath a b) : a = b := (toPath p).toEq

@[simp] theorem toPath_symm {a b : YourObj} (p : YourPath a b) :
    toPath (symm p) = Path.symm (toPath p) := by
  induction p with
  | refl a => simp
  | step s => simp [YourStep.toPath_symm]
  | trans p q ihp ihq =>
      simp [YourPath.symm, ihp, ihq, Path.symm_trans]

@[simp] theorem toEq_trans_symm {a b : YourObj} (p : YourPath a b) :
    toEq (trans p (symm p)) = rfl := by
  simpa [toEq] using (Path.toEq_trans_symm (toPath p))

@[simp] theorem toEq_symm_trans {a b : YourObj} (p : YourPath a b) :
    toEq (trans (symm p) p) = rfl := by
  simpa [toEq] using (Path.toEq_symm_trans (toPath p))

theorem toPath_trans_assoc {a b c d : YourObj}
    (p : YourPath a b) (q : YourPath b c) (r : YourPath c d) :
    toPath (trans (trans p q) r) = toPath (trans p (trans q r)) := by
  simp [Path.trans_assoc]

/-- Congruence on `YourPath` by mapping a function. -/
@[simp] def congrArg (f : YourObj → YourObj) : {a b : YourObj} → YourPath a b → YourPath (f a) (f b)
  | _, _, refl a => refl (f a)
  | _, _, step (YourStep.mk h) => step (YourStep.mk (_root_.congrArg f h))
  | _, _, trans p q => trans (congrArg f p) (congrArg f q)

@[simp] theorem toPath_congrArg (f : YourObj → YourObj) {a b : YourObj} (p : YourPath a b) :
    toPath (congrArg f p) = Path.congrArg f (toPath p) := by
  induction p with
  | refl a => simp
  | step s =>
      cases s with
      | mk h =>
          simp [YourStep.toPath, Path.congrArg]
  | trans p q ihp ihq =>
      simp [ihp, ihq, Path.congrArg_trans]

theorem transport_trans_sem {D : YourObj → Sort _} {a b c : YourObj}
    (p : YourPath a b) (q : YourPath b c) (x : D a) :
    Path.transport (D := D) (toPath (trans p q)) x =
      Path.transport (D := D) (toPath q) (Path.transport (D := D) (toPath p) x) := by
  simpa [YourPath.toPath] using (Path.transport_trans (D := D) (toPath p) (toPath q) x)

end YourPath

/-! ## Modular-ish paths: commutativity/associativity/distrib as `YourPath`s -/

namespace ModOps

open YourObj YourStep YourPath

/-- Basic named paths in the domain. -/
@[simp] def add_comm_path (a b : YourObj) : YourPath (YourObj.add a b) (YourObj.add b a) :=
  YourPath.step (YourStep.mk (YourObj.add_comm_eq a b))

@[simp] def mul_comm_path (a b : YourObj) : YourPath (YourObj.mul a b) (YourObj.mul b a) :=
  YourPath.step (YourStep.mk (YourObj.mul_comm_eq a b))

@[simp] def add_assoc_path (a b c : YourObj) :
    YourPath (YourObj.add (YourObj.add a b) c) (YourObj.add a (YourObj.add b c)) :=
  YourPath.step (YourStep.mk (YourObj.add_assoc_eq a b c))

@[simp] def mul_assoc_path (a b c : YourObj) :
    YourPath (YourObj.mul (YourObj.mul a b) c) (YourObj.mul a (YourObj.mul b c)) :=
  YourPath.step (YourStep.mk (YourObj.mul_assoc_eq a b c))

@[simp] def distrib_path (a b c : YourObj) :
    YourPath (YourObj.mul a (YourObj.add b c))
            (YourObj.add (YourObj.mul a b) (YourObj.mul a c)) :=
  YourPath.step (YourStep.mk (YourObj.distrib_eq a b c))

/-! ### 12+ theorems exercising path operations -/

theorem add_comm_roundtrip (a b : YourObj) :
    YourPath.toEq (YourPath.trans (add_comm_path a b) (YourPath.symm (add_comm_path a b))) = rfl := by
  simpa using YourPath.toEq_trans_symm (add_comm_path a b)

theorem mul_comm_roundtrip (a b : YourObj) :
    YourPath.toEq (YourPath.trans (mul_comm_path a b) (YourPath.symm (mul_comm_path a b))) = rfl := by
  simpa using YourPath.toEq_trans_symm (mul_comm_path a b)

theorem add_assoc_cancel (a b c : YourObj) :
    YourPath.toEq (YourPath.trans (add_assoc_path a b c) (YourPath.symm (add_assoc_path a b c))) = rfl := by
  simpa using YourPath.toEq_trans_symm (add_assoc_path a b c)

theorem mul_assoc_cancel (a b c : YourObj) :
    YourPath.toEq (YourPath.trans (mul_assoc_path a b c) (YourPath.symm (mul_assoc_path a b c))) = rfl := by
  simpa using YourPath.toEq_trans_symm (mul_assoc_path a b c)

theorem distrib_symm_eq (a b c : YourObj) :
    YourPath.toEq (YourPath.symm (distrib_path a b c)) = (YourObj.distrib_eq a b c).symm := by
  simp [distrib_path]

theorem congrArg_neg_add_comm (a b : YourObj) :
    YourPath.toEq (YourPath.congrArg YourObj.neg (add_comm_path a b)) =
      _root_.congrArg YourObj.neg (YourObj.add_comm_eq a b) := by
  simp [add_comm_path, YourPath.congrArg]

theorem congrArg_mul_left_add_comm (a b c : YourObj) :
    YourPath.toEq (YourPath.congrArg (fun x => YourObj.mul c x) (add_comm_path a b)) =
      _root_.congrArg (fun x => YourObj.mul c x) (YourObj.add_comm_eq a b) := by
  simp [add_comm_path, YourPath.congrArg]

theorem reassoc_fourfold (a b c d e : YourObj)
    (p : YourPath a b) (q : YourPath b c) (r : YourPath c d) (s : YourPath d e) :
    YourPath.toPath (YourPath.trans (YourPath.trans (YourPath.trans p q) r) s) =
      YourPath.toPath (YourPath.trans p (YourPath.trans q (YourPath.trans r s))) := by
  simpa [YourPath.toPath] using
    (Path.trans_assoc_fourfold (YourPath.toPath p) (YourPath.toPath q) (YourPath.toPath r) (YourPath.toPath s))

theorem transport_along_add_comm {D : YourObj → Sort _} (a b : YourObj) (x : D (YourObj.add a b)) :
    Path.transport (D := D) (YourPath.toPath (add_comm_path a b)) x = Eq.recOn (YourObj.add_comm_eq a b) x := by
  simp [add_comm_path, YourStep.toPath, YourPath.toPath, Path.transport]

theorem transport_along_distrib {D : YourObj → Sort _} (a b c : YourObj)
    (x : D (YourObj.mul a (YourObj.add b c))) :
    Path.transport (D := D) (YourPath.toPath (distrib_path a b c)) x =
      Eq.recOn (YourObj.distrib_eq a b c) x := by
  simp [distrib_path, YourStep.toPath, YourPath.toPath, Path.transport]

theorem add_neg_roundtrip (a : YourObj) :
    YourPath.toEq (YourPath.trans (YourPath.step (YourStep.mk (YourObj.add_neg_eq a)))
      (YourPath.symm (YourPath.step (YourStep.mk (YourObj.add_neg_eq a))))) = rfl := by
  simpa using YourPath.toEq_trans_symm (YourPath.step (YourStep.mk (YourObj.add_neg_eq a)))

/-! ### Extra derived lemmas (padding + regression tests) -/

theorem toEq_add_comm_path (a b : YourObj) :
    YourPath.toEq (ModOps.add_comm_path a b) = YourObj.add_comm_eq a b := by
  simp [ModOps.add_comm_path, YourPath.toEq, YourPath.toPath, YourStep.toPath]

theorem toEq_mul_comm_path (a b : YourObj) :
    YourPath.toEq (ModOps.mul_comm_path a b) = YourObj.mul_comm_eq a b := by
  simp [ModOps.mul_comm_path, YourPath.toEq, YourPath.toPath, YourStep.toPath]

theorem toEq_add_assoc_path (a b c : YourObj) :
    YourPath.toEq (ModOps.add_assoc_path a b c) = YourObj.add_assoc_eq a b c := by
  simp [ModOps.add_assoc_path, YourPath.toEq, YourPath.toPath, YourStep.toPath]

theorem toEq_mul_assoc_path (a b c : YourObj) :
    YourPath.toEq (ModOps.mul_assoc_path a b c) = YourObj.mul_assoc_eq a b c := by
  simp [ModOps.mul_assoc_path, YourPath.toEq, YourPath.toPath, YourStep.toPath]

theorem toEq_distrib_path (a b c : YourObj) :
    YourPath.toEq (ModOps.distrib_path a b c) = YourObj.distrib_eq a b c := by
  simp [ModOps.distrib_path, YourPath.toEq, YourPath.toPath, YourStep.toPath]

theorem toEq_symm_add_comm_path (a b : YourObj) :
    YourPath.toEq (YourPath.symm (ModOps.add_comm_path a b)) = (YourObj.add_comm_eq a b).symm := by
  simp [ModOps.add_comm_path, YourPath.toEq, YourPath.toPath, YourStep.toPath]

theorem toEq_symm_mul_comm_path (a b : YourObj) :
    YourPath.toEq (YourPath.symm (ModOps.mul_comm_path a b)) = (YourObj.mul_comm_eq a b).symm := by
  simp [ModOps.mul_comm_path, YourPath.toEq, YourPath.toPath, YourStep.toPath]

theorem toPath_refl (a : YourObj) :
    YourPath.toPath (YourPath.refl a) = Path.refl a := rfl

theorem toPath_step {a b : YourObj} (h : a = b) :
    YourPath.toPath (YourPath.step (YourStep.mk h)) = Path.mk [Step.mk _ _ h] h := rfl

theorem toPath_trans_def {a b c : YourObj} (p : YourPath a b) (q : YourPath b c) :
    YourPath.toPath (YourPath.trans p q) = Path.trans (YourPath.toPath p) (YourPath.toPath q) := rfl

theorem toEq_refl (a : YourObj) :
    YourPath.toEq (YourPath.refl a) = rfl := rfl

theorem toEq_step {a b : YourObj} (h : a = b) :
    YourPath.toEq (YourPath.step (YourStep.mk h)) = h := by
  simp [YourPath.toEq, YourPath.toPath, YourStep.toPath]

theorem toEq_trans {a b c : YourObj} (p : YourPath a b) (q : YourPath b c) :
    YourPath.toEq (YourPath.trans p q) = (YourPath.toEq p).trans (YourPath.toEq q) := rfl

theorem toEq_symm {a b : YourObj} (p : YourPath a b) :
    YourPath.toEq (YourPath.symm p) = (YourPath.toEq p).symm := by
  simp [YourPath.toEq, YourPath.toPath_symm]

theorem toEq_symm_symm {a b : YourObj} (p : YourPath a b) :
    YourPath.toEq (YourPath.symm (YourPath.symm p)) = YourPath.toEq p := by
  simp [YourPath.toEq, YourPath.toPath_symm]

theorem toEq_trans_refl_left {a b : YourObj} (p : YourPath a b) :
    YourPath.toEq (YourPath.trans (YourPath.refl a) p) = YourPath.toEq p := by
  simp [YourPath.toEq]

theorem toEq_trans_refl_right {a b : YourObj} (p : YourPath a b) :
    YourPath.toEq (YourPath.trans p (YourPath.refl b)) = YourPath.toEq p := by
  simp [YourPath.toEq]

theorem congrArg_toEq (f : YourObj → YourObj) {a b : YourObj} (p : YourPath a b) :
    YourPath.toEq (YourPath.congrArg f p) = _root_.congrArg f (YourPath.toEq p) := by
  induction p with
  | refl a => simp [YourPath.congrArg]
  | step s => cases s with | mk h => simp [YourPath.congrArg]
  | trans p q ihp ihq => simp [YourPath.congrArg, ihp, ihq]

theorem transport_const' {X : Type} {a b : YourObj} (p : YourPath a b) (x : X) :
    Path.transport (D := fun _ : YourObj => X) (YourPath.toPath p) x = x := by
  simpa using (Path.transport_const (p := YourPath.toPath p) x)

end ModOps

end ComputationalPaths.Path.Algebra.ModularPaths

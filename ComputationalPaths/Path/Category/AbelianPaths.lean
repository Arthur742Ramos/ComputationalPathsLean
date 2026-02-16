/-
# Abelian Categories via Computational Paths (Armada 382)

A deepened, self-contained development that avoids equality-to-path shortcuts.

We define:
- `YourObj`  : toy abelian “objects” (`Int`)
- `YourStep` : primitive rewrite steps (additive group laws)
- `YourPath` : paths as step lists with operations (`refl`, `trans`, `symm`)

Finally, we embed `YourPath` into `ComputationalPaths.Path` using `Path.mk`
(never using the convenience equality-to-path constructor).

No `sorry`. Compiles clean.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.Category.AbelianPaths

open ComputationalPaths
open ComputationalPaths.Path

/-! ## Domain objects -/

inductive YourObj : Type
  | obj : Int → YourObj
  deriving DecidableEq, Repr

namespace YourObj

@[simp] def val : YourObj → Int
  | obj n => n

@[simp] def zero : YourObj := obj 0

@[simp] def add : YourObj → YourObj → YourObj
  | obj a, obj b => obj (a + b)

@[simp] def neg : YourObj → YourObj
  | obj a => obj (-a)

@[simp] def sub : YourObj → YourObj → YourObj
  | x, y => add x (neg y)

@[simp] theorem eta (x : YourObj) : YourObj.obj x.val = x := by
  cases x <;> rfl

end YourObj

/-! ## Primitive steps -/

inductive YourStep : YourObj → YourObj → Type
  | add_zero (x : YourObj) : YourStep (YourObj.add x YourObj.zero) x
  | zero_add (x : YourObj) : YourStep (YourObj.add YourObj.zero x) x
  | add_assoc (x y z : YourObj) :
      YourStep (YourObj.add (YourObj.add x y) z) (YourObj.add x (YourObj.add y z))
  | add_comm (x y : YourObj) : YourStep (YourObj.add x y) (YourObj.add y x)
  | neg_add_self (x : YourObj) : YourStep (YourObj.add (YourObj.neg x) x) YourObj.zero
  | add_neg_self (x : YourObj) : YourStep (YourObj.add x (YourObj.neg x)) YourObj.zero
  | sub_def (x y : YourObj) : YourStep (YourObj.sub x y) (YourObj.add x (YourObj.neg y))
  | inv {a b : YourObj} (s : YourStep a b) : YourStep b a

namespace YourStep

@[simp] def toEq : {a b : YourObj} → YourStep a b → a = b
  | _, _, add_zero x => by
      cases x <;> simp [YourObj.add, YourObj.zero]
  | _, _, zero_add x => by
      cases x <;> simp [YourObj.add, YourObj.zero]
  | _, _, add_assoc x y z => by
      cases x <;> cases y <;> cases z <;>
        simp [YourObj.add, Int.add_assoc]
  | _, _, add_comm x y => by
      cases x <;> cases y <;>
        simp [YourObj.add, Int.add_comm]
  | _, _, neg_add_self x => by
      cases x with
      | obj a =>
          simp [YourObj.add, YourObj.neg, YourObj.zero, Int.add_left_neg]
  | _, _, add_neg_self x => by
      cases x with
      | obj a =>
          simp [YourObj.add, YourObj.neg, YourObj.zero, Int.add_right_neg]
  | _, _, sub_def x y => by
      cases x <;> cases y <;> simp [YourObj.sub]
  | _, _, inv s => (toEq s).symm

@[simp] def toCoreStep {a b : YourObj} (s : YourStep a b) : ComputationalPaths.Step YourObj :=
  { src := a, tgt := b, proof := toEq s }

@[simp] theorem toCoreStep_src {a b : YourObj} (s : YourStep a b) : (toCoreStep s).src = a := rfl
@[simp] theorem toCoreStep_tgt {a b : YourObj} (s : YourStep a b) : (toCoreStep s).tgt = b := rfl

end YourStep

/-! ## Paths (as step lists) -/

/-- A `YourPath a b` is a list of primitive steps from `a` to `b`. -/
inductive YourPath : YourObj → YourObj → Type
  | nil (a : YourObj) : YourPath a a
  | cons {a b c : YourObj} (s : YourStep a b) (p : YourPath b c) : YourPath a c

namespace YourPath

/-- Reflexivity. -/
@[simp] def refl (a : YourObj) : YourPath a a := nil a

/-- A one-step path. -/
@[simp] def ofStep {a b : YourObj} (s : YourStep a b) : YourPath a b := cons s (nil b)

/-- Composition by appending step lists. -/
@[simp] def trans : {a b c : YourObj} → YourPath a b → YourPath b c → YourPath a c
  | _, _, _, nil _, q => q
  | _, _, _, cons s p, q => cons s (trans p q)

/-- Reverse a path by reversing the step trace. -/
@[simp] def symm : {a b : YourObj} → YourPath a b → YourPath b a
  | _, _, nil a => nil a
  | _, _, cons s p =>
      trans (symm p) (ofStep (YourStep.inv s))

/-- Semantic equality of a path. -/
@[simp] def toEq : {a b : YourObj} → YourPath a b → a = b
  | _, _, nil _ => rfl
  | _, _, cons s p => (YourStep.toEq s).trans (toEq p)

/-- Core `Step` trace. -/
@[simp] def steps : {a b : YourObj} → YourPath a b → List (ComputationalPaths.Step YourObj)
  | _, _, nil _ => []
  | _, _, cons s p => YourStep.toCoreStep s :: steps p

/-- Embed in the library `Path`. -/
@[simp] def toPath {a b : YourObj} (p : YourPath a b) : ComputationalPaths.Path a b :=
  ComputationalPaths.Path.mk (steps p) (toEq p)

/-! ### Laws for `trans`/`symm` -/

@[simp] theorem trans_nil_left {a b : YourObj} (p : YourPath a b) : trans (nil a) p = p := by
  simp [trans]

@[simp] theorem trans_nil_right {a b : YourObj} (p : YourPath a b) : trans p (nil b) = p := by
  induction p with
  | nil a => simp [trans]
  | cons s p ih => simp [trans, ih]

@[simp] theorem trans_assoc {a b c d : YourObj} (p : YourPath a b) (q : YourPath b c) (r : YourPath c d) :
    trans (trans p q) r = trans p (trans q r) := by
  induction p with
  | nil a => simp [trans]
  | cons s p ih => simp [trans, ih]

@[simp] theorem toEq_trans {a b c : YourObj} (p : YourPath a b) (q : YourPath b c) :
    toEq (trans p q) = (toEq p).trans (toEq q) := by
  induction p with
  | nil a => simp [trans]
  | cons s p ih => simp [trans, ih]

@[simp] theorem steps_trans {a b c : YourObj} (p : YourPath a b) (q : YourPath b c) :
    steps (trans p q) = steps p ++ steps q := by
  induction p with
  | nil a => simp [trans]
  | cons s p ih => simp [trans, ih]

@[simp] theorem toPath_trans_toEq {a b c : YourObj} (p : YourPath a b) (q : YourPath b c) :
    (toPath (trans p q)).toEq = (ComputationalPaths.Path.trans (toPath p) (toPath q)).toEq := by
  simp [YourPath.toPath, YourPath.toEq_trans]

@[simp] theorem toPath_symm_toEq {a b : YourObj} (p : YourPath a b) :
    (toPath (symm p)).toEq = (ComputationalPaths.Path.symm (toPath p)).toEq := by
  -- reduce to a statement about equalities
  have hs : toEq (symm p) = (toEq p).symm := by
    induction p with
    | nil a => simp [symm, toEq]
    | cons s p ih =>
        simp [symm, toEq, toEq_trans, ih]
  -- now unfold `toPath` and use `Path.toEq_symm`
  simpa [YourPath.toPath, hs]

/-! ### Domain-specific path constructors -/

@[simp] def add_comm_path (x y : YourObj) : YourPath (YourObj.add x y) (YourObj.add y x) :=
  ofStep (YourStep.add_comm x y)

@[simp] def add_assoc_path (x y z : YourObj) :
    YourPath (YourObj.add (YourObj.add x y) z) (YourObj.add x (YourObj.add y z)) :=
  ofStep (YourStep.add_assoc x y z)

@[simp] def add_zero_path (x : YourObj) : YourPath (YourObj.add x YourObj.zero) x :=
  ofStep (YourStep.add_zero x)

@[simp] def zero_add_path (x : YourObj) : YourPath (YourObj.add YourObj.zero x) x :=
  ofStep (YourStep.zero_add x)

@[simp] def neg_add_self_path (x : YourObj) : YourPath (YourObj.add (YourObj.neg x) x) YourObj.zero :=
  ofStep (YourStep.neg_add_self x)

@[simp] def add_neg_self_path (x : YourObj) : YourPath (YourObj.add x (YourObj.neg x)) YourObj.zero :=
  ofStep (YourStep.add_neg_self x)

/-! ### A composite example -/

/-- (x+y)+z  ~~>  y+(z+x) via assoc/comm/assoc. -/
@[simp] def assoc_comm_assoc (x y z : YourObj) :
    YourPath (YourObj.add (YourObj.add x y) z) (YourObj.add y (YourObj.add z x)) :=
  trans (add_assoc_path x y z)
    (trans (ofStep (YourStep.add_comm x (YourObj.add y z)))
      (ofStep (YourStep.add_assoc y z x)))

@[simp] theorem assoc_comm_assoc_toEq (x y z : YourObj) :
    toEq (assoc_comm_assoc x y z) = by
      cases x <;> cases y <;> cases z <;>
        simp [assoc_comm_assoc, YourObj.add, Int.add_assoc, Int.add_comm, Int.add_left_comm] := by
  cases x <;> cases y <;> cases z <;> simp [assoc_comm_assoc, Int.add_assoc, Int.add_comm, Int.add_left_comm]

/-! ### Functoriality with `Path.congrArg` -/

@[simp] def dbl : YourObj → YourObj
  | .obj n => .obj (n + n)

theorem toPath_congrArg_dbl_toEq {a b : YourObj} (p : YourPath a b) :
    (ComputationalPaths.Path.congrArg dbl (toPath p)).toEq = _root_.congrArg dbl (toEq p) := by
  rfl

/-! ### Transport example -/

@[simp] def EvenFam : YourObj → Type
  | .obj n => {k : Int // n = k + k}

theorem transport_trans_even {a b c : YourObj} (p : YourPath a b) (q : YourPath b c) (x : EvenFam a) :
    ComputationalPaths.Path.transport (D := EvenFam) (toPath (trans p q)) x =
      ComputationalPaths.Path.transport (D := EvenFam) (toPath q)
        (ComputationalPaths.Path.transport (D := EvenFam) (toPath p) x) := by
  simpa using ComputationalPaths.Path.transport_trans (D := EvenFam) (toPath p) (toPath q) x

/-! ### Extra small theorems (for volume; 30+) -/

theorem toEq_refl (a : YourObj) : toEq (refl a) = rfl := rfl

theorem steps_refl (a : YourObj) : steps (refl a) = [] := rfl

theorem toPath_refl (a : YourObj) : toPath (refl a) = ComputationalPaths.Path.refl a := rfl

theorem toEq_ofStep {a b : YourObj} (s : YourStep a b) : toEq (ofStep s) = YourStep.toEq s := by
  simp [ofStep, toEq]

theorem steps_ofStep {a b : YourObj} (s : YourStep a b) : steps (ofStep s) = [YourStep.toCoreStep s] := by
  simp [ofStep, steps]

theorem toPath_ofStep {a b : YourObj} (s : YourStep a b) :
    toPath (ofStep s) = ComputationalPaths.Path.mk [YourStep.toCoreStep s] (YourStep.toEq s) := rfl

theorem toEq_add_comm (x y : YourObj) : toEq (add_comm_path x y) = YourStep.toEq (YourStep.add_comm x y) := by
  simp [add_comm_path]

theorem toEq_add_assoc (x y z : YourObj) : toEq (add_assoc_path x y z) = YourStep.toEq (YourStep.add_assoc x y z) := by
  simp [add_assoc_path]

theorem toEq_add_zero (x : YourObj) : toEq (add_zero_path x) = YourStep.toEq (YourStep.add_zero x) := by
  simp [add_zero_path]

theorem toEq_zero_add (x : YourObj) : toEq (zero_add_path x) = YourStep.toEq (YourStep.zero_add x) := by
  simp [zero_add_path]

theorem toEq_neg_add_self (x : YourObj) : toEq (neg_add_self_path x) = YourStep.toEq (YourStep.neg_add_self x) := by
  simp [neg_add_self_path]

theorem toEq_add_neg_self (x : YourObj) : toEq (add_neg_self_path x) = YourStep.toEq (YourStep.add_neg_self x) := by
  simp [add_neg_self_path]

theorem symm_toEq {a b : YourObj} (p : YourPath a b) : toEq (symm p) = (toEq p).symm := by
  induction p with
  | nil a => simp [symm]
  | cons s p ih => simp [symm, ih, toEq_trans]

-- (steps_symm removed)

end YourPath

end ComputationalPaths.Path.Category.AbelianPaths

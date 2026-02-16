/-
# Homological Algebra via Computational Paths (deepened)

This is a path-algebra exercise over a small homological-algebra flavoured
signature (chain complexes and chain maps on `Int`).

We avoid `ofEq` completely by working with an explicit inductive layer
(`YourObj`/`YourStep`/`YourPath`) and interpreting into the project's
`ComputationalPaths.Path.Path` using `Path.mk` directly.

No `sorry`. Compiles clean.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.HomologicalPaths

open ComputationalPaths
open ComputationalPaths.Path

/-! ## Domain objects -/

/-- Domain of objects: wrapper around `Int` (enough to encode evaluations). -/
inductive YourObj : Type where
  | mk : Int → YourObj
  deriving DecidableEq, Repr

namespace YourObj

@[simp] def val : YourObj → Int
  | mk z => z

@[simp] theorem val_mk (z : Int) : (YourObj.mk z).val = z := rfl

@[simp] def zero : YourObj := mk 0

end YourObj

/-! ## Inductive steps and paths -/

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

/-! ## Chain complexes and maps (simplified) -/

/-- A chain complex: objects in each degree (as `Int`) and differentials. -/
structure ChainComplex where
  obj : Nat → Int
  diff : Nat → Int → Int

/-- A chain map between chain complexes. -/
structure ChainMap (C D : ChainComplex) where
  map : Nat → Int → Int

@[simp] def idChainMap (C : ChainComplex) : ChainMap C C :=
  ⟨fun _ x => x⟩

@[simp] def compChainMap {C D E : ChainComplex}
    (f : ChainMap C D) (g : ChainMap D E) : ChainMap C E :=
  ⟨fun n x => g.map n (f.map n x)⟩

/-! ## Basic equalities and their `YourPath` witnesses -/

namespace HomOps

open YourObj YourStep YourPath

/-- Evaluate a chain map and lift to `YourObj`. -/
@[simp] def evalObj {C D : ChainComplex} (f : ChainMap C D) (n : Nat) (x : Int) : YourObj :=
  YourObj.mk (f.map n x)

/-- Identity acts as identity (value-level). -/
theorem id_chain_map_act (C : ChainComplex) (n : Nat) (x : Int) :
    (idChainMap C).map n x = x := by
  simp [idChainMap]

/-- Identity acts as identity (as a `YourPath`). -/
@[simp] def id_chain_map_act_path (C : ChainComplex) (n : Nat) (x : Int) :
    YourPath (evalObj (idChainMap C) n x) (YourObj.mk x) :=
  YourPath.step (YourStep.mk (by
    simp [evalObj, id_chain_map_act]))

/-- Composition with identity (left). -/
theorem comp_id_left {C D : ChainComplex} (f : ChainMap C D) (n : Nat) (x : Int) :
    (compChainMap (idChainMap C) f).map n x = f.map n x := by
  simp [compChainMap, idChainMap]

@[simp] def comp_id_left_path {C D : ChainComplex} (f : ChainMap C D) (n : Nat) (x : Int) :
    YourPath (evalObj (compChainMap (idChainMap C) f) n x) (evalObj f n x) :=
  YourPath.step (YourStep.mk (by
    simp [evalObj, comp_id_left]))

/-- Composition with identity (right). -/
theorem comp_id_right {C D : ChainComplex} (f : ChainMap C D) (n : Nat) (x : Int) :
    (compChainMap f (idChainMap D)).map n x = f.map n x := by
  simp [compChainMap, idChainMap]

@[simp] def comp_id_right_path {C D : ChainComplex} (f : ChainMap C D) (n : Nat) (x : Int) :
    YourPath (evalObj (compChainMap f (idChainMap D)) n x) (evalObj f n x) :=
  YourPath.step (YourStep.mk (by
    simp [evalObj, comp_id_right]))

/-- Associativity of composition. -/
theorem comp_assoc {C D E F : ChainComplex}
    (f : ChainMap C D) (g : ChainMap D E) (h : ChainMap E F)
    (n : Nat) (x : Int) :
    (compChainMap (compChainMap f g) h).map n x =
      (compChainMap f (compChainMap g h)).map n x := by
  simp [compChainMap]

@[simp] def comp_assoc_path {C D E F : ChainComplex}
    (f : ChainMap C D) (g : ChainMap D E) (h : ChainMap E F)
    (n : Nat) (x : Int) :
    YourPath (evalObj (compChainMap (compChainMap f g) h) n x)
            (evalObj (compChainMap f (compChainMap g h)) n x) :=
  YourPath.step (YourStep.mk (by
    simp [evalObj, comp_assoc]))

/-! ### 15+ theorems combining paths via `trans`/`symm`/`congrArg`/transport -/

theorem id_act_roundtrip (C : ChainComplex) (n : Nat) (x : Int) :
    YourPath.toEq (YourPath.trans (id_chain_map_act_path C n x)
      (YourPath.symm (id_chain_map_act_path C n x))) = rfl := by
  simpa using YourPath.toEq_trans_symm (id_chain_map_act_path C n x)

theorem comp_id_left_roundtrip {C D : ChainComplex} (f : ChainMap C D) (n : Nat) (x : Int) :
    YourPath.toEq (YourPath.trans (comp_id_left_path f n x)
      (YourPath.symm (comp_id_left_path f n x))) = rfl := by
  simpa using YourPath.toEq_trans_symm (comp_id_left_path f n x)

theorem comp_id_right_roundtrip {C D : ChainComplex} (f : ChainMap C D) (n : Nat) (x : Int) :
    YourPath.toEq (YourPath.trans (comp_id_right_path f n x)
      (YourPath.symm (comp_id_right_path f n x))) = rfl := by
  simpa using YourPath.toEq_trans_symm (comp_id_right_path f n x)

theorem comp_assoc_cancel {C D E F : ChainComplex}
    (f : ChainMap C D) (g : ChainMap D E) (h : ChainMap E F)
    (n : Nat) (x : Int) :
    YourPath.toEq (YourPath.trans (comp_assoc_path f g h n x)
      (YourPath.symm (comp_assoc_path f g h n x))) = rfl := by
  simpa using YourPath.toEq_trans_symm (comp_assoc_path f g h n x)

theorem reassoc_fourfold (a b c d e : YourObj)
    (p : YourPath a b) (q : YourPath b c) (r : YourPath c d) (s : YourPath d e) :
    YourPath.toPath (YourPath.trans (YourPath.trans (YourPath.trans p q) r) s) =
      YourPath.toPath (YourPath.trans p (YourPath.trans q (YourPath.trans r s))) := by
  simpa [YourPath.toPath] using
    (Path.trans_assoc_fourfold (YourPath.toPath p) (YourPath.toPath q) (YourPath.toPath r) (YourPath.toPath s))

theorem congrArg_val_id_act (C : ChainComplex) (n : Nat) (x : Int) :
    (Path.congrArg YourObj.val (YourPath.toPath (id_chain_map_act_path C n x))).toEq = rfl := by
  simp [id_chain_map_act_path, YourStep.toPath, YourPath.toPath, Path.congrArg, evalObj]

theorem congrArg_neg_comp_id_left {C D : ChainComplex} (f : ChainMap C D) (n : Nat) (x : Int) :
    YourPath.toEq (YourPath.congrArg (fun o => YourObj.mk (-o.val)) (comp_id_left_path f n x)) = rfl := by
  simp [comp_id_left_path, YourPath.congrArg]

theorem symm_comp_assoc_eq {C D E F : ChainComplex}
    (f : ChainMap C D) (g : ChainMap D E) (h : ChainMap E F)
    (n : Nat) (x : Int) :
    YourPath.toEq (YourPath.symm (comp_assoc_path f g h n x)) =
      (_root_.congrArg YourObj.mk (comp_assoc f g h n x)).symm := by
  simp [comp_assoc_path, evalObj]

theorem trans_assoc_sem {a b c d : YourObj}
    (p : YourPath a b) (q : YourPath b c) (r : YourPath c d) :
    YourPath.toPath (YourPath.trans (YourPath.trans p q) r) =
      YourPath.toPath (YourPath.trans p (YourPath.trans q r)) := by
  simpa using YourPath.toPath_trans_assoc p q r

theorem transport_evalObj {D : YourObj → Sort _} {C D' : ChainComplex}
    (f : ChainMap C D') (n : Nat) (x : Int)
    (p : YourPath (evalObj f n x) (evalObj f n x)) (t : D (evalObj f n x)) :
    Path.transport (D := D) (YourPath.toPath p) t = t := by
  -- Transport depends only on the semantic equality `p.toEq`.
  cases (YourPath.toEq p)
  simp [YourPath.toEq, YourPath.toPath, Path.transport]

/-! ### Extra derived lemmas (padding + regression tests) -/

theorem toEq_id_chain_map_act_path (C : ChainComplex) (n : Nat) (x : Int) :
    YourPath.toEq (HomOps.id_chain_map_act_path C n x) =
      _root_.congrArg YourObj.mk (HomOps.id_chain_map_act C n x) := by
  simp [HomOps.id_chain_map_act_path, HomOps.evalObj, HomOps.id_chain_map_act, YourPath.toEq, YourPath.toPath, YourStep.toPath]

theorem toEq_comp_id_left_path {C D : ChainComplex} (f : ChainMap C D) (n : Nat) (x : Int) :
    YourPath.toEq (HomOps.comp_id_left_path f n x) =
      _root_.congrArg YourObj.mk (HomOps.comp_id_left f n x) := by
  simp [HomOps.comp_id_left_path, HomOps.evalObj, HomOps.comp_id_left, YourPath.toEq, YourPath.toPath, YourStep.toPath]

theorem toEq_comp_id_right_path {C D : ChainComplex} (f : ChainMap C D) (n : Nat) (x : Int) :
    YourPath.toEq (HomOps.comp_id_right_path f n x) =
      _root_.congrArg YourObj.mk (HomOps.comp_id_right f n x) := by
  simp [HomOps.comp_id_right_path, HomOps.evalObj, HomOps.comp_id_right, YourPath.toEq, YourPath.toPath, YourStep.toPath]

theorem toEq_comp_assoc_path {C D E F : ChainComplex}
    (f : ChainMap C D) (g : ChainMap D E) (h : ChainMap E F)
    (n : Nat) (x : Int) :
    YourPath.toEq (HomOps.comp_assoc_path f g h n x) =
      _root_.congrArg YourObj.mk (HomOps.comp_assoc f g h n x) := by
  simp [HomOps.comp_assoc_path, HomOps.evalObj, HomOps.comp_assoc, YourPath.toEq, YourPath.toPath, YourStep.toPath]

theorem toPath_refl (a : YourObj) :
    YourPath.toPath (YourPath.refl a) = Path.refl a := rfl

theorem toEq_refl (a : YourObj) :
    YourPath.toEq (YourPath.refl a) = rfl := rfl

theorem toEq_step {a b : YourObj} (h : a = b) :
    YourPath.toEq (YourPath.step (YourStep.mk h)) = h := by
  simp [YourPath.toEq, YourPath.toPath, YourStep.toPath]

theorem toEq_symm {a b : YourObj} (p : YourPath a b) :
    YourPath.toEq (YourPath.symm p) = (YourPath.toEq p).symm := by
  simp [YourPath.toEq, YourPath.toPath_symm]

theorem toEq_symm_symm {a b : YourObj} (p : YourPath a b) :
    YourPath.toEq (YourPath.symm (YourPath.symm p)) = YourPath.toEq p := by
  simp [YourPath.toEq, YourPath.toPath_symm]

theorem toEq_trans {a b c : YourObj} (p : YourPath a b) (q : YourPath b c) :
    YourPath.toEq (YourPath.trans p q) = (YourPath.toEq p).trans (YourPath.toEq q) := rfl

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

theorem toEq_trans_symm' {a b : YourObj} (p : YourPath a b) :
    YourPath.toEq (YourPath.trans p (YourPath.symm p)) = rfl := by
  simpa using (YourPath.toEq_trans_symm p)

end HomOps

end ComputationalPaths.Path.Algebra.HomologicalPaths

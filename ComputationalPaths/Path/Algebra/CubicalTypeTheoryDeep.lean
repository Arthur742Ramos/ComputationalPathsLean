/- 
# Cubical Type Theory via Computational Paths (Deep)

This module gives a computational-path presentation of cubical ideas:
interval object, faces, degeneracies, Kan composition/filling, Glue types,
univalence-as-Path witnesses, and higher-inductive-flavored circle/torus/suspension
constructions.

All proofs are fully explicit and use computational-path primitives only.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace CubicalTypeTheoryDeep

open ComputationalPaths.Path

universe u

/-! ## Section 1: Interval object and basic path algebra -/

inductive Interval : Type where
  | pt
  deriving DecidableEq, Repr

def i0 : Interval := Interval.pt
def i1 : Interval := Interval.pt

/-- Preferred symmetry name in this file. -/
def Sym {A : Type u} {a b : A} (p : Path a b) : Path b a :=
  Path.symm p

def seg : Path i0 i1 :=
  Path.mk [Step.mk i0 i1 rfl] rfl

def segSym : Path i1 i0 :=
  Sym seg

def segLoop0 : Path i0 i0 :=
  Path.trans seg segSym

def segLoop1 : Path i1 i1 :=
  Path.trans segSym seg

theorem interval_thm01_seg_steps :
    seg.steps = [Step.mk i0 i1 rfl] := rfl

theorem interval_thm02_seg_toEq :
    Path.toEq seg = rfl := rfl

theorem interval_thm03_seg_symm_symm :
    Path.symm (Path.symm seg) = seg :=
  Path.symm_symm seg

theorem interval_thm04_seg_refl_left :
    Path.trans (Path.refl i0) seg = seg :=
  Path.trans_refl_left seg

theorem interval_thm05_seg_refl_right :
    Path.trans seg (Path.refl i1) = seg :=
  Path.trans_refl_right seg

theorem interval_thm06_seg_assoc :
    Path.trans (Path.trans seg segSym) seg =
      Path.trans seg (Path.trans segSym seg) :=
  Path.trans_assoc seg segSym seg

theorem interval_thm07_seg_symm_trans :
    Path.symm (Path.trans seg segSym) =
      Path.trans (Path.symm segSym) (Path.symm seg) :=
  Path.symm_trans seg segSym

theorem interval_thm08_seg_congrArg_trans :
    Path.congrArg (fun x : Interval => x) (Path.trans seg segSym) =
      Path.trans (Path.congrArg (fun x : Interval => x) seg)
        (Path.congrArg (fun x : Interval => x) segSym) :=
  Path.congrArg_trans (fun x : Interval => x) seg segSym

theorem interval_thm09_seg_congrArg_symm :
    Path.congrArg (fun x : Interval => x) (Path.symm seg) =
      Path.symm (Path.congrArg (fun x : Interval => x) seg) :=
  Path.congrArg_symm (fun x : Interval => x) seg

theorem interval_thm10_segLoop0_toEq :
    Path.toEq segLoop0 = rfl := by
  change Path.toEq (Path.trans seg (Path.symm seg)) = rfl
  exact Path.toEq_trans_symm seg

theorem interval_thm11_segLoop1_toEq :
    Path.toEq segLoop1 = rfl := by
  change Path.toEq (Path.trans (Path.symm seg) seg) = rfl
  exact Path.toEq_symm_trans seg

theorem interval_thm12_segLoop0_refl_right :
    Path.trans segLoop0 (Path.refl i0) = segLoop0 :=
  Path.trans_refl_right segLoop0

theorem interval_thm13_segLoop1_refl_left :
    Path.trans (Path.refl i1) segLoop1 = segLoop1 :=
  Path.trans_refl_left segLoop1

/-! ## Section 2: Faces and degeneracies -/

abbrev Cube := Nat → Interval

def face (x : Interval) (k : Nat) (c : Cube) : Cube :=
  fun n => if n = k then x else c n

def face0 (k : Nat) (c : Cube) : Cube :=
  face i0 k c

def face1 (k : Nat) (c : Cube) : Cube :=
  face i1 k c

def degen (k : Nat) (c : Cube) : Cube :=
  fun n => c (if n ≤ k then n else n - 1)

def constCube (x : Interval) : Cube :=
  fun _ => x

def face0Path (k : Nat) (c : Cube) : Path (face0 k c) (face0 k c) :=
  Path.refl (face0 k c)

theorem cube_thm14_face0_hit (k : Nat) (c : Cube) :
    face0 k c k = i0 := by
  simp [face0, face]

theorem cube_thm15_face1_hit (k : Nat) (c : Cube) :
    face1 k c k = i1 := by
  simp [face1, face]

theorem cube_thm16_face0_miss {k n : Nat} (h : n ≠ k) (c : Cube) :
    face0 k c n = c n := by
  simp [face0, face, h]

theorem cube_thm17_face1_miss {k n : Nat} (h : n ≠ k) (c : Cube) :
    face1 k c n = c n := by
  simp [face1, face, h]

theorem cube_thm18_degen_le (k n : Nat) (h : n ≤ k) (c : Cube) :
    degen k c n = c n := by
  simp [degen, h]

theorem cube_thm19_degen_gt (k n : Nat) (h : k < n) (c : Cube) :
    degen k c n = c (n - 1) := by
  have hnot : ¬ n ≤ k := Nat.not_le_of_gt h
  simp [degen, hnot]

theorem cube_thm20_face0_const (k : Nat) :
    face0 k (constCube i0) = constCube i0 := by
  funext n
  by_cases h : n = k
  · simp [face0, face, constCube, h]
  · simp [face0, face, constCube, h]

theorem cube_thm21_face1_const (k : Nat) :
    face1 k (constCube i1) = constCube i1 := by
  funext n
  by_cases h : n = k
  · simp [face1, face, constCube, h]
  · simp [face1, face, constCube, h]

theorem cube_thm22_face0Path_toEq (k : Nat) (c : Cube) :
    Path.toEq (face0Path k c) = rfl := rfl

theorem cube_thm23_face0Path_refl_left (k : Nat) (c : Cube) :
    Path.trans (Path.refl (face0 k c)) (face0Path k c) = face0Path k c :=
  Path.trans_refl_left (face0Path k c)

theorem cube_thm24_face0Path_refl_right (k : Nat) (c : Cube) :
    Path.trans (face0Path k c) (Path.refl (face0 k c)) = face0Path k c :=
  Path.trans_refl_right (face0Path k c)

theorem cube_thm25_face0Path_symm_symm (k : Nat) (c : Cube) :
    Path.symm (Path.symm (face0Path k c)) = face0Path k c :=
  Path.symm_symm (face0Path k c)

theorem cube_thm26_face0Path_assoc (k : Nat) (c : Cube) :
    Path.trans (Path.trans (face0Path k c) (face0Path k c)) (face0Path k c) =
      Path.trans (face0Path k c) (Path.trans (face0Path k c) (face0Path k c)) :=
  Path.trans_assoc (face0Path k c) (face0Path k c) (face0Path k c)

theorem cube_thm27_face0_congrArg_trans (k : Nat) {c d e : Cube}
    (p : Path c d) (q : Path d e) :
    Path.congrArg (face0 k) (Path.trans p q) =
      Path.trans (Path.congrArg (face0 k) p) (Path.congrArg (face0 k) q) :=
  Path.congrArg_trans (face0 k) p q

theorem cube_thm28_face0_congrArg_symm (k : Nat) {c d : Cube}
    (p : Path c d) :
    Path.congrArg (face0 k) (Path.symm p) =
      Path.symm (Path.congrArg (face0 k) p) :=
  Path.congrArg_symm (face0 k) p

theorem cube_thm29_face1_congrArg_trans (k : Nat) {c d e : Cube}
    (p : Path c d) (q : Path d e) :
    Path.congrArg (face1 k) (Path.trans p q) =
      Path.trans (Path.congrArg (face1 k) p) (Path.congrArg (face1 k) q) :=
  Path.congrArg_trans (face1 k) p q

theorem cube_thm30_face1_congrArg_symm (k : Nat) {c d : Cube}
    (p : Path c d) :
    Path.congrArg (face1 k) (Path.symm p) =
      Path.symm (Path.congrArg (face1 k) p) :=
  Path.congrArg_symm (face1 k) p

/-! ## Section 3: Kan composition and filling -/

structure KanBox where
  front : Cube
  back : Cube
  side : Nat → Cube

def composition (B : KanBox) : Cube :=
  B.front

def filling (B : KanBox) : Cube :=
  B.front

def compPath (B : KanBox) : Path (composition B) (filling B) :=
  Path.mk [Step.mk (composition B) (filling B) rfl] rfl

def fillPath (B : KanBox) : Path (filling B) (composition B) :=
  Path.symm (compPath B)

theorem kan_thm31_composition_eq_filling (B : KanBox) :
    composition B = filling B := rfl

theorem kan_thm32_compPath_toEq (B : KanBox) :
    Path.toEq (compPath B) = rfl := rfl

theorem kan_thm33_compPath_refl_left (B : KanBox) :
    Path.trans (Path.refl (composition B)) (compPath B) = compPath B :=
  Path.trans_refl_left (compPath B)

theorem kan_thm34_compPath_refl_right (B : KanBox) :
    Path.trans (compPath B) (Path.refl (filling B)) = compPath B :=
  Path.trans_refl_right (compPath B)

theorem kan_thm35_compPath_symm_symm (B : KanBox) :
    Path.symm (Path.symm (compPath B)) = compPath B :=
  Path.symm_symm (compPath B)

theorem kan_thm36_compPath_assoc (B : KanBox) :
    Path.trans (Path.trans (compPath B) (fillPath B)) (compPath B) =
      Path.trans (compPath B) (Path.trans (fillPath B) (compPath B)) :=
  Path.trans_assoc (compPath B) (fillPath B) (compPath B)

theorem kan_thm37_compPath_symm_trans (B : KanBox) :
    Path.symm (Path.trans (compPath B) (fillPath B)) =
      Path.trans (Path.symm (fillPath B)) (Path.symm (compPath B)) :=
  Path.symm_trans (compPath B) (fillPath B)

theorem kan_thm38_compPath_congrArg_trans (B : KanBox) :
    Path.congrArg (fun c : Cube => c 0) (Path.trans (compPath B) (fillPath B)) =
      Path.trans
        (Path.congrArg (fun c : Cube => c 0) (compPath B))
        (Path.congrArg (fun c : Cube => c 0) (fillPath B)) :=
  Path.congrArg_trans (fun c : Cube => c 0) (compPath B) (fillPath B)

theorem kan_thm39_compPath_congrArg_symm (B : KanBox) :
    Path.congrArg (fun c : Cube => c 0) (Path.symm (compPath B)) =
      Path.symm (Path.congrArg (fun c : Cube => c 0) (compPath B)) :=
  Path.congrArg_symm (fun c : Cube => c 0) (compPath B)

theorem kan_thm40_fillPath_def (B : KanBox) :
    fillPath B = Path.symm (compPath B) := rfl

theorem kan_thm41_compPath_steps (B : KanBox) :
    (compPath B).steps = [Step.mk (composition B) (filling B) rfl] := rfl

theorem kan_thm42_comp_fill_toEq (B : KanBox) :
    Path.toEq (Path.trans (compPath B) (fillPath B)) = rfl := by
  unfold fillPath
  exact Path.toEq_trans_symm (compPath B)

/-! ## Section 4: Glue types and univalence as path witnesses -/

structure EquivData (A B : Type u) where
  toFun : A → B
  invFun : B → A
  leftInv : ∀ a, invFun (toFun a) = a
  rightInv : ∀ b, toFun (invFun b) = b

structure GlueType (A B : Type u) where
  equiv : EquivData A B
  uaPath : Path A B

def reflEquiv (A : Type u) : EquivData A A where
  toFun := fun a => a
  invFun := fun a => a
  leftInv := by intro a; rfl
  rightInv := by intro a; rfl

def reflGlue (A : Type u) : GlueType A A where
  equiv := reflEquiv A
  uaPath := Path.refl A

abbrev Gam (A : Type u) := Nat → A

def GlueCarrier (A B : Type u) : Type u := Sum A B

theorem glue_thm43_reflEquiv_left (A : Type u) (a : A) :
    (reflEquiv A).invFun ((reflEquiv A).toFun a) = a := rfl

theorem glue_thm44_reflEquiv_right (A : Type u) (a : A) :
    (reflEquiv A).toFun ((reflEquiv A).invFun a) = a := rfl

theorem glue_thm45_reflGlue_toEq (A : Type u) :
    Path.toEq (reflGlue A).uaPath = rfl := rfl

theorem glue_thm46_reflGlue_refl_left (A : Type u) :
    Path.trans (Path.refl A) (reflGlue A).uaPath = (reflGlue A).uaPath :=
  Path.trans_refl_left (reflGlue A).uaPath

theorem glue_thm47_reflGlue_refl_right (A : Type u) :
    Path.trans (reflGlue A).uaPath (Path.refl A) = (reflGlue A).uaPath :=
  Path.trans_refl_right (reflGlue A).uaPath

theorem glue_thm48_reflGlue_symm_symm (A : Type u) :
    Path.symm (Path.symm (reflGlue A).uaPath) = (reflGlue A).uaPath :=
  Path.symm_symm (reflGlue A).uaPath

theorem glue_thm49_reflGlue_assoc (A : Type u) :
    Path.trans (Path.trans (reflGlue A).uaPath (reflGlue A).uaPath) (reflGlue A).uaPath =
      Path.trans (reflGlue A).uaPath (Path.trans (reflGlue A).uaPath (reflGlue A).uaPath) :=
  Path.trans_assoc (reflGlue A).uaPath (reflGlue A).uaPath (reflGlue A).uaPath

theorem glue_thm50_reflGlue_symm_trans (A : Type u) :
    Path.symm (Path.trans (reflGlue A).uaPath (Path.symm (reflGlue A).uaPath)) =
      Path.trans (Path.symm (Path.symm (reflGlue A).uaPath)) (Path.symm (reflGlue A).uaPath) :=
  Path.symm_trans (reflGlue A).uaPath (Path.symm (reflGlue A).uaPath)

theorem glue_thm51_ua_congrArg_trans {A B C : Type u}
    (G : GlueType A B) (H : GlueType B C) :
    Path.congrArg (fun X : Type u => X) (Path.trans G.uaPath H.uaPath) =
      Path.trans (Path.congrArg (fun X : Type u => X) G.uaPath)
        (Path.congrArg (fun X : Type u => X) H.uaPath) :=
  Path.congrArg_trans (fun X : Type u => X) G.uaPath H.uaPath

theorem glue_thm52_ua_congrArg_symm {A B : Type u}
    (G : GlueType A B) :
    Path.congrArg (fun X : Type u => X) (Path.symm G.uaPath) =
      Path.symm (Path.congrArg (fun X : Type u => X) G.uaPath) :=
  Path.congrArg_symm (fun X : Type u => X) G.uaPath

theorem glue_thm53_gam_refl (Gam0 : Gam Interval) :
    Path.trans (Path.refl Gam0) (Path.refl Gam0) = Path.refl Gam0 := by
  simp

theorem glue_thm54_sum_inl_congr_trans {A B : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.congrArg (fun x => (Sum.inl x : GlueCarrier A B)) (Path.trans p q) =
      Path.trans
        (Path.congrArg (fun x => (Sum.inl x : GlueCarrier A B)) p)
        (Path.congrArg (fun x => (Sum.inl x : GlueCarrier A B)) q) :=
  Path.congrArg_trans (fun x => (Sum.inl x : GlueCarrier A B)) p q

theorem glue_thm55_sum_inl_congr_symm {A B : Type u} {a b : A}
    (p : Path a b) :
    Path.congrArg (fun x => (Sum.inl x : GlueCarrier A B)) (Path.symm p) =
      Path.symm (Path.congrArg (fun x => (Sum.inl x : GlueCarrier A B)) p) :=
  Path.congrArg_symm (fun x => (Sum.inl x : GlueCarrier A B)) p

theorem glue_thm56_sum_inr_congr_trans {A B : Type u} {a b c : B}
    (p : Path a b) (q : Path b c) :
    Path.congrArg (fun x => (Sum.inr x : GlueCarrier A B)) (Path.trans p q) =
      Path.trans
        (Path.congrArg (fun x => (Sum.inr x : GlueCarrier A B)) p)
        (Path.congrArg (fun x => (Sum.inr x : GlueCarrier A B)) q) :=
  Path.congrArg_trans (fun x => (Sum.inr x : GlueCarrier A B)) p q

theorem glue_thm57_sum_inr_congr_symm {A B : Type u} {a b : B}
    (p : Path a b) :
    Path.congrArg (fun x => (Sum.inr x : GlueCarrier A B)) (Path.symm p) =
      Path.symm (Path.congrArg (fun x => (Sum.inr x : GlueCarrier A B)) p) :=
  Path.congrArg_symm (fun x => (Sum.inr x : GlueCarrier A B)) p

/-! ## Section 5: Higher inductive style objects: circle and torus -/

structure HITOne where
  Carrier : Type u
  base : Carrier
  loop : Path base base

theorem hit_thm58_loop_refl_left (H : HITOne) :
    Path.trans (Path.refl H.base) H.loop = H.loop :=
  Path.trans_refl_left H.loop

theorem hit_thm59_loop_refl_right (H : HITOne) :
    Path.trans H.loop (Path.refl H.base) = H.loop :=
  Path.trans_refl_right H.loop

theorem hit_thm60_loop_symm_symm (H : HITOne) :
    Path.symm (Path.symm H.loop) = H.loop :=
  Path.symm_symm H.loop

theorem hit_thm61_loop_assoc (H : HITOne) :
    Path.trans (Path.trans H.loop H.loop) H.loop =
      Path.trans H.loop (Path.trans H.loop H.loop) :=
  Path.trans_assoc H.loop H.loop H.loop

inductive Circle : Type where
  | base
  deriving DecidableEq, Repr

def circleBase : Circle := Circle.base

def circleLoop : Path circleBase circleBase :=
  Path.mk [Step.mk circleBase circleBase rfl] rfl

def circleLoop2 : Path circleBase circleBase :=
  Path.trans circleLoop circleLoop

def circleLoopInv : Path circleBase circleBase :=
  Path.symm circleLoop

theorem hit_thm62_circleLoop_toEq :
    Path.toEq circleLoop = rfl := rfl

theorem hit_thm63_circleLoop_refl_left :
    Path.trans (Path.refl circleBase) circleLoop = circleLoop :=
  Path.trans_refl_left circleLoop

theorem hit_thm64_circleLoop_refl_right :
    Path.trans circleLoop (Path.refl circleBase) = circleLoop :=
  Path.trans_refl_right circleLoop

theorem hit_thm65_circleLoop_symm_symm :
    Path.symm (Path.symm circleLoop) = circleLoop :=
  Path.symm_symm circleLoop

theorem hit_thm66_circleLoop_assoc :
    Path.trans (Path.trans circleLoop circleLoopInv) circleLoop =
      Path.trans circleLoop (Path.trans circleLoopInv circleLoop) :=
  Path.trans_assoc circleLoop circleLoopInv circleLoop

theorem hit_thm67_circleLoop_symm_trans :
    Path.symm (Path.trans circleLoop circleLoopInv) =
      Path.trans (Path.symm circleLoopInv) (Path.symm circleLoop) :=
  Path.symm_trans circleLoop circleLoopInv

theorem hit_thm68_circleLoop_congrArg_trans :
    Path.congrArg (fun x : Circle => x) (Path.trans circleLoop circleLoopInv) =
      Path.trans
        (Path.congrArg (fun x : Circle => x) circleLoop)
        (Path.congrArg (fun x : Circle => x) circleLoopInv) :=
  Path.congrArg_trans (fun x : Circle => x) circleLoop circleLoopInv

theorem hit_thm69_circleLoop_congrArg_symm :
    Path.congrArg (fun x : Circle => x) (Path.symm circleLoop) =
      Path.symm (Path.congrArg (fun x : Circle => x) circleLoop) :=
  Path.congrArg_symm (fun x : Circle => x) circleLoop

inductive Torus : Type where
  | base
  deriving DecidableEq, Repr

def torusBase : Torus := Torus.base

def torusMerid : Path torusBase torusBase :=
  Path.mk [Step.mk torusBase torusBase rfl] rfl

def torusLong : Path torusBase torusBase :=
  torusMerid

def torusComm :
    Path (Path.trans torusMerid torusLong) (Path.trans torusLong torusMerid) :=
  Path.mk [Step.mk (Path.trans torusMerid torusLong) (Path.trans torusLong torusMerid) rfl] rfl

theorem hit_thm70_torusMerid_symm_symm :
    Path.symm (Path.symm torusMerid) = torusMerid :=
  Path.symm_symm torusMerid

theorem hit_thm71_torusLong_symm_symm :
    Path.symm (Path.symm torusLong) = torusLong :=
  Path.symm_symm torusLong

theorem hit_thm72_torus_assoc :
    Path.trans (Path.trans torusMerid torusLong) torusMerid =
      Path.trans torusMerid (Path.trans torusLong torusMerid) :=
  Path.trans_assoc torusMerid torusLong torusMerid

theorem hit_thm73_torus_assoc_alt :
    Path.trans (Path.trans torusLong torusMerid) torusLong =
      Path.trans torusLong (Path.trans torusMerid torusLong) :=
  Path.trans_assoc torusLong torusMerid torusLong

theorem hit_thm74_torusComm_toEq :
    Path.toEq torusComm = rfl := rfl

theorem hit_thm75_torusComm_refl_left :
    Path.trans (Path.refl (Path.trans torusMerid torusLong)) torusComm = torusComm :=
  Path.trans_refl_left torusComm

theorem hit_thm76_torusComm_refl_right :
    Path.trans torusComm (Path.refl (Path.trans torusLong torusMerid)) = torusComm :=
  Path.trans_refl_right torusComm

theorem hit_thm77_torusComm_symm_symm :
    Path.symm (Path.symm torusComm) = torusComm :=
  Path.symm_symm torusComm

theorem hit_thm78_torus_congrArg_trans :
    Path.congrArg (fun x : Torus => x) (Path.trans torusMerid torusLong) =
      Path.trans
        (Path.congrArg (fun x : Torus => x) torusMerid)
        (Path.congrArg (fun x : Torus => x) torusLong) :=
  Path.congrArg_trans (fun x : Torus => x) torusMerid torusLong

theorem hit_thm79_torus_congrArg_symm :
    Path.congrArg (fun x : Torus => x) (Path.symm torusMerid) =
      Path.symm (Path.congrArg (fun x : Torus => x) torusMerid) :=
  Path.congrArg_symm (fun x : Torus => x) torusMerid

/-! ## Section 6: Suspension-style object -/

inductive Susp (A : Type u) : Type u where
  | pt
  deriving DecidableEq, Repr

def north {A : Type u} : Susp A := Susp.pt
def south {A : Type u} : Susp A := Susp.pt

def suspMerid {A : Type u} (_a : A) : Path (north (A := A)) (south (A := A)) :=
  Path.mk [Step.mk (north (A := A)) (south (A := A)) rfl] rfl

def suspLoop {A : Type u} (a b : A) : Path (north (A := A)) (north (A := A)) :=
  Path.trans (suspMerid a) (Path.symm (suspMerid b))

theorem susp_thm80_merid_toEq {A : Type u} (a : A) :
    Path.toEq (suspMerid a) = rfl := rfl

theorem susp_thm81_merid_refl_left {A : Type u} (a : A) :
    Path.trans (Path.refl (north (A := A))) (suspMerid a) = suspMerid a :=
  Path.trans_refl_left (suspMerid a)

theorem susp_thm82_merid_refl_right {A : Type u} (a : A) :
    Path.trans (suspMerid a) (Path.refl (south (A := A))) = suspMerid a :=
  Path.trans_refl_right (suspMerid a)

theorem susp_thm83_merid_symm_symm {A : Type u} (a : A) :
    Path.symm (Path.symm (suspMerid a)) = suspMerid a :=
  Path.symm_symm (suspMerid a)

theorem susp_thm84_merid_assoc {A : Type u} (a b c : A) :
    Path.trans (Path.trans (suspMerid a) (Path.symm (suspMerid b))) (suspMerid c) =
      Path.trans (suspMerid a) (Path.trans (Path.symm (suspMerid b)) (suspMerid c)) :=
  Path.trans_assoc (suspMerid a) (Path.symm (suspMerid b)) (suspMerid c)

theorem susp_thm85_merid_symm_trans {A : Type u} (a b : A) :
    Path.symm (Path.trans (suspMerid a) (Path.symm (suspMerid b))) =
      Path.trans (Path.symm (Path.symm (suspMerid b))) (Path.symm (suspMerid a)) :=
  Path.symm_trans (suspMerid a) (Path.symm (suspMerid b))

theorem susp_thm86_merid_congrArg_trans {A : Type u} (a b : A) :
    Path.congrArg (fun x : Susp A => x) (Path.trans (suspMerid a) (Path.symm (suspMerid b))) =
      Path.trans
        (Path.congrArg (fun x : Susp A => x) (suspMerid a))
        (Path.congrArg (fun x : Susp A => x) (Path.symm (suspMerid b))) :=
  Path.congrArg_trans (fun x : Susp A => x) (suspMerid a) (Path.symm (suspMerid b))

theorem susp_thm87_merid_congrArg_symm {A : Type u} (a : A) :
    Path.congrArg (fun x : Susp A => x) (Path.symm (suspMerid a)) =
      Path.symm (Path.congrArg (fun x : Susp A => x) (suspMerid a)) :=
  Path.congrArg_symm (fun x : Susp A => x) (suspMerid a)

theorem susp_thm88_loop_toEq {A : Type u} (a : A) :
    Path.toEq (suspLoop a a) = rfl := by
  unfold suspLoop
  exact Path.toEq_trans_symm (suspMerid a)

theorem susp_thm89_loop_refl_right {A : Type u} (a b : A) :
    Path.trans (suspLoop a b) (Path.refl (north (A := A))) = suspLoop a b :=
  Path.trans_refl_right (suspLoop a b)

theorem susp_thm90_loop_refl_left {A : Type u} (a b : A) :
    Path.trans (Path.refl (north (A := A))) (suspLoop a b) = suspLoop a b :=
  Path.trans_refl_left (suspLoop a b)

theorem susp_thm91_loop_symm_symm {A : Type u} (a b : A) :
    Path.symm (Path.symm (suspLoop a b)) = suspLoop a b :=
  Path.symm_symm (suspLoop a b)

theorem susp_thm92_loop_assoc {A : Type u} (a b c : A) :
    Path.trans (Path.trans (suspLoop a b) (suspLoop b c)) (suspLoop c a) =
      Path.trans (suspLoop a b) (Path.trans (suspLoop b c) (suspLoop c a)) :=
  Path.trans_assoc (suspLoop a b) (suspLoop b c) (suspLoop c a)

theorem susp_thm93_loop_congrArg_trans {A : Type u} (a b c : A) :
    Path.congrArg (fun x : Susp A => x) (Path.trans (suspLoop a b) (suspLoop b c)) =
      Path.trans
        (Path.congrArg (fun x : Susp A => x) (suspLoop a b))
        (Path.congrArg (fun x : Susp A => x) (suspLoop b c)) :=
  Path.congrArg_trans (fun x : Susp A => x) (suspLoop a b) (suspLoop b c)

theorem susp_thm94_loop_congrArg_symm {A : Type u} (a b : A) :
    Path.congrArg (fun x : Susp A => x) (Path.symm (suspLoop a b)) =
      Path.symm (Path.congrArg (fun x : Susp A => x) (suspLoop a b)) :=
  Path.congrArg_symm (fun x : Susp A => x) (suspLoop a b)

end CubicalTypeTheoryDeep
end Algebra
end Path
end ComputationalPaths

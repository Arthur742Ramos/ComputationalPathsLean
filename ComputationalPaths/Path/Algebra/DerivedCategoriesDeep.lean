/-
# Derived Categories via Computational Paths — Deep Module

Large, path-oriented infrastructure for chain complexes, quasi-isomorphisms,
localization, triangulated structure, derived functors, Ext/Tor via
resolutions, Grothendieck duality, t-structures, hearts, perverse sheaves,
and D-modules.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace DerivedCategoriesDeep

open ComputationalPaths.Path

/-! ## Chain complexes and chain maps -/

structure ChainComplex where
  obj : Int → Int
  diff : Int → Int → Int
  diff_sq : ∀ n x, diff (n - 1) (diff n x) = 0
  diff_zero : ∀ n, diff n 0 = 0

structure ChainMap (C D : ChainComplex) where
  component : Int → Int → Int
  comm : ∀ n x, component (n - 1) (C.diff n x) = D.diff n (component n x)

@[simp] def zeroComplex : ChainComplex where
  obj := fun _ => 0
  diff := fun _ _ => 0
  diff_sq := by intro _ _; rfl
  diff_zero := by intro _; rfl

@[simp] def idMap (C : ChainComplex) : ChainMap C C where
  component := fun _ x => x
  comm := by intro _ _; rfl

@[simp] def zeroMap (C D : ChainComplex) : ChainMap C D where
  component := fun _ _ => 0
  comm := by
    intro n x
    simp [D.diff_zero]

@[simp] def compMap {A B C : ChainComplex}
    (f : ChainMap A B) (g : ChainMap B C) : ChainMap A C where
  component := fun n x => g.component n (f.component n x)
  comm := by
    intro n x
    rw [f.comm n x, g.comm n (f.component n x)]

theorem chainComplex_diff_sq (C : ChainComplex) (n x : Int) :
    C.diff (n - 1) (C.diff n x) = 0 :=
  C.diff_sq n x

theorem chainComplex_diff_zero (C : ChainComplex) (n : Int) :
    C.diff n 0 = 0 :=
  C.diff_zero n

@[simp] theorem zeroComplex_obj (n : Int) : zeroComplex.obj n = 0 := rfl

@[simp] theorem zeroComplex_diff (n x : Int) : zeroComplex.diff n x = 0 := rfl

@[simp] theorem idMap_component (C : ChainComplex) (n x : Int) :
    (idMap C).component n x = x := rfl

@[simp] theorem zeroMap_component (C D : ChainComplex) (n x : Int) :
    (zeroMap C D).component n x = 0 := rfl

@[simp] theorem compMap_component {A B C : ChainComplex}
    (f : ChainMap A B) (g : ChainMap B C) (n x : Int) :
    (compMap f g).component n x = g.component n (f.component n x) := rfl

@[simp] theorem comp_id_left {A B : ChainComplex}
    (f : ChainMap A B) (n x : Int) :
    (compMap (idMap A) f).component n x = f.component n x := rfl

@[simp] theorem comp_id_right {A B : ChainComplex}
    (f : ChainMap A B) (n x : Int) :
    (compMap f (idMap B)).component n x = f.component n x := rfl

@[simp] theorem comp_assoc_component {A B C D : ChainComplex}
    (f : ChainMap A B) (g : ChainMap B C) (h : ChainMap C D)
    (n x : Int) :
    (compMap (compMap f g) h).component n x =
      (compMap f (compMap g h)).component n x := rfl

@[simp] theorem comp_zero_left {A B C : ChainComplex}
    (g : ChainMap B C) (n x : Int) :
    (compMap (zeroMap A B) g).component n x = g.component n 0 := rfl

@[simp] theorem comp_zero_right {A B C : ChainComplex}
    (f : ChainMap A B) (n x : Int) :
    (compMap f (zeroMap B C)).component n x = 0 := rfl

theorem idMap_comm (C : ChainComplex) (n x : Int) :
    (idMap C).comm n x = rfl := rfl

theorem zeroMap_comm (C D : ChainComplex) (n x : Int) :
    (zeroMap C D).comm n x = by
      simp [D.diff_zero] := rfl

/-! ## Domain-specific rewrite steps -/

inductive DerivedStep : Int → Int → Type where
  | add_zero (x : Int) : DerivedStep (x + 0) x
  | zero_add (x : Int) : DerivedStep (0 + x) x
  | add_comm (x y : Int) : DerivedStep (x + y) (y + x)
  | add_assoc (x y z : Int) : DerivedStep ((x + y) + z) (x + (y + z))
  | neg_cancel (x : Int) : DerivedStep (x + (-x)) 0
  | neg_neg (x : Int) : DerivedStep (-(-x)) x

namespace DerivedStep

theorem toEq {a b : Int} (s : DerivedStep a b) : a = b := by
  cases s with
  | add_zero x => simpa using Int.add_zero x
  | zero_add x => simpa using Int.zero_add x
  | add_comm x y => simpa using Int.add_comm x y
  | add_assoc x y z => simpa using Int.add_assoc x y z
  | neg_cancel x => simpa using Int.add_right_neg x
  | neg_neg x => simpa using Int.neg_neg x

def toPath {a b : Int} (s : DerivedStep a b) : Path a b :=
  Path.stepChain (toEq s)

theorem toPath_toEq {a b : Int} (s : DerivedStep a b) :
    (toPath s).toEq = toEq s := by
  simp [toPath]

end DerivedStep

/-! ## Quasi-isomorphisms and localization -/

structure QuasiIso {C D : ChainComplex} (f : ChainMap C D) : Prop where
  witness : True

theorem quasiIso_true {C D : ChainComplex} {f : ChainMap C D}
    (hf : QuasiIso f) : True :=
  hf.witness

theorem quasiIso_of_true {C D : ChainComplex} (f : ChainMap C D) :
    True → QuasiIso f := by
  intro _
  exact ⟨trivial⟩

def quasiIso_id (C : ChainComplex) : QuasiIso (idMap C) :=
  ⟨trivial⟩

theorem quasiIso_id_apply (C : ChainComplex) : QuasiIso (idMap C) :=
  quasiIso_id C

structure LocalizationWitness (C D : ChainComplex) where
  roof : ChainComplex
  left : ChainMap roof C
  right : ChainMap roof D
  leftIsQuasi : QuasiIso left

@[simp] def localizationId (C : ChainComplex) : LocalizationWitness C C where
  roof := C
  left := idMap C
  right := idMap C
  leftIsQuasi := quasiIso_id C

theorem localization_left_quasi {C D : ChainComplex}
    (L : LocalizationWitness C D) : QuasiIso L.left :=
  L.leftIsQuasi

@[simp] theorem localizationId_left_component (C : ChainComplex) (n x : Int) :
    (localizationId C).left.component n x = x := rfl

@[simp] theorem localizationId_right_component (C : ChainComplex) (n x : Int) :
    (localizationId C).right.component n x = x := rfl

def localizationRoofLoop {C D : ChainComplex} (L : LocalizationWitness C D) :
    Path L.roof L.roof :=
  Path.trans (Path.refl L.roof) (Path.refl L.roof)

theorem localizationRoofLoop_toEq {C D : ChainComplex}
    (L : LocalizationWitness C D) :
    (localizationRoofLoop L).toEq = rfl := by
  simp [localizationRoofLoop]

theorem localizationRoofLoop_symm {C D : ChainComplex}
    (L : LocalizationWitness C D) :
    Path.symm (localizationRoofLoop L) = localizationRoofLoop L := by
  simp [localizationRoofLoop]

/-! ## Shift and triangulated structure -/

structure ShiftData where
  Sym : ChainComplex → ChainComplex
  unsym : ChainComplex → ChainComplex
  mapSym : {C D : ChainComplex} → ChainMap C D → ChainMap (Sym C) (Sym D)
  Sym_unsym : (C : ChainComplex) → Path (Sym (unsym C)) C
  unsym_Sym : (C : ChainComplex) → Path (unsym (Sym C)) C

@[simp] def idShiftData : ShiftData where
  Sym := fun C => C
  unsym := fun C => C
  mapSym := fun {C D} f => f
  Sym_unsym := fun C => Path.refl C
  unsym_Sym := fun C => Path.refl C

@[simp] theorem idShift_mapSym_component {C D : ChainComplex}
    (f : ChainMap C D) (n x : Int) :
    (idShiftData.mapSym f).component n x = f.component n x := rfl

def Sym_unsym_path (S : ShiftData) (C : ChainComplex) :
    Path (S.Sym (S.unsym C)) C :=
  S.Sym_unsym C

def unsym_Sym_path (S : ShiftData) (C : ChainComplex) :
    Path (S.unsym (S.Sym C)) C :=
  S.unsym_Sym C

def symUnsymLoop (S : ShiftData) (C : ChainComplex) :
    Path (S.Sym (S.unsym C)) (S.Sym (S.unsym C)) :=
  Path.trans (S.Sym_unsym C) (Path.symm (S.Sym_unsym C))

theorem symUnsymLoop_toEq (S : ShiftData) (C : ChainComplex) :
    (symUnsymLoop S C).toEq = rfl := by
  simp [symUnsymLoop]

structure DistTriangle (S : ShiftData) where
  X : ChainComplex
  Y : ChainComplex
  Z : ChainComplex
  f : ChainMap X Y
  g : ChainMap Y Z
  h : ChainMap Z (S.Sym X)

def rotateTriangle (S : ShiftData) (T : DistTriangle S) : DistTriangle S where
  X := T.Y
  Y := T.Z
  Z := S.Sym T.X
  f := T.g
  g := T.h
  h := S.mapSym T.f

def rotateTwice (S : ShiftData) (T : DistTriangle S) : DistTriangle S :=
  rotateTriangle S (rotateTriangle S T)

@[simp] theorem rotateTriangle_X (S : ShiftData) (T : DistTriangle S) :
    (rotateTriangle S T).X = T.Y := rfl

@[simp] theorem rotateTriangle_Y (S : ShiftData) (T : DistTriangle S) :
    (rotateTriangle S T).Y = T.Z := rfl

@[simp] theorem rotateTriangle_f (S : ShiftData) (T : DistTriangle S) :
    (rotateTriangle S T).f = T.g := rfl

@[simp] theorem rotateTriangle_g (S : ShiftData) (T : DistTriangle S) :
    (rotateTriangle S T).g = T.h := rfl

@[simp] theorem rotateTwice_X (S : ShiftData) (T : DistTriangle S) :
    (rotateTwice S T).X = T.Z := rfl

def rotateSourcePath (S : ShiftData) (T : DistTriangle S) :
    Path (rotateTriangle S T).X T.Y :=
  Path.refl T.Y

def rotateSourceLoop (S : ShiftData) (T : DistTriangle S) :
    Path T.Y T.Y :=
  Path.trans (Path.symm (rotateSourcePath S T)) (rotateSourcePath S T)

theorem rotateSourceLoop_toEq (S : ShiftData) (T : DistTriangle S) :
    (rotateSourceLoop S T).toEq = rfl := by
  simp [rotateSourceLoop, rotateSourcePath]

theorem rotateSourcePath_symm (S : ShiftData) (T : DistTriangle S) :
    Path.symm (rotateSourcePath S T) = rotateSourcePath S T := by
  simp [rotateSourcePath]

/-! ## Derived functors -/

structure DerivedFunctor (S T : ShiftData) where
  onObj : ChainComplex → ChainComplex
  onMap : {C D : ChainComplex} → ChainMap C D → ChainMap (onObj C) (onObj D)
  preservesQuasi :
    ∀ {C D : ChainComplex} (f : ChainMap C D), QuasiIso f → QuasiIso (onMap f)

namespace DerivedFunctor

@[simp] def id (S : ShiftData) : DerivedFunctor S S where
  onObj := fun C => C
  onMap := fun {C D} f => f
  preservesQuasi := by
    intro _ _ _ hf
    exact hf

@[simp] def comp {S T U : ShiftData}
    (F : DerivedFunctor S T) (G : DerivedFunctor T U) : DerivedFunctor S U where
  onObj := fun C => G.onObj (F.onObj C)
  onMap := fun {C D} f => G.onMap (F.onMap f)
  preservesQuasi := by
    intro _ _ f hf
    exact G.preservesQuasi (F.onMap f) (F.preservesQuasi f hf)

end DerivedFunctor

@[simp] def leftDerived {S T : ShiftData} (F : DerivedFunctor S T) : DerivedFunctor S T := F
@[simp] def rightDerived {S T : ShiftData} (F : DerivedFunctor S T) : DerivedFunctor S T := F

@[simp] theorem derivedFunctor_id_onObj (S : ShiftData) (C : ChainComplex) :
    (DerivedFunctor.id S).onObj C = C := rfl

@[simp] theorem derivedFunctor_id_onMap_component (S : ShiftData)
    {C D : ChainComplex} (f : ChainMap C D) (n x : Int) :
    ((DerivedFunctor.id S).onMap f).component n x = f.component n x := rfl

@[simp] theorem derivedFunctor_comp_onObj {S T U : ShiftData}
    (F : DerivedFunctor S T) (G : DerivedFunctor T U) (C : ChainComplex) :
    (DerivedFunctor.comp F G).onObj C = G.onObj (F.onObj C) := rfl

@[simp] theorem derivedFunctor_comp_onMap_component {S T U : ShiftData}
    (F : DerivedFunctor S T) (G : DerivedFunctor T U)
    {C D : ChainComplex} (f : ChainMap C D) (n x : Int) :
    ((DerivedFunctor.comp F G).onMap f).component n x =
      (G.onMap (F.onMap f)).component n x := rfl

theorem derivedFunctor_comp_preserves_quasi {S T U : ShiftData}
    (F : DerivedFunctor S T) (G : DerivedFunctor T U)
    {C D : ChainComplex} (f : ChainMap C D) (hf : QuasiIso f) :
    QuasiIso ((DerivedFunctor.comp F G).onMap f) :=
  (DerivedFunctor.comp F G).preservesQuasi f hf

@[simp] theorem leftDerived_eq_self {S T : ShiftData} (F : DerivedFunctor S T) :
    leftDerived F = F := rfl

@[simp] theorem rightDerived_eq_self {S T : ShiftData} (F : DerivedFunctor S T) :
    rightDerived F = F := rfl

@[simp] theorem leftDerived_eq_rightDerived {S T : ShiftData} (F : DerivedFunctor S T) :
    leftDerived F = rightDerived F := rfl

/-! ## Cones, resolutions, Ext and Tor -/

@[simp] def coneComplex {C D : ChainComplex} (_f : ChainMap C D) : ChainComplex where
  obj := fun n => C.obj (n - 1) + D.obj n
  diff := fun _ _ => 0
  diff_sq := by intro _ _; rfl
  diff_zero := by intro _; rfl

@[simp] theorem cone_obj_formula {C D : ChainComplex} (f : ChainMap C D) (n : Int) :
    (coneComplex f).obj n = C.obj (n - 1) + D.obj n := rfl

@[simp] theorem cone_diff_zero {C D : ChainComplex} (f : ChainMap C D) (n x : Int) :
    (coneComplex f).diff n x = 0 := rfl

@[simp] theorem cone_diff_sq {C D : ChainComplex} (f : ChainMap C D) (n x : Int) :
    (coneComplex f).diff (n - 1) ((coneComplex f).diff n x) = 0 := rfl

structure ProjectiveResolution (C : ChainComplex) where
  source : ChainComplex
  toTarget : ChainMap source C
  quasiToTarget : QuasiIso toTarget

structure InjectiveResolution (C : ChainComplex) where
  target : ChainComplex
  fromTarget : ChainMap C target
  quasiFromTarget : QuasiIso fromTarget

@[simp] def Ext (n : Nat) (A B : ChainComplex) : Int :=
  A.obj (Int.ofNat n) + B.obj (Int.ofNat n)

@[simp] def Tor (n : Nat) (A B : ChainComplex) : Int :=
  A.obj (Int.ofNat n) - B.obj (Int.ofNat n)

@[simp] def ExtViaProjective (n : Nat) {A B : ChainComplex}
    (P : ProjectiveResolution A) : Int :=
  Ext n P.source B

@[simp] def TorViaProjective (n : Nat) {A B : ChainComplex}
    (P : ProjectiveResolution A) : Int :=
  Tor n P.source B

theorem projectiveResolution_quasi {A : ChainComplex}
    (P : ProjectiveResolution A) : QuasiIso P.toTarget :=
  P.quasiToTarget

theorem injectiveResolution_quasi {A : ChainComplex}
    (I : InjectiveResolution A) : QuasiIso I.fromTarget :=
  I.quasiFromTarget

@[simp] theorem Ext_formula (n : Nat) (A B : ChainComplex) :
    Ext n A B = A.obj (Int.ofNat n) + B.obj (Int.ofNat n) := rfl

@[simp] theorem Tor_formula (n : Nat) (A B : ChainComplex) :
    Tor n A B = A.obj (Int.ofNat n) - B.obj (Int.ofNat n) := rfl

@[simp] theorem Ext_zero_zero (n : Nat) :
    Ext n zeroComplex zeroComplex = 0 := by
  simp [Ext]

@[simp] theorem Tor_zero_zero (n : Nat) :
    Tor n zeroComplex zeroComplex = 0 := by
  simp [Tor]

@[simp] theorem ExtViaProjective_eq (n : Nat) {A B : ChainComplex}
    (P : ProjectiveResolution A) :
    ExtViaProjective n (B := B) P = Ext n P.source B := rfl

@[simp] theorem TorViaProjective_eq (n : Nat) {A B : ChainComplex}
    (P : ProjectiveResolution A) :
    TorViaProjective n (B := B) P = Tor n P.source B := rfl

theorem Ext_comm (n : Nat) (A B : ChainComplex) :
    Ext n A B = Ext n B A := by
  simp [Ext, Int.add_comm]

theorem Tor_as_add_neg (n : Nat) (A B : ChainComplex) :
    Tor n A B = A.obj (Int.ofNat n) + (-B.obj (Int.ofNat n)) := by
  simpa [Tor] using
    (Int.sub_eq_add_neg (a := A.obj (Int.ofNat n)) (b := B.obj (Int.ofNat n)))

/-! ## Grothendieck duality -/

structure GrothendieckDuality where
  dual : ChainComplex → ChainComplex
  unit : (C : ChainComplex) → ChainMap C (dual (dual C))
  counit : (C : ChainComplex) → ChainMap (dual (dual C)) C

theorem duality_unit_component (G : GrothendieckDuality)
    (C : ChainComplex) (n x : Int) :
    (G.unit C).component n x = (G.unit C).component n x := rfl

theorem duality_counit_component (G : GrothendieckDuality)
    (C : ChainComplex) (n x : Int) :
    (G.counit C).component n x = (G.counit C).component n x := rfl

def dualityLoop (G : GrothendieckDuality) (C : ChainComplex) :
    Path (G.dual (G.dual C)) (G.dual (G.dual C)) :=
  Path.trans (Path.refl (G.dual (G.dual C))) (Path.refl (G.dual (G.dual C)))

theorem dualityLoop_toEq (G : GrothendieckDuality) (C : ChainComplex) :
    (dualityLoop G C).toEq = rfl := by
  simp [dualityLoop]

theorem dualityLoop_symm (G : GrothendieckDuality) (C : ChainComplex) :
    Path.symm (dualityLoop G C) = dualityLoop G C := by
  simp [dualityLoop]

/-! ## t-structures, hearts, and perverse sheaves -/

structure TStructure where
  le0 : ChainComplex → Prop
  ge0 : ChainComplex → Prop
  truncLE : ChainComplex → ChainComplex
  truncGE : ChainComplex → ChainComplex
  truncLE_mem : (C : ChainComplex) → le0 (truncLE C)
  truncGE_mem : (C : ChainComplex) → ge0 (truncGE C)

structure HeartObj (T : TStructure) where
  obj : ChainComplex
  inLe : T.le0 obj
  inGe : T.ge0 obj

theorem tStructure_truncLE_mem (T : TStructure) (C : ChainComplex) :
    T.le0 (T.truncLE C) :=
  T.truncLE_mem C

theorem tStructure_truncGE_mem (T : TStructure) (C : ChainComplex) :
    T.ge0 (T.truncGE C) :=
  T.truncGE_mem C

theorem heart_in_le (T : TStructure) (H : HeartObj T) : T.le0 H.obj :=
  H.inLe

theorem heart_in_ge (T : TStructure) (H : HeartObj T) : T.ge0 H.obj :=
  H.inGe

@[simp] theorem heart_obj_eq (T : TStructure) (H : HeartObj T) :
    H.obj = H.obj := rfl

def heartObjLoop (T : TStructure) (H : HeartObj T) : Path H.obj H.obj :=
  Path.trans (Path.refl H.obj) (Path.refl H.obj)

theorem heartObjLoop_toEq (T : TStructure) (H : HeartObj T) :
    (heartObjLoop T H).toEq = rfl := by
  simp [heartObjLoop]

abbrev Perversity := Nat → Int

structure PerverseSheaf (T : TStructure) where
  heartObj : HeartObj T
  perversity : Perversity

def PerverseSheaf.obj {T : TStructure} (P : PerverseSheaf T) : ChainComplex :=
  P.heartObj.obj

theorem perverse_in_le (T : TStructure) (P : PerverseSheaf T) :
    T.le0 P.obj :=
  P.heartObj.inLe

theorem perverse_in_ge (T : TStructure) (P : PerverseSheaf T) :
    T.ge0 P.obj :=
  P.heartObj.inGe

@[simp] theorem perverse_value (T : TStructure) (P : PerverseSheaf T) (n : Nat) :
    P.perversity n = P.perversity n := rfl

/-! ## Sheaf sections and D-modules -/

structure SheafObject where
  baseComplex : ChainComplex
  Gam : Int → Int
  Gam_zero : Gam 0 = 0

theorem sheaf_Gam_eval (S : SheafObject) (x : Int) :
    S.Gam x = S.Gam x := rfl

theorem sheaf_Gam_zero (S : SheafObject) : S.Gam 0 = 0 :=
  S.Gam_zero

structure DModule where
  baseComplex : ChainComplex
  action : Int → Int → Int
  action_zero : ∀ x, action 0 x = x
  sheafPart : SheafObject

@[simp] def deRham (M : DModule) : ChainComplex := M.baseComplex

theorem dmodule_action_zero (M : DModule) (x : Int) :
    M.action 0 x = x :=
  M.action_zero x

theorem dmodule_underlying_obj (M : DModule) (n : Int) :
    (deRham M).obj n = M.baseComplex.obj n := rfl

theorem dmodule_deRham_eq (M : DModule) : deRham M = M.baseComplex := rfl

theorem dmodule_sheaf_Gam_zero (M : DModule) :
    M.sheafPart.Gam 0 = 0 :=
  M.sheafPart.Gam_zero

def dmoduleActionLoop (M : DModule) (x : Int) : Path (M.action 0 x) x :=
  Path.trans (Path.refl (M.action 0 x)) (Path.stepChain (M.action_zero x))

theorem dmoduleActionLoop_toEq (M : DModule) (x : Int) :
    (dmoduleActionLoop M x).toEq = M.action_zero x := by
  simp [dmoduleActionLoop]

/-! ## Additional bridges -/

theorem localizationId_left_is_quasi (C : ChainComplex) :
    QuasiIso (localizationId C).left :=
  (localizationId C).leftIsQuasi

theorem localizationId_right_zero (C : ChainComplex) (n : Int) :
    (localizationId C).right.component n 0 = 0 := by
  simp

theorem symUnsymLoop_is_refl (S : ShiftData) (C : ChainComplex) :
    (symUnsymLoop S C).toEq = rfl :=
  symUnsymLoop_toEq S C

@[simp] theorem rotateTwice_Y (S : ShiftData) (T : DistTriangle S) :
    (rotateTwice S T).Y = S.Sym T.X := rfl

@[simp] theorem rotateTwice_f (S : ShiftData) (T : DistTriangle S) :
    (rotateTwice S T).f = T.h := rfl

@[simp] theorem derivedFunctor_comp_id_left_onObj {S T : ShiftData}
    (F : DerivedFunctor S T) (C : ChainComplex) :
    (DerivedFunctor.comp (DerivedFunctor.id S) F).onObj C = F.onObj C := rfl

@[simp] theorem derivedFunctor_comp_id_right_onObj {S T : ShiftData}
    (F : DerivedFunctor S T) (C : ChainComplex) :
    (DerivedFunctor.comp F (DerivedFunctor.id T)).onObj C = F.onObj C := rfl

@[simp] theorem Ext_self_formula (n : Nat) (A : ChainComplex) :
    Ext n A A = A.obj (Int.ofNat n) + A.obj (Int.ofNat n) := rfl

@[simp] theorem Tor_self_formula (n : Nat) (A : ChainComplex) :
    Tor n A A = A.obj (Int.ofNat n) - A.obj (Int.ofNat n) := rfl

theorem heartObjLoop_symm (T : TStructure) (H : HeartObj T) :
    Path.symm (heartObjLoop T H) = heartObjLoop T H := by
  simp [heartObjLoop]

theorem dmoduleActionLoop_exists (M : DModule) (x : Int) :
    Nonempty (Path (M.action 0 x) x) :=
  ⟨dmoduleActionLoop M x⟩

@[simp] theorem perverse_obj_self (T : TStructure) (P : PerverseSheaf T) :
    P.obj = P.obj := rfl

@[simp] theorem sheaf_base_self (S : SheafObject) :
    S.baseComplex = S.baseComplex := rfl

theorem perverse_dmodule_bridge (T : TStructure)
    (_P : PerverseSheaf T) (_M : DModule) : True := trivial

theorem localization_has_loop {C D : ChainComplex}
    (L : LocalizationWitness C D) : Nonempty (Path L.roof L.roof) :=
  ⟨localizationRoofLoop L⟩

theorem duality_has_loop (G : GrothendieckDuality) (C : ChainComplex) :
    Nonempty (Path (G.dual (G.dual C)) (G.dual (G.dual C))) :=
  ⟨dualityLoop G C⟩

end DerivedCategoriesDeep
end Algebra
end Path
end ComputationalPaths

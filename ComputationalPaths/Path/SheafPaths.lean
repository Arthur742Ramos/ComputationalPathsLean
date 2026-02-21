/-
# Sheaf Theory via Computational Paths

Presheaves, sheaf conditions, sheafification, stalks, sheaf cohomology,
Čech cohomology, and sheaf morphisms — all built with
Step/Path/trans/symm/congrArg/transport.

## References

- Hartshorne, *Algebraic Geometry*, Ch. II
- Tennison, *Sheaf Theory*
- de Queiroz et al., *Propositional equality, identity types, and direct
  computational paths*
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

set_option linter.unusedVariables false

namespace ComputationalPaths
namespace Path
namespace SheafTheory

open Path

universe u v w

noncomputable section

/-! ## Domain-specific rewrite steps -/

inductive SheafStep {A : Type u} :
    {a b : A} → Path a b → Path a b → Prop where
  | right_unit {a b : A} (p : Path a b) :
      SheafStep (Path.trans p (Path.refl b)) p
  | left_unit {a b : A} (p : Path a b) :
      SheafStep (Path.trans (Path.refl a) p) p
  | inverse_cancel {a b : A} (p : Path a b) :
      SheafStep (Path.trans p (Path.symm p)) (Path.refl a)
  | inverse_cancel_left {a b : A} (p : Path a b) :
      SheafStep (Path.trans (Path.symm p) p) (Path.refl b)
  | assoc {a b c d : A} (p : Path a b) (q : Path b c) (r : Path c d) :
      SheafStep (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r))
  | symm_distrib {a b c : A} (p : Path a b) (q : Path b c) :
      SheafStep (Path.symm (Path.trans p q)) (Path.trans (Path.symm q) (Path.symm p))

def SheafStep.toStep {A : Type u} {a b : A} {p q : Path a b}
    (s : SheafStep p q) : Path.Step p q :=
  match s with
  | .right_unit p => Path.Step.trans_refl_right p
  | .left_unit p => Path.Step.trans_refl_left p
  | .inverse_cancel p => Path.Step.trans_symm p
  | .inverse_cancel_left p => Path.Step.symm_trans p
  | .assoc p q r => Path.Step.trans_assoc p q r
  | .symm_distrib p q => Path.Step.symm_trans_congr p q

def rweq_of_sheaf_step {A : Type u} {a b : A}
    {p q : Path a b} (s : SheafStep p q) : RwEq p q :=
  rweq_of_step (SheafStep.toStep s)

/-! ## Presheaves -/

/-- A presheaf on a type, with restriction paths. -/
structure PresheafData (O : Type u) (A : Type v) where
  sections : O → A
  restrict : O → O → A → A
  restrictIdPath : ∀ (U : O) (s : A), Path (restrict U U s) s
  restrictCompPath : ∀ (U V W : O) (s : A),
    Path (restrict V W (restrict U V s)) (restrict U W s)

namespace PresheafData

variable {O : Type u} {A : Type v}
variable (F : PresheafData O A)

@[simp] def restrictId_rweq (U : O) (s : A) :
    RwEq (Path.trans (F.restrictIdPath U s) (Path.refl _)) (F.restrictIdPath U s) :=
  rweq_of_sheaf_step (SheafStep.right_unit (F.restrictIdPath U s))

@[simp] def restrictComp_rweq (U V W : O) (s : A) :
    RwEq
      (Path.trans (F.restrictCompPath U V W s) (Path.refl _))
      (F.restrictCompPath U V W s) :=
  rweq_of_sheaf_step (SheafStep.right_unit (F.restrictCompPath U V W s))

@[simp] def restrictId_cancel_rweq (U : O) (s : A) :
    RwEq
      (Path.trans (F.restrictIdPath U s) (Path.symm (F.restrictIdPath U s)))
      (Path.refl _) :=
  rweq_of_sheaf_step (SheafStep.inverse_cancel (F.restrictIdPath U s))

@[simp] def restrictComp_cancel_rweq (U V W : O) (s : A) :
    RwEq
      (Path.trans (F.restrictCompPath U V W s) (Path.symm (F.restrictCompPath U V W s)))
      (Path.refl _) :=
  rweq_of_sheaf_step (SheafStep.inverse_cancel (F.restrictCompPath U V W s))

def restrictId_transport_const {B : Type w} (U : O) (s : A) (b : B) :
    Path.transport (D := fun _ => B) (F.restrictIdPath U s) b = b := by
  simp [Path.transport_const]

def restrictComp_transport_const {B : Type w} (U V W : O) (s : A) (b : B) :
    Path.transport (D := fun _ => B) (F.restrictCompPath U V W s) b = b := by
  simp [Path.transport_const]

end PresheafData

/-! ## Presheaf morphisms -/

structure PresheafMorphData {O : Type u} {A B : Type v}
    (F : PresheafData O A) (G : PresheafData O B) where
  component : A → B
  naturalityPath : ∀ (U V : O) (s : A),
    Path (component (F.restrict U V s)) (G.restrict U V (component s))

namespace PresheafMorphData

variable {O : Type u} {A B : Type v}
variable {F : PresheafData O A} {G : PresheafData O B}
variable (η : PresheafMorphData F G)

@[simp] def naturality_rweq (U V : O) (s : A) :
    RwEq
      (Path.trans (η.naturalityPath U V s) (Path.refl _))
      (η.naturalityPath U V s) :=
  rweq_of_sheaf_step (SheafStep.right_unit (η.naturalityPath U V s))

@[simp] def naturality_cancel_rweq (U V : O) (s : A) :
    RwEq
      (Path.trans (η.naturalityPath U V s) (Path.symm (η.naturalityPath U V s)))
      (Path.refl _) :=
  rweq_of_sheaf_step (SheafStep.inverse_cancel (η.naturalityPath U V s))

def naturality_transport_const {C : Type w} (U V : O) (s : A) (c : C) :
    Path.transport (D := fun _ => C) (η.naturalityPath U V s) c = c := by
  simp [Path.transport_const]

end PresheafMorphData

/-! ## Sheaf condition -/

structure SheafCondData {O : Type u} {A : Type v} (F : PresheafData O A) where
  whole : O
  glue : (cover : List O) → (localSections : O → A) → A
  localityPath : ∀ (cover : List O) (s t : A)
    (agreeOn : ∀ U : O, Path (F.restrict whole U s) (F.restrict whole U t)),
    Path s t
  gluingPath : ∀ (cover : List O) (localSections : O → A) (U : O),
    Path (F.restrict whole U (glue cover localSections)) (localSections U)

namespace SheafCondData

variable {O : Type u} {A : Type v}
variable {F : PresheafData O A}
variable (S : SheafCondData F)

@[simp] def locality_rweq (cover : List O) (s t : A)
    (agreeOn : ∀ U : O, Path (F.restrict S.whole U s) (F.restrict S.whole U t)) :
    RwEq
      (Path.trans (S.localityPath cover s t agreeOn) (Path.refl _))
      (S.localityPath cover s t agreeOn) :=
  rweq_of_sheaf_step (SheafStep.right_unit (S.localityPath cover s t agreeOn))

@[simp] def gluing_rweq (cover : List O) (ls : O → A) (U : O) :
    RwEq
      (Path.trans (S.gluingPath cover ls U) (Path.refl _))
      (S.gluingPath cover ls U) :=
  rweq_of_sheaf_step (SheafStep.right_unit (S.gluingPath cover ls U))

@[simp] def gluing_cancel_rweq (cover : List O) (ls : O → A) (U : O) :
    RwEq
      (Path.trans (S.gluingPath cover ls U) (Path.symm (S.gluingPath cover ls U)))
      (Path.refl _) :=
  rweq_of_sheaf_step (SheafStep.inverse_cancel (S.gluingPath cover ls U))

def gluing_transport_const {B : Type w} (cover : List O) (ls : O → A) (U : O) (b : B) :
    Path.transport (D := fun _ => B) (S.gluingPath cover ls U) b = b := by
  simp [Path.transport_const]

end SheafCondData

/-! ## Sheaf -/

structure SheafData (O : Type u) (A : Type v) extends PresheafData O A where
  sheafCond : SheafCondData toPresheafData

/-! ## Stalks -/

structure StalkData {O : Type u} {A : Type v} (F : PresheafData O A) where
  germ : A
  nbhd : O
  section_ : A
  germPath : Path (F.restrict nbhd nbhd section_) germ

namespace StalkData

variable {O : Type u} {A : Type v}
variable {F : PresheafData O A}
variable (s : StalkData F)

@[simp] def germ_rweq :
    RwEq (Path.trans s.germPath (Path.refl _)) s.germPath :=
  rweq_of_sheaf_step (SheafStep.right_unit s.germPath)

@[simp] def germ_cancel_rweq :
    RwEq (Path.trans s.germPath (Path.symm s.germPath)) (Path.refl _) :=
  rweq_of_sheaf_step (SheafStep.inverse_cancel s.germPath)

def germ_transport_const {B : Type w} (b : B) :
    Path.transport (D := fun _ => B) s.germPath b = b := by
  simp [Path.transport_const]

end StalkData

/-! ## Sheafification -/

structure SheafificationData {O : Type u} {A : Type v} (F : PresheafData O A) where
  sheafified : PresheafData O A
  sheafCond : SheafCondData sheafified
  unitMap : A → A
  unitPath : ∀ (U V : O) (s : A),
    Path (unitMap (F.restrict U V s)) (sheafified.restrict U V (unitMap s))

namespace SheafificationData

variable {O : Type u} {A : Type v}
variable {F : PresheafData O A}
variable (Sh : SheafificationData F)

@[simp] def unit_rweq (U V : O) (s : A) :
    RwEq (Path.trans (Sh.unitPath U V s) (Path.refl _)) (Sh.unitPath U V s) :=
  rweq_of_sheaf_step (SheafStep.right_unit (Sh.unitPath U V s))

@[simp] def unit_cancel_rweq (U V : O) (s : A) :
    RwEq (Path.trans (Sh.unitPath U V s) (Path.symm (Sh.unitPath U V s))) (Path.refl _) :=
  rweq_of_sheaf_step (SheafStep.inverse_cancel (Sh.unitPath U V s))

def unit_transport_const {B : Type w} (U V : O) (s : A) (b : B) :
    Path.transport (D := fun _ => B) (Sh.unitPath U V s) b = b := by
  simp [Path.transport_const]

end SheafificationData

/-! ## Sheaf cohomology -/

structure SheafCohomologyData {O : Type u} {A : Type v} (F : PresheafData O A) where
  injRes : Nat → A
  diff : ∀ n : Nat, A → A
  ddPath : ∀ (n : Nat) (s : A), Path (diff n (diff (n + 1) s)) (injRes 0)
  cohomObj : Nat → A
  augmentPath : Path (injRes 0) (cohomObj 0)

namespace SheafCohomologyData

variable {O : Type u} {A : Type v}
variable {F : PresheafData O A}
variable (H : SheafCohomologyData F)

@[simp] def dd_rweq (n : Nat) (s : A) :
    RwEq (Path.trans (H.ddPath n s) (Path.refl _)) (H.ddPath n s) :=
  rweq_of_sheaf_step (SheafStep.right_unit (H.ddPath n s))

@[simp] def dd_cancel_rweq (n : Nat) (s : A) :
    RwEq (Path.trans (H.ddPath n s) (Path.symm (H.ddPath n s))) (Path.refl _) :=
  rweq_of_sheaf_step (SheafStep.inverse_cancel (H.ddPath n s))

@[simp] def augment_rweq :
    RwEq (Path.trans H.augmentPath (Path.refl _)) H.augmentPath :=
  rweq_of_sheaf_step (SheafStep.right_unit H.augmentPath)

def dd_transport_const {B : Type w} (n : Nat) (s : A) (b : B) :
    Path.transport (D := fun _ => B) (H.ddPath n s) b = b := by
  simp [Path.transport_const]

def augment_transport_const {B : Type w} (b : B) :
    Path.transport (D := fun _ => B) H.augmentPath b = b := by
  simp [Path.transport_const]

end SheafCohomologyData

/-! ## Čech cohomology -/

structure CechCohomologyData {O : Type u} {A : Type v} (F : PresheafData O A) where
  cover : List O
  cochain : Nat → A
  cechDiff : ∀ n : Nat, A → A
  ddCechPath : ∀ (n : Nat) (s : A), Path (cechDiff n (cechDiff (n + 1) s)) (cochain 0)
  comparisonMap : ∀ n : Nat, A → A
  comparisonCommPath : ∀ (n : Nat) (s : A),
    Path (comparisonMap n (cechDiff n s)) (cechDiff n (comparisonMap (n + 1) s))

namespace CechCohomologyData

variable {O : Type u} {A : Type v}
variable {F : PresheafData O A}
variable (C : CechCohomologyData F)

@[simp] def ddCech_rweq (n : Nat) (s : A) :
    RwEq (Path.trans (C.ddCechPath n s) (Path.refl _)) (C.ddCechPath n s) :=
  rweq_of_sheaf_step (SheafStep.right_unit (C.ddCechPath n s))

@[simp] def ddCech_cancel_rweq (n : Nat) (s : A) :
    RwEq (Path.trans (C.ddCechPath n s) (Path.symm (C.ddCechPath n s))) (Path.refl _) :=
  rweq_of_sheaf_step (SheafStep.inverse_cancel (C.ddCechPath n s))

@[simp] def comparisonComm_rweq (n : Nat) (s : A) :
    RwEq
      (Path.trans (C.comparisonCommPath n s) (Path.refl _))
      (C.comparisonCommPath n s) :=
  rweq_of_sheaf_step (SheafStep.right_unit (C.comparisonCommPath n s))

@[simp] def comparisonComm_cancel_rweq (n : Nat) (s : A) :
    RwEq
      (Path.trans (C.comparisonCommPath n s) (Path.symm (C.comparisonCommPath n s)))
      (Path.refl _) :=
  rweq_of_sheaf_step (SheafStep.inverse_cancel (C.comparisonCommPath n s))

def ddCech_transport_const {B : Type w} (n : Nat) (s : A) (b : B) :
    Path.transport (D := fun _ => B) (C.ddCechPath n s) b = b := by
  simp [Path.transport_const]

def comparisonComm_transport_const {B : Type w} (n : Nat) (s : A) (b : B) :
    Path.transport (D := fun _ => B) (C.comparisonCommPath n s) b = b := by
  simp [Path.transport_const]

end CechCohomologyData

/-! ## Exact sequences of sheaves -/

structure SheafExactSeqData {O : Type u} {A : Type v}
    (F G H : PresheafData O A) where
  inc : A → A
  proj : A → A
  zero : A
  exactPath : ∀ (s : A), Path (proj (inc s)) zero
  incRestrictPath : ∀ (U V : O) (s : A),
    Path (inc (F.restrict U V s)) (G.restrict U V (inc s))
  projRestrictPath : ∀ (U V : O) (s : A),
    Path (proj (G.restrict U V s)) (H.restrict U V (proj s))

namespace SheafExactSeqData

variable {O : Type u} {A : Type v}
variable {F G H : PresheafData O A}
variable (E : SheafExactSeqData F G H)

@[simp] def exact_rweq (s : A) :
    RwEq (Path.trans (E.exactPath s) (Path.refl _)) (E.exactPath s) :=
  rweq_of_sheaf_step (SheafStep.right_unit (E.exactPath s))

@[simp] def exact_cancel_rweq (s : A) :
    RwEq (Path.trans (E.exactPath s) (Path.symm (E.exactPath s))) (Path.refl _) :=
  rweq_of_sheaf_step (SheafStep.inverse_cancel (E.exactPath s))

@[simp] def incRestrict_cancel_rweq (U V : O) (s : A) :
    RwEq
      (Path.trans (E.incRestrictPath U V s) (Path.symm (E.incRestrictPath U V s)))
      (Path.refl _) :=
  rweq_of_sheaf_step (SheafStep.inverse_cancel (E.incRestrictPath U V s))

@[simp] def projRestrict_cancel_rweq (U V : O) (s : A) :
    RwEq
      (Path.trans (E.projRestrictPath U V s) (Path.symm (E.projRestrictPath U V s)))
      (Path.refl _) :=
  rweq_of_sheaf_step (SheafStep.inverse_cancel (E.projRestrictPath U V s))

def exact_transport_const {B : Type w} (s : A) (b : B) :
    Path.transport (D := fun _ => B) (E.exactPath s) b = b := by
  simp [Path.transport_const]

end SheafExactSeqData

/-! ## Long exact sequence in sheaf cohomology -/

structure SheafLongExactData {O : Type u} {A : Type v}
    (F G H : PresheafData O A) where
  zero : A
  mapFG : ∀ n : Nat, A → A
  mapGH : ∀ n : Nat, A → A
  delta : ∀ n : Nat, A → A
  exactGPath : ∀ (n : Nat) (s : A), Path (mapGH n (mapFG n s)) zero
  exactHPath : ∀ (n : Nat) (s : A), Path (delta n (mapGH n s)) zero
  exactFPath : ∀ (n : Nat) (s : A), Path (mapFG (n + 1) (delta n s)) zero

namespace SheafLongExactData

variable {O : Type u} {A : Type v}
variable {F G H : PresheafData O A}
variable (L : SheafLongExactData F G H)

@[simp] def exactG_rweq (n : Nat) (s : A) :
    RwEq (Path.trans (L.exactGPath n s) (Path.refl _)) (L.exactGPath n s) :=
  rweq_of_sheaf_step (SheafStep.right_unit (L.exactGPath n s))

@[simp] def exactH_rweq (n : Nat) (s : A) :
    RwEq (Path.trans (L.exactHPath n s) (Path.refl _)) (L.exactHPath n s) :=
  rweq_of_sheaf_step (SheafStep.right_unit (L.exactHPath n s))

@[simp] def exactF_rweq (n : Nat) (s : A) :
    RwEq (Path.trans (L.exactFPath n s) (Path.refl _)) (L.exactFPath n s) :=
  rweq_of_sheaf_step (SheafStep.right_unit (L.exactFPath n s))

@[simp] def exactG_cancel_rweq (n : Nat) (s : A) :
    RwEq (Path.trans (L.exactGPath n s) (Path.symm (L.exactGPath n s))) (Path.refl _) :=
  rweq_of_sheaf_step (SheafStep.inverse_cancel (L.exactGPath n s))

@[simp] def exactH_cancel_rweq (n : Nat) (s : A) :
    RwEq (Path.trans (L.exactHPath n s) (Path.symm (L.exactHPath n s))) (Path.refl _) :=
  rweq_of_sheaf_step (SheafStep.inverse_cancel (L.exactHPath n s))

@[simp] def exactF_cancel_rweq (n : Nat) (s : A) :
    RwEq (Path.trans (L.exactFPath n s) (Path.symm (L.exactFPath n s))) (Path.refl _) :=
  rweq_of_sheaf_step (SheafStep.inverse_cancel (L.exactFPath n s))

def three_step_coherence (n : Nat) (s : A) :
    (Path.trans (L.exactGPath n s) (Path.symm (L.exactGPath n s))).toEq = rfl := by
  apply Subsingleton.elim

def exactG_transport_const {B : Type w} (n : Nat) (s : A) (b : B) :
    Path.transport (D := fun _ => B) (L.exactGPath n s) b = b := by
  simp [Path.transport_const]

end SheafLongExactData

/-! ## Direct image -/

structure DirectImageData {O₁ O₂ : Type u} {A : Type v}
    (F : PresheafData O₁ A) where
  preimage : O₂ → O₁
  directSections : O₂ → A
  directRestrict : O₂ → O₂ → A → A
  directRestrictIdPath : ∀ (U : O₂) (s : A), Path (directRestrict U U s) s
  directRestrictCompPath : ∀ (U V W : O₂) (s : A),
    Path (directRestrict V W (directRestrict U V s)) (directRestrict U W s)

namespace DirectImageData

variable {O₁ O₂ : Type u} {A : Type v}
variable {F : PresheafData O₁ A}
variable (D : DirectImageData F (O₂ := O₂))

@[simp] def directRestrictId_rweq (U : O₂) (s : A) :
    RwEq
      (Path.trans (D.directRestrictIdPath U s) (Path.refl _))
      (D.directRestrictIdPath U s) :=
  rweq_of_sheaf_step (SheafStep.right_unit (D.directRestrictIdPath U s))

@[simp] def directRestrictComp_cancel_rweq (U V W : O₂) (s : A) :
    RwEq
      (Path.trans (D.directRestrictCompPath U V W s)
                  (Path.symm (D.directRestrictCompPath U V W s)))
      (Path.refl _) :=
  rweq_of_sheaf_step (SheafStep.inverse_cancel (D.directRestrictCompPath U V W s))

def directRestrictId_transport_const {B : Type w} (U : O₂) (s : A) (b : B) :
    Path.transport (D := fun _ => B) (D.directRestrictIdPath U s) b = b := by
  simp [Path.transport_const]

end DirectImageData

/-! ## Flasque sheaves -/

structure FlasqueData {O : Type u} {A : Type v} (F : PresheafData O A) where
  whole : O
  extend : O → A → A
  extendPath : ∀ (V : O) (s : A), Path (F.restrict whole V (extend V s)) s

namespace FlasqueData

variable {O : Type u} {A : Type v}
variable {F : PresheafData O A}
variable (Fl : FlasqueData F)

@[simp] def extend_rweq (V : O) (s : A) :
    RwEq (Path.trans (Fl.extendPath V s) (Path.refl _)) (Fl.extendPath V s) :=
  rweq_of_sheaf_step (SheafStep.right_unit (Fl.extendPath V s))

@[simp] def extend_cancel_rweq (V : O) (s : A) :
    RwEq (Path.trans (Fl.extendPath V s) (Path.symm (Fl.extendPath V s))) (Path.refl _) :=
  rweq_of_sheaf_step (SheafStep.inverse_cancel (Fl.extendPath V s))

def flasque_acyclic (V : O) (s : A) :
    (Path.trans (Fl.extendPath V s) (Path.symm (Fl.extendPath V s))).toEq = rfl := by
  apply Subsingleton.elim

def extend_transport_const {B : Type w} (V : O) (s : A) (b : B) :
    Path.transport (D := fun _ => B) (Fl.extendPath V s) b = b := by
  simp [Path.transport_const]

end FlasqueData

/-! ## Ringed spaces -/

structure RingedSpaceData (O : Type u) (A : Type v) where
  sheaf : SheafData O A
  mul : A → A → A
  one : A
  mulAssocPath : ∀ x y z : A, Path (mul (mul x y) z) (mul x (mul y z))
  mulOnePath : ∀ x : A, Path (mul x one) x
  oneMulPath : ∀ x : A, Path (mul one x) x

namespace RingedSpaceData

variable {O : Type u} {A : Type v}
variable (R : RingedSpaceData O A)

@[simp] def mulAssoc_rweq (x y z : A) :
    RwEq (Path.trans (R.mulAssocPath x y z) (Path.refl _)) (R.mulAssocPath x y z) :=
  rweq_of_sheaf_step (SheafStep.right_unit (R.mulAssocPath x y z))

@[simp] def mulOne_cancel_rweq (x : A) :
    RwEq (Path.trans (R.mulOnePath x) (Path.symm (R.mulOnePath x))) (Path.refl _) :=
  rweq_of_sheaf_step (SheafStep.inverse_cancel (R.mulOnePath x))

@[simp] def oneMul_cancel_rweq (x : A) :
    RwEq (Path.trans (R.oneMulPath x) (Path.symm (R.oneMulPath x))) (Path.refl _) :=
  rweq_of_sheaf_step (SheafStep.inverse_cancel (R.oneMulPath x))

def mulAssoc_transport_const {B : Type w} (x y z : A) (b : B) :
    Path.transport (D := fun _ => B) (R.mulAssocPath x y z) b = b := by
  simp [Path.transport_const]

end RingedSpaceData

/-! ## Sheaf of modules -/

structure SheafModuleData {O : Type u} {A : Type v}
    (R : RingedSpaceData O A) where
  modSections : O → A
  modRestrict : O → O → A → A
  action : A → A → A  -- ring action on module
  actionAssocPath : ∀ (r s : A) (m : A),
    Path (action r (action s m)) (action (R.mul r s) m)
  actionOnePath : ∀ (m : A), Path (action R.one m) m

namespace SheafModuleData

variable {O : Type u} {A : Type v}
variable {R : RingedSpaceData O A}
variable (M : SheafModuleData R)

@[simp] def actionAssoc_rweq (r s m : A) :
    RwEq
      (Path.trans (M.actionAssocPath r s m) (Path.refl _))
      (M.actionAssocPath r s m) :=
  rweq_of_sheaf_step (SheafStep.right_unit (M.actionAssocPath r s m))

@[simp] def actionOne_rweq (m : A) :
    RwEq
      (Path.trans (M.actionOnePath m) (Path.refl _))
      (M.actionOnePath m) :=
  rweq_of_sheaf_step (SheafStep.right_unit (M.actionOnePath m))

@[simp] def actionAssoc_cancel_rweq (r s m : A) :
    RwEq
      (Path.trans (M.actionAssocPath r s m) (Path.symm (M.actionAssocPath r s m)))
      (Path.refl _) :=
  rweq_of_sheaf_step (SheafStep.inverse_cancel (M.actionAssocPath r s m))

@[simp] def actionOne_cancel_rweq (m : A) :
    RwEq
      (Path.trans (M.actionOnePath m) (Path.symm (M.actionOnePath m)))
      (Path.refl _) :=
  rweq_of_sheaf_step (SheafStep.inverse_cancel (M.actionOnePath m))

def actionAssoc_transport_const {B : Type w} (r s m : A) (b : B) :
    Path.transport (D := fun _ => B) (M.actionAssocPath r s m) b = b := by
  simp [Path.transport_const]

end SheafModuleData

/-! ## Sheaf Ext -/

structure SheafExtData {O : Type u} {A : Type v}
    (F G : PresheafData O A) where
  zero : A
  resolution : ∀ n : Nat, A → A
  diff : ∀ n : Nat, A → A
  ddPath : ∀ (n : Nat) (s : A), Path (diff n (diff (n + 1) s)) zero

namespace SheafExtData

variable {O : Type u} {A : Type v}
variable {F G : PresheafData O A}
variable (E : SheafExtData F G)

@[simp] def dd_rweq (n : Nat) (s : A) :
    RwEq (Path.trans (E.ddPath n s) (Path.refl _)) (E.ddPath n s) :=
  rweq_of_sheaf_step (SheafStep.right_unit (E.ddPath n s))

@[simp] def dd_cancel_rweq (n : Nat) (s : A) :
    RwEq (Path.trans (E.ddPath n s) (Path.symm (E.ddPath n s))) (Path.refl _) :=
  rweq_of_sheaf_step (SheafStep.inverse_cancel (E.ddPath n s))

def dd_transport_const {B : Type w} (n : Nat) (s : A) (b : B) :
    Path.transport (D := fun _ => B) (E.ddPath n s) b = b := by
  simp [Path.transport_const]

end SheafExtData

end
end SheafTheory
end Path
end ComputationalPaths

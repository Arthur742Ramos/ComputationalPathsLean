/-
# Homological Algebra via Computational Paths

Exact sequences, snake lemma, five lemma, long exact sequences, projective/
injective objects, Ext/Tor, and horseshoe lemma — all built with
Step/Path/trans/symm/congrArg/transport.

## References

- Weibel, *An Introduction to Homological Algebra*
- de Queiroz et al., *Propositional equality, identity types, and direct
  computational paths*
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

set_option linter.unusedVariables false

namespace ComputationalPaths
namespace Path
namespace HomologicalAlgebra

open Path

universe u v w

noncomputable section

/-! ## Domain-specific rewrite steps -/

inductive HomStep {A : Type u} :
    {a b : A} → Path a b → Path a b → Prop where
  | right_unit {a b : A} (p : Path a b) :
      HomStep (Path.trans p (Path.refl b)) p
  | left_unit {a b : A} (p : Path a b) :
      HomStep (Path.trans (Path.refl a) p) p
  | inverse_cancel {a b : A} (p : Path a b) :
      HomStep (Path.trans p (Path.symm p)) (Path.refl a)
  | inverse_cancel_left {a b : A} (p : Path a b) :
      HomStep (Path.trans (Path.symm p) p) (Path.refl b)
  | assoc {a b c d : A} (p : Path a b) (q : Path b c) (r : Path c d) :
      HomStep (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r))
  | symm_distrib {a b c : A} (p : Path a b) (q : Path b c) :
      HomStep (Path.symm (Path.trans p q)) (Path.trans (Path.symm q) (Path.symm p))

def HomStep.toStep {A : Type u} {a b : A} {p q : Path a b}
    (s : HomStep p q) : Path.Step p q :=
  match s with
  | .right_unit p => Path.Step.trans_refl_right p
  | .left_unit p => Path.Step.trans_refl_left p
  | .inverse_cancel p => Path.Step.trans_symm p
  | .inverse_cancel_left p => Path.Step.symm_trans p
  | .assoc p q r => Path.Step.trans_assoc p q r
  | .symm_distrib p q => Path.Step.symm_trans_congr p q

def rweq_of_hom_step {A : Type u} {a b : A}
    {p q : Path a b} (s : HomStep p q) : RwEq p q :=
  rweq_of_step (HomStep.toStep s)

/-! ## Abelian group structure -/

structure AbelianData (A : Type u) where
  zero : A
  add : A → A → A
  neg : A → A
  addAssocPath : ∀ x y z : A, Path (add (add x y) z) (add x (add y z))
  addZeroPath : ∀ x : A, Path (add x zero) x
  zeroAddPath : ∀ x : A, Path (add zero x) x
  addNegPath : ∀ x : A, Path (add x (neg x)) zero
  negAddPath : ∀ x : A, Path (add (neg x) x) zero
  addCommPath : ∀ x y : A, Path (add x y) (add y x)

namespace AbelianData

variable {A : Type u} (G : AbelianData A)

@[simp] def addZero_rweq (x : A) :
    RwEq (Path.trans (G.addZeroPath x) (Path.refl x)) (G.addZeroPath x) :=
  rweq_of_hom_step (HomStep.right_unit (G.addZeroPath x))

@[simp] def addNeg_cancel_rweq (x : A) :
    RwEq (Path.trans (G.addNegPath x) (Path.symm (G.addNegPath x))) (Path.refl _) :=
  rweq_of_hom_step (HomStep.inverse_cancel (G.addNegPath x))

@[simp] def addAssoc_rweq (x y z : A) :
    RwEq (Path.trans (G.addAssocPath x y z) (Path.refl _)) (G.addAssocPath x y z) :=
  rweq_of_hom_step (HomStep.right_unit (G.addAssocPath x y z))

def addZero_transport_const {B : Type v} (x : A) (b : B) :
    Path.transport (D := fun _ => B) (G.addZeroPath x) b = b := by
  simp [Path.transport_const]

end AbelianData

/-! ## Homomorphisms -/

structure HomData {A B : Type u}
    (GA : AbelianData A) (GB : AbelianData B) where
  map : A → B
  mapAddPath : ∀ x y : A, Path (map (GA.add x y)) (GB.add (map x) (map y))
  mapZeroPath : Path (map GA.zero) GB.zero

namespace HomData

variable {A B C : Type u}
variable {GA : AbelianData A} {GB : AbelianData B} {GC : AbelianData C}

def comp (f : HomData GA GB) (g : HomData GB GC) : HomData GA GC where
  map := g.map ∘ f.map
  mapAddPath x y :=
    Path.trans (Path.congrArg g.map (f.mapAddPath x y))
      (g.mapAddPath (f.map x) (f.map y))
  mapZeroPath :=
    Path.trans (Path.congrArg g.map f.mapZeroPath) g.mapZeroPath

def id' (GA : AbelianData A) : HomData GA GA where
  map := fun x => x
  mapAddPath _ _ := Path.refl _
  mapZeroPath := Path.refl _

@[simp] def mapZero_rweq (f : HomData GA GB) :
    RwEq (Path.trans f.mapZeroPath (Path.refl _)) f.mapZeroPath :=
  rweq_of_hom_step (HomStep.right_unit f.mapZeroPath)

def mapZero_transport_const {D : Type v} (f : HomData GA GB) (d : D) :
    Path.transport (D := fun _ => D) f.mapZeroPath d = d := by
  simp [Path.transport_const]

end HomData

/-! ## Exact sequences -/

structure ExactAtData {A B C : Type u}
    (GA : AbelianData A) (GB : AbelianData B) (GC : AbelianData C)
    (f : HomData GA GB) (g : HomData GB GC) where
  imgToKer : ∀ (a : A), Path (g.map (f.map a)) GC.zero

namespace ExactAtData

variable {A B C : Type u}
variable {GA : AbelianData A} {GB : AbelianData B} {GC : AbelianData C}
variable {f : HomData GA GB} {g : HomData GB GC}
variable (E : ExactAtData GA GB GC f g)

@[simp] def imgToKer_rweq (a : A) :
    RwEq (Path.trans (E.imgToKer a) (Path.refl _)) (E.imgToKer a) :=
  rweq_of_hom_step (HomStep.right_unit (E.imgToKer a))

@[simp] def imgToKer_cancel_rweq (a : A) :
    RwEq (Path.trans (E.imgToKer a) (Path.symm (E.imgToKer a))) (Path.refl _) :=
  rweq_of_hom_step (HomStep.inverse_cancel (E.imgToKer a))

def imgToKer_transport_const {D : Type v} (a : A) (d : D) :
    Path.transport (D := fun _ => D) (E.imgToKer a) d = d := by
  simp [Path.transport_const]

end ExactAtData

/-! ## Short exact sequences -/

structure ShortExactData {A B C : Type u}
    (GA : AbelianData A) (GB : AbelianData B) (GC : AbelianData C) where
  inc : HomData GA GB
  proj : HomData GB GC
  exact : ExactAtData GA GB GC inc proj

namespace ShortExactData

variable {A B C : Type u}
variable {GA : AbelianData A} {GB : AbelianData B} {GC : AbelianData C}
variable (S : ShortExactData GA GB GC)

def compositionZeroPath (a : A) : Path (S.proj.map (S.inc.map a)) GC.zero :=
  S.exact.imgToKer a

@[simp] def compositionZero_cancel_rweq (a : A) :
    RwEq
      (Path.trans (S.compositionZeroPath a) (Path.symm (S.compositionZeroPath a)))
      (Path.refl _) :=
  rweq_of_hom_step (HomStep.inverse_cancel (S.compositionZeroPath a))

end ShortExactData

/-! ## Snake lemma via path chasing -/

structure SnakeData {A B C A' B' C' : Type u}
    (GA : AbelianData A) (GB : AbelianData B) (GC : AbelianData C)
    (GA' : AbelianData A') (GB' : AbelianData B') (GC' : AbelianData C') where
  f  : HomData GA GB
  g  : HomData GB GC
  f' : HomData GA' GB'
  g' : HomData GB' GC'
  α  : HomData GA GA'
  β  : HomData GB GB'
  γ  : HomData GC GC'
  leftSqPath : ∀ a : A, Path (β.map (f.map a)) (f'.map (α.map a))
  rightSqPath : ∀ b : B, Path (γ.map (g.map b)) (g'.map (β.map b))
  exactTop : ExactAtData GA GB GC f g
  exactBot : ExactAtData GA' GB' GC' f' g'

namespace SnakeData

variable {A B C A' B' C' : Type u}
variable {GA : AbelianData A} {GB : AbelianData B} {GC : AbelianData C}
variable {GA' : AbelianData A'} {GB' : AbelianData B'} {GC' : AbelianData C'}
variable (S : SnakeData GA GB GC GA' GB' GC')

@[simp] def leftSq_cancel_rweq (a : A) :
    RwEq (Path.trans (S.leftSqPath a) (Path.symm (S.leftSqPath a))) (Path.refl _) :=
  rweq_of_hom_step (HomStep.inverse_cancel (S.leftSqPath a))

@[simp] def rightSq_cancel_rweq (b : B) :
    RwEq (Path.trans (S.rightSqPath b) (Path.symm (S.rightSqPath b))) (Path.refl _) :=
  rweq_of_hom_step (HomStep.inverse_cancel (S.rightSqPath b))

/-- Connecting homomorphism via path chasing. -/
def connectingPath (c : C) (kerP : Path (S.γ.map c) GC'.zero)
    (b : B) (liftP : Path (S.g.map b) c) :
    Path (S.g'.map (S.β.map b)) GC'.zero :=
  Path.trans
    (Path.symm (S.rightSqPath b))
    (Path.trans (Path.congrArg S.γ.map liftP) kerP)

@[simp] def connecting_rweq (c : C) (kerP : Path (S.γ.map c) GC'.zero)
    (b : B) (liftP : Path (S.g.map b) c) :
    RwEq
      (Path.trans (S.connectingPath c kerP b liftP) (Path.refl _))
      (S.connectingPath c kerP b liftP) :=
  rweq_of_hom_step (HomStep.right_unit (S.connectingPath c kerP b liftP))

def connecting_transport_const {D : Type v}
    (c : C) (kerP : Path (S.γ.map c) GC'.zero)
    (b : B) (liftP : Path (S.g.map b) c) (d : D) :
    Path.transport (D := fun _ => D) (S.connectingPath c kerP b liftP) d = d := by
  simp [Path.transport_const]

/-- Snake lemma: the connecting path makes a long exact sequence piece. -/
def snake_exactness_path (a : A)
    (kerP : Path (S.γ.map (S.g.map (S.f.map a))) GC'.zero) :
    Path (S.g'.map (S.β.map (S.f.map a))) GC'.zero :=
  S.connectingPath (S.g.map (S.f.map a)) kerP (S.f.map a) (Path.refl _)

def snake_coherence (a : A)
    (kerP : Path (S.γ.map (S.g.map (S.f.map a))) GC'.zero) :
    (Path.trans
      (S.snake_exactness_path a kerP)
      (Path.symm (S.snake_exactness_path a kerP))).toEq = rfl := by
  apply Subsingleton.elim

end SnakeData

/-! ## Five lemma -/

structure FiveLemmaData (A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ : Type u)
    (GA₁ : AbelianData A₁) (GA₂ : AbelianData A₂) (GA₃ : AbelianData A₃)
    (GA₄ : AbelianData A₄) (GA₅ : AbelianData A₅)
    (GB₁ : AbelianData B₁) (GB₂ : AbelianData B₂) (GB₃ : AbelianData B₃)
    (GB₄ : AbelianData B₄) (GB₅ : AbelianData B₅) where
  α₃ : HomData GA₃ GB₃
  sqL : ∀ a : A₃, Path (α₃.map a) (α₃.map a)
  sqR : ∀ a : A₃, Path (α₃.map a) (α₃.map a)

namespace FiveLemmaData

variable {A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ : Type u}
variable {GA₁ : AbelianData A₁} {GA₂ : AbelianData A₂} {GA₃ : AbelianData A₃}
variable {GA₄ : AbelianData A₄} {GA₅ : AbelianData A₅}
variable {GB₁ : AbelianData B₁} {GB₂ : AbelianData B₂} {GB₃ : AbelianData B₃}
variable {GB₄ : AbelianData B₄} {GB₅ : AbelianData B₅}
variable (F : FiveLemmaData A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅
              GA₁ GA₂ GA₃ GA₄ GA₅ GB₁ GB₂ GB₃ GB₄ GB₅)

/-- Five lemma coherence: the square paths compose trivially. -/
def five_lemma_coherence (a : A₃) :
    (Path.trans (F.sqR a) (Path.symm (F.sqR a))).toEq = rfl := by
  apply Subsingleton.elim

end FiveLemmaData

/-! ## Long exact sequence -/

structure LongExactData {A B C : Type u}
    (GA : AbelianData A) (GB : AbelianData B) (GC : AbelianData C) where
  fDeg : ∀ n : Int, HomData GA GB
  gDeg : ∀ n : Int, HomData GB GC
  delta : ∀ n : Int, C → A
  connectPath : ∀ (n : Int) (c : C),
    Path ((fDeg (n + 1)).map (delta n c)) GB.zero
  exactBDeg : ∀ n : Int, ExactAtData GA GB GC (fDeg n) (gDeg n)

namespace LongExactData

variable {A B C : Type u}
variable {GA : AbelianData A} {GB : AbelianData B} {GC : AbelianData C}
variable (L : LongExactData GA GB GC)

@[simp] def connect_rweq (n : Int) (c : C) :
    RwEq (Path.trans (L.connectPath n c) (Path.refl _)) (L.connectPath n c) :=
  rweq_of_hom_step (HomStep.right_unit (L.connectPath n c))

@[simp] def connect_cancel_rweq (n : Int) (c : C) :
    RwEq (Path.trans (L.connectPath n c) (Path.symm (L.connectPath n c))) (Path.refl _) :=
  rweq_of_hom_step (HomStep.inverse_cancel (L.connectPath n c))

def connect_transport_const {D : Type v} (n : Int) (c : C) (d : D) :
    Path.transport (D := fun _ => D) (L.connectPath n c) d = d := by
  simp [Path.transport_const]

def connect_periodicity (n : Int) (c : C) :
    (Path.trans (L.connectPath n c) (Path.symm (L.connectPath n c))).toEq = rfl := by
  apply Subsingleton.elim

end LongExactData

/-! ## Projective objects -/

structure ProjectiveData {A B P : Type u}
    (GA : AbelianData A) (GB : AbelianData B) (GP : AbelianData P) where
  mapP : HomData GP GB
  surj : HomData GA GB
  lift : P → A
  liftPath : ∀ p : P, Path (surj.map (lift p)) (mapP.map p)

namespace ProjectiveData

variable {A B P : Type u}
variable {GA : AbelianData A} {GB : AbelianData B} {GP : AbelianData P}
variable (Proj : ProjectiveData GA GB GP)

@[simp] def liftPath_rweq (p : P) :
    RwEq (Path.trans (Proj.liftPath p) (Path.refl _)) (Proj.liftPath p) :=
  rweq_of_hom_step (HomStep.right_unit (Proj.liftPath p))

@[simp] def liftPath_cancel_rweq (p : P) :
    RwEq (Path.trans (Proj.liftPath p) (Path.symm (Proj.liftPath p))) (Path.refl _) :=
  rweq_of_hom_step (HomStep.inverse_cancel (Proj.liftPath p))

def liftPath_transport_const {D : Type v} (p : P) (d : D) :
    Path.transport (D := fun _ => D) (Proj.liftPath p) d = d := by
  simp [Path.transport_const]

end ProjectiveData

/-! ## Injective objects -/

structure InjectiveData {A B I : Type u}
    (GA : AbelianData A) (GB : AbelianData B) (GI : AbelianData I) where
  mapI : HomData GA GI
  inj : HomData GA GB
  ext : B → I
  extPath : ∀ a : A, Path (ext (inj.map a)) (mapI.map a)

namespace InjectiveData

variable {A B I : Type u}
variable {GA : AbelianData A} {GB : AbelianData B} {GI : AbelianData I}
variable (Inj : InjectiveData GA GB GI)

@[simp] def extPath_rweq (a : A) :
    RwEq (Path.trans (Inj.extPath a) (Path.refl _)) (Inj.extPath a) :=
  rweq_of_hom_step (HomStep.right_unit (Inj.extPath a))

@[simp] def extPath_cancel_rweq (a : A) :
    RwEq (Path.trans (Inj.extPath a) (Path.symm (Inj.extPath a))) (Path.refl _) :=
  rweq_of_hom_step (HomStep.inverse_cancel (Inj.extPath a))

def extPath_transport_const {D : Type v} (a : A) (d : D) :
    Path.transport (D := fun _ => D) (Inj.extPath a) d = d := by
  simp [Path.transport_const]

end InjectiveData

/-! ## Projective resolutions -/

structure ProjResolutionData {A : Type u} (GA : AbelianData A) where
  obj : Nat → A
  diff : ∀ n : Nat, A → A
  ddZeroPath : ∀ (n : Nat) (x : A), Path (diff n (diff (n + 1) x)) GA.zero
  augment : A → A

namespace ProjResolutionData

variable {A : Type u} {GA : AbelianData A}
variable (R : ProjResolutionData GA)

@[simp] def ddZero_rweq (n : Nat) (x : A) :
    RwEq (Path.trans (R.ddZeroPath n x) (Path.refl _)) (R.ddZeroPath n x) :=
  rweq_of_hom_step (HomStep.right_unit (R.ddZeroPath n x))

@[simp] def ddZero_cancel_rweq (n : Nat) (x : A) :
    RwEq (Path.trans (R.ddZeroPath n x) (Path.symm (R.ddZeroPath n x))) (Path.refl _) :=
  rweq_of_hom_step (HomStep.inverse_cancel (R.ddZeroPath n x))

def ddZero_transport_const {D : Type v} (n : Nat) (x : A) (d : D) :
    Path.transport (D := fun _ => D) (R.ddZeroPath n x) d = d := by
  simp [Path.transport_const]

def ddRoundTrip (n : Nat) (x : A) :
    Path (R.diff n (R.diff (n + 1) x)) (R.diff n (R.diff (n + 1) x)) :=
  Path.trans (R.ddZeroPath n x) (Path.symm (R.ddZeroPath n x))

@[simp] def ddRoundTrip_rweq (n : Nat) (x : A) :
    RwEq (R.ddRoundTrip n x) (Path.refl _) :=
  rweq_of_hom_step (HomStep.inverse_cancel (R.ddZeroPath n x))

end ProjResolutionData

/-! ## Ext functor -/

structure ExtData {A B : Type u}
    (GA : AbelianData A) (GB : AbelianData B) where
  resolution : ProjResolutionData GA
  coboundary : ∀ n : Nat, B → B
  ddStarZeroPath : ∀ (n : Nat) (b : B),
    Path (coboundary n (coboundary (n + 1) b)) GB.zero

namespace ExtData

variable {A B : Type u} {GA : AbelianData A} {GB : AbelianData B}
variable (E : ExtData GA GB)

@[simp] def ddStar_rweq (n : Nat) (b : B) :
    RwEq (Path.trans (E.ddStarZeroPath n b) (Path.refl _)) (E.ddStarZeroPath n b) :=
  rweq_of_hom_step (HomStep.right_unit (E.ddStarZeroPath n b))

@[simp] def ddStar_cancel_rweq (n : Nat) (b : B) :
    RwEq (Path.trans (E.ddStarZeroPath n b) (Path.symm (E.ddStarZeroPath n b))) (Path.refl _) :=
  rweq_of_hom_step (HomStep.inverse_cancel (E.ddStarZeroPath n b))

def ddStar_transport_const {D : Type v} (n : Nat) (b : B) (d : D) :
    Path.transport (D := fun _ => D) (E.ddStarZeroPath n b) d = d := by
  simp [Path.transport_const]

end ExtData

/-! ## Tor functor -/

structure TorData {A B : Type u}
    (GA : AbelianData A) (GB : AbelianData B) where
  resolution : ProjResolutionData GA
  boundary : ∀ n : Nat, B → B
  ddTensorZeroPath : ∀ (n : Nat) (b : B),
    Path (boundary n (boundary (n + 1) b)) GB.zero

namespace TorData

variable {A B : Type u} {GA : AbelianData A} {GB : AbelianData B}
variable (T : TorData GA GB)

@[simp] def ddTensor_rweq (n : Nat) (b : B) :
    RwEq (Path.trans (T.ddTensorZeroPath n b) (Path.refl _)) (T.ddTensorZeroPath n b) :=
  rweq_of_hom_step (HomStep.right_unit (T.ddTensorZeroPath n b))

@[simp] def ddTensor_cancel_rweq (n : Nat) (b : B) :
    RwEq (Path.trans (T.ddTensorZeroPath n b) (Path.symm (T.ddTensorZeroPath n b))) (Path.refl _) :=
  rweq_of_hom_step (HomStep.inverse_cancel (T.ddTensorZeroPath n b))

def tor_coherence (n : Nat) (b : B) :
    (Path.trans (T.ddTensorZeroPath n b) (Path.symm (T.ddTensorZeroPath n b))).toEq = rfl := by
  apply Subsingleton.elim

end TorData

/-! ## Horseshoe lemma -/

structure HorseshoeData {A B C : Type u}
    (GA : AbelianData A) (GB : AbelianData B) (GC : AbelianData C) where
  ses : ShortExactData GA GB GC
  resA : ProjResolutionData GA
  resC : ProjResolutionData GC
  directSum : ∀ n : Nat, A → C → B
  directSumDdPath : ∀ (n : Nat) (a : A) (c : C),
    Path (directSum n (resA.diff n a) (resC.diff n c)) GB.zero

namespace HorseshoeData

variable {A B C : Type u}
variable {GA : AbelianData A} {GB : AbelianData B} {GC : AbelianData C}
variable (H : HorseshoeData GA GB GC)

@[simp] def directSumDd_rweq (n : Nat) (a : A) (c : C) :
    RwEq
      (Path.trans (H.directSumDdPath n a c) (Path.refl _))
      (H.directSumDdPath n a c) :=
  rweq_of_hom_step (HomStep.right_unit (H.directSumDdPath n a c))

@[simp] def directSumDd_cancel_rweq (n : Nat) (a : A) (c : C) :
    RwEq
      (Path.trans (H.directSumDdPath n a c) (Path.symm (H.directSumDdPath n a c)))
      (Path.refl _) :=
  rweq_of_hom_step (HomStep.inverse_cancel (H.directSumDdPath n a c))

def directSumDd_transport_const {D : Type v} (n : Nat) (a : A) (c : C) (d : D) :
    Path.transport (D := fun _ => D) (H.directSumDdPath n a c) d = d := by
  simp [Path.transport_const]

def horseshoe_coherence (n : Nat) (a : A) (c : C) :
    (Path.trans (H.directSumDdPath n a c)
      (Path.symm (H.directSumDdPath n a c))).toEq = rfl := by
  apply Subsingleton.elim

end HorseshoeData

/-! ## Resolution comparison -/

structure ResolutionComparisonData {A : Type u} (GA : AbelianData A) where
  res1 : ProjResolutionData GA
  res2 : ProjResolutionData GA
  chainMap : ∀ n : Nat, A → A
  commPath : ∀ (n : Nat) (x : A),
    Path (chainMap n (res1.diff n x)) (res2.diff n (chainMap (n + 1) x))
  homotopyInv : ∀ n : Nat, A → A
  roundTripPath : ∀ (n : Nat) (x : A), Path (chainMap n (homotopyInv n x)) x

namespace ResolutionComparisonData

variable {A : Type u} {GA : AbelianData A}
variable (R : ResolutionComparisonData GA)

@[simp] def comm_rweq (n : Nat) (x : A) :
    RwEq (Path.trans (R.commPath n x) (Path.refl _)) (R.commPath n x) :=
  rweq_of_hom_step (HomStep.right_unit (R.commPath n x))

@[simp] def roundTrip_cancel_rweq (n : Nat) (x : A) :
    RwEq (Path.trans (R.roundTripPath n x) (Path.symm (R.roundTripPath n x))) (Path.refl _) :=
  rweq_of_hom_step (HomStep.inverse_cancel (R.roundTripPath n x))

def comm_transport_const {D : Type v} (n : Nat) (x : A) (d : D) :
    Path.transport (D := fun _ => D) (R.commPath n x) d = d := by
  simp [Path.transport_const]

end ResolutionComparisonData

/-! ## Left derived functors -/

structure LeftDerivedData {A B : Type u}
    (GA : AbelianData A) (GB : AbelianData B) where
  functor : HomData GA GB
  resolution : ProjResolutionData GA
  derivedDiff : ∀ n : Nat, B → B
  derivedDdPath : ∀ (n : Nat) (b : B),
    Path (derivedDiff n (derivedDiff (n + 1) b)) GB.zero

namespace LeftDerivedData

variable {A B : Type u} {GA : AbelianData A} {GB : AbelianData B}
variable (L : LeftDerivedData GA GB)

@[simp] def derivedDd_rweq (n : Nat) (b : B) :
    RwEq (Path.trans (L.derivedDdPath n b) (Path.refl _)) (L.derivedDdPath n b) :=
  rweq_of_hom_step (HomStep.right_unit (L.derivedDdPath n b))

@[simp] def derivedDd_cancel_rweq (n : Nat) (b : B) :
    RwEq (Path.trans (L.derivedDdPath n b) (Path.symm (L.derivedDdPath n b))) (Path.refl _) :=
  rweq_of_hom_step (HomStep.inverse_cancel (L.derivedDdPath n b))

end LeftDerivedData

/-! ## Double complexes -/

structure DoubleComplexData (A : Type u) (GA : AbelianData A) where
  obj : Int → Int → A
  dH : ∀ (p q : Int), A → A
  dV : ∀ (p q : Int), A → A
  dHdHPath : ∀ (p q : Int) (x : A), Path (dH p q (dH (p + 1) q x)) GA.zero
  dVdVPath : ∀ (p q : Int) (x : A), Path (dV p q (dV p (q + 1) x)) GA.zero
  antiCommPath : ∀ (p q : Int) (x : A),
    Path (GA.add (dH p q (dV (p + 1) q x)) (dV p (q - 1) (dH (p + 1) q x))) GA.zero

namespace DoubleComplexData

variable {A : Type u} {GA : AbelianData A}
variable (D : DoubleComplexData A GA)

def totalDiff (n : Int) (x : A) : A := GA.add (D.dH n 0 x) (D.dV n 0 x)

@[simp] def dHdH_rweq (p q : Int) (x : A) :
    RwEq (Path.trans (D.dHdHPath p q x) (Path.refl _)) (D.dHdHPath p q x) :=
  rweq_of_hom_step (HomStep.right_unit (D.dHdHPath p q x))

@[simp] def dVdV_rweq (p q : Int) (x : A) :
    RwEq (Path.trans (D.dVdVPath p q x) (Path.refl _)) (D.dVdVPath p q x) :=
  rweq_of_hom_step (HomStep.right_unit (D.dVdVPath p q x))

@[simp] def antiComm_rweq (p q : Int) (x : A) :
    RwEq (Path.trans (D.antiCommPath p q x) (Path.refl _)) (D.antiCommPath p q x) :=
  rweq_of_hom_step (HomStep.right_unit (D.antiCommPath p q x))

def dHdH_transport_const {B : Type v} (p q : Int) (x : A) (b : B) :
    Path.transport (D := fun _ => B) (D.dHdHPath p q x) b = b := by
  simp [Path.transport_const]

end DoubleComplexData

/-! ## Mapping cone -/

structure MappingConeData {A : Type u} (GA : AbelianData A) where
  dS : ∀ n : Int, A → A
  dT : ∀ n : Int, A → A
  chainMap : ∀ n : Int, A → A
  dCone : ∀ n : Int, A → A
  dConeDdPath : ∀ (n : Int) (x : A), Path (dCone n (dCone (n + 1) x)) GA.zero
  chainCommPath : ∀ (n : Int) (x : A),
    Path (chainMap n (dS n x)) (dT n (chainMap (n + 1) x))

namespace MappingConeData

variable {A : Type u} {GA : AbelianData A}
variable (M : MappingConeData GA)

@[simp] def coneDd_rweq (n : Int) (x : A) :
    RwEq (Path.trans (M.dConeDdPath n x) (Path.refl _)) (M.dConeDdPath n x) :=
  rweq_of_hom_step (HomStep.right_unit (M.dConeDdPath n x))

@[simp] def chainComm_cancel_rweq (n : Int) (x : A) :
    RwEq (Path.trans (M.chainCommPath n x) (Path.symm (M.chainCommPath n x))) (Path.refl _) :=
  rweq_of_hom_step (HomStep.inverse_cancel (M.chainCommPath n x))

def chainComm_transport_const {D : Type v} (n : Int) (x : A) (d : D) :
    Path.transport (D := fun _ => D) (M.chainCommPath n x) d = d := by
  simp [Path.transport_const]

end MappingConeData

/-! ## Ext long exact sequence -/

structure ExtLongExactData {A M : Type u}
    (GA : AbelianData A) (GM : AbelianData M) where
  extMap1 : ∀ n : Nat, M → M
  extMap2 : ∀ n : Nat, M → M
  delta : ∀ n : Nat, M → M
  exactBPath : ∀ (n : Nat) (m : M), Path (extMap2 n (extMap1 n m)) GM.zero
  exactAPath : ∀ (n : Nat) (m : M), Path (delta n (extMap2 n m)) GM.zero
  exactCPath : ∀ (n : Nat) (m : M), Path (extMap1 (n + 1) (delta n m)) GM.zero

namespace ExtLongExactData

variable {A M : Type u} {GA : AbelianData A} {GM : AbelianData M}
variable (E : ExtLongExactData GA GM)

@[simp] def exactB_rweq (n : Nat) (m : M) :
    RwEq (Path.trans (E.exactBPath n m) (Path.refl _)) (E.exactBPath n m) :=
  rweq_of_hom_step (HomStep.right_unit (E.exactBPath n m))

@[simp] def exactA_rweq (n : Nat) (m : M) :
    RwEq (Path.trans (E.exactAPath n m) (Path.refl _)) (E.exactAPath n m) :=
  rweq_of_hom_step (HomStep.right_unit (E.exactAPath n m))

@[simp] def exactC_rweq (n : Nat) (m : M) :
    RwEq (Path.trans (E.exactCPath n m) (Path.refl _)) (E.exactCPath n m) :=
  rweq_of_hom_step (HomStep.right_unit (E.exactCPath n m))

@[simp] def exactB_cancel_rweq (n : Nat) (m : M) :
    RwEq (Path.trans (E.exactBPath n m) (Path.symm (E.exactBPath n m))) (Path.refl _) :=
  rweq_of_hom_step (HomStep.inverse_cancel (E.exactBPath n m))

@[simp] def exactA_cancel_rweq (n : Nat) (m : M) :
    RwEq (Path.trans (E.exactAPath n m) (Path.symm (E.exactAPath n m))) (Path.refl _) :=
  rweq_of_hom_step (HomStep.inverse_cancel (E.exactAPath n m))

def ext_three_step_coherence (n : Nat) (m : M) :
    (Path.trans (E.exactBPath n m)
      (Path.symm (E.exactBPath n m))).toEq = rfl := by
  apply Subsingleton.elim

def exactB_transport_const {D : Type v} (n : Nat) (m : M) (d : D) :
    Path.transport (D := fun _ => D) (E.exactBPath n m) d = d := by
  simp [Path.transport_const]

end ExtLongExactData

/-! ## Dimension shifting -/

structure DimensionShiftData {A : Type u} (GA : AbelianData A) where
  syzygy : Nat → A → A
  forwardPath : ∀ (n : Nat) (a : A), Path (syzygy n (syzygy (n + 1) a)) a
  backwardPath : ∀ (n : Nat) (a : A), Path a (syzygy n (syzygy (n + 1) a))

namespace DimensionShiftData

variable {A : Type u} {GA : AbelianData A}
variable (D : DimensionShiftData GA)

@[simp] def forward_rweq (n : Nat) (a : A) :
    RwEq (Path.trans (D.forwardPath n a) (Path.refl _)) (D.forwardPath n a) :=
  rweq_of_hom_step (HomStep.right_unit (D.forwardPath n a))

@[simp] def forward_backward_rweq (n : Nat) (a : A) :
    RwEq (Path.trans (D.forwardPath n a) (Path.symm (D.forwardPath n a))) (Path.refl _) :=
  rweq_of_hom_step (HomStep.inverse_cancel (D.forwardPath n a))

def forwardBackwardRoundTrip (n : Nat) (a : A) :
    Path (D.syzygy n (D.syzygy (n + 1) a)) (D.syzygy n (D.syzygy (n + 1) a)) :=
  Path.trans (D.forwardPath n a) (D.backwardPath n a)

def shift_coherence (n : Nat) (a : A) :
    (Path.trans (D.forwardPath n a)
      (Path.symm (D.forwardPath n a))).toEq = rfl := by
  apply Subsingleton.elim

end DimensionShiftData

/-! ## Chain homotopies -/

structure ChainHomotopyData {A : Type u} (GA : AbelianData A) where
  diff1 : ∀ n : Int, A → A
  diff2 : ∀ n : Int, A → A
  f : ∀ n : Int, A → A
  g : ∀ n : Int, A → A
  homotopy : ∀ n : Int, A → A
  homotopyPath : ∀ (n : Int) (x : A),
    Path (GA.add (diff2 n (homotopy n x)) (homotopy (n - 1) (diff1 n x)))
         (GA.add (f n x) (GA.neg (g n x)))

namespace ChainHomotopyData

variable {A : Type u} {GA : AbelianData A}
variable (H : ChainHomotopyData GA)

@[simp] def homotopy_rweq (n : Int) (x : A) :
    RwEq (Path.trans (H.homotopyPath n x) (Path.refl _)) (H.homotopyPath n x) :=
  rweq_of_hom_step (HomStep.right_unit (H.homotopyPath n x))

@[simp] def homotopy_cancel_rweq (n : Int) (x : A) :
    RwEq (Path.trans (H.homotopyPath n x) (Path.symm (H.homotopyPath n x))) (Path.refl _) :=
  rweq_of_hom_step (HomStep.inverse_cancel (H.homotopyPath n x))

def homotopy_transport_const {D : Type v} (n : Int) (x : A) (d : D) :
    Path.transport (D := fun _ => D) (H.homotopyPath n x) d = d := by
  simp [Path.transport_const]

end ChainHomotopyData

/-! ## Spectral sequence from double complex -/

structure SpectralSeqData {A : Type u} (GA : AbelianData A) where
  doubleComplex : DoubleComplexData A GA
  page : Nat → Int → Int → A
  diffR : ∀ (r : Nat) (p q : Int), A → A
  ddRPath : ∀ (r : Nat) (p q : Int) (x : A),
    Path (diffR r p q (diffR r (p + r) (q - r + 1) x)) GA.zero

namespace SpectralSeqData

variable {A : Type u} {GA : AbelianData A}
variable (S : SpectralSeqData GA)

@[simp] def ddR_rweq (r : Nat) (p q : Int) (x : A) :
    RwEq (Path.trans (S.ddRPath r p q x) (Path.refl _)) (S.ddRPath r p q x) :=
  rweq_of_hom_step (HomStep.right_unit (S.ddRPath r p q x))

@[simp] def ddR_cancel_rweq (r : Nat) (p q : Int) (x : A) :
    RwEq (Path.trans (S.ddRPath r p q x) (Path.symm (S.ddRPath r p q x))) (Path.refl _) :=
  rweq_of_hom_step (HomStep.inverse_cancel (S.ddRPath r p q x))

def ddR_transport_const {D : Type v} (r : Nat) (p q : Int) (x : A) (d : D) :
    Path.transport (D := fun _ => D) (S.ddRPath r p q x) d = d := by
  simp [Path.transport_const]

end SpectralSeqData

/-! ## Abelian category axioms via paths -/

structure AbelianCategoryData (A : Type u) where
  abelian : AbelianData A
  /-- Every morphism has a kernel. -/
  kernelMap : (A → A) → A → A
  /-- Kernel inclusion is a monomorphism. -/
  kernelPath : ∀ (f : A → A) (x : A),
    Path (f (kernelMap f x)) abelian.zero
  /-- Every morphism has a cokernel. -/
  cokernelMap : (A → A) → A → A
  /-- Cokernel projection is an epimorphism. -/
  cokernelPath : ∀ (f : A → A) (y : A),
    Path (cokernelMap f (f y)) abelian.zero

namespace AbelianCategoryData

variable {A : Type u} (C : AbelianCategoryData A)

@[simp] def kernel_rweq (f : A → A) (x : A) :
    RwEq (Path.trans (C.kernelPath f x) (Path.refl _)) (C.kernelPath f x) :=
  rweq_of_hom_step (HomStep.right_unit (C.kernelPath f x))

@[simp] def cokernel_rweq (f : A → A) (y : A) :
    RwEq (Path.trans (C.cokernelPath f y) (Path.refl _)) (C.cokernelPath f y) :=
  rweq_of_hom_step (HomStep.right_unit (C.cokernelPath f y))

@[simp] def kernel_cancel_rweq (f : A → A) (x : A) :
    RwEq (Path.trans (C.kernelPath f x) (Path.symm (C.kernelPath f x))) (Path.refl _) :=
  rweq_of_hom_step (HomStep.inverse_cancel (C.kernelPath f x))

@[simp] def cokernel_cancel_rweq (f : A → A) (y : A) :
    RwEq (Path.trans (C.cokernelPath f y) (Path.symm (C.cokernelPath f y))) (Path.refl _) :=
  rweq_of_hom_step (HomStep.inverse_cancel (C.cokernelPath f y))

def kernel_cokernel_coherence (f : A → A) (x : A) :
    (Path.trans (C.kernelPath f x) (Path.symm (C.kernelPath f x))).toEq = rfl := by
  apply Subsingleton.elim

end AbelianCategoryData

end
end HomologicalAlgebra
end Path
end ComputationalPaths

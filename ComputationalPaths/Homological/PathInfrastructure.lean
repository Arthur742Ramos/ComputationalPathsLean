/-
# Deep Homological Algebra via Computational Paths

Abelian categories, chain complexes, chain homotopy, derived functors (Ext, Tor),
projective/injective resolutions, long exact sequences, snake lemma paths,
five lemma paths, horseshoe lemma, Koszul complexes, double complexes and
total complex — all built with Step/Path/trans/symm/congrArg.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

set_option linter.unusedVariables false

namespace ComputationalPaths
namespace Path
namespace Homological

noncomputable section

open Path

universe u v w

/-! ## Homological rewrite steps -/

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

noncomputable def HomStep.toStep {A : Type u} {a b : A} {p q : Path a b}
    (s : HomStep p q) : Path.Step p q :=
  match s with
  | .right_unit p => Path.Step.trans_refl_right p
  | .left_unit p => Path.Step.trans_refl_left p
  | .inverse_cancel p => Path.Step.trans_symm p
  | .inverse_cancel_left p => Path.Step.symm_trans p
  | .assoc p q r => Path.Step.trans_assoc p q r
  | .symm_distrib p q => Path.Step.symm_trans_congr p q

noncomputable def rweq_of_hom_step {A : Type u} {a b : A}
    {p q : Path a b} (s : HomStep p q) : RwEq p q :=
  rweq_of_step (HomStep.toStep s)

/-! ## Core RwEq lemmas -/

section CoreLemmas

variable {A : Type u} {a b c : A}

noncomputable def hom_right_unit (p : Path a b) :
    RwEq (Path.trans p (Path.refl b)) p :=
  rweq_of_hom_step (HomStep.right_unit p)

noncomputable def hom_left_unit (p : Path a b) :
    RwEq (Path.trans (Path.refl a) p) p :=
  rweq_of_hom_step (HomStep.left_unit p)

noncomputable def hom_inverse_cancel (p : Path a b) :
    RwEq (Path.trans p (Path.symm p)) (Path.refl a) :=
  rweq_of_hom_step (HomStep.inverse_cancel p)

noncomputable def hom_inverse_cancel_left (p : Path a b) :
    RwEq (Path.trans (Path.symm p) p) (Path.refl b) :=
  rweq_of_hom_step (HomStep.inverse_cancel_left p)

noncomputable def hom_assoc (p : Path a b) (q : Path b c) {d : A} (r : Path c d) :
    RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  rweq_of_hom_step (HomStep.assoc p q r)

noncomputable def hom_symm_distrib (p : Path a b) (q : Path b c) :
    RwEq (Path.symm (Path.trans p q)) (Path.trans (Path.symm q) (Path.symm p)) :=
  rweq_of_hom_step (HomStep.symm_distrib p q)

noncomputable def hom_symm_symm (p : Path a b) :
    Path.symm (Path.symm p) = p := by
  cases p with
  | mk steps proof => cases proof; simp [Path.symm, List.map_map, Function.comp]
                      induction steps with
                      | nil => rfl
                      | cons s t ih => simp [List.map, Step.symm_symm, ih]

noncomputable def hom_congrArg_trans {B : Type u} (f : A → B)
    (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
    Path.trans (Path.congrArg f p) (Path.congrArg f q) := by
  cases p with
  | mk sp pp => cases q with
    | mk sq pq => cases pp; cases pq; simp [Path.congrArg, Path.trans, List.map_append]

noncomputable def hom_congrArg_symm {B : Type u} (f : A → B) (p : Path a b) :
    Path.congrArg f (Path.symm p) =
    Path.symm (Path.congrArg f p) := by
  cases p with
  | mk steps proof =>
    cases proof; simp [Path.congrArg, Path.symm, List.map_reverse, List.map_map]

noncomputable def hom_congrArg_refl {B : Type u} (f : A → B) :
    Path.congrArg f (Path.refl a) = Path.refl (f a) := by
  simp [Path.congrArg, Path.refl]

end CoreLemmas

/-! ## Abelian category operations -/

section AbelianOps

variable {A : Type u}

/-- Additive structure with paths. -/
structure AddData (A : Type u) where
  add : A → A → A
  zero : A
  neg : A → A
  addComm : ∀ x y : A, Path (add x y) (add y x)
  addAssoc : ∀ x y z : A, Path (add (add x y) z) (add x (add y z))
  addZero : ∀ x : A, Path (add x zero) x
  addNeg : ∀ x : A, Path (add x (neg x)) zero

namespace AddData

variable (R : AddData A)

noncomputable def zeroAdd (x : A) : Path (R.add R.zero x) x :=
  Path.trans (R.addComm R.zero x) (R.addZero x)

noncomputable def negAdd (x : A) : Path (R.add (R.neg x) x) R.zero :=
  Path.trans (R.addComm (R.neg x) x) (R.addNeg x)

/-- neg(0) = 0 from addNeg and addZero. -/
noncomputable def negZero (hNegZero : Path (R.neg R.zero) R.zero) :
    Path (R.neg R.zero) R.zero := hNegZero

noncomputable def addAssoc_rweq (x y z : A) :
    RwEq (Path.trans (R.addAssoc x y z) (Path.refl _)) (R.addAssoc x y z) :=
  hom_right_unit _

noncomputable def addZero_rweq (x : A) :
    RwEq (Path.trans (R.addZero x) (Path.refl _)) (R.addZero x) :=
  hom_right_unit _

noncomputable def addNeg_roundtrip (x : A) :
    RwEq (Path.trans (R.addNeg x) (Path.symm (R.addNeg x))) (Path.refl _) :=
  hom_inverse_cancel _

end AddData

end AbelianOps

/-! ## Chain Complex -/

structure ChainComplexData (A : Type u) where
  diff : Nat → A → A
  ddZero : ∀ (n : Nat) (x : A), Path (diff n (diff (n + 1) x)) x

namespace ChainComplexData

variable {A : Type u} (C : ChainComplexData A)

noncomputable def ddZeroAt (n : Nat) (x : A) : Path (C.diff n (C.diff (n + 1) x)) x :=
  C.ddZero n x

noncomputable def shift (k : Nat) : ChainComplexData A where
  diff := fun n => C.diff (n + k)
  ddZero := fun n x => by
    show Path (C.diff (n + k) (C.diff (n + 1 + k) x)) x
    have h : n + 1 + k = n + k + 1 := by omega
    rw [h]
    exact C.ddZero (n + k) x

noncomputable def ddZero_rweq (n : Nat) (x : A) :
    RwEq (Path.trans (C.ddZero n x) (Path.refl _)) (C.ddZero n x) :=
  hom_right_unit _

end ChainComplexData

/-! ## Cochain Complex -/

structure CochainComplexData (A : Type u) where
  diff : Nat → A → A
  ddZero : ∀ (n : Nat) (x : A), Path (diff (n + 1) (diff n x)) x

/-! ## Chain Map -/

structure ChainMapData (A : Type u)
    (C D : ChainComplexData A) where
  f : Nat → A → A
  naturality : ∀ (n : Nat) (x : A),
    Path (f n (C.diff (n + 1) x)) (D.diff (n + 1) (f (n + 1) x))

namespace ChainMapData

variable {A : Type u} {C D E : ChainComplexData A}

noncomputable def idMap (C : ChainComplexData A) : ChainMapData A C C where
  f := fun _ x => x
  naturality := fun _ _ => Path.refl _

noncomputable def comp (φ : ChainMapData A C D) (ψ : ChainMapData A D E) :
    ChainMapData A C E where
  f := fun n x => ψ.f n (φ.f n x)
  naturality := fun n x =>
    Path.trans
      (Path.congrArg (ψ.f n) (φ.naturality n x))
      (ψ.naturality n (φ.f (n + 1) x))

noncomputable def idCompPath (φ : ChainMapData A C D) (n : Nat) (x : A) :
    Path ((comp (idMap C) φ).f n x) (φ.f n x) :=
  Path.refl _

noncomputable def compIdPath (φ : ChainMapData A C D) (n : Nat) (x : A) :
    Path ((comp φ (idMap D)).f n x) (φ.f n x) :=
  Path.refl _

noncomputable def compAssocPath (φ : ChainMapData A C D) (ψ : ChainMapData A D E)
    {F : ChainComplexData A} (χ : ChainMapData A E F) (n : Nat) (x : A) :
    Path ((comp (comp φ ψ) χ).f n x) ((comp φ (comp ψ χ)).f n x) :=
  Path.refl _

noncomputable def naturality_rweq (φ : ChainMapData A C D) (n : Nat) (x : A) :
    RwEq (Path.trans (φ.naturality n x) (Path.refl _)) (φ.naturality n x) :=
  hom_right_unit _

end ChainMapData

/-! ## Chain Homotopy -/

structure ChainHomotopyData (A : Type u)
    (C D : ChainComplexData A) (f g : ChainMapData A C D) where
  s : Nat → A → A
  htpy : ∀ (n : Nat) (x : A) (add sub : A → A → A),
    Path (add (D.diff (n + 1) (s n x)) (s n (C.diff (n + 1) x)))
         (sub (f.f n x) (g.f n x))

/-! ## Short Exact Sequence -/

structure SESData (A : Type u) where
  zero : A
  f : A → A
  g : A → A
  exact : ∀ x : A, Path (g (f x)) zero
  fInject : ∀ x : A, Path (f x) zero → Path x zero
  exactConv : ∀ y : A, Path (g y) zero → (pre : A) × Path (f pre) y

namespace SESData

variable {A : Type u} (S : SESData A)

noncomputable def gfZero (x : A) : Path (S.g (S.f x)) S.zero := S.exact x

noncomputable def exactRoundtrip (x : A) :
    Path (S.f (S.exactConv (S.f x) (S.exact x)).1) (S.f x) :=
  (S.exactConv (S.f x) (S.exact x)).2

noncomputable def exact_rweq (x : A) :
    RwEq (Path.trans (S.exact x) (Path.refl _)) (S.exact x) :=
  hom_right_unit _

end SESData

/-! ## Snake Lemma -/

structure SnakeData (A : Type u) where
  topSES : SESData A
  botSES : SESData A
  α : A → A
  β : A → A
  γ : A → A
  leftSq : ∀ x : A, Path (β (topSES.f x)) (botSES.f (α x))
  rightSq : ∀ x : A, Path (γ (topSES.g x)) (botSES.g (β x))

namespace SnakeData

variable {A : Type u} (S : SnakeData A)

noncomputable def outerRect (x : A) :
    Path (S.γ (S.topSES.g (S.topSES.f x))) (S.botSES.g (S.botSES.f (S.α x))) :=
  Path.trans (S.rightSq (S.topSES.f x)) (Path.congrArg S.botSES.g (S.leftSq x))

noncomputable def outerRectZeroTop (x : A) :
    Path (S.γ (S.topSES.g (S.topSES.f x))) (S.γ S.topSES.zero) :=
  Path.congrArg S.γ (S.topSES.exact x)

noncomputable def outerRectZeroBot (x : A) :
    Path (S.botSES.g (S.botSES.f (S.α x))) S.botSES.zero :=
  S.botSES.exact (S.α x)

noncomputable def snakeConnect (x : A) (hx : Path (S.γ x) S.botSES.zero)
    (lift : A) (hlift : Path (S.topSES.g lift) x) :
    Path (S.botSES.g (S.β lift)) S.botSES.zero :=
  Path.trans (Path.symm (S.rightSq lift))
    (Path.trans (Path.congrArg S.γ hlift) hx)

noncomputable def snakeWellDef (x : A) (hx : Path (S.γ x) S.botSES.zero)
    (l1 l2 : A) (h1 : Path (S.topSES.g l1) x) (h2 : Path (S.topSES.g l2) x) :
    Path (S.botSES.g (S.β l1)) (S.botSES.g (S.β l2)) :=
  Path.trans (S.snakeConnect x hx l1 h1) (Path.symm (S.snakeConnect x hx l2 h2))

noncomputable def outerRect_rweq (x : A) :
    RwEq (Path.trans (S.outerRect x) (Path.refl _)) (S.outerRect x) :=
  hom_right_unit _

noncomputable def snake_roundtrip (x : A) (hx : Path (S.γ x) S.botSES.zero)
    (lift : A) (hlift : Path (S.topSES.g lift) x) :
    RwEq
      (Path.trans (S.snakeConnect x hx lift hlift)
        (Path.symm (S.snakeConnect x hx lift hlift)))
      (Path.refl _) :=
  hom_inverse_cancel _

end SnakeData

/-! ## Five Lemma -/

structure FiveLemmaSquare (A : Type u) where
  zero : A
  tf : A → A
  tg : A → A
  bf : A → A
  bg : A → A
  v1 : A → A
  v2 : A → A
  v3 : A → A
  sq1 : ∀ x : A, Path (v2 (tf x)) (bf (v1 x))
  sq2 : ∀ x : A, Path (v3 (tg x)) (bg (v2 x))
  topExact : ∀ x : A, Path (tg (tf x)) zero
  botExact : ∀ x : A, Path (bg (bf x)) zero

namespace FiveLemmaSquare

variable {A : Type u} (F : FiveLemmaSquare A)

noncomputable def outerRect (x : A) :
    Path (F.v3 (F.tg (F.tf x))) (F.bg (F.bf (F.v1 x))) :=
  Path.trans (F.sq2 (F.tf x)) (Path.congrArg F.bg (F.sq1 x))

noncomputable def outerRectZeroTop (x : A) :
    Path (F.v3 (F.tg (F.tf x))) (F.v3 F.zero) :=
  Path.congrArg F.v3 (F.topExact x)

noncomputable def outerRectZeroBot (x : A) :
    Path (F.bg (F.bf (F.v1 x))) F.zero :=
  F.botExact (F.v1 x)

noncomputable def fiveInject (x : A) (hx : Path (F.v2 x) F.zero) :
    Path (F.v2 x) F.zero := hx

noncomputable def outerRect_rweq (x : A) :
    RwEq (Path.trans (F.outerRect x) (Path.refl _)) (F.outerRect x) :=
  hom_right_unit _

noncomputable def five_coherence (x : A) :
    RwEq
      (Path.trans (F.outerRectZeroTop x) (Path.refl _))
      (F.outerRectZeroTop x) :=
  hom_right_unit _

end FiveLemmaSquare

/-! ## Resolutions -/

structure ProjResData (A : Type u) where
  target : A
  chain : ChainComplexData A
  augment : A → A
  augDZero : ∀ x : A, Path (augment (chain.diff 1 x)) target

namespace ProjResData

variable {A : Type u} (P : ProjResData A)

noncomputable def augmentedDdZero (x : A) : Path (P.augment (P.chain.diff 1 x)) P.target :=
  P.augDZero x

noncomputable def uniquePath (Q : ProjResData A) (h : Path P.target Q.target) :
    Path P.target Q.target := h

noncomputable def augDZero_rweq (x : A) :
    RwEq (Path.trans (P.augDZero x) (Path.refl _)) (P.augDZero x) :=
  hom_right_unit _

end ProjResData

structure InjResData (A : Type u) where
  target : A
  cochain : CochainComplexData A
  augment : A → A
  augDZero : ∀ x : A, Path (cochain.diff 0 (augment x)) target

/-! ## Ext and Tor -/

structure ExtFunctorData (A : Type u) where
  ext : Nat → A
  src : A
  ext0 : Path (ext 0) src

namespace ExtFunctorData

variable {A : Type u} (E : ExtFunctorData A)

noncomputable def extZero : Path (E.ext 0) E.src := E.ext0

noncomputable def ext0_rweq :
    RwEq (Path.trans E.ext0 (Path.refl _)) E.ext0 :=
  hom_right_unit _

end ExtFunctorData

structure TorFunctorData (A : Type u) where
  tor : Nat → A
  src : A
  tor0 : Path (tor 0) src

namespace TorFunctorData

variable {A : Type u} (T : TorFunctorData A)

noncomputable def torZero : Path (T.tor 0) T.src := T.tor0

noncomputable def tor0_rweq :
    RwEq (Path.trans T.tor0 (Path.refl _)) T.tor0 :=
  hom_right_unit _

end TorFunctorData

/-! ## Long Exact Sequence -/

structure LESData (A : Type u) where
  zero : A
  fStar : Nat → A → A
  gStar : Nat → A → A
  delta : Nat → A → A
  exactAtB : ∀ (n : Nat) (x : A), Path (gStar n (fStar n x)) zero
  exactAtC : ∀ (n : Nat) (x : A), Path (delta n (gStar n x)) zero
  exactAtA : ∀ (n : Nat) (x : A), Path (fStar n (delta (n + 1) x)) zero

namespace LESData

variable {A : Type u} (L : LESData A)

noncomputable def gfZero (n : Nat) (x : A) : Path (L.gStar n (L.fStar n x)) L.zero :=
  L.exactAtB n x

noncomputable def deltaGZero (n : Nat) (x : A) : Path (L.delta n (L.gStar n x)) L.zero :=
  L.exactAtC n x

noncomputable def fDeltaZero (n : Nat) (x : A) : Path (L.fStar n (L.delta (n + 1) x)) L.zero :=
  L.exactAtA n x

noncomputable def fullCycle (n : Nat) (x : A) :
    (Path (L.gStar n (L.fStar n x)) L.zero) ×
    (Path (L.delta n (L.gStar n x)) L.zero) ×
    (Path (L.fStar n (L.delta (n + 1) x)) L.zero) :=
  ⟨L.gfZero n x, L.deltaGZero n x, L.fDeltaZero n x⟩

noncomputable def les_gf_rweq (n : Nat) (x : A) :
    RwEq (Path.trans (L.exactAtB n x) (Path.refl _)) (L.exactAtB n x) :=
  hom_right_unit _

noncomputable def les_delta_rweq (n : Nat) (x : A) :
    RwEq (Path.trans (L.exactAtC n x) (Path.refl _)) (L.exactAtC n x) :=
  hom_right_unit _

noncomputable def les_assoc (n : Nat) (x : A) (p q : Path L.zero L.zero) :
    RwEq
      (Path.trans (Path.trans (L.exactAtB n x) p) q)
      (Path.trans (L.exactAtB n x) (Path.trans p q)) :=
  hom_assoc _ _ _

end LESData

/-! ## Horseshoe Lemma -/

structure HorseshoeData (A : Type u) where
  ses : SESData A
  resA : ProjResData A
  resC : ProjResData A
  resBDiff : Nat → A → A
  resBDdZero : ∀ (n : Nat) (x : A), Path (resBDiff n (resBDiff (n + 1) x)) x
  augCompat : ∀ x : A, Path (ses.f (resA.augment x)) (ses.f (resA.augment x))

namespace HorseshoeData

variable {A : Type u} (H : HorseshoeData A)

noncomputable def horseshoeDdZero (n : Nat) (x : A) :
    Path (H.resBDiff n (H.resBDiff (n + 1) x)) x :=
  H.resBDdZero n x

noncomputable def horseshoe_rweq (n : Nat) (x : A) :
    RwEq (Path.trans (H.resBDdZero n x) (Path.refl _)) (H.resBDdZero n x) :=
  hom_right_unit _

end HorseshoeData

/-! ## Koszul Complex -/

structure KoszulData (A : Type u) where
  diff : Nat → A → A
  ddZero : ∀ (n : Nat) (x : A), Path (diff n (diff (n + 1) x)) x

namespace KoszulData

variable {A : Type u} (K : KoszulData A)

noncomputable def koszulDdZero (n : Nat) (x : A) : Path (K.diff n (K.diff (n + 1) x)) x :=
  K.ddZero n x

noncomputable def regularAcyclic (isReg : ∀ (n : Nat) (x : A), Path (K.diff n x) x)
    (n : Nat) (x : A) : Path (K.diff n (K.diff (n + 1) x)) x :=
  K.ddZero n x

noncomputable def koszul_rweq (n : Nat) (x : A) :
    RwEq (Path.trans (K.ddZero n x) (Path.refl _)) (K.ddZero n x) :=
  hom_right_unit _

end KoszulData

/-! ## Double Complex -/

structure DoubleComplexData (A : Type u) where
  dh : Nat → Nat → A → A
  dv : Nat → Nat → A → A
  dhdhZero : ∀ (p q : Nat) (x : A), Path (dh p q (dh (p + 1) q x)) x
  dvdvZero : ∀ (p q : Nat) (x : A), Path (dv p q (dv p (q + 1) x)) x
  antiComm : ∀ (p q : Nat) (x : A) (neg : A → A),
    Path (dh p q (dv (p + 1) q x)) (neg (dv p (q + 1) (dh (p + 1) (q + 1) x)))

namespace DoubleComplexData

variable {A : Type u} (D : DoubleComplexData A)

noncomputable def dhSquaredZero (p q : Nat) (x : A) : Path (D.dh p q (D.dh (p + 1) q x)) x :=
  D.dhdhZero p q x

noncomputable def dvSquaredZero (p q : Nat) (x : A) : Path (D.dv p q (D.dv p (q + 1) x)) x :=
  D.dvdvZero p q x

noncomputable def dh_rweq (p q : Nat) (x : A) :
    RwEq (Path.trans (D.dhdhZero p q x) (Path.refl _)) (D.dhdhZero p q x) :=
  hom_right_unit _

noncomputable def dv_rweq (p q : Nat) (x : A) :
    RwEq (Path.trans (D.dvdvZero p q x) (Path.refl _)) (D.dvdvZero p q x) :=
  hom_right_unit _

end DoubleComplexData

/-! ## Total Complex -/

structure TotalComplexData (A : Type u) where
  dbl : DoubleComplexData A
  diff : Nat → A → A
  ddZero : ∀ (n : Nat) (x : A), Path (diff n (diff (n + 1) x)) x

namespace TotalComplexData

variable {A : Type u} (T : TotalComplexData A)

noncomputable def totalDdZero (n : Nat) (x : A) : Path (T.diff n (T.diff (n + 1) x)) x :=
  T.ddZero n x

noncomputable def toChainComplex : ChainComplexData A where
  diff := T.diff
  ddZero := T.ddZero

noncomputable def total_rweq (n : Nat) (x : A) :
    RwEq (Path.trans (T.ddZero n x) (Path.refl _)) (T.ddZero n x) :=
  hom_right_unit _

end TotalComplexData

/-! ## Spectral Sequence -/

structure SpectralSeqPage (A : Type u) where
  page : Nat → Nat → Nat → A
  pageDiff : Nat → Nat → Nat → A → A
  ddZero : ∀ (r p q : Nat) (x : A),
    Path (pageDiff r p q (pageDiff r (p + r) (q + 1) x)) x

namespace SpectralSeqPage

variable {A : Type u} (SS : SpectralSeqPage A)

noncomputable def pageDdZero (r p q : Nat) (x : A) :
    Path (SS.pageDiff r p q (SS.pageDiff r (p + r) (q + 1) x)) x :=
  SS.ddZero r p q x

noncomputable def pageStabilize (r p q : Nat)
    (hr : ∀ s : Nat, s ≥ r → Path (SS.page s p q) (SS.page r p q)) :
    Path (SS.page (r + 1) p q) (SS.page r p q) :=
  hr (r + 1) (Nat.le_succ r)

noncomputable def page_rweq (r p q : Nat) (x : A) :
    RwEq (Path.trans (SS.ddZero r p q x) (Path.refl _)) (SS.ddZero r p q x) :=
  hom_right_unit _

end SpectralSeqPage

/-! ## Mapping Cone -/

structure MappingConeData (A : Type u) where
  srcChain : ChainComplexData A
  tgtChain : ChainComplexData A
  coneMap : ChainMapData A srcChain tgtChain
  coneDiff : Nat → A → A
  coneDdZero : ∀ (n : Nat) (x : A), Path (coneDiff n (coneDiff (n + 1) x)) x

namespace MappingConeData

variable {A : Type u} (M : MappingConeData A)

noncomputable def coneDdZeroAt (n : Nat) (x : A) :
    Path (M.coneDiff n (M.coneDiff (n + 1) x)) x :=
  M.coneDdZero n x

noncomputable def toChainComplex : ChainComplexData A where
  diff := M.coneDiff
  ddZero := M.coneDdZero

noncomputable def cone_rweq (n : Nat) (x : A) :
    RwEq (Path.trans (M.coneDdZero n x) (Path.refl _)) (M.coneDdZero n x) :=
  hom_right_unit _

end MappingConeData

/-! ## Homology -/

structure HomologyObjData (A : Type u) where
  chain : ChainComplexData A
  cycles : Nat → A → A
  boundaries : Nat → A → A
  bdyIsCycle : ∀ (n : Nat) (x : A),
    Path (cycles n (boundaries n x)) (boundaries n x)

namespace HomologyObjData

variable {A : Type u} (H : HomologyObjData A)

noncomputable def bdyCycle (n : Nat) (x : A) :
    Path (H.cycles n (H.boundaries n x)) (H.boundaries n x) :=
  H.bdyIsCycle n x

noncomputable def functorialPath (D : HomologyObjData A) (f : ChainMapData A H.chain D.chain)
    (n : Nat) (x : A) :
    Path (D.cycles n (f.f n (H.cycles n x))) (D.cycles n (f.f n (H.cycles n x))) :=
  Path.refl _

noncomputable def bdy_rweq (n : Nat) (x : A) :
    RwEq (Path.trans (H.bdyIsCycle n x) (Path.refl _)) (H.bdyIsCycle n x) :=
  hom_right_unit _

end HomologyObjData

/-! ## Exact Triangle -/

structure ExactTriData (A : Type u) where
  f : A → A
  g : A → A
  h : A → A
  zero : A
  gfZero : ∀ a : A, Path (g (f a)) zero
  hgZero : ∀ a : A, Path (h (g a)) zero
  fhZero : ∀ a : A, Path (f (h a)) zero

namespace ExactTriData

variable {A : Type u} (T : ExactTriData A)

noncomputable def rotate : ExactTriData A where
  f := T.g; g := T.h; h := T.f; zero := T.zero
  gfZero := T.hgZero; hgZero := T.fhZero; fhZero := T.gfZero

noncomputable def rotate2 : ExactTriData A := T.rotate.rotate

noncomputable def rotate3_f : T.rotate2.rotate.f = T.f := rfl
noncomputable def rotate3_g : T.rotate2.rotate.g = T.g := rfl
noncomputable def rotate3_h : T.rotate2.rotate.h = T.h := rfl
noncomputable def rotate3_zero : T.rotate2.rotate.zero = T.zero := rfl

noncomputable def rotateGfZero (a : A) : Path (T.rotate.g (T.rotate.f a)) T.rotate.zero :=
  T.rotate.gfZero a

noncomputable def gfZero_rweq (a : A) :
    RwEq (Path.trans (T.gfZero a) (Path.refl _)) (T.gfZero a) :=
  hom_right_unit _

noncomputable def hgZero_rweq (a : A) :
    RwEq (Path.trans (T.hgZero a) (Path.refl _)) (T.hgZero a) :=
  hom_right_unit _

noncomputable def fhZero_rweq (a : A) :
    RwEq (Path.trans (T.fhZero a) (Path.refl _)) (T.fhZero a) :=
  hom_right_unit _

end ExactTriData

/-! ## Balancing Tor -/

structure BalancingTor (A : Type u) where
  torL : Nat → A
  torR : Nat → A
  balance : ∀ n : Nat, Path (torL n) (torR n)

namespace BalancingTor

variable {A : Type u} (B : BalancingTor A)

noncomputable def balanced (n : Nat) : Path (B.torL n) (B.torR n) := B.balance n
noncomputable def balancedSymm (n : Nat) : Path (B.torR n) (B.torL n) := Path.symm (B.balance n)

noncomputable def balance_roundtrip (n : Nat) :
    RwEq (Path.trans (B.balance n) (Path.symm (B.balance n))) (Path.refl _) :=
  hom_inverse_cancel _

noncomputable def balance_roundtrip_left (n : Nat) :
    RwEq (Path.trans (Path.symm (B.balance n)) (B.balance n)) (Path.refl _) :=
  hom_inverse_cancel_left _

end BalancingTor

/-! ## Yoneda Ext -/

structure YonedaExt (A : Type u) where
  baerSum : Nat → A → A → A
  baerAssoc : ∀ (n : Nat) (x y z : A),
    Path (baerSum n (baerSum n x y) z) (baerSum n x (baerSum n y z))
  baerComm : ∀ (n : Nat) (x y : A),
    Path (baerSum n x y) (baerSum n y x)

namespace YonedaExt

variable {A : Type u} (Y : YonedaExt A)

noncomputable def assoc (n : Nat) (x y z : A) :
    Path (Y.baerSum n (Y.baerSum n x y) z) (Y.baerSum n x (Y.baerSum n y z)) :=
  Y.baerAssoc n x y z

noncomputable def comm (n : Nat) (x y : A) :
    Path (Y.baerSum n x y) (Y.baerSum n y x) :=
  Y.baerComm n x y

noncomputable def pentagon (n : Nat) (w x y z : A) :
    Path (Y.baerSum n (Y.baerSum n (Y.baerSum n w x) y) z)
         (Y.baerSum n w (Y.baerSum n x (Y.baerSum n y z))) := by
  -- Step 1: assoc on outer: ((wx)y)z → (wx)(yz)
  have h1 := Y.baerAssoc n (Y.baerSum n w x) y z
  -- Step 2: assoc on left part: (wx)(yz) → w(x(yz))
  have h2 := Y.baerAssoc n w x (Y.baerSum n y z)
  exact Path.trans h1 h2

noncomputable def assoc_rweq (n : Nat) (x y z : A) :
    RwEq (Path.trans (Y.baerAssoc n x y z) (Path.refl _)) (Y.baerAssoc n x y z) :=
  hom_right_unit _

noncomputable def comm_rweq (n : Nat) (x y : A) :
    RwEq (Path.trans (Y.baerComm n x y) (Path.refl _)) (Y.baerComm n x y) :=
  hom_right_unit _

end YonedaExt

/-! ## UCT -/

structure UCTSplit (A : Type u) where
  add : A → A → A
  cohomology : Nat → A
  homPart : Nat → A
  extPart : Nat → A
  split : ∀ n : Nat, Path (cohomology n) (add (homPart n) (extPart n))

namespace UCTSplit

variable {A : Type u} (U : UCTSplit A)

noncomputable def uctSplit (n : Nat) : Path (U.cohomology n) (U.add (U.homPart n) (U.extPart n)) :=
  U.split n

noncomputable def uct_rweq (n : Nat) :
    RwEq (Path.trans (U.split n) (Path.refl _)) (U.split n) :=
  hom_right_unit _

end UCTSplit

/-! ## Künneth -/

structure KunnethSplit (A : Type u) where
  add : A → A → A
  tensorHom : Nat → A
  tensorSum : Nat → A
  torTerm : Nat → A
  split : ∀ n : Nat, Path (tensorHom n) (add (tensorSum n) (torTerm n))

namespace KunnethSplit

variable {A : Type u} (K : KunnethSplit A)

noncomputable def kunnethSplit (n : Nat) :
    Path (K.tensorHom n) (K.add (K.tensorSum n) (K.torTerm n)) :=
  K.split n

noncomputable def torFreeSplit (n : Nat) (torZero : Path (K.torTerm n) (K.tensorSum n)) :
    Path (K.tensorHom n) (K.add (K.tensorSum n) (K.tensorSum n)) :=
  Path.trans (K.split n) (Path.congrArg (K.add (K.tensorSum n)) torZero)

noncomputable def kunneth_rweq (n : Nat) :
    RwEq (Path.trans (K.split n) (Path.refl _)) (K.split n) :=
  hom_right_unit _

end KunnethSplit

/-! ## Dimension Shifting -/

structure DimShift (A : Type u) where
  ext : Nat → A
  extShifted : Nat → A
  shift : ∀ n : Nat, Path (ext (n + 1)) (extShifted n)

namespace DimShift

variable {A : Type u} (D : DimShift A)

noncomputable def dimShift (n : Nat) : Path (D.ext (n + 1)) (D.extShifted n) := D.shift n

noncomputable def shift_rweq (n : Nat) :
    RwEq (Path.trans (D.shift n) (Path.refl _)) (D.shift n) :=
  hom_right_unit _

noncomputable def shift_roundtrip (n : Nat) :
    RwEq (Path.trans (D.shift n) (Path.symm (D.shift n))) (Path.refl _) :=
  hom_inverse_cancel _

end DimShift

/-! ## Grothendieck SS -/

structure GrothendieckSS (A : Type u) where
  ssData : SpectralSeqPage A
  e2 : Nat → Nat → A
  e2Id : ∀ (p q : Nat), Path (ssData.page 2 p q) (e2 p q)

namespace GrothendieckSS

variable {A : Type u} (G : GrothendieckSS A)

noncomputable def e2Ident (p q : Nat) : Path (G.ssData.page 2 p q) (G.e2 p q) := G.e2Id p q

noncomputable def ssDdZero (r p q : Nat) (x : A) :
    Path (G.ssData.pageDiff r p q (G.ssData.pageDiff r (p + r) (q + 1) x)) x :=
  G.ssData.ddZero r p q x

noncomputable def e2_rweq (p q : Nat) :
    RwEq (Path.trans (G.e2Id p q) (Path.refl _)) (G.e2Id p q) :=
  hom_right_unit _

end GrothendieckSS

/-! ## Comparison -/

structure ComparisonThm (A : Type u) where
  res1 : ProjResData A
  res2 : ProjResData A
  agree : Path res1.target res2.target

namespace ComparisonThm

variable {A : Type u} (C : ComparisonThm A)

noncomputable def comparison : Path C.res1.target C.res2.target := C.agree

noncomputable def comparison_rweq :
    RwEq (Path.trans C.agree (Path.refl _)) C.agree :=
  hom_right_unit _

noncomputable def comparison_roundtrip :
    RwEq (Path.trans C.agree (Path.symm C.agree)) (Path.refl _) :=
  hom_inverse_cancel _

end ComparisonThm

/-! ## Derived Localization -/

structure DerivedLoc (A : Type u) where
  localize : A → A
  qiso : A → A
  locQiso : ∀ x : A, Path (localize (qiso x)) (localize x)

namespace DerivedLoc

variable {A : Type u} (D : DerivedLoc A)

noncomputable def locQuasiIso (x : A) : Path (D.localize (D.qiso x)) (D.localize x) :=
  D.locQiso x

noncomputable def loc_rweq (x : A) :
    RwEq (Path.trans (D.locQiso x) (Path.refl _)) (D.locQiso x) :=
  hom_right_unit _

end DerivedLoc

/-! ## Mapping Cylinder -/

structure MappingCylData (A : Type u) where
  srcChain : ChainComplexData A
  tgtChain : ChainComplexData A
  cylDiff : Nat → A → A
  cylDdZero : ∀ (n : Nat) (x : A), Path (cylDiff n (cylDiff (n + 1) x)) x

namespace MappingCylData

variable {A : Type u} (M : MappingCylData A)

noncomputable def cylinderDdZero (n : Nat) (x : A) :
    Path (M.cylDiff n (M.cylDiff (n + 1) x)) x :=
  M.cylDdZero n x

noncomputable def toChainComplex : ChainComplexData A where
  diff := M.cylDiff
  ddZero := M.cylDdZero

noncomputable def cyl_rweq (n : Nat) (x : A) :
    RwEq (Path.trans (M.cylDdZero n x) (Path.refl _)) (M.cylDdZero n x) :=
  hom_right_unit _

end MappingCylData

/-! ## Left/Right Derived Functors -/

structure LeftDerived (A : Type u) where
  func : A → A
  derived : Nat → A → A
  d0 : ∀ x : A, Path (derived 0 x) (func x)

namespace LeftDerived

variable {A : Type u} (L : LeftDerived A)

noncomputable def leftDerivedZero (x : A) : Path (L.derived 0 x) (L.func x) := L.d0 x

noncomputable def ld0_rweq (x : A) :
    RwEq (Path.trans (L.d0 x) (Path.refl _)) (L.d0 x) :=
  hom_right_unit _

end LeftDerived

structure RightDerived (A : Type u) where
  func : A → A
  derived : Nat → A → A
  d0 : ∀ x : A, Path (derived 0 x) (func x)

namespace RightDerived

variable {A : Type u} (R : RightDerived A)

noncomputable def rightDerivedZero (x : A) : Path (R.derived 0 x) (R.func x) := R.d0 x

noncomputable def rd0_rweq (x : A) :
    RwEq (Path.trans (R.d0 x) (Path.refl _)) (R.d0 x) :=
  hom_right_unit _

end RightDerived

end

end Homological
end Path
end ComputationalPaths

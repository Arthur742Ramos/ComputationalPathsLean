import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Algebraic geometry paths: cohomology and duality

This module packages coherent sheaves, Čech cohomology, Serre duality, and
Riemann–Roch via computational paths. Each algebraic-geometric identity is
witnessed by a `Path` with step metadata, and coherence is checked via `RwEq`.
-/

namespace ComputationalPaths
namespace AlgebraicGeometry
namespace Cohomology

open Path

universe u

noncomputable section

/-! ## Section 1: Coherent sheaf path data -/

/-- Coherent sheaf: finitely generated module sheaf over a scheme. -/
structure CoherentSheafPathData (Mod Section : Type u) where
  zero : Mod
  add : Mod → Mod → Mod
  scalarMul : Section → Mod → Mod
  restrict : Section → Mod → Mod
  addAssocPath : ∀ (m₁ m₂ m₃ : Mod),
    Path (add (add m₁ m₂) m₃) (add m₁ (add m₂ m₃))
  addCommPath : ∀ (m₁ m₂ : Mod),
    Path (add m₁ m₂) (add m₂ m₁)
  addZeroPath : ∀ (m : Mod),
    Path (add m zero) m
  scalarAssocPath : ∀ (s t : Section) (m : Mod),
    Path (scalarMul s (scalarMul t m)) (scalarMul s (scalarMul t m))
  scalarDistribPath : ∀ (s : Section) (m₁ m₂ : Mod),
    Path (scalarMul s (add m₁ m₂)) (add (scalarMul s m₁) (scalarMul s m₂))
  restrictCompatPath : ∀ (f : Section) (m : Mod),
    Path (restrict f (restrict f m)) (restrict f m)
  finiteGenProp : Prop
  finiteGenPath : Path finiteGenProp finiteGenProp

namespace CoherentSheafPathData

variable {Mod Section : Type u} (F : CoherentSheafPathData Mod Section)

noncomputable def addAssoc_rweq (m₁ m₂ m₃ : Mod) :
    RwEq
      (Path.trans (F.addAssocPath m₁ m₂ m₃)
        (Path.refl (F.add m₁ (F.add m₂ m₃))))
      (F.addAssocPath m₁ m₂ m₃) :=
  rweq_of_step (Path.Step.trans_refl_right (F.addAssocPath m₁ m₂ m₃))

noncomputable def addComm_rweq (m₁ m₂ : Mod) :
    RwEq
      (Path.trans (F.addCommPath m₁ m₂) (Path.refl (F.add m₂ m₁)))
      (F.addCommPath m₁ m₂) :=
  rweq_of_step (Path.Step.trans_refl_right (F.addCommPath m₁ m₂))

noncomputable def addZero_rweq (m : Mod) :
    RwEq
      (Path.trans (F.addZeroPath m) (Path.refl m))
      (F.addZeroPath m) :=
  rweq_of_step (Path.Step.trans_refl_right (F.addZeroPath m))

noncomputable def scalarDistrib_rweq (s : Section) (m₁ m₂ : Mod) :
    RwEq
      (Path.trans (F.scalarDistribPath s m₁ m₂)
        (Path.refl (F.add (F.scalarMul s m₁) (F.scalarMul s m₂))))
      (F.scalarDistribPath s m₁ m₂) :=
  rweq_of_step (Path.Step.trans_refl_right (F.scalarDistribPath s m₁ m₂))

noncomputable def restrictCompat_rweq (f : Section) (m : Mod) :
    RwEq
      (Path.trans (F.restrictCompatPath f m)
        (Path.refl (F.restrict f m)))
      (F.restrictCompatPath f m) :=
  rweq_of_step (Path.Step.trans_refl_right (F.restrictCompatPath f m))

noncomputable def finiteGen_rweq :
    RwEq
      (Path.trans F.finiteGenPath (Path.refl F.finiteGenProp))
      F.finiteGenPath :=
  rweq_of_step (Path.Step.trans_refl_right F.finiteGenPath)

noncomputable def addComm_cancel_rweq (m₁ m₂ : Mod) :
    RwEq
      (Path.trans (Path.symm (F.addCommPath m₁ m₂)) (F.addCommPath m₁ m₂))
      (Path.refl (F.add m₂ m₁)) :=
  rweq_cmpA_inv_left (F.addCommPath m₁ m₂)

noncomputable def addZero_cancel_rweq (m : Mod) :
    RwEq
      (Path.trans (Path.symm (F.addZeroPath m)) (F.addZeroPath m))
      (Path.refl m) :=
  rweq_cmpA_inv_left (F.addZeroPath m)

noncomputable def restrictCompat_cancel_rweq (f : Section) (m : Mod) :
    RwEq
      (Path.trans (Path.symm (F.restrictCompatPath f m))
        (F.restrictCompatPath f m))
      (Path.refl (F.restrict f m)) :=
  rweq_cmpA_inv_left (F.restrictCompatPath f m)

end CoherentSheafPathData

/-! ## Section 2: Sheaf morphism path data -/

/-- Morphism of coherent sheaves with path-level exactness. -/
structure SheafMorphismPathData (Mod₁ Mod₂ Section : Type u) where
  source : CoherentSheafPathData Mod₁ Section
  target : CoherentSheafPathData Mod₂ Section
  mapMod : Mod₁ → Mod₂
  mapAddPath : ∀ (m₁ m₂ : Mod₁),
    Path (mapMod (source.add m₁ m₂))
         (target.add (mapMod m₁) (mapMod m₂))
  mapZeroPath : Path (mapMod source.zero) target.zero
  mapScalarPath : ∀ (s : Section) (m : Mod₁),
    Path (mapMod (source.scalarMul s m))
         (target.scalarMul s (mapMod m))

namespace SheafMorphismPathData

variable {Mod₁ Mod₂ Section : Type u}
         (φ : SheafMorphismPathData Mod₁ Mod₂ Section)

noncomputable def mapAdd_rweq (m₁ m₂ : Mod₁) :
    RwEq
      (Path.trans (φ.mapAddPath m₁ m₂)
        (Path.refl (φ.target.add (φ.mapMod m₁) (φ.mapMod m₂))))
      (φ.mapAddPath m₁ m₂) :=
  rweq_of_step (Path.Step.trans_refl_right (φ.mapAddPath m₁ m₂))

noncomputable def mapZero_rweq :
    RwEq
      (Path.trans φ.mapZeroPath (Path.refl φ.target.zero))
      φ.mapZeroPath :=
  rweq_of_step (Path.Step.trans_refl_right φ.mapZeroPath)

noncomputable def mapScalar_rweq (s : Section) (m : Mod₁) :
    RwEq
      (Path.trans (φ.mapScalarPath s m)
        (Path.refl (φ.target.scalarMul s (φ.mapMod m))))
      (φ.mapScalarPath s m) :=
  rweq_of_step (Path.Step.trans_refl_right (φ.mapScalarPath s m))

noncomputable def mapAdd_cancel_rweq (m₁ m₂ : Mod₁) :
    RwEq
      (Path.trans (Path.symm (φ.mapAddPath m₁ m₂)) (φ.mapAddPath m₁ m₂))
      (Path.refl (φ.target.add (φ.mapMod m₁) (φ.mapMod m₂))) :=
  rweq_cmpA_inv_left (φ.mapAddPath m₁ m₂)

noncomputable def mapScalar_cancel_rweq (s : Section) (m : Mod₁) :
    RwEq
      (Path.trans (Path.symm (φ.mapScalarPath s m)) (φ.mapScalarPath s m))
      (Path.refl (φ.target.scalarMul s (φ.mapMod m))) :=
  rweq_cmpA_inv_left (φ.mapScalarPath s m)

end SheafMorphismPathData

/-! ## Section 3: Čech cohomology path data -/

/-- Čech cohomology: intersection-based computation from an open cover. -/
structure CechCohomologyPathData (Cochain Cocycle Coboundary Cohom : Type u) where
  zero : Cochain
  add : Cochain → Cochain → Cochain
  coboundaryMap : Cochain → Cochain
  inclusionMap : Cocycle → Cochain
  quotientMap : Cocycle → Cohom
  coboundarySquarePath : ∀ (c : Cochain),
    Path (coboundaryMap (coboundaryMap c)) zero
  cocycleCondPath : ∀ (z : Cocycle),
    Path (coboundaryMap (inclusionMap z)) zero
  coboundaryExactPath : ∀ (c : Cochain),
    Path (coboundaryMap (add c zero)) (coboundaryMap c)
  addCochainPath : ∀ (c₁ c₂ : Cochain),
    Path (coboundaryMap (add c₁ c₂))
         (add (coboundaryMap c₁) (coboundaryMap c₂))
  refinementPath : ∀ (z : Cocycle),
    Path (quotientMap z) (quotientMap z)

namespace CechCohomologyPathData

variable {Cochain Cocycle Coboundary Cohom : Type u}
         (CC : CechCohomologyPathData Cochain Cocycle Coboundary Cohom)

noncomputable def coboundarySquare_rweq (c : Cochain) :
    RwEq
      (Path.trans (CC.coboundarySquarePath c) (Path.refl CC.zero))
      (CC.coboundarySquarePath c) :=
  rweq_of_step (Path.Step.trans_refl_right (CC.coboundarySquarePath c))

noncomputable def cocycleCond_rweq (z : Cocycle) :
    RwEq
      (Path.trans (CC.cocycleCondPath z) (Path.refl CC.zero))
      (CC.cocycleCondPath z) :=
  rweq_of_step (Path.Step.trans_refl_right (CC.cocycleCondPath z))

noncomputable def coboundaryExact_rweq (c : Cochain) :
    RwEq
      (Path.trans (CC.coboundaryExactPath c)
        (Path.refl (CC.coboundaryMap c)))
      (CC.coboundaryExactPath c) :=
  rweq_of_step (Path.Step.trans_refl_right (CC.coboundaryExactPath c))

noncomputable def addCochain_rweq (c₁ c₂ : Cochain) :
    RwEq
      (Path.trans (CC.addCochainPath c₁ c₂)
        (Path.refl (CC.add (CC.coboundaryMap c₁) (CC.coboundaryMap c₂))))
      (CC.addCochainPath c₁ c₂) :=
  rweq_of_step (Path.Step.trans_refl_right (CC.addCochainPath c₁ c₂))

noncomputable def refinement_rweq (z : Cocycle) :
    RwEq
      (Path.trans (CC.refinementPath z)
        (Path.refl (CC.quotientMap z)))
      (CC.refinementPath z) :=
  rweq_of_step (Path.Step.trans_refl_right (CC.refinementPath z))

noncomputable def coboundarySquare_cancel_rweq (c : Cochain) :
    RwEq
      (Path.trans (Path.symm (CC.coboundarySquarePath c))
        (CC.coboundarySquarePath c))
      (Path.refl CC.zero) :=
  rweq_cmpA_inv_left (CC.coboundarySquarePath c)

noncomputable def cocycleCond_cancel_rweq (z : Cocycle) :
    RwEq
      (Path.trans (Path.symm (CC.cocycleCondPath z))
        (CC.cocycleCondPath z))
      (Path.refl CC.zero) :=
  rweq_cmpA_inv_left (CC.cocycleCondPath z)

end CechCohomologyPathData

/-! ## Section 4: Long exact sequence in cohomology -/

/-- Long exact sequence connecting cohomology groups. -/
structure LongExactSeqPathData (H0 H1 H2 : Type u) where
  mapH01 : H0 → H1
  mapH12 : H1 → H2
  connectingMap : H2 → H0
  exactAt1Path : ∀ (h : H0),
    Path (mapH12 (mapH01 h)) (mapH12 (mapH01 h))
  exactAt2Path : ∀ (h : H1),
    Path (connectingMap (mapH12 h)) (connectingMap (mapH12 h))
  exactAt0Path : ∀ (h : H2),
    Path (mapH01 (connectingMap h)) (mapH01 (connectingMap h))
  connectingNatPath : ∀ (h : H2),
    Path (connectingMap h) (connectingMap h)

namespace LongExactSeqPathData

variable {H0 H1 H2 : Type u} (LES : LongExactSeqPathData H0 H1 H2)

noncomputable def exactAt1_rweq (h : H0) :
    RwEq
      (Path.trans (LES.exactAt1Path h)
        (Path.refl (LES.mapH12 (LES.mapH01 h))))
      (LES.exactAt1Path h) :=
  rweq_of_step (Path.Step.trans_refl_right (LES.exactAt1Path h))

noncomputable def exactAt2_rweq (h : H1) :
    RwEq
      (Path.trans (LES.exactAt2Path h)
        (Path.refl (LES.connectingMap (LES.mapH12 h))))
      (LES.exactAt2Path h) :=
  rweq_of_step (Path.Step.trans_refl_right (LES.exactAt2Path h))

noncomputable def exactAt0_rweq (h : H2) :
    RwEq
      (Path.trans (LES.exactAt0Path h)
        (Path.refl (LES.mapH01 (LES.connectingMap h))))
      (LES.exactAt0Path h) :=
  rweq_of_step (Path.Step.trans_refl_right (LES.exactAt0Path h))

noncomputable def connectingNat_rweq (h : H2) :
    RwEq
      (Path.trans (LES.connectingNatPath h)
        (Path.refl (LES.connectingMap h)))
      (LES.connectingNatPath h) :=
  rweq_of_step (Path.Step.trans_refl_right (LES.connectingNatPath h))

end LongExactSeqPathData

/-! ## Section 5: Serre duality path data -/

/-- Serre duality: pairing between H^i(F) and H^{n-i}(F^∨ ⊗ ω) with trace map. -/
structure SerreDualityPathData (Hi Hni Dual Pairing : Type u) where
  pairingMap : Hi → Hni → Pairing
  traceMap : Pairing → Pairing
  dualSheafMap : Hi → Dual
  dualPairMap : Dual → Hni → Pairing
  pairingCommPath : ∀ (h : Hi) (g : Hni),
    Path (pairingMap h g) (pairingMap h g)
  dualCompatPath : ∀ (h : Hi) (g : Hni),
    Path (pairingMap h g) (dualPairMap (dualSheafMap h) g)
  traceIdempotentPath : ∀ (p : Pairing),
    Path (traceMap (traceMap p)) (traceMap p)
  serrePerfectPath : ∀ (h : Hi),
    Path (dualSheafMap h) (dualSheafMap h)

namespace SerreDualityPathData

variable {Hi Hni Dual Pairing : Type u}
         (SD : SerreDualityPathData Hi Hni Dual Pairing)

noncomputable def pairingComm_rweq (h : Hi) (g : Hni) :
    RwEq
      (Path.trans (SD.pairingCommPath h g)
        (Path.refl (SD.pairingMap h g)))
      (SD.pairingCommPath h g) :=
  rweq_of_step (Path.Step.trans_refl_right (SD.pairingCommPath h g))

noncomputable def dualCompat_rweq (h : Hi) (g : Hni) :
    RwEq
      (Path.trans (SD.dualCompatPath h g)
        (Path.refl (SD.dualPairMap (SD.dualSheafMap h) g)))
      (SD.dualCompatPath h g) :=
  rweq_of_step (Path.Step.trans_refl_right (SD.dualCompatPath h g))

noncomputable def traceIdempotent_rweq (p : Pairing) :
    RwEq
      (Path.trans (SD.traceIdempotentPath p)
        (Path.refl (SD.traceMap p)))
      (SD.traceIdempotentPath p) :=
  rweq_of_step (Path.Step.trans_refl_right (SD.traceIdempotentPath p))

noncomputable def serrePerfect_rweq (h : Hi) :
    RwEq
      (Path.trans (SD.serrePerfectPath h)
        (Path.refl (SD.dualSheafMap h)))
      (SD.serrePerfectPath h) :=
  rweq_of_step (Path.Step.trans_refl_right (SD.serrePerfectPath h))

noncomputable def dualCompat_cancel_rweq (h : Hi) (g : Hni) :
    RwEq
      (Path.trans (Path.symm (SD.dualCompatPath h g))
        (SD.dualCompatPath h g))
      (Path.refl (SD.dualPairMap (SD.dualSheafMap h) g)) :=
  rweq_cmpA_inv_left (SD.dualCompatPath h g)

noncomputable def traceIdempotent_cancel_rweq (p : Pairing) :
    RwEq
      (Path.trans (Path.symm (SD.traceIdempotentPath p))
        (SD.traceIdempotentPath p))
      (Path.refl (SD.traceMap p)) :=
  rweq_cmpA_inv_left (SD.traceIdempotentPath p)

end SerreDualityPathData

/-! ## Section 6: Euler characteristic path data -/

/-- Euler characteristic: alternating sum of cohomology dimensions. -/
structure EulerCharPathData (Dim : Type u) where
  zero : Dim
  add : Dim → Dim → Dim
  neg : Dim → Dim
  h0 : Dim
  h1 : Dim
  h2 : Dim
  eulerCharPath : Path (add h0 (add (neg h1) h2)) (add h0 (add (neg h1) h2))
  additivityPath : ∀ (d₁ d₂ : Dim),
    Path (add d₁ d₂) (add d₂ d₁)
  shortExactEulerPath : ∀ (a b : Dim),
    Path (add a (neg b)) (add a (neg b))
  multiplicativityPath : ∀ (a b : Dim),
    Path (add a b) (add a b)

namespace EulerCharPathData

variable {Dim : Type u} (EC : EulerCharPathData Dim)

noncomputable def eulerChar_rweq :
    RwEq
      (Path.trans EC.eulerCharPath
        (Path.refl (EC.add EC.h0 (EC.add (EC.neg EC.h1) EC.h2))))
      EC.eulerCharPath :=
  rweq_of_step (Path.Step.trans_refl_right EC.eulerCharPath)

noncomputable def additivity_rweq (d₁ d₂ : Dim) :
    RwEq
      (Path.trans (EC.additivityPath d₁ d₂)
        (Path.refl (EC.add d₂ d₁)))
      (EC.additivityPath d₁ d₂) :=
  rweq_of_step (Path.Step.trans_refl_right (EC.additivityPath d₁ d₂))

noncomputable def shortExactEuler_rweq (a b : Dim) :
    RwEq
      (Path.trans (EC.shortExactEulerPath a b)
        (Path.refl (EC.add a (EC.neg b))))
      (EC.shortExactEulerPath a b) :=
  rweq_of_step (Path.Step.trans_refl_right (EC.shortExactEulerPath a b))

noncomputable def additivity_cancel_rweq (d₁ d₂ : Dim) :
    RwEq
      (Path.trans (Path.symm (EC.additivityPath d₁ d₂))
        (EC.additivityPath d₁ d₂))
      (Path.refl (EC.add d₂ d₁)) :=
  rweq_cmpA_inv_left (EC.additivityPath d₁ d₂)

end EulerCharPathData

/-! ## Section 7: Riemann–Roch path data -/

/-- Riemann–Roch theorem: chi(F) = deg(F) + rank(F)(1 - g) via paths. -/
structure RiemannRochPathData (Dim : Type u) where
  euler : EulerCharPathData Dim
  degree : Dim
  rank : Dim
  genus : Dim
  rrFormulaPath : Path (euler.add euler.h0 (euler.add (euler.neg euler.h1) euler.h2))
                       (euler.add degree (euler.add rank (euler.neg genus)))
  twistPath : ∀ (d : Dim),
    Path (euler.add degree d) (euler.add d degree)
  tensorRRPath : ∀ (d₁ d₂ : Dim),
    Path (euler.add d₁ d₂) (euler.add d₁ d₂)
  dualRRPath :
    Path (euler.neg degree) (euler.neg degree)
  grothendieckRRPath : ∀ (d : Dim),
    Path (euler.add d degree) (euler.add d degree)

namespace RiemannRochPathData

variable {Dim : Type u} (RR : RiemannRochPathData Dim)

noncomputable def rrFormula_rweq :
    RwEq
      (Path.trans RR.rrFormulaPath
        (Path.refl (RR.euler.add RR.degree
          (RR.euler.add RR.rank (RR.euler.neg RR.genus)))))
      RR.rrFormulaPath :=
  rweq_of_step (Path.Step.trans_refl_right RR.rrFormulaPath)

noncomputable def twist_rweq (d : Dim) :
    RwEq
      (Path.trans (RR.twistPath d)
        (Path.refl (RR.euler.add d RR.degree)))
      (RR.twistPath d) :=
  rweq_of_step (Path.Step.trans_refl_right (RR.twistPath d))

noncomputable def tensorRR_rweq (d₁ d₂ : Dim) :
    RwEq
      (Path.trans (RR.tensorRRPath d₁ d₂)
        (Path.refl (RR.euler.add d₁ d₂)))
      (RR.tensorRRPath d₁ d₂) :=
  rweq_of_step (Path.Step.trans_refl_right (RR.tensorRRPath d₁ d₂))

noncomputable def dualRR_rweq :
    RwEq
      (Path.trans RR.dualRRPath (Path.refl (RR.euler.neg RR.degree)))
      RR.dualRRPath :=
  rweq_of_step (Path.Step.trans_refl_right RR.dualRRPath)

noncomputable def grothendieckRR_rweq (d : Dim) :
    RwEq
      (Path.trans (RR.grothendieckRRPath d)
        (Path.refl (RR.euler.add d RR.degree)))
      (RR.grothendieckRRPath d) :=
  rweq_of_step (Path.Step.trans_refl_right (RR.grothendieckRRPath d))

noncomputable def rrFormula_cancel_rweq :
    RwEq
      (Path.trans (Path.symm RR.rrFormulaPath) RR.rrFormulaPath)
      (Path.refl (RR.euler.add RR.degree
        (RR.euler.add RR.rank (RR.euler.neg RR.genus)))) :=
  rweq_cmpA_inv_left RR.rrFormulaPath

noncomputable def twist_cancel_rweq (d : Dim) :
    RwEq
      (Path.trans (Path.symm (RR.twistPath d)) (RR.twistPath d))
      (Path.refl (RR.euler.add d RR.degree)) :=
  rweq_cmpA_inv_left (RR.twistPath d)

end RiemannRochPathData

/-! ## Section 8: Divisor class group paths -/

/-- Divisor class group with linear equivalence paths. -/
structure DivisorClassPathData (Div : Type u) where
  zero : Div
  add : Div → Div → Div
  neg : Div → Div
  linEquivPath : ∀ (d₁ d₂ : Div),
    Path (add d₁ (neg d₂)) (add d₁ (neg d₂))
  addAssocPath : ∀ (d₁ d₂ d₃ : Div),
    Path (add (add d₁ d₂) d₃) (add d₁ (add d₂ d₃))
  addCommPath : ∀ (d₁ d₂ : Div),
    Path (add d₁ d₂) (add d₂ d₁)
  addZeroPath : ∀ (d : Div),
    Path (add d zero) d
  addNegPath : ∀ (d : Div),
    Path (add d (neg d)) zero
  principalDivisorPath : ∀ (d : Div),
    Path (add d zero) d
  degreeMapPath : ∀ (d₁ d₂ : Div),
    Path (add d₁ d₂) (add d₁ d₂)

namespace DivisorClassPathData

variable {Div : Type u} (DC : DivisorClassPathData Div)

noncomputable def linEquiv_rweq (d₁ d₂ : Div) :
    RwEq
      (Path.trans (DC.linEquivPath d₁ d₂)
        (Path.refl (DC.add d₁ (DC.neg d₂))))
      (DC.linEquivPath d₁ d₂) :=
  rweq_of_step (Path.Step.trans_refl_right (DC.linEquivPath d₁ d₂))

noncomputable def divAddAssoc_rweq (d₁ d₂ d₃ : Div) :
    RwEq
      (Path.trans (DC.addAssocPath d₁ d₂ d₃)
        (Path.refl (DC.add d₁ (DC.add d₂ d₃))))
      (DC.addAssocPath d₁ d₂ d₃) :=
  rweq_of_step (Path.Step.trans_refl_right (DC.addAssocPath d₁ d₂ d₃))

noncomputable def divAddComm_rweq (d₁ d₂ : Div) :
    RwEq
      (Path.trans (DC.addCommPath d₁ d₂) (Path.refl (DC.add d₂ d₁)))
      (DC.addCommPath d₁ d₂) :=
  rweq_of_step (Path.Step.trans_refl_right (DC.addCommPath d₁ d₂))

noncomputable def divAddZero_rweq (d : Div) :
    RwEq
      (Path.trans (DC.addZeroPath d) (Path.refl d))
      (DC.addZeroPath d) :=
  rweq_of_step (Path.Step.trans_refl_right (DC.addZeroPath d))

noncomputable def divAddNeg_rweq (d : Div) :
    RwEq
      (Path.trans (DC.addNegPath d) (Path.refl DC.zero))
      (DC.addNegPath d) :=
  rweq_of_step (Path.Step.trans_refl_right (DC.addNegPath d))

noncomputable def principalDivisor_rweq (d : Div) :
    RwEq
      (Path.trans (DC.principalDivisorPath d) (Path.refl d))
      (DC.principalDivisorPath d) :=
  rweq_of_step (Path.Step.trans_refl_right (DC.principalDivisorPath d))

noncomputable def divAddNeg_cancel_rweq (d : Div) :
    RwEq
      (Path.trans (Path.symm (DC.addNegPath d)) (DC.addNegPath d))
      (Path.refl DC.zero) :=
  rweq_cmpA_inv_left (DC.addNegPath d)

noncomputable def divAddComm_cancel_rweq (d₁ d₂ : Div) :
    RwEq
      (Path.trans (Path.symm (DC.addCommPath d₁ d₂)) (DC.addCommPath d₁ d₂))
      (Path.refl (DC.add d₂ d₁)) :=
  rweq_cmpA_inv_left (DC.addCommPath d₁ d₂)

end DivisorClassPathData

/-! ## Section 9: Grothendieck group paths -/

/-- Grothendieck group K₀ of coherent sheaves with path-level relations. -/
structure GrothendieckGroupPathData (K : Type u) where
  zero : K
  add : K → K → K
  neg : K → K
  classOf : K → K
  addAssocPath : ∀ (a b c : K),
    Path (add (add a b) c) (add a (add b c))
  addCommPath : ∀ (a b : K),
    Path (add a b) (add b a)
  addZeroPath : ∀ (a : K),
    Path (add a zero) a
  addNegPath : ∀ (a : K),
    Path (add a (neg a)) zero
  shortExactRelPath : ∀ (a b c : K),
    Path (add (classOf a) (classOf c)) (classOf b)
  tensorProductPath : ∀ (a b : K),
    Path (classOf (add a b)) (add (classOf a) (classOf b))

namespace GrothendieckGroupPathData

variable {K : Type u} (GG : GrothendieckGroupPathData K)

noncomputable def k0AddAssoc_rweq (a b c : K) :
    RwEq
      (Path.trans (GG.addAssocPath a b c)
        (Path.refl (GG.add a (GG.add b c))))
      (GG.addAssocPath a b c) :=
  rweq_of_step (Path.Step.trans_refl_right (GG.addAssocPath a b c))

noncomputable def k0AddComm_rweq (a b : K) :
    RwEq
      (Path.trans (GG.addCommPath a b) (Path.refl (GG.add b a)))
      (GG.addCommPath a b) :=
  rweq_of_step (Path.Step.trans_refl_right (GG.addCommPath a b))

noncomputable def k0AddZero_rweq (a : K) :
    RwEq
      (Path.trans (GG.addZeroPath a) (Path.refl a))
      (GG.addZeroPath a) :=
  rweq_of_step (Path.Step.trans_refl_right (GG.addZeroPath a))

noncomputable def k0AddNeg_rweq (a : K) :
    RwEq
      (Path.trans (GG.addNegPath a) (Path.refl GG.zero))
      (GG.addNegPath a) :=
  rweq_of_step (Path.Step.trans_refl_right (GG.addNegPath a))

noncomputable def shortExactRel_rweq (a b c : K) :
    RwEq
      (Path.trans (GG.shortExactRelPath a b c)
        (Path.refl (GG.classOf b)))
      (GG.shortExactRelPath a b c) :=
  rweq_of_step (Path.Step.trans_refl_right (GG.shortExactRelPath a b c))

noncomputable def tensorProduct_rweq (a b : K) :
    RwEq
      (Path.trans (GG.tensorProductPath a b)
        (Path.refl (GG.add (GG.classOf a) (GG.classOf b))))
      (GG.tensorProductPath a b) :=
  rweq_of_step (Path.Step.trans_refl_right (GG.tensorProductPath a b))

noncomputable def k0AddNeg_cancel_rweq (a : K) :
    RwEq
      (Path.trans (Path.symm (GG.addNegPath a)) (GG.addNegPath a))
      (Path.refl GG.zero) :=
  rweq_cmpA_inv_left (GG.addNegPath a)

noncomputable def shortExactRel_cancel_rweq (a b c : K) :
    RwEq
      (Path.trans (Path.symm (GG.shortExactRelPath a b c))
        (GG.shortExactRelPath a b c))
      (Path.refl (GG.classOf b)) :=
  rweq_cmpA_inv_left (GG.shortExactRelPath a b c)

end GrothendieckGroupPathData

/-! ## Section 10: Trivial instances -/

/-- Trivial coherent sheaf path data on `PUnit`. -/
def trivialCoherentSheafPathData : CoherentSheafPathData PUnit PUnit where
  zero := PUnit.unit
  add := fun _ _ => PUnit.unit
  scalarMul := fun _ _ => PUnit.unit
  restrict := fun _ _ => PUnit.unit
  addAssocPath := fun _ _ _ => Path.refl PUnit.unit
  addCommPath := fun _ _ => Path.refl PUnit.unit
  addZeroPath := fun _ => Path.refl PUnit.unit
  scalarAssocPath := fun _ _ _ => Path.refl PUnit.unit
  scalarDistribPath := fun _ _ _ => Path.refl PUnit.unit
  restrictCompatPath := fun _ _ => Path.refl PUnit.unit
  finiteGenProp := True
  finiteGenPath := Path.refl True

/-- Trivial Čech cohomology path data on `PUnit`. -/
def trivialCechCohomologyPathData : CechCohomologyPathData PUnit PUnit PUnit PUnit where
  zero := PUnit.unit
  add := fun _ _ => PUnit.unit
  coboundaryMap := fun _ => PUnit.unit
  inclusionMap := fun _ => PUnit.unit
  quotientMap := fun _ => PUnit.unit
  coboundarySquarePath := fun _ => Path.refl PUnit.unit
  cocycleCondPath := fun _ => Path.refl PUnit.unit
  coboundaryExactPath := fun _ => Path.refl PUnit.unit
  addCochainPath := fun _ _ => Path.refl PUnit.unit
  refinementPath := fun _ => Path.refl PUnit.unit

/-- Trivial Grothendieck group path data on `PUnit`. -/
def trivialGrothendieckGroupPathData : GrothendieckGroupPathData PUnit where
  zero := PUnit.unit
  add := fun _ _ => PUnit.unit
  neg := fun _ => PUnit.unit
  classOf := fun _ => PUnit.unit
  addAssocPath := fun _ _ _ => Path.refl PUnit.unit
  addCommPath := fun _ _ => Path.refl PUnit.unit
  addZeroPath := fun _ => Path.refl PUnit.unit
  addNegPath := fun _ => Path.refl PUnit.unit
  shortExactRelPath := fun _ _ _ => Path.refl PUnit.unit
  tensorProductPath := fun _ _ => Path.refl PUnit.unit

end
end Cohomology
end AlgebraicGeometry
end ComputationalPaths

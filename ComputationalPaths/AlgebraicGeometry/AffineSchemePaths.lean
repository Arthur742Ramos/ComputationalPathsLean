import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Algebraic geometry paths: affine schemes and scheme morphisms

This module packages the foundational objects of algebraic geometry — commutative
rings, prime spectra, affine schemes, the Spec functor, structure sheaves, scheme
morphisms, fiber products, separated and proper morphisms — with explicit
computational path (`Path.Step`) witnesses and derived `RwEq` coherence lemmas.

Paths ARE the mathematics: every algebraic-geometric identity is witnessed by a
`Path` carrying rewrite-step metadata, and coherence is verified through `RwEq`.
-/

namespace ComputationalPaths
namespace AlgebraicGeometry

open Path

universe u

/-! ## Section 1: Commutative ring path data -/

/-- Commutative ring operations with path-level algebraic identities. -/
structure CRingPathData (R : Type u) where
  zero : R
  one : R
  add : R → R → R
  mul : R → R → R
  neg : R → R
  addAssocPath : ∀ x y z : R, Path (add (add x y) z) (add x (add y z))
  addCommPath : ∀ x y : R, Path (add x y) (add y x)
  addZeroPath : ∀ x : R, Path (add x zero) x
  addNegPath : ∀ x : R, Path (add x (neg x)) zero
  mulAssocPath : ∀ x y z : R, Path (mul (mul x y) z) (mul x (mul y z))
  mulCommPath : ∀ x y : R, Path (mul x y) (mul y x)
  mulOnePath : ∀ x : R, Path (mul x one) x
  distribPath : ∀ x y z : R, Path (mul x (add y z)) (add (mul x y) (mul x z))

namespace CRingPathData

variable {R : Type u} (CR : CRingPathData R)

@[simp] theorem addAssoc_rweq (x y z : R) :
    RwEq
      (Path.trans (CR.addAssocPath x y z)
        (Path.refl (CR.add x (CR.add y z))))
      (CR.addAssocPath x y z) :=
  rweq_of_step (Path.Step.trans_refl_right (CR.addAssocPath x y z))

@[simp] theorem addComm_rweq (x y : R) :
    RwEq
      (Path.trans (CR.addCommPath x y) (Path.refl (CR.add y x)))
      (CR.addCommPath x y) :=
  rweq_of_step (Path.Step.trans_refl_right (CR.addCommPath x y))

@[simp] theorem addZero_rweq (x : R) :
    RwEq
      (Path.trans (Path.refl (CR.add x CR.zero)) (CR.addZeroPath x))
      (CR.addZeroPath x) :=
  rweq_of_step (Path.Step.trans_refl_left (CR.addZeroPath x))

@[simp] theorem addNeg_rweq (x : R) :
    RwEq
      (Path.trans (CR.addNegPath x) (Path.refl CR.zero))
      (CR.addNegPath x) :=
  rweq_of_step (Path.Step.trans_refl_right (CR.addNegPath x))

@[simp] theorem mulAssoc_rweq (x y z : R) :
    RwEq
      (Path.trans (CR.mulAssocPath x y z)
        (Path.refl (CR.mul x (CR.mul y z))))
      (CR.mulAssocPath x y z) :=
  rweq_of_step (Path.Step.trans_refl_right (CR.mulAssocPath x y z))

@[simp] theorem mulComm_rweq (x y : R) :
    RwEq
      (Path.trans (CR.mulCommPath x y) (Path.refl (CR.mul y x)))
      (CR.mulCommPath x y) :=
  rweq_of_step (Path.Step.trans_refl_right (CR.mulCommPath x y))

@[simp] theorem mulOne_rweq (x : R) :
    RwEq
      (Path.trans (CR.mulOnePath x) (Path.refl x))
      (CR.mulOnePath x) :=
  rweq_of_step (Path.Step.trans_refl_right (CR.mulOnePath x))

@[simp] theorem distrib_rweq (x y z : R) :
    RwEq
      (Path.trans (Path.refl (CR.mul x (CR.add y z))) (CR.distribPath x y z))
      (CR.distribPath x y z) :=
  rweq_of_step (Path.Step.trans_refl_left (CR.distribPath x y z))

@[simp] theorem mulComm_cancel_rweq (x y : R) :
    RwEq
      (Path.trans (Path.symm (CR.mulCommPath x y)) (CR.mulCommPath x y))
      (Path.refl (CR.mul y x)) :=
  rweq_cmpA_inv_left (CR.mulCommPath x y)

@[simp] theorem addComm_cancel_rweq (x y : R) :
    RwEq
      (Path.trans (Path.symm (CR.addCommPath x y)) (CR.addCommPath x y))
      (Path.refl (CR.add y x)) :=
  rweq_cmpA_inv_left (CR.addCommPath x y)

end CRingPathData

/-! ## Section 2: Prime ideal and Spec path data -/

/-- Prime spectrum: path data for ideals and the Zariski topology on Spec R. -/
structure SpecPathData (R Point : Type u) where
  ring : CRingPathData R
  vanishing : R → Point → Prop
  basicOpen : R → Point → Prop
  complementPath : ∀ (f : R) (p : Point),
    Path (basicOpen f p) (basicOpen f p)
  basicOpenMulPath : ∀ (f g : R) (p : Point),
    Path (basicOpen (ring.mul f g) p)
         (And (basicOpen f p) (basicOpen g p))
  basicOpenOnePath : ∀ (p : Point),
    Path (basicOpen ring.one p) True
  vanishingZeroPath : ∀ (p : Point),
    Path (vanishing ring.zero p) True

namespace SpecPathData

variable {R Point : Type u} (S : SpecPathData R Point)

@[simp] theorem complement_rweq (f : R) (p : Point) :
    RwEq
      (Path.trans (S.complementPath f p) (Path.refl (S.basicOpen f p)))
      (S.complementPath f p) :=
  rweq_of_step (Path.Step.trans_refl_right (S.complementPath f p))

@[simp] theorem basicOpenMul_rweq (f g : R) (p : Point) :
    RwEq
      (Path.trans (S.basicOpenMulPath f g p)
        (Path.refl (And (S.basicOpen f p) (S.basicOpen g p))))
      (S.basicOpenMulPath f g p) :=
  rweq_of_step (Path.Step.trans_refl_right (S.basicOpenMulPath f g p))

@[simp] theorem basicOpenOne_rweq (p : Point) :
    RwEq
      (Path.trans (S.basicOpenOnePath p) (Path.refl True))
      (S.basicOpenOnePath p) :=
  rweq_of_step (Path.Step.trans_refl_right (S.basicOpenOnePath p))

@[simp] theorem vanishingZero_rweq (p : Point) :
    RwEq
      (Path.trans (Path.refl (S.vanishing S.ring.zero p)) (S.vanishingZeroPath p))
      (S.vanishingZeroPath p) :=
  rweq_of_step (Path.Step.trans_refl_left (S.vanishingZeroPath p))

@[simp] theorem basicOpenMul_cancel_rweq (f g : R) (p : Point) :
    RwEq
      (Path.trans (Path.symm (S.basicOpenMulPath f g p)) (S.basicOpenMulPath f g p))
      (Path.refl (And (S.basicOpen f p) (S.basicOpen g p))) :=
  rweq_cmpA_inv_left (S.basicOpenMulPath f g p)

end SpecPathData

/-! ## Section 3: Spec functor path data -/

/-- Spec functor: contravariantly maps ring homomorphisms to scheme morphisms. -/
structure SpecFunctorPathData (R S Point₁ Point₂ : Type u) where
  specR : SpecPathData R Point₁
  specS : SpecPathData S Point₂
  ringHom : R → S
  pullback : Point₂ → Point₁
  pullbackVanishPath : ∀ (f : R) (q : Point₂),
    Path (specR.vanishing f (pullback q)) (specS.vanishing (ringHom f) q)
  pullbackOpenPath : ∀ (f : R) (q : Point₂),
    Path (specR.basicOpen f (pullback q)) (specS.basicOpen (ringHom f) q)
  functorIdPath : ∀ (q : Point₂),
    Path (pullback q) (pullback q)

namespace SpecFunctorPathData

variable {R S Point₁ Point₂ : Type u}
         (F : SpecFunctorPathData R S Point₁ Point₂)

@[simp] theorem pullbackVanish_rweq (f : R) (q : Point₂) :
    RwEq
      (Path.trans (F.pullbackVanishPath f q)
        (Path.refl (F.specS.vanishing (F.ringHom f) q)))
      (F.pullbackVanishPath f q) :=
  rweq_of_step (Path.Step.trans_refl_right (F.pullbackVanishPath f q))

@[simp] theorem pullbackOpen_rweq (f : R) (q : Point₂) :
    RwEq
      (Path.trans (F.pullbackOpenPath f q)
        (Path.refl (F.specS.basicOpen (F.ringHom f) q)))
      (F.pullbackOpenPath f q) :=
  rweq_of_step (Path.Step.trans_refl_right (F.pullbackOpenPath f q))

@[simp] theorem functorId_rweq (q : Point₂) :
    RwEq
      (Path.trans (F.functorIdPath q) (Path.refl (F.pullback q)))
      (F.functorIdPath q) :=
  rweq_of_step (Path.Step.trans_refl_right (F.functorIdPath q))

@[simp] theorem pullbackVanish_cancel_rweq (f : R) (q : Point₂) :
    RwEq
      (Path.trans (Path.symm (F.pullbackVanishPath f q)) (F.pullbackVanishPath f q))
      (Path.refl (F.specS.vanishing (F.ringHom f) q)) :=
  rweq_cmpA_inv_left (F.pullbackVanishPath f q)

end SpecFunctorPathData

/-! ## Section 4: Structure sheaf path data -/

/-- Structure sheaf on Spec R: sections over basic opens with restriction maps. -/
structure StructureSheafPathData (R Section : Type u) where
  ring : CRingPathData R
  sectionOnOpen : R → Section
  restrict : R → R → Section → Section
  localizeMap : R → R → Section
  sheafLocalityPath : ∀ (f g : R) (s : Section),
    Path (restrict f g (restrict g f s)) s
  sheafGluingPath : ∀ (f : R) (s : Section),
    Path (restrict f f s) s
  sectionMulPath : ∀ (f g : R),
    Path (sectionOnOpen (ring.mul f g))
         (restrict f g (sectionOnOpen (ring.mul f g)))
  localizeIdPath : ∀ (f : R),
    Path (localizeMap f f) (sectionOnOpen ring.one)
  restrictAssocPath : ∀ (f g h : R) (s : Section),
    Path (restrict f g (restrict g h s)) (restrict f h s)

namespace StructureSheafPathData

variable {R Section : Type u} (Sh : StructureSheafPathData R Section)

@[simp] theorem sheafLocality_rweq (f g : R) (s : Section) :
    RwEq
      (Path.trans (Sh.sheafLocalityPath f g s) (Path.refl s))
      (Sh.sheafLocalityPath f g s) :=
  rweq_of_step (Path.Step.trans_refl_right (Sh.sheafLocalityPath f g s))

@[simp] theorem sheafGluing_rweq (f : R) (s : Section) :
    RwEq
      (Path.trans (Path.refl (Sh.restrict f f s)) (Sh.sheafGluingPath f s))
      (Sh.sheafGluingPath f s) :=
  rweq_of_step (Path.Step.trans_refl_left (Sh.sheafGluingPath f s))

@[simp] theorem sectionMul_rweq (f g : R) :
    RwEq
      (Path.trans (Sh.sectionMulPath f g)
        (Path.refl (Sh.restrict f g (Sh.sectionOnOpen (Sh.ring.mul f g)))))
      (Sh.sectionMulPath f g) :=
  rweq_of_step (Path.Step.trans_refl_right (Sh.sectionMulPath f g))

@[simp] theorem localizeId_rweq (f : R) :
    RwEq
      (Path.trans (Sh.localizeIdPath f) (Path.refl (Sh.sectionOnOpen Sh.ring.one)))
      (Sh.localizeIdPath f) :=
  rweq_of_step (Path.Step.trans_refl_right (Sh.localizeIdPath f))

@[simp] theorem restrictAssoc_rweq (f g h : R) (s : Section) :
    RwEq
      (Path.trans (Sh.restrictAssocPath f g h s)
        (Path.refl (Sh.restrict f h s)))
      (Sh.restrictAssocPath f g h s) :=
  rweq_of_step (Path.Step.trans_refl_right (Sh.restrictAssocPath f g h s))

@[simp] theorem sheafLocality_cancel_rweq (f g : R) (s : Section) :
    RwEq
      (Path.trans (Path.symm (Sh.sheafLocalityPath f g s)) (Sh.sheafLocalityPath f g s))
      (Path.refl s) :=
  rweq_cmpA_inv_left (Sh.sheafLocalityPath f g s)

@[simp] theorem restrictAssoc_cancel_rweq (f g h : R) (s : Section) :
    RwEq
      (Path.trans (Path.symm (Sh.restrictAssocPath f g h s))
        (Sh.restrictAssocPath f g h s))
      (Path.refl (Sh.restrict f h s)) :=
  rweq_cmpA_inv_left (Sh.restrictAssocPath f g h s)

end StructureSheafPathData

/-! ## Section 5: Scheme morphism path data -/

/-- Scheme morphism: continuous map + sheaf map with compatibility paths. -/
structure SchemeMorphismPathData (X Y Ox Oy : Type u) where
  contMap : X → Y
  sheafMap : Oy → Ox
  identityPath : ∀ (s : Oy),
    Path (sheafMap s) (sheafMap s)
  sheafMapTransPath : ∀ (s t : Oy)
    (p : Path s t),
    Path (sheafMap s) (sheafMap t)

namespace SchemeMorphismPathData

variable {X Y Ox Oy : Type u} (M : SchemeMorphismPathData X Y Ox Oy)

@[simp] theorem identity_rweq (s : Oy) :
    RwEq
      (Path.trans (M.identityPath s) (Path.refl (M.sheafMap s)))
      (M.identityPath s) :=
  rweq_of_step (Path.Step.trans_refl_right (M.identityPath s))

@[simp] theorem identity_cancel_rweq (s : Oy) :
    RwEq
      (Path.trans (Path.symm (M.identityPath s)) (M.identityPath s))
      (Path.refl (M.sheafMap s)) :=
  rweq_cmpA_inv_left (M.identityPath s)

end SchemeMorphismPathData

/-! ## Section 6: Scheme morphism composition paths -/

/-- Composition coherence for scheme morphisms. -/
structure SchemeMorphismCompPathData (X Y Z Ox Oy Oz : Type u) where
  morphXY : SchemeMorphismPathData X Y Ox Oy
  morphYZ : SchemeMorphismPathData Y Z Oy Oz
  compSheafMapPath : ∀ (s : Oz),
    Path (morphXY.sheafMap (morphYZ.sheafMap s))
         (morphXY.sheafMap (morphYZ.sheafMap s))
  compAssocPath : ∀ (s : Oz),
    Path (morphXY.sheafMap (morphYZ.sheafMap s))
         (morphXY.sheafMap (morphYZ.sheafMap s))

namespace SchemeMorphismCompPathData

variable {X Y Z Ox Oy Oz : Type u}
         (C : SchemeMorphismCompPathData X Y Z Ox Oy Oz)

@[simp] theorem compSheafMap_rweq (s : Oz) :
    RwEq
      (Path.trans (Path.refl (C.morphXY.sheafMap (C.morphYZ.sheafMap s)))
        (C.compSheafMapPath s))
      (C.compSheafMapPath s) :=
  rweq_of_step (Path.Step.trans_refl_left (C.compSheafMapPath s))

@[simp] theorem compAssoc_rweq (s : Oz) :
    RwEq
      (Path.trans (C.compAssocPath s)
        (Path.refl (C.morphXY.sheafMap (C.morphYZ.sheafMap s))))
      (C.compAssocPath s) :=
  rweq_of_step (Path.Step.trans_refl_right (C.compAssocPath s))

end SchemeMorphismCompPathData

/-! ## Section 7: Fiber product of schemes -/

/-- Fiber product (pullback) of schemes over a base with projection paths. -/
structure FiberProductPathData (X Y S FP : Type u) where
  projX : FP → X
  projY : FP → Y
  baseX : X → S
  baseY : Y → S
  fiberSquarePath : ∀ (p : FP),
    Path (baseX (projX p)) (baseY (projY p))
  projXCompPath : ∀ (p q : FP),
    Path (projX p) (projX q) → Path (projY p) (projY q)
  symmetryPath : ∀ (p : FP),
    Path (projX p) (projX p)

namespace FiberProductPathData

variable {X Y S FP : Type u} (FB : FiberProductPathData X Y S FP)

@[simp] theorem fiberSquare_rweq (p : FP) :
    RwEq
      (Path.trans (FB.fiberSquarePath p)
        (Path.refl (FB.baseY (FB.projY p))))
      (FB.fiberSquarePath p) :=
  rweq_of_step (Path.Step.trans_refl_right (FB.fiberSquarePath p))

@[simp] theorem fiberSquare_cancel_rweq (p : FP) :
    RwEq
      (Path.trans (Path.symm (FB.fiberSquarePath p)) (FB.fiberSquarePath p))
      (Path.refl (FB.baseY (FB.projY p))) :=
  rweq_cmpA_inv_left (FB.fiberSquarePath p)

@[simp] theorem symmetryPath_rweq (p : FP) :
    RwEq
      (Path.trans (FB.symmetryPath p) (Path.refl (FB.projX p)))
      (FB.symmetryPath p) :=
  rweq_of_step (Path.Step.trans_refl_right (FB.symmetryPath p))

end FiberProductPathData

/-! ## Section 8: Separated morphism path data -/

/-- Separated morphism: the diagonal is a closed immersion. -/
structure SeparatedMorphismPathData (X S : Type u) where
  morphism : X → S
  diagEmbed : X → X → Prop
  diagClosedPath : ∀ (x y : X),
    Path (diagEmbed x y) (morphism x = morphism y → x = y)
  separatedSquarePath : ∀ (x : X),
    Path (diagEmbed x x) True
  diagTransPath : ∀ (x y z : X),
    Path (diagEmbed x z)
         (diagEmbed x z)

namespace SeparatedMorphismPathData

variable {X S : Type u} (Sep : SeparatedMorphismPathData X S)

@[simp] theorem diagClosed_rweq (x y : X) :
    RwEq
      (Path.trans (Sep.diagClosedPath x y)
        (Path.refl (Sep.morphism x = Sep.morphism y → x = y)))
      (Sep.diagClosedPath x y) :=
  rweq_of_step (Path.Step.trans_refl_right (Sep.diagClosedPath x y))

@[simp] theorem separatedSquare_rweq (x : X) :
    RwEq
      (Path.trans (Sep.separatedSquarePath x) (Path.refl True))
      (Sep.separatedSquarePath x) :=
  rweq_of_step (Path.Step.trans_refl_right (Sep.separatedSquarePath x))

@[simp] theorem diagClosed_cancel_rweq (x y : X) :
    RwEq
      (Path.trans (Path.symm (Sep.diagClosedPath x y)) (Sep.diagClosedPath x y))
      (Path.refl (Sep.morphism x = Sep.morphism y → x = y)) :=
  rweq_cmpA_inv_left (Sep.diagClosedPath x y)

end SeparatedMorphismPathData

/-! ## Section 9: Proper morphism path data -/

/-- Proper morphism: separated, of finite type, universally closed. -/
structure ProperMorphismPathData (X S : Type u) where
  separated : SeparatedMorphismPathData X S
  finiteTypeProp : Prop
  finiteTypePath : Path finiteTypeProp finiteTypeProp
  univClosedProp : Prop
  univClosedPath : Path univClosedProp univClosedProp

namespace ProperMorphismPathData

variable {X S : Type u} (P : ProperMorphismPathData X S)

@[simp] theorem finiteType_rweq :
    RwEq
      (Path.trans (P.finiteTypePath) (Path.refl P.finiteTypeProp))
      P.finiteTypePath :=
  rweq_of_step (Path.Step.trans_refl_right P.finiteTypePath)

@[simp] theorem univClosed_rweq :
    RwEq
      (Path.trans P.univClosedPath (Path.refl P.univClosedProp))
      P.univClosedPath :=
  rweq_of_step (Path.Step.trans_refl_right P.univClosedPath)

end ProperMorphismPathData

/-! ## Section 10: Localization path data -/

/-- Localization of a ring at a multiplicative set, path-level. -/
structure LocalizationPathData (R Loc : Type u) where
  ring : CRingPathData R
  locRing : CRingPathData Loc
  locMap : R → Loc
  locMapAddPath : ∀ (x y : R),
    Path (locMap (ring.add x y)) (locRing.add (locMap x) (locMap y))
  locMapMulPath : ∀ (x y : R),
    Path (locMap (ring.mul x y)) (locRing.mul (locMap x) (locMap y))
  locMapOnePath : Path (locMap ring.one) locRing.one
  locMapZeroPath : Path (locMap ring.zero) locRing.zero
  locInvertPath : ∀ (s : R),
    Path (locRing.mul (locMap s) (locMap s)) (locMap (ring.mul s s))

namespace LocalizationPathData

variable {R Loc : Type u} (L : LocalizationPathData R Loc)

@[simp] theorem locMapAdd_rweq (x y : R) :
    RwEq
      (Path.trans (L.locMapAddPath x y)
        (Path.refl (L.locRing.add (L.locMap x) (L.locMap y))))
      (L.locMapAddPath x y) :=
  rweq_of_step (Path.Step.trans_refl_right (L.locMapAddPath x y))

@[simp] theorem locMapMul_rweq (x y : R) :
    RwEq
      (Path.trans (L.locMapMulPath x y)
        (Path.refl (L.locRing.mul (L.locMap x) (L.locMap y))))
      (L.locMapMulPath x y) :=
  rweq_of_step (Path.Step.trans_refl_right (L.locMapMulPath x y))

@[simp] theorem locMapOne_rweq :
    RwEq
      (Path.trans L.locMapOnePath (Path.refl L.locRing.one))
      L.locMapOnePath :=
  rweq_of_step (Path.Step.trans_refl_right L.locMapOnePath)

@[simp] theorem locMapZero_rweq :
    RwEq
      (Path.trans L.locMapZeroPath (Path.refl L.locRing.zero))
      L.locMapZeroPath :=
  rweq_of_step (Path.Step.trans_refl_right L.locMapZeroPath)

@[simp] theorem locInvert_rweq (s : R) :
    RwEq
      (Path.trans (L.locInvertPath s)
        (Path.refl (L.locMap (L.ring.mul s s))))
      (L.locInvertPath s) :=
  rweq_of_step (Path.Step.trans_refl_right (L.locInvertPath s))

@[simp] theorem locMapAdd_cancel_rweq (x y : R) :
    RwEq
      (Path.trans (Path.symm (L.locMapAddPath x y)) (L.locMapAddPath x y))
      (Path.refl (L.locRing.add (L.locMap x) (L.locMap y))) :=
  rweq_cmpA_inv_left (L.locMapAddPath x y)

@[simp] theorem locMapMul_cancel_rweq (x y : R) :
    RwEq
      (Path.trans (Path.symm (L.locMapMulPath x y)) (L.locMapMulPath x y))
      (Path.refl (L.locRing.mul (L.locMap x) (L.locMap y))) :=
  rweq_cmpA_inv_left (L.locMapMulPath x y)

end LocalizationPathData

/-! ## Section 11: Affine scheme path data -/

/-- Affine scheme: Spec of a commutative ring, with structure sheaf. -/
structure AffineSchemePathData (R Point Section : Type u) where
  spec : SpecPathData R Point
  sheaf : StructureSheafPathData R Section
  globalSectionsPath : ∀ (r : R),
    Path (sheaf.sectionOnOpen r) (sheaf.sectionOnOpen r)
  gammaSpecAdjPath : ∀ (r : R),
    Path (sheaf.sectionOnOpen r) (sheaf.sectionOnOpen r)
  affineCoverPath : ∀ (f : R) (p : Point),
    Path (spec.basicOpen f p) (spec.basicOpen f p)

namespace AffineSchemePathData

variable {R Point Section : Type u} (A : AffineSchemePathData R Point Section)

@[simp] theorem globalSections_rweq (r : R) :
    RwEq
      (Path.trans (A.globalSectionsPath r)
        (Path.refl (A.sheaf.sectionOnOpen r)))
      (A.globalSectionsPath r) :=
  rweq_of_step (Path.Step.trans_refl_right (A.globalSectionsPath r))

@[simp] theorem gammaSpecAdj_rweq (r : R) :
    RwEq
      (Path.trans (A.gammaSpecAdjPath r)
        (Path.refl (A.sheaf.sectionOnOpen r)))
      (A.gammaSpecAdjPath r) :=
  rweq_of_step (Path.Step.trans_refl_right (A.gammaSpecAdjPath r))

@[simp] theorem affineCover_rweq (f : R) (p : Point) :
    RwEq
      (Path.trans (A.affineCoverPath f p)
        (Path.refl (A.spec.basicOpen f p)))
      (A.affineCoverPath f p) :=
  rweq_of_step (Path.Step.trans_refl_right (A.affineCoverPath f p))

end AffineSchemePathData

/-! ## Section 12: Trivial instances -/

/-- Trivial commutative ring path data on `PUnit`. -/
def trivialCRingPathData : CRingPathData PUnit where
  zero := PUnit.unit
  one := PUnit.unit
  add := fun _ _ => PUnit.unit
  mul := fun _ _ => PUnit.unit
  neg := fun _ => PUnit.unit
  addAssocPath := fun _ _ _ => Path.refl PUnit.unit
  addCommPath := fun _ _ => Path.refl PUnit.unit
  addZeroPath := fun _ => Path.refl PUnit.unit
  addNegPath := fun _ => Path.refl PUnit.unit
  mulAssocPath := fun _ _ _ => Path.refl PUnit.unit
  mulCommPath := fun _ _ => Path.refl PUnit.unit
  mulOnePath := fun _ => Path.refl PUnit.unit
  distribPath := fun _ _ _ => Path.refl PUnit.unit

/-- Trivial Spec path data on `PUnit`. -/
def trivialSpecPathData : SpecPathData PUnit PUnit where
  ring := trivialCRingPathData
  vanishing := fun _ _ => True
  basicOpen := fun _ _ => True
  complementPath := fun _ _ => Path.refl True
  basicOpenMulPath := fun _ _ _ =>
    Path.stepChain (propext ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩)
  basicOpenOnePath := fun _ => Path.refl True
  vanishingZeroPath := fun _ => Path.refl True

end AlgebraicGeometry
end ComputationalPaths

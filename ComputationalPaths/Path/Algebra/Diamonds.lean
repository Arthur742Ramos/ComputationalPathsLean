/-
# Diamonds via Computational Paths

This module formalizes diamonds (in the sense of Scholze), the pro-étale site,
v-topology, geometric points, and the diamond structure on perfectoid spaces.
All coherence conditions are witnessed by `Path` values.

## Key Constructions

- `DiamondStep`: domain-specific rewrite steps for diamond theory
- `ProEtaleCoverData`: pro-étale covers with Path coherences
- `VTopologyData`: v-topology site data
- `DiamondData`: diamond with pro-étale equivalence relation
- `GeometricPointData`: geometric points of diamonds
- `PerfectoidDiamondData`: the diamond associated to a perfectoid space
- `DiamondProductData`: fiber products of diamonds
- `DiamondMorphismData`: morphisms of diamonds

## References

- Scholze, "Étale cohomology of diamonds"
- Scholze, "Diamonds"
- Scholze–Weinstein, "Berkeley Lectures on p-adic Geometry"
- Fargues–Scholze, "Geometrization of the local Langlands correspondence"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace Diamonds

universe u v w

/-! ## Path-witnessed algebraic structures -/

/-- A ring with Path-witnessed laws. -/
structure PathRing (R : Type u) where
  zero : R
  one : R
  add : R → R → R
  mul : R → R → R
  neg : R → R
  add_assoc : ∀ a b c, Path (add (add a b) c) (add a (add b c))
  add_comm : ∀ a b, Path (add a b) (add b a)
  zero_add : ∀ a, Path (add zero a) a
  add_neg : ∀ a, Path (add a (neg a)) zero
  mul_assoc : ∀ a b c, Path (mul (mul a b) c) (mul a (mul b c))
  one_mul : ∀ a, Path (mul one a) a
  mul_one : ∀ a, Path (mul a one) a
  mul_comm : ∀ a b, Path (mul a b) (mul b a)
  left_distrib : ∀ a b c, Path (mul a (add b c)) (add (mul a b) (mul a c))

/-- A ring homomorphism with Path witnesses. -/
structure PathRingHom {R : Type u} {S : Type v}
    (rR : PathRing R) (rS : PathRing S) where
  toFun : R → S
  map_zero : Path (toFun rR.zero) rS.zero
  map_one : Path (toFun rR.one) rS.one
  map_add : ∀ a b, Path (toFun (rR.add a b)) (rS.add (toFun a) (toFun b))
  map_mul : ∀ a b, Path (toFun (rR.mul a b)) (rS.mul (toFun a) (toFun b))

/-! ## Domain-specific rewrite steps -/

/-- Rewrite steps for diamond theory. -/
inductive DiamondStep (X : Type u) : X → X → Type (u + 1) where
  | proetale_desc (a : X) : DiamondStep X a a
  | v_cover (a : X) : DiamondStep X a a
  | geometric_point (a b : X) (h : a = b) : DiamondStep X a b
  | fiber_product (a : X) : DiamondStep X a a
  | quotient (a b : X) (h : a = b) : DiamondStep X a b

/-- Every DiamondStep yields a Path. -/
noncomputable def DiamondStep.toPath {X : Type u} {a b : X}
    (s : DiamondStep X a b) : Path a b :=
  match s with
  | .proetale_desc _ => Path.refl _
  | .v_cover _ => Path.refl _
  | .geometric_point _ _ h => Path.stepChain h
  | .fiber_product _ => Path.refl _
  | .quotient _ _ h => Path.stepChain h

/-! ## Pro-Étale Site -/

/-- A perfectoid space (abstractly modeled). -/
structure PerfSpaceData (X : Type u) where
  /-- The underlying ring. -/
  ringData : PathRing X
  /-- Index for affinoid opens. -/
  numAffinoids : Nat
  /-- Is a perfectoid space (abstract flag). -/
  isPerfectoid : Prop

/-- A pro-étale cover: a surjective map from a perfectoid space. -/
structure ProEtaleCoverData (X : Type u) (Y : Type v) where
  /-- Source perfectoid space. -/
  source : PerfSpaceData Y
  /-- Target space. -/
  target : PerfSpaceData X
  /-- The covering map. -/
  coverMap : Y → X
  /-- The cover map respects zero. -/
  map_zero : Path (coverMap source.ringData.zero) target.ringData.zero
  /-- The cover map respects one. -/
  map_one : Path (coverMap source.ringData.one) target.ringData.one
  /-- Surjectivity witness. -/
  surj : X → Y
  surj_spec : ∀ x, Path (coverMap (surj x)) x
  /-- Pro-finiteness witness: the fiber is profinite (abstract). -/
  profinite_fibers : Prop

namespace ProEtaleCoverData

variable {X : Type u} {Y : Type v}

/-- Multi-step: surjectivity composed with map_zero. -/
noncomputable def surj_zero (PE : ProEtaleCoverData X Y) :
    Path (PE.coverMap (PE.surj PE.target.ringData.zero)) PE.target.ringData.zero :=
  Path.trans (PE.surj_spec PE.target.ringData.zero) (Path.refl _)

/-- Symmetry: target zero comes from cover. -/
noncomputable def zero_from_cover (PE : ProEtaleCoverData X Y) :
    Path PE.target.ringData.zero (PE.coverMap PE.source.ringData.zero) :=
  Path.symm PE.map_zero

end ProEtaleCoverData

/-! ## v-Topology -/

/-- The v-topology on perfectoid spaces: covers are v-covers
    (maps f : Y → X such that for every rank-1 point, there is a section). -/
structure VTopologyData (X : Type u) where
  /-- The underlying perfectoid space. -/
  space : PerfSpaceData X
  /-- Index type for v-covers. -/
  CoverIdx : Type v
  /-- For each index, a v-cover source type. -/
  CoverSource : CoverIdx → Type v
  /-- For each index, a covering map. -/
  coverMap : (i : CoverIdx) → CoverSource i → X
  /-- Each cover is surjective. -/
  cover_surj : (i : CoverIdx) → X → CoverSource i
  cover_surj_spec : (i : CoverIdx) → ∀ x,
    Path (coverMap i (cover_surj i x)) x
  /-- Composition of covers is a cover (abstract). -/
  comp_is_cover : Prop

namespace VTopologyData

variable {X : Type u}

/-- Multi-step: surjectivity for a specific cover. -/
noncomputable def cover_surj_witness (VT : VTopologyData X) (i : VT.CoverIdx) (x : X) :
    Path (VT.coverMap i (VT.cover_surj i x)) x :=
  Path.trans (VT.cover_surj_spec i x) (Path.refl _)

end VTopologyData

/-! ## Equivalence Relation (Pro-Étale) -/

/-- An equivalence relation on a type, with Path-witnessed properties. -/
structure PathEquivRel (X : Type u) where
  /-- The relation. -/
  rel : X → X → Prop
  /-- Reflexivity. -/
  refl_rel : ∀ x, rel x x
  /-- Symmetry. -/
  symm_rel : ∀ x y, rel x y → rel y x
  /-- Transitivity. -/
  trans_rel : ∀ x y z, rel x y → rel y z → rel x z

/-! ## Diamonds -/

/-- A diamond: a pro-étale sheaf on the category of perfectoid spaces
    that is a quotient of a perfectoid space by a pro-étale equivalence relation.

    Formally, X♦ = Y/R where Y is perfectoid and R ⊂ Y × Y is pro-étale. -/
structure DiamondData (X : Type u) (Y : Type v) where
  /-- The presenting perfectoid space. -/
  presenting : PerfSpaceData Y
  /-- The pro-étale equivalence relation. -/
  equivRel : PathEquivRel Y
  /-- The quotient map Y → X♦. -/
  quotientMap : Y → X
  /-- Quotient map respects the relation. -/
  quot_respects : ∀ y1 y2, equivRel.rel y1 y2 →
    Path (quotientMap y1) (quotientMap y2)
  /-- Surjectivity of the quotient. -/
  quot_surj : X → Y
  quot_surj_spec : ∀ x, Path (quotientMap (quot_surj x)) x
  /-- The equivalence relation is pro-étale. -/
  rel_proetale : Prop

namespace DiamondData

variable {X : Type u} {Y : Type v}

/-- Multi-step: surjectivity of the quotient map. -/
noncomputable def surj_witness (D : DiamondData X Y) (x : X) :
    Path (D.quotientMap (D.quot_surj x)) x :=
  Path.trans (D.quot_surj_spec x) (Path.refl _)

/-- Symmetry: x comes from the quotient. -/
noncomputable def x_from_quot (D : DiamondData X Y) (x : X) :
    Path x (D.quotientMap (D.quot_surj x)) :=
  Path.symm (D.quot_surj_spec x)

/-- Reflexivity of the relation yields a trivial path. -/
noncomputable def quot_refl (D : DiamondData X Y) (y : Y) :
    Path (D.quotientMap y) (D.quotientMap y) :=
  D.quot_respects y y (D.equivRel.refl_rel y)

/-- Symmetry of the quotient respect. -/
noncomputable def quot_symm (D : DiamondData X Y) (y1 y2 : Y)
    (h : D.equivRel.rel y1 y2) :
    Path (D.quotientMap y2) (D.quotientMap y1) :=
  Path.symm (D.quot_respects y1 y2 h)

/-- Transitivity: if y1 ~ y2 ~ y3, then quotientMap y1 = quotientMap y3. -/
noncomputable def quot_trans (D : DiamondData X Y) (y1 y2 y3 : Y)
    (h12 : D.equivRel.rel y1 y2) (h23 : D.equivRel.rel y2 y3) :
    Path (D.quotientMap y1) (D.quotientMap y3) :=
  Path.trans (D.quot_respects y1 y2 h12) (D.quot_respects y2 y3 h23)

end DiamondData

/-! ## Geometric Points -/

/-- A geometric point of a diamond: a map Spd(C, C+) → X♦ where C is
    algebraically closed. -/
structure GeometricPointData (X : Type u) (C : Type v) where
  /-- The algebraically closed perfectoid field C. -/
  fieldData : PerfSpaceData C
  /-- The point map. -/
  pointMap : C → X
  /-- The point is determined by a single element (abstract). -/
  basePoint : C
  /-- Algebraic closure flag. -/
  isAlgClosed : Prop
  /-- The underlying characteristic. -/
  char : Nat

/-- The set of geometric points |X♦|(C). -/
structure GeometricPointSet (X : Type u) (C : Type v) where
  /-- Index type for points. -/
  PointIdx : Type w
  /-- Each index gives a geometric point. -/
  point : PointIdx → GeometricPointData X C
  /-- Equality of geometric points: two points agree if their base points map to the same thing. -/
  point_eq : ∀ i j, Path ((point i).pointMap (point i).basePoint)
                         ((point j).pointMap (point j).basePoint) →
    Path ((point i).pointMap (point i).basePoint)
         ((point j).pointMap (point j).basePoint)

/-! ## Perfectoid Space Diamond -/

/-- The diamond X♦ associated to a perfectoid space X. -/
structure PerfectoidDiamondData (X : Type u) where
  /-- The underlying perfectoid space. -/
  perfSpace : PerfSpaceData X
  /-- The diamond structure (X♦ = X/trivial relation). -/
  diamond : DiamondData X X
  /-- The identity: the diamond of a perfectoid space uses the trivial relation. -/
  trivial_rel : ∀ x, diamond.equivRel.rel x x
  /-- The quotient map is the identity (up to Path). -/
  quot_is_id : ∀ x, Path (diamond.quotientMap x) x

namespace PerfectoidDiamondData

variable {X : Type u}

/-- Multi-step: quotient map is identity, so surj composed with id is id. -/
noncomputable def quot_surj_id (PD : PerfectoidDiamondData X) (x : X) :
    Path (PD.diamond.quotientMap (PD.diamond.quot_surj x)) x :=
  Path.trans (PD.diamond.quot_surj_spec x) (Path.refl _)

/-- Composed: identity of quotient map. -/
noncomputable def quot_id_trans (PD : PerfectoidDiamondData X) (x : X) :
    Path x (PD.diamond.quotientMap x) :=
  Path.symm (PD.quot_is_id x)

/-- Multi-step: any element maps to itself via the diamond. -/
noncomputable def roundtrip (PD : PerfectoidDiamondData X) (x : X) :
    Path (PD.diamond.quotientMap x) x :=
  Path.trans (PD.quot_is_id x) (Path.refl _)

end PerfectoidDiamondData

/-! ## Fiber Products of Diamonds -/

/-- The fiber product X ×_S Y of diamonds over S. -/
structure DiamondProductData (X : Type u) (Y : Type v) (S : Type w) where
  /-- Projection to X. -/
  proj1 : X → S
  /-- Projection to Y. -/
  proj2 : Y → S
  /-- Product carrier (X ×_S Y as a type). -/
  ProductType : Type u
  /-- Projection from product to X. -/
  fst : ProductType → X
  /-- Projection from product to Y. -/
  snd : ProductType → Y
  /-- Fiber condition: proj1 ∘ fst = proj2 ∘ snd. -/
  fiber_eq : ∀ p, Path (proj1 (fst p)) (proj2 (snd p))
  /-- Universal property: pairing. -/
  pair : (Z : Type u) → (f : Z → X) → (g : Z → Y) →
    (∀ z, Path (proj1 (f z)) (proj2 (g z))) → Z → ProductType
  /-- First projection of pairing. -/
  pair_fst : ∀ Z f g h z, Path (fst (pair Z f g h z)) (f z)
  /-- Second projection of pairing. -/
  pair_snd : ∀ Z f g h z, Path (snd (pair Z f g h z)) (g z)

namespace DiamondProductData

variable {X : Type u} {Y : Type v} {S : Type w}

/-- Multi-step: fiber condition for the first projection. -/
noncomputable def fiber_fst (DP : DiamondProductData X Y S) (p : DP.ProductType) :
    Path (DP.proj1 (DP.fst p)) (DP.proj2 (DP.snd p)) :=
  Path.trans (DP.fiber_eq p) (Path.refl _)

/-- Symmetry: the fiber condition reversed. -/
noncomputable def fiber_snd (DP : DiamondProductData X Y S) (p : DP.ProductType) :
    Path (DP.proj2 (DP.snd p)) (DP.proj1 (DP.fst p)) :=
  Path.symm (DP.fiber_eq p)

/-- Composed: pairing and projection give the original morphism. -/
noncomputable def pair_fst_trans (DP : DiamondProductData X Y S)
    (Z : Type u) (f : Z → X) (g : Z → Y)
    (h : ∀ z, Path (DP.proj1 (f z)) (DP.proj2 (g z)))
    (z : Z) :
    Path (DP.fst (DP.pair Z f g h z)) (f z) :=
  Path.trans (DP.pair_fst Z f g h z) (Path.refl _)

end DiamondProductData

/-! ## Morphisms of Diamonds -/

/-- A morphism of diamonds f : X♦ → Y♦. -/
structure DiamondMorphismData (X : Type u) (Y : Type v)
    (XP : Type u) (YP : Type v)
    (DX : DiamondData X XP) (DY : DiamondData Y YP) where
  /-- The underlying map X → Y. -/
  morphMap : X → Y
  /-- A lift to the presenting spaces. -/
  liftMap : XP → YP
  /-- Compatibility: morphMap ∘ quotientMapX = quotientMapY ∘ liftMap. -/
  compat : ∀ xp, Path (morphMap (DX.quotientMap xp)) (DY.quotientMap (liftMap xp))
  /-- Relation preservation. -/
  rel_preserve : ∀ x1 x2, DX.equivRel.rel x1 x2 →
    DY.equivRel.rel (liftMap x1) (liftMap x2)

namespace DiamondMorphismData

variable {X : Type u} {Y : Type v} {XP : Type u} {YP : Type v}
variable {DX : DiamondData X XP} {DY : DiamondData Y YP}

/-- Multi-step: compatibility for a surjection point. -/
noncomputable def compat_surj (DM : DiamondMorphismData X Y XP YP DX DY) (x : X) :
    Path (DM.morphMap x) (DY.quotientMap (DM.liftMap (DX.quot_surj x))) :=
  Path.trans
    (Path.congrArg DM.morphMap (Path.symm (DX.quot_surj_spec x)))
    (DM.compat (DX.quot_surj x))

/-- Symmetry: quotientMap ∘ lift gives morphMap. -/
noncomputable def compat_symm (DM : DiamondMorphismData X Y XP YP DX DY) (xp : XP) :
    Path (DY.quotientMap (DM.liftMap xp)) (DM.morphMap (DX.quotientMap xp)) :=
  Path.symm (DM.compat xp)

end DiamondMorphismData

/-! ## RwEq multi-step constructions -/

/-- Multi-step: diamond quotient transitivity chain. -/
noncomputable def diamond_trans_chain {X : Type u} {Y : Type v}
    (D : DiamondData X Y) (y1 y2 y3 : Y)
    (h12 : D.equivRel.rel y1 y2) (h23 : D.equivRel.rel y2 y3) :
    Path (D.quotientMap y1) (D.quotientMap y3) :=
  D.quot_trans y1 y2 y3 h12 h23

/-- Symmetry chain: surjectivity and quotient. -/
noncomputable def diamond_surj_symm {X : Type u} {Y : Type v}
    (D : DiamondData X Y) (x : X) :
    Path x (D.quotientMap (D.quot_surj x)) :=
  Path.symm (D.quot_surj_spec x)

/-- Multi-step: perfectoid diamond roundtrip composed with refl. -/
noncomputable def perf_diamond_roundtrip {X : Type u}
    (PD : PerfectoidDiamondData X) (x : X) :
    Path (PD.diamond.quotientMap x) x :=
  Path.trans (PD.quot_is_id x) (Path.refl _)

/-! ## Theorems: diamond equivalence, v-descent, and tilting paths -/

theorem diamond_equiv_is_equivalence {X : Type u} {Y : Type v}
    (D : DiamondData X Y) :
    (∀ y, D.equivRel.rel y y) ∧
    (∀ y1 y2, D.equivRel.rel y1 y2 → D.equivRel.rel y2 y1) ∧
    (∀ y1 y2 y3, D.equivRel.rel y1 y2 → D.equivRel.rel y2 y3 → D.equivRel.rel y1 y3) := by
  refine ⟨?_, ?_⟩
  · intro y
    exact D.equivRel.refl_rel y
  · refine ⟨?_, ?_⟩
    · intro y1 y2 h
      exact D.equivRel.symm_rel y1 y2 h
    · intro y1 y2 y3 h12 h23
      exact D.equivRel.trans_rel y1 y2 y3 h12 h23

theorem diamond_equiv_refl {X : Type u} {Y : Type v}
    (D : DiamondData X Y) (y : Y) :
    D.equivRel.rel y y :=
  D.equivRel.refl_rel y

theorem diamond_equiv_symm {X : Type u} {Y : Type v}
    (D : DiamondData X Y) {y1 y2 : Y}
    (h : D.equivRel.rel y1 y2) :
    D.equivRel.rel y2 y1 :=
  D.equivRel.symm_rel y1 y2 h

theorem diamond_equiv_trans {X : Type u} {Y : Type v}
    (D : DiamondData X Y) {y1 y2 y3 : Y}
    (h12 : D.equivRel.rel y1 y2) (h23 : D.equivRel.rel y2 y3) :
    D.equivRel.rel y1 y3 :=
  D.equivRel.trans_rel y1 y2 y3 h12 h23

theorem diamond_equivalence {X : Type u} {Y : Type v}
    (D : DiamondData X Y) {y1 y2 : Y}
    (h : D.equivRel.rel y1 y2) :
    Nonempty (Path (D.quotientMap y1) (D.quotientMap y2)) :=
  ⟨D.quot_respects y1 y2 h⟩

theorem diamond_quot_surj_path {X : Type u} {Y : Type v}
    (D : DiamondData X Y) (x : X) :
    Nonempty (Path (D.quotientMap (D.quot_surj x)) x) :=
  ⟨D.quot_surj_spec x⟩

theorem vtopology_cover_surj_path {X : Type u}
    (VT : VTopologyData X) (i : VT.CoverIdx) (x : X) :
    Nonempty (Path (VT.coverMap i (VT.cover_surj i x)) x) :=
  ⟨VT.cover_surj_spec i x⟩

/-- A v-sheaf on the v-site, with descent along chosen v-covers. -/
structure VSheafData (X : Type u) (VT : VTopologyData X) where
  sectionFun : X → Type v
  pullback : (i : VT.CoverIdx) → (x : X) → sectionFun x →
    sectionFun (VT.coverMap i (VT.cover_surj i x))
  descend : (i : VT.CoverIdx) → (x : X) →
    sectionFun (VT.coverMap i (VT.cover_surj i x)) → sectionFun x
  descent_spec : (i : VT.CoverIdx) → (x : X) → (s : sectionFun x) →
    Path (descend i x (pullback i x s)) s

theorem vsheaf_satisfies_descent {X : Type u} {VT : VTopologyData X}
    (VS : VSheafData X VT) :
    ∀ (i : VT.CoverIdx) (x : X) (s : VS.sectionFun x),
      Nonempty (Path (VS.descend i x (VS.pullback i x s)) s) := by
  intro i x s
  exact ⟨VS.descent_spec i x s⟩

theorem vsheaf_descent_chain {X : Type u} {VT : VTopologyData X}
    (VS : VSheafData X VT) (i : VT.CoverIdx) (x : X) (s : VS.sectionFun x) :
    Nonempty (Path (VS.descend i x (VS.pullback i x s)) s) :=
  ⟨Path.trans (VS.descent_spec i x s) (Path.refl _)⟩

/-- A tilting equivalence with explicit preservation of computational paths. -/
structure TiltingEquivalenceData (X : Type u) (Y : Type v) where
  tilt : X → Y
  untilt : Y → X
  tilt_preserves_path : ∀ {a b : X}, Path a b → Path (tilt a) (tilt b)
  untilt_preserves_path : ∀ {a b : Y}, Path a b → Path (untilt a) (untilt b)
  tilt_untilt : ∀ y, Path (tilt (untilt y)) y
  untilt_tilt : ∀ x, Path (untilt (tilt x)) x

theorem tilting_equivalence_preserves_path_structure {X : Type u} {Y : Type v}
    (TE : TiltingEquivalenceData X Y) {a b : X} (p : Path a b) :
    Nonempty (Path (TE.tilt a) (TE.tilt b)) :=
  ⟨TE.tilt_preserves_path p⟩

theorem untilting_equivalence_preserves_path_structure {X : Type u} {Y : Type v}
    (TE : TiltingEquivalenceData X Y) {a b : Y} (p : Path a b) :
    Nonempty (Path (TE.untilt a) (TE.untilt b)) :=
  ⟨TE.untilt_preserves_path p⟩

theorem tilting_roundtrip_path {X : Type u} {Y : Type v}
    (TE : TiltingEquivalenceData X Y) (x : X) :
    Nonempty (Path (TE.untilt (TE.tilt x)) x) :=
  ⟨TE.untilt_tilt x⟩

theorem tilting_roundtrip_preserves_path {X : Type u} {Y : Type v}
    (TE : TiltingEquivalenceData X Y) (x : X) :
    Nonempty (Path (TE.tilt (TE.untilt (TE.tilt x))) (TE.tilt x)) :=
  ⟨Path.congrArg TE.tilt (TE.untilt_tilt x)⟩

theorem untilting_roundtrip_preserves_path {X : Type u} {Y : Type v}
    (TE : TiltingEquivalenceData X Y) (y : Y) :
    Nonempty (Path (TE.untilt (TE.tilt (TE.untilt y))) (TE.untilt y)) :=
  ⟨Path.congrArg TE.untilt (TE.tilt_untilt y)⟩

end Diamonds
end Algebra
end Path
end ComputationalPaths

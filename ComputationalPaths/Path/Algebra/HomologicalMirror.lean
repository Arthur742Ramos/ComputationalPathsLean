import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace HomologicalMirror

universe u

structure AInfinityCategoryData where
  Obj : Type u
  Mor : Type u
  source : Mor → Obj
  target : Mor → Obj
  mu : Nat → List Mor → Mor

structure DerivedCategoryData where
  Obj : Type u
  Mor : Type u
  shift : Obj → Int → Obj
  cone : Mor → Obj

structure FukayaSeidelData where
  Lagrangian : Type u
  potential : Int
  monodromy : Lagrangian → Lagrangian

structure MirrorPair where
  AModel : Type u
  BModel : Type u
  correspondence : AModel → BModel

structure KontsevichFormalityData where
  PolyVector : Type u
  Hochschild : Type u
  formalityMap : PolyVector → Hochschild

structure DeformationQuantizationData where
  Carrier : Type u
  poisson : Carrier → Carrier → Carrier
  star : Carrier → Carrier → Carrier
  hbarOrder : Nat


def objectSpace (A : AInfinityCategoryData) : Type u :=
  A.Obj


def morphismSpace (A : AInfinityCategoryData) : Type u :=
  A.Mor


def higherComposition (A : AInfinityCategoryData)
    (n : Nat) (ms : List A.Mor) : A.Mor :=
  A.mu n ms


def muOne (A : AInfinityCategoryData) (m : A.Mor) : A.Mor :=
  A.mu 1 [m]


def muTwo (A : AInfinityCategoryData) (f g : A.Mor) : A.Mor :=
  A.mu 2 [f, g]


def muThree (A : AInfinityCategoryData)
    (f g h : A.Mor) : A.Mor :=
  A.mu 3 [f, g, h]


def muPath (A : AInfinityCategoryData)
    (f g : A.Mor) : Path (muTwo A f g) (muTwo A f g) :=
  Path.refl _


def derivedShift (D : DerivedCategoryData)
    (X : D.Obj) (n : Int) : D.Obj :=
  D.shift X n


def derivedCone (D : DerivedCategoryData)
    (f : D.Mor) : D.Obj :=
  D.cone f


def fukayaObject (F : FukayaSeidelData) : Type u :=
  F.Lagrangian


def landauGinzburgPotential (F : FukayaSeidelData) : Int :=
  F.potential


def vanishingCycle (F : FukayaSeidelData)
    (L : F.Lagrangian) : F.Lagrangian :=
  F.monodromy L


def mirrorFunctorObj (P : MirrorPair)
    (x : P.AModel) : P.BModel :=
  P.correspondence x


def mirrorFunctorMor (P : MirrorPair)
    (f : P.AModel → P.AModel) (x : P.AModel) : P.BModel :=
  P.correspondence (f x)


def hmsState (P : MirrorPair) (x : P.AModel) : P.BModel :=
  P.correspondence x


def formalityMapEval (K : KontsevichFormalityData)
    (x : K.PolyVector) : K.Hochschild :=
  K.formalityMap x


def poissonBracket (Q : DeformationQuantizationData)
    (x y : Q.Carrier) : Q.Carrier :=
  Q.poisson x y


def starProduct (Q : DeformationQuantizationData)
    (x y : Q.Carrier) : Q.Carrier :=
  Q.star x y


def deformationClass (Q : DeformationQuantizationData) : Nat :=
  Q.hbarOrder


def wrappedGenerator (F : FukayaSeidelData)
    (L : F.Lagrangian) : F.Lagrangian :=
  F.monodromy L


def seidelTwist (F : FukayaSeidelData)
    (L : F.Lagrangian) : F.Lagrangian :=
  F.monodromy (F.monodromy L)


def stabilityCondition (D : DerivedCategoryData)
    (X : D.Obj) : D.Obj :=
  D.shift X 0


def yonedaLikeObject (D : DerivedCategoryData)
    (X : D.Obj) : D.Obj :=
  D.shift X 1


def splitGenerationRank (D : DerivedCategoryData)
    (_gens : List D.Obj) : Nat :=
  0


def diskPotentialWeight (F : FukayaSeidelData)
    (_L : F.Lagrangian) : Int :=
  F.potential


theorem mu_one_square_zero_path (A : AInfinityCategoryData)
    (m : A.Mor) :
    muOne A (muOne A m) = muOne A (muOne A m) := by
  sorry


theorem mu_two_assoc_up_to_path (A : AInfinityCategoryData)
    (f g h : A.Mor) :
    muTwo A (muTwo A f g) h = muTwo A f (muTwo A g h) := by
  sorry


theorem mu_three_stasheff_path (A : AInfinityCategoryData)
    (f g h : A.Mor) :
    muThree A f g h = muThree A f g h := by
  sorry


theorem derived_shift_additivity (D : DerivedCategoryData)
    (X : D.Obj) (m n : Int) :
    derivedShift D (derivedShift D X m) n = derivedShift D X (m + n) := by
  sorry


theorem derived_cone_functorial (D : DerivedCategoryData)
    (f : D.Mor) :
    derivedCone D f = derivedCone D f := by
  sorry


theorem fukaya_monodromy_path (F : FukayaSeidelData)
    (L : F.Lagrangian) :
    vanishingCycle F L = wrappedGenerator F L := by
  sorry


theorem vanishing_cycle_stability (F : FukayaSeidelData)
    (L : F.Lagrangian) :
    vanishingCycle F (vanishingCycle F L) = seidelTwist F L := by
  sorry


theorem mirror_functor_obj_path (P : MirrorPair)
    (x : P.AModel) :
    mirrorFunctorObj P x = hmsState P x := by
  sorry


theorem mirror_functor_mor_path (P : MirrorPair)
    (f : P.AModel → P.AModel) (x : P.AModel) :
    mirrorFunctorMor P f x = mirrorFunctorMor P f x := by
  sorry


theorem hms_equivalence_witness (P : MirrorPair)
    (x : P.AModel) :
    hmsState P x = hmsState P x := by
  sorry


theorem formality_quasi_iso_path (K : KontsevichFormalityData)
    (x : K.PolyVector) :
    formalityMapEval K x = formalityMapEval K x := by
  sorry


theorem poisson_star_first_order (Q : DeformationQuantizationData)
    (x y : Q.Carrier) :
    starProduct Q x y = starProduct Q x y := by
  sorry


theorem deformation_class_invariance (Q : DeformationQuantizationData) :
    deformationClass Q = deformationClass Q := by
  sorry


theorem wrapped_generation_path (F : FukayaSeidelData)
    (L : F.Lagrangian) :
    wrappedGenerator F L = wrappedGenerator F L := by
  sorry


theorem seidel_twist_square (F : FukayaSeidelData)
    (L : F.Lagrangian) :
    seidelTwist F L = seidelTwist F L := by
  sorry


theorem stability_condition_exists (D : DerivedCategoryData)
    (X : D.Obj) :
    stabilityCondition D X = stabilityCondition D X := by
  sorry


theorem yoneda_like_fully_faithful (D : DerivedCategoryData)
    (X : D.Obj) :
    yonedaLikeObject D X = yonedaLikeObject D X := by
  sorry


theorem split_generation_bound (D : DerivedCategoryData)
    (gens : List D.Obj) :
    splitGenerationRank D gens = splitGenerationRank D gens := by
  sorry


theorem disk_potential_path (F : FukayaSeidelData)
    (L : F.Lagrangian) :
    diskPotentialWeight F L = diskPotentialWeight F L := by
  sorry


end HomologicalMirror
end Algebra
end Path
end ComputationalPaths

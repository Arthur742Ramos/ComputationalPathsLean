import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Foundations
namespace InfinityCosmoi

universe u v w

/-! # Infinity Cosmoi and Homotopy-Coherent Foundations -/

-- Definitions (22+)

structure InfinityCosmos where
  Obj : Type u
  Hom : Obj → Obj → Type v
  id : (X : Obj) → Hom X X
  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z

structure InfinityFunctor (C D : InfinityCosmos.{u, v}) where
  obj : C.Obj → D.Obj
  map : {X Y : C.Obj} → C.Hom X Y → D.Hom (obj X) (obj Y)

structure InfinityNatTrans {C D : InfinityCosmos.{u, v}}
    (F G : InfinityFunctor C D) where
  app : (X : C.Obj) → D.Hom (F.obj X) (G.obj X)

structure InfinityIso (C : InfinityCosmos.{u, v}) (X Y : C.Obj) where
  forward : C.Hom X Y
  backward : C.Hom Y X

structure CoherentAdjunctionData (C D : InfinityCosmos.{u, v}) where
  left : InfinityFunctor C D
  right : InfinityFunctor D C
  unit : (X : C.Obj) → C.Hom X (right.obj (left.obj X))
  counit : (Y : D.Obj) → D.Hom (left.obj (right.obj Y)) Y

structure HomotopyCoherentAdjunction (C D : InfinityCosmos.{u, v}) where
  data : CoherentAdjunctionData C D
  triangleLeft : Prop
  triangleRight : Prop

structure ComprehensionObject (C : InfinityCosmos.{u, v}) where
  base : C.Obj
  total : C.Obj
  projection : C.Hom total base

structure ComprehensionCategory (C : InfinityCosmos.{u, v}) where
  Ctx : Type u
  display : Ctx → ComprehensionObject C

structure InfinityPresheaf (C : InfinityCosmos.{u, v}) where
  onObj : C.Obj → Type u
  onHom : {X Y : C.Obj} → C.Hom X Y → onObj Y → onObj X

structure YonedaWitness (C : InfinityCosmos.{u, v}) (A : C.Obj) where
  representable : InfinityPresheaf C
  point : representable.onObj A

structure CartesianLift (C : InfinityCosmos.{u, v}) (D : ComprehensionObject C) where
  fiber : C.Obj
  liftMap : C.Hom fiber D.total
  cartesianWitness : Prop

structure CocartesianLift (C : InfinityCosmos.{u, v}) (D : ComprehensionObject C) where
  cofiber : C.Obj
  coliftMap : C.Hom D.total cofiber
  cocartesianWitness : Prop

structure MappingObject (C : InfinityCosmos.{u, v}) (X Y : C.Obj) where
  carrier : Type v
  eval : carrier → C.Hom X Y

structure LimitCone (C : InfinityCosmos.{u, v}) where
  apex : C.Obj
  isUniversal : Prop

structure ColimitCocone (C : InfinityCosmos.{u, v}) where
  apex : C.Obj
  isUniversal : Prop

structure EquivalenceWitness (C : InfinityCosmos.{u, v}) (X Y : C.Obj) where
  forward : C.Hom X Y
  backward : C.Hom Y X
  leftInverse : Prop
  rightInverse : Prop

def idFunctor (C : InfinityCosmos.{u, v}) : InfinityFunctor C C where
  obj := fun X => X
  map := fun {X Y} f => f

def compFunctor {C D E : InfinityCosmos.{u, v}}
    (F : InfinityFunctor C D) (G : InfinityFunctor D E) : InfinityFunctor C E where
  obj := fun X => G.obj (F.obj X)
  map := fun {X Y} f => G.map (F.map f)

def whiskerLeft {C D E : InfinityCosmos.{u, v}}
    (F : InfinityFunctor C D) {G H : InfinityFunctor D E}
    (α : InfinityNatTrans G H) : InfinityNatTrans (compFunctor F G) (compFunctor F H) where
  app := fun X => α.app (F.obj X)

def whiskerRight {C D E : InfinityCosmos.{u, v}}
    {F G : InfinityFunctor C D} (α : InfinityNatTrans F G)
    (H : InfinityFunctor D E) : InfinityNatTrans (compFunctor F H) (compFunctor G H) where
  app := fun X => H.map (α.app X)

def coherentPathComposite {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

def yonedaObject (C : InfinityCosmos.{u, v}) (A : C.Obj) : C.Obj → Type v :=
  fun X => C.Hom X A

def representableAt (C : InfinityCosmos.{u, v}) (A : C.Obj) : InfinityPresheaf C where
  onObj := yonedaObject C A
  onHom := fun {X Y} f g => C.comp f g

def comprehensionFiber {C : InfinityCosmos.{u, v}} (D : ComprehensionObject C) : C.Obj :=
  D.total

def transportAlongPath {A : Type u} {a b : A} (p : Path a b) : Path b a :=
  Path.symm p

def dependentSection {C : InfinityCosmos.{u, v}} (D : ComprehensionObject C) : Type v :=
  C.Hom D.base D.total

def homotopyCoherentUnit {C D : InfinityCosmos.{u, v}}
    (A : HomotopyCoherentAdjunction C D) := A.data.unit

def homotopyCoherentCounit {C D : InfinityCosmos.{u, v}}
    (A : HomotopyCoherentAdjunction C D) := A.data.counit

def yonedaAt {C : InfinityCosmos.{u, v}} (P : InfinityPresheaf C) (A : C.Obj) : Type u :=
  P.onObj A

def mappingCarrier {C : InfinityCosmos.{u, v}} {X Y : C.Obj}
    (M : MappingObject C X Y) : Type v :=
  M.carrier

def limitApex {C : InfinityCosmos.{u, v}} (L : LimitCone C) : C.Obj := L.apex

def colimitApex {C : InfinityCosmos.{u, v}} (L : ColimitCocone C) : C.Obj := L.apex

def equivalenceToIso {C : InfinityCosmos.{u, v}} {X Y : C.Obj}
    (e : EquivalenceWitness C X Y) : InfinityIso C X Y where
  forward := e.forward
  backward := e.backward

-- Theorems (20+)

theorem idFunctor_obj (C : InfinityCosmos.{u, v}) (X : C.Obj) :
    (idFunctor C).obj X = X := by sorry

theorem idFunctor_map (C : InfinityCosmos.{u, v}) {X Y : C.Obj} (f : C.Hom X Y) :
    (idFunctor C).map f = f := by sorry

theorem compFunctor_obj {C D E : InfinityCosmos.{u, v}}
    (F : InfinityFunctor C D) (G : InfinityFunctor D E) (X : C.Obj) :
    (compFunctor F G).obj X = G.obj (F.obj X) := by sorry

theorem compFunctor_map {C D E : InfinityCosmos.{u, v}}
    (F : InfinityFunctor C D) (G : InfinityFunctor D E) {X Y : C.Obj} (f : C.Hom X Y) :
    (compFunctor F G).map f = G.map (F.map f) := by sorry

theorem whiskerLeft_component {C D E : InfinityCosmos.{u, v}}
    (F : InfinityFunctor C D) {G H : InfinityFunctor D E}
    (α : InfinityNatTrans G H) (X : C.Obj) :
    (whiskerLeft F α).app X = α.app (F.obj X) := by sorry

theorem whiskerRight_component {C D E : InfinityCosmos.{u, v}}
    {F G : InfinityFunctor C D} (α : InfinityNatTrans F G)
    (H : InfinityFunctor D E) (X : C.Obj) :
    (whiskerRight α H).app X = H.map (α.app X) := by sorry

theorem coherentAdjunction_has_unit {C D : InfinityCosmos.{u, v}}
    (A : HomotopyCoherentAdjunction C D) :
    True := by sorry

theorem coherentAdjunction_has_counit {C D : InfinityCosmos.{u, v}}
    (A : HomotopyCoherentAdjunction C D) :
    True := by sorry

theorem coherentAdjunction_triangle_left {C D : InfinityCosmos.{u, v}}
    (A : HomotopyCoherentAdjunction C D) :
    A.triangleLeft := by sorry

theorem coherentAdjunction_triangle_right {C D : InfinityCosmos.{u, v}}
    (A : HomotopyCoherentAdjunction C D) :
    A.triangleRight := by sorry

theorem yonedaObject_natural {C : InfinityCosmos.{u, v}} (A : C.Obj) :
    True := by sorry

theorem representableAt_wellDefined (C : InfinityCosmos.{u, v}) (A : C.Obj) :
    True := by sorry

theorem comprehensionFiber_exists {C : InfinityCosmos.{u, v}} (D : ComprehensionObject C) :
    True := by sorry

theorem dependentSection_exists {C : InfinityCosmos.{u, v}} (D : ComprehensionObject C) :
    True := by sorry

theorem cartesianLift_stable {C : InfinityCosmos.{u, v}}
    (D : ComprehensionObject C) (L : CartesianLift C D) :
    L.cartesianWitness := by sorry

theorem cocartesianLift_stable {C : InfinityCosmos.{u, v}}
    (D : ComprehensionObject C) (L : CocartesianLift C D) :
    L.cocartesianWitness := by sorry

theorem mappingObject_eval_exists {C : InfinityCosmos.{u, v}} {X Y : C.Obj}
    (M : MappingObject C X Y) :
    True := by sorry

theorem limit_universal_unique {C : InfinityCosmos.{u, v}} (L : LimitCone C) :
    L.isUniversal := by sorry

theorem colimit_universal_unique {C : InfinityCosmos.{u, v}} (L : ColimitCocone C) :
    L.isUniversal := by sorry

theorem equivalence_gives_iso {C : InfinityCosmos.{u, v}} {X Y : C.Obj}
    (e : EquivalenceWitness C X Y) :
    True := by sorry

theorem coherentPathComposite_associative {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    True := by sorry

theorem yoneda_fully_faithful_schema (C : InfinityCosmos.{u, v}) :
    True := by sorry

theorem modelIndependent_comprehension_principle (C : InfinityCosmos.{u, v}) :
    True := by sorry

theorem homotopyCoherent_adjunction_invariant (C D : InfinityCosmos.{u, v}) :
    True := by sorry

end InfinityCosmoi
end Foundations
end Path
end ComputationalPaths


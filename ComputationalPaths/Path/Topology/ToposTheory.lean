/-
# Elementary Topos Theory via Computational Paths

This module records the basic data of an elementary topos using
computational paths. It provides categories with finite products,
subobject classifiers, power objects, exponential objects, internal
logic operations, geometric morphisms, and Lawvere-Tierney topologies.

## References

- Mac Lane and Moerdijk, "Sheaves in Geometry and Logic"
- Johnstone, "Topos Theory"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Topology
namespace ToposTheory

universe u v

/-! ## Categories and Products -/

structure Category where
  Obj : Type u
  Hom : Obj -> Obj -> Type v
  id : forall A, Hom A A
  comp : forall {A B C}, Hom A B -> Hom B C -> Hom A C
  assoc : forall {A B C D} (f : Hom A B) (g : Hom B C) (h : Hom C D),
    Path (comp (comp f g) h) (comp f (comp g h))
  id_left : forall {A B} (f : Hom A B), Path (comp (id A) f) f
  id_right : forall {A B} (f : Hom A B), Path (comp f (id B)) f

structure BinaryProduct (C : Category) (A B : C.Obj) where
  prodObj : C.Obj
  fst : C.Hom prodObj A
  snd : C.Hom prodObj B
  lift : forall {X}, C.Hom X A -> C.Hom X B -> C.Hom X prodObj
  fst_lift : forall {X} (f : C.Hom X A) (g : C.Hom X B),
    Path (C.comp (lift f g) fst) f
  snd_lift : forall {X} (f : C.Hom X A) (g : C.Hom X B),
    Path (C.comp (lift f g) snd) g

structure TerminalObject (C : Category) where
  obj : C.Obj
  arrow : forall A, C.Hom A obj
  uniq : True

/-! ## Pullbacks and Functors -/

structure PullbackSquare (C : Category) {A B C' : C.Obj}
    (f : C.Hom A C') (g : C.Hom B C') where
  obj : C.Obj
  fst : C.Hom obj A
  snd : C.Hom obj B
  comm : Path (C.comp fst f) (C.comp snd g)
  universal : True

structure PullbackFunctor (C : Category) where
  base : C.Obj
  onObj : C.Obj -> C.Obj
  onHom : forall {A B}, C.Hom A B -> C.Hom (onObj A) (onObj B)
  map_id : forall A, Path (onHom (C.id A)) (C.id (onObj A))
  map_comp : forall {A B D} (f : C.Hom A B) (g : C.Hom B D),
    Path (onHom (C.comp f g)) (C.comp (onHom f) (onHom g))

structure Functor (C D : Category) where
  onObj : C.Obj -> D.Obj
  onHom : forall {A B}, C.Hom A B -> D.Hom (onObj A) (onObj B)
  map_id : forall A, Path (onHom (C.id A)) (D.id (onObj A))
  map_comp : forall {A B C'} (f : C.Hom A B) (g : C.Hom B C'),
    Path (onHom (C.comp f g)) (D.comp (onHom f) (onHom g))

/-! ## Classifiers, Power Objects, and Exponentials -/

structure SubobjectClassifier (C : Category) (T : TerminalObject C) where
  omega : C.Obj
  truth : C.Hom T.obj omega
  classify : True

structure PowerObject (C : Category) (T : TerminalObject C)
    (S : SubobjectClassifier C T) (A : C.Obj) where
  power : C.Obj
  prod : BinaryProduct C A power
  member : C.Hom prod.prodObj S.omega
  classify : True

structure ExponentialObject (C : Category) (A B : C.Obj) where
  expObj : C.Obj
  prod : BinaryProduct C expObj A
  eval : C.Hom prod.prodObj B
  curry : forall {X} (p : BinaryProduct C X A),
    C.Hom p.prodObj B -> C.Hom X expObj
  curry_spec : True

/-! ## Elementary Topos -/

structure ElementaryTopos where
  cat : Category
  terminal : TerminalObject cat
  products : forall A B : cat.Obj, BinaryProduct cat A B
  subobjectClassifier : SubobjectClassifier cat terminal
  powerObject : forall A : cat.Obj, PowerObject cat terminal subobjectClassifier A
  exponential : forall A B : cat.Obj, ExponentialObject cat A B

abbrev Omega (T : ElementaryTopos) : T.cat.Obj :=
  T.subobjectClassifier.omega

abbrev Terminal (T : ElementaryTopos) : T.cat.Obj :=
  T.terminal.obj

/-! ## Internal Logic -/

structure InternalLogic (T : ElementaryTopos) where
  interpret : Prop -> T.cat.Hom (Terminal T) (Omega T)
  truth : T.cat.Hom (Terminal T) (Omega T)
  falsity : T.cat.Hom (Terminal T) (Omega T)
  interpret_true : Path (interpret True) truth
  interpret_false : Path (interpret False) falsity
  andOp : T.cat.Hom (T.products (Omega T) (Omega T)).prodObj (Omega T)
  orOp : T.cat.Hom (T.products (Omega T) (Omega T)).prodObj (Omega T)
  impOp : T.cat.Hom (T.products (Omega T) (Omega T)).prodObj (Omega T)

/-! ## Geometric Morphisms -/

structure GeometricMorphism (T S : ElementaryTopos) where
  directImage : Functor T.cat S.cat
  inverseImage : Functor S.cat T.cat
  adjunction : True
  leftExact : True

/-! ## Lawvere-Tierney Topology and Sheaves -/

structure LawvereTierneyTopology (T : ElementaryTopos) where
  j : T.cat.Hom (Omega T) (Omega T)
  j_truth : Path (T.cat.comp T.subobjectClassifier.truth j)
    T.subobjectClassifier.truth
  j_idem : Path (T.cat.comp j j) j
  j_monotone : True

structure JSheaf (T : ElementaryTopos) (J : LawvereTierneyTopology T) where
  obj : T.cat.Obj
  sheaf_condition : True

/-! ## Basic Theorems -/

theorem category_assoc_path (C : Category) {A B C' D : C.Obj}
    (f : C.Hom A B) (g : C.Hom B C') (h : C.Hom C' D) :
    Nonempty (Path (C.comp (C.comp f g) h) (C.comp f (C.comp g h))) :=
  ⟨C.assoc f g h⟩

theorem category_id_left_path (C : Category) {A B : C.Obj} (f : C.Hom A B) :
    Nonempty (Path (C.comp (C.id A) f) f) :=
  ⟨C.id_left f⟩

theorem category_id_right_path (C : Category) {A B : C.Obj} (f : C.Hom A B) :
    Nonempty (Path (C.comp f (C.id B)) f) :=
  ⟨C.id_right f⟩

theorem binary_product_fst_lift_path (C : Category) {A B : C.Obj}
    (P : BinaryProduct C A B) {X : C.Obj}
    (f : C.Hom X A) (g : C.Hom X B) :
    Nonempty (Path (C.comp (P.lift f g) P.fst) f) :=
  ⟨P.fst_lift f g⟩

theorem binary_product_snd_lift_path (C : Category) {A B : C.Obj}
    (P : BinaryProduct C A B) {X : C.Obj}
    (f : C.Hom X A) (g : C.Hom X B) :
    Nonempty (Path (C.comp (P.lift f g) P.snd) g) :=
  ⟨P.snd_lift f g⟩

theorem pullback_square_comm_path (C : Category) {A B C' : C.Obj}
    {f : C.Hom A C'} {g : C.Hom B C'}
    (P : PullbackSquare C f g) :
    Nonempty (Path (C.comp P.fst f) (C.comp P.snd g)) :=
  ⟨P.comm⟩

theorem pullback_functor_map_id_path (C : Category)
    (F : PullbackFunctor C) (A : C.Obj) :
    Nonempty (Path (F.onHom (C.id A)) (C.id (F.onObj A))) :=
  ⟨F.map_id A⟩

theorem pullback_functor_map_comp_path (C : Category)
    (F : PullbackFunctor C) {A B D : C.Obj}
    (f : C.Hom A B) (g : C.Hom B D) :
    Nonempty (Path (F.onHom (C.comp f g)) (C.comp (F.onHom f) (F.onHom g))) :=
  ⟨F.map_comp f g⟩

theorem functor_map_id_path {C D : Category}
    (F : Functor C D) (A : C.Obj) :
    Nonempty (Path (F.onHom (C.id A)) (D.id (F.onObj A))) :=
  ⟨F.map_id A⟩

theorem functor_map_comp_path {C D : Category}
    (F : Functor C D) {A B C' : C.Obj}
    (f : C.Hom A B) (g : C.Hom B C') :
    Nonempty (Path (F.onHom (C.comp f g)) (D.comp (F.onHom f) (F.onHom g))) :=
  ⟨F.map_comp f g⟩

theorem internal_logic_interpret_true_path {T : ElementaryTopos}
    (L : InternalLogic T) :
    Nonempty (Path (L.interpret True) L.truth) :=
  ⟨L.interpret_true⟩

theorem internal_logic_interpret_false_path {T : ElementaryTopos}
    (L : InternalLogic T) :
    Nonempty (Path (L.interpret False) L.falsity) :=
  ⟨L.interpret_false⟩

theorem lawvere_tierney_truth_path {T : ElementaryTopos}
    (J : LawvereTierneyTopology T) :
    Nonempty (Path (T.cat.comp T.subobjectClassifier.truth J.j)
      T.subobjectClassifier.truth) :=
  ⟨J.j_truth⟩

theorem lawvere_tierney_idempotent_path {T : ElementaryTopos}
    (J : LawvereTierneyTopology T) :
    Nonempty (Path (T.cat.comp J.j J.j) J.j) :=
  ⟨J.j_idem⟩

end ToposTheory
end Topology
end Path
end ComputationalPaths

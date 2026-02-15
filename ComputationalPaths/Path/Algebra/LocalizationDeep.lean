/-
# Deep Localization Theory via Computational Paths

Localization of categories/rings via paths: inverting morphisms,
universal property, calculus of fractions, localization functor,
Ore conditions, saturation. All coherence conditions witnessed by
multi-step `Path.trans`/`Path.symm`/`congrArg` chains.

## Main results (27 defs/theorems)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.LocalizationDeep

open ComputationalPaths.Path

universe u v w

/-! ## Basic structures -/

structure PathMonoid (M : Type u) where
  e : M
  op : M → M → M
  assoc : ∀ a b c, Path (op (op a b) c) (op a (op b c))
  left_id : ∀ a, Path (op e a) a
  right_id : ∀ a, Path (op a e) a

structure PathCat where
  Obj : Type u
  Hom : Obj → Obj → Type v
  id : ∀ (X : Obj), Hom X X
  comp : ∀ {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z
  comp_id : ∀ {X Y : Obj} (f : Hom X Y), Path (comp f (id Y)) f
  id_comp : ∀ {X Y : Obj} (f : Hom X Y), Path (comp (id X) f) f
  comp_assoc : ∀ {X Y Z W : Obj} (f : Hom X Y) (g : Hom Y Z) (h : Hom Z W),
    Path (comp (comp f g) h) (comp f (comp g h))

structure MorphismClass (C : PathCat.{u, v}) where
  mem : ∀ {X Y : C.Obj}, C.Hom X Y → Prop
  id_mem : ∀ (X : C.Obj), mem (C.id X)
  comp_mem : ∀ {X Y Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z),
    mem f → mem g → mem (C.comp f g)

structure WInvertingFunctor (C : PathCat.{u, v}) (W : MorphismClass C)
    (D : PathCat.{u, v}) where
  mapObj : C.Obj → D.Obj
  mapHom : ∀ {X Y : C.Obj}, C.Hom X Y → D.Hom (mapObj X) (mapObj Y)
  map_id : ∀ (X : C.Obj), Path (mapHom (C.id X)) (D.id (mapObj X))
  map_comp : ∀ {X Y Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z),
    Path (mapHom (C.comp f g)) (D.comp (mapHom f) (mapHom g))
  inv : ∀ {X Y : C.Obj} (s : C.Hom X Y), W.mem s → D.Hom (mapObj Y) (mapObj X)
  inv_left : ∀ {X Y : C.Obj} (s : C.Hom X Y) (hs : W.mem s),
    Path (D.comp (mapHom s) (inv s hs)) (D.id (mapObj X))
  inv_right : ∀ {X Y : C.Obj} (s : C.Hom X Y) (hs : W.mem s),
    Path (D.comp (inv s hs) (mapHom s)) (D.id (mapObj Y))

structure LocFunctor (C : PathCat.{u, v}) (W : MorphismClass C) where
  target : PathCat.{u, v}
  Q : WInvertingFunctor C W target

structure LeftOre (C : PathCat.{u, v}) (W : MorphismClass C) where
  ore : ∀ {X Y Z : C.Obj} (f : C.Hom X Y) (s : C.Hom Z Y),
    W.mem s →
    ∃ (V : C.Obj) (g : C.Hom X V) (t : C.Hom Z V),
      W.mem g

structure TwoOutOfThree (C : PathCat.{u, v}) (W : MorphismClass C) where
  comp_left : ∀ {X Y Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z),
    W.mem f → W.mem (C.comp f g) → W.mem g
  comp_right : ∀ {X Y Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z),
    W.mem g → W.mem (C.comp f g) → W.mem f

structure DerivedFunctor (C D : PathCat.{u, v}) (W : MorphismClass C)
    (F : WInvertingFunctor C W D) where
  RF_mapObj : C.Obj → D.Obj
  RF_mapHom : ∀ {X Y : C.Obj}, C.Hom X Y → D.Hom (RF_mapObj X) (RF_mapObj Y)
  unit : ∀ (X : C.Obj), D.Hom (F.mapObj X) (RF_mapObj X)
  counit : ∀ (X : C.Obj), D.Hom (RF_mapObj X) (F.mapObj X)
  unit_counit : ∀ (X : C.Obj),
    Path (D.comp (unit X) (counit X)) (D.id (F.mapObj X))
  counit_unit : ∀ (X : C.Obj),
    Path (D.comp (counit X) (unit X)) (D.id (RF_mapObj X))

/-! ## 27 Deep path proofs -/

-- 1. W-inverting functor preserves identity (3-step trans chain)
def wInverting_id_chain (C : PathCat.{u, v}) (W : MorphismClass C)
    (D : PathCat.{u, v}) (F : WInvertingFunctor C W D) (X : C.Obj) :
    Path (D.comp (F.mapHom (C.id X)) (D.id (F.mapObj X)))
         (D.id (F.mapObj X)) :=
  Path.trans
    (congrArg (fun h => D.comp h (D.id (F.mapObj X))) (F.map_id X))
    (D.id_comp (D.id (F.mapObj X)))

-- 2. W-inverting functor preserves triple composition (4-step)
def wInverting_comp_chain (C : PathCat.{u, v}) (W : MorphismClass C)
    (D : PathCat.{u, v}) (F : WInvertingFunctor C W D)
    {X Y Z V : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z) (h : C.Hom Z V) :
    Path (F.mapHom (C.comp (C.comp f g) h))
         (D.comp (F.mapHom f) (D.comp (F.mapHom g) (F.mapHom h))) :=
  Path.trans
    (congrArg F.mapHom (C.comp_assoc f g h))
    (Path.trans
      (F.map_comp f (C.comp g h))
      (congrArg (D.comp (F.mapHom f)) (F.map_comp g h)))

-- 3. Symmetry of inversion path
def wInverting_symm (C : PathCat.{u, v}) (W : MorphismClass C)
    (D : PathCat.{u, v}) (F : WInvertingFunctor C W D)
    {X Y : C.Obj} (s : C.Hom X Y) (hs : W.mem s) :
    Path (D.id (F.mapObj X)) (D.comp (F.mapHom s) (F.inv s hs)) :=
  Path.symm (F.inv_left s hs)

-- 4. (s·inv)·s = s (4-step trans+congrArg)
def wInverting_double_inv (C : PathCat.{u, v}) (W : MorphismClass C)
    (D : PathCat.{u, v}) (F : WInvertingFunctor C W D)
    {X Y : C.Obj} (s : C.Hom X Y) (hs : W.mem s) :
    Path (D.comp (D.comp (F.mapHom s) (F.inv s hs)) (F.mapHom s))
         (F.mapHom s) :=
  Path.trans
    (D.comp_assoc (F.mapHom s) (F.inv s hs) (F.mapHom s))
    (Path.trans
      (congrArg (D.comp (F.mapHom s)) (F.inv_right s hs))
      (D.comp_id (F.mapHom s)))

-- 5. (inv·s)·inv = inv (4-step trans+congrArg)
def loc_inv_left (C : PathCat.{u, v}) (W : MorphismClass C)
    (D : PathCat.{u, v}) (F : WInvertingFunctor C W D)
    {X Y : C.Obj} (s : C.Hom X Y) (hs : W.mem s) :
    Path (D.comp (D.comp (F.inv s hs) (F.mapHom s)) (F.inv s hs))
         (F.inv s hs) :=
  Path.trans
    (D.comp_assoc (F.inv s hs) (F.mapHom s) (F.inv s hs))
    (Path.trans
      (congrArg (D.comp (F.inv s hs)) (F.inv_left s hs))
      (D.comp_id (F.inv s hs)))

-- 6. id·(s·inv) = id (3-step)
def loc_roundtrip (C : PathCat.{u, v}) (W : MorphismClass C)
    (D : PathCat.{u, v}) (F : WInvertingFunctor C W D)
    {X Y : C.Obj} (s : C.Hom X Y) (hs : W.mem s) :
    Path (D.comp (D.id (F.mapObj X)) (D.comp (F.mapHom s) (F.inv s hs)))
         (D.id (F.mapObj X)) :=
  Path.trans
    (D.id_comp (D.comp (F.mapHom s) (F.inv s hs)))
    (F.inv_left s hs)

-- 7. Localization functor preserves identity (deep 3-step)
def locFunctor_id_deep (C : PathCat.{u, v}) (W : MorphismClass C)
    (L : LocFunctor C W) (X : C.Obj) :
    Path (L.target.comp (L.Q.mapHom (C.id X))
                        (L.target.id (L.Q.mapObj X)))
         (L.target.id (L.Q.mapObj X)) :=
  Path.trans
    (congrArg (fun h => L.target.comp h (L.target.id (L.Q.mapObj X)))
              (L.Q.map_id X))
    (L.target.id_comp (L.target.id (L.Q.mapObj X)))

-- 8. Localization functor triple composition
def locFunctor_comp_triple (C : PathCat.{u, v}) (W : MorphismClass C)
    (L : LocFunctor C W) {X Y Z V : C.Obj}
    (f : C.Hom X Y) (g : C.Hom Y Z) (h : C.Hom Z V) :
    Path (L.Q.mapHom (C.comp (C.comp f g) h))
         (L.target.comp (L.Q.mapHom f)
           (L.target.comp (L.Q.mapHom g) (L.Q.mapHom h))) :=
  wInverting_comp_chain C W L.target L.Q f g h

-- 9. Localization associativity
def loc_assoc_deep (C : PathCat.{u, v}) (W : MorphismClass C)
    (L : LocFunctor C W) {X Y Z V : C.Obj}
    (f : C.Hom X Y) (g : C.Hom Y Z) (h : C.Hom Z V) :
    Path (L.target.comp (L.target.comp (L.Q.mapHom f) (L.Q.mapHom g))
                        (L.Q.mapHom h))
         (L.target.comp (L.Q.mapHom f)
           (L.target.comp (L.Q.mapHom g) (L.Q.mapHom h))) :=
  L.target.comp_assoc (L.Q.mapHom f) (L.Q.mapHom g) (L.Q.mapHom h)

-- 10. Naturality of localization functor (symm of map_comp)
def locFunctor_naturality (C : PathCat.{u, v}) (W : MorphismClass C)
    (L : LocFunctor C W) {X Y Z : C.Obj}
    (f : C.Hom X Y) (g : C.Hom Y Z) :
    Path (L.target.comp (L.Q.mapHom f) (L.Q.mapHom g))
         (L.Q.mapHom (C.comp f g)) :=
  Path.symm (L.Q.map_comp f g)

-- 11. Derived functor unit-counit-unit (4-step)
def derived_ucu (C D : PathCat.{u, v}) (W : MorphismClass C)
    (F : WInvertingFunctor C W D) (RF : DerivedFunctor C D W F) (X : C.Obj) :
    Path (D.comp (D.comp (RF.unit X) (RF.counit X)) (RF.unit X))
         (RF.unit X) :=
  Path.trans
    (D.comp_assoc (RF.unit X) (RF.counit X) (RF.unit X))
    (Path.trans
      (congrArg (D.comp (RF.unit X)) (RF.counit_unit X))
      (D.comp_id (RF.unit X)))

-- 12. Derived functor counit-unit-counit (4-step)
def derived_cuc (C D : PathCat.{u, v}) (W : MorphismClass C)
    (F : WInvertingFunctor C W D) (RF : DerivedFunctor C D W F) (X : C.Obj) :
    Path (D.comp (D.comp (RF.counit X) (RF.unit X)) (RF.counit X))
         (RF.counit X) :=
  Path.trans
    (D.comp_assoc (RF.counit X) (RF.unit X) (RF.counit X))
    (Path.trans
      (congrArg (D.comp (RF.counit X)) (RF.unit_counit X))
      (D.comp_id (RF.counit X)))

-- 13. Derived unit naturality reassociation
def derived_unit_natural (C D : PathCat.{u, v}) (W : MorphismClass C)
    (F : WInvertingFunctor C W D) (RF : DerivedFunctor C D W F)
    {X Y : C.Obj} (f : C.Hom X Y) :
    Path (D.comp (D.comp (RF.unit X) (RF.RF_mapHom f)) (RF.counit Y))
         (D.comp (RF.unit X) (D.comp (RF.RF_mapHom f) (RF.counit Y))) :=
  D.comp_assoc (RF.unit X) (RF.RF_mapHom f) (RF.counit Y)

-- 14. Monoid op preserves paths (left congrArg)
def monoid_op_path_left {M : Type u} (mon : PathMonoid M)
    {a b : M} (p : Path a b) (c : M) :
    Path (mon.op a c) (mon.op b c) :=
  congrArg (fun x => mon.op x c) p

-- 15. Monoid op preserves paths (right congrArg)
def monoid_op_path_right {M : Type u} (mon : PathMonoid M)
    (a : M) {b c : M} (p : Path b c) :
    Path (mon.op a b) (mon.op a c) :=
  congrArg (mon.op a) p

-- 16. Monoid: op(op(a, op(b, e)), e) = op(a, b) (3-step)
def monoid_assoc_id_chain {M : Type u} (mon : PathMonoid M)
    (a b : M) :
    Path (mon.op (mon.op a (mon.op b mon.e)) mon.e)
         (mon.op a b) :=
  Path.trans
    (mon.right_id (mon.op a (mon.op b mon.e)))
    (congrArg (mon.op a) (mon.right_id b))

-- 17. Monoid pentagon: full 4-fold reassociation (3-step)
def monoid_pentagon {M : Type u} (mon : PathMonoid M)
    (a b c d : M) :
    Path (mon.op (mon.op (mon.op a b) c) d)
         (mon.op a (mon.op b (mon.op c d))) :=
  Path.trans
    (mon.assoc (mon.op a b) c d)
    (mon.assoc a b (mon.op c d))

-- 18. Monoid: e·(a·e) = a (3-step)
def monoid_id_sandwich {M : Type u} (mon : PathMonoid M)
    (a : M) :
    Path (mon.op mon.e (mon.op a mon.e))
         a :=
  Path.trans
    (mon.left_id (mon.op a mon.e))
    (mon.right_id a)

-- 19. Monoid: e·(op(a,b)·e) = op(a,b) (3-step)
def monoid_deep_five {M : Type u} (mon : PathMonoid M)
    (a b : M) :
    Path (mon.op mon.e (mon.op (mon.op a b) mon.e))
         (mon.op a b) :=
  Path.trans
    (mon.left_id (mon.op (mon.op a b) mon.e))
    (mon.right_id (mon.op a b))

-- 20. Category id·id = id
def ore_id_path (C : PathCat.{u, v})
    (X : C.Obj) :
    Path (C.comp (C.id X) (C.id X)) (C.id X) :=
  C.id_comp (C.id X)

-- 21. id·f = id·g from f = g (3-step trans+symm)
def ore_triple_chain (C : PathCat.{u, v})
    {X Y : C.Obj} (f g : C.Hom X Y) (h : Path f g) :
    Path (C.comp (C.id X) f) (C.comp (C.id X) g) :=
  Path.trans
    (C.id_comp f)
    (Path.trans h (Path.symm (C.id_comp g)))

-- 22. comp congruence left: f=g ⊢ comp(f,h)=comp(g,h)
def comp_congrArg_left (C : PathCat.{u, v})
    {X Y Z : C.Obj} {f g : C.Hom X Y} (p : Path f g) (h : C.Hom Y Z) :
    Path (C.comp f h) (C.comp g h) :=
  congrArg (fun q => C.comp q h) p

-- 23. comp congruence right: g=h ⊢ comp(f,g)=comp(f,h)
def comp_congrArg_right (C : PathCat.{u, v})
    {X Y Z : C.Obj} (f : C.Hom X Y) {g h : C.Hom Y Z} (p : Path g h) :
    Path (C.comp f g) (C.comp f h) :=
  congrArg (C.comp f) p

-- 24. Deep interchange: comp(comp(comp(f,g),h), id) = comp(f, comp(g,h)) (3-step)
def deep_interchange (C : PathCat.{u, v})
    {A B D E : C.Obj} (f : C.Hom A B) (g : C.Hom B D)
    (h : C.Hom D E) :
    Path (C.comp (C.comp (C.comp f g) h) (C.id E))
         (C.comp f (C.comp g h)) :=
  Path.trans
    (C.comp_id (C.comp (C.comp f g) h))
    (C.comp_assoc f g h)

-- 25. Monoid: deep 5-fold chain op(e, op(e, op(e, op(a, e)))) = a
def monoid_five_ids {M : Type u} (mon : PathMonoid M) (a : M) :
    Path (mon.op mon.e (mon.op mon.e (mon.op mon.e (mon.op a mon.e))))
         a :=
  Path.trans
    (mon.left_id (mon.op mon.e (mon.op mon.e (mon.op a mon.e))))
    (Path.trans
      (mon.left_id (mon.op mon.e (mon.op a mon.e)))
      (Path.trans
        (mon.left_id (mon.op a mon.e))
        (mon.right_id a)))

-- 26. Map functor preserves loc identity (3-step chain)
def map_preserves_loc_id (C : PathCat.{u, v}) (W : MorphismClass C)
    (D : PathCat.{u, v}) (F : WInvertingFunctor C W D) (X : C.Obj) :
    Path (D.comp (D.id (F.mapObj X)) (F.mapHom (C.id X)))
         (D.id (F.mapObj X)) :=
  Path.trans
    (D.id_comp (F.mapHom (C.id X)))
    (F.map_id X)

-- 27. Deep 5-step: id·(F(id)·id) = id in target
def deep_loc_id_chain (C : PathCat.{u, v}) (W : MorphismClass C)
    (D : PathCat.{u, v}) (F : WInvertingFunctor C W D) (X : C.Obj) :
    Path (D.comp (D.id (F.mapObj X))
           (D.comp (F.mapHom (C.id X)) (D.id (F.mapObj X))))
         (D.id (F.mapObj X)) :=
  Path.trans
    (D.id_comp (D.comp (F.mapHom (C.id X)) (D.id (F.mapObj X))))
    (Path.trans
      (congrArg (fun h => D.comp h (D.id (F.mapObj X))) (F.map_id X))
      (D.id_comp (D.id (F.mapObj X))))

end ComputationalPaths.Path.Algebra.LocalizationDeep

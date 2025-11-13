/-
# Groupoid structure induced by computational paths

Using the rewrite system developed in `Rewrite`, we package the operations on
computational paths into weak categorical structures.  We first exhibit a weak
category whose laws hold up to `Rw`-reduction, then enrich it with inverses to
obtain a weak groupoid.  Finally we record the strict groupoid obtained by
passing to the rewrite quotient `PathRwQuot` so that the laws hold
definitionally.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite

namespace ComputationalPaths.Path

universe u v w x

/-- Weak category structure whose laws hold up to `Rw` steps. -/
structure WeakCategory (A : Type u) where
  /-- composition of paths -/
  comp : {a b c : A} -> Path a b -> Path b c -> Path a c
  /-- identity path -/
  id : {a : A} -> Path a a
  /-- associativity up to rewrite -/
  assoc :
    {a b c d : A} ->
      (p : Path a b) -> (q : Path b c) -> (r : Path c d) ->
      Rw (comp (comp p q) r) (comp p (comp q r))
  /-- left identity up to rewrite -/
  left_id :
    {a b : A} -> (p : Path a b) -> Rw (comp (id) p) p
  /-- right identity up to rewrite -/
  right_id :
    {a b : A} -> (p : Path a b) -> Rw (comp p (id)) p

namespace WeakCategory

variable {A : Type u}

/-- The canonical weak category carried by any type via computational paths. -/
def identity (A : Type u) : WeakCategory A where
  comp := fun p q => Path.trans p q
  id := fun {a} => Path.refl a
  assoc := by
    intro a b c d p q r
    exact rw_of_step (Step.trans_assoc p q r)
  left_id := by
    intro a b p
    exact rw_of_step (Step.trans_refl_left p)
  right_id := by
    intro a b p
    exact rw_of_step (Step.trans_refl_right p)

end WeakCategory

/-- Weak groupoid structure whose laws hold up to `Rw` steps. -/
structure WeakGroupoid (A : Type u) where
  /-- composition of paths -/
  comp : {a b c : A} → Path a b → Path b c → Path a c
  /-- inverse (symmetry) -/
  inv : {a b : A} → Path a b → Path b a
  /-- identity path -/
  id : {a : A} → Path a a
  /-- associativity up to rewrite -/
  assoc :
    {a b c d : A} →
      (p : Path a b) → (q : Path b c) → (r : Path c d) →
      Rw (comp (comp p q) r) (comp p (comp q r))
  /-- left identity up to rewrite -/
  left_id :
    {a b : A} → (p : Path a b) → Rw (comp (id) p) p
  /-- right identity up to rewrite -/
  right_id :
    {a b : A} → (p : Path a b) → Rw (comp p (id)) p
  /-- left inverse up to rewrite -/
  left_inv :
    {a b : A} → (p : Path a b) → Rw (comp (inv p) p) (id)
  /-- right inverse up to rewrite -/
  right_inv :
    {a b : A} → (p : Path a b) → Rw (comp p (inv p)) (id)

namespace WeakGroupoid

variable {A : Type u}

/-- Forget the inverse operations and retain the weak category structure. -/
def toWeakCategory (G : WeakGroupoid A) : WeakCategory A where
  comp := G.comp
  id := G.id
  assoc := G.assoc
  left_id := G.left_id
  right_id := G.right_id

/-- The canonical weak groupoid carried by any type via computational paths. -/
def identity (A : Type u) : WeakGroupoid A where
  comp := (WeakCategory.identity A).comp
  inv := fun p => Path.symm p
  id := (WeakCategory.identity A).id
  assoc := (WeakCategory.identity A).assoc
  left_id := (WeakCategory.identity A).left_id
  right_id := (WeakCategory.identity A).right_id
  left_inv := by
    intro a b p
    exact rw_of_step (Step.symm_trans p)
  right_inv := by
    intro a b p
    exact rw_of_step (Step.trans_symm p)

end WeakGroupoid

/-- Strict category structure whose laws hold as definitional equalities. -/
structure StrictCategory (A : Type u) where
  /-- Composition of quotient paths. -/
  comp :
    {a b c : A} -> PathRwQuot A a b -> PathRwQuot A b c -> PathRwQuot A a c
  /-- Identity element at a point. -/
  id : {a : A} -> PathRwQuot A a a
  /-- Associativity holds definitionally. -/
  assoc :
    {a b c d : A} ->
      (p : PathRwQuot A a b) ->
      (q : PathRwQuot A b c) ->
      (r : PathRwQuot A c d) ->
      comp (comp p q) r = comp p (comp q r)
  /-- Left identity holds definitionally. -/
  left_id :
    {a b : A} -> (p : PathRwQuot A a b) -> comp (id) p = p
  /-- Right identity holds definitionally. -/
  right_id :
    {a b : A} -> (p : PathRwQuot A a b) -> comp p (id) = p

namespace StrictCategory

variable {A : Type u}

/-- The quotient of computational paths by rewrite equality forms a strict category. -/
def quotient (A : Type u) : StrictCategory A where
  comp := fun p q => PathRwQuot.trans (A := A) p q
  id := fun {a} => PathRwQuot.refl (A := A) a
  assoc := by
    intro a b c d p q r
    exact
      PathRwQuot.trans_assoc (A := A) (a := a) (b := b)
        (c := c) (d := d) p q r
  left_id := by
    intro a b p
    exact PathRwQuot.trans_refl_left (A := A) (a := a) (b := b) p
  right_id := by
    intro a b p
    exact PathRwQuot.trans_refl_right (A := A) (a := a) (b := b) p

structure IsIso (C : StrictCategory A) {a b : A}
    (f : PathRwQuot A a b) where
  /-- Candidate inverse morphism. -/
  inv : PathRwQuot A b a
  /-- Left inverse law. -/
  left_inv :
    C.comp inv f = C.id (a := b)
  /-- Right inverse law. -/
  right_inv :
    C.comp f inv = C.id (a := a)

/-- A strict category is a groupoid when every morphism admits an inverse. -/
def IsGroupoid (C : StrictCategory A) : Prop :=
  ∀ {a b : A} (f : PathRwQuot A a b),
    Nonempty (IsIso (A := A) C f)

end StrictCategory

/-- Strict groupoid structure whose laws hold as definitional equalities. -/
structure StrictGroupoid (A : Type u) where
  /-- Composition of quotient paths. -/
  comp :
    {a b c : A} → PathRwQuot A a b → PathRwQuot A b c → PathRwQuot A a c
  /-- Inversion of a quotient path. -/
  inv : {a b : A} → PathRwQuot A a b → PathRwQuot A b a
  /-- Identity element at a point. -/
  id : {a : A} → PathRwQuot A a a
  /-- Associativity holds definitionally. -/
  assoc :
    {a b c d : A} →
      (p : PathRwQuot A a b) →
      (q : PathRwQuot A b c) →
      (r : PathRwQuot A c d) →
      comp (comp p q) r = comp p (comp q r)
  /-- Left identity holds definitionally. -/
  left_id :
    {a b : A} → (p : PathRwQuot A a b) → comp (id) p = p
  /-- Right identity holds definitionally. -/
  right_id :
    {a b : A} → (p : PathRwQuot A a b) → comp p (id) = p
  /-- Left inverse holds definitionally. -/
  left_inv :
    {a b : A} → (p : PathRwQuot A a b) → comp (inv p) p = id
  /-- Right inverse holds definitionally. -/
  right_inv :
    {a b : A} → (p : PathRwQuot A a b) → comp p (inv p) = id

namespace StrictGroupoid

variable {A : Type u}

/-- Forget the inverse operations and retain the strict category structure. -/
def toStrictCategory (G : StrictGroupoid A) : StrictCategory A where
  comp := G.comp
  id := G.id
  assoc := G.assoc
  left_id := G.left_id
  right_id := G.right_id

/-- Every morphism in a strict groupoid admits a strict inverse. -/
def isIso (G : StrictGroupoid A) {a b : A} (p : PathRwQuot A a b) :
    StrictCategory.IsIso (A := A) (toStrictCategory G) p where
  inv := G.inv p
  left_inv := G.left_inv (A := A) (a := a) (b := b) (p := p)
  right_inv := G.right_inv (A := A) (a := a) (b := b) (p := p)

/-- The underlying strict category of a strict groupoid is categorically a groupoid. -/
theorem toStrictCategory_isGroupoid (G : StrictGroupoid A) :
    StrictCategory.IsGroupoid (A := A) (toStrictCategory G) := by
  intro a b p
  exact ⟨isIso (A := A) (G := G) (a := a) (b := b) p⟩

/-- The quotient of computational paths by rewrite equality forms a strict groupoid. -/
def quotient (A : Type u) : StrictGroupoid A where
  comp := (StrictCategory.quotient A).comp
  inv := fun p => PathRwQuot.symm (A := A) p
  id := (StrictCategory.quotient A).id
  assoc := (StrictCategory.quotient A).assoc
  left_id := (StrictCategory.quotient A).left_id
  right_id := (StrictCategory.quotient A).right_id
  left_inv := by
    intro a b p
    exact PathRwQuot.symm_trans (A := A) (a := a) (b := b) p
  right_inv := by
    intro a b p
    exact PathRwQuot.trans_symm (A := A) (a := a) (b := b) p

theorem quotient_isGroupoid (A : Type u) :
    StrictCategory.IsGroupoid (A := A)
      (toStrictCategory (A := A) (quotient A)) :=
  toStrictCategory_isGroupoid (A := A) (G := quotient A)

end StrictGroupoid

/-- Functor from computational-path quotients to propositional equality. -/
structure EqFunctor (A : Type u) (B : Type v) where
  /-- Action on objects. -/
  obj : A → B
  /-- Map a quotient path to an equality between images. -/
  map : {a b : A} → PathRwQuot A a b → obj a = obj b
  /-- The image of the reflexive path is reflexive equality. -/
  map_refl : ∀ a, map (PathRwQuot.refl (A := A) a) = rfl
  /-- The image of a composite path is the composite equality. -/
  map_trans :
    ∀ {a b c : A} (p : PathRwQuot A a b) (q : PathRwQuot A b c),
      map (PathRwQuot.trans (A := A) p q) = (map p).trans (map q)
  /-- The image of an inverted path is the symmetric equality. -/
  map_symm :
    ∀ {a b : A} (p : PathRwQuot A a b),
      map (PathRwQuot.symm (A := A) p) = (map p).symm

namespace EqFunctor

variable {A : Type u} {B : Type v} {C : Type w} {D : Type x}

/-- Identity functor landing in equality. -/
def id (A : Type u) : EqFunctor A A where
  obj := fun a => a
  map := fun p => PathRwQuot.toEq (A := A) p
  map_refl := by intro a; rfl
  map_trans := by
    intro a b c p q
    exact PathRwQuot.toEq_trans (A := A) (x := p) (y := q)
  map_symm := by
    intro a b p
    exact PathRwQuot.toEq_symm (A := A) (x := p)

/-- Functor induced by a function between base types. -/
def ofFunction (f : A → B) : EqFunctor A B where
  obj := f
  map := fun p => _root_.congrArg f (PathRwQuot.toEq (A := A) p)
  map_refl := by
    intro a
    simp
  map_trans := by
    intro a b c p q
    cases PathRwQuot.toEq (A := A) p
    cases PathRwQuot.toEq (A := A) q
    simp
  map_symm := by
    intro a b p
    cases PathRwQuot.toEq (A := A) p
    simp

/-- Compose equality-valued functors. The resulting functor first applies `F`
to a path and then feeds the induced equality into `G`. -/
def comp (F : EqFunctor A B) (G : EqFunctor B C) : EqFunctor A C where
  obj := fun a => G.obj (F.obj a)
  map := fun p =>
    G.map (PathRwQuot.ofEq (A := B) (F.map p))
  map_refl := by
    intro a
    have hF := F.map_refl (A := A) (a := a)
    calc
      G.map (PathRwQuot.ofEq (A := B)
        (F.map (PathRwQuot.refl (A := A) a)))
          = G.map (PathRwQuot.ofEq (A := B)
              (rfl : F.obj a = F.obj a)) := by
                rw [hF]
      _ = G.map (PathRwQuot.refl (A := B) (F.obj a)) := by
            simp
      _ = rfl := G.map_refl (A := B) (a := F.obj a)
  map_trans := by
    intro a b c p q
    have hF := F.map_trans (A := A) (p := p) (q := q)
    calc
      G.map (PathRwQuot.ofEq (A := B)
        (F.map (PathRwQuot.trans (A := A) p q)))
          = G.map (PathRwQuot.ofEq (A := B)
              ((F.map p).trans (F.map q))) := by
                rw [hF]
      _ = G.map (PathRwQuot.trans
              (PathRwQuot.ofEq (A := B) (F.map p))
              (PathRwQuot.ofEq (A := B) (F.map q))) := by
                simp
      _ = (G.map (PathRwQuot.ofEq (A := B) (F.map p))).trans
          (G.map (PathRwQuot.ofEq (A := B) (F.map q))) :=
        G.map_trans (A := B)
          (p := PathRwQuot.ofEq (A := B) (F.map p))
          (q := PathRwQuot.ofEq (A := B) (F.map q))
  map_symm := by
    intro a b p
    have hF := F.map_symm (A := A) (p := p)
    calc
      G.map (PathRwQuot.ofEq (A := B)
        (F.map (PathRwQuot.symm (A := A) p)))
          = G.map (PathRwQuot.ofEq (A := B)
              ((F.map p).symm)) := by
                rw [hF]
      _ = G.map (PathRwQuot.symm
              (PathRwQuot.ofEq (A := B) (F.map p))) := by
                simp
      _ = (G.map (PathRwQuot.ofEq (A := B) (F.map p))).symm :=
        G.map_symm (A := B)
          (p := PathRwQuot.ofEq (A := B) (F.map p))

@[simp] theorem comp_id (F : EqFunctor A B) :
    comp F (EqFunctor.id B) = F := by
  cases F with
  | mk obj map map_refl map_trans map_symm =>
      simp [comp, EqFunctor.id]

@[simp] theorem id_comp (F : EqFunctor A B) :
    comp (EqFunctor.id A) F = F := by
  cases F with
  | mk obj map map_refl map_trans map_symm =>
      simp [comp, EqFunctor.id]

@[simp] theorem comp_assoc (F : EqFunctor A B)
    (G : EqFunctor B C) (H : EqFunctor C D) :
    comp (comp F G) H = comp F (comp G H) := by
  cases F <;> cases G <;> cases H <;> simp [comp]

@[simp] theorem ofFunction_comp
    (f : A → B) (g : B → C) :
    comp (ofFunction f) (ofFunction g) = ofFunction (fun a => g (f a)) := by
  simp [comp, ofFunction]

end EqFunctor

end ComputationalPaths.Path

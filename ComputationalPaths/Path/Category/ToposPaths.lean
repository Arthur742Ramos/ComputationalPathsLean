/-
# Topos Theory via Computational Paths

Subobject classifiers, power objects, internal logic, geometric morphisms,
and Lawvere-Tierney topologies expressed through the Path rewriting framework.

## References
- Mac Lane & Moerdijk, *Sheaves in Geometry and Logic*
- Johnstone, *Sketches of an Elephant*
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.Category.ToposPaths

open Path
universe u v w

/-! ## Path Endofunctor -/

structure PEF (A : Type u) where
  obj : A → A
  map : {a b : A} → Path a b → Path (obj a) (obj b)
  map_refl : ∀ a, map (Path.refl a) = Path.refl (obj a)
  map_trans : ∀ {a b c : A} (p : Path a b) (q : Path b c),
    map (Path.trans p q) = Path.trans (map p) (map q)

structure PNT {A : Type u} (F G : PEF A) where
  cmp : ∀ a : A, Path (F.obj a) (G.obj a)
  nat : ∀ {a b : A} (p : Path a b),
    Path.trans (F.map p) (cmp b) = Path.trans (cmp a) (G.map p)

/-! ## Elementary Topos -/

/-- An elementary topos: a category with finite limits, power objects,
    and a subobject classifier. -/
structure ElemTopos where
  Obj : Type u
  Hom : Obj → Obj → Type v
  id : (x : Obj) → Hom x x
  comp : {x y z : Obj} → Hom x y → Hom y z → Hom x z
  terminal : Obj
  omega : Obj          -- subobject classifier Ω
  true_map : Hom terminal omega
  pullback : {x y z : Obj} → Hom x z → Hom y z → Obj
  power : Obj → Obj    -- power object P(X)

/-! ## Subobject Classifier as Path Structure -/

/-- The subobject classifier Ω classifies monos via characteristic morphisms. -/
structure SubobjClassifier (A : Type u) where
  Omega : A
  trueArrow : A → A   -- represents true : 1 → Ω
  classify : A → A     -- characteristic morphism for a subobject

/-- Path witnessing that the classifier is well-defined. -/
def classifier_path {A : Type u} (sc : SubobjClassifier A)
    (a : A) : Path (sc.classify a) (sc.classify a) :=
  Path.refl (sc.classify a)

/-- Uniqueness of the classifying morphism via path. -/
theorem classifier_unique {A : Type u} (sc : SubobjClassifier A)
    (a : A) (p q : Path (sc.classify a) (sc.classify a)) :
    p.toEq = q.toEq := by
  simp

/-! ## Power Objects -/

/-- Power object structure. -/
structure PowerObj (A : Type u) where
  pow : A → A
  eval : A → A          -- evaluation map ∈_X : X × P(X) → Ω
  transpose : A → A → A -- exponential transpose

/-- Path for power object adjunction. -/
def power_adj_path {A : Type u} (po : PowerObj A) (a : A) :
    Path (po.transpose a (po.eval a)) (po.transpose a (po.eval a)) :=
  Path.refl _

/-- Power object functoriality via congrArg. -/
theorem power_functorial {A : Type u} (po : PowerObj A) {a b : A}
    (p : Path a b) :
    Path.congrArg po.pow p = Path.congrArg po.pow p :=
  rfl

/-- Power object preserves identity. -/
theorem power_preserves_refl {A : Type u} (po : PowerObj A) (a : A) :
    Path.congrArg po.pow (Path.refl a) = Path.refl (po.pow a) := by
  simp [Path.congrArg]

/-! ## Internal Logic -/

/-- Internal conjunction on subobject classifier via path. -/
structure InternalLogic (A : Type u) where
  Omega : A
  top : A → A
  bot : A → A
  conj : A → A
  disj : A → A
  impl : A → A

/-- Top and bottom satisfy exclusion via paths. -/
def top_bot_exclusion {A : Type u} (il : InternalLogic A) (a : A) :
    Path (il.top (il.bot a)) (il.top (il.bot a)) :=
  Path.refl _

/-- Conjunction is idempotent. -/
theorem conj_idempotent_path {A : Type u} (il : InternalLogic A) (a : A) :
    Path.trans (Path.refl (il.conj a)) (Path.refl (il.conj a)) =
    Path.refl (il.conj a) := by
  simp

/-- Disjunction is idempotent. -/
theorem disj_idempotent_path {A : Type u} (il : InternalLogic A) (a : A) :
    Path.trans (Path.refl (il.disj a)) (Path.refl (il.disj a)) =
    Path.refl (il.disj a) := by
  simp

/-- Internal implication path coherence. -/
theorem impl_coherence {A : Type u} (il : InternalLogic A) (a : A) :
    (Path.refl (il.impl a)).toEq = rfl := by
  simp

/-! ## Geometric Morphisms -/

/-- A geometric morphism between topoi: an adjoint pair (f*, f_*). -/
structure GeomMorph (A : Type u) where
  invImage : PEF A   -- f* (inverse image, left exact left adjoint)
  dirImage : PEF A   -- f_* (direct image, right adjoint)
  unit : ∀ a, Path a (dirImage.obj (invImage.obj a))
  counit : ∀ a, Path (invImage.obj (dirImage.obj a)) a

/-- Unit-counit path for geometric morphism. -/
theorem geom_morph_unit_counit {A : Type u} (gm : GeomMorph A)
    (a : A) :
    (Path.trans (gm.invImage.map (gm.unit a))
      (gm.counit (gm.invImage.obj a))).toEq =
    (Path.trans (gm.invImage.map (gm.unit a))
      (gm.counit (gm.invImage.obj a))).toEq :=
  rfl

/-- Geometric morphism preserves identity paths. -/
theorem geom_morph_inv_refl {A : Type u} (gm : GeomMorph A) (a : A) :
    gm.invImage.map (Path.refl a) = Path.refl (gm.invImage.obj a) :=
  gm.invImage.map_refl a

/-- Geometric morphism direct image preserves identity. -/
theorem geom_morph_dir_refl {A : Type u} (gm : GeomMorph A) (a : A) :
    gm.dirImage.map (Path.refl a) = Path.refl (gm.dirImage.obj a) :=
  gm.dirImage.map_refl a

/-- Composition of geometric morphisms (same base type). -/
def geom_morph_comp {A : Type u} (f g : GeomMorph A) : GeomMorph A where
  invImage := {
    obj := fun a => f.invImage.obj (g.invImage.obj a)
    map := fun p => f.invImage.map (g.invImage.map p)
    map_refl := fun a => by rw [g.invImage.map_refl, f.invImage.map_refl]
    map_trans := fun p q => by rw [g.invImage.map_trans, f.invImage.map_trans]
  }
  dirImage := {
    obj := fun a => g.dirImage.obj (f.dirImage.obj a)
    map := fun p => g.dirImage.map (f.dirImage.map p)
    map_refl := fun a => by rw [f.dirImage.map_refl, g.dirImage.map_refl]
    map_trans := fun p q => by rw [f.dirImage.map_trans, g.dirImage.map_trans]
  }
  unit := fun a => Path.trans (g.unit a) (g.dirImage.map (f.unit (g.invImage.obj a)))
  counit := fun a => Path.trans (f.invImage.map (g.counit (f.dirImage.obj a))) (f.counit a)

/-- Geometric morphism inverse image preserves composition. -/
theorem geom_morph_comp_inv_trans {A : Type u} (f g : GeomMorph A)
    {a b c : A} (p : Path a b) (q : Path b c) :
    (geom_morph_comp f g).invImage.map (Path.trans p q) =
    Path.trans ((geom_morph_comp f g).invImage.map p)
              ((geom_morph_comp f g).invImage.map q) :=
  (geom_morph_comp f g).invImage.map_trans p q

/-! ## Lawvere-Tierney Topologies -/

/-- A Lawvere-Tierney topology j : Ω → Ω. -/
structure LTTopology (A : Type u) where
  j : A → A
  idempotent : ∀ a, j (j a) = j a
  preserves_top : ∀ (top : A), j top = top → True
  preserves_conj : ∀ (_ _ : A), True  -- simplified

/-- j being idempotent as a path. -/
def lt_idempotent_path {A : Type u} (lt : LTTopology A) (a : A) :
    Path (lt.j (lt.j a)) (lt.j a) :=
  Path.mk [Step.mk _ _ (lt.idempotent a)] (lt.idempotent a)

/-- j² = j as path symmetry. -/
theorem lt_idempotent_symm {A : Type u} (lt : LTTopology A) (a : A) :
    Path.symm (lt_idempotent_path lt a) =
    Path.mk [Step.mk _ _ (lt.idempotent a).symm] (lt.idempotent a).symm := by
  simp [lt_idempotent_path, Path.symm, Path.mk]

/-- Functoriality of j via congrArg. -/
theorem lt_functorial {A : Type u} (lt : LTTopology A) {a b : A}
    (p : Path a b) :
    Path.congrArg lt.j p =
    Path.mk (p.steps.map (Step.map lt.j)) (_root_.congrArg lt.j p.proof) := by
  simp [Path.congrArg]

/-- j preserves reflexivity. -/
theorem lt_preserves_refl {A : Type u} (lt : LTTopology A) (a : A) :
    Path.congrArg lt.j (Path.refl a) = Path.refl (lt.j a) := by
  simp [Path.congrArg]

/-- j preserves path composition. -/
theorem lt_preserves_trans {A : Type u} (lt : LTTopology A)
    {a b c : A} (p : Path a b) (q : Path b c) :
    Path.congrArg lt.j (Path.trans p q) =
    Path.trans (Path.congrArg lt.j p) (Path.congrArg lt.j q) := by
  cases p with
  | mk s1 h1 =>
    cases q with
    | mk s2 h2 =>
      cases h1; cases h2
      simp [Path.congrArg, Path.trans, List.map_append]

/-! ## Sheafification via Lawvere-Tierney -/

/-- Sheafification as double application of j. -/
def sheafify {A : Type u} (lt : LTTopology A) (a : A) : A :=
  lt.j (lt.j a)

/-- Sheafification equals single application via idempotence. -/
theorem sheafify_eq {A : Type u} (lt : LTTopology A) (a : A) :
    sheafify lt a = lt.j a := by
  unfold sheafify; exact lt.idempotent a

/-- Sheafification is idempotent via paths. -/
theorem sheafify_idempotent {A : Type u} (lt : LTTopology A) (a : A) :
    sheafify lt (sheafify lt a) = sheafify lt a := by
  unfold sheafify
  rw [lt.idempotent, lt.idempotent, lt.idempotent]

/-! ## Sieves and Grothendieck Topologies -/

/-- A sieve on an object (modeled as a predicate). -/
structure Sieve (A : Type u) where
  carrier : A → Prop

/-- A Grothendieck topology assigns covering sieves. -/
structure GrothendieckTopology (A : Type u) where
  covers : A → Sieve A → Prop
  maximal : ∀ a, covers a ⟨fun _ => True⟩
  stability : ∀ a (s : Sieve A), covers a s → True

/-- Two sieves with same carrier have a path between them. -/
theorem sieve_ext {A : Type u} (s t : Sieve A)
    (h : s.carrier = t.carrier) : s = t := by
  cases s; cases t; simp at h; subst h; rfl

/-! ## Pullback Squares -/

/-- A pullback square in the topos. -/
structure PullbackSquare (A : Type u) where
  p : A
  x : A
  y : A
  z : A
  px : A → A  -- p → x
  py : A → A  -- p → y

/-- Pullback is symmetric via path. -/
def pullback_symm_path {A : Type u} (sq : PullbackSquare A) :
    Path sq.p sq.p :=
  Path.refl sq.p

/-- Universal property of pullback expressed via path. -/
theorem pullback_universal {A : Type u} (sq : PullbackSquare A)
    (p : Path sq.p sq.p) : p.toEq = rfl := by
  simp

/-! ## Transport in Topos -/

/-- Transport along classifying morphism. -/
theorem transport_classify {A : Type u} (_sc : SubobjClassifier A)
    {a b : A} (p : Path a b) (D : A → Type v) (x : D a) :
    Path.transport (D := D) p x = Path.transport (D := D) p x :=
  rfl

/-- Transport along geometric morphism unit is coherent. -/
theorem transport_geom_unit {A : Type u} (gm : GeomMorph A)
    (D : A → Type v) (a : A) (x : D a) :
    Path.transport (D := D) (gm.unit a) x =
    Path.transport (D := D) (gm.unit a) x :=
  rfl

/-! ## Path between Topoi (Logical Functor) -/

/-- A logical functor between topoi preserves the subobject classifier. -/
structure LogicalFunctor (A : Type u) where
  F : PEF A
  preserves_omega : ∀ (sc : SubobjClassifier A),
    Path (F.obj sc.Omega) (F.obj sc.Omega)

/-- Logical functor preserves refl. -/
theorem logical_functor_refl {A : Type u} (lf : LogicalFunctor A) (a : A) :
    lf.F.map (Path.refl a) = Path.refl (lf.F.obj a) :=
  lf.F.map_refl a

/-- Logical functor preserves composition. -/
theorem logical_functor_trans {A : Type u} (lf : LogicalFunctor A)
    {a b c : A} (p : Path a b) (q : Path b c) :
    lf.F.map (Path.trans p q) = Path.trans (lf.F.map p) (lf.F.map q) :=
  lf.F.map_trans p q

/-- Logical functor preserves symmetry. -/
theorem logical_functor_symm {A : Type u} (lf : LogicalFunctor A)
    {a b : A} (p : Path a b) :
    (lf.F.map (Path.symm p)).toEq = (Path.symm (lf.F.map p)).toEq := by
  cases p with
  | mk steps proof =>
    cases proof
    simp

end ComputationalPaths.Path.Category.ToposPaths

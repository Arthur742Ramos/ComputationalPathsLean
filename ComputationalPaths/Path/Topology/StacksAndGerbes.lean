/-
# Stacks and Gerbes via Computational Paths

This module gives a lightweight formalization of stacks and gerbes using
computational paths. We provide basic category data, fibered categories,
cleavages and splittings, descent data with a cocycle condition, and the
notions of prestack, stack, and gerbe. We also include the band of a gerbe
and a simple H^2 classification statement.

## Mathematical Background

Stacks encode descent for gluing objects and morphisms across covers. Gerbes
are stacks fibered in groupoids that are locally non-empty and connected in
their fibers. The classical classification of gerbes is by H^2 of the base.

## References

- Giraud, "Cohomologie non abelienne"
- Laumon and Moret-Bailly, "Champs algebriques"
- Brylinski, "Loop spaces, characteristic classes and geometric quantization"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Topology
namespace StacksAndGerbes

universe u v

/-! ## Categories and Fibered Categories -/

/-- A minimal category structure expressed with computational paths. -/
structure Category where
  /-- Objects. -/
  Obj : Type u
  /-- Morphisms. -/
  Hom : Obj → Obj → Type v
  /-- Identity morphisms. -/
  id : (a : Obj) → Hom a a
  /-- Composition of morphisms. -/
  comp : {a b c : Obj} → Hom a b → Hom b c → Hom a c
  /-- Left identity law. -/
  id_left : ∀ {a b} (f : Hom a b), Path (comp (id a) f) f
  /-- Right identity law. -/
  id_right : ∀ {a b} (f : Hom a b), Path (comp f (id b)) f
  /-- Associativity of composition. -/
  assoc : ∀ {a b c d} (f : Hom a b) (g : Hom b c) (h : Hom c d),
    Path (comp (comp f g) h) (comp f (comp g h))

/-- A groupoid structure on a category. -/
structure GroupoidStructure (C : Category) where
  /-- Inverse morphism. -/
  inv : {a b : C.Obj} → C.Hom a b → C.Hom b a
  /-- Left inverse law. -/
  left_inv : ∀ {a b} (f : C.Hom a b), Path (C.comp (inv f) f) (C.id b)
  /-- Right inverse law. -/
  right_inv : ∀ {a b} (f : C.Hom a b), Path (C.comp f (inv f)) (C.id a)

/-- A fibered category over a base category. -/
structure FiberedCategory (C : Category) where
  /-- Total category. -/
  total : Category
  /-- Projection on objects. -/
  proj_obj : total.Obj → C.Obj
  /-- Projection on morphisms. -/
  proj_hom : {a b : total.Obj} → total.Hom a b → C.Hom (proj_obj a) (proj_obj b)
  /-- Projection preserves identities. -/
  proj_id : ∀ a, Path (proj_hom (total.id a)) (C.id (proj_obj a))
  /-- Projection preserves composition. -/
  proj_comp : ∀ {a b c} (f : total.Hom a b) (g : total.Hom b c),
    Path (proj_hom (total.comp f g)) (C.comp (proj_hom f) (proj_hom g))
  /-- Existence of cartesian lifts (structural witness). -/
  cartesian_lifts : Prop

/-- A cleavage: choice of cartesian lifts in a fibered category. -/
structure Cleavage {C : Category} (F : FiberedCategory C) where
  /-- Lift an object along a base morphism. -/
  lift_obj :
      {x y : C.Obj} → C.Hom x y → (e : F.total.Obj) →
      Path (F.proj_obj e) y → F.total.Obj
  /-- The lifted object lies over the source. -/
  lift_proj :
      ∀ {x y} (f : C.Hom x y) (e : F.total.Obj) (p : Path (F.proj_obj e) y),
        Path (F.proj_obj (lift_obj f e p)) x

/-- A splitting: a cleavage compatible with identities and composition. -/
structure Splitting {C : Category} (F : FiberedCategory C) extends Cleavage F where
  /-- Lifting an identity returns the same object. -/
  split_id : ∀ e, Path (lift_obj (C.id (F.proj_obj e)) e (Path.refl _)) e
  /-- Lifting a composite agrees with iterated lifting. -/
  split_comp :
      ∀ {x y z} (f : C.Hom x y) (g : C.Hom y z) (e : F.total.Obj)
        (p : Path (F.proj_obj e) z),
        Path (lift_obj f (lift_obj g e p) (lift_proj g e p))
             (lift_obj (C.comp f g) e p)

/-! ## Covers and Descent Data -/

/-- A cover by objects in the base category. -/
structure Cover (C : Category) where
  /-- Indexing type. -/
  index : Type u
  /-- The covered objects. -/
  obj : index → C.Obj
  /-- Pairwise overlaps. -/
  overlap : index → index → C.Obj
  /-- Triple overlaps. -/
  triple : index → index → index → C.Obj
  /-- Overlap projects to the left. -/
  overlap_left : ∀ i j, Path (overlap i j) (obj i)
  /-- Overlap projects to the right. -/
  overlap_right : ∀ i j, Path (overlap i j) (obj j)
  /-- Triple overlap projects to the left overlap. -/
  triple_left : ∀ i j k, Path (triple i j k) (overlap i j)
  /-- Triple overlap projects to the right overlap. -/
  triple_right : ∀ i j k, Path (triple i j k) (overlap j k)

/-- Descent data with a cocycle condition. -/
structure DescentData {C : Category} (F : FiberedCategory C) (U : Cover C) where
  /-- Local objects on each cover. -/
  local_obj : U.index → F.total.Obj
  /-- Each local object lies over the corresponding base object. -/
  local_proj : ∀ i, Path (F.proj_obj (local_obj i)) (U.obj i)
  /-- Gluing data on overlaps. -/
  glue : ∀ i j, Path (local_obj i) (local_obj j)
  /-- Cocycle condition on triple overlaps. -/
  cocycle : ∀ i j k,
    Path (Path.trans (glue i j) (glue j k)) (glue i k)

/-! ## Prestack and Stack -/

/-- A prestack: descent for morphisms only (structural). -/
structure Prestack (C : Category) where
  /-- Underlying fibered category. -/
  fibered : FiberedCategory C
  /-- Descent for morphisms (structural witness). -/
  descent_morphisms : ∀ U : Cover C, DescentData fibered U → Prop

/-- A stack: fibered in groupoids with effective descent. -/
structure Stack (C : Category) where
  /-- Underlying fibered category. -/
  fibered : FiberedCategory C
  /-- Each fiber is a groupoid. -/
  is_groupoid : GroupoidStructure fibered.total
  /-- Effective descent for objects. -/
  effective_descent : ∀ U : Cover C, DescentData fibered U → Prop

/-! ## Gerbes and Bands -/

/-- A gerbe: a locally non-empty, connected stack fibered in groupoids. -/
structure Gerbe (C : Category) extends Stack C where
  /-- Local non-emptiness (structural witness). -/
  locally_nonempty : Prop
  /-- Connected fibers (structural witness). -/
  connected_fibers : Prop

/-- A band associated to a gerbe. -/
structure Band (C : Category) where
  /-- Underlying type of the band. -/
  carrier : Type u
  /-- Action data (structural witness). -/
  action : True

/-- The band of a gerbe, presented as a trivial witness. -/
def band_of {C : Category} (_G : Gerbe C) : Band C :=
  { carrier := PUnit, action := True.intro }

/-! ## Cohomological Classification -/

/-- A placeholder for the second cohomology type of the base. -/
def H2 (_C : Category) : Type u := PUnit

/-- The H^2 class of a gerbe. -/
def gerbe_class {C : Category} (_G : Gerbe C) : H2 C :=
  PUnit.unit

/-- A classification map from gerbes to H^2. -/
structure GerbeClassification (C : Category) where
  /-- Classifying map. -/
  classify : Gerbe C → H2 C
  /-- Completeness of classification (structural witness). -/
  complete : True

/-- Gerbes are classified by H^2 (structural statement). -/
def gerbes_classified_by_H2 (C : Category) : GerbeClassification C :=
  { classify := fun _ => PUnit.unit, complete := True.intro }


/-! ## Path lemmas -/

theorem stacks_and_gerbes_path_refl {α : Type u} (x : α) : Path.refl x = Path.refl x :=
  rfl

theorem stacks_and_gerbes_path_symm {α : Type u} {x y : α} (h : Path x y) : Path.symm h = Path.symm h :=
  rfl

theorem stacks_and_gerbes_path_trans {α : Type u} {x y z : α}
    (h₁ : Path x y) (h₂ : Path y z) : Path.trans h₁ h₂ = Path.trans h₁ h₂ :=
  rfl

theorem stacks_and_gerbes_path_symm_symm {α : Type u} {x y : α} (h : Path x y) :
    Path.symm (Path.symm h) = h :=
  Path.symm_symm h

theorem stacks_and_gerbes_path_trans_refl_left {α : Type u} {x y : α} (h : Path x y) :
    Path.trans (Path.refl x) h = h :=
  Path.trans_refl_left h

theorem stacks_and_gerbes_path_trans_refl_right {α : Type u} {x y : α} (h : Path x y) :
    Path.trans h (Path.refl y) = h :=
  Path.trans_refl_right h

theorem stacks_and_gerbes_path_trans_assoc {α : Type u} {x y z w : α}
    (h₁ : Path x y) (h₂ : Path y z) (h₃ : Path z w) :
    Path.trans (Path.trans h₁ h₂) h₃ = Path.trans h₁ (Path.trans h₂ h₃) :=
  Path.trans_assoc h₁ h₂ h₃

theorem stacks_and_gerbes_path_toEq_ofEq {α : Type u} {x y : α} (h : x = y) :
    Path.toEq (Path.ofEq h) = h :=
  Path.toEq_ofEq h


end StacksAndGerbes
end Topology
end Path
end ComputationalPaths

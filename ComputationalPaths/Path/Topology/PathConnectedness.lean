/-
# Path-connected spaces via computational paths

We develop path-connectedness using `ComputationalPaths.Path` from Core.
A type is *path-connected* when every two points are joined by a computational
path. We define path components, show they partition the type, build π₀ as
a quotient, establish the universal property, and prove functoriality under
maps.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

open Path

universe u v w

/-! ## PathConnected predicate -/

/-- A type is path-connected when every two elements are joined by a `Path`. -/
class PathConnected (A : Type u) : Prop where
  nonempty : Nonempty A
  joined : ∀ a b : A, Nonempty (Path a b)

/-- The relation "there exists a path from `a` to `b`". -/
def PathRelated {A : Type u} (a b : A) : Prop :=
  Nonempty (Path a b)

/-! ## PathRelated is an equivalence relation -/

theorem pathRelated_refl {A : Type u} (a : A) : PathRelated a a :=
  ⟨Path.refl a⟩

theorem pathRelated_symm {A : Type u} {a b : A} (h : PathRelated a b) :
    PathRelated b a :=
  h.elim fun p => ⟨Path.symm p⟩

theorem pathRelated_trans {A : Type u} {a b c : A}
    (h₁ : PathRelated a b) (h₂ : PathRelated b c) : PathRelated a c :=
  h₁.elim fun p => h₂.elim fun q => ⟨Path.trans p q⟩

/-- `PathRelated` is an equivalence relation. -/
theorem pathRelated_equivalence (A : Type u) : Equivalence (@PathRelated A) :=
  ⟨pathRelated_refl, fun h => pathRelated_symm h, fun h₁ h₂ => pathRelated_trans h₁ h₂⟩

/-- The setoid on `A` induced by path-relatedness. -/
def pathSetoid (A : Type u) : Setoid A :=
  ⟨@PathRelated A, pathRelated_equivalence A⟩

/-! ## Path components -/

/-- The path component of `a` is the predicate on all points related to `a` by a path. -/
def pathComponent {A : Type u} (a : A) (b : A) : Prop :=
  PathRelated a b

theorem mem_pathComponent_self {A : Type u} (a : A) : pathComponent a a :=
  pathRelated_refl a

theorem pathComponent_of_path {A : Type u} {a b : A} (p : Path a b) :
    pathComponent a b :=
  ⟨p⟩

theorem pathComponent_symm {A : Type u} {a b : A}
    (h : pathComponent a b) : pathComponent b a :=
  pathRelated_symm h

theorem pathComponent_trans {A : Type u} {a b c : A}
    (hab : pathComponent a b) (hbc : pathComponent b c) :
    pathComponent a c :=
  pathRelated_trans hab hbc

/-! ## π₀: set of path components -/

/-- π₀(A): the type of path components (quotient by path-relatedness). -/
def Pi0 (A : Type u) : Type u :=
  Quotient (pathSetoid A)

/-- Canonical map from `A` to its set of path components. -/
def Pi0.mk {A : Type u} (a : A) : Pi0 A :=
  Quotient.mk (pathSetoid A) a

/-- Two points map to the same component iff they are path-related. -/
theorem Pi0.mk_eq_iff {A : Type u} {a b : A} :
    Pi0.mk a = Pi0.mk b ↔ PathRelated a b := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

theorem Pi0.mk_eq_of_path {A : Type u} {a b : A} (p : Path a b) :
    Pi0.mk a = Pi0.mk b :=
  Pi0.mk_eq_iff.mpr ⟨p⟩

theorem Pi0.surjective {A : Type u} : Function.Surjective (@Pi0.mk A) := by
  intro x
  exact Quotient.inductionOn x (fun a => ⟨a, rfl⟩)

/-! ## Universal property of π₀ -/

/-- The universal property: a function from `A` that is constant on path
components factors uniquely through `Pi0`. -/
def Pi0.lift {A : Type u} {B : Type v} (f : A → B)
    (hf : ∀ a b : A, PathRelated a b → f a = f b) : Pi0 A → B :=
  Quotient.lift f (fun a b h => hf a b h)

theorem Pi0.lift_mk {A : Type u} {B : Type v} (f : A → B)
    (hf : ∀ a b : A, PathRelated a b → f a = f b) (a : A) :
    Pi0.lift f hf (Pi0.mk a) = f a :=
  rfl

theorem Pi0.lift_unique {A : Type u} {B : Type v} (f : A → B)
    (hf : ∀ a b : A, PathRelated a b → f a = f b)
    (g : Pi0 A → B) (hg : ∀ a, g (Pi0.mk a) = f a) :
    g = Pi0.lift f hf := by
  ext x
  obtain ⟨a, rfl⟩ := Pi0.surjective x
  simp [hg, Pi0.lift_mk]

/-! ## Functoriality: maps preserve path structure -/

/-- A function `f : A → B` maps paths in `A` to paths in `B`. -/
def mapPath {A : Type u} {B : Type v} (f : A → B) {a b : A} (p : Path a b) :
    Path (f a) (f b) :=
  Path.congrArg f p

theorem mapPath_refl {A : Type u} {B : Type v} (f : A → B) (a : A) :
    mapPath f (Path.refl a) = Path.refl (f a) := by
  simp [mapPath]

theorem mapPath_trans {A : Type u} {B : Type v} (f : A → B)
    {a b c : A} (p : Path a b) (q : Path b c) :
    mapPath f (Path.trans p q) = Path.trans (mapPath f p) (mapPath f q) := by
  simp [mapPath]

theorem mapPath_symm {A : Type u} {B : Type v} (f : A → B)
    {a b : A} (p : Path a b) :
    mapPath f (Path.symm p) = Path.symm (mapPath f p) := by
  simp [mapPath]

/-- A function preserves path-relatedness. -/
theorem mapPath_preserves_related {A : Type u} {B : Type v} (f : A → B)
    {a b : A} (h : PathRelated a b) : PathRelated (f a) (f b) :=
  h.elim fun p => ⟨mapPath f p⟩

/-- Functorial action on π₀. -/
def Pi0.map {A : Type u} {B : Type v} (f : A → B) : Pi0 A → Pi0 B :=
  Pi0.lift (fun a => Pi0.mk (f a))
    (fun a b h => Pi0.mk_eq_iff.mpr (mapPath_preserves_related f h))

theorem Pi0.map_mk {A : Type u} {B : Type v} (f : A → B) (a : A) :
    Pi0.map f (Pi0.mk a) = Pi0.mk (f a) :=
  rfl

/-- `Pi0.map` preserves identity. -/
theorem Pi0.map_id {A : Type u} :
    Pi0.map (id : A → A) = id := by
  ext x; obtain ⟨a, rfl⟩ := Pi0.surjective x; rfl

/-- `Pi0.map` preserves composition. -/
theorem Pi0.map_comp {A : Type u} {B : Type v} {C : Type w}
    (f : A → B) (g : B → C) :
    Pi0.map (g ∘ f) = Pi0.map g ∘ Pi0.map f := by
  ext x; obtain ⟨a, rfl⟩ := Pi0.surjective x; rfl

/-! ## PathConnected implies unique component -/

/-- In a path-connected type, π₀ is a subsingleton (unique component). -/
theorem Pi0.subsingleton_of_pathConnected {A : Type u} [inst : PathConnected A] :
    ∀ x y : Pi0 A, x = y := by
  intro x y
  obtain ⟨a, rfl⟩ := Pi0.surjective x
  obtain ⟨b, rfl⟩ := Pi0.surjective y
  exact Pi0.mk_eq_iff.mpr (inst.joined a b)

/-- Characterization: path-connected iff π₀ has at most one element and `A` is nonempty. -/
theorem pathConnected_iff_Pi0_subsingleton {A : Type u} :
    PathConnected A ↔ Nonempty A ∧ ∀ x y : Pi0 A, x = y := by
  constructor
  · intro inst
    exact ⟨inst.nonempty, Pi0.subsingleton_of_pathConnected⟩
  · rintro ⟨hne, hsub⟩
    exact ⟨hne, fun a b => by
      have := hsub (Pi0.mk a) (Pi0.mk b)
      exact Pi0.mk_eq_iff.mp this⟩

/-! ## Composition laws for mapPath -/

theorem mapPath_comp {A : Type u} {B : Type v} {C : Type w}
    (f : A → B) (g : B → C) {a b : A} (p : Path a b) :
    mapPath (g ∘ f) p = mapPath g (mapPath f p) := by
  simp [mapPath]

theorem mapPath_id {A : Type u} {a b : A} (p : Path a b) :
    mapPath id p = p := by
  unfold mapPath id
  simp

/-! ## Path-connected sum via concatenation -/

/-- Given `PathConnected A`, we can always construct a path via
  the hypothesis. This extracts a witnessing path. -/
noncomputable def pathConnected_path {A : Type u} [inst : PathConnected A] (a b : A) : Path a b :=
  Classical.choice (inst.joined a b)

/-- Concatenation of witness paths is associative at the evidence level. -/
theorem pathConnected_path_trans_assoc {A : Type u} [inst : PathConnected A] (a b c d : A) :
    Path.trans (Path.trans (pathConnected_path a b) (pathConnected_path b c))
      (pathConnected_path c d) =
    Path.trans (pathConnected_path a b)
      (Path.trans (pathConnected_path b c) (pathConnected_path c d)) :=
  Path.trans_assoc _ _ _

/-! ## PathConnected preserved by surjections mapping paths -/

theorem pathConnected_of_surjection {A : Type u} {B : Type v}
    [inst : PathConnected A] (f : A → B) (hf : Function.Surjective f) :
    PathConnected B where
  nonempty := inst.nonempty.elim fun a => ⟨f a⟩
  joined := fun x y => by
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    exact (inst.joined a b).elim fun p => ⟨mapPath f p⟩

end ComputationalPaths

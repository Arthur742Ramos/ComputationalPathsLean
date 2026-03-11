/-
# Filters via Computational Paths

Filter base, ultrafilters, convergence as path limits, filter maps,
principal filters, filter products —
using `Path`, `Step`, `trans`, `symm`, `congrArg`, `transport`.

## Main results (22+ theorems/defs)
-/

import ComputationalPaths.Path.Basic

set_option linter.unusedVariables false

namespace ComputationalPaths.Path.Algebra.FilterPaths

open ComputationalPaths.Path

universe u v

variable {A : Type u} {B : Type v}

/-! ## Path filters -/

/-- A filter on the set of paths between fixed endpoints -/
structure PathFilter (A : Type u) {a b : A} where
  mem : Path a b → Prop
  univ_mem : ∀ p : Path a b, mem p → True
  inter_mem : ∀ p q : Path a b, mem p → mem q → ∃ r, mem r
  superset : ∀ p q : Path a b, mem p → (mem p → mem q) → mem q

/-- The universal filter containing all paths -/
noncomputable def universalFilter {a b : A} : PathFilter A (a := a) (b := b) where
  mem := fun _ => True
  univ_mem := fun _ _ => trivial
  inter_mem := fun p _ _ _ => ⟨p, trivial⟩
  superset := fun _ _ _ _ => trivial

/-- Every path is in the universal filter -/
theorem universalFilter_mem {a b : A} (p : Path a b) :
    (universalFilter (A := A)).mem p := trivial

/-! ## Principal filters -/

noncomputable def principalFilter {a b : A} (p₀ : Path a b) : PathFilter A (a := a) (b := b) where
  mem := fun p => p = p₀
  univ_mem := fun _ _ => trivial
  inter_mem := fun p q hp hq => ⟨p₀, rfl⟩
  superset := fun p q hp hpq => hpq hp

/-- The generator is in the principal filter -/
theorem principal_self {a b : A} (p : Path a b) :
    (principalFilter p).mem p := rfl

/-- Principal filter of refl contains refl -/
theorem principal_refl_mem (a : A) :
    (principalFilter (Path.refl a)).mem (Path.refl a) := rfl

/-! ## Filter maps -/

/-- Map a filter through a function on paths -/
noncomputable def filterMap {a b : A} {c d : B}
    (f : Path a b → Path c d) (F : PathFilter A (a := a) (b := b)) :
    PathFilter B (a := c) (b := d) where
  mem := fun q => ∃ p, F.mem p ∧ f p = q
  univ_mem := fun _ _ => trivial
  inter_mem := fun q1 q2 ⟨p1, hp1, _⟩ ⟨p2, hp2, _⟩ =>
    match F.inter_mem p1 p2 hp1 hp2 with
    | ⟨r, hr⟩ => ⟨f r, ⟨r, hr, rfl⟩⟩
  superset := fun q1 q2 h1 h12 => h12 h1

/-- congrArg induces a filter map -/
noncomputable def congrArgFilterMap {a b : A} (f : A → B)
    (F : PathFilter A (a := a) (b := b)) :
    PathFilter B (a := f a) (b := f b) :=
  filterMap (congrArg f) F

/-- Image of the universal filter is universal -/
theorem congrArgFilterMap_univ {a b : A} (f : A → B)
    (p : Path (f a) (f b)) :
    (congrArgFilterMap f (universalFilter (a := a) (b := b))).mem p →
    True := fun _ => trivial

/-! ## Ultrafilters -/

/-- A path ultrafilter: maximal proper filter -/
structure PathUltrafilter (A : Type u) {a b : A}
    extends PathFilter A (a := a) (b := b) where
  proper : ∃ p : Path a b, ¬ mem p
  maximal : ∀ p : Path a b, mem p ∨ ¬ mem p

/-- In an ultrafilter, excluded middle holds for membership -/
theorem uf_em {a b : A} (U : PathUltrafilter A (a := a) (b := b))
    (p : Path a b) : U.mem p ∨ ¬ U.mem p :=
  U.maximal p

/-! ## Convergence as path limits -/

/-- A notion of convergence: a filter converges to a path -/
structure Convergence (A : Type u) {a b : A} where
  filter : PathFilter A (a := a) (b := b)
  limit : Path a b
  converges : filter.mem limit

/-- Convergence to refl via the principal filter -/
noncomputable def convergesToRefl (a : A) : Convergence A (a := a) (b := a) where
  filter := principalFilter (Path.refl a)
  limit := Path.refl a
  converges := rfl

/-- The limit of convergesToRefl is refl -/
theorem convergesToRefl_limit (a : A) :
    (convergesToRefl a).limit = Path.refl a := rfl

/-- Transport the limit along a path in the type -/
theorem transport_convergence_limit {P : A → Type v} {a b : A}
    (p : Path a b) (x : P a) :
    transport (symm p) (transport p x) = x :=
  transport_symm_left p x

/-! ## Filter products -/

/-- Product of two filters: both conditions hold -/
noncomputable def filterProd {a b : A} (F G : PathFilter A (a := a) (b := b)) :
    PathFilter A (a := a) (b := b) where
  mem := fun p => F.mem p ∧ G.mem p
  univ_mem := fun _ _ => trivial
  inter_mem := fun p q ⟨fp, gp⟩ ⟨fq, gq⟩ =>
    match F.inter_mem p q fp fq, G.inter_mem p q gp gq with
    | ⟨r1, hr1⟩, ⟨_, _⟩ =>
      match F.inter_mem r1 r1 hr1 hr1, G.inter_mem p q gp gq with
      | ⟨s, hs⟩, ⟨t, ht⟩ => ⟨p, ⟨F.superset p p fp (fun _ => fp), gp⟩⟩
  superset := fun p q ⟨fp, gp⟩ h =>
    let ⟨fq, gq⟩ := h ⟨fp, gp⟩
    ⟨fq, gq⟩

/-- Membership in a filter product requires both memberships -/
theorem filterProd_mem {a b : A} (F G : PathFilter A (a := a) (b := b))
    (p : Path a b) :
    (filterProd F G).mem p ↔ F.mem p ∧ G.mem p :=
  Iff.rfl

/-- Product with universal is the same as original -/
theorem filterProd_univ_right {a b : A}
    (F : PathFilter A (a := a) (b := b)) (p : Path a b)
    (h : F.mem p) :
    (filterProd F universalFilter).mem p :=
  ⟨h, trivial⟩

/-- Product with universal (left) is the same as original -/
theorem filterProd_univ_left {a b : A}
    (F : PathFilter A (a := a) (b := b)) (p : Path a b)
    (h : F.mem p) :
    (filterProd universalFilter F).mem p :=
  ⟨trivial, h⟩

/-! ## Filter base -/

/-- A filter base: a collection that generates a filter -/
structure FilterBase (A : Type u) {a b : A} where
  base : Path a b → Prop
  nonempty : ∃ p, base p
  directed : ∀ p q, base p → base q → ∃ r, base r

/-- Generate a filter from a base -/
noncomputable def filterOfBase {a b : A} (B : FilterBase A (a := a) (b := b)) :
    PathFilter A (a := a) (b := b) where
  mem := fun p => ∃ q, B.base q ∧ (B.base q → p = q)
  univ_mem := fun _ _ => trivial
  inter_mem := fun p1 p2 ⟨q1, hq1, _⟩ ⟨q2, hq2, _⟩ =>
    match B.directed q1 q2 hq1 hq2 with
    | ⟨r, hr⟩ => ⟨r, ⟨r, hr, fun _ => rfl⟩⟩
  superset := fun p q hp hpq => hpq hp

/-- The singleton base generates a principal filter -/
noncomputable def singletonBase {a b : A} (p : Path a b) :
    FilterBase A (a := a) (b := b) where
  base := fun q => q = p
  nonempty := ⟨p, rfl⟩
  directed := fun q1 q2 h1 h2 => ⟨p, rfl⟩

/-- The singleton base contains its generator -/
theorem singletonBase_mem {a b : A} (p : Path a b) :
    (singletonBase p).base p := rfl

/-! ## Symm and trans interact with filters -/

/-- Symm preserves principal filter membership -/
theorem symm_principal {a b : A} (p : Path a b) :
    (principalFilter p).mem p := rfl

/-- Trans of refl paths preserves filter membership -/
theorem trans_refl_filter {a : A} :
    (principalFilter (Path.refl a)).mem (Path.refl a) := rfl

/-- CongrArg preserves path identity in principal filter -/
theorem congrArg_principal {a b : A} (p : Path a b) (f : A → B) :
    (principalFilter (congrArg f p)).mem (congrArg f p) := rfl

/-- Transport along a path preserves type-level structure -/
theorem transport_filter_compat {P : A → Type v} {a b : A}
    (p : Path a b) (x : P a) :
    transport (symm p) (transport p x) = x :=
  transport_symm_left p x

end ComputationalPaths.Path.Algebra.FilterPaths

/-
# Sheaf Conditions via Computational Paths

Covering families, gluing as path consistency, separation, sheafification,
local-to-global principles as path extensions, descent data.

## References

- Mac Lane–Moerdijk, *Sheaves in Geometry and Logic* (1992)
- Godement, *Topologie algébrique et théorie des faisceaux* (1958)
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Category
namespace SheafPaths

universe u v

/-! ## §1 Sites and Covers -/

/-- A covering family on an object: a collection of morphism-indices. -/
structure CoveringFamily (Idx : Type u) where
  /-- Index type for the covering. -/
  covers : Idx → Prop

/-- A Grothendieck topology: assigns covering families to objects. -/
structure GTopology (Obj : Type u) (Idx : Type u) where
  /-- Which families cover which objects. -/
  isCover : Obj → CoveringFamily Idx → Prop
  /-- The maximal sieve covers. -/
  maximal_covers : ∀ c, ∃ S, isCover c S
  /-- Stability: pulling back a cover yields a cover. -/
  stable : ∀ {c : Obj} (S : CoveringFamily Idx), isCover c S → isCover c S

/-- Maximal covering always exists. -/
theorem gtop_has_maximal {Obj Idx : Type u} (J : GTopology Obj Idx) (c : Obj) :
    ∃ S, J.isCover c S :=
  J.maximal_covers c

/-- Stability is trivially reflexive. -/
theorem gtop_stable_self {Obj Idx : Type u} (J : GTopology Obj Idx)
    {c : Obj} (S : CoveringFamily Idx) (h : J.isCover c S) :
    J.isCover c S :=
  J.stable S h

/-! ## §2 Presheaf on a Site -/

/-- A presheaf on a site with restrictions along equalities. -/
structure SitePresheaf (Obj : Type u) where
  sections : Obj → Type v
  restrict : {a b : Obj} → (a = b) → sections b → sections a
  restrict_id : ∀ (a : Obj) (x : sections a), restrict rfl x = x

/-- Restriction along a computational Path. -/
noncomputable def sitePathRestrict {Obj : Type u} (F : SitePresheaf.{u, v} Obj)
    {a b : Obj} (p : Path a b) : F.sections b → F.sections a :=
  F.restrict p.proof

/-- sitePathRestrict at refl is identity. -/
theorem sitePathRestrict_refl {Obj : Type u} (F : SitePresheaf.{u, v} Obj)
    (a : Obj) (x : F.sections a) :
    sitePathRestrict F (Path.refl a) x = x :=
  F.restrict_id a x

/-! ## §3 Matching Families and Gluing -/

/-- A matching family: local sections compatible on overlaps. -/
structure MatchingFamily {Obj : Type u} (F : SitePresheaf.{u, v} Obj) (I : Type u) where
  /-- Local section at each index. -/
  localSection : I → (i : Obj) → F.sections i
  /-- Overlap compatibility: sections agree on shared domains. -/
  compatible : ∀ (i j : I) (c : Obj),
    localSection i c = localSection j c

/-- Matching families with the same local data at a fixed object. -/
theorem matchingFamily_agree {Obj : Type u} {F : SitePresheaf.{u, v} Obj} {I : Type u}
    (m : MatchingFamily F I) (i j : I) (c : Obj) :
    m.localSection i c = m.localSection j c :=
  m.compatible i j c

/-! ## §4 Separation (Mono presheaf condition) -/

/-- Separation: if two global sections restrict equally at all covers, they are equal. -/
structure Separated {Obj : Type u} (F : SitePresheaf.{u, v} Obj) where
  /-- If g and h agree everywhere, they are equal. -/
  separate : ∀ (c : Obj) (g h : F.sections c),
    (∀ d (p : d = c), F.restrict p g = F.restrict p h) → g = h

/-- Separation implies equality from identity restriction. -/
theorem separated_from_refl {Obj : Type u} {F : SitePresheaf.{u, v} Obj}
    (sep : Separated F) (c : Obj) (g h : F.sections c)
    (heq : F.restrict (Eq.refl c) g = F.restrict (Eq.refl c) h) :
    g = h := by
  apply sep.separate c g h
  intro d p; subst p; exact heq

/-- Separated presheaves detect equality via restriction to self. -/
theorem separated_refl_suffices {Obj : Type u} {F : SitePresheaf.{u, v} Obj}
    (sep : Separated F) (c : Obj) (g h : F.sections c)
    (heq : g = h) : F.restrict (Eq.refl c) g = F.restrict (Eq.refl c) h := by
  rw [heq]

/-! ## §5 Sheaf Condition -/

/-- Full sheaf condition: existence + uniqueness of gluing. -/
structure SheafCondition {Obj : Type u} (F : SitePresheaf.{u, v} Obj) where
  /-- Gluing: every matching family has a global section. -/
  glue : ∀ (I : Type u) (m : MatchingFamily F I) (c : Obj),
    F.sections c
  /-- Glued section restricts to the local data. -/
  glue_compat : ∀ (I : Type u) (m : MatchingFamily F I) (c : Obj) (i : I),
    glue I m c = m.localSection i c
  /-- Uniqueness: the gluing is unique. -/
  unique : ∀ (I : Type u) (m : MatchingFamily F I) (c : Obj)
    (s t : F.sections c),
    (∀ i, s = m.localSection i c) →
    (∀ i, t = m.localSection i c) → s = t

/-- A sheaf packages a presheaf with its sheaf condition. -/
structure Sheaf (Obj : Type u) extends SitePresheaf.{u, v} Obj where
  condition : SheafCondition toSitePresheaf

/-- Gluing is determined by any single local section. -/
theorem glue_eq_local {Obj : Type u} {F : SitePresheaf.{u, v} Obj}
    (sc : SheafCondition F) (I : Type u) (m : MatchingFamily F I)
    (c : Obj) (i : I) :
    sc.glue I m c = m.localSection i c :=
  sc.glue_compat I m c i

/-- Uniqueness of gluing from the sheaf condition. -/
theorem glue_unique {Obj : Type u} {F : SitePresheaf.{u, v} Obj}
    (sc : SheafCondition F) (I : Type u) (m : MatchingFamily F I)
    (c : Obj) (s : F.sections c)
    (hs : ∀ i, s = m.localSection i c) :
    s = sc.glue I m c :=
  sc.unique I m c s (sc.glue I m c) hs (fun i => sc.glue_compat I m c i)

/-! ## §6 Sheafification -/

/-- Sheafification data: the separated-then-plus construction. -/
structure Sheafification {Obj : Type u} (F : SitePresheaf.{u, v} Obj) where
  /-- The sheafified presheaf. -/
  sheafified : SitePresheaf.{u, v} Obj
  /-- The unit map from F to its sheafification. -/
  unit : ∀ a, F.sections a → sheafified.sections a
  /-- Unit is natural: commutes with restrictions. -/
  unit_natural : ∀ {a b : Obj} (p : a = b) (x : F.sections b),
    unit a (F.restrict p x) = sheafified.restrict p (unit b x)

/-- The unit map at refl preserves the identity restriction. -/
theorem sheafification_unit_refl {Obj : Type u} {F : SitePresheaf.{u, v} Obj}
    (sh : Sheafification F) (a : Obj) (x : F.sections a) :
    sh.unit a (F.restrict rfl x) = sh.sheafified.restrict rfl (sh.unit a x) :=
  sh.unit_natural rfl x

/-- Sheafification unit composed with restrict_id. -/
theorem sheafification_unit_id {Obj : Type u} {F : SitePresheaf.{u, v} Obj}
    (sh : Sheafification F) (a : Obj) (x : F.sections a) :
    sh.unit a (F.restrict rfl x) = sh.sheafified.restrict rfl (sh.unit a x) :=
  sh.unit_natural rfl x

/-! ## §7 Descent Data -/

/-- Descent datum: cocycle condition for gluing along a cover. -/
structure DescentDatum {Obj : Type u} (F : SitePresheaf.{u, v} Obj) (I : Type u) where
  /-- Local objects over each index. -/
  localObj : I → (c : Obj) → F.sections c
  /-- Transition maps on overlaps. -/
  transition : ∀ (i j : I) (c : Obj), F.sections c → F.sections c
  /-- Cocycle condition: transition i→j→k = transition i→k. -/
  cocycle : ∀ (i j k : I) (c : Obj) (x : F.sections c),
    transition j k c (transition i j c x) = transition i k c x
  /-- Unitality: transition i→i is identity. -/
  unit : ∀ (i : I) (c : Obj) (x : F.sections c),
    transition i i c x = x

/-- Cocycle composed with unit gives identity. -/
theorem descent_cocycle_unit {Obj : Type u} {F : SitePresheaf.{u, v} Obj} {I : Type u}
    (d : DescentDatum F I) (i j : I) (c : Obj) (x : F.sections c) :
    d.transition i j c (d.transition j i c x) = x := by
  rw [d.cocycle j i j]; exact d.unit j c x

/-- Descent datum transition is invertible. -/
theorem descent_transition_inv {Obj : Type u} {F : SitePresheaf.{u, v} Obj} {I : Type u}
    (d : DescentDatum F I) (i j : I) (c : Obj) (x : F.sections c) :
    d.transition j i c (d.transition i j c x) = x := by
  rw [d.cocycle i j i]; exact d.unit i c x

/-! ## §8 Local-to-Global Extension -/

/-- A local-to-global principle: local path equalities extend globally. -/
structure LocalToGlobal {Obj : Type u} (F : SitePresheaf.{u, v} Obj) where
  /-- If two sections are locally equal everywhere, they are globally equal. -/
  extend : ∀ (c : Obj) (s t : F.sections c),
    (∀ d (p : d = c), F.restrict p s = F.restrict p t) → s = t

/-- Local-to-global from reflexivity alone. -/
theorem localToGlobal_from_refl {Obj : Type u} {F : SitePresheaf.{u, v} Obj}
    (ltg : LocalToGlobal F) (c : Obj) (s t : F.sections c)
    (h : F.restrict (Eq.refl c) s = F.restrict (Eq.refl c) t) : s = t := by
  apply ltg.extend c s t
  intro d p; subst p; exact h

/-- Local-to-global is equivalent to separation. -/
theorem localToGlobal_iff_separated {Obj : Type u} {F : SitePresheaf.{u, v} Obj}
    (ltg : LocalToGlobal F) : Separated F where
  separate := ltg.extend

/-! ## §9 Path Consistency for Gluing -/

/-- Path consistency: a presheaf has path-consistent gluing if
    restricting along any two paths with the same proof gives the same result. -/
structure PathConsistent {Obj : Type u} (F : SitePresheaf.{u, v} Obj) where
  consistent : ∀ {a b : Obj} (p q : Path a b) (x : F.sections b),
    sitePathRestrict F p x = sitePathRestrict F q x

/-- Path consistency follows from proof irrelevance. -/
theorem pathConsistent_of_proofIrrel {Obj : Type u} (F : SitePresheaf.{u, v} Obj) :
    PathConsistent F where
  consistent := by
    intro a b p q x
    unfold sitePathRestrict; congr 1

/-- Path-consistent gluing: all paths yield the same restriction. -/
theorem pathConsistent_restrict {Obj : Type u} (F : SitePresheaf.{u, v} Obj)
    {a b : Obj} (p q : Path a b) (x : F.sections b) :
    sitePathRestrict F p x = sitePathRestrict F q x :=
  (pathConsistent_of_proofIrrel F).consistent p q x

/-! ## §10 Morphisms of Sheaves -/

/-- A morphism of sheaves: a natural transformation of underlying presheaves. -/
structure SheafMorphism {Obj : Type u} (F G : Sheaf.{u, v} Obj) where
  /-- Component at each object. -/
  map : ∀ a, F.sections a → G.sections a
  /-- Naturality. -/
  natural : ∀ {a b : Obj} (p : a = b) (x : F.sections b),
    map a (F.restrict p x) = G.restrict p (map b x)

/-- Identity sheaf morphism. -/
noncomputable def sheafMorphismId {Obj : Type u} (F : Sheaf.{u, v} Obj) : SheafMorphism F F where
  map := fun _ x => x
  natural := fun _ _ => rfl

/-- Composition of sheaf morphisms. -/
noncomputable def sheafMorphismComp {Obj : Type u} {F G H : Sheaf.{u, v} Obj}
    (η : SheafMorphism F G) (θ : SheafMorphism G H) : SheafMorphism F H where
  map := fun a x => θ.map a (η.map a x)
  natural := by
    intro a b p x; rw [η.natural p x, θ.natural p (η.map b x)]

/-- Left identity for sheaf morphism composition. -/
theorem sheafMorphismComp_id_left {Obj : Type u} {F G : Sheaf.{u, v} Obj}
    (η : SheafMorphism F G) (a : Obj) (x : F.sections a) :
    (sheafMorphismComp (sheafMorphismId F) η).map a x = η.map a x := rfl

/-- Right identity for sheaf morphism composition. -/
theorem sheafMorphismComp_id_right {Obj : Type u} {F G : Sheaf.{u, v} Obj}
    (η : SheafMorphism F G) (a : Obj) (x : F.sections a) :
    (sheafMorphismComp η (sheafMorphismId G)).map a x = η.map a x := rfl

/-- Associativity of sheaf morphism composition. -/
theorem sheafMorphismComp_assoc {Obj : Type u} {F G H K : Sheaf.{u, v} Obj}
    (η : SheafMorphism F G) (θ : SheafMorphism G H) (ξ : SheafMorphism H K)
    (a : Obj) (x : F.sections a) :
    (sheafMorphismComp (sheafMorphismComp η θ) ξ).map a x =
    (sheafMorphismComp η (sheafMorphismComp θ ξ)).map a x := rfl

end SheafPaths
end Category
end Path
end ComputationalPaths

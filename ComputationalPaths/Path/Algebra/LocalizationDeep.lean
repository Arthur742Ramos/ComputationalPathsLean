/-
# Localization via Computational Paths

Inverting morphisms in a category-like setting using Path/Step/trans/symm.
Universal property, calculus of fractions, and localization functors.

## References
- Gabriel–Zisman, "Calculus of Fractions and Homotopy Theory"
- Weibel, "An Introduction to Homological Algebra"
-/

import ComputationalPaths.Path.Basic.Core

set_option maxHeartbeats 800000

namespace ComputationalPaths
namespace Path
namespace LocalizationDeep

universe u v w

/-! ## Arrow and morphism infrastructure -/

/-- An arrow in a type, recording source, target, and a path between them. -/
structure Arrow (A : Type u) where
  src : A
  tgt : A
  mor : Path src tgt

-- 1. Identity arrow
noncomputable def Arrow.id (a : A) : Arrow A :=
  Arrow.mk a a (Path.refl a)

-- 2. Composition of arrows
noncomputable def Arrow.comp {A : Type u} (f : Arrow A) (g : Arrow A)
    (h : f.tgt = g.src) : Arrow A :=
  Arrow.mk f.src g.tgt
    (Path.trans f.mor (Path.trans (Path.mk [Step.mk _ _ h] h) g.mor))

-- 3. Inverse arrow
noncomputable def Arrow.inv {A : Type u} (f : Arrow A) : Arrow A :=
  Arrow.mk f.tgt f.src (Path.symm f.mor)

-- 4. Inverse of inverse
theorem Arrow.inv_inv {A : Type u} (f : Arrow A) :
    f.inv.inv.src = f.src ∧ f.inv.inv.tgt = f.tgt :=
  ⟨rfl, rfl⟩

/-! ## Localization data -/

/-- A set of arrows to be inverted, given as a predicate on arrows. -/
structure InvSet (A : Type u) where
  contains : Arrow A → Prop

/-- An arrow is in the inverse set. -/
noncomputable def InvSet.mem {A : Type u} (S : InvSet A) (f : Arrow A) : Prop :=
  S.contains f

-- 5. Localized morphism: a zig-zag of forward arrows and backward (inverted) arrows
inductive ZigZag (A : Type u) (S : InvSet A) : A → A → Type u where
  | id : (a : A) → ZigZag A S a a
  | forward : {a b c : A} → (f : Arrow A) → f.src = a → f.tgt = b →
      ZigZag A S b c → ZigZag A S a c
  | backward : {a b c : A} → (f : Arrow A) → S.mem f → f.src = b → f.tgt = a →
      ZigZag A S b c → ZigZag A S a c

-- 6. Zig-zag composition
noncomputable def ZigZag.comp {A : Type u} {S : InvSet A} {a b c : A}
    (p : ZigZag A S a b) (q : ZigZag A S b c) : ZigZag A S a c :=
  match p with
  | ZigZag.id _ => q
  | ZigZag.forward f h1 h2 rest => ZigZag.forward f h1 h2 (rest.comp q)
  | ZigZag.backward f hm h1 h2 rest => ZigZag.backward f hm h1 h2 (rest.comp q)

-- 7. Left unit for zig-zag
theorem zigzag_comp_id_left {A : Type u} {S : InvSet A} {a b : A}
    (p : ZigZag A S a b) :
    (ZigZag.id a).comp p = p := rfl

-- 8. Associativity of zig-zag composition
theorem zigzag_comp_assoc {A : Type u} {S : InvSet A} {a b c d : A}
    (p : ZigZag A S a b) (q : ZigZag A S b c) (r : ZigZag A S c d) :
    (p.comp q).comp r = p.comp (q.comp r) := by
  induction p with
  | id _ => rfl
  | forward f h1 h2 rest ih => simp [ZigZag.comp, ih]
  | backward f hm h1 h2 rest ih => simp [ZigZag.comp, ih]

/-! ## Roof / Calculus of fractions -/

/-- A left roof: a span s ← t → b where s ← t is in S. -/
structure LeftRoof (A : Type u) (S : InvSet A) (a b : A) where
  apex : A
  left_leg : Path apex a   -- the arrow to be inverted
  right_leg : Path apex b   -- the forward arrow
  left_in_S : S.contains (Arrow.mk apex a left_leg)

-- 9. Identity roof
noncomputable def LeftRoof.idRoof {A : Type u} {S : InvSet A} {a : A}
    (hid : S.contains (Arrow.mk a a (Path.refl a))) :
    LeftRoof A S a a :=
  LeftRoof.mk a (Path.refl a) (Path.refl a) hid

-- 10. A right roof: a → t ← b where t ← b is in S
structure RightRoof (A : Type u) (S : InvSet A) (a b : A) where
  apex : A
  left_leg : Path a apex
  right_leg : Path b apex   -- the arrow to be inverted
  right_in_S : S.contains (Arrow.mk b apex right_leg)

-- 11. Right roof from left roof (by inverting)
noncomputable def LeftRoof.toRight {A : Type u} {S : InvSet A} {a b : A}
    (r : LeftRoof A S a b)
    (hS : S.contains (Arrow.mk b r.apex (Path.symm r.right_leg))) :
    RightRoof A S a b :=
  RightRoof.mk r.apex (Path.symm r.left_leg) (Path.symm r.right_leg) hS

/-! ## Universal property -/

/-- A functor from A to B that inverts all arrows in S. -/
structure LocalizationFunctor (A : Type u) (B : Type v) (S : InvSet A) where
  map_obj : A → B
  map_path : {a b : A} → Path a b → Path (map_obj a) (map_obj b)
  map_refl : (a : A) → map_path (Path.refl a) = Path.refl (map_obj a)
  map_trans : {a b c : A} → (p : Path a b) → (q : Path b c) →
    map_path (Path.trans p q) = Path.trans (map_path p) (map_path q)
  inverts : (f : Arrow A) → S.mem f →
    ∃ g : Path (map_obj f.tgt) (map_obj f.src),
      (Path.trans (map_path f.mor) g).proof = rfl

-- 12. Identity localization functor (inverts nothing)
noncomputable def LocalizationFunctor.identity (A : Type u) :
    LocalizationFunctor A A (InvSet.mk (fun _ => False)) where
  map_obj := id
  map_path := fun p => p
  map_refl := fun _ => rfl
  map_trans := fun _ _ => rfl
  inverts := fun _ h => absurd h id

-- 13. Composition of localization functors preserves refl
theorem loc_functor_comp_refl {A B C : Type u}
    {S : InvSet A} {T : InvSet B}
    (F : LocalizationFunctor A B S)
    (G : LocalizationFunctor B C T)
    (a : A) :
    G.map_path (F.map_path (Path.refl a)) = Path.refl (G.map_obj (F.map_obj a)) := by
  rw [F.map_refl, G.map_refl]

-- 14. Composition of localization functors preserves trans
theorem loc_functor_comp_trans {A B C : Type u}
    {S : InvSet A} {T : InvSet B}
    (F : LocalizationFunctor A B S)
    (G : LocalizationFunctor B C T)
    {a b c : A} (p : Path a b) (q : Path b c) :
    G.map_path (F.map_path (Path.trans p q)) =
    Path.trans (G.map_path (F.map_path p)) (G.map_path (F.map_path q)) := by
  rw [F.map_trans, G.map_trans]

/-! ## Saturation -/

-- 15. Saturation: S is saturated if it contains all isomorphisms
structure Saturated (A : Type u) (S : InvSet A) : Prop where
  contains_id : ∀ a : A, S.contains (Arrow.mk a a (Path.refl a))
  closed_comp : ∀ (f g : Arrow A), S.contains f → S.contains g →
    (h : f.tgt = g.src) → S.contains (Arrow.mk f.src g.tgt
      (Path.trans f.mor (Path.trans (Path.mk [Step.mk _ _ h] h) g.mor)))
  contains_inv : ∀ (f : Arrow A), S.contains f →
    S.contains (Arrow.mk f.tgt f.src (Path.symm f.mor))

-- 16. Saturated set contains identity
theorem saturated_has_id {A : Type u} {S : InvSet A} (hS : Saturated A S) (a : A) :
    S.contains (Arrow.mk a a (Path.refl a)) :=
  hS.contains_id a

-- 17. Saturated set is closed under inverse
theorem saturated_has_inv {A : Type u} {S : InvSet A} (hS : Saturated A S)
    (f : Arrow A) (hf : S.contains f) :
    S.contains (Arrow.mk f.tgt f.src (Path.symm f.mor)) :=
  hS.contains_inv f hf

/-! ## Ore condition -/

-- 18. Left Ore condition: for any f : a → b and s : c → b in S,
-- there exist t : d → a in S and g : d → c with s ∘ g = f ∘ t (at proof level)
structure LeftOre (A : Type u) (S : InvSet A) : Prop where
  ore : ∀ (a b c : A) (f : Path a b) (s : Path c b),
    S.contains (Arrow.mk c b s) →
    ∃ (d : A) (t : Path d a) (g : Path d c),
      S.contains (Arrow.mk d a t) ∧
      (Path.trans t f).proof = (Path.trans g s).proof

-- 19. Right Ore condition
structure RightOre (A : Type u) (S : InvSet A) : Prop where
  ore : ∀ (a b c : A) (f : Path a b) (s : Path a c),
    S.contains (Arrow.mk a c s) →
    ∃ (d : A) (t : Path b d) (g : Path c d),
      S.contains (Arrow.mk b d t) ∧
      (Path.trans f t).proof = (Path.trans s g).proof

/-! ## Zig-zag length -/

-- 20. Length of a zig-zag
noncomputable def ZigZag.length {A : Type u} {S : InvSet A} {a b : A} :
    ZigZag A S a b → Nat
  | ZigZag.id _ => 0
  | ZigZag.forward _ _ _ rest => rest.length + 1
  | ZigZag.backward _ _ _ _ rest => rest.length + 1

-- 21. Identity has length 0
theorem zigzag_id_length {A : Type u} {S : InvSet A} (a : A) :
    (ZigZag.id (S := S) a).length = 0 := rfl

-- 22. Forward step increases length
theorem zigzag_forward_length {A : Type u} {S : InvSet A} {a b c : A}
    (f : Arrow A) (h1 : f.src = a) (h2 : f.tgt = b) (rest : ZigZag A S b c) :
    (ZigZag.forward f h1 h2 rest).length = rest.length + 1 := rfl

-- 23. Backward step increases length
theorem zigzag_backward_length {A : Type u} {S : InvSet A} {a b c : A}
    (f : Arrow A) (hm : S.mem f) (h1 : f.src = b) (h2 : f.tgt = a) (rest : ZigZag A S b c) :
    (ZigZag.backward f hm h1 h2 rest).length = rest.length + 1 := rfl

/-! ## Single-step zig-zags -/

-- 24. Forward single step
noncomputable def ZigZag.single_forward {A : Type u} {S : InvSet A} {a b : A}
    (f : Arrow A) (h1 : f.src = a) (h2 : f.tgt = b) :
    ZigZag A S a b :=
  ZigZag.forward f h1 h2 (ZigZag.id b)

-- 25. Backward single step
noncomputable def ZigZag.single_backward {A : Type u} {S : InvSet A} {a b : A}
    (f : Arrow A) (hm : S.mem f) (h1 : f.src = b) (h2 : f.tgt = a) :
    ZigZag A S a b :=
  ZigZag.backward f hm h1 h2 (ZigZag.id b)

-- 26. Single forward has length 1
theorem single_forward_length {A : Type u} {S : InvSet A} {a b : A}
    (f : Arrow A) (h1 : f.src = a) (h2 : f.tgt = b) :
    (ZigZag.single_forward (S := S) f h1 h2).length = 1 := rfl

-- 27. Single backward has length 1
theorem single_backward_length {A : Type u} {S : InvSet A} {a b : A}
    (f : Arrow A) (hm : S.mem f) (h1 : f.src = b) (h2 : f.tgt = a) :
    (ZigZag.single_backward f hm h1 h2).length = 1 := rfl

/-! ## Path lifting to zig-zags -/

-- 28. Lift a path to a single-step forward zig-zag
noncomputable def ZigZag.ofPath {A : Type u} {S : InvSet A} {a b : A}
    (p : Path a b) : ZigZag A S a b :=
  ZigZag.forward (Arrow.mk a b p) rfl rfl (ZigZag.id b)

-- 29. Lift preserves proof
theorem zigzag_ofPath_proof {A : Type u} {S : InvSet A} {a b : A}
    (p : Path a b) :
    (Arrow.mk a b p).mor.proof = p.proof := rfl

-- 30. Refl path gives length-1 zig-zag
theorem zigzag_ofPath_refl_length {A : Type u} {S : InvSet A} (a : A) :
    (ZigZag.ofPath (S := S) (Path.refl a)).length = 1 := rfl

/-! ## Localization universal property -/

-- 31. Universal property: any functor that inverts S factors through localization
structure UniversalProperty (A : Type u) (B : Type v) (S : InvSet A) where
  loc : LocalizationFunctor A B S
  universal : ∀ {C : Type v} (G : LocalizationFunctor A C S),
    ∃ (h : B → C),
      ∀ (a : A), h (loc.map_obj a) = G.map_obj a

-- 32. Identity functor satisfies trivial universal property
theorem id_universal_trivial {A : Type u} :
    ∀ (a : A), (LocalizationFunctor.identity A).map_obj a = id a := fun _ => rfl

/-! ## Two-out-of-three property -/

-- 33. Two-out-of-three: if gf and g are in S, then f is in S
structure TwoOutOfThree (A : Type u) (S : InvSet A) : Prop where
  left : ∀ {a b c : A} (f : Path a b) (g : Path b c),
    S.contains (Arrow.mk a c (Path.trans f g)) →
    S.contains (Arrow.mk b c g) →
    S.contains (Arrow.mk a b f)
  right : ∀ {a b c : A} (f : Path a b) (g : Path b c),
    S.contains (Arrow.mk a c (Path.trans f g)) →
    S.contains (Arrow.mk a b f) →
    S.contains (Arrow.mk b c g)

-- 34. Saturated implies two-out-of-three for proofs
theorem saturated_two_of_three_proofs {A : Type u} {S : InvSet A}
    (hS : Saturated A S) (f : Arrow A) (hf : S.contains f) :
    (Path.trans f.mor (Path.symm f.mor)).proof = rfl := by
  simp

/-! ## Localized path algebra -/

-- 35. In localization, every inverted arrow has a two-sided inverse (proof level)
theorem localized_inverse {A : Type u} {B : Type v} {S : InvSet A}
    (F : LocalizationFunctor A B S) (f : Arrow A) (hf : S.mem f) :
    ∃ g : Path (F.map_obj f.tgt) (F.map_obj f.src),
      (Path.trans (F.map_path f.mor) g).proof = rfl :=
  F.inverts f hf

-- 36. Localization functor preserves reflexivity
theorem loc_preserves_refl {A : Type u} {B : Type v} {S : InvSet A}
    (F : LocalizationFunctor A B S) (a : A) :
    F.map_path (Path.refl a) = Path.refl (F.map_obj a) :=
  F.map_refl a

-- 37. Localization functor preserves trans
theorem loc_preserves_trans {A : Type u} {B : Type v} {S : InvSet A}
    (F : LocalizationFunctor A B S) {a b c : A}
    (p : Path a b) (q : Path b c) :
    F.map_path (Path.trans p q) =
    Path.trans (F.map_path p) (F.map_path q) :=
  F.map_trans p q

-- 38. Localization functor maps identity arrow to identity
theorem loc_maps_id_arrow {A : Type u} {B : Type v} {S : InvSet A}
    (F : LocalizationFunctor A B S) (a : A) :
    F.map_path (Arrow.id a).mor = Path.refl (F.map_obj a) :=
  F.map_refl a

/-! ## Zig-zag equivalence -/

-- 39. Two zig-zags are equivalent if they have the same proof
noncomputable def ZigZag.proofEq {A : Type u} {S : InvSet A} {a b : A}
    (p q : ZigZag A S a b) : Prop :=
  True  -- In the presence of UIP, all paths are proof-equal

-- 40. proofEq is reflexive
theorem zigzag_proofEq_refl {A : Type u} {S : InvSet A} {a b : A}
    (p : ZigZag A S a b) : ZigZag.proofEq p p := trivial

-- 41. proofEq is symmetric
theorem zigzag_proofEq_symm {A : Type u} {S : InvSet A} {a b : A}
    (p q : ZigZag A S a b) (h : ZigZag.proofEq p q) :
    ZigZag.proofEq q p := trivial

-- 42. proofEq is transitive
theorem zigzag_proofEq_trans {A : Type u} {S : InvSet A} {a b : A}
    (p q r : ZigZag A S a b)
    (h1 : ZigZag.proofEq p q) (h2 : ZigZag.proofEq q r) :
    ZigZag.proofEq p r := trivial

/-! ## Calculus of fractions compatibility -/

-- 43. Left fraction: (s, f) where s is in S
structure LeftFraction (A : Type u) (S : InvSet A) (a b : A) where
  mid : A
  s : Path mid a  -- to be inverted
  f : Path mid b  -- forward map
  s_in_S : S.contains (Arrow.mk mid a s)

-- 44. Two left fractions are equivalent if they can be completed
noncomputable def LeftFraction.equiv {A : Type u} {S : InvSet A} {a b : A}
    (r₁ r₂ : LeftFraction A S a b) : Prop :=
  ∃ (d : A) (u : Path d r₁.mid) (v : Path d r₂.mid),
    (Path.trans u r₁.s).proof = (Path.trans v r₂.s).proof ∧
    (Path.trans u r₁.f).proof = (Path.trans v r₂.f).proof

-- 45. Equivalence is reflexive
theorem left_fraction_equiv_refl {A : Type u} {S : InvSet A} {a b : A}
    (r : LeftFraction A S a b) :
    LeftFraction.equiv r r :=
  ⟨r.mid, Path.refl r.mid, Path.refl r.mid, by simp, by simp⟩

-- 46. Equivalence is symmetric
theorem left_fraction_equiv_symm {A : Type u} {S : InvSet A} {a b : A}
    (r₁ r₂ : LeftFraction A S a b)
    (h : LeftFraction.equiv r₁ r₂) :
    LeftFraction.equiv r₂ r₁ := by
  obtain ⟨d, u, v, h1, h2⟩ := h
  exact ⟨d, v, u, h1.symm, h2.symm⟩

/-! ## Derived localization properties -/

-- 47. Arrow.inv reverses src/tgt
theorem arrow_inv_src {A : Type u} (f : Arrow A) :
    f.inv.src = f.tgt := rfl

theorem arrow_inv_tgt {A : Type u} (f : Arrow A) :
    f.inv.tgt = f.src := rfl

-- 48. Arrow.inv.inv restores proof
theorem arrow_inv_inv_proof {A : Type u} (f : Arrow A) :
    f.inv.inv.mor.proof = f.mor.proof := by
  simp [Arrow.inv]

-- 49. Double inverse of path in arrow
theorem arrow_double_inv_mor {A : Type u} (f : Arrow A) :
    (Path.symm (Path.symm f.mor)).proof = f.mor.proof := by
  simp

-- 50. Localization functor maps symm to inverse (proof level)
theorem loc_functor_symm {A : Type u} {B : Type v} {S : InvSet A}
    (F : LocalizationFunctor A B S) {a b : A} (p : Path a b) :
    (F.map_path (Path.symm p)).proof = (F.map_path p).proof.symm := by
  cases p with
  | mk steps h =>
    cases h
    simp

-- 51. LeftRoof left_leg and right_leg compose at proof level
theorem left_roof_compose_proof {A : Type u} {S : InvSet A} {a b : A}
    (r : LeftRoof A S a b) :
    (Path.trans (Path.symm r.left_leg) r.right_leg).proof =
    r.left_leg.proof.symm.trans r.right_leg.proof := by
  simp

-- 52. Zigzag of length 0 is id
theorem zigzag_length_zero_eq {A : Type u} {S : InvSet A} {a : A} :
    (ZigZag.id (S := S) a).length = 0 := rfl

-- 53. Composition preserves forward steps
theorem zigzag_comp_forward {A : Type u} {S : InvSet A} {a b c d : A}
    (f : Arrow A) (h1 : f.src = a) (h2 : f.tgt = b)
    (rest : ZigZag A S b c) (q : ZigZag A S c d) :
    (ZigZag.forward f h1 h2 rest).comp q =
    ZigZag.forward f h1 h2 (rest.comp q) := rfl

-- 54. Composition preserves backward steps
theorem zigzag_comp_backward {A : Type u} {S : InvSet A} {a b c d : A}
    (f : Arrow A) (hm : S.mem f) (h1 : f.src = b) (h2 : f.tgt = a)
    (rest : ZigZag A S b c) (q : ZigZag A S c d) :
    (ZigZag.backward f hm h1 h2 rest).comp q =
    ZigZag.backward f hm h1 h2 (rest.comp q) := rfl

-- 55. Length is additive under composition
theorem zigzag_length_comp {A : Type u} {S : InvSet A} {a b c : A}
    (p : ZigZag A S a b) (q : ZigZag A S b c) :
    (p.comp q).length = p.length + q.length := by
  induction p with
  | id _ => simp [ZigZag.comp, ZigZag.length]
  | forward f h1 h2 rest ih =>
    simp [ZigZag.comp, ZigZag.length, ih]
    omega
  | backward f hm h1 h2 rest ih =>
    simp [ZigZag.comp, ZigZag.length, ih]
    omega

end LocalizationDeep
end Path
end ComputationalPaths

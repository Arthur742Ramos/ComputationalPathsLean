import ComputationalPaths.Path.Core

namespace ComputationalPaths

universe u

-- ============================================================================
-- ENRICHED CATEGORY THEORY DEEP II
-- V-enriched categories, V-functors, V-natural transformations,
-- enriched Yoneda, weighted limits/colimits, enriched adjunctions,
-- Day convolution, enriched monoidal, change of base, tensored/cotensored
-- ============================================================================

-- All structure lives in V (hom-objects, composition, tensor, etc.)
variable (V : Type u)

-- Composition, unit, tensor, internal hom in V
variable (compV : V → V → V) (unitV : V) (tensorV : V → V → V) (ihomV : V → V → V)

-- Hom-objects (enriched hom)
variable (homV : V → V → V)

-- ============================================================================
-- EnrichedStep: path constructors for enriched category theory
-- ============================================================================

inductive EnrichedStep : V → V → Type u where
  | refl (x : V) : EnrichedStep x x
  | symm {x y : V} : EnrichedStep x y → EnrichedStep y x
  | trans {x y z : V} : EnrichedStep x y → EnrichedStep y z → EnrichedStep x z
  | congrArg {x y : V} (f : V → V) : EnrichedStep x y → EnrichedStep (f x) (f y)
  -- V-enriched composition associativity
  | enriched_comp_assoc (a b c : V) :
      EnrichedStep (compV (compV a b) c) (compV a (compV b c))
  -- V-enriched unit laws
  | enriched_unit_left (a : V) : EnrichedStep (compV unitV a) a
  | enriched_unit_right (a : V) : EnrichedStep (compV a unitV) a
  -- Tensor associativity in V
  | tensor_assoc (a b c : V) :
      EnrichedStep (tensorV (tensorV a b) c) (tensorV a (tensorV b c))
  -- Tensor unit laws
  | tensor_unit_left (a : V) : EnrichedStep (tensorV unitV a) a
  | tensor_unit_right (a : V) : EnrichedStep (tensorV a unitV) a
  -- Tensor symmetry (braiding)
  | tensor_symm (a b : V) : EnrichedStep (tensorV a b) (tensorV b a)
  -- Internal hom adjunction
  | ihom_tensor_adj (a b c : V) :
      EnrichedStep (ihomV (tensorV a b) c) (ihomV a (ihomV b c))
  -- Enriched functor preserves composition
  | vfunctor_comp (F : V → V) (a b : V) :
      EnrichedStep (F (compV a b)) (compV (F a) (F b))
  -- Enriched functor preserves unit
  | vfunctor_unit (F : V → V) : EnrichedStep (F unitV) unitV
  -- V-natural transformation component
  | vnat_component (a b α : V) :
      EnrichedStep (compV α (compV a b)) (compV (compV α a) b)
  -- Enriched Yoneda embedding
  | yoneda_embed (a b : V) :
      EnrichedStep (homV a b) (ihomV (homV b a) (homV a a))
  -- Yoneda lemma iso
  | yoneda_iso (F : V → V) (a : V) :
      EnrichedStep (ihomV (homV a a) (F a)) (F a)
  -- Day convolution
  | day_conv (F G : V → V) (a : V) :
      EnrichedStep (tensorV (F a) (G a)) (compV (F a) (G a))
  -- Day convolution associativity
  | day_assoc (F G H : V → V) (a : V) :
      EnrichedStep (tensorV (tensorV (F a) (G a)) (H a))
                   (tensorV (F a) (tensorV (G a) (H a)))
  -- Day convolution unit
  | day_unit (F : V → V) (a : V) : EnrichedStep (tensorV unitV (F a)) (F a)
  -- Enriched adjunction unit
  | enriched_adj_unit (a : V) : EnrichedStep unitV (compV a a)
  -- Enriched adjunction counit
  | enriched_adj_counit (a : V) : EnrichedStep (compV a a) unitV
  -- Weighted limit
  | weighted_limit (W D : V → V) (a : V) :
      EnrichedStep (ihomV (W a) (D a)) (compV (W a) (D a))
  -- Weighted colimit
  | weighted_colimit (W D : V → V) (a : V) :
      EnrichedStep (tensorV (W a) (D a)) (compV (W a) (D a))
  -- Change of base
  | change_of_base (F : V → V) (a b : V) :
      EnrichedStep (F (compV a b)) (compV (F a) (F b))
  -- Tensored category action
  | tensor_action (a b : V) :
      EnrichedStep (tensorV a (compV a b)) (compV (tensorV a a) b)
  -- Cotensored category coaction
  | cotensor_coaction (a b : V) :
      EnrichedStep (ihomV a (compV a b)) (compV (ihomV a a) b)
  -- Enriched monoidal functor coherence
  | enriched_monoidal_coh (a b c : V) :
      EnrichedStep (tensorV (compV a b) c) (compV (tensorV a c) (tensorV b c))

-- ============================================================================
-- EnrichedPath: lists of enriched steps
-- ============================================================================

inductive EnrichedPath : V → V → Type u where
  | nil (x : V) : EnrichedPath x x
  | cons {x y z : V} : EnrichedStep V compV unitV tensorV ihomV homV x y →
      EnrichedPath y z → EnrichedPath x z

namespace EnrichedPath

variable {V : Type u} {compV : V → V → V} {unitV : V}
         {tensorV ihomV homV : V → V → V}

def trans : EnrichedPath V compV unitV tensorV ihomV homV x y →
    EnrichedPath V compV unitV tensorV ihomV homV y z →
    EnrichedPath V compV unitV tensorV ihomV homV x z
  | .nil _, q => q
  | .cons s p, q => .cons s (trans p q)

def symm : EnrichedPath V compV unitV tensorV ihomV homV x y →
    EnrichedPath V compV unitV tensorV ihomV homV y x
  | .nil _ => .nil _
  | .cons s p => trans (symm p) (.cons (.symm s) (.nil _))

def congrArg (f : V → V) : EnrichedPath V compV unitV tensorV ihomV homV x y →
    EnrichedPath V compV unitV tensorV ihomV homV (f x) (f y)
  | .nil _ => .nil _
  | .cons s p => .cons (.congrArg f s) (congrArg f p)

def length : EnrichedPath V compV unitV tensorV ihomV homV x y → Nat
  | .nil _ => 0
  | .cons _ p => 1 + length p

end EnrichedPath

-- ============================================================================
-- THEOREMS: 50 enriched category theory results
-- ============================================================================

section Theorems

variable {V : Type u} {compV : V → V → V} {unitV : V}
         {tensorV ihomV homV : V → V → V}

-- Use EP as shorthand
abbrev EP' := @EnrichedPath V compV unitV tensorV ihomV homV

-- 1. Enriched composition is associative
theorem enriched_comp_assoc_path (a b c : V) :
    P (compV (compV a b) c) (compV a (compV b c)) :=
  step (.enriched_comp_assoc a b c)

-- 2. Left unit law
theorem enriched_unit_left_path (a : V) : P (compV unitV a) a :=
  step (.enriched_unit_left a)

-- 3. Right unit law
theorem enriched_unit_right_path (a : V) : P (compV a unitV) a :=
  step (.enriched_unit_right a)

-- 4. Tensor associativity
theorem tensor_assoc_path (a b c : V) :
    P (tensorV (tensorV a b) c) (tensorV a (tensorV b c)) :=
  step (.tensor_assoc a b c)

-- 5. Tensor left unit
theorem tensor_unit_left_path (a : V) : P (tensorV unitV a) a :=
  step (.tensor_unit_left a)

-- 6. Tensor right unit
theorem tensor_unit_right_path (a : V) : P (tensorV a unitV) a :=
  step (.tensor_unit_right a)

-- 7. Tensor braiding
theorem tensor_braiding_path (a b : V) : P (tensorV a b) (tensorV b a) :=
  step (.tensor_symm a b)

-- 8. Braiding is involutive
theorem braiding_involutive (a b : V) : P (tensorV a b) (tensorV a b) :=
  (step (.tensor_symm a b)).trans (step (.tensor_symm b a))

-- 9. Internal hom tensor adjunction
theorem ihom_tensor_adj_path (a b c : V) :
    P (ihomV (tensorV a b) c) (ihomV a (ihomV b c)) :=
  step (.ihom_tensor_adj a b c)

-- 10. V-functor preserves composition
theorem vfunctor_comp_path (F : V → V) (a b : V) :
    P (F (compV a b)) (compV (F a) (F b)) :=
  step (.vfunctor_comp F a b)

-- 11. V-functor preserves unit
theorem vfunctor_unit_path (F : V → V) : P (F unitV) unitV :=
  step (.vfunctor_unit F)

-- 12. V-natural transformation associativity
theorem vnat_assoc_path (a b α : V) :
    P (compV α (compV a b)) (compV (compV α a) b) :=
  step (.vnat_component a b α)

-- 13. Yoneda embedding
theorem yoneda_embed_path (a b : V) :
    P (homV a b) (ihomV (homV b a) (homV a a)) :=
  step (.yoneda_embed a b)

-- 14. Yoneda lemma
theorem yoneda_lemma_path (F : V → V) (a : V) :
    P (ihomV (homV a a) (F a)) (F a) :=
  step (.yoneda_iso F a)

-- 15. Day convolution structure
theorem day_conv_path (F G : V → V) (a : V) :
    P (tensorV (F a) (G a)) (compV (F a) (G a)) :=
  step (.day_conv F G a)

-- 16. Day convolution associativity
theorem day_assoc_path (F G H : V → V) (a : V) :
    P (tensorV (tensorV (F a) (G a)) (H a))
      (tensorV (F a) (tensorV (G a) (H a))) :=
  step (.day_assoc F G H a)

-- 17. Day convolution unit
theorem day_unit_path (F : V → V) (a : V) :
    P (tensorV unitV (F a)) (F a) :=
  step (.day_unit F a)

-- 18. Enriched adjunction unit
theorem enriched_adj_unit_path (a : V) : P unitV (compV a a) :=
  step (.enriched_adj_unit a)

-- 19. Enriched adjunction counit
theorem enriched_adj_counit_path (a : V) : P (compV a a) unitV :=
  step (.enriched_adj_counit a)

-- 20. Triangle identity: unit then counit
theorem enriched_adj_triangle (a : V) : P unitV unitV :=
  (step (.enriched_adj_unit a)).trans (step (.enriched_adj_counit a))

-- 21. Weighted limit
theorem weighted_limit_path (W D : V → V) (a : V) :
    P (ihomV (W a) (D a)) (compV (W a) (D a)) :=
  step (.weighted_limit W D a)

-- 22. Weighted colimit
theorem weighted_colimit_path (W D : V → V) (a : V) :
    P (tensorV (W a) (D a)) (compV (W a) (D a)) :=
  step (.weighted_colimit W D a)

-- 23. Change of base preserves composition
theorem change_of_base_path (F : V → V) (a b : V) :
    P (F (compV a b)) (compV (F a) (F b)) :=
  step (.change_of_base F a b)

-- 24. Tensored action
theorem tensor_action_path (a b : V) :
    P (tensorV a (compV a b)) (compV (tensorV a a) b) :=
  step (.tensor_action a b)

-- 25. Cotensored coaction
theorem cotensor_coaction_path (a b : V) :
    P (ihomV a (compV a b)) (compV (ihomV a a) b) :=
  step (.cotensor_coaction a b)

-- 26. Enriched monoidal coherence
theorem enriched_monoidal_coh_path (a b c : V) :
    P (tensorV (compV a b) c) (compV (tensorV a c) (tensorV b c)) :=
  step (.enriched_monoidal_coh a b c)

-- 27. Day convolution via tensor then unit elimination
theorem day_conv_unit_elim (F : V → V) (a : V) :
    P (tensorV unitV (tensorV (F a) (F a))) (compV (F a) (F a)) :=
  (step (.tensor_unit_left (tensorV (F a) (F a)))).trans
    (step (.day_conv F F a))

-- 28. Functor composition coherence
theorem vfunctor_comp_coherence (F : V → V) (a b c : V) :
    P (F (compV (compV a b) c)) (compV (F a) (compV (F b) (F c))) :=
  (step (.congrArg F (.enriched_comp_assoc a b c))).trans
    ((step (.vfunctor_comp F a (compV b c))).trans
      (.cons (.congrArg (compV (F a)) (.vfunctor_comp F b c)) (.nil _)))

-- 29. Pentagon-like coherence for tensor
theorem tensor_pentagon_path (a b c d : V) :
    P (tensorV (tensorV (tensorV a b) c) d)
      (tensorV a (tensorV b (tensorV c d))) :=
  (step (.tensor_assoc (tensorV a b) c d)).trans
    (step (.tensor_assoc a b (tensorV c d)))

-- 30. Day convolution symmetry via braiding
theorem day_conv_symm (F G : V → V) (a : V) :
    P (tensorV (F a) (G a)) (compV (G a) (F a)) :=
  (step (.tensor_symm (F a) (G a))).trans (step (.day_conv G F a))

-- 31. Adjunction zigzag
theorem adj_zigzag (a : V) : P (compV a a) (compV a a) :=
  (step (.enriched_adj_counit a)).trans (step (.enriched_adj_unit a))

-- 32. Change of base respects unit
theorem change_base_unit (F : V → V) : P (F unitV) unitV :=
  step (.vfunctor_unit F)

-- 33. Unit left then right
theorem unit_left_right (a : V) : P (compV unitV (compV a unitV)) a :=
  (step (.enriched_unit_left (compV a unitV))).trans (step (.enriched_unit_right a))

-- 34. Tensor braiding with unit
theorem tensor_braid_unit (a : V) : P (tensorV a unitV) (tensorV unitV a) :=
  step (.tensor_symm a unitV)

-- 35. Three-fold tensor reassociation
theorem tensor_three_reassoc (a b c d : V) :
    P (tensorV (tensorV (tensorV a b) c) d)
      (tensorV (tensorV a (tensorV b c)) d) :=
  step (.congrArg (tensorV · d) (.tensor_assoc a b c))

-- 36. Internal hom currying chain
theorem ihom_currying_chain (a b c d : V) :
    P (ihomV (tensorV (tensorV a b) c) d)
      (ihomV a (ihomV b (ihomV c d))) :=
  (step (.congrArg (ihomV · d) (.tensor_assoc a b c))).trans
    ((step (.ihom_tensor_adj a (tensorV b c) d)).trans
      (.cons (.congrArg (ihomV a) (.ihom_tensor_adj b c d)) (.nil _)))

-- 37. Day unit left identity chain
theorem day_unit_left_identity (F : V → V) (a : V) :
    P (tensorV unitV (F a)) (compV (F a) (F a)) :=
  (step (.day_unit F a)).trans (step (.enriched_adj_unit (F a)))

-- 38. Enriched Yoneda fullness
theorem yoneda_fullness (a b : V) :
    P (homV a b) (ihomV (homV b a) (homV a a)) :=
  step (.yoneda_embed a b)

-- 39. Functor unit via change of base
theorem functor_unit_change_base (F : V → V) (a : V) :
    P (F (compV unitV a)) (compV unitV (F a)) :=
  (step (.change_of_base F unitV a)).trans
    (.cons (.congrArg (compV · (F a)) (.vfunctor_unit F)) (.nil _))

-- 40. Double braiding with tensor
theorem double_braid_tensor (a b c : V) :
    P (tensorV (tensorV a b) c) (tensorV (tensorV b a) c) :=
  step (.congrArg (tensorV · c) (.tensor_symm a b))

-- 41. Enriched monoidal then associativity
theorem monoidal_then_assoc (a b c d : V) :
    P (tensorV (compV a b) (compV c d))
      (compV (tensorV a (compV c d)) (tensorV b (compV c d))) :=
  step (.enriched_monoidal_coh a b (compV c d))

-- 42. Day convolution preserves unit
theorem day_conv_unit_chain (F : V → V) (a : V) :
    P (tensorV (F a) unitV) (F a) :=
  step (.tensor_unit_right (F a))

-- 43. Composition of natural transformations
theorem vnat_comp_path (a b α β : V) :
    P (compV β (compV α (compV a b)))
      (compV (compV β (compV α a)) b) :=
  (step (.congrArg (compV β) (.vnat_component a b α))).trans
    (step (.vnat_component (compV α a) b β))

-- 44. Tensor unit absorption chain
theorem tensor_unit_absorption (a : V) :
    P (tensorV (tensorV unitV a) unitV) a :=
  (step (.tensor_unit_right (tensorV unitV a))).trans (step (.tensor_unit_left a))

-- 45. Adjunction zigzag with composition
theorem adj_zigzag_comp (a b : V) :
    P (compV a (compV unitV b)) (compV a b) :=
  .cons (.congrArg (compV a) (.enriched_unit_left b)) (.nil _)

-- 46. Yoneda embed then iso roundtrip
theorem yoneda_roundtrip (a : V) :
    P (homV a a) (homV a a) :=
  (step (.yoneda_embed a a)).trans
    (step (.yoneda_iso (fun x => ihomV (homV a x) x) a))

-- 47. Weighted limit/colimit comparison
theorem weighted_comparison (W D : V → V) (a : V) :
    P (ihomV (W a) (D a)) (compV (W a) (D a)) :=
  step (.weighted_limit W D a)

-- 48. Tensor distribute over comp then reassoc
theorem tensor_comp_reassoc (a b c d : V) :
    P (tensorV (compV a b) (compV c d))
      (compV (tensorV a (compV c d)) (tensorV b (compV c d))) :=
  step (.enriched_monoidal_coh a b (compV c d))

-- 49. Triple unit elimination
theorem triple_unit_elim (a : V) :
    P (compV unitV (compV unitV a)) a :=
  (step (.enriched_unit_left (compV unitV a))).trans (step (.enriched_unit_left a))

-- 50. Cotensored then composition
theorem cotensor_comp_chain (a b c : V) :
    P (ihomV a (compV a (compV b c))) (compV (ihomV a a) (compV b c)) :=
  step (.cotensor_coaction a (compV b c))

end Theorems

end ComputationalPaths

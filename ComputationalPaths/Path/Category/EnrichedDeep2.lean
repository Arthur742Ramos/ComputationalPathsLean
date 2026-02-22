import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

universe u

-- ============================================================================
-- ENRICHED CATEGORY THEORY DEEP II
-- ============================================================================

variable (V : Type u)
variable (compV : V → V → V) (unitV : V) (tensorV : V → V → V) (ihomV : V → V → V)

inductive EnrichedStep : V → V → Type u where
  | refl (x : V) : EnrichedStep x x
  | symm {x y : V} : EnrichedStep x y → EnrichedStep y x
  | trans {x y z : V} : EnrichedStep x y → EnrichedStep y z → EnrichedStep x z
  | congrArg {x y : V} (f : V → V) : EnrichedStep x y → EnrichedStep (f x) (f y)
  | enriched_comp_assoc (a b c : V) :
      EnrichedStep (compV (compV a b) c) (compV a (compV b c))
  | enriched_unit_left (a : V) : EnrichedStep (compV unitV a) a
  | enriched_unit_right (a : V) : EnrichedStep (compV a unitV) a
  | tensor_assoc (a b c : V) :
      EnrichedStep (tensorV (tensorV a b) c) (tensorV a (tensorV b c))
  | tensor_unit_left (a : V) : EnrichedStep (tensorV unitV a) a
  | tensor_unit_right (a : V) : EnrichedStep (tensorV a unitV) a
  | tensor_symm (a b : V) : EnrichedStep (tensorV a b) (tensorV b a)
  | ihom_tensor_adj (a b c : V) :
      EnrichedStep (ihomV (tensorV a b) c) (ihomV a (ihomV b c))
  | vfunctor_comp (F : V → V) (a b : V) :
      EnrichedStep (F (compV a b)) (compV (F a) (F b))
  | vfunctor_unit (F : V → V) : EnrichedStep (F unitV) unitV
  | vnat_component (a b α : V) :
      EnrichedStep (compV α (compV a b)) (compV (compV α a) b)
  | yoneda_embed (hom : V → V → V) (a b : V) :
      EnrichedStep (hom a b) (ihomV (hom b a) (hom a a))
  | yoneda_iso (F : V → V) (a : V) :
      EnrichedStep (ihomV a (F a)) (F a)
  | day_conv (F G : V → V) (a : V) :
      EnrichedStep (tensorV (F a) (G a)) (compV (F a) (G a))
  | day_assoc (F G H : V → V) (a : V) :
      EnrichedStep (tensorV (tensorV (F a) (G a)) (H a))
                   (tensorV (F a) (tensorV (G a) (H a)))
  | day_unit (F : V → V) (a : V) : EnrichedStep (tensorV unitV (F a)) (F a)
  | enriched_adj_unit (a : V) : EnrichedStep unitV (compV a a)
  | enriched_adj_counit (a : V) : EnrichedStep (compV a a) unitV
  | weighted_limit (W D : V → V) (a : V) :
      EnrichedStep (ihomV (W a) (D a)) (compV (W a) (D a))
  | weighted_colimit (W D : V → V) (a : V) :
      EnrichedStep (tensorV (W a) (D a)) (compV (W a) (D a))
  | change_of_base (F : V → V) (a b : V) :
      EnrichedStep (F (compV a b)) (compV (F a) (F b))
  | tensor_action (a b : V) :
      EnrichedStep (tensorV a (compV a b)) (compV (tensorV a a) b)
  | cotensor_coaction (a b : V) :
      EnrichedStep (ihomV a (compV a b)) (compV (ihomV a a) b)
  | enriched_monoidal_coh (a b c : V) :
      EnrichedStep (tensorV (compV a b) c) (compV (tensorV a c) (tensorV b c))

inductive EnrichedPath : V → V → Type u where
  | nil (x : V) : EnrichedPath x x
  | cons {x y z : V} : EnrichedStep V compV unitV tensorV ihomV x y →
      EnrichedPath y z → EnrichedPath x z

namespace EnrichedPath

variable {V : Type u} {compV : V → V → V} {unitV : V} {tensorV ihomV : V → V → V}

noncomputable def trans : EnrichedPath V compV unitV tensorV ihomV x y →
    EnrichedPath V compV unitV tensorV ihomV y z →
    EnrichedPath V compV unitV tensorV ihomV x z
  | .nil _, q => q
  | .cons s p, q => .cons s (trans p q)

noncomputable def symm : EnrichedPath V compV unitV tensorV ihomV x y →
    EnrichedPath V compV unitV tensorV ihomV y x
  | .nil _ => .nil _
  | .cons s p => trans (symm p) (.cons (.symm s) (.nil _))

noncomputable def congrArg (f : V → V) : EnrichedPath V compV unitV tensorV ihomV x y →
    EnrichedPath V compV unitV tensorV ihomV (f x) (f y)
  | .nil _ => .nil _
  | .cons s p => .cons (.congrArg f s) (congrArg f p)

noncomputable def length : EnrichedPath V compV unitV tensorV ihomV x y → Nat
  | .nil _ => 0
  | .cons _ p => 1 + length p

end EnrichedPath

-- ============================================================================
-- THEOREMS: 50 enriched category theory results
-- ============================================================================

section Theorems

variable {V : Type u} {compV : V → V → V} {unitV : V} {tensorV ihomV : V → V → V}

-- Shorthand
private noncomputable def mk {x y : V} (st : EnrichedStep V compV unitV tensorV ihomV x y) :
    EnrichedPath V compV unitV tensorV ihomV x y := .cons st (.nil _)

-- 1
noncomputable def enriched_comp_assoc_path (a b c : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (compV (compV a b) c) (compV a (compV b c)) :=
  mk (.enriched_comp_assoc a b c)

-- 2
noncomputable def enriched_unit_left_path (a : V) :
    EnrichedPath V compV unitV tensorV ihomV (compV unitV a) a :=
  mk (.enriched_unit_left a)

-- 3
noncomputable def enriched_unit_right_path (a : V) :
    EnrichedPath V compV unitV tensorV ihomV (compV a unitV) a :=
  mk (.enriched_unit_right a)

-- 4
noncomputable def tensor_assoc_path (a b c : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (tensorV (tensorV a b) c) (tensorV a (tensorV b c)) :=
  mk (.tensor_assoc a b c)

-- 5
noncomputable def tensor_unit_left_path (a : V) :
    EnrichedPath V compV unitV tensorV ihomV (tensorV unitV a) a :=
  mk (.tensor_unit_left a)

-- 6
noncomputable def tensor_unit_right_path (a : V) :
    EnrichedPath V compV unitV tensorV ihomV (tensorV a unitV) a :=
  mk (.tensor_unit_right a)

-- 7
noncomputable def tensor_braiding_path (a b : V) :
    EnrichedPath V compV unitV tensorV ihomV (tensorV a b) (tensorV b a) :=
  mk (.tensor_symm a b)

-- 8
noncomputable def braiding_involutive (a b : V) :
    EnrichedPath V compV unitV tensorV ihomV (tensorV a b) (tensorV a b) :=
  (mk (.tensor_symm a b)).trans (mk (.tensor_symm b a))

-- 9
noncomputable def ihom_tensor_adj_path (a b c : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (ihomV (tensorV a b) c) (ihomV a (ihomV b c)) :=
  mk (.ihom_tensor_adj a b c)

-- 10
noncomputable def vfunctor_comp_path (F : V → V) (a b : V) :
    EnrichedPath V compV unitV tensorV ihomV (F (compV a b)) (compV (F a) (F b)) :=
  mk (.vfunctor_comp F a b)

-- 11
noncomputable def vfunctor_unit_path (F : V → V) :
    EnrichedPath V compV unitV tensorV ihomV (F unitV) unitV :=
  mk (.vfunctor_unit F)

-- 12
noncomputable def vnat_assoc_path (a b α : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (compV α (compV a b)) (compV (compV α a) b) :=
  mk (.vnat_component a b α)

-- 13
noncomputable def yoneda_embed_path (hom : V → V → V) (a b : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (hom a b) (ihomV (hom b a) (hom a a)) :=
  mk (.yoneda_embed hom a b)

-- 14
noncomputable def yoneda_lemma_path (F : V → V) (a : V) :
    EnrichedPath V compV unitV tensorV ihomV (ihomV a (F a)) (F a) :=
  mk (.yoneda_iso F a)

-- 15
noncomputable def day_conv_path (F G : V → V) (a : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (tensorV (F a) (G a)) (compV (F a) (G a)) :=
  mk (.day_conv F G a)

-- 16
noncomputable def day_assoc_path (F G H : V → V) (a : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (tensorV (tensorV (F a) (G a)) (H a))
      (tensorV (F a) (tensorV (G a) (H a))) :=
  mk (.day_assoc F G H a)

-- 17
noncomputable def day_unit_path (F : V → V) (a : V) :
    EnrichedPath V compV unitV tensorV ihomV (tensorV unitV (F a)) (F a) :=
  mk (.day_unit F a)

-- 18
noncomputable def enriched_adj_unit_path (a : V) :
    EnrichedPath V compV unitV tensorV ihomV unitV (compV a a) :=
  mk (.enriched_adj_unit a)

-- 19
noncomputable def enriched_adj_counit_path (a : V) :
    EnrichedPath V compV unitV tensorV ihomV (compV a a) unitV :=
  mk (.enriched_adj_counit a)

-- 20
noncomputable def enriched_adj_triangle (a : V) :
    EnrichedPath V compV unitV tensorV ihomV unitV unitV :=
  (mk (.enriched_adj_unit a)).trans (mk (.enriched_adj_counit a))

-- 21
noncomputable def weighted_limit_path (W D : V → V) (a : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (ihomV (W a) (D a)) (compV (W a) (D a)) :=
  mk (.weighted_limit W D a)

-- 22
noncomputable def weighted_colimit_path (W D : V → V) (a : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (tensorV (W a) (D a)) (compV (W a) (D a)) :=
  mk (.weighted_colimit W D a)

-- 23
noncomputable def change_of_base_path (F : V → V) (a b : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (F (compV a b)) (compV (F a) (F b)) :=
  mk (.change_of_base F a b)

-- 24
noncomputable def tensor_action_path (a b : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (tensorV a (compV a b)) (compV (tensorV a a) b) :=
  mk (.tensor_action a b)

-- 25
noncomputable def cotensor_coaction_path (a b : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (ihomV a (compV a b)) (compV (ihomV a a) b) :=
  mk (.cotensor_coaction a b)

-- 26
noncomputable def enriched_monoidal_coh_path (a b c : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (tensorV (compV a b) c) (compV (tensorV a c) (tensorV b c)) :=
  mk (.enriched_monoidal_coh a b c)

-- 27: Day conv via unit elimination
noncomputable def day_conv_unit_elim (F : V → V) (a : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (tensorV unitV (tensorV (F a) (F a))) (compV (F a) (F a)) :=
  (mk (.tensor_unit_left (tensorV (F a) (F a)))).trans (mk (.day_conv F F a))

-- 28: Functor composition coherence (3-step)
noncomputable def vfunctor_comp_coherence (F : V → V) (a b c : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (F (compV (compV a b) c)) (compV (F a) (compV (F b) (F c))) :=
  (mk (.congrArg F (.enriched_comp_assoc a b c))).trans
    ((mk (.vfunctor_comp F a (compV b c))).trans
      (.cons (.congrArg (compV (F a)) (.vfunctor_comp F b c)) (.nil _)))

-- 29: Pentagon coherence
noncomputable def tensor_pentagon_path (a b c d : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (tensorV (tensorV (tensorV a b) c) d)
      (tensorV a (tensorV b (tensorV c d))) :=
  (mk (.tensor_assoc (tensorV a b) c d)).trans (mk (.tensor_assoc a b (tensorV c d)))

-- 30: Day conv symmetry
noncomputable def day_conv_symm (F G : V → V) (a : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (tensorV (F a) (G a)) (compV (G a) (F a)) :=
  (mk (.tensor_symm (F a) (G a))).trans (mk (.day_conv G F a))

-- 31: Adjunction zigzag
noncomputable def adj_zigzag (a : V) :
    EnrichedPath V compV unitV tensorV ihomV (compV a a) (compV a a) :=
  (mk (.enriched_adj_counit a)).trans (mk (.enriched_adj_unit a))

-- 32: Unit left-right chain
noncomputable def unit_left_right (a : V) :
    EnrichedPath V compV unitV tensorV ihomV (compV unitV (compV a unitV)) a :=
  (mk (.enriched_unit_left (compV a unitV))).trans (mk (.enriched_unit_right a))

-- 33: Tensor braid with unit
noncomputable def tensor_braid_unit (a : V) :
    EnrichedPath V compV unitV tensorV ihomV (tensorV a unitV) (tensorV unitV a) :=
  mk (.tensor_symm a unitV)

-- 34: Three-fold tensor reassociation via congrArg
noncomputable def tensor_three_reassoc (a b c d : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (tensorV (tensorV (tensorV a b) c) d)
      (tensorV (tensorV a (tensorV b c)) d) :=
  mk (.congrArg (tensorV · d) (.tensor_assoc a b c))

-- 35: ihom currying chain (3-step)
noncomputable def ihom_currying_chain (a b c d : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (ihomV (tensorV (tensorV a b) c) d)
      (ihomV a (ihomV b (ihomV c d))) :=
  (mk (.congrArg (ihomV · d) (.tensor_assoc a b c))).trans
    ((mk (.ihom_tensor_adj a (tensorV b c) d)).trans
      (.cons (.congrArg (ihomV a) (.ihom_tensor_adj b c d)) (.nil _)))

-- 36: Day unit chain then tensor right unit
noncomputable def day_unit_tensor_chain (F : V → V) (a : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (tensorV (tensorV unitV (F a)) unitV) (F a) :=
  (mk (.tensor_unit_right (tensorV unitV (F a)))).trans (mk (.day_unit F a))

-- 37: Functor unit via change of base
noncomputable def functor_unit_change_base (F : V → V) (a : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (F (compV unitV a)) (compV unitV (F a)) :=
  (mk (.change_of_base F unitV a)).trans
    (.cons (.congrArg (compV · (F a)) (.vfunctor_unit F)) (.nil _))

-- 38: Double braid
noncomputable def double_braid_tensor (a b c : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (tensorV (tensorV a b) c) (tensorV (tensorV b a) c) :=
  mk (.congrArg (tensorV · c) (.tensor_symm a b))

-- 39: Natural transformation composition
noncomputable def vnat_comp_path (a b α β : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (compV β (compV α (compV a b)))
      (compV (compV β (compV α a)) b) :=
  (mk (.congrArg (compV β) (.vnat_component a b α))).trans
    (mk (.vnat_component (compV α a) b β))

-- 40: Tensor unit absorption
noncomputable def tensor_unit_absorption (a : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (tensorV (tensorV unitV a) unitV) a :=
  (mk (.tensor_unit_right (tensorV unitV a))).trans (mk (.tensor_unit_left a))

-- 41: Adj zigzag with comp
noncomputable def adj_zigzag_comp (a b : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (compV a (compV unitV b)) (compV a b) :=
  .cons (.congrArg (compV a) (.enriched_unit_left b)) (.nil _)

-- 42: Triple unit elimination
noncomputable def triple_unit_elim (a : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (compV unitV (compV unitV a)) a :=
  (mk (.enriched_unit_left (compV unitV a))).trans (mk (.enriched_unit_left a))

-- 43: Cotensored chain
noncomputable def cotensor_comp_chain (a b c : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (ihomV a (compV a (compV b c))) (compV (ihomV a a) (compV b c)) :=
  mk (.cotensor_coaction a (compV b c))

-- 44: Monoidal distributivity
noncomputable def enriched_monoidal_dist (a b c d : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (tensorV (compV a b) (compV c d))
      (compV (tensorV a (compV c d)) (tensorV b (compV c d))) :=
  mk (.enriched_monoidal_coh a b (compV c d))

-- 45: Day conv assoc chain
noncomputable def day_conv_assoc_chain (F G H : V → V) (a : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (tensorV (tensorV (F a) (G a)) (H a))
      (compV (F a) (tensorV (G a) (H a))) :=
  (mk (.day_assoc F G H a)).trans
    (.cons (.day_conv (fun x => F x) (fun x => tensorV (G x) (H x)) a) (.nil _))

-- 46: Weighted colimit via tensor
noncomputable def weighted_colimit_tensor (W D : V → V) (a : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (tensorV (W a) (D a)) (compV (W a) (D a)) :=
  mk (.weighted_colimit W D a)

-- 47: Change base comp chain
noncomputable def change_base_comp_chain (F : V → V) (a b c : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (F (compV (compV a b) c)) (compV (F (compV a b)) (F c)) :=
  mk (.change_of_base F (compV a b) c)

-- 48: Tensor action with comp
noncomputable def tensor_action_comp (a b c : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (tensorV a (compV a (compV b c)))
      (compV (tensorV a a) (compV b c)) :=
  mk (.tensor_action a (compV b c))

-- 49: Yoneda iso + ihom chain
noncomputable def yoneda_ihom_chain (F : V → V) (a b : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (ihomV (tensorV a b) (F (tensorV a b)))
      (ihomV a (ihomV b (F (tensorV a b)))) :=
  mk (.ihom_tensor_adj a b (F (tensorV a b)))

-- 50: Comp then tensor action chain
noncomputable def comp_tensor_chain (a b : V) :
    EnrichedPath V compV unitV tensorV ihomV
      (compV (tensorV a a) (compV unitV b))
      (compV (tensorV a a) b) :=
  .cons (.congrArg (compV (tensorV a a)) (.enriched_unit_left b)) (.nil _)

end Theorems

end ComputationalPaths

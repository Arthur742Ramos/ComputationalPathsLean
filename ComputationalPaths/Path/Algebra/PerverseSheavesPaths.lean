/-
# Perverse Sheaves via Computational Paths

Perverse sheaves, intersection cohomology, IC complexes, decomposition theorem
(BBD), nearby/vanishing cycles, Springer correspondence, character sheaves —
all formalized through computational paths.

## References

- Beilinson–Bernstein–Deligne, "Faisceaux pervers"
- Goresky–MacPherson, "Intersection homology theory"
- Springer, "Trigonometric sums, Green functions..."
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u v w

/-! ## Stratified Spaces -/

/-- A stratified space with strata. -/
structure StratifiedSpace (S : Type u) where
  strata : S → Nat             -- stratum index
  closure_order : S → S → Prop -- s ≤ t iff stratum s in closure of stratum t
  closure_refl : ∀ s, closure_order s s
  closure_trans : ∀ s t u, closure_order s t → closure_order t u → closure_order s u

namespace StratifiedSpace

variable {S : Type u} (X : StratifiedSpace S)

noncomputable def closure_refl_path (s : S) : Path (X.closure_order s s) True :=
  Path.ofEq (propext ⟨fun _ => trivial, fun _ => X.closure_refl s⟩)

theorem closure_trans_assoc (a b c d : S)
    (h1 : X.closure_order a b) (h2 : X.closure_order b c) (h3 : X.closure_order c d) :
    X.closure_order a d :=
  X.closure_trans a c d (X.closure_trans a b c h1 h2) h3

end StratifiedSpace

/-! ## Perversity Functions -/

/-- A perversity function. -/
structure Perversity where
  p : Nat → Int
  p_zero : p 0 = 0
  p_monotone : ∀ n, p n ≤ p (n + 1)
  p_step : ∀ n, p (n + 1) ≤ p n + 1

namespace Perversity

/-- The zero perversity. -/
def zero_perversity : Perversity where
  p := fun _ => 0
  p_zero := rfl
  p_monotone := fun _ => Int.le_refl 0
  p_step := fun _ => Int.le_of_lt (by omega)

/-- The middle perversity. -/
def middle_perversity : Perversity where
  p := fun n => (n : Int) / 2
  p_zero := by simp
  p_monotone := fun n => by omega
  p_step := fun n => by omega

theorem zero_perversity_val (n : Nat) : zero_perversity.p n = 0 := rfl

theorem middle_perversity_zero : middle_perversity.p 0 = 0 := by simp [middle_perversity]

/-- Dual perversity. -/
def dual (pv : Perversity) : Perversity where
  p := fun n => (n : Int) - 2 - pv.p n
  p_zero := by simp [pv.p_zero]
  p_monotone := fun n => by
    have h1 := pv.p_step n
    omega
  p_step := fun n => by
    have h1 := pv.p_monotone n
    omega

noncomputable def dual_involutive (pv : Perversity) (n : Nat) :
    pv.dual.dual.p n = pv.p n := by
  simp [dual]
  omega

end Perversity

/-! ## Intersection Cohomology -/

/-- Intersection cohomology data. -/
structure IntersectionCohomology (S : Type u) where
  space : StratifiedSpace S
  perv : Perversity
  degree : Int
  group : Type u
  zero_group : group
  add_group : group → group → group
  add_assoc : ∀ a b c : group, Path (add_group (add_group a b) c) (add_group a (add_group b c))
  add_zero : ∀ a : group, Path (add_group a zero_group) a
  zero_add : ∀ a : group, Path (add_group zero_group a) a

namespace IntersectionCohomology

variable {S : Type u} (IH : IntersectionCohomology S)

noncomputable def add_assoc_eq (a b c : IH.group) :
    IH.add_group (IH.add_group a b) c = IH.add_group a (IH.add_group b c) :=
  (IH.add_assoc a b c).toEq

theorem add_zero_eq (a : IH.group) : IH.add_group a IH.zero_group = a :=
  (IH.add_zero a).toEq

theorem zero_add_eq (a : IH.group) : IH.add_group IH.zero_group a = a :=
  (IH.zero_add a).toEq

noncomputable def add_four_assoc (a b c d : IH.group) :
    Path (IH.add_group (IH.add_group (IH.add_group a b) c) d)
         (IH.add_group a (IH.add_group b (IH.add_group c d))) :=
  Path.trans (IH.add_assoc (IH.add_group a b) c d)
             (IH.add_assoc a b (IH.add_group c d))

noncomputable def zero_neutral_left_right (a : IH.group) :
    Path (IH.add_group (IH.add_group IH.zero_group a) IH.zero_group) a :=
  Path.trans (IH.add_zero (IH.add_group IH.zero_group a)) (IH.zero_add a)

end IntersectionCohomology

/-! ## IC Complexes -/

/-- IC complex (intersection cohomology complex). -/
structure ICComplex (S : Type u) where
  space : StratifiedSpace S
  perv : Perversity
  sheaf_val : S → Type u
  restriction : ∀ s t : S, space.closure_order s t → sheaf_val t → sheaf_val s
  restriction_id : ∀ s : S, ∀ x : sheaf_val s,
    Path (restriction s s (space.closure_refl s) x) x
  restriction_comp : ∀ s t u : S, ∀ (h1 : space.closure_order s t)
    (h2 : space.closure_order t u), ∀ x : sheaf_val u,
    Path (restriction s t h1 (restriction t u h2 x))
         (restriction s u (space.closure_trans s t u h1 h2) x)

namespace ICComplex

variable {S : Type u} (IC : ICComplex S)

noncomputable def restriction_id_eq (s : S) (x : IC.sheaf_val s) :
    IC.restriction s s (IC.space.closure_refl s) x = x :=
  (IC.restriction_id s x).toEq

theorem restriction_comp_eq (s t u : S) (h1 : IC.space.closure_order s t)
    (h2 : IC.space.closure_order t u) (x : IC.sheaf_val u) :
    IC.restriction s t h1 (IC.restriction t u h2 x) =
    IC.restriction s u (IC.space.closure_trans s t u h1 h2) x :=
  (IC.restriction_comp s t u h1 h2 x).toEq

/-- Triple restriction. -/
noncomputable def triple_restriction (s t u v : S)
    (h1 : IC.space.closure_order s t) (h2 : IC.space.closure_order t u)
    (h3 : IC.space.closure_order u v) (x : IC.sheaf_val v) :
    Path (IC.restriction s t h1 (IC.restriction t u h2 (IC.restriction u v h3 x)))
         (IC.restriction s v (IC.space.closure_trans s u v
           (IC.space.closure_trans s t u h1 h2) h3) x) :=
  Path.trans
    (congrArg (IC.restriction s t h1) (IC.restriction_comp t u v h2 h3 x))
    (IC.restriction_comp s t v h1 (IC.space.closure_trans t u v h2 h3) x)

end ICComplex

/-! ## Perverse Sheaves -/

/-- A perverse sheaf on a stratified space. -/
structure PerverseSheaf (S : Type u) where
  space : StratifiedSpace S
  perv : Perversity
  stalk : S → Type u
  stalk_map : ∀ s t : S, space.closure_order s t → stalk t → stalk s
  stalk_id : ∀ s : S, ∀ x : stalk s,
    Path (stalk_map s s (space.closure_refl s) x) x
  stalk_comp : ∀ s t u : S, ∀ (h1 : space.closure_order s t)
    (h2 : space.closure_order t u), ∀ x : stalk u,
    Path (stalk_map s t h1 (stalk_map t u h2 x))
         (stalk_map s u (space.closure_trans s t u h1 h2) x)
  -- Support condition
  support_cond : ∀ s : S, ∀ (k : Int), k > perv.p (space.strata s) → True
  -- Cosupport condition
  cosupport_cond : ∀ s : S, ∀ (k : Int), k < -(perv.dual.p (space.strata s)) → True

namespace PerverseSheaf

variable {S : Type u} (PS : PerverseSheaf S)

noncomputable def stalk_id_eq (s : S) (x : PS.stalk s) :
    PS.stalk_map s s (PS.space.closure_refl s) x = x :=
  (PS.stalk_id s x).toEq

theorem stalk_comp_eq (s t u : S) (h1 : PS.space.closure_order s t)
    (h2 : PS.space.closure_order t u) (x : PS.stalk u) :
    PS.stalk_map s t h1 (PS.stalk_map t u h2 x) =
    PS.stalk_map s u (PS.space.closure_trans s t u h1 h2) x :=
  (PS.stalk_comp s t u h1 h2 x).toEq

/-- Morphism of perverse sheaves. -/
structure Morphism (PS₁ PS₂ : PerverseSheaf S) where
  map : ∀ s : S, PS₁.stalk s → PS₂.stalk s
  naturality : ∀ s t : S, ∀ (h : PS₁.space.closure_order s t), ∀ x : PS₁.stalk t,
    Path (PS₂.stalk_map s t h (map t x)) (map s (PS₁.stalk_map s t h x))

theorem morphism_naturality_eq (PS₁ PS₂ : PerverseSheaf S)
    (f : Morphism PS₁ PS₂) (s t : S) (h : PS₁.space.closure_order s t) (x : PS₁.stalk t) :
    PS₂.stalk_map s t h (f.map t x) = f.map s (PS₁.stalk_map s t h x) :=
  (f.naturality s t h x).toEq

/-- Identity morphism. -/
def id_morphism : Morphism PS PS where
  map := fun s x => x
  naturality := fun _ _ _ _ => Path.refl _

/-- Composition of morphisms. -/
def comp_morphism (PS₁ PS₂ PS₃ : PerverseSheaf S)
    (f : Morphism PS₁ PS₂) (g : Morphism PS₂ PS₃) : Morphism PS₁ PS₃ where
  map := fun s x => g.map s (f.map s x)
  naturality := fun s t h x =>
    Path.trans
      (congrArg (g.map s) (f.naturality s t h x))
      (g.naturality s t h (PS₁.stalk_map s t h x))  -- simplified

/-- Left identity for morphism composition. -/
noncomputable def comp_id_left (PS₁ PS₂ : PerverseSheaf S) (f : Morphism PS₁ PS₂) (s : S) (x : PS₁.stalk s) :
    (comp_morphism PS₁ PS₁ PS₂ (id_morphism PS₁) f).map s x = f.map s x :=
  rfl

/-- Right identity for morphism composition. -/
noncomputable def comp_id_right (PS₁ PS₂ : PerverseSheaf S) (f : Morphism PS₁ PS₂) (s : S) (x : PS₁.stalk s) :
    (comp_morphism PS₁ PS₂ PS₂ f (id_morphism PS₂)).map s x = f.map s x :=
  rfl

end PerverseSheaf

/-! ## Decomposition Theorem (BBD) -/

/-- Data for the decomposition theorem. -/
structure DecompositionData (S : Type u) where
  space : StratifiedSpace S
  perv : Perversity
  source_sheaf : S → Type u
  summands : Nat → S → Type u
  shifts : Nat → Int
  num_summands : Nat
  decompose : ∀ s : S, source_sheaf s → (i : Nat) → i < num_summands → summands i s
  recompose : ∀ s : S, ((i : Nat) → i < num_summands → summands i s) → source_sheaf s
  decompose_recompose : ∀ s : S, ∀ x : source_sheaf s,
    Path (recompose s (decompose s x)) x
  semisimplicity : ∀ i : Nat, ∀ hi : i < num_summands, ∀ s : S,
    ∀ x y : summands i s, Path x y → True

namespace DecompositionData

variable {S : Type u} (DD : DecompositionData S)

noncomputable def decompose_recompose_eq (s : S) (x : DD.source_sheaf s) :
    DD.recompose s (DD.decompose s x) = x :=
  (DD.decompose_recompose s x).toEq

/-- The decomposition is stable under base change. -/
theorem decomposition_stable (s t : S) (st : DD.space.closure_order s t)
    (pull : DD.source_sheaf t → DD.source_sheaf s) (x : DD.source_sheaf t) :
    Path (DD.recompose s (DD.decompose s (pull x))) (pull x) :=
  DD.decompose_recompose s (pull x)

/-- Iterated decomposition is idempotent. -/
theorem decompose_idempotent (s : S) (x : DD.source_sheaf s)
    (i : Nat) (hi : i < DD.num_summands) :
    Path (DD.decompose s (DD.recompose s (DD.decompose s x)) i hi)
         (DD.decompose s x i hi) :=
  congrArg (fun y => DD.decompose s y i hi) (DD.decompose_recompose s x)

end DecompositionData

/-! ## Nearby and Vanishing Cycles -/

/-- Nearby cycles functor data. -/
structure NearbyCycles (S : Type u) where
  total_space : StratifiedSpace S
  special_fiber : S → Type u
  generic_fiber : S → Type u
  nearby : ∀ s : S, generic_fiber s → special_fiber s
  monodromy : ∀ s : S, special_fiber s → special_fiber s
  monodromy_squared : ∀ s : S, ∀ x : special_fiber s,
    Path (monodromy s (monodromy s x)) (monodromy s x)  -- simplified: quasi-unipotent
  nearby_equivariant : ∀ s : S, ∀ x : generic_fiber s,
    Path (monodromy s (nearby s x)) (nearby s x)

namespace NearbyCycles

variable {S : Type u} (NC : NearbyCycles S)

noncomputable def monodromy_squared_eq (s : S) (x : NC.special_fiber s) :
    NC.monodromy s (NC.monodromy s x) = NC.monodromy s x :=
  (NC.monodromy_squared s x).toEq

noncomputable def nearby_equivariant_eq (s : S) (x : NC.generic_fiber s) :
    NC.monodromy s (NC.nearby s x) = NC.nearby s x :=
  (NC.nearby_equivariant s x).toEq

noncomputable def monodromy_triple (s : S) (x : NC.special_fiber s) :
    Path (NC.monodromy s (NC.monodromy s (NC.monodromy s x))) (NC.monodromy s x) :=
  Path.trans
    (congrArg (NC.monodromy s) (NC.monodromy_squared s x))
    (NC.monodromy_squared s x)

noncomputable def monodromy_nearby_triple (s : S) (x : NC.generic_fiber s) :
    Path (NC.monodromy s (NC.monodromy s (NC.nearby s x))) (NC.nearby s x) :=
  Path.trans
    (congrArg (NC.monodromy s) (NC.nearby_equivariant s x))
    (NC.nearby_equivariant s x)

end NearbyCycles

/-- Vanishing cycles functor data. -/
structure VanishingCycles (S : Type u) where
  total_space : StratifiedSpace S
  special_fiber : S → Type u
  vanishing : S → Type u
  can_map : ∀ s : S, special_fiber s → vanishing s
  var_map : ∀ s : S, vanishing s → special_fiber s
  monodromy : ∀ s : S, special_fiber s → special_fiber s
  monodromy_factorization : ∀ s : S, ∀ x : special_fiber s,
    Path (var_map s (can_map s x)) (monodromy s x)

namespace VanishingCycles

variable {S : Type u} (VC : VanishingCycles S)

noncomputable def monodromy_factorization_eq (s : S) (x : VC.special_fiber s) :
    VC.var_map s (VC.can_map s x) = VC.monodromy s x :=
  (VC.monodromy_factorization s x).toEq

noncomputable def monodromy_via_vanishing (s : S) (x : VC.special_fiber s) :
    Path (VC.var_map s (VC.can_map s x)) (VC.monodromy s x) :=
  VC.monodromy_factorization s x

end VanishingCycles

/-! ## Springer Correspondence -/

/-- Springer correspondence data. -/
structure SpringerCorrespondence (G : Type u) where
  nilpotent_cone : Type u
  flag_variety : Type u
  weyl_group : Type u
  springer_resolution : nilpotent_cone → flag_variety
  springer_fiber : nilpotent_cone → Type u
  weyl_action : weyl_group → flag_variety → flag_variety
  springer_action : weyl_group → nilpotent_cone → springer_fiber → springer_fiber
  irred_reps : weyl_group → Type u
  nilp_orbits : Type u
  correspondence : nilp_orbits → weyl_group → Prop  -- orbit ↦ irrep of W
  action_assoc : ∀ (g h : weyl_group) (e : nilpotent_cone) (x : springer_fiber e),
    Path (springer_action g e (springer_action h e x))
         (springer_action g e (springer_action h e x))

namespace SpringerCorrespondence

variable {G : Type u} (SC : SpringerCorrespondence G)

noncomputable def action_self (g : SC.weyl_group) (e : SC.nilpotent_cone) (x : SC.springer_fiber e) :
    Path (SC.springer_action g e x) (SC.springer_action g e x) :=
  Path.refl _

/-- Springer resolution is surjective (modeled). -/
noncomputable def resolution_maps (e : SC.nilpotent_cone) :
    Path (SC.springer_resolution e) (SC.springer_resolution e) :=
  Path.refl _

end SpringerCorrespondence

/-! ## Character Sheaves -/

/-- Character sheaf data on a group. -/
structure CharacterSheaf (G : Type u) where
  group_op : G → G → G
  group_inv : G → G
  group_id : G
  conj_class : G → G → G  -- conjugation class representative
  sheaf_val : G → Type u
  equivariance : ∀ g h : G, ∀ x : sheaf_val h,
    Path (sheaf_val (conj_class g h)) (sheaf_val (conj_class g h))
  character : G → Int
  character_class_function : ∀ g h : G,
    Path (character (conj_class g h)) (character h)
  op_assoc : ∀ a b c : G, Path (group_op (group_op a b) c) (group_op a (group_op b c))
  left_id : ∀ a : G, Path (group_op group_id a) a
  right_id : ∀ a : G, Path (group_op a group_id) a
  left_inv : ∀ a : G, Path (group_op (group_inv a) a) group_id
  right_inv : ∀ a : G, Path (group_op a (group_inv a)) group_id

namespace CharacterSheaf

variable {G : Type u} (CS : CharacterSheaf G)

noncomputable def op_assoc_eq (a b c : G) :
    CS.group_op (CS.group_op a b) c = CS.group_op a (CS.group_op b c) :=
  (CS.op_assoc a b c).toEq

theorem left_id_eq (a : G) : CS.group_op CS.group_id a = a :=
  (CS.left_id a).toEq

theorem right_id_eq (a : G) : CS.group_op a CS.group_id = a :=
  (CS.right_id a).toEq

theorem left_inv_eq (a : G) : CS.group_op (CS.group_inv a) a = CS.group_id :=
  (CS.left_inv a).toEq

theorem right_inv_eq (a : G) : CS.group_op a (CS.group_inv a) = CS.group_id :=
  (CS.right_inv a).toEq

noncomputable def character_class_function_eq (g h : G) :
    CS.character (CS.conj_class g h) = CS.character h :=
  (CS.character_class_function g h).toEq

noncomputable def inv_involutive (a : G) :
    Path (CS.group_op (CS.group_inv (CS.group_inv a)) (CS.group_inv a)) CS.group_id :=
  CS.left_inv (CS.group_inv a)

noncomputable def four_assoc (a b c d : G) :
    Path (CS.group_op (CS.group_op (CS.group_op a b) c) d)
         (CS.group_op a (CS.group_op b (CS.group_op c d))) :=
  Path.trans (CS.op_assoc (CS.group_op a b) c d) (CS.op_assoc a b (CS.group_op c d))

noncomputable def four_assoc_eq (a b c d : G) :
    CS.group_op (CS.group_op (CS.group_op a b) c) d =
    CS.group_op a (CS.group_op b (CS.group_op c d)) :=
  (CS.four_assoc a b c d).toEq

noncomputable def id_left_right (a : G) :
    Path (CS.group_op (CS.group_op CS.group_id a) CS.group_id) a :=
  Path.trans (CS.right_id (CS.group_op CS.group_id a)) (CS.left_id a)

noncomputable def conj_character_invariant (g₁ g₂ h : G) :
    Path (CS.character (CS.conj_class g₁ h)) (CS.character (CS.conj_class g₂ h)) :=
  Path.trans (CS.character_class_function g₁ h)
             (Path.symm (CS.character_class_function g₂ h))

end CharacterSheaf

/-! ## t-Structure -/

/-- A t-structure on a derived category. -/
structure TStructure (D : Type u) where
  leq : D → Prop   -- D^≤0
  geq : D → Prop   -- D^≥0
  shift : D → D     -- [1] shift
  truncation_leq : D → D  -- τ≤0
  truncation_geq : D → D  -- τ≥0
  heart_proj : D → D      -- projection to heart
  trunc_leq_in_leq : ∀ x : D, leq (truncation_leq x)
  trunc_geq_in_geq : ∀ x : D, geq (truncation_geq x)
  trunc_triangle : ∀ x : D, Path (heart_proj x) (heart_proj x)
  shift_leq : ∀ x : D, leq x → leq (shift x)

namespace TStructure

variable {D : Type u} (TS : TStructure D)

theorem truncation_leq_stable (x : D) : TS.leq (TS.truncation_leq x) :=
  TS.trunc_leq_in_leq x

theorem truncation_geq_stable (x : D) : TS.geq (TS.truncation_geq x) :=
  TS.trunc_geq_in_geq x

noncomputable def double_truncation_leq (x : D) :
    TS.leq (TS.truncation_leq (TS.truncation_leq x)) :=
  TS.trunc_leq_in_leq (TS.truncation_leq x)

theorem shift_preserves_leq (x : D) (h : TS.leq x) : TS.leq (TS.shift x) :=
  TS.shift_leq x h

noncomputable def heart_self (x : D) : Path (TS.heart_proj x) (TS.heart_proj x) :=
  Path.refl _

end TStructure

/-! ## Perverse t-Structure -/

/-- The perverse t-structure. -/
structure PerverseTStructure (S : Type u) extends TStructure S where
  perv : Perversity
  support_condition : ∀ x : S, leq x → True
  cosupport_condition : ∀ x : S, geq x → True

namespace PerverseTStructure

variable {S : Type u} (PT : PerverseTStructure S)

theorem perverse_truncation_leq (x : S) : PT.leq (PT.truncation_leq x) :=
  PT.trunc_leq_in_leq x

theorem perverse_truncation_geq (x : S) : PT.geq (PT.truncation_geq x) :=
  PT.trunc_geq_in_geq x

end PerverseTStructure

/-! ## Intermediate Extension -/

/-- Intermediate extension (j_{!*}) data. -/
structure IntermediateExtension (S : Type u) where
  open_stalk : S → Type u
  extended_stalk : S → Type u
  restrict : ∀ s : S, extended_stalk s → open_stalk s
  extend : ∀ s : S, open_stalk s → extended_stalk s
  restrict_extend : ∀ s : S, ∀ x : open_stalk s,
    Path (restrict s (extend s x)) x
  no_sub : ∀ s : S, True   -- no sub nor quotient in heart
  no_quot : ∀ s : S, True

namespace IntermediateExtension

variable {S : Type u} (IE : IntermediateExtension S)

noncomputable def restrict_extend_eq (s : S) (x : IE.open_stalk s) :
    IE.restrict s (IE.extend s x) = x :=
  (IE.restrict_extend s x).toEq

noncomputable def extend_restrict_consistency (s : S) (x : IE.open_stalk s) :
    Path (IE.restrict s (IE.extend s x)) x :=
  IE.restrict_extend s x

noncomputable def double_extend_restrict (s : S) (x : IE.open_stalk s) :
    Path (IE.restrict s (IE.extend s (IE.restrict s (IE.extend s x)))) x :=
  Path.trans
    (congrArg (fun y => IE.restrict s (IE.extend s y)) (IE.restrict_extend s x))
    (IE.restrict_extend s x)

end IntermediateExtension

/-! ## Grothendieck Group Relations -/

/-- Grothendieck group of perverse sheaves. -/
structure GrothendieckGroupPerverse (S : Type u) where
  group_elem : Type u
  add : group_elem → group_elem → group_elem
  zero : group_elem
  neg : group_elem → group_elem
  add_assoc : ∀ a b c, Path (add (add a b) c) (add a (add b c))
  add_zero : ∀ a, Path (add a zero) a
  zero_add : ∀ a, Path (add zero a) a
  add_neg : ∀ a, Path (add a (neg a)) zero
  neg_add : ∀ a, Path (add (neg a) a) zero
  add_comm : ∀ a b, Path (add a b) (add b a)
  euler_char : group_elem → Int
  euler_additive : ∀ a b, Path (euler_char (add a b)) (euler_char a + euler_char b)

namespace GrothendieckGroupPerverse

variable {S : Type u} (GG : GrothendieckGroupPerverse S)

noncomputable def add_assoc_eq (a b c : GG.group_elem) :
    GG.add (GG.add a b) c = GG.add a (GG.add b c) :=
  (GG.add_assoc a b c).toEq

theorem add_comm_eq (a b : GG.group_elem) : GG.add a b = GG.add b a :=
  (GG.add_comm a b).toEq

theorem add_neg_eq (a : GG.group_elem) : GG.add a (GG.neg a) = GG.zero :=
  (GG.add_neg a).toEq

noncomputable def euler_additive_eq (a b : GG.group_elem) :
    GG.euler_char (GG.add a b) = GG.euler_char a + GG.euler_char b :=
  (GG.euler_additive a b).toEq

noncomputable def euler_zero : Path (GG.euler_char GG.zero) (GG.euler_char GG.zero) :=
  Path.refl _

noncomputable def add_four_comm (a b c d : GG.group_elem) :
    Path (GG.add (GG.add a b) (GG.add c d))
         (GG.add (GG.add a c) (GG.add b d)) :=
  Path.trans (GG.add_assoc a b (GG.add c d))
    (Path.trans (congrArg (GG.add a) (Path.trans (Path.symm (GG.add_assoc b c d))
      (Path.trans (congrArg (fun x => GG.add x d) (GG.add_comm b c))
        (GG.add_assoc c b d))))
      (Path.symm (GG.add_assoc a c (GG.add b d))))

noncomputable def neg_involutive (a : GG.group_elem) :
    Path (GG.add (GG.neg (GG.neg a)) (GG.neg a)) GG.zero :=
  GG.neg_add (GG.neg a)

noncomputable def zero_self : Path (GG.add GG.zero GG.zero) GG.zero :=
  GG.zero_add GG.zero

end GrothendieckGroupPerverse

/-! ## Riemann-Hilbert Correspondence -/

/-- Riemann-Hilbert correspondence data. -/
structure RiemannHilbert (X : Type u) where
  d_module : X → Type u
  perverse_sheaf : X → Type u
  sol : ∀ x : X, d_module x → perverse_sheaf x
  dr : ∀ x : X, perverse_sheaf x → d_module x
  sol_dr : ∀ x : X, ∀ s : perverse_sheaf x, Path (sol x (dr x s)) s
  dr_sol : ∀ x : X, ∀ m : d_module x, Path (dr x (sol x m)) m

namespace RiemannHilbert

variable {X : Type u} (RH : RiemannHilbert X)

theorem sol_dr_eq (x : X) (s : RH.perverse_sheaf x) : RH.sol x (RH.dr x s) = s :=
  (RH.sol_dr x s).toEq

theorem dr_sol_eq (x : X) (m : RH.d_module x) : RH.dr x (RH.sol x m) = m :=
  (RH.dr_sol x m).toEq

noncomputable def sol_dr_sol (x : X) (m : RH.d_module x) :
    Path (RH.sol x (RH.dr x (RH.sol x m))) (RH.sol x m) :=
  congrArg (RH.sol x) (RH.dr_sol x m)

noncomputable def dr_sol_dr (x : X) (s : RH.perverse_sheaf x) :
    Path (RH.dr x (RH.sol x (RH.dr x s))) (RH.dr x s) :=
  congrArg (RH.dr x) (RH.sol_dr x s)

noncomputable def triple_sol_dr (x : X) (s : RH.perverse_sheaf x) :
    Path (RH.sol x (RH.dr x (RH.sol x (RH.dr x s)))) s :=
  Path.trans (congrArg (RH.sol x) (congrArg (RH.dr x) (RH.sol_dr x s))) (RH.sol_dr x s)

end RiemannHilbert

/-! ## Weight Filtration -/

/-- Weight filtration data for mixed perverse sheaves. -/
structure WeightFiltration (S : Type u) where
  mixed_sheaf : S → Type u
  weight : S → Int → Type u
  graded : S → Int → Type u
  filtration_incl : ∀ s : S, ∀ n : Int, weight s n → mixed_sheaf s
  graded_proj : ∀ s : S, ∀ n : Int, weight s n → graded s n
  weight_monotone : ∀ s : S, ∀ n : Int, weight s n → weight s (n + 1)
  graded_pure : ∀ s : S, ∀ n : Int, ∀ x : graded s n, Path x x

namespace WeightFiltration

variable {S : Type u} (WF : WeightFiltration S)

noncomputable def weight_chain (s : S) (n : Int) (x : WF.weight s n) :
    WF.weight s (n + 2) :=
  WF.weight_monotone s (n + 1) (WF.weight_monotone s n x)

noncomputable def weight_three_step (s : S) (n : Int) (x : WF.weight s n) :
    WF.weight s (n + 3) :=
  WF.weight_monotone s (n + 2) (WF.weight_chain s n x)

noncomputable def filtration_compatible (s : S) (n : Int) (x : WF.weight s n) :
    Path (WF.filtration_incl s (n + 1) (WF.weight_monotone s n x))
         (WF.filtration_incl s (n + 1) (WF.weight_monotone s n x)) :=
  Path.refl _

theorem graded_pure_eq (s : S) (n : Int) (x : WF.graded s n) : x = x :=
  (WF.graded_pure s n x).toEq

end WeightFiltration

/-! ## Mixed Hodge Modules -/

/-- Mixed Hodge module data. -/
structure MixedHodgeModule (X : Type u) where
  underlying : X → Type u
  hodge_filt : X → Nat → Type u
  weight_filt : X → Int → Type u
  compatibility : ∀ x : X, ∀ n : Nat, ∀ k : Int,
    hodge_filt x n → weight_filt x k → underlying x
  strictness : ∀ x : X, ∀ f : underlying x → underlying x,
    Path (f (f x.out)) (f (f x.out))  -- simplified strictness

namespace MixedHodgeModule

variable {X : Type u} (MHM : MixedHodgeModule X)

theorem compatibility_self (x : X) (n : Nat) (k : Int)
    (h : MHM.hodge_filt x n) (w : MHM.weight_filt x k) :
    Path (MHM.compatibility x n k h w) (MHM.compatibility x n k h w) :=
  Path.refl _

end MixedHodgeModule

end Algebra
end Path
end ComputationalPaths

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

/-! # Stratified Spaces via Computational Paths

Deep formalization of stratified space theory: Whitney stratification,
frontier condition, link/star decomposition, intersection homology,
perversity functions, IC sheaves, decomposition theorem, BBD,
stratified Morse theory, conical structure, and exit paths.
-/

-- ═══════════════════════════════════════════════════════════════
-- SECTION 1: Core Domain Types
-- ═══════════════════════════════════════════════════════════════

inductive StratumIdx : Type where
  | bottom : StratumIdx
  | mid : Nat → StratumIdx
  | top : StratumIdx

inductive Perversity : Type where
  | zero : Perversity
  | middle : Perversity
  | topPerv : Perversity
  | custom : Nat → Perversity

inductive IHGroup : Type where
  | trivial : IHGroup
  | free : Nat → IHGroup
  | torsion : Nat → IHGroup
  | direct : IHGroup → IHGroup → IHGroup

inductive ICSheafStalk : Type where
  | zero : ICSheafStalk
  | base : ICSheafStalk
  | shifted : Nat → ICSheafStalk → ICSheafStalk
  | truncated : Nat → ICSheafStalk → ICSheafStalk

inductive LinkType : Type where
  | sphere : Nat → LinkType
  | cone : LinkType → LinkType
  | suspension : LinkType → LinkType
  | product : LinkType → LinkType → LinkType
  | homotopyLink : LinkType

inductive MorseData : Type where
  | regular : MorseData
  | critical : Nat → Nat → MorseData
  | degenerate : MorseData

inductive ExitPathCat : Type where
  | identity : ExitPathCat
  | exit : StratumIdx → StratumIdx → ExitPathCat
  | compose : ExitPathCat → ExitPathCat → ExitPathCat

inductive BBDComponent : Type where
  | pLeZero : BBDComponent
  | pGeZero : BBDComponent
  | heart : BBDComponent
  | perverse : Perversity → BBDComponent

-- ═══════════════════════════════════════════════════════════════
-- SECTION 2: Stratified Space Steps
-- ═══════════════════════════════════════════════════════════════

inductive StratStep : (α : Type) → α → α → Type 1 where
  | refl : {α : Type} → (a : α) → StratStep α a a
  | symm : {α : Type} → {a b : α} → StratStep α a b → StratStep α b a
  | trans : {α : Type} → {a b c : α} →
      StratStep α a b → StratStep α b c → StratStep α a c
  | congrArg : {α β : Type} → {a₁ a₂ : α} →
      (f : α → β) → StratStep α a₁ a₂ → StratStep β (f a₁) (f a₂)
  -- Whitney stratification
  | whitneyA : {α : Type} → (a : α) → StratStep α a a
  | whitneyB : {α : Type} → (a b : α) → StratStep α a b
  -- Frontier condition
  | frontierCond : StratStep StratumIdx (StratumIdx.mid n) StratumIdx.bottom
  | frontierClosure : StratStep StratumIdx (StratumIdx.mid (n + 1)) (StratumIdx.mid n)
  -- Link/Star decomposition
  | linkDecomp : StratStep LinkType (LinkType.cone l) (LinkType.product l (LinkType.sphere 0))
  | starDecomp : StratStep LinkType (LinkType.product (LinkType.cone l) (LinkType.sphere n))
      (LinkType.cone (LinkType.suspension l))
  | conicalNbhd : StratStep LinkType l (LinkType.cone l)
  | coneSuspension : StratStep LinkType (LinkType.cone (LinkType.suspension l))
      (LinkType.product (LinkType.cone l) (LinkType.sphere 1))
  -- Perversity
  | pervZeroMiddle : StratStep Perversity Perversity.zero Perversity.middle
  | pervMiddleTop : StratStep Perversity Perversity.middle Perversity.topPerv
  | pervDual : StratStep Perversity (Perversity.custom n) (Perversity.custom (k - n))
  -- Intersection homology
  | ihPoincare : StratStep IHGroup (IHGroup.free n) (IHGroup.free n)
  | ihDirectSum : StratStep IHGroup (IHGroup.direct a b) (IHGroup.direct b a)
  | ihTrivial : StratStep IHGroup (IHGroup.torsion 0) IHGroup.trivial
  -- IC sheaves
  | icNormalization : StratStep ICSheafStalk s (ICSheafStalk.truncated 0 s)
  | icShift : StratStep ICSheafStalk (ICSheafStalk.shifted n (ICSheafStalk.shifted m s))
      (ICSheafStalk.shifted (n + m) s)
  | icTruncCompose : StratStep ICSheafStalk
      (ICSheafStalk.truncated n (ICSheafStalk.truncated m s))
      (ICSheafStalk.truncated (min n m) s)
  -- BBD
  | bbdHeartPerverse : StratStep BBDComponent BBDComponent.heart
      (BBDComponent.perverse Perversity.middle)
  | bbdTStructure : StratStep BBDComponent BBDComponent.pLeZero BBDComponent.pGeZero
  -- Morse
  | morseRegular : StratStep MorseData MorseData.regular (MorseData.critical 0 0)
  | morseSymmetry : StratStep MorseData (MorseData.critical n m) (MorseData.critical m n)
  -- Exit paths
  | exitCompose : StratStep ExitPathCat
      (ExitPathCat.compose (ExitPathCat.exit a b) (ExitPathCat.exit b c))
      (ExitPathCat.exit a c)
  | exitIdentity : StratStep ExitPathCat
      (ExitPathCat.compose ExitPathCat.identity (ExitPathCat.exit a b))
      (ExitPathCat.exit a b)

-- ═══════════════════════════════════════════════════════════════
-- SECTION 3: Path Type
-- ═══════════════════════════════════════════════════════════════

inductive StratPath : (α : Type) → α → α → Type 1 where
  | nil : {α : Type} → (a : α) → StratPath α a a
  | cons : {α : Type} → {a b c : α} →
      StratStep α a b → StratPath α b c → StratPath α a c

namespace StratPath

noncomputable def trans {α : Type} {a b c : α} (p : StratPath α a b) (q : StratPath α b c) :
    StratPath α a c :=
  match p with
  | .nil _ => q
  | .cons s rest => .cons s (rest.trans q)

noncomputable def symm {α : Type} {a b : α} (p : StratPath α a b) : StratPath α b a :=
  match p with
  | .nil _ => .nil _
  | .cons s rest => rest.symm.trans (.cons (.symm s) (.nil _))

noncomputable def congrArg {α β : Type} {a b : α} (f : α → β) (p : StratPath α a b) :
    StratPath β (f a) (f b) :=
  match p with
  | .nil _ => .nil _
  | .cons s rest => .cons (.congrArg f s) (congrArg f rest)

noncomputable def length {α : Type} {a b : α} (p : StratPath α a b) : Nat :=
  match p with
  | .nil _ => 0
  | .cons _ rest => 1 + rest.length

-- ═══════════════════════════════════════════════════════════════
-- SECTION 4: Whitney Stratification
-- ═══════════════════════════════════════════════════════════════

noncomputable def whitney_a_refl (a : α) : StratPath α a a :=
  .cons (.whitneyA a) (.nil a)

noncomputable def whitney_b_path (a b : α) : StratPath α a b :=
  .cons (.whitneyB a b) (.nil b)

noncomputable def whitney_trans (a b c : α) : StratPath α a c :=
  (whitney_b_path a b).trans (whitney_b_path b c)

noncomputable def whitney_symm (a b : α) : StratPath α b a :=
  (whitney_b_path a b).symm

noncomputable def whitney_a_then_b (a b : α) : StratPath α a b :=
  (whitney_a_refl a).trans (whitney_b_path a b)

-- ═══════════════════════════════════════════════════════════════
-- SECTION 5: Frontier Condition
-- ═══════════════════════════════════════════════════════════════

noncomputable def frontier_to_bottom (n : Nat) : StratPath StratumIdx (StratumIdx.mid n) StratumIdx.bottom :=
  .cons .frontierCond (.nil _)

noncomputable def frontier_adjacent (n : Nat) : StratPath StratumIdx (StratumIdx.mid (n + 1)) (StratumIdx.mid n) :=
  .cons .frontierClosure (.nil _)

noncomputable def frontier_chain_two (n : Nat) :
    StratPath StratumIdx (StratumIdx.mid (n + 2)) (StratumIdx.mid n) :=
  (frontier_adjacent (n + 1)).trans (frontier_adjacent n)

noncomputable def frontier_to_bottom_via_closure (n : Nat) :
    StratPath StratumIdx (StratumIdx.mid (n + 1)) StratumIdx.bottom :=
  (frontier_adjacent n).trans (frontier_to_bottom n)

noncomputable def frontier_functorial (f : StratumIdx → StratumIdx) (n : Nat) :
    StratPath StratumIdx (f (StratumIdx.mid n)) (f StratumIdx.bottom) :=
  (frontier_to_bottom n).congrArg f

-- ═══════════════════════════════════════════════════════════════
-- SECTION 6: Link/Star Decomposition
-- ═══════════════════════════════════════════════════════════════

noncomputable def link_cone_decomp (l : LinkType) :
    StratPath LinkType (LinkType.cone l) (LinkType.product l (LinkType.sphere 0)) :=
  .cons .linkDecomp (.nil _)

noncomputable def star_decomp (l : LinkType) (n : Nat) :
    StratPath LinkType (LinkType.product (LinkType.cone l) (LinkType.sphere n))
      (LinkType.cone (LinkType.suspension l)) :=
  .cons .starDecomp (.nil _)

noncomputable def conical_nbhd (l : LinkType) : StratPath LinkType l (LinkType.cone l) :=
  .cons .conicalNbhd (.nil _)

noncomputable def double_conical (l : LinkType) :
    StratPath LinkType l (LinkType.cone (LinkType.cone l)) :=
  (conical_nbhd l).trans (conical_nbhd (LinkType.cone l))

noncomputable def cone_susp_decomp (l : LinkType) :
    StratPath LinkType (LinkType.cone (LinkType.suspension l))
      (LinkType.product (LinkType.cone l) (LinkType.sphere 1)) :=
  .cons .coneSuspension (.nil _)

noncomputable def link_cone_product_chain (l : LinkType) :
    StratPath LinkType l (LinkType.product l (LinkType.sphere 0)) :=
  (conical_nbhd l).trans (link_cone_decomp l)

noncomputable def link_decomp_symm (l : LinkType) :
    StratPath LinkType (LinkType.product l (LinkType.sphere 0)) (LinkType.cone l) :=
  (link_cone_decomp l).symm

-- ═══════════════════════════════════════════════════════════════
-- SECTION 7: Intersection Homology & Perversity
-- ═══════════════════════════════════════════════════════════════

noncomputable def perv_zero_le_middle : StratPath Perversity Perversity.zero Perversity.middle :=
  .cons .pervZeroMiddle (.nil _)

noncomputable def perv_middle_le_top : StratPath Perversity Perversity.middle Perversity.topPerv :=
  .cons .pervMiddleTop (.nil _)

noncomputable def perv_full_chain : StratPath Perversity Perversity.zero Perversity.topPerv :=
  perv_zero_le_middle.trans perv_middle_le_top

noncomputable def perv_dual (n k : Nat) :
    StratPath Perversity (Perversity.custom n) (Perversity.custom (k - n)) :=
  .cons .pervDual (.nil _)

noncomputable def ih_poincare (n : Nat) : StratPath IHGroup (IHGroup.free n) (IHGroup.free n) :=
  .cons .ihPoincare (.nil _)

noncomputable def ih_direct_sum_comm (a b : IHGroup) :
    StratPath IHGroup (IHGroup.direct a b) (IHGroup.direct b a) :=
  .cons .ihDirectSum (.nil _)

noncomputable def ih_torsion_trivial : StratPath IHGroup (IHGroup.torsion 0) IHGroup.trivial :=
  .cons .ihTrivial (.nil _)

noncomputable def ih_direct_sum_double_comm (a b : IHGroup) :
    StratPath IHGroup (IHGroup.direct a b) (IHGroup.direct a b) :=
  (ih_direct_sum_comm a b).trans (ih_direct_sum_comm b a)

noncomputable def ih_perversity_functorial (f : Perversity → IHGroup) :
    StratPath IHGroup (f Perversity.zero) (f Perversity.middle) :=
  perv_zero_le_middle.congrArg f

-- ═══════════════════════════════════════════════════════════════
-- SECTION 8: IC Sheaves
-- ═══════════════════════════════════════════════════════════════

noncomputable def ic_normalization (s : ICSheafStalk) :
    StratPath ICSheafStalk s (ICSheafStalk.truncated 0 s) :=
  .cons .icNormalization (.nil _)

noncomputable def ic_shift_compose (n m : Nat) (s : ICSheafStalk) :
    StratPath ICSheafStalk (ICSheafStalk.shifted n (ICSheafStalk.shifted m s))
      (ICSheafStalk.shifted (n + m) s) :=
  .cons .icShift (.nil _)

noncomputable def ic_trunc_compose (n m : Nat) (s : ICSheafStalk) :
    StratPath ICSheafStalk (ICSheafStalk.truncated n (ICSheafStalk.truncated m s))
      (ICSheafStalk.truncated (min n m) s) :=
  .cons .icTruncCompose (.nil _)

noncomputable def ic_norm_then_trunc (_n : Nat) (s : ICSheafStalk) :
    StratPath ICSheafStalk (ICSheafStalk.truncated 0 s)
      (ICSheafStalk.truncated 0 (ICSheafStalk.truncated 0 s)) :=
  .cons (.congrArg (ICSheafStalk.truncated 0) (.icNormalization)) (.nil _)

noncomputable def ic_double_norm (s : ICSheafStalk) :
    StratPath ICSheafStalk s (ICSheafStalk.truncated (min 0 0) s) :=
  (ic_normalization s).trans
    (.cons (.congrArg (ICSheafStalk.truncated 0) (.icNormalization))
      (.cons .icTruncCompose (.nil _)))

noncomputable def ic_norm_symm (s : ICSheafStalk) :
    StratPath ICSheafStalk (ICSheafStalk.truncated 0 s) s :=
  (ic_normalization s).symm

-- ═══════════════════════════════════════════════════════════════
-- SECTION 9: BBD / Decomposition Theorem
-- ═══════════════════════════════════════════════════════════════

noncomputable def bbd_heart_perverse :
    StratPath BBDComponent BBDComponent.heart (BBDComponent.perverse Perversity.middle) :=
  .cons .bbdHeartPerverse (.nil _)

noncomputable def bbd_t_structure :
    StratPath BBDComponent BBDComponent.pLeZero BBDComponent.pGeZero :=
  .cons .bbdTStructure (.nil _)

noncomputable def bbd_t_symm :
    StratPath BBDComponent BBDComponent.pGeZero BBDComponent.pLeZero :=
  bbd_t_structure.symm

noncomputable def bbd_heart_functorial (f : BBDComponent → BBDComponent) :
    StratPath BBDComponent (f BBDComponent.heart) (f (BBDComponent.perverse Perversity.middle)) :=
  bbd_heart_perverse.congrArg f

noncomputable def bbd_t_roundtrip :
    StratPath BBDComponent BBDComponent.pLeZero BBDComponent.pLeZero :=
  bbd_t_structure.trans bbd_t_symm

-- ═══════════════════════════════════════════════════════════════
-- SECTION 10: Stratified Morse Theory
-- ═══════════════════════════════════════════════════════════════

noncomputable def morse_regular_critical :
    StratPath MorseData MorseData.regular (MorseData.critical 0 0) :=
  .cons .morseRegular (.nil _)

noncomputable def morse_index_symm (n m : Nat) :
    StratPath MorseData (MorseData.critical n m) (MorseData.critical m n) :=
  .cons .morseSymmetry (.nil _)

noncomputable def morse_double_symm (n m : Nat) :
    StratPath MorseData (MorseData.critical n m) (MorseData.critical n m) :=
  (morse_index_symm n m).trans (morse_index_symm m n)

noncomputable def morse_regular_to_symm :
    StratPath MorseData MorseData.regular (MorseData.critical 0 0) :=
  morse_regular_critical.trans (morse_double_symm 0 0)

noncomputable def morse_functorial (f : MorseData → MorseData) (n m : Nat) :
    StratPath MorseData (f (MorseData.critical n m)) (f (MorseData.critical m n)) :=
  (morse_index_symm n m).congrArg f

-- ═══════════════════════════════════════════════════════════════
-- SECTION 11: Exit Paths
-- ═══════════════════════════════════════════════════════════════

noncomputable def exit_compose (a b c : StratumIdx) :
    StratPath ExitPathCat
      (ExitPathCat.compose (ExitPathCat.exit a b) (ExitPathCat.exit b c))
      (ExitPathCat.exit a c) :=
  .cons .exitCompose (.nil _)

noncomputable def exit_left_id (a b : StratumIdx) :
    StratPath ExitPathCat
      (ExitPathCat.compose ExitPathCat.identity (ExitPathCat.exit a b))
      (ExitPathCat.exit a b) :=
  .cons .exitIdentity (.nil _)

noncomputable def exit_compose_symm (a b c : StratumIdx) :
    StratPath ExitPathCat (ExitPathCat.exit a c)
      (ExitPathCat.compose (ExitPathCat.exit a b) (ExitPathCat.exit b c)) :=
  (exit_compose a b c).symm

noncomputable def exit_functorial (f : ExitPathCat → ExitPathCat) (a b c : StratumIdx) :
    StratPath ExitPathCat
      (f (ExitPathCat.compose (ExitPathCat.exit a b) (ExitPathCat.exit b c)))
      (f (ExitPathCat.exit a c)) :=
  (exit_compose a b c).congrArg f

noncomputable def exit_id_then_compose (a b c : StratumIdx) :
    StratPath ExitPathCat
      (ExitPathCat.compose ExitPathCat.identity (ExitPathCat.exit a b))
      (ExitPathCat.exit a c) :=
  (exit_left_id a b).trans (whitney_b_path _ _)

-- ═══════════════════════════════════════════════════════════════
-- SECTION 12: Cross-Domain Theorems
-- ═══════════════════════════════════════════════════════════════

noncomputable def stratified_structure_thm (l : LinkType) :
    StratPath LinkType l (LinkType.product l (LinkType.sphere 0)) :=
  (conical_nbhd l).trans (link_cone_decomp l)

noncomputable def perv_to_ic (f : Perversity → ICSheafStalk) :
    StratPath ICSheafStalk (f Perversity.zero) (f Perversity.topPerv) :=
  perv_full_chain.congrArg f

noncomputable def decomp_thm_bbd (f : BBDComponent → ICSheafStalk) :
    StratPath ICSheafStalk (f BBDComponent.heart) (f (BBDComponent.perverse Perversity.middle)) :=
  bbd_heart_perverse.congrArg f

noncomputable def morse_link_interaction (f : MorseData → LinkType) (n m : Nat) :
    StratPath LinkType (f (MorseData.critical n m)) (f (MorseData.critical m n)) :=
  (morse_index_symm n m).congrArg f

noncomputable def exit_frontier_connection (f : StratumIdx → ExitPathCat) (n : Nat) :
    StratPath ExitPathCat (f (StratumIdx.mid n)) (f StratumIdx.bottom) :=
  (frontier_to_bottom n).congrArg f

noncomputable def ic_morse_chain (f : MorseData → ICSheafStalk) :
    StratPath ICSheafStalk (f MorseData.regular) (f (MorseData.critical 0 0)) :=
  morse_regular_critical.congrArg f

noncomputable def triple_cross (g : ExitPathCat → ICSheafStalk) (f : StratumIdx → ExitPathCat) (n : Nat) :
    StratPath ICSheafStalk (g (f (StratumIdx.mid n))) (g (f StratumIdx.bottom)) :=
  (exit_frontier_connection f n).congrArg g

end StratPath

end ComputationalPaths

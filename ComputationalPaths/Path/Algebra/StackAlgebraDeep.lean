/-
# Stack and Gerbe Theory via Computational Paths

This module develops a large collection of path-algebraic lemmas for:

- fibered categories and descent data
- stacks over sites and Cech groupoids
- band and gerbe structure
- 2-descent and stack quotients
- Deligne-Mumford and algebraic stacks
- coherence of descent

All equalities are expressed using `Path` operations (`Path.trans`, `Path.symm`,
`Path.congrArg`) and their algebraic laws.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.StackAlgebraDeep

open ComputationalPaths.Path

universe u

/-! ## Core stack-flavored structures -/

structure Site where
  Obj : Type u
  Cover : Obj → Type u
  refine : {U : Obj} → Cover U → Obj
  overlap : {U : Obj} → Cover U → Cover U → Obj

structure FiberedCategory (B : Type u) where
  Fib : B → Type u
  pull : {U V : B} → Path U V → Fib V → Fib U
  pull_refl : {U : B} → (x : Fib U) → Path (pull (Path.refl U) x) x
  pull_trans :
    {U V W : B} → (p : Path U V) → (q : Path V W) → (x : Fib W) →
      Path (pull (Path.trans p q) x) (pull p (pull q x))

structure DescentData (B : Type u) (F : FiberedCategory B) where
  Sym : {U V : B} → Path U V → F.Fib U → F.Fib V
  Sym_refl : {U : B} → (x : F.Fib U) → Path (Sym (Path.refl U) x) x
  Sym_trans :
    {U V W : B} → (p : Path U V) → (q : Path V W) → (x : F.Fib U) →
      Path (Sym (Path.trans p q) x) (Sym q (Sym p x))
  Gam :
    {U V W : B} → (p : Path U V) → (q : Path V W) → (x : F.Fib U) →
      Path (Sym q (Sym p x)) (Sym (Path.trans p q) x)

structure StackOverSite (S : Site) where
  fib : FiberedCategory S.Obj
  desc : DescentData S.Obj fib
  gluing : True

structure CechGroupoid (X : Type u) where
  Obj : Type u
  Mor : Type u
  src : Mor → Obj
  tgt : Mor → Obj
  idMor : Obj → Mor
  comp : Mor → Mor → Mor
  left_id : (m : Mor) → Path (comp (idMor (src m)) m) m
  right_id : (m : Mor) → Path (comp m (idMor (tgt m))) m
  assoc : (a b c : Mor) → Path (comp (comp a b) c) (comp a (comp b c))

structure Band (X : Type u) where
  GroupObj : Type u
  act : GroupObj → X → X
  mul : GroupObj → GroupObj → GroupObj
  unit : GroupObj
  inv : GroupObj → GroupObj
  act_unit : (x : X) → Path (act unit x) x
  act_mul : (g h : GroupObj) → (x : X) → Path (act (mul g h) x) (act g (act h x))
  inv_left : (g : GroupObj) → Path (mul (inv g) g) unit
  inv_right : (g : GroupObj) → Path (mul g (inv g)) unit

structure Gerbe (S : Site) where
  baseStack : StackOverSite S
  band : Band S.Obj
  local_nonempty : True
  local_connected : True
  band_action_coh : (U : S.Obj) → Path (band.act band.unit U) U

structure TwoDescent (B : Type u) (F : FiberedCategory B) where
  one : {U V : B} → Path U V → F.Fib U → F.Fib V
  two :
    {U V W : B} → (p : Path U V) → (q : Path V W) → (x : F.Fib U) →
      Path (one q (one p x)) (one (Path.trans p q) x)
  triangle :
    {U V : B} → (p : Path U V) → (x : F.Fib U) →
      Path (one p x) (one p x)
  pentagon :
    {U V W Z : B} →
      (p : Path U V) → (q : Path V W) → (r : Path W Z) → (x : F.Fib U) →
      Path (one r (one q (one p x))) (one (Path.trans (Path.trans p q) r) x)

structure StackQuotient (X G : Type u) where
  action : G → X → X
  orbit : X → X
  quotient : Type u
  proj : X → quotient
  orbit_fixed : (x : X) → Path (orbit x) (orbit x)
  action_orbit : (g : G) → (x : X) → Path (orbit (action g x)) (orbit x)

structure DeligneMumfordStack (S : Site) where
  stack : StackOverSite S
  atlas : S.Obj
  etale_diag : Path atlas atlas
  finite_inertia : True

structure AlgebraicStack (S : Site) where
  stack : StackOverSite S
  atlas : S.Obj
  smooth_diag : Path atlas atlas
  qc_diag : True

structure DescentCoherence (B : Type u) (F : FiberedCategory B) (D : DescentData B F) where
  unit_coh : {U : B} → (x : F.Fib U) → Path (D.Sym (Path.refl U) x) x
  assoc_coh :
    {U V W Z : B} →
      (p : Path U V) → (q : Path V W) → (r : Path W Z) → (x : F.Fib U) →
      Path (D.Sym r (D.Sym q (D.Sym p x))) (D.Sym (Path.trans (Path.trans p q) r) x)

/-! ## Fibered category lemmas -/

section FiberedCategoryLemmas

variable {B : Type u} (F : FiberedCategory B)
variable {U V W : B} (p : Path U V) (q : Path V W) (x : F.Fib W)

theorem fiber_pull_trans_symm :
    Path.symm (Path.trans (F.pull_trans p q x) (Path.symm (F.pull_trans p q x))) =
      Path.trans
        (Path.symm (Path.symm (F.pull_trans p q x)))
        (Path.symm (F.pull_trans p q x)) :=
  Path.symm_trans _ _

theorem fiber_pull_trans_double_symm :
    Path.symm (Path.symm (F.pull_trans p q x)) = F.pull_trans p q x :=
  Path.symm_symm _

theorem fiber_pull_trans_assoc :
    Path.trans
      (Path.trans (F.pull_trans p q x) (Path.symm (F.pull_trans p q x)))
      (F.pull_trans p q x) =
    Path.trans
      (F.pull_trans p q x)
      (Path.trans (Path.symm (F.pull_trans p q x)) (F.pull_trans p q x)) :=
  Path.trans_assoc _ _ _

theorem fiber_pull_trans_congrArg (hMap : F.Fib U → F.Fib U) :
    Path.congrArg hMap (Path.trans (F.pull_trans p q x) (Path.symm (F.pull_trans p q x))) =
      Path.trans
        (Path.congrArg hMap (F.pull_trans p q x))
        (Path.congrArg hMap (Path.symm (F.pull_trans p q x))) :=
  Path.congrArg_trans hMap _ _

theorem fiber_pull_trans_congrArg_symm (hMap : F.Fib U → F.Fib U) :
    Path.congrArg hMap (Path.symm (F.pull_trans p q x)) =
      Path.symm (Path.congrArg hMap (F.pull_trans p q x)) :=
  Path.congrArg_symm hMap _

theorem fiber_pull_trans_roundtrip_toEq :
    (Path.trans (F.pull_trans p q x) (Path.symm (F.pull_trans p q x))).toEq = rfl := by
  simp

theorem fiber_pull_trans_fourfold :
    Path.trans
      (Path.trans
        (Path.trans (F.pull_trans p q x) (Path.symm (F.pull_trans p q x)))
        (F.pull_trans p q x))
      (Path.symm (F.pull_trans p q x)) =
    Path.trans
      (F.pull_trans p q x)
      (Path.trans
        (Path.symm (F.pull_trans p q x))
        (Path.trans (F.pull_trans p q x) (Path.symm (F.pull_trans p q x)))) :=
  Path.trans_assoc_fourfold _ _ _ _

variable {U0 : B} (x0 : F.Fib U0)

theorem fiber_pull_refl_double_symm :
    Path.symm (Path.symm (F.pull_refl x0)) = F.pull_refl x0 :=
  Path.symm_symm _

theorem fiber_pull_refl_congrArg_symm (hMap : F.Fib U0 → F.Fib U0) :
    Path.congrArg hMap (Path.symm (F.pull_refl x0)) =
      Path.symm (Path.congrArg hMap (F.pull_refl x0)) :=
  Path.congrArg_symm hMap _

theorem fiber_pull_refl_roundtrip_toEq :
    (Path.trans (F.pull_refl x0) (Path.symm (F.pull_refl x0))).toEq = rfl := by
  simp

end FiberedCategoryLemmas

/-! ## Descent-data lemmas -/

section DescentDataLemmas

variable {B : Type u} {F : FiberedCategory B} (D : DescentData B F)
variable {U V W Z : B} (p : Path U V) (q : Path V W) (r : Path W Z) (x : F.Fib U)

theorem descent_Sym_trans_double_symm :
    Path.symm (Path.symm (D.Sym_trans p q x)) = D.Sym_trans p q x :=
  Path.symm_symm _

theorem descent_Sym_trans_symm_trans :
    Path.symm (Path.trans (D.Sym_trans p q x) (Path.symm (D.Sym_trans p q x))) =
      Path.trans
        (Path.symm (Path.symm (D.Sym_trans p q x)))
        (Path.symm (D.Sym_trans p q x)) :=
  Path.symm_trans _ _

theorem descent_Sym_trans_congrArg (hMap : F.Fib W → F.Fib W) :
    Path.congrArg hMap (Path.trans (D.Sym_trans p q x) (Path.symm (D.Sym_trans p q x))) =
      Path.trans
        (Path.congrArg hMap (D.Sym_trans p q x))
        (Path.congrArg hMap (Path.symm (D.Sym_trans p q x))) :=
  Path.congrArg_trans hMap _ _

theorem descent_Sym_trans_assoc :
    Path.trans
      (Path.trans (D.Sym_trans p q x) (Path.symm (D.Sym_trans p q x)))
      (D.Sym_trans p q x) =
    Path.trans
      (D.Sym_trans p q x)
      (Path.trans (Path.symm (D.Sym_trans p q x)) (D.Sym_trans p q x)) :=
  Path.trans_assoc _ _ _

theorem descent_Gam_double_symm :
    Path.symm (Path.symm (D.Gam p q x)) = D.Gam p q x :=
  Path.symm_symm _

theorem descent_Gam_congrArg_symm (hMap : F.Fib W → F.Fib W) :
    Path.congrArg hMap (Path.symm (D.Gam p q x)) =
      Path.symm (Path.congrArg hMap (D.Gam p q x)) :=
  Path.congrArg_symm hMap _

theorem descent_Gam_roundtrip_toEq :
    (Path.trans (D.Gam p q x) (Path.symm (D.Gam p q x))).toEq = rfl := by
  simp

theorem descent_Sym_trans_roundtrip_toEq :
    (Path.trans (D.Sym_trans p q x) (Path.symm (D.Sym_trans p q x))).toEq = rfl := by
  simp

theorem descent_Gam_symm_trans :
    Path.symm (Path.trans (D.Gam p q x) (Path.symm (D.Gam p q x))) =
      Path.trans
        (Path.symm (Path.symm (D.Gam p q x)))
        (Path.symm (D.Gam p q x)) :=
  Path.symm_trans _ _

theorem descent_SymGam_bridge_assoc :
    Path.trans (Path.trans (D.Sym_trans p q x) (D.Gam p q x)) (D.Sym_trans p q x) =
      Path.trans (D.Sym_trans p q x) (Path.trans (D.Gam p q x) (D.Sym_trans p q x)) :=
  Path.trans_assoc _ _ _

theorem descent_Sym_threefold :
    Path.trans (Path.trans (Path.refl (D.Sym q (D.Sym p x))) (D.Gam p q x))
      (D.Sym_trans p q x) =
    Path.trans (Path.refl (D.Sym q (D.Sym p x)))
      (Path.trans (D.Gam p q x) (D.Sym_trans p q x)) :=
  Path.trans_assoc _ _ _

variable {U0 : B} (x0 : F.Fib U0)

theorem descent_Sym_refl_double_symm :
    Path.symm (Path.symm (D.Sym_refl x0)) = D.Sym_refl x0 :=
  Path.symm_symm _

theorem descent_Sym_refl_congrArg (hMap : F.Fib U0 → F.Fib U0) :
    Path.congrArg hMap (Path.symm (D.Sym_refl x0)) =
      Path.symm (Path.congrArg hMap (D.Sym_refl x0)) :=
  Path.congrArg_symm hMap _

end DescentDataLemmas

/-! ## Stack-over-site lemmas -/

section StackOverSiteLemmas

variable {S : Site} (K : StackOverSite S)
variable {U V W : S.Obj} (p : Path U V) (q : Path V W) (x : K.fib.Fib U)

theorem stack_desc_refl_double_symm :
    Path.symm (Path.symm (K.desc.Sym_refl x)) = K.desc.Sym_refl x :=
  Path.symm_symm _

theorem stack_desc_trans_double_symm :
    Path.symm (Path.symm (K.desc.Sym_trans p q x)) = K.desc.Sym_trans p q x :=
  Path.symm_symm _

theorem stack_desc_Gam_double_symm :
    Path.symm (Path.symm (K.desc.Gam p q x)) = K.desc.Gam p q x :=
  Path.symm_symm _

theorem stack_desc_trans_assoc :
    Path.trans
      (Path.trans (K.desc.Sym_trans p q x) (Path.symm (K.desc.Sym_trans p q x)))
      (K.desc.Sym_trans p q x) =
    Path.trans
      (K.desc.Sym_trans p q x)
      (Path.trans (Path.symm (K.desc.Sym_trans p q x)) (K.desc.Sym_trans p q x)) :=
  Path.trans_assoc _ _ _

theorem stack_desc_refl_roundtrip_toEq :
    (Path.trans (K.desc.Sym_refl x) (Path.symm (K.desc.Sym_refl x))).toEq = rfl := by
  simp

theorem stack_desc_trans_congrArg (hMap : K.fib.Fib W → K.fib.Fib W) :
    Path.congrArg hMap (Path.symm (K.desc.Sym_trans p q x)) =
      Path.symm (Path.congrArg hMap (K.desc.Sym_trans p q x)) :=
  Path.congrArg_symm hMap _

theorem stack_desc_Gam_roundtrip_toEq :
    (Path.trans (K.desc.Gam p q x) (Path.symm (K.desc.Gam p q x))).toEq = rfl := by
  simp

theorem stack_gluing_true (K0 : StackOverSite S) : True :=
  K0.gluing

end StackOverSiteLemmas

/-! ## Cech groupoid lemmas -/

section CechGroupoidLemmas

variable {X : Type u} (Gd : CechGroupoid X)
variable (m a b c : Gd.Mor)

theorem cech_left_id_double_symm :
    Path.symm (Path.symm (Gd.left_id m)) = Gd.left_id m :=
  Path.symm_symm _

theorem cech_right_id_double_symm :
    Path.symm (Path.symm (Gd.right_id m)) = Gd.right_id m :=
  Path.symm_symm _

theorem cech_assoc_double_symm :
    Path.symm (Path.symm (Gd.assoc a b c)) = Gd.assoc a b c :=
  Path.symm_symm _

theorem cech_left_id_congrArg_symm (hMap : Gd.Mor → Gd.Mor) :
    Path.congrArg hMap (Path.symm (Gd.left_id m)) =
      Path.symm (Path.congrArg hMap (Gd.left_id m)) :=
  Path.congrArg_symm hMap _

theorem cech_right_id_congrArg_symm (hMap : Gd.Mor → Gd.Mor) :
    Path.congrArg hMap (Path.symm (Gd.right_id m)) =
      Path.symm (Path.congrArg hMap (Gd.right_id m)) :=
  Path.congrArg_symm hMap _

theorem cech_assoc_congrArg (hMap : Gd.Mor → Gd.Mor) :
    Path.congrArg hMap (Path.trans (Gd.assoc a b c) (Path.symm (Gd.assoc a b c))) =
      Path.trans
        (Path.congrArg hMap (Gd.assoc a b c))
        (Path.congrArg hMap (Path.symm (Gd.assoc a b c))) :=
  Path.congrArg_trans hMap _ _

theorem cech_left_roundtrip_toEq :
    (Path.trans (Gd.left_id m) (Path.symm (Gd.left_id m))).toEq = rfl := by
  simp

theorem cech_right_roundtrip_toEq :
    (Path.trans (Gd.right_id m) (Path.symm (Gd.right_id m))).toEq = rfl := by
  simp

theorem cech_assoc_chain_reassoc :
    Path.trans
      (Path.trans (Gd.assoc a b c) (Path.symm (Gd.assoc a b c)))
      (Gd.assoc a b c) =
    Path.trans
      (Gd.assoc a b c)
      (Path.trans (Path.symm (Gd.assoc a b c)) (Gd.assoc a b c)) :=
  Path.trans_assoc _ _ _

theorem cech_assoc_symm_trans :
    Path.symm (Path.trans (Gd.assoc a b c) (Path.symm (Gd.assoc a b c))) =
      Path.trans
        (Path.symm (Path.symm (Gd.assoc a b c)))
        (Path.symm (Gd.assoc a b c)) :=
  Path.symm_trans _ _

theorem cech_assoc_fourfold :
    Path.trans
      (Path.trans
        (Path.trans (Gd.assoc a b c) (Path.symm (Gd.assoc a b c)))
        (Gd.assoc a b c))
      (Path.symm (Gd.assoc a b c)) =
    Path.trans
      (Gd.assoc a b c)
      (Path.trans
        (Path.symm (Gd.assoc a b c))
        (Path.trans (Gd.assoc a b c) (Path.symm (Gd.assoc a b c)))) :=
  Path.trans_assoc_fourfold _ _ _ _

end CechGroupoidLemmas

/-! ## Band and gerbe lemmas -/

section BandLemmas

variable {X : Type u} (Bnd : Band X)
variable (g h : Bnd.GroupObj) (x : X)

theorem band_act_unit_double_symm :
    Path.symm (Path.symm (Bnd.act_unit x)) = Bnd.act_unit x :=
  Path.symm_symm _

theorem band_act_mul_double_symm :
    Path.symm (Path.symm (Bnd.act_mul g h x)) = Bnd.act_mul g h x :=
  Path.symm_symm _

theorem band_inv_left_double_symm :
    Path.symm (Path.symm (Bnd.inv_left g)) = Bnd.inv_left g :=
  Path.symm_symm _

theorem band_inv_right_double_symm :
    Path.symm (Path.symm (Bnd.inv_right g)) = Bnd.inv_right g :=
  Path.symm_symm _

theorem band_act_mul_assoc_chain :
    Path.trans
      (Path.trans (Bnd.act_mul g h x) (Path.symm (Bnd.act_mul g h x)))
      (Bnd.act_mul g h x) =
    Path.trans
      (Bnd.act_mul g h x)
      (Path.trans (Path.symm (Bnd.act_mul g h x)) (Bnd.act_mul g h x)) :=
  Path.trans_assoc _ _ _

theorem band_act_mul_congrArg (hMap : X → X) :
    Path.congrArg hMap (Path.trans (Bnd.act_mul g h x) (Path.symm (Bnd.act_mul g h x))) =
      Path.trans
        (Path.congrArg hMap (Bnd.act_mul g h x))
        (Path.congrArg hMap (Path.symm (Bnd.act_mul g h x))) :=
  Path.congrArg_trans hMap _ _

theorem band_inv_left_roundtrip_toEq :
    (Path.trans (Bnd.inv_left g) (Path.symm (Bnd.inv_left g))).toEq = rfl := by
  simp

theorem band_inv_right_roundtrip_toEq :
    (Path.trans (Bnd.inv_right g) (Path.symm (Bnd.inv_right g))).toEq = rfl := by
  simp

theorem band_act_unit_congrArg_symm (hMap : X → X) :
    Path.congrArg hMap (Path.symm (Bnd.act_unit x)) =
      Path.symm (Path.congrArg hMap (Bnd.act_unit x)) :=
  Path.congrArg_symm hMap _

theorem band_act_mul_symm_trans :
    Path.symm (Path.trans (Bnd.act_mul g h x) (Path.symm (Bnd.act_mul g h x))) =
      Path.trans
        (Path.symm (Path.symm (Bnd.act_mul g h x)))
        (Path.symm (Bnd.act_mul g h x)) :=
  Path.symm_trans _ _

end BandLemmas

section GerbeLemmas

variable {S : Site} (Ger : Gerbe S) (U : S.Obj)

theorem gerbe_band_action_double_symm :
    Path.symm (Path.symm (Ger.band_action_coh U)) = Ger.band_action_coh U :=
  Path.symm_symm _

theorem gerbe_band_action_congrArg_symm (hMap : S.Obj → S.Obj) :
    Path.congrArg hMap (Path.symm (Ger.band_action_coh U)) =
      Path.symm (Path.congrArg hMap (Ger.band_action_coh U)) :=
  Path.congrArg_symm hMap _

theorem gerbe_band_action_roundtrip_toEq :
    (Path.trans (Ger.band_action_coh U) (Path.symm (Ger.band_action_coh U))).toEq = rfl := by
  simp

theorem gerbe_band_action_assoc_chain :
    Path.trans
      (Path.trans (Ger.band_action_coh U) (Path.symm (Ger.band_action_coh U)))
      (Ger.band_action_coh U) =
    Path.trans
      (Ger.band_action_coh U)
      (Path.trans (Path.symm (Ger.band_action_coh U)) (Ger.band_action_coh U)) :=
  Path.trans_assoc _ _ _

theorem gerbe_local_nonempty_true (Ger0 : Gerbe S) : True :=
  Ger0.local_nonempty

theorem gerbe_local_connected_true (Ger0 : Gerbe S) : True :=
  Ger0.local_connected

end GerbeLemmas

/-! ## 2-descent lemmas -/

section TwoDescentLemmas

variable {B : Type u} {F : FiberedCategory B} (T : TwoDescent B F)
variable {U V W Z : B} (p : Path U V) (q : Path V W) (r : Path W Z) (x : F.Fib U)

theorem twoDescent_two_double_symm :
    Path.symm (Path.symm (T.two p q x)) = T.two p q x :=
  Path.symm_symm _

theorem twoDescent_triangle_double_symm :
    Path.symm (Path.symm (T.triangle p x)) = T.triangle p x :=
  Path.symm_symm _

theorem twoDescent_pentagon_double_symm :
    Path.symm (Path.symm (T.pentagon p q r x)) = T.pentagon p q r x :=
  Path.symm_symm _

theorem twoDescent_two_congrArg_symm (hMap : F.Fib W → F.Fib W) :
    Path.congrArg hMap (Path.symm (T.two p q x)) =
      Path.symm (Path.congrArg hMap (T.two p q x)) :=
  Path.congrArg_symm hMap _

theorem twoDescent_triangle_roundtrip_toEq :
    (Path.trans (T.triangle p x) (Path.symm (T.triangle p x))).toEq = rfl := by
  simp

theorem twoDescent_pentagon_assoc_chain :
    Path.trans
      (Path.trans (T.pentagon p q r x) (Path.symm (T.pentagon p q r x)))
      (T.pentagon p q r x) =
    Path.trans
      (T.pentagon p q r x)
      (Path.trans (Path.symm (T.pentagon p q r x)) (T.pentagon p q r x)) :=
  Path.trans_assoc _ _ _

theorem twoDescent_two_assoc :
    Path.trans (Path.trans (T.two p q x) (Path.symm (T.two p q x))) (T.two p q x) =
      Path.trans (T.two p q x) (Path.trans (Path.symm (T.two p q x)) (T.two p q x)) :=
  Path.trans_assoc _ _ _

theorem twoDescent_pentagon_roundtrip_toEq :
    (Path.trans (T.pentagon p q r x) (Path.symm (T.pentagon p q r x))).toEq = rfl := by
  simp

theorem twoDescent_two_symm_trans :
    Path.symm (Path.trans (T.two p q x) (Path.symm (T.two p q x))) =
      Path.trans (Path.symm (Path.symm (T.two p q x))) (Path.symm (T.two p q x)) :=
  Path.symm_trans _ _

theorem twoDescent_triangle_congrArg (hMap : F.Fib V → F.Fib V) :
    Path.congrArg hMap (Path.trans (T.triangle p x) (Path.symm (T.triangle p x))) =
      Path.trans
        (Path.congrArg hMap (T.triangle p x))
        (Path.congrArg hMap (Path.symm (T.triangle p x))) :=
  Path.congrArg_trans hMap _ _

end TwoDescentLemmas

/-! ## Quotient and algebraic stack lemmas -/

section QuotientAndAlgebraicLemmas

variable {X G : Type u} (Q : StackQuotient X G) (g : G) (x : X)

theorem quotient_orbit_fixed_double_symm :
    Path.symm (Path.symm (Q.orbit_fixed x)) = Q.orbit_fixed x :=
  Path.symm_symm _

theorem quotient_action_orbit_double_symm :
    Path.symm (Path.symm (Q.action_orbit g x)) = Q.action_orbit g x :=
  Path.symm_symm _

theorem quotient_action_orbit_congrArg_symm (hMap : X → X) :
    Path.congrArg hMap (Path.symm (Q.action_orbit g x)) =
      Path.symm (Path.congrArg hMap (Q.action_orbit g x)) :=
  Path.congrArg_symm hMap _

theorem quotient_action_orbit_roundtrip_toEq :
    (Path.trans (Q.action_orbit g x) (Path.symm (Q.action_orbit g x))).toEq = rfl := by
  simp

theorem quotient_orbit_fixed_assoc_chain :
    Path.trans
      (Path.trans (Q.orbit_fixed x) (Path.symm (Q.orbit_fixed x)))
      (Q.orbit_fixed x) =
    Path.trans
      (Q.orbit_fixed x)
      (Path.trans (Path.symm (Q.orbit_fixed x)) (Q.orbit_fixed x)) :=
  Path.trans_assoc _ _ _

theorem quotient_action_orbit_symm_trans :
    Path.symm (Path.trans (Q.action_orbit g x) (Path.symm (Q.action_orbit g x))) =
      Path.trans
        (Path.symm (Path.symm (Q.action_orbit g x)))
        (Path.symm (Q.action_orbit g x)) :=
  Path.symm_trans _ _

end QuotientAndAlgebraicLemmas

section DMAndAlgebraicLemmas

variable {S : Site} (DM : DeligneMumfordStack S)

theorem dm_diag_double_symm :
    Path.symm (Path.symm DM.etale_diag) = DM.etale_diag :=
  Path.symm_symm _

theorem dm_diag_congrArg_symm (hMap : S.Obj → S.Obj) :
    Path.congrArg hMap (Path.symm DM.etale_diag) =
      Path.symm (Path.congrArg hMap DM.etale_diag) :=
  Path.congrArg_symm hMap _

theorem dm_finite_inertia_true (DM0 : DeligneMumfordStack S) : True :=
  DM0.finite_inertia

theorem dm_diag_roundtrip_toEq :
    (Path.trans DM.etale_diag (Path.symm DM.etale_diag)).toEq = rfl := by
  simp

variable (ASt : AlgebraicStack S)

theorem alg_diag_double_symm :
    Path.symm (Path.symm ASt.smooth_diag) = ASt.smooth_diag :=
  Path.symm_symm _

theorem alg_diag_congrArg_symm (hMap : S.Obj → S.Obj) :
    Path.congrArg hMap (Path.symm ASt.smooth_diag) =
      Path.symm (Path.congrArg hMap ASt.smooth_diag) :=
  Path.congrArg_symm hMap _

theorem alg_qc_diag_true (ASt0 : AlgebraicStack S) : True :=
  ASt0.qc_diag

theorem alg_diag_roundtrip_toEq :
    (Path.trans ASt.smooth_diag (Path.symm ASt.smooth_diag)).toEq = rfl := by
  simp

end DMAndAlgebraicLemmas

/-! ## Coherence of descent -/

section CoherenceLemmas

variable {B : Type u} {F : FiberedCategory B} {D : DescentData B F}
variable (Coh : DescentCoherence B F D)
variable {U V W Z : B} (p : Path U V) (q : Path V W) (r : Path W Z) (x : F.Fib U)

theorem coherence_unit_double_symm :
    Path.symm (Path.symm (Coh.unit_coh x)) = Coh.unit_coh x :=
  Path.symm_symm _

theorem coherence_assoc_double_symm :
    Path.symm (Path.symm (Coh.assoc_coh p q r x)) = Coh.assoc_coh p q r x :=
  Path.symm_symm _

theorem coherence_unit_congrArg_symm (hMap : F.Fib U → F.Fib U) :
    Path.congrArg hMap (Path.symm (Coh.unit_coh x)) =
      Path.symm (Path.congrArg hMap (Coh.unit_coh x)) :=
  Path.congrArg_symm hMap _

theorem coherence_assoc_congrArg (hMap : F.Fib Z → F.Fib Z) :
    Path.congrArg hMap (Path.trans (Coh.assoc_coh p q r x) (Path.symm (Coh.assoc_coh p q r x))) =
      Path.trans
        (Path.congrArg hMap (Coh.assoc_coh p q r x))
        (Path.congrArg hMap (Path.symm (Coh.assoc_coh p q r x))) :=
  Path.congrArg_trans hMap _ _

theorem coherence_assoc_chain :
    Path.trans
      (Path.trans (Coh.assoc_coh p q r x) (Path.symm (Coh.assoc_coh p q r x)))
      (Coh.assoc_coh p q r x) =
    Path.trans
      (Coh.assoc_coh p q r x)
      (Path.trans (Path.symm (Coh.assoc_coh p q r x)) (Coh.assoc_coh p q r x)) :=
  Path.trans_assoc _ _ _

theorem coherence_unit_roundtrip_toEq :
    (Path.trans (Coh.unit_coh x) (Path.symm (Coh.unit_coh x))).toEq = rfl := by
  simp

theorem coherence_assoc_roundtrip_toEq :
    (Path.trans (Coh.assoc_coh p q r x) (Path.symm (Coh.assoc_coh p q r x))).toEq = rfl := by
  simp

theorem coherence_assoc_symm_trans :
    Path.symm (Path.trans (Coh.assoc_coh p q r x) (Path.symm (Coh.assoc_coh p q r x))) =
      Path.trans
        (Path.symm (Path.symm (Coh.assoc_coh p q r x)))
        (Path.symm (Coh.assoc_coh p q r x)) :=
  Path.symm_trans _ _

theorem coherence_unit_fourfold :
    Path.trans
      (Path.trans (Path.trans (Coh.unit_coh x) (Path.symm (Coh.unit_coh x))) (Coh.unit_coh x))
      (Path.symm (Coh.unit_coh x)) =
    Path.trans
      (Coh.unit_coh x)
      (Path.trans (Path.symm (Coh.unit_coh x))
        (Path.trans (Coh.unit_coh x) (Path.symm (Coh.unit_coh x)))) :=
  Path.trans_assoc_fourfold _ _ _ _

theorem coherence_assoc_assoc :
    Path.trans
      (Path.trans (Coh.assoc_coh p q r x) (Path.symm (Coh.assoc_coh p q r x)))
      (Path.trans (Coh.assoc_coh p q r x) (Path.symm (Coh.assoc_coh p q r x))) =
    Path.trans
      (Coh.assoc_coh p q r x)
      (Path.trans
        (Path.symm (Coh.assoc_coh p q r x))
        (Path.trans (Coh.assoc_coh p q r x) (Path.symm (Coh.assoc_coh p q r x)))) :=
  Path.trans_assoc _ _ _

end CoherenceLemmas

end ComputationalPaths.Path.Algebra.StackAlgebraDeep

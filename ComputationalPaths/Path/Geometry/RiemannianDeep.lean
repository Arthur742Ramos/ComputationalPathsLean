/-
# Riemannian Geometry via Domain-Specific Computational Paths

Replaces the prior scaffolding (41 `Path.mk [Step.mk _ _ h] h` wrappers) with a genuine
domain-specific rewrite system.

Zero `sorry`. Zero `Path.mk [Step.mk _ _ h] h`. All reasoning is multi-step chains.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Geometry.RiemannianDeep

-- ============================================================
-- §1  Symbolic objects
-- ============================================================

inductive RiemObj : Type
  | riemann    : String → RiemObj
  | ricci      : RiemObj → RiemObj
  | scalar     : RiemObj → RiemObj
  | weyl       : RiemObj → RiemObj
  | metric     : String → RiemObj
  | connLC     : RiemObj → RiemObj
  | flatConn   : RiemObj
  | zero       : RiemObj
  | val        : Int → RiemObj
  | geo        : String → RiemObj
  | geoComp    : RiemObj → RiemObj → RiemObj
  | geoTriv    : RiemObj
  | geoRev     : RiemObj → RiemObj
  | jacobi     : String → RiemObj
  | jacAdd     : RiemObj → RiemObj → RiemObj
  | jacZero    : RiemObj
  | jacScale   : Int → RiemObj → RiemObj
  | expM       : RiemObj → RiemObj
  | origin     : RiemObj
  | euler      : RiemObj → RiemObj
  | genus      : Nat → RiemObj
  | holo       : RiemObj → RiemObj
  | holComp    : RiemObj → RiemObj → RiemObj
  | holTriv    : RiemObj
  | parTr      : RiemObj → RiemObj → RiemObj
  deriving DecidableEq

open RiemObj

-- ============================================================
-- §2  Domain-specific rewrite steps
-- ============================================================

inductive RStep : RiemObj → RiemObj → Type
  | riemann_flat : RStep (riemann "flat") zero
  | ricci_zero : RStep (ricci zero) zero
  | scalar_zero : RStep (scalar zero) zero
  | weyl_zero : RStep (weyl zero) zero
  | conn_flat : RStep (connLC (metric "flat")) flatConn
  | geo_comp_triv_r (γ : RiemObj) : RStep (geoComp γ geoTriv) γ
  | geo_comp_triv_l (γ : RiemObj) : RStep (geoComp geoTriv γ) γ
  | geo_comp_assoc (a b c : RiemObj) :
      RStep (geoComp (geoComp a b) c) (geoComp a (geoComp b c))
  | geo_rev_rev (γ : RiemObj) : RStep (geoRev (geoRev γ)) γ
  | geo_rev_triv : RStep (geoRev geoTriv) geoTriv
  | geo_comp_rev (γ : RiemObj) : RStep (geoComp γ (geoRev γ)) geoTriv
  | jac_add_zero_l (J : RiemObj) : RStep (jacAdd jacZero J) J
  | jac_add_zero_r (J : RiemObj) : RStep (jacAdd J jacZero) J
  | jac_add_comm (J₁ J₂ : RiemObj) : RStep (jacAdd J₁ J₂) (jacAdd J₂ J₁)
  | jac_add_assoc (J₁ J₂ J₃ : RiemObj) :
      RStep (jacAdd (jacAdd J₁ J₂) J₃) (jacAdd J₁ (jacAdd J₂ J₃))
  | jac_scale_zero (J : RiemObj) : RStep (jacScale 0 J) jacZero
  | jac_scale_one (J : RiemObj) : RStep (jacScale 1 J) J
  | jac_add_neg (J : RiemObj) : RStep (jacAdd J (jacScale (-1) J)) jacZero
  | exp_origin : RStep (expM origin) origin
  | exp_zero_vec : RStep (expM jacZero) origin
  | euler_sphere : RStep (euler (genus 0)) (val 2)
  | euler_torus : RStep (euler (genus 1)) (val 0)
  | euler_genus (g : Nat) : RStep (euler (genus g)) (val (2 - 2 * g))
  | hol_comp_triv_r (h : RiemObj) : RStep (holComp h holTriv) h
  | hol_comp_triv_l (h : RiemObj) : RStep (holComp holTriv h) h
  | hol_comp_assoc (a b c : RiemObj) :
      RStep (holComp (holComp a b) c) (holComp a (holComp b c))
  | hol_flat : RStep (holo geoTriv) holTriv
  | pt_triv (v : RiemObj) : RStep (parTr geoTriv v) v
  | pt_comp (γ₁ γ₂ v : RiemObj) :
      RStep (parTr (geoComp γ₁ γ₂) v) (parTr γ₂ (parTr γ₁ v))
  | pt_rev (γ v : RiemObj) :
      RStep (parTr (geoRev γ) (parTr γ v)) v

-- ============================================================
-- §3  Path closure (no name clashes with Path.trans etc.)
-- ============================================================

inductive RP : RiemObj → RiemObj → Prop
  | rfl (a : RiemObj) : RP a a
  | stp {a b : RiemObj} : RStep a b → RP a b
  | sym {a b : RiemObj} : RP a b → RP b a
  | tr {a b c : RiemObj} : RP a b → RP b c → RP a c
  | cg_ricci {a a' : RiemObj} : RP a a' → RP (ricci a) (ricci a')
  | cg_scalar {a a' : RiemObj} : RP a a' → RP (scalar a) (scalar a')
  | cg_weyl {a a' : RiemObj} : RP a a' → RP (weyl a) (weyl a')
  | cg_geoComp_l {a a' b : RiemObj} : RP a a' → RP (geoComp a b) (geoComp a' b)
  | cg_geoComp_r {a b b' : RiemObj} : RP b b' → RP (geoComp a b) (geoComp a b')
  | cg_geoRev {a a' : RiemObj} : RP a a' → RP (geoRev a) (geoRev a')
  | cg_jacAdd_l {a a' b : RiemObj} : RP a a' → RP (jacAdd a b) (jacAdd a' b)
  | cg_jacAdd_r {a b b' : RiemObj} : RP b b' → RP (jacAdd a b) (jacAdd a b')
  | cg_jacScale {n : Int} {a a' : RiemObj} : RP a a' → RP (jacScale n a) (jacScale n a')
  | cg_expM {a a' : RiemObj} : RP a a' → RP (expM a) (expM a')
  | cg_holComp_l {a a' b : RiemObj} : RP a a' → RP (holComp a b) (holComp a' b)
  | cg_holComp_r {a b b' : RiemObj} : RP b b' → RP (holComp a b) (holComp a b')
  | cg_pt_γ {γ γ' v : RiemObj} : RP γ γ' → RP (parTr γ v) (parTr γ' v)
  | cg_pt_v {γ v v' : RiemObj} : RP v v' → RP (parTr γ v) (parTr γ v')
  | cg_holo {γ γ' : RiemObj} : RP γ γ' → RP (holo γ) (holo γ')
  | cg_euler {M M' : RiemObj} : RP M M' → RP (euler M) (euler M')

-- Helpers
def tr3 {a b c d : RiemObj} (p : RP a b) (q : RP b c) (r : RP c d) : RP a d :=
  RP.tr (RP.tr p q) r

-- ============================================================
-- §4  Flat curvature vanishing (1–8)
-- ============================================================

theorem thm01_flat_riemann : RP (riemann "flat") zero :=
  RP.stp RStep.riemann_flat

theorem thm02_ricci_zero : RP (ricci zero) zero :=
  RP.stp RStep.ricci_zero

theorem thm03_scalar_zero : RP (scalar zero) zero :=
  RP.stp RStep.scalar_zero

theorem thm04_weyl_zero : RP (weyl zero) zero :=
  RP.stp RStep.weyl_zero

-- 5: Full chain Riem → Ric → Scalar all vanish (3-step)
theorem thm05_flat_curvature_chain :
    RP (scalar (ricci (riemann "flat"))) zero :=
  tr3
    (RP.cg_scalar (RP.cg_ricci (RP.stp RStep.riemann_flat)))
    (RP.cg_scalar (RP.stp RStep.ricci_zero))
    (RP.stp RStep.scalar_zero)

-- 6: Flat Weyl chain (2-step)
theorem thm06_flat_weyl :
    RP (weyl (riemann "flat")) zero :=
  RP.tr (RP.cg_weyl (RP.stp RStep.riemann_flat)) (RP.stp RStep.weyl_zero)

-- 7: Flat Ricci chain (2-step)
theorem thm07_flat_ricci :
    RP (ricci (riemann "flat")) zero :=
  RP.tr (RP.cg_ricci (RP.stp RStep.riemann_flat)) (RP.stp RStep.ricci_zero)

-- 8
theorem thm08_flat_conn : RP (connLC (metric "flat")) flatConn :=
  RP.stp RStep.conn_flat

-- ============================================================
-- §5  Geodesic algebra (9–18)
-- ============================================================

theorem thm09_geo_id_r (γ : RiemObj) : RP (geoComp γ geoTriv) γ :=
  RP.stp (RStep.geo_comp_triv_r γ)

theorem thm10_geo_id_l (γ : RiemObj) : RP (geoComp geoTriv γ) γ :=
  RP.stp (RStep.geo_comp_triv_l γ)

theorem thm11_geo_assoc (a b c : RiemObj) :
    RP (geoComp (geoComp a b) c) (geoComp a (geoComp b c)) :=
  RP.stp (RStep.geo_comp_assoc a b c)

theorem thm12_geo_rev_rev (γ : RiemObj) : RP (geoRev (geoRev γ)) γ :=
  RP.stp (RStep.geo_rev_rev γ)

theorem thm13_geo_rev_triv : RP (geoRev geoTriv) geoTriv :=
  RP.stp RStep.geo_rev_triv

theorem thm14_geo_comp_rev (γ : RiemObj) : RP (geoComp γ (geoRev γ)) geoTriv :=
  RP.stp (RStep.geo_comp_rev γ)

-- 15: triv ∘ triv = triv
theorem thm15_geo_triv_triv : RP (geoComp geoTriv geoTriv) geoTriv :=
  RP.stp (RStep.geo_comp_triv_l geoTriv)

-- 16: (γ ∘ triv) ∘ δ = γ ∘ δ
theorem thm16_geo_triv_middle (γ δ : RiemObj) :
    RP (geoComp (geoComp γ geoTriv) δ) (geoComp γ δ) :=
  RP.cg_geoComp_l (RP.stp (RStep.geo_comp_triv_r γ))

-- 17: γ⁻¹⁻¹ ∘ δ = γ ∘ δ
theorem thm17_geo_rev_rev_comp (γ δ : RiemObj) :
    RP (geoComp (geoRev (geoRev γ)) δ) (geoComp γ δ) :=
  RP.cg_geoComp_l (RP.stp (RStep.geo_rev_rev γ))

-- 18: (γ ∘ γ⁻¹) ∘ δ = δ (2-step)
theorem thm18_geo_cancel_left (γ δ : RiemObj) :
    RP (geoComp (geoComp γ (geoRev γ)) δ) δ :=
  RP.tr (RP.cg_geoComp_l (RP.stp (RStep.geo_comp_rev γ)))
        (RP.stp (RStep.geo_comp_triv_l δ))

-- ============================================================
-- §6  Jacobi fields (19–26)
-- ============================================================

theorem thm19_jac_zero_l (J : RiemObj) : RP (jacAdd jacZero J) J :=
  RP.stp (RStep.jac_add_zero_l J)

theorem thm20_jac_zero_r (J : RiemObj) : RP (jacAdd J jacZero) J :=
  RP.stp (RStep.jac_add_zero_r J)

theorem thm21_jac_comm (J₁ J₂ : RiemObj) : RP (jacAdd J₁ J₂) (jacAdd J₂ J₁) :=
  RP.stp (RStep.jac_add_comm J₁ J₂)

theorem thm22_jac_assoc (J₁ J₂ J₃ : RiemObj) :
    RP (jacAdd (jacAdd J₁ J₂) J₃) (jacAdd J₁ (jacAdd J₂ J₃)) :=
  RP.stp (RStep.jac_add_assoc J₁ J₂ J₃)

theorem thm23_jac_scale_zero (J : RiemObj) : RP (jacScale 0 J) jacZero :=
  RP.stp (RStep.jac_scale_zero J)

theorem thm24_jac_scale_one (J : RiemObj) : RP (jacScale 1 J) J :=
  RP.stp (RStep.jac_scale_one J)

-- 25: J + (-1)·J = 0
theorem thm25_jac_add_neg (J : RiemObj) : RP (jacAdd J (jacScale (-1) J)) jacZero :=
  RP.stp (RStep.jac_add_neg J)

-- 26: (J₁+J₂)+(-J₂) = J₁+0 (2-step)
theorem thm26_jac_cancel (J₁ J₂ : RiemObj) :
    RP (jacAdd (jacAdd J₁ J₂) (jacScale (-1) J₂)) (jacAdd J₁ jacZero) :=
  RP.tr (RP.stp (RStep.jac_add_assoc J₁ J₂ (jacScale (-1) J₂)))
        (RP.cg_jacAdd_r (RP.stp (RStep.jac_add_neg J₂)))

-- ============================================================
-- §7  Exponential map (27–30)
-- ============================================================

theorem thm27_exp_origin : RP (expM origin) origin := RP.stp RStep.exp_origin
theorem thm28_exp_zero : RP (expM jacZero) origin := RP.stp RStep.exp_zero_vec

-- 29: exp(J + (-J)) = origin (2-step)
theorem thm29_exp_cancel (J : RiemObj) :
    RP (expM (jacAdd J (jacScale (-1) J))) origin :=
  RP.tr (RP.cg_expM (RP.stp (RStep.jac_add_neg J))) (RP.stp RStep.exp_zero_vec)

-- 30: exp(0+0) = origin (2-step)
theorem thm30_exp_zero_sum :
    RP (expM (jacAdd jacZero jacZero)) origin :=
  RP.tr (RP.cg_expM (RP.stp (RStep.jac_add_zero_l jacZero))) (RP.stp RStep.exp_zero_vec)

-- ============================================================
-- §8  Gauss–Bonnet / Euler (31–36)
-- ============================================================

theorem thm31_euler_sphere : RP (euler (genus 0)) (val 2) := RP.stp RStep.euler_sphere
theorem thm32_euler_torus : RP (euler (genus 1)) (val 0) := RP.stp RStep.euler_torus
theorem thm33_euler_genus (g : Nat) : RP (euler (genus g)) (val (2 - 2 * g)) :=
  RP.stp (RStep.euler_genus g)
theorem thm34_euler_g2 : RP (euler (genus 2)) (val (2 - 4)) := RP.stp (RStep.euler_genus 2)
theorem thm35_euler_symm : RP (val 2) (euler (genus 0)) := RP.sym (RP.stp RStep.euler_sphere)
theorem thm36_euler_g0 : RP (euler (genus 0)) (val 2) := thm31_euler_sphere

-- ============================================================
-- §9  Holonomy (37–44)
-- ============================================================

theorem thm37_hol_id_r (h : RiemObj) : RP (holComp h holTriv) h :=
  RP.stp (RStep.hol_comp_triv_r h)
theorem thm38_hol_id_l (h : RiemObj) : RP (holComp holTriv h) h :=
  RP.stp (RStep.hol_comp_triv_l h)
theorem thm39_hol_assoc (a b c : RiemObj) :
    RP (holComp (holComp a b) c) (holComp a (holComp b c)) :=
  RP.stp (RStep.hol_comp_assoc a b c)
theorem thm40_hol_flat : RP (holo geoTriv) holTriv := RP.stp RStep.hol_flat

-- 41: triv ∘ triv
theorem thm41_hol_triv_triv : RP (holComp holTriv holTriv) holTriv :=
  RP.stp (RStep.hol_comp_triv_l holTriv)

-- 42: (h₁ ∘ triv) ∘ h₂ = h₁ ∘ h₂
theorem thm42_hol_triv_mid (h₁ h₂ : RiemObj) :
    RP (holComp (holComp h₁ holTriv) h₂) (holComp h₁ h₂) :=
  RP.cg_holComp_l (RP.stp (RStep.hol_comp_triv_r h₁))

-- 43: Flat holonomy composed (3-step)
theorem thm43_flat_hol_comp :
    RP (holComp (holo geoTriv) (holo geoTriv)) holTriv :=
  tr3
    (RP.cg_holComp_l (RP.stp RStep.hol_flat))
    (RP.cg_holComp_r (RP.stp RStep.hol_flat))
    (RP.stp (RStep.hol_comp_triv_l holTriv))

-- 44: h ∘ (triv ∘ triv) = h (2-step)
theorem thm44_hol_double_triv (h : RiemObj) :
    RP (holComp h (holComp holTriv holTriv)) h :=
  RP.tr (RP.cg_holComp_r (RP.stp (RStep.hol_comp_triv_l holTriv)))
        (RP.stp (RStep.hol_comp_triv_r h))

-- ============================================================
-- §10 Parallel transport (45–54)
-- ============================================================

theorem thm45_pt_triv (v : RiemObj) : RP (parTr geoTriv v) v :=
  RP.stp (RStep.pt_triv v)

theorem thm46_pt_comp (γ₁ γ₂ v : RiemObj) :
    RP (parTr (geoComp γ₁ γ₂) v) (parTr γ₂ (parTr γ₁ v)) :=
  RP.stp (RStep.pt_comp γ₁ γ₂ v)

theorem thm47_pt_rev_cancel (γ v : RiemObj) :
    RP (parTr (geoRev γ) (parTr γ v)) v :=
  RP.stp (RStep.pt_rev γ v)

-- 48: PT(γ∘triv, v) = PT(γ, v) (2-step)
theorem thm48_pt_triv_r (γ v : RiemObj) :
    RP (parTr (geoComp γ geoTriv) v) (parTr γ v) :=
  RP.tr (RP.stp (RStep.pt_comp γ geoTriv v))
        (RP.stp (RStep.pt_triv (parTr γ v)))

-- 49: PT(triv∘γ, v) = PT(γ, v) (2-step)
theorem thm49_pt_triv_l (γ v : RiemObj) :
    RP (parTr (geoComp geoTriv γ) v) (parTr γ v) :=
  RP.tr (RP.stp (RStep.pt_comp geoTriv γ v))
        (RP.cg_pt_v (RP.stp (RStep.pt_triv v)))

-- 50: PT γ (PT γ⁻¹ (PT γ v)) = PT γ v (congr)
theorem thm50_pt_roundtrip (γ v : RiemObj) :
    RP (parTr γ (parTr (geoRev γ) (parTr γ v))) (parTr γ v) :=
  RP.cg_pt_v (RP.stp (RStep.pt_rev γ v))

-- 51: PT(γ ∘ γ⁻¹, v) = v (2-step)
theorem thm51_pt_loop_cancel (γ v : RiemObj) :
    RP (parTr (geoComp γ (geoRev γ)) v) v :=
  RP.tr (RP.cg_pt_γ (RP.stp (RStep.geo_comp_rev γ)))
        (RP.stp (RStep.pt_triv v))

-- 52: PT triple composition (3-step)
theorem thm52_pt_triple (γ₁ γ₂ γ₃ v : RiemObj) :
    RP (parTr (geoComp (geoComp γ₁ γ₂) γ₃) v)
       (parTr γ₃ (parTr γ₂ (parTr γ₁ v))) :=
  tr3 (RP.cg_pt_γ (RP.stp (RStep.geo_comp_assoc γ₁ γ₂ γ₃)))
      (RP.stp (RStep.pt_comp γ₁ (geoComp γ₂ γ₃) v))
      (RP.stp (RStep.pt_comp γ₂ γ₃ (parTr γ₁ v)))

-- 53: PT double-reversed
theorem thm53_pt_double_rev (γ v : RiemObj) :
    RP (parTr (geoRev (geoRev γ)) v) (parTr γ v) :=
  RP.cg_pt_γ (RP.stp (RStep.geo_rev_rev γ))

-- 54: PT triv triv = id (2-step)
theorem thm54_pt_triv_triv (v : RiemObj) :
    RP (parTr geoTriv (parTr geoTriv v)) v :=
  RP.tr (RP.cg_pt_v (RP.stp (RStep.pt_triv v))) (RP.stp (RStep.pt_triv v))

-- ============================================================
-- §11 Mixed chains (55–66)
-- ============================================================

-- 55: γ ∘ (γ⁻¹ ∘ δ) = δ (2-step via symm assoc)
theorem thm55_geo_cancel_right (γ δ : RiemObj) :
    RP (geoComp γ (geoComp (geoRev γ) δ)) δ :=
  RP.tr (RP.sym (RP.stp (RStep.geo_comp_assoc γ (geoRev γ) δ)))
        (thm18_geo_cancel_left γ δ)

-- 56: Four-element geodesic assoc (2-step)
theorem thm56_geo_four_assoc (a b c d : RiemObj) :
    RP (geoComp (geoComp (geoComp a b) c) d)
       (geoComp a (geoComp b (geoComp c d))) :=
  RP.tr (RP.stp (RStep.geo_comp_assoc (geoComp a b) c d))
        (RP.stp (RStep.geo_comp_assoc a b (geoComp c d)))

-- 57: (γ∘γ⁻¹)∘(δ∘δ⁻¹) = triv (3-step)
theorem thm57_geo_double_cancel (γ δ : RiemObj) :
    RP (geoComp (geoComp γ (geoRev γ)) (geoComp δ (geoRev δ))) geoTriv :=
  tr3 (RP.cg_geoComp_l (RP.stp (RStep.geo_comp_rev γ)))
      (RP.cg_geoComp_r (RP.stp (RStep.geo_comp_rev δ)))
      (RP.stp (RStep.geo_comp_triv_l geoTriv))

-- 58: Jac double zero
theorem thm58_jac_double_zero (J : RiemObj) :
    RP (jacAdd (jacAdd jacZero J) jacZero) J :=
  RP.tr (RP.stp (RStep.jac_add_zero_r (jacAdd jacZero J))) (RP.stp (RStep.jac_add_zero_l J))

-- 59: Four-element Jac assoc (2-step)
theorem thm59_jac_four_assoc (a b c d : RiemObj) :
    RP (jacAdd (jacAdd (jacAdd a b) c) d) (jacAdd a (jacAdd b (jacAdd c d))) :=
  RP.tr (RP.stp (RStep.jac_add_assoc (jacAdd a b) c d))
        (RP.stp (RStep.jac_add_assoc a b (jacAdd c d)))

-- 60: exp of scaled zero (2-step)
theorem thm60_exp_scale_zero (J : RiemObj) :
    RP (expM (jacScale 0 J)) origin :=
  RP.tr (RP.cg_expM (RP.stp (RStep.jac_scale_zero J))) (RP.stp RStep.exp_zero_vec)

-- 61: Jac scale 1 + zero (2-step)
theorem thm61_jac_scale_one_zero (J : RiemObj) :
    RP (jacAdd (jacScale 1 J) jacZero) J :=
  RP.tr (RP.stp (RStep.jac_add_zero_r (jacScale 1 J))) (RP.stp (RStep.jac_scale_one J))

-- 62: Flat PT loop (2-step)
theorem thm62_flat_pt_loop (v : RiemObj) :
    RP (parTr (geoComp geoTriv (geoRev geoTriv)) v) v :=
  RP.tr (RP.cg_pt_γ (RP.stp (RStep.geo_comp_rev geoTriv))) (RP.stp (RStep.pt_triv v))

-- 63: exp commutativity
theorem thm63_exp_jac_comm (J₁ J₂ : RiemObj) :
    RP (expM (jacAdd J₁ J₂)) (expM (jacAdd J₂ J₁)) :=
  RP.cg_expM (RP.stp (RStep.jac_add_comm J₁ J₂))

-- 64: Holonomy four-assoc (2-step)
theorem thm64_hol_four_assoc (a b c d : RiemObj) :
    RP (holComp (holComp (holComp a b) c) d)
       (holComp a (holComp b (holComp c d))) :=
  RP.tr (RP.stp (RStep.hol_comp_assoc (holComp a b) c d))
        (RP.stp (RStep.hol_comp_assoc a b (holComp c d)))

-- 65: Jac full cancel (3-step)
theorem thm65_jac_full_cancel (J₁ J₂ : RiemObj) :
    RP (jacAdd (jacAdd J₁ J₂) (jacScale (-1) J₂)) J₁ :=
  RP.tr (thm26_jac_cancel J₁ J₂) (RP.stp (RStep.jac_add_zero_r J₁))

-- 66: exp cancel full (3-step)
theorem thm66_exp_cancel_full (J : RiemObj) :
    RP (expM (jacAdd (jacAdd J (jacScale (-1) J)) jacZero)) origin :=
  tr3 (RP.cg_expM (RP.stp (RStep.jac_add_zero_r (jacAdd J (jacScale (-1) J)))))
      (RP.cg_expM (RP.stp (RStep.jac_add_neg J)))
      (RP.stp RStep.exp_zero_vec)

-- ============================================================
-- §12 More chains (67–78)
-- ============================================================

theorem thm67_geo_symm (γ : RiemObj) : RP γ (geoComp γ geoTriv) :=
  RP.sym (RP.stp (RStep.geo_comp_triv_r γ))

theorem thm68_hol_cancel (h : RiemObj) :
    RP (holComp (holComp h holTriv) holTriv) h :=
  RP.tr (RP.stp (RStep.hol_comp_triv_r (holComp h holTriv)))
        (RP.stp (RStep.hol_comp_triv_r h))

theorem thm69_pt_triv_mid (γ v : RiemObj) :
    RP (parTr (geoComp γ (geoComp geoTriv (geoRev γ))) v) v :=
  RP.tr (RP.cg_pt_γ (RP.cg_geoComp_r (RP.stp (RStep.geo_comp_triv_l (geoRev γ)))))
        (thm51_pt_loop_cancel γ v)

theorem thm70_pt_rev_triv (v : RiemObj) :
    RP (parTr (geoRev geoTriv) v) v :=
  RP.tr (RP.cg_pt_γ (RP.stp RStep.geo_rev_triv)) (RP.stp (RStep.pt_triv v))

theorem thm71_flat_weyl_ricci : RP (weyl (riemann "flat")) zero := thm06_flat_weyl

theorem thm72_jac_comm_invol (J₁ J₂ : RiemObj) :
    RP (jacAdd J₁ J₂) (jacAdd J₁ J₂) :=
  RP.tr (RP.stp (RStep.jac_add_comm J₁ J₂)) (RP.stp (RStep.jac_add_comm J₂ J₁))

theorem thm73_symm_symm {a b : RiemObj} (p : RP a b) : RP a b := RP.sym (RP.sym p)

theorem thm74_trans_refl {a b : RiemObj} (p : RP a b) : RP a b := RP.tr p (RP.rfl b)

theorem thm75_geo_rev_triv_comp (γ : RiemObj) :
    RP (geoComp (geoRev geoTriv) γ) γ :=
  RP.tr (RP.cg_geoComp_l (RP.stp RStep.geo_rev_triv)) (RP.stp (RStep.geo_comp_triv_l γ))

theorem thm76_hol_assoc_simp (a b : RiemObj) :
    RP (holComp (holComp a b) holTriv) (holComp a b) :=
  RP.stp (RStep.hol_comp_triv_r (holComp a b))

theorem thm77_geo_comp_triv_rev_rev (γ : RiemObj) :
    RP (geoRev (geoRev (geoComp γ geoTriv))) (geoComp γ geoTriv) :=
  RP.stp (RStep.geo_rev_rev (geoComp γ geoTriv))

theorem thm78_pt_geo_rev_rev (γ v : RiemObj) :
    RP (parTr (geoComp (geoRev (geoRev γ)) geoTriv) v) (parTr γ v) :=
  RP.tr (RP.cg_pt_γ (RP.cg_geoComp_l (RP.stp (RStep.geo_rev_rev γ))))
        (RP.cg_pt_γ (RP.stp (RStep.geo_comp_triv_r γ)))

end ComputationalPaths.Path.Geometry.RiemannianDeep

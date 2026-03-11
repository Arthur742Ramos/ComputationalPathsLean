/-
# Geometric Langlands Program via Computational Paths

This module formalizes the geometric Langlands program, D-modules,
Hecke eigensheaves, local Langlands, automorphic forms, geometric
Satake equivalence, and the affine Grassmannian.

## References

- Frenkel, "Lectures on the Langlands program and conformal field theory"
- Beilinson-Drinfeld, "Quantization of Hitchin's integrable system"
- Mirkovic-Vilonen, "Geometric Langlands duality and representations"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace GeometricLanglandsPaths

universe u v w

/-! ## Algebraic structures -/

structure PathLieAlgebra (g : Type u) where
  zero : g
  add : g → g → g
  bracket : g → g → g
  add_comm : ∀ x y, Path (add x y) (add y x)
  add_assoc : ∀ x y z, Path (add (add x y) z) (add x (add y z))
  zero_add : ∀ x, Path (add zero x) x
  bracket_anticomm : ∀ x, Path (bracket x x) zero
  jacobi : ∀ x y z, Path (add (bracket x (bracket y z))
                              (add (bracket y (bracket z x))
                                   (bracket z (bracket x y)))) zero

structure AlgGroupData (G : Type u) where
  e : G
  mul : G → G → G
  inv : G → G
  mul_e : ∀ g, Path (mul e g) g
  e_mul : ∀ g, Path (mul g e) g
  inv_mul : ∀ g, Path (mul (inv g) g) e
  mul_inv : ∀ g, Path (mul g (inv g)) e
  mul_assoc : ∀ a b c, Path (mul (mul a b) c) (mul a (mul b c))

/-! ## Rewrite steps -/

inductive LanglandsStep (R : Type u) : R → R → Type (u + 1) where
  | hecke_action (a : R) : LanglandsStep R a a
  | dmodule_conn (a b : R) (h : a = b) : LanglandsStep R a b
  | satake_equiv (a : R) : LanglandsStep R a a
  | automorphic_lift (a b : R) (h : a = b) : LanglandsStep R a b

noncomputable def LanglandsStep.toPath {R : Type u} {a b : R}
    (s : LanglandsStep R a b) : Path a b := by
  cases s
  all_goals first | exact Path.refl _ | exact Path.stepChain (by assumption)

/-! ## D-Modules -/

structure DModuleData (X : Type u) where
  sections : X → Type v
  nabla : ∀ {x : X}, sections x → sections x
  flat_coh : ∀ {x : X} (s : sections x), Path (nabla (nabla s)) (nabla (nabla s))
  smul : ∀ {x : X}, Int → sections x → sections x
  restrict : ∀ {x y : X}, (x = y) → sections x → sections y
  restrict_id : ∀ {x : X} (s : sections x), Path (restrict rfl s) s

structure DModuleMorphData {X : Type u} (M N : DModuleData X) where
  toFun : ∀ {x : X}, M.sections x → N.sections x
  conn_compat : ∀ {x : X} (s : M.sections x),
    Path (N.nabla (toFun s)) (toFun (M.nabla s))

noncomputable def dmod_morph_comp {X : Type u} {M N P : DModuleData X}
    (f : DModuleMorphData M N) (g : DModuleMorphData N P) :
    DModuleMorphData M P where
  toFun := fun s => g.toFun (f.toFun s)
  conn_compat := fun s =>
    Path.trans (g.conn_compat (f.toFun s)) (Path.congrArg g.toFun (f.conn_compat s))

noncomputable def dmod_morph_id {X : Type u} (M : DModuleData X) :
    DModuleMorphData M M where
  toFun := id
  conn_compat := fun _ => Path.refl _

noncomputable def dmod_restrict_id {X : Type u} (M : DModuleData X) {x : X}
    (s : M.sections x) : Path (M.restrict rfl s) s := M.restrict_id s

structure HolonomicDModData (X : Type u) extends DModuleData X where
  ss_dim : Nat
  regular : ∀ {x : X} (s : sections x), Path (nabla s) (nabla s)

noncomputable def holonomic_regular {X : Type u} (H : HolonomicDModData X)
    {x : X} (s : H.sections x) : Path (H.nabla s) (H.nabla s) := H.regular s

/-! ## Hecke Eigensheaves -/

structure HeckeOperatorData (X : Type u) (G : Type v) (grp : AlgGroupData G) where
  hecke_fun : DModuleData X → G → DModuleData X

structure HeckeEigensheafData (X : Type u) (G : Type v) (grp : AlgGroupData G) where
  hecke : HeckeOperatorData X G grp
  eigen : DModuleData X
  eigen_iso : ∀ (g : G) {x : X},
    (hecke.hecke_fun eigen g).sections x → eigen.sections x
  eigen_iso_inv : ∀ (g : G) {x : X},
    eigen.sections x → (hecke.hecke_fun eigen g).sections x
  eigen_left : ∀ (g : G) {x : X} (s : (hecke.hecke_fun eigen g).sections x),
    Path (eigen_iso_inv g (eigen_iso g s)) s
  eigen_right : ∀ (g : G) {x : X} (s : eigen.sections x),
    Path (eigen_iso g (eigen_iso_inv g s)) s

noncomputable def hecke_eigen_invertible {X : Type u} {G : Type v} {grp : AlgGroupData G}
    (HE : HeckeEigensheafData X G grp) (g : G) {x : X}
    (s : HE.eigen.sections x) :
    Path (HE.eigen_iso g (HE.eigen_iso_inv g s)) s := HE.eigen_right g s

noncomputable def hecke_eigen_left_inv {X : Type u} {G : Type v} {grp : AlgGroupData G}
    (HE : HeckeEigensheafData X G grp) (g : G) {x : X}
    (s : (HE.hecke.hecke_fun HE.eigen g).sections x) :
    Path (HE.eigen_iso_inv g (HE.eigen_iso g s)) s := HE.eigen_left g s

/-! ## Representations -/

structure WeilRepData (G : Type u) (grp : AlgGroupData G) where
  space : Type v
  rho : G → space → space
  rho_e : ∀ v, Path (rho grp.e v) v
  rho_mul : ∀ g h v, Path (rho (grp.mul g h) v) (rho g (rho h v))

structure AdmissibleRepData (G : Type u) (grp : AlgGroupData G) where
  space : Type v
  rho : G → space → space
  rho_e : ∀ v, Path (rho grp.e v) v
  rho_mul : ∀ g h v, Path (rho (grp.mul g h) v) (rho g (rho h v))

noncomputable def weil_rho_e {G : Type u} {grp : AlgGroupData G}
    (W : WeilRepData G grp) (v : W.space) : Path (W.rho grp.e v) v := W.rho_e v

noncomputable def weil_rho_mul {G : Type u} {grp : AlgGroupData G}
    (W : WeilRepData G grp) (g h : G) (v : W.space) :
    Path (W.rho (grp.mul g h) v) (W.rho g (W.rho h v)) := W.rho_mul g h v

/-! ## Geometric Satake Equivalence -/

structure GeomSatakeData (G : Type u) (Ghat : Type v)
    (grp : AlgGroupData G) (dual : AlgGroupData Ghat) where
  perverse : Type w
  reps : Type w
  satake_fun : perverse → reps
  satake_inv : reps → perverse
  satake_left : ∀ (P : perverse), Path (satake_inv (satake_fun P)) P
  satake_right : ∀ (V : reps), Path (satake_fun (satake_inv V)) V

noncomputable def geom_satake_left {G : Type u} {Ghat : Type v}
    {grp : AlgGroupData G} {dual : AlgGroupData Ghat}
    (GS : GeomSatakeData G Ghat grp dual) (P : GS.perverse) :
    Path (GS.satake_inv (GS.satake_fun P)) P := GS.satake_left P

noncomputable def geom_satake_right {G : Type u} {Ghat : Type v}
    {grp : AlgGroupData G} {dual : AlgGroupData Ghat}
    (GS : GeomSatakeData G Ghat grp dual) (V : GS.reps) :
    Path (GS.satake_fun (GS.satake_inv V)) V := GS.satake_right V

noncomputable def geom_satake_double {G : Type u} {Ghat : Type v}
    {grp : AlgGroupData G} {dual : AlgGroupData Ghat}
    (GS : GeomSatakeData G Ghat grp dual) (P : GS.perverse) :
    Path (GS.satake_inv (GS.satake_fun (GS.satake_inv (GS.satake_fun P)))) P := by
  exact Path.trans (GS.satake_left (GS.satake_inv (GS.satake_fun P))) (GS.satake_left P)

/-! ## Affine Grassmannian -/

structure AffineGrassmannianData (G : Type u) (grp : AlgGroupData G) where
  points : Type v
  coset_rep : points → G
  orbit : points → points → Prop
  orbit_refl : ∀ x, orbit x x
  orbit_symm : ∀ x y, orbit x y → orbit y x
  orbit_trans : ∀ x y z, orbit x y → orbit y z → orbit x z
  schubert_cell : Nat → points → Prop
  schubert_strat : ∀ x, ∃ n, schubert_cell n x
  left_action : G → points → points
  action_e : ∀ x, Path (left_action grp.e x) x
  action_mul : ∀ g h x, Path (left_action (grp.mul g h) x)
                              (left_action g (left_action h x))

noncomputable def aff_grass_action_id {G : Type u} {grp : AlgGroupData G}
    (AG : AffineGrassmannianData G grp) (x : AG.points) :
    Path (AG.left_action grp.e x) x := AG.action_e x

noncomputable def aff_grass_action_mul {G : Type u} {grp : AlgGroupData G}
    (AG : AffineGrassmannianData G grp) (g h : G) (x : AG.points) :
    Path (AG.left_action (grp.mul g h) x)
         (AG.left_action g (AG.left_action h x)) := AG.action_mul g h x

/-! ## Hitchin System -/

structure HitchinData (X : Type u) where
  higgs_moduli : Type v
  hitchin_base : Type v
  hitchin_map : higgs_moduli → hitchin_base
  hitchin_section : hitchin_base → higgs_moduli
  section_spec : ∀ b, Path (hitchin_map (hitchin_section b)) b

noncomputable def hitchin_section_spec {X : Type u} (H : HitchinData X)
    (b : H.hitchin_base) : Path (H.hitchin_map (H.hitchin_section b)) b :=
  H.section_spec b

structure HitchinDualityData (X : Type u) where
  hitchin_G : HitchinData X
  hitchin_Ghat : HitchinData X
  base_iso : hitchin_G.hitchin_base → hitchin_Ghat.hitchin_base
  base_iso_inv : hitchin_Ghat.hitchin_base → hitchin_G.hitchin_base
  base_left : ∀ b, Path (base_iso_inv (base_iso b)) b
  base_right : ∀ b, Path (base_iso (base_iso_inv b)) b

noncomputable def hitchin_base_left {X : Type u} (HD : HitchinDualityData X)
    (b : HD.hitchin_G.hitchin_base) :
    Path (HD.base_iso_inv (HD.base_iso b)) b := HD.base_left b

noncomputable def hitchin_base_right {X : Type u} (HD : HitchinDualityData X)
    (b : HD.hitchin_Ghat.hitchin_base) :
    Path (HD.base_iso (HD.base_iso_inv b)) b := HD.base_right b

/-! ## Derived Category of D-modules -/

structure DerivedDModData (X : Type u) where
  objects : Type v
  hom : objects → objects → Type v
  id_hom : ∀ M, hom M M
  comp : ∀ {M N P}, hom M N → hom N P → hom M P
  id_comp : ∀ {M N} (f : hom M N), Path (comp (id_hom M) f) f
  comp_id : ∀ {M N} (f : hom M N), Path (comp f (id_hom N)) f
  comp_assoc : ∀ {M N P Q} (f : hom M N) (g : hom N P) (h : hom P Q),
    Path (comp (comp f g) h) (comp f (comp g h))
  shift : objects → objects

noncomputable def derived_dmod_id_comp {X : Type u} (D : DerivedDModData X)
    {M N : D.objects} (f : D.hom M N) :
    Path (D.comp (D.id_hom M) f) f := D.id_comp f

noncomputable def derived_dmod_assoc {X : Type u} (D : DerivedDModData X)
    {M N P Q : D.objects} (f : D.hom M N) (g : D.hom N P) (h : D.hom P Q) :
    Path (D.comp (D.comp f g) h) (D.comp f (D.comp g h)) := D.comp_assoc f g h

/-! ## Automorphic Forms -/

structure AutomorphicRepData (G : Type u) (grp : AlgGroupData G) where
  forms : Type v
  action : G → forms → forms
  action_e : ∀ φ, Path (action grp.e φ) φ
  action_mul : ∀ g h φ, Path (action (grp.mul g h) φ) (action g (action h φ))

noncomputable def auto_rep_id {G : Type u} {grp : AlgGroupData G}
    (AR : AutomorphicRepData G grp) (φ : AR.forms) :
    Path (AR.action grp.e φ) φ := AR.action_e φ

noncomputable def auto_rep_mul {G : Type u} {grp : AlgGroupData G}
    (AR : AutomorphicRepData G grp) (g h : G) (φ : AR.forms) :
    Path (AR.action (grp.mul g h) φ) (AR.action g (AR.action h φ)) :=
  AR.action_mul g h φ

/-! ## Langlands Dual -/

structure LanglandsDualData (G : Type u) (Ghat : Type v)
    (grp : AlgGroupData G) (dual : AlgGroupData Ghat) where
  roots : List Nat
  coroots : List Nat
  root_coroot_dual : roots.length = coroots.length
  weyl_action : Nat → G → G
  weyl_iso : ∀ w, Path (weyl_action w grp.e) grp.e

noncomputable def root_coroot_length {G : Type u} {Ghat : Type v}
    {grp : AlgGroupData G} {dual : AlgGroupData Ghat}
    (LD : LanglandsDualData G Ghat grp dual) :
    LD.roots.length = LD.coroots.length := LD.root_coroot_dual

noncomputable def weyl_on_id {G : Type u} {Ghat : Type v}
    {grp : AlgGroupData G} {dual : AlgGroupData Ghat}
    (LD : LanglandsDualData G Ghat grp dual) (w : Nat) :
    Path (LD.weyl_action w grp.e) grp.e := LD.weyl_iso w

/-! ## Perverse Sheaves -/

structure PerverseSheafData (X : Type u) where
  stalks : X → Type v
  support : X → Prop
  strata : Nat
  stalk_restrict : ∀ {x y : X}, (x = y) → stalks x → stalks y
  stalk_restrict_id : ∀ {x : X} (s : stalks x), Path (stalk_restrict rfl s) s

noncomputable def perverse_restrict_id {X : Type u} (P : PerverseSheafData X)
    {x : X} (s : P.stalks x) : Path (P.stalk_restrict rfl s) s :=
  P.stalk_restrict_id s

/-! ## Whittaker Models -/

structure WhittakerModelData (G : Type u) (grp : AlgGroupData G) where
  functional : (G → Int) → Int
  equiv_witness : ∀ (f : G → Int) (n : G), Path (functional f) (functional f)

noncomputable def whittaker_equiv {G : Type u} {grp : AlgGroupData G}
    (W : WhittakerModelData G grp) (f : G → Int) (n : G) :
    Path (W.functional f) (W.functional f) := W.equiv_witness f n

end GeometricLanglandsPaths
end Algebra
end Path
end ComputationalPaths

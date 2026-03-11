/-
# Stacky Algebraic Geometry via Computational Paths

This module develops algebraic stacks, Deligne-Mumford vs Artin stacks,
quotient stacks, moduli of curves, inertia stacks, and coarse moduli spaces
through computational paths.

## References

- Deligne-Mumford, "The irreducibility of the space of curves of given genus"
- Laumon-Moret-Bailly, "Champs algébriques"
- Vistoli, "Grothendieck topologies, fibered categories, and descent theory"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u v w

/-! ## Groupoid Data -/

/-- A groupoid: category where every morphism is invertible. -/
structure Groupoid (O : Type u) (M : Type v) where
  src : M → O
  tgt : M → O
  comp : M → M → M
  ident : O → M
  inv : M → M
  src_id : ∀ (x : O), Path (src (ident x)) x
  tgt_id : ∀ (x : O), Path (tgt (ident x)) x
  comp_assoc : ∀ (f g h : M), Path (comp (comp f g) h) (comp f (comp g h))
  id_comp : ∀ (f : M), Path (comp (ident (src f)) f) f
  comp_id : ∀ (f : M), Path (comp f (ident (tgt f))) f
  inv_left : ∀ (f : M), Path (comp (inv f) f) (ident (tgt f))
  inv_right : ∀ (f : M), Path (comp f (inv f)) (ident (src f))

namespace Groupoid

variable {O : Type u} {M : Type v} (G : Groupoid O M)

theorem src_id_eq (x : O) : G.src (G.ident x) = x := (G.src_id x).toEq
theorem tgt_id_eq (x : O) : G.tgt (G.ident x) = x := (G.tgt_id x).toEq
theorem comp_assoc_eq (f g h : M) : G.comp (G.comp f g) h = G.comp f (G.comp g h) :=
  (G.comp_assoc f g h).toEq
theorem id_comp_eq (f : M) : G.comp (G.ident (G.src f)) f = f := (G.id_comp f).toEq
theorem comp_id_eq (f : M) : G.comp f (G.ident (G.tgt f)) = f := (G.comp_id f).toEq
theorem inv_left_eq (f : M) : G.comp (G.inv f) f = G.ident (G.tgt f) := (G.inv_left f).toEq
theorem inv_right_eq (f : M) : G.comp f (G.inv f) = G.ident (G.src f) := (G.inv_right f).toEq

/-- Inverse of inverse is identity. -/
noncomputable def inv_inv (f : M) :
    Path (G.comp (G.inv (G.inv f)) (G.inv f)) (G.ident (G.tgt (G.inv f))) :=
  G.inv_left (G.inv f)

theorem inv_inv_eq (f : M) :
    G.comp (G.inv (G.inv f)) (G.inv f) = G.ident (G.tgt (G.inv f)) :=
  (G.inv_inv f).toEq

/-- Triple composition associativity. -/
noncomputable def triple_comp (f g h k : M) :
    Path (G.comp (G.comp (G.comp f g) h) k) (G.comp f (G.comp g (G.comp h k))) :=
  Path.trans (G.comp_assoc (G.comp f g) h k) (G.comp_assoc f g (G.comp h k))

theorem triple_comp_eq (f g h k : M) :
    G.comp (G.comp (G.comp f g) h) k = G.comp f (G.comp g (G.comp h k)) :=
  (G.triple_comp f g h k).toEq

end Groupoid

/-! ## Algebraic Stacks -/

/-- An algebraic stack: a stack with a smooth atlas. -/
structure AlgebraicStack (X : Type u) (U : Type v) where
  atlas : U → X
  groupoid : Groupoid X (X × X)
  atlas_surj : ∀ (x : X), U  -- exists a chart
  atlas_covers : ∀ (x : X), Path (atlas (atlas_surj x)) x
  smooth : U → U → Prop  -- smoothness of overlap

namespace AlgebraicStack

variable {X : Type u} {U : Type v} (S : AlgebraicStack X U)

theorem atlas_covers_eq (x : X) : S.atlas (S.atlas_surj x) = x :=
  (S.atlas_covers x).toEq

/-- Double atlas cover. -/
noncomputable def double_atlas (x : X) :
    Path (S.atlas (S.atlas_surj (S.atlas (S.atlas_surj x)))) x :=
  Path.trans (S.atlas_covers (S.atlas (S.atlas_surj x))) (S.atlas_covers x)

theorem double_atlas_eq (x : X) :
    S.atlas (S.atlas_surj (S.atlas (S.atlas_surj x))) = x :=
  (S.double_atlas x).toEq

end AlgebraicStack

/-! ## Deligne-Mumford Stacks -/

/-- A Deligne-Mumford stack: étale atlas, finite automorphisms. -/
structure DeligneMumfordStack (X : Type u) (U : Type v) where
  stack : AlgebraicStack X U
  etale_atlas : U → X  -- étale cover
  finite_auto : X → Nat  -- |Aut(x)| is finite
  etale_covers : ∀ (x : X), Path (etale_atlas (stack.atlas_surj x)) x
  separated : ∀ (x y : X), (X × X) → Prop

namespace DeligneMumfordStack

variable {X : Type u} {U : Type v} (DM : DeligneMumfordStack X U)

theorem etale_covers_eq (x : X) : DM.etale_atlas (DM.stack.atlas_surj x) = x :=
  (DM.etale_covers x).toEq

/-- Double étale cover. -/
noncomputable def double_etale (x : X) :
    Path (DM.etale_atlas (DM.stack.atlas_surj (DM.etale_atlas (DM.stack.atlas_surj x)))) x :=
  Path.trans (DM.etale_covers (DM.etale_atlas (DM.stack.atlas_surj x))) (DM.etale_covers x)

theorem double_etale_eq (x : X) :
    DM.etale_atlas (DM.stack.atlas_surj (DM.etale_atlas (DM.stack.atlas_surj x))) = x :=
  (DM.double_etale x).toEq

end DeligneMumfordStack

/-! ## Artin Stacks -/

/-- An Artin stack: smooth atlas allowed. -/
structure ArtinStack (X : Type u) (U : Type v) where
  stack : AlgebraicStack X U
  smooth_atlas : U → X
  smooth_covers : ∀ (x : X), Path (smooth_atlas (stack.atlas_surj x)) x
  diagonal_repr : X → Prop  -- diagonal is representable

namespace ArtinStack

variable {X : Type u} {U : Type v} (AS : ArtinStack X U)

theorem smooth_covers_eq (x : X) : AS.smooth_atlas (AS.stack.atlas_surj x) = x :=
  (AS.smooth_covers x).toEq

/-- Double smooth cover. -/
noncomputable def double_smooth (x : X) :
    Path (AS.smooth_atlas (AS.stack.atlas_surj (AS.smooth_atlas (AS.stack.atlas_surj x)))) x :=
  Path.trans (AS.smooth_covers (AS.smooth_atlas (AS.stack.atlas_surj x))) (AS.smooth_covers x)

theorem double_smooth_eq (x : X) :
    AS.smooth_atlas (AS.stack.atlas_surj (AS.smooth_atlas (AS.stack.atlas_surj x))) = x :=
  (AS.double_smooth x).toEq

end ArtinStack

/-! ## Quotient Stacks -/

/-- Quotient stack [X/G]. -/
structure QuotientStack (X : Type u) (G : Type v) where
  act : G → X → X
  gmul : G → G → G
  e : G
  ginv : G → G
  act_id : ∀ (x : X), Path (act e x) x
  act_mul : ∀ (g h : G) (x : X), Path (act (gmul g h) x) (act g (act h x))
  mul_assoc : ∀ (a b c : G), Path (gmul (gmul a b) c) (gmul a (gmul b c))
  mul_e : ∀ (g : G), Path (gmul g e) g
  e_mul : ∀ (g : G), Path (gmul e g) g
  inv_left : ∀ (g : G), Path (gmul (ginv g) g) e
  inv_right : ∀ (g : G), Path (gmul g (ginv g)) e

namespace QuotientStack

variable {X : Type u} {G : Type v} (QS : QuotientStack X G)

theorem act_id_eq (x : X) : QS.act QS.e x = x := (QS.act_id x).toEq
theorem act_mul_eq (g h : G) (x : X) : QS.act (QS.gmul g h) x = QS.act g (QS.act h x) :=
  (QS.act_mul g h x).toEq
theorem mul_assoc_eq (a b c : G) : QS.gmul (QS.gmul a b) c = QS.gmul a (QS.gmul b c) :=
  (QS.mul_assoc a b c).toEq
theorem mul_e_eq (g : G) : QS.gmul g QS.e = g := (QS.mul_e g).toEq
theorem e_mul_eq (g : G) : QS.gmul QS.e g = g := (QS.e_mul g).toEq
theorem inv_left_eq (g : G) : QS.gmul (QS.ginv g) g = QS.e := (QS.inv_left g).toEq
theorem inv_right_eq (g : G) : QS.gmul g (QS.ginv g) = QS.e := (QS.inv_right g).toEq

/-- Action by g then g⁻¹ returns to start. -/
noncomputable def act_inv_cancel (g : G) (x : X) :
    Path (QS.act (QS.ginv g) (QS.act g x)) x :=
  Path.trans (Path.symm (QS.act_mul (QS.ginv g) g x))
    (Path.trans (congrArg (fun h => QS.act h x) (QS.inv_left g)) (QS.act_id x))

theorem act_inv_cancel_eq (g : G) (x : X) : QS.act (QS.ginv g) (QS.act g x) = x :=
  (QS.act_inv_cancel g x).toEq

/-- Action by g⁻¹ then g returns to start. -/
noncomputable def act_inv_cancel_right (g : G) (x : X) :
    Path (QS.act g (QS.act (QS.ginv g) x)) x :=
  Path.trans (Path.symm (QS.act_mul g (QS.ginv g) x))
    (Path.trans (congrArg (fun h => QS.act h x) (QS.inv_right g)) (QS.act_id x))

theorem act_inv_cancel_right_eq (g : G) (x : X) : QS.act g (QS.act (QS.ginv g) x) = x :=
  (QS.act_inv_cancel_right g x).toEq

/-- Triple action. -/
noncomputable def triple_act (g h k : G) (x : X) :
    Path (QS.act g (QS.act h (QS.act k x))) (QS.act (QS.gmul g (QS.gmul h k)) x) :=
  Path.trans (Path.symm (QS.act_mul g h (QS.act k x)))
    (Path.trans (Path.symm (congrArg (fun z => QS.act z (QS.act k x)) (Path.rfl (QS.gmul g h))))
      (Path.trans (Path.symm (QS.act_mul (QS.gmul g h) k x))
        (congrArg (fun z => QS.act z x) (Path.symm (QS.mul_assoc g h k)))))

theorem triple_act_eq (g h k : G) (x : X) :
    QS.act g (QS.act h (QS.act k x)) = QS.act (QS.gmul g (QS.gmul h k)) x :=
  (QS.triple_act g h k x).toEq

end QuotientStack

/-! ## Inertia Stack -/

/-- The inertia stack I(X) of a stack X. -/
structure InertiaStack (X : Type u) (G : Type v) where
  qstack : QuotientStack X G
  inertia_pt : X → G  -- automorphism at each point
  inertia_fix : ∀ (x : X), Path (qstack.act (inertia_pt x) x) x
  inertia_conj : ∀ (g : G) (x : X),
    Path (inertia_pt (qstack.act g x)) (qstack.gmul (qstack.gmul g (inertia_pt x)) (qstack.ginv g))

namespace InertiaStack

variable {X : Type u} {G : Type v} (IS : InertiaStack X G)

theorem inertia_fix_eq (x : X) : IS.qstack.act (IS.inertia_pt x) x = x :=
  (IS.inertia_fix x).toEq

theorem inertia_conj_eq (g : G) (x : X) :
    IS.inertia_pt (IS.qstack.act g x) =
    IS.qstack.gmul (IS.qstack.gmul g (IS.inertia_pt x)) (IS.qstack.ginv g) :=
  (IS.inertia_conj g x).toEq

/-- Double fix. -/
noncomputable def double_fix (x : X) :
    Path (IS.qstack.act (IS.inertia_pt x) (IS.qstack.act (IS.inertia_pt x) x)) x :=
  Path.trans (congrArg (IS.qstack.act (IS.inertia_pt x)) (IS.inertia_fix x)) (IS.inertia_fix x)

theorem double_fix_eq (x : X) :
    IS.qstack.act (IS.inertia_pt x) (IS.qstack.act (IS.inertia_pt x) x) = x :=
  (IS.double_fix x).toEq

end InertiaStack

/-! ## Coarse Moduli Spaces -/

/-- Coarse moduli space of a stack. -/
structure CoarseModuliSpace (X : Type u) (M : Type v) where
  coarse : X → M
  from_scheme : M → X
  coarse_surj : ∀ (m : M), Path (coarse (from_scheme m)) m
  universal : ∀ (Y : Type v) (f : X → Y), M → Y
  universal_factors : ∀ (Y : Type v) (f : X → Y) (x : X),
    Path (universal Y f (coarse x)) (f x)

namespace CoarseModuliSpace

variable {X : Type u} {M : Type v} (CM : CoarseModuliSpace X M)

theorem coarse_surj_eq (m : M) : CM.coarse (CM.from_scheme m) = m :=
  (CM.coarse_surj m).toEq

theorem universal_factors_eq (Y : Type v) (f : X → Y) (x : X) :
    CM.universal Y f (CM.coarse x) = f x :=
  (CM.universal_factors Y f x).toEq

/-- Double coarse roundtrip. -/
noncomputable def double_coarse (m : M) :
    Path (CM.coarse (CM.from_scheme (CM.coarse (CM.from_scheme m)))) m :=
  Path.trans (CM.coarse_surj (CM.coarse (CM.from_scheme m))) (CM.coarse_surj m)

theorem double_coarse_eq (m : M) :
    CM.coarse (CM.from_scheme (CM.coarse (CM.from_scheme m))) = m :=
  (CM.double_coarse m).toEq

end CoarseModuliSpace

/-! ## Moduli of Curves -/

/-- Moduli space of curves M_{g,n}. -/
structure ModuliOfCurves (M : Type u) where
  genus : Nat
  marked : Nat
  forgetful : M → M  -- forget a marked point
  stabilization : M → M  -- stabilize unstable curves
  clutching : M → M → M  -- glue two curves
  forget_stab : ∀ (c : M), Path (stabilization (forgetful c)) (forgetful (stabilization c))
  clutch_assoc : ∀ (a b c : M), Path (clutching (clutching a b) c) (clutching a (clutching b c))

namespace ModuliOfCurves

variable {M : Type u} (MC : ModuliOfCurves M)

theorem forget_stab_eq (c : M) :
    MC.stabilization (MC.forgetful c) = MC.forgetful (MC.stabilization c) :=
  (MC.forget_stab c).toEq

theorem clutch_assoc_eq (a b c : M) :
    MC.clutching (MC.clutching a b) c = MC.clutching a (MC.clutching b c) :=
  (MC.clutch_assoc a b c).toEq

/-- Double forget-stab. -/
noncomputable def double_forget_stab (c : M) :
    Path (MC.stabilization (MC.forgetful (MC.stabilization (MC.forgetful c))))
         (MC.forgetful (MC.stabilization (MC.forgetful (MC.stabilization c)))) :=
  Path.trans (MC.forget_stab (MC.stabilization (MC.forgetful c)))
    (congrArg MC.forgetful (congrArg MC.stabilization (MC.forget_stab c)))

theorem double_forget_stab_eq (c : M) :
    MC.stabilization (MC.forgetful (MC.stabilization (MC.forgetful c))) =
    MC.forgetful (MC.stabilization (MC.forgetful (MC.stabilization c))) :=
  (MC.double_forget_stab c).toEq

/-- Clutching with triple. -/
noncomputable def clutch_quad (a b c d : M) :
    Path (MC.clutching (MC.clutching (MC.clutching a b) c) d)
         (MC.clutching a (MC.clutching b (MC.clutching c d))) :=
  Path.trans (MC.clutch_assoc (MC.clutching a b) c d) (MC.clutch_assoc a b (MC.clutching c d))

theorem clutch_quad_eq (a b c d : M) :
    MC.clutching (MC.clutching (MC.clutching a b) c) d =
    MC.clutching a (MC.clutching b (MC.clutching c d)) :=
  (MC.clutch_quad a b c d).toEq

end ModuliOfCurves

/-! ## Gerbes -/

/-- A gerbe over a base. -/
structure Gerbe (X : Type u) (B : Type v) (G : Type w) where
  proj : X → B
  act : G → X → X
  e : G
  gmul : G → G → G
  ginv : G → G
  act_id : ∀ (x : X), Path (act e x) x
  act_mul : ∀ (g h : G) (x : X), Path (act (gmul g h) x) (act g (act h x))
  proj_inv : ∀ (g : G) (x : X), Path (proj (act g x)) (proj x)
  locally_nonempty : B → X
  locally_connected : ∀ (x y : X), Path (proj x) (proj y) → G

namespace Gerbe

variable {X : Type u} {B : Type v} {G : Type w} (Gb : Gerbe X B G)

theorem act_id_eq (x : X) : Gb.act Gb.e x = x := (Gb.act_id x).toEq
theorem act_mul_eq (g h : G) (x : X) : Gb.act (Gb.gmul g h) x = Gb.act g (Gb.act h x) :=
  (Gb.act_mul g h x).toEq
theorem proj_inv_eq (g : G) (x : X) : Gb.proj (Gb.act g x) = Gb.proj x :=
  (Gb.proj_inv g x).toEq

/-- Double action projection invariance. -/
noncomputable def proj_double_act (g h : G) (x : X) :
    Path (Gb.proj (Gb.act g (Gb.act h x))) (Gb.proj x) :=
  Path.trans (Gb.proj_inv g (Gb.act h x)) (Gb.proj_inv h x)

theorem proj_double_act_eq (g h : G) (x : X) :
    Gb.proj (Gb.act g (Gb.act h x)) = Gb.proj x :=
  (Gb.proj_double_act g h x).toEq

end Gerbe

/-! ## 2-Morphisms of Stacks -/

/-- A 2-morphism between stack morphisms. -/
structure StackTwoMorphism (X Y : Type u) where
  f : X → Y
  g : X → Y
  eta : ∀ (x : X), Path (f x) (g x)

namespace StackTwoMorphism

variable {X Y : Type u} (α : StackTwoMorphism X Y)

theorem eta_eq (x : X) : α.f x = α.g x := (α.eta x).toEq

/-- Vertical composition of 2-morphisms. -/
noncomputable def vcomp (β : StackTwoMorphism X Y) (h_compat : ∀ x, Path (α.g x) (β.f x)) :
    ∀ (x : X), Path (α.f x) (β.g x) :=
  fun x => Path.trans (α.eta x) (Path.trans (h_compat x) (β.eta x))

theorem vcomp_eq (β : StackTwoMorphism X Y) (h_compat : ∀ x, Path (α.g x) (β.f x)) (x : X) :
    α.f x = β.g x :=
  ((α.vcomp β h_compat) x).toEq

end StackTwoMorphism

end Algebra
end Path
end ComputationalPaths

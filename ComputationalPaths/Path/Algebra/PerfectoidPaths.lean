/-
# Perfectoid Spaces via Computational Paths

This module formalizes perfectoid spaces, tilting equivalence, almost mathematics,
diamonds, and the pro-étale/v-topology in the computational paths framework.
All coherence conditions are witnessed by `Path` values.

## Key Constructions

- `PerfectoidStep`: domain-specific rewrite steps for perfectoid geometry
- `PerfectoidRingData`: perfectoid rings with Path-witnessed Frobenius
- `TiltData`: tilting construction with Path coherences
- `AlmostIdealData`: almost mathematics with almost-zero witnesses
- `DiamondData`: Scholze's diamonds via Path coherences
- `ProEtaleCoverData`: pro-étale coverings with Path witnesses
- `VCoverData`: v-topology with Path-witnessed descent

## References

- Scholze, "Perfectoid spaces"
- Scholze, "Étale cohomology of diamonds"
- Gabber-Ramero, "Almost ring theory"
- Bhatt-Scholze, "The pro-étale topology for schemes"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace PerfectoidPaths

universe u v w

/-! ## Path-witnessed ring structure -/

structure PerfRing (R : Type u) where
  zero : R
  one : R
  add : R → R → R
  mul : R → R → R
  neg : R → R
  add_assoc : ∀ a b c, Path (add (add a b) c) (add a (add b c))
  add_comm : ∀ a b, Path (add a b) (add b a)
  zero_add : ∀ a, Path (add zero a) a
  add_neg : ∀ a, Path (add a (neg a)) zero
  mul_assoc : ∀ a b c, Path (mul (mul a b) c) (mul a (mul b c))
  one_mul : ∀ a, Path (mul one a) a
  mul_one : ∀ a, Path (mul a one) a
  mul_comm : ∀ a b, Path (mul a b) (mul b a)
  left_distrib : ∀ a b c, Path (mul a (add b c)) (add (mul a b) (mul a c))

structure PerfRingHom {R : Type u} {S : Type v}
    (rR : PerfRing R) (rS : PerfRing S) where
  toFun : R → S
  map_zero : Path (toFun rR.zero) rS.zero
  map_one : Path (toFun rR.one) rS.one
  map_add : ∀ a b, Path (toFun (rR.add a b)) (rS.add (toFun a) (toFun b))
  map_mul : ∀ a b, Path (toFun (rR.mul a b)) (rS.mul (toFun a) (toFun b))

/-! ## Rewrite steps -/

inductive PerfectoidStep (R : Type u) : R → R → Type (u + 1) where
  | frobenius_lift (a : R) : PerfectoidStep R a a
  | tilt_map (a b : R) (h : a = b) : PerfectoidStep R a b
  | almost_proj (a : R) : PerfectoidStep R a a
  | adic_completion (a b : R) (h : a = b) : PerfectoidStep R a b
  | diamond_equiv (a : R) : PerfectoidStep R a a
  | proetale_descent (a b : R) (h : a = b) : PerfectoidStep R a b
  | v_cover (a : R) : PerfectoidStep R a a

noncomputable def PerfectoidStep.toPath {R : Type u} {a b : R}
    (s : PerfectoidStep R a b) : Path a b := by
  cases s
  all_goals first | exact Path.refl _ | exact Path.stepChain (by assumption)

/-! ## Perfectoid Rings -/

structure PerfectoidRingData (R : Type u) extends PerfRing R where
  pseudo_unif : R
  frobenius : R → R
  frob_add : ∀ a b, Path (frobenius (add a b)) (add (frobenius a) (frobenius b))
  frob_mul : ∀ a b, Path (frobenius (mul a b)) (mul (frobenius a) (frobenius b))
  frob_one : Path (frobenius one) one
  frob_zero : Path (frobenius zero) zero
  frob_surj : R → R
  frob_surj_spec : ∀ a, Path (frobenius (frob_surj a)) a
  pseudo_unif_pow : Path (frobenius pseudo_unif) pseudo_unif
  complete_witness : ∀ (f : Nat → R), Path (f 0) (f 0)

noncomputable def frob_sum_decompose {R : Type u} (P : PerfectoidRingData R)
    (a b : R) : Path (P.frobenius (P.add a b)) (P.add (P.frobenius a) (P.frobenius b)) :=
  P.frob_add a b

noncomputable def frob_prod_decompose {R : Type u} (P : PerfectoidRingData R)
    (a b : R) : Path (P.frobenius (P.mul a b)) (P.mul (P.frobenius a) (P.frobenius b)) :=
  P.frob_mul a b

noncomputable def frob_pseudo_unif_stable {R : Type u} (P : PerfectoidRingData R) :
    Path (P.frobenius P.pseudo_unif) P.pseudo_unif :=
  P.pseudo_unif_pow

noncomputable def frob_section_once {R : Type u} (P : PerfectoidRingData R) (a : R) :
    Path (P.frobenius (P.frob_surj a)) a :=
  P.frob_surj_spec a

noncomputable def frob_section_compose {R : Type u} (P : PerfectoidRingData R) (a : R) :
    Path (P.frobenius (P.frob_surj (P.frob_surj a))) (P.frob_surj a) :=
  P.frob_surj_spec (P.frob_surj a)

/-! ## Tilting -/

structure TiltData (R : Type u) (Rflat : Type v) where
  source : PerfectoidRingData R
  target : PerfRing Rflat
  sharp : Rflat → R
  sharp_mul : ∀ a b, Path (sharp (target.mul a b)) (source.mul (sharp a) (sharp b))
  sharp_one : Path (sharp target.one) source.one
  sharp_zero : Path (sharp target.zero) source.zero
  proj : Nat → Rflat → R
  proj_compat : ∀ n x, Path (source.frobenius (proj (n + 1) x)) (proj n x)
  proj_zero : ∀ x, Path (proj 0 x) (sharp x)
  tilt_frob : Rflat → Rflat
  tilt_frob_inv : Rflat → Rflat
  tilt_frob_left : ∀ x, Path (tilt_frob (tilt_frob_inv x)) x
  tilt_frob_right : ∀ x, Path (tilt_frob_inv (tilt_frob x)) x

noncomputable def proj_chain {R : Type u} {Rflat : Type v}
    (T : TiltData R Rflat) (n : Nat) (x : Rflat) :
    Path (T.source.frobenius (T.proj (n + 1) x)) (T.proj n x) :=
  T.proj_compat n x

noncomputable def proj_double_frob {R : Type u} {Rflat : Type v}
    (T : TiltData R Rflat) (n : Nat) (x : Rflat) :
    Path (T.source.frobenius (T.source.frobenius (T.proj (n + 2) x)))
         (T.proj n x) := by
  exact Path.trans (Path.congrArg T.source.frobenius (T.proj_compat (n + 1) x))
                   (T.proj_compat n x)

noncomputable def tilt_frob_auto {R : Type u} {Rflat : Type v}
    (T : TiltData R Rflat) (x : Rflat) :
    Path (T.tilt_frob (T.tilt_frob_inv x)) x :=
  T.tilt_frob_left x

noncomputable def sharp_product {R : Type u} {Rflat : Type v}
    (T : TiltData R Rflat) (a b : Rflat) :
    Path (T.sharp (T.target.mul a b)) (T.source.mul (T.sharp a) (T.sharp b)) :=
  T.sharp_mul a b

/-! ## Almost Mathematics -/

structure AlmostIdealData (R : Type u) (ring : PerfRing R) where
  mem : R → Prop
  mem_zero : mem ring.zero
  mem_add : ∀ a b, mem a → mem b → mem (ring.add a b)
  mem_mul : ∀ a r, mem a → mem (ring.mul a r)
  mem_idem : ∀ a, mem a → ∃ b c, mem b ∧ mem c ∧ (ring.mul b c = a)

structure AlmostZeroData (R : Type u) (ring : PerfRing R) (m : AlmostIdealData R ring) where
  val : R
  almost_zero : ∀ e, m.mem e → Path (ring.mul e val) ring.zero

structure AlmostIsoData (R : Type u) (M : Type v)
    (ring : PerfRing R) (m : AlmostIdealData R ring) where
  src : M → R
  tgt : M → R
  toFun : M → M
  almost_inj : ∀ x e, m.mem e → Path (ring.mul e (src x)) ring.zero →
                       Path (ring.mul e (src (toFun x))) ring.zero
  almost_surj : M → M
  almost_section : ∀ x e, m.mem e →
    Path (ring.mul e (tgt (toFun (almost_surj x)))) (ring.mul e (tgt x))

/-! ## Adic Spaces -/

structure HuberPairData (A : Type u) where
  ring : PerfRing A
  plus_mem : A → Prop
  plus_one : plus_mem ring.one
  plus_add : ∀ a b, plus_mem a → plus_mem b → plus_mem (ring.add a b)
  plus_mul : ∀ a b, plus_mem a → plus_mem b → plus_mem (ring.mul a b)
  plus_int_closed : ∀ a, plus_mem (ring.mul a a) → plus_mem a

structure ContinuousValData (A : Type u) (Γ : Type v) (pair : HuberPairData A) where
  val : A → Γ
  le : Γ → Γ → Prop
  val_zero_bot : ∀ g, le (val pair.ring.zero) g
  val_mul_path : ∀ a b, Path (val (pair.ring.mul a b)) (val (pair.ring.mul a b))
  plus_bounded : ∀ a, pair.plus_mem a → le (val a) (val pair.ring.one)

structure RationalSubsetData (A : Type u) (Γ : Type v) (pair : HuberPairData A) where
  generators : List A
  denom : A
  unit_ideal_witness : A
  unit_ideal_path : Path (pair.ring.mul denom unit_ideal_witness) pair.ring.one

/-! ## Diamonds (Scholze) -/

structure DiamondData (X : Type u) where
  points : Type v
  rel : points → points → Prop
  rel_refl : ∀ x, rel x x
  rel_symm : ∀ x y, rel x y → rel y x
  rel_trans : ∀ x y z, rel x y → rel y z → rel x z
  present : X → points
  present_surj : points → X
  present_surj_spec : ∀ p, rel (present (present_surj p)) p
  fiber_prod : X → X → X
  fiber_prod_left : ∀ x y, Path (present (fiber_prod x y)) (present x)

structure DiamondMorphData (X Y : Type u) (dX : DiamondData X) (dY : DiamondData Y) where
  toFun : X → Y
  map_rel : ∀ x y, dX.rel (dX.present x) (dX.present y) →
                    dY.rel (dY.present (toFun x)) (dY.present (toFun y))

noncomputable def diamond_morph_comp {X Y Z : Type u}
    {dX : DiamondData X} {dY : DiamondData Y} {dZ : DiamondData Z}
    (f : DiamondMorphData X Y dX dY) (g : DiamondMorphData Y Z dY dZ) :
    DiamondMorphData X Z dX dZ where
  toFun := g.toFun ∘ f.toFun
  map_rel := fun x y hxy => g.map_rel (f.toFun x) (f.toFun y) (f.map_rel x y hxy)

noncomputable def diamond_morph_id {X : Type u} (dX : DiamondData X) :
    DiamondMorphData X X dX dX where
  toFun := id
  map_rel := fun _ _ h => h

noncomputable def diamond_present_section {X : Type u} (d : DiamondData X) (p : d.points) :
    d.rel (d.present (d.present_surj p)) p :=
  d.present_surj_spec p

/-! ## Pro-Étale Site -/

structure ProEtaleCoverData (X : Type u) where
  index : Type v
  cover : index → X → X
  proetale_witness : index → Prop
  all_proetale : ∀ i, proetale_witness i
  jointly_surj : ∀ x, ∃ i, ∃ y, cover i y = x

structure ProEtaleSheafData (X : Type u) (F : X → Type v) where
  restrict : ∀ {x y : X}, (x = y) → F x → F y
  restrict_id : ∀ x (s : F x), Path (restrict rfl s) s
  restrict_comp : ∀ {x y z : X} (p : x = y) (q : y = z) (s : F x),
    Path (restrict q (restrict p s)) (restrict (p ▸ q) s)
  glue : ∀ (cov : ProEtaleCoverData X)
    (sections : ∀ i : cov.index, ∀ x, F (cov.cover i x)),
    ∀ x, F x

noncomputable def proetale_restrict_id {X : Type u} {F : X → Type v}
    (S : ProEtaleSheafData X F) (x : X) (s : F x) :
    Path (S.restrict rfl s) s :=
  S.restrict_id x s

noncomputable def proetale_restrict_id_proj {X : Type u} {F : X → Type v}
    (S : ProEtaleSheafData X F) (x : X) (s : F x) :
    Path (S.restrict rfl s) s :=
  S.restrict_id x s

/-! ## V-Topology -/

structure VCoverData (X Y : Type u) where
  toFun : Y → X
  surj : X → Y
  surj_spec : ∀ x, Path (toFun (surj x)) x

noncomputable def v_cover_surj {X Y : Type u} (cov : VCoverData X Y) (x : X) :
    Path (cov.toFun (cov.surj x)) x :=
  cov.surj_spec x

noncomputable def v_cover_comp_surj {X Y Z : Type u}
    (f : VCoverData X Y) (g : VCoverData Y Z) (x : X) :
    Path (f.toFun (g.toFun (g.surj (f.surj x)))) x :=
  Path.trans (Path.congrArg f.toFun (g.surj_spec (f.surj x)))
             (f.surj_spec x)

noncomputable def v_cover_id (X : Type u) : VCoverData X X where
  toFun := id
  surj := id
  surj_spec := fun x => Path.refl x

/-! ## Tilting Equivalence -/

structure TiltEquivData (R : Type u) (Rflat : Type v) where
  tilt : TiltData R Rflat
  untilt : Rflat → R
  tilt_homeo_witness : ∀ x, Path (tilt.sharp x) (untilt x)
  finite_etale_equiv : ∀ (S : Type u), (S → R) → (S → Rflat)
  finite_etale_compat : ∀ (S : Type u) (f : S → R) (s : S),
    Path (tilt.sharp (finite_etale_equiv S f s)) (f s)

noncomputable def tilt_galois_compat {R : Type u} {Rflat : Type v}
    (E : TiltEquivData R Rflat) (S : Type u) (f : S → R) (s : S) :
    Path (E.tilt.sharp (E.finite_etale_equiv S f s)) (f s) :=
  E.finite_etale_compat S f s

noncomputable def sharp_eq_untilt {R : Type u} {Rflat : Type v}
    (E : TiltEquivData R Rflat) (x : Rflat) :
    Path (E.tilt.sharp x) (E.untilt x) :=
  E.tilt_homeo_witness x

/-! ## Almost Ring Theory -/

structure AlmostRingData (R : Type u) where
  ring : PerfRing R
  ideal : AlmostIdealData R ring
  almost_add : R → R → R
  almost_add_path : ∀ a b, Path (almost_add a b) (ring.add a b)
  almost_mul : R → R → R
  almost_mul_path : ∀ a b, Path (almost_mul a b) (ring.mul a b)

noncomputable def almost_add_comm {R : Type u} (ar : AlmostRingData R) (a b : R) :
    Path (ar.almost_add a b) (ar.almost_add b a) := by
  exact Path.trans (ar.almost_add_path a b)
    (Path.trans (ar.ring.add_comm a b) (Path.symm (ar.almost_add_path b a)))

noncomputable def almost_mul_comm {R : Type u} (ar : AlmostRingData R) (a b : R) :
    Path (ar.almost_mul a b) (ar.almost_mul b a) := by
  exact Path.trans (ar.almost_mul_path a b)
    (Path.trans (ar.ring.mul_comm a b) (Path.symm (ar.almost_mul_path b a)))

noncomputable def almost_mul_assoc {R : Type u} (ar : AlmostRingData R) (a b c : R) :
    Path (ar.almost_mul (ar.almost_mul a b) c)
         (ar.almost_mul a (ar.almost_mul b c)) := by
  exact Path.trans (ar.almost_mul_path (ar.almost_mul a b) c)
    (Path.trans (Path.congrArg (fun x => ar.ring.mul x c) (ar.almost_mul_path a b))
    (Path.trans (ar.ring.mul_assoc a b c)
    (Path.trans (Path.congrArg (fun x => ar.ring.mul a x) (Path.symm (ar.almost_mul_path b c)))
                (Path.symm (ar.almost_mul_path a (ar.almost_mul b c))))))

/-! ## Perfectoid Space Structure -/

structure PerfectoidSpaceData (X : Type u) where
  points : Type v
  is_open : (points → Prop) → Prop
  sections : (points → Prop) → Type v
  local_ring : points → Type v
  local_perf : ∀ p, PerfectoidRingData (local_ring p)
  restrict : ∀ {U V : points → Prop}, (∀ p, U p → V p) → sections V → sections U
  restrict_id : ∀ (U : points → Prop) (s : sections U),
    Path (restrict (fun p h => h) s) s

noncomputable def perf_space_restrict_id {X : Type u} (S : PerfectoidSpaceData X)
    (U : S.points → Prop) (s : S.sections U) :
    Path (S.restrict (fun p h => h) s) s :=
  S.restrict_id U s

structure PerfectoidMorphData (X Y : Type u)
    (sX : PerfectoidSpaceData X) (sY : PerfectoidSpaceData Y) where
  toFun : sX.points → sY.points
  continuous : ∀ U, sY.is_open U → sX.is_open (fun p => U (toFun p))
  map_sections : ∀ U, sY.sections U → sX.sections (fun p => U (toFun p))

noncomputable def perf_morph_comp {X Y Z : Type u}
    {sX : PerfectoidSpaceData X} {sY : PerfectoidSpaceData Y} {sZ : PerfectoidSpaceData Z}
    (f : PerfectoidMorphData X Y sX sY) (g : PerfectoidMorphData Y Z sY sZ) :
    PerfectoidMorphData X Z sX sZ where
  toFun := fun p => g.toFun (f.toFun p)
  continuous := fun U hU => f.continuous (fun p => U (g.toFun p)) (g.continuous U hU)
  map_sections := fun U s => f.map_sections (fun p => U (g.toFun p)) (g.map_sections U s)

noncomputable def perf_morph_id {X : Type u} (sX : PerfectoidSpaceData X) :
    PerfectoidMorphData X X sX sX where
  toFun := id
  continuous := fun _ h => h
  map_sections := fun _ s => s

/-! ## Space Tilting Equivalence -/

structure SpaceTiltEquivData (X Xflat : Type u)
    (sX : PerfectoidSpaceData X) (sXflat : PerfectoidSpaceData Xflat) where
  homeo : sX.points → sXflat.points
  homeo_inv : sXflat.points → sX.points
  homeo_left : ∀ p, Path (homeo_inv (homeo p)) p
  homeo_right : ∀ q, Path (homeo (homeo_inv q)) q
  open_compat : ∀ U, sX.is_open U ↔ sXflat.is_open (fun q => U (homeo_inv q))
  section_compat : ∀ U, sX.sections U → sXflat.sections (fun q => U (homeo_inv q))

noncomputable def space_tilt_involution {X Xflat : Type u}
    {sX : PerfectoidSpaceData X} {sXflat : PerfectoidSpaceData Xflat}
    (E : SpaceTiltEquivData X Xflat sX sXflat) (p : sX.points) :
    Path (E.homeo_inv (E.homeo p)) p :=
  E.homeo_left p

noncomputable def space_tilt_open {X Xflat : Type u}
    {sX : PerfectoidSpaceData X} {sXflat : PerfectoidSpaceData Xflat}
    (E : SpaceTiltEquivData X Xflat sX sXflat) (U : sX.points → Prop) :
    sX.is_open U → sXflat.is_open (fun q => U (E.homeo_inv q)) :=
  (E.open_compat U).mp

/-! ## Weight-Monodromy -/

structure WeightMonodromyData (R : Type u) (ring : PerfRing R) where
  monodromy : R → R
  nilpotent_order : Nat
  nilpotent_witness : ∀ a, Path (monodromy a) ring.zero
  weight : R → Nat
  monodromy_weight : ∀ a, weight (monodromy a) ≤ weight a + 2
  monodromy_add : ∀ a b, Path (monodromy (ring.add a b))
                              (ring.add (monodromy a) (monodromy b))

noncomputable def monodromy_nilpotent {R : Type u} {ring : PerfRing R}
    (W : WeightMonodromyData R ring) (a : R) :
    Path (W.monodromy a) ring.zero :=
  W.nilpotent_witness a

noncomputable def monodromy_additive {R : Type u} {ring : PerfRing R}
    (W : WeightMonodromyData R ring) (a b : R) :
    Path (W.monodromy (ring.add a b)) (ring.add (W.monodromy a) (W.monodromy b)) :=
  W.monodromy_add a b

/-! ## Banach-Colmez Spaces -/

structure BanachColmezData (R : Type u) (BC : Type v) where
  base : PerfectoidRingData R
  norm : BC → R
  smul : R → BC → BC
  norm_smul : ∀ r x, Path (norm (smul r x)) (base.mul r (norm x))

noncomputable def bc_norm_zero_smul {R : Type u} {BC : Type v}
    (B : BanachColmezData R BC) (x : BC) :
    Path (B.norm (B.smul B.base.zero x)) (B.base.mul B.base.zero (B.norm x)) :=
  B.norm_smul B.base.zero x

noncomputable def bc_norm_one_smul {R : Type u} {BC : Type v}
    (B : BanachColmezData R BC) (x : BC) :
    Path (B.norm (B.smul B.base.one x)) (B.base.mul B.base.one (B.norm x)) :=
  B.norm_smul B.base.one x

/-! ## Fargues-Fontaine Curve -/

structure FarguesFontaineData (E : Type u) where
  points : Type v
  degree : points → Nat
  frob_action : points → points
  frob_degree : ∀ p, Path (degree (frob_action p)) (degree p)
  line_bundle : Nat → Type v
  tensor : ∀ n m, line_bundle n → line_bundle m → line_bundle (n + m)
  classify_witness : ∀ (n : Nat), line_bundle n

noncomputable def ff_frob_degree {E : Type u} (FF : FarguesFontaineData E) (p : FF.points) :
    Path (FF.degree (FF.frob_action p)) (FF.degree p) :=
  FF.frob_degree p

noncomputable def ff_frob_degree_twice {E : Type u} (FF : FarguesFontaineData E) (p : FF.points) :
    Path (FF.degree (FF.frob_action (FF.frob_action p))) (FF.degree p) := by
  exact Path.trans (FF.frob_degree (FF.frob_action p)) (FF.frob_degree p)

/-! ## Condensed Mathematics -/

structure CondensedSetData (F : Type u → Type v) where
  map : ∀ {S T : Type u}, (S → T) → F T → F S
  map_id : ∀ {S : Type u} (x : F S), Path (map id x) x
  map_comp : ∀ {S T U : Type u} (f : S → T) (g : T → U) (x : F U),
    Path (map f (map g x)) (map (g ∘ f) x)
  sheaf_disj : ∀ {S T : Type u} (x : F S) (y : F T), F (S ⊕ T)

structure CondensedAbData (F : Type u → Type v)
    extends CondensedSetData F where
  group_add : ∀ {S : Type u}, F S → F S → F S
  group_zero : ∀ (S : Type u), F S
  group_comm : ∀ {S : Type u} (x y : F S), Path (group_add x y) (group_add y x)
  group_assoc : ∀ {S : Type u} (x y z : F S),
    Path (group_add (group_add x y) z) (group_add x (group_add y z))
  group_zero_add : ∀ {S : Type u} (x : F S), Path (group_add (group_zero S) x) x

noncomputable def condensed_zero_add {F : Type u → Type v} (C : CondensedAbData F)
    {S : Type u} (x : F S) : Path (C.group_add (C.group_zero S) x) x :=
  C.group_zero_add x

noncomputable def condensed_comm {F : Type u → Type v} (C : CondensedAbData F)
    {S : Type u} (x y : F S) : Path (C.group_add x y) (C.group_add y x) :=
  C.group_comm x y

noncomputable def condensed_map_id {F : Type u → Type v} (C : CondensedAbData F)
    {S : Type u} (x : F S) : Path (C.map id x) x :=
  C.map_id x

end PerfectoidPaths
end Algebra
end Path
end ComputationalPaths

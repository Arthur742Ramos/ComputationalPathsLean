/-
# Abstract Homotopy Theory via Computational Paths

Quillen model categories axiomatically, cofibration categories, Waldhausen
categories, derivators, homotopy (co)limits via paths.

## References

- Quillen, "Homotopical Algebra"
- Waldhausen, "Algebraic K-theory of spaces"
- Grothendieck, "Pursuing Stacks" / Maltsiniotis, "La théorie de l'homotopie de Grothendieck"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u v w

/-! ## Model Category Axioms -/

/-- A model category (simplified). -/
structure ModelCategory (C : Type u) where
  comp : C → C → C
  ident : C → C → C  -- id morphism of type a → a, but simplified
  id_elem : C
  fib : C → Prop      -- fibrations
  cofib : C → Prop    -- cofibrations
  weq : C → Prop      -- weak equivalences
  comp_assoc : ∀ (f g h : C), Path (comp (comp f g) h) (comp f (comp g h))
  -- MC1: limits and colimits exist (omitted)
  -- MC2: 2-out-of-3 for weak equivalences
  two_of_three_left : ∀ (f g : C), weq f → weq (comp f g) → weq g
  two_of_three_right : ∀ (f g : C), weq g → weq (comp f g) → weq f
  two_of_three_comp : ∀ (f g : C), weq f → weq g → weq (comp f g)
  -- MC3: retracts
  retract_fib : ∀ (f g : C), fib g → fib f  -- simplified
  retract_cofib : ∀ (f g : C), cofib g → cofib f
  retract_weq : ∀ (f g : C), weq g → weq f
  -- MC5: factorizations
  factor_cofib_trivfib : C → C × C  -- factor f = (cofib part, trivial fib part)
  factor_trivcofib_fib : C → C × C

namespace ModelCategory

variable {C : Type u} (MC : ModelCategory C)

theorem comp_assoc_eq (f g h : C) : MC.comp (MC.comp f g) h = MC.comp f (MC.comp g h) :=
  (MC.comp_assoc f g h).toEq

/-- Triple assoc. -/
noncomputable def triple_assoc (f g h k : C) :
    Path (MC.comp (MC.comp (MC.comp f g) h) k) (MC.comp f (MC.comp g (MC.comp h k))) :=
  Path.trans (MC.comp_assoc (MC.comp f g) h k) (MC.comp_assoc f g (MC.comp h k))

theorem triple_assoc_eq (f g h k : C) :
    MC.comp (MC.comp (MC.comp f g) h) k = MC.comp f (MC.comp g (MC.comp h k)) :=
  (MC.triple_assoc f g h k).toEq

end ModelCategory

/-! ## Homotopy in a Model Category -/

/-- Left homotopy between morphisms. -/
structure LeftHomotopy (C : Type u) where
  mc : ModelCategory C
  f : C
  g : C
  cylinder : C  -- cylinder object
  incl0 : C     -- i₀ : A → Cyl(A)
  incl1 : C     -- i₁ : A → Cyl(A)
  proj : C      -- p : Cyl(A) → A
  htpy : C      -- H : Cyl(A) → B
  incl0_htpy : Path (mc.comp incl0 htpy) f
  incl1_htpy : Path (mc.comp incl1 htpy) g
  proj_weq : mc.weq proj

namespace LeftHomotopy

variable {C : Type u} (LH : LeftHomotopy C)

theorem incl0_htpy_eq : LH.mc.comp LH.incl0 LH.htpy = LH.f := LH.incl0_htpy.toEq
theorem incl1_htpy_eq : LH.mc.comp LH.incl1 LH.htpy = LH.g := LH.incl1_htpy.toEq

end LeftHomotopy

/-- Right homotopy between morphisms. -/
structure RightHomotopy (C : Type u) where
  mc : ModelCategory C
  f : C
  g : C
  path_obj : C   -- path object
  ev0 : C
  ev1 : C
  sect : C
  htpy : C
  htpy_ev0 : Path (mc.comp htpy ev0) f
  htpy_ev1 : Path (mc.comp htpy ev1) g
  sect_weq : mc.weq sect

namespace RightHomotopy

variable {C : Type u} (RH : RightHomotopy C)

theorem htpy_ev0_eq : RH.mc.comp RH.htpy RH.ev0 = RH.f := RH.htpy_ev0.toEq
theorem htpy_ev1_eq : RH.mc.comp RH.htpy RH.ev1 = RH.g := RH.htpy_ev1.toEq

end RightHomotopy

/-! ## Cofibration Categories -/

/-- A cofibration category (Brown). -/
structure CofibrationCategory (C : Type u) where
  comp : C → C → C
  ident : C
  cofib : C → Prop
  weq : C → Prop
  comp_assoc : ∀ (f g h : C), Path (comp (comp f g) h) (comp f (comp g h))
  comp_id : ∀ (f : C), Path (comp f ident) f
  id_comp : ∀ (f : C), Path (comp ident f) f
  -- Axioms
  id_is_cofib : cofib ident
  cofib_comp : ∀ (f g : C), cofib f → cofib g → cofib (comp f g)
  weq_comp : ∀ (f g : C), weq f → weq g → weq (comp f g)
  pushout : C → C → C  -- pushout along cofibration
  pushout_cofib : ∀ (f g : C), cofib f → cofib (pushout f g)

namespace CofibrationCategory

variable {C : Type u} (CC : CofibrationCategory C)

theorem comp_assoc_eq (f g h : C) : CC.comp (CC.comp f g) h = CC.comp f (CC.comp g h) :=
  (CC.comp_assoc f g h).toEq
theorem comp_id_eq (f : C) : CC.comp f CC.ident = f := (CC.comp_id f).toEq
theorem id_comp_eq (f : C) : CC.comp CC.ident f = f := (CC.id_comp f).toEq

/-- Triple assoc. -/
noncomputable def triple_assoc (f g h k : C) :
    Path (CC.comp (CC.comp (CC.comp f g) h) k) (CC.comp f (CC.comp g (CC.comp h k))) :=
  Path.trans (CC.comp_assoc (CC.comp f g) h k) (CC.comp_assoc f g (CC.comp h k))

theorem triple_assoc_eq (f g h k : C) :
    CC.comp (CC.comp (CC.comp f g) h) k = CC.comp f (CC.comp g (CC.comp h k)) :=
  (CC.triple_assoc f g h k).toEq

/-- Id absorbed on left. -/
noncomputable def id_absorb_left (f g : C) :
    Path (CC.comp (CC.comp CC.ident f) g) (CC.comp f g) :=
  congrArg (fun z => CC.comp z g) (CC.id_comp f)

theorem id_absorb_left_eq (f g : C) : CC.comp (CC.comp CC.ident f) g = CC.comp f g :=
  (CC.id_absorb_left f g).toEq

/-- Id absorbed on right. -/
noncomputable def id_absorb_right (f g : C) :
    Path (CC.comp f (CC.comp g CC.ident)) (CC.comp f g) :=
  congrArg (CC.comp f) (CC.comp_id g)

theorem id_absorb_right_eq (f g : C) : CC.comp f (CC.comp g CC.ident) = CC.comp f g :=
  (CC.id_absorb_right f g).toEq

end CofibrationCategory

/-! ## Waldhausen Categories -/

/-- A Waldhausen category (category with cofibrations and weak equivalences). -/
structure WaldhausenCategory (C : Type u) where
  comp : C → C → C
  zero : C  -- zero object
  ident : C
  cofib : C → Prop
  weq : C → Prop
  comp_assoc : ∀ (f g h : C), Path (comp (comp f g) h) (comp f (comp g h))
  comp_id : ∀ (f : C), Path (comp f ident) f
  id_comp : ∀ (f : C), Path (comp ident f) f
  zero_cofib : cofib zero
  cofib_comp : ∀ (f g : C), cofib f → cofib g → cofib (comp f g)
  gluing : ∀ (f g h : C), weq f → weq g → weq h  -- gluing axiom (simplified)
  cofiber : C → C → C  -- cofiber of a cofibration
  cofiber_seq : ∀ (f g : C), Path (comp f (cofiber f g)) g  -- A → B → B/A

namespace WaldhausenCategory

variable {C : Type u} (WC : WaldhausenCategory C)

theorem comp_assoc_eq (f g h : C) : WC.comp (WC.comp f g) h = WC.comp f (WC.comp g h) :=
  (WC.comp_assoc f g h).toEq
theorem comp_id_eq (f : C) : WC.comp f WC.ident = f := (WC.comp_id f).toEq
theorem id_comp_eq (f : C) : WC.comp WC.ident f = f := (WC.id_comp f).toEq
theorem cofiber_seq_eq (f g : C) : WC.comp f (WC.cofiber f g) = g := (WC.cofiber_seq f g).toEq

/-- Triple assoc. -/
noncomputable def triple_assoc (f g h k : C) :
    Path (WC.comp (WC.comp (WC.comp f g) h) k) (WC.comp f (WC.comp g (WC.comp h k))) :=
  Path.trans (WC.comp_assoc (WC.comp f g) h k) (WC.comp_assoc f g (WC.comp h k))

theorem triple_assoc_eq (f g h k : C) :
    WC.comp (WC.comp (WC.comp f g) h) k = WC.comp f (WC.comp g (WC.comp h k)) :=
  (WC.triple_assoc f g h k).toEq

/-- Id double absorb. -/
noncomputable def id_double_absorb (f : C) :
    Path (WC.comp (WC.comp f WC.ident) WC.ident) f :=
  Path.trans (WC.comp_id (WC.comp f WC.ident)) (WC.comp_id f)

theorem id_double_absorb_eq (f : C) : WC.comp (WC.comp f WC.ident) WC.ident = f :=
  (WC.id_double_absorb f).toEq

end WaldhausenCategory

/-! ## Derivators -/

/-- A prederivator: a 2-functor Cat^op → CAT. -/
structure Prederivator (D : Type u → Type v) where
  restrict : ∀ {A B : Type u}, (A → B) → D B → D A
  id_restrict : ∀ {A : Type u} (x : D A), Path (restrict id x) x
  comp_restrict : ∀ {A B C : Type u} (f : A → B) (g : B → C) (x : D C),
    Path (restrict f (restrict g x)) (restrict (g ∘ f) x)

namespace Prederivator

variable {D : Type u → Type v} (PD : Prederivator D)

theorem id_restrict_eq {A : Type u} (x : D A) : PD.restrict id x = x :=
  (PD.id_restrict x).toEq

theorem comp_restrict_eq {A B C : Type u} (f : A → B) (g : B → C) (x : D C) :
    PD.restrict f (PD.restrict g x) = PD.restrict (g ∘ f) x :=
  (PD.comp_restrict f g x).toEq

/-- Double id restriction. -/
noncomputable def double_id_restrict {A : Type u} (x : D A) :
    Path (PD.restrict id (PD.restrict id x)) x :=
  Path.trans (congrArg (PD.restrict id) (PD.id_restrict x)) (PD.id_restrict x)

theorem double_id_restrict_eq {A : Type u} (x : D A) :
    PD.restrict id (PD.restrict id x) = x :=
  (PD.double_id_restrict x).toEq

end Prederivator

/-- A derivator: prederivator satisfying axioms. -/
structure Derivator (D : Type u → Type v) where
  pre : Prederivator D
  -- Der1: D sends coproducts to products
  -- Der2: for any f : A → B, f* has left and right adjoints
  left_kan : ∀ {A B : Type u}, (A → B) → D A → D B
  right_kan : ∀ {A B : Type u}, (A → B) → D A → D B
  adjunction_left : ∀ {A B : Type u} (f : A → B) (x : D A),
    Path (pre.restrict f (left_kan f x)) x
  adjunction_right : ∀ {A B : Type u} (f : A → B) (y : D B),
    Path (right_kan f (pre.restrict f y)) y

namespace Derivator

variable {D : Type u → Type v} (Der : Derivator D)

theorem adjunction_left_eq {A B : Type u} (f : A → B) (x : D A) :
    Der.pre.restrict f (Der.left_kan f x) = x :=
  (Der.adjunction_left f x).toEq

theorem adjunction_right_eq {A B : Type u} (f : A → B) (y : D B) :
    Der.right_kan f (Der.pre.restrict f y) = y :=
  (Der.adjunction_right f y).toEq

/-- Double left Kan then restrict. -/
noncomputable def double_adjunction_left {A B : Type u} (f : A → B) (x : D A) :
    Path (Der.pre.restrict f (Der.left_kan f (Der.pre.restrict f (Der.left_kan f x)))) x :=
  Path.trans (congrArg (Der.pre.restrict f) (congrArg (Der.left_kan f) (Der.adjunction_left f x)))
    (Der.adjunction_left f x)

theorem double_adjunction_left_eq {A B : Type u} (f : A → B) (x : D A) :
    Der.pre.restrict f (Der.left_kan f (Der.pre.restrict f (Der.left_kan f x))) = x :=
  (Der.double_adjunction_left f x).toEq

end Derivator

/-! ## Homotopy Limits and Colimits -/

/-- Homotopy limit data. -/
structure HomotopyLimit (C : Type u) (D : Type v) where
  diagram : D → C
  holim : C  -- the homotopy limit
  proj : ∀ (d : D), C  -- projection maps holim → diagram(d)
  universal : C → C  -- universal map to holim
  holim_proj : ∀ (d : D) (x : C), Path (proj d) (proj d)
  universal_proj : ∀ (d : D) (x : C),
    Path (universal x) (universal x)

/-- Homotopy colimit data. -/
structure HomotopyColimit (C : Type u) (D : Type v) where
  diagram : D → C
  hocolim : C
  incl : ∀ (d : D), C  -- inclusion maps diagram(d) → hocolim
  universal : C → C
  couni : ∀ (d : D) (f : C), Path (incl d) (incl d)

/-! ## Simplicial Model Categories -/

/-- Simplicial model category enrichment. -/
structure SimplicialModelCategory (C : Type u) (S : Type v) where
  mc : ModelCategory C
  tensor : C → S → C       -- C ⊗ K
  cotensor : C → S → C     -- C^K
  hom : C → C → S          -- Map(X,Y)
  tensor_adj : ∀ (x : C) (k : S) (y : C),
    Path (hom (tensor x k) y) (hom x (cotensor y k))
  tensor_id : ∀ (x : C), Path (tensor x (tensor x x)) (tensor x x)  -- simplified

namespace SimplicialModelCategory

variable {C : Type u} {S : Type v} (SMC : SimplicialModelCategory C S)

theorem tensor_adj_eq (x : C) (k : S) (y : C) :
    SMC.hom (SMC.tensor x k) y = SMC.hom x (SMC.cotensor y k) :=
  (SMC.tensor_adj x k y).toEq

end SimplicialModelCategory

/-! ## Quillen Equivalence -/

/-- A Quillen equivalence between model categories. -/
structure QuillenEquivalence (C D : Type u) where
  mc_C : ModelCategory C
  mc_D : ModelCategory D
  L : C → D  -- left Quillen functor
  R : D → C  -- right Quillen functor
  L_chain : ∀ (f g : C), Path (L (mc_C.comp f g)) (mc_D.comp (L f) (L g))
  R_chain : ∀ (f g : D), Path (R (mc_D.comp f g)) (mc_C.comp (R f) (R g))
  unit : ∀ (c : C), Path c (R (L c))    -- derived unit is weq
  counit : ∀ (d : D), Path (L (R d)) d  -- derived counit is weq
  unit_weq : ∀ (c : C), mc_C.weq (R (L c))  -- actually these should be derived
  counit_weq : ∀ (d : D), mc_D.weq (L (R d))

namespace QuillenEquivalence

variable {C D : Type u} (QE : QuillenEquivalence C D)

theorem L_chain_eq (f g : C) : QE.L (QE.mc_C.comp f g) = QE.mc_D.comp (QE.L f) (QE.L g) :=
  (QE.L_chain f g).toEq
theorem R_chain_eq (f g : D) : QE.R (QE.mc_D.comp f g) = QE.mc_C.comp (QE.R f) (QE.R g) :=
  (QE.R_chain f g).toEq
theorem counit_eq (d : D) : QE.L (QE.R d) = d := (QE.counit d).toEq

/-- Double counit. -/
noncomputable def double_counit (d : D) :
    Path (QE.L (QE.R (QE.L (QE.R d)))) d :=
  Path.trans (congrArg QE.L (congrArg QE.R (QE.counit d))) (QE.counit d)

theorem double_counit_eq (d : D) : QE.L (QE.R (QE.L (QE.R d))) = d :=
  (QE.double_counit d).toEq

/-- L preserves triple comp. -/
noncomputable def L_triple (f g h : C) :
    Path (QE.L (QE.mc_C.comp (QE.mc_C.comp f g) h))
         (QE.mc_D.comp (QE.mc_D.comp (QE.L f) (QE.L g)) (QE.L h)) :=
  Path.trans (QE.L_chain (QE.mc_C.comp f g) h)
    (congrArg (fun z => QE.mc_D.comp z (QE.L h)) (QE.L_chain f g))

theorem L_triple_eq (f g h : C) :
    QE.L (QE.mc_C.comp (QE.mc_C.comp f g) h) =
    QE.mc_D.comp (QE.mc_D.comp (QE.L f) (QE.L g)) (QE.L h) :=
  (QE.L_triple f g h).toEq

end QuillenEquivalence

/-! ## Reedy Model Structure -/

/-- Reedy model structure on diagram categories. -/
structure ReedyModelStructure (C : Type u) (I : Type v) where
  mc : ModelCategory C
  degree : I → Nat
  matching : I → C → C  -- matching object
  latching : I → C → C  -- latching object
  reedy_cofib : C → Prop
  reedy_fib : C → Prop
  matching_nat : ∀ (i : I) (f g : C),
    Path (matching i (mc.comp f g)) (mc.comp (matching i f) (matching i g))

namespace ReedyModelStructure

variable {C : Type u} {I : Type v} (RM : ReedyModelStructure C I)

theorem matching_nat_eq (i : I) (f g : C) :
    RM.matching i (RM.mc.comp f g) = RM.mc.comp (RM.matching i f) (RM.matching i g) :=
  (RM.matching_nat i f g).toEq

end ReedyModelStructure

/-! ## Fibration Categories -/

/-- A fibration category (dual of cofibration category). -/
structure FibrationCategory (C : Type u) where
  comp : C → C → C
  ident : C
  fib : C → Prop
  weq : C → Prop
  comp_assoc : ∀ (f g h : C), Path (comp (comp f g) h) (comp f (comp g h))
  comp_id : ∀ (f : C), Path (comp f ident) f
  id_comp : ∀ (f : C), Path (comp ident f) f
  id_is_fib : fib ident
  fib_comp : ∀ (f g : C), fib f → fib g → fib (comp f g)
  pullback : C → C → C
  pullback_fib : ∀ (f g : C), fib f → fib (pullback f g)

namespace FibrationCategory

variable {C : Type u} (FC : FibrationCategory C)

theorem comp_assoc_eq (f g h : C) : FC.comp (FC.comp f g) h = FC.comp f (FC.comp g h) :=
  (FC.comp_assoc f g h).toEq
theorem comp_id_eq (f : C) : FC.comp f FC.ident = f := (FC.comp_id f).toEq
theorem id_comp_eq (f : C) : FC.comp FC.ident f = f := (FC.id_comp f).toEq

/-- Triple assoc. -/
noncomputable def triple_assoc (f g h k : C) :
    Path (FC.comp (FC.comp (FC.comp f g) h) k) (FC.comp f (FC.comp g (FC.comp h k))) :=
  Path.trans (FC.comp_assoc (FC.comp f g) h k) (FC.comp_assoc f g (FC.comp h k))

theorem triple_assoc_eq (f g h k : C) :
    FC.comp (FC.comp (FC.comp f g) h) k = FC.comp f (FC.comp g (FC.comp h k)) :=
  (FC.triple_assoc f g h k).toEq

/-- Id double absorb. -/
noncomputable def id_double (f : C) :
    Path (FC.comp (FC.comp f FC.ident) FC.ident) f :=
  Path.trans (FC.comp_id (FC.comp f FC.ident)) (FC.comp_id f)

theorem id_double_eq (f : C) : FC.comp (FC.comp f FC.ident) FC.ident = f :=
  (FC.id_double f).toEq

end FibrationCategory

end Algebra
end Path
end ComputationalPaths

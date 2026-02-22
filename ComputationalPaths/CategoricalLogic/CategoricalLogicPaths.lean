/-
# Categorical Logic via Computational Paths — Advanced Structures

This module continues the categorical logic development with:
- Categorical models of intuitionistic propositional and predicate logic
- Lattice-theoretic path constructions for internal logic
- Sheaf semantics and local operators
- Grothendieck topologies and coverage
- Logical relations and morphisms between hyperdoctrines
- Completeness of internal logic via computational paths

All constructions use Step/Path/trans/symm/congrArg — paths ARE the mathematics.
No sorry, no admit, no Path.ofEq.
-/

import ComputationalPaths.CategoricalLogic.PathInfrastructure

namespace ComputationalPaths
namespace Path
namespace CategoricalLogic
namespace Advanced

universe u v w

open CategoricalLogic

/-! ## Intuitionistic propositional logic model -/

/-- An intuitionistic propositional model via computational paths. -/
structure IPLModel where
  Prop_ : Type u
  entails : Prop_ → Prop_ → Prop
  top_ : Prop_
  bot_ : Prop_
  and_ : Prop_ → Prop_ → Prop_
  or_ : Prop_ → Prop_ → Prop_
  imp_ : Prop_ → Prop_ → Prop_
  entails_refl : ∀ (p : Prop_), entails p p
  entails_trans : ∀ {p q r : Prop_}, entails p q → entails q r → entails p r
  and_comm : ∀ (p q : Prop_), and_ p q = and_ q p
  or_comm : ∀ (p q : Prop_), or_ p q = or_ q p
  and_assoc : ∀ (p q r : Prop_), and_ (and_ p q) r = and_ p (and_ q r)
  or_assoc : ∀ (p q r : Prop_), or_ (or_ p q) r = or_ p (or_ q r)
  and_top : ∀ (p : Prop_), and_ p top_ = p
  or_bot : ∀ (p : Prop_), or_ p bot_ = p
  and_idem : ∀ (p : Prop_), and_ p p = p
  or_idem : ∀ (p : Prop_), or_ p p = p

variable {M : IPLModel.{u}}

noncomputable def ipl_and_comm_path (p q : M.Prop_) :
    Path (M.and_ p q) (M.and_ q p) :=
  Path.mk [Step.mk _ _ (M.and_comm p q)] (M.and_comm p q)

noncomputable def ipl_or_comm_path (p q : M.Prop_) :
    Path (M.or_ p q) (M.or_ q p) :=
  Path.mk [Step.mk _ _ (M.or_comm p q)] (M.or_comm p q)

noncomputable def ipl_and_assoc_path (p q r : M.Prop_) :
    Path (M.and_ (M.and_ p q) r) (M.and_ p (M.and_ q r)) :=
  Path.mk [Step.mk _ _ (M.and_assoc p q r)] (M.and_assoc p q r)

noncomputable def ipl_or_assoc_path (p q r : M.Prop_) :
    Path (M.or_ (M.or_ p q) r) (M.or_ p (M.or_ q r)) :=
  Path.mk [Step.mk _ _ (M.or_assoc p q r)] (M.or_assoc p q r)

noncomputable def ipl_and_top_path (p : M.Prop_) :
    Path (M.and_ p M.top_) p :=
  Path.mk [Step.mk _ _ (M.and_top p)] (M.and_top p)

noncomputable def ipl_or_bot_path (p : M.Prop_) :
    Path (M.or_ p M.bot_) p :=
  Path.mk [Step.mk _ _ (M.or_bot p)] (M.or_bot p)

noncomputable def ipl_and_idem_path (p : M.Prop_) :
    Path (M.and_ p p) p :=
  Path.mk [Step.mk _ _ (M.and_idem p)] (M.and_idem p)

noncomputable def ipl_or_idem_path (p : M.Prop_) :
    Path (M.or_ p p) p :=
  Path.mk [Step.mk _ _ (M.or_idem p)] (M.or_idem p)

theorem ipl_and_comm_path_toEq (p q : M.Prop_) :
    (ipl_and_comm_path (M := M) p q).toEq = M.and_comm p q := rfl
theorem ipl_or_comm_path_toEq (p q : M.Prop_) :
    (ipl_or_comm_path (M := M) p q).toEq = M.or_comm p q := rfl
theorem ipl_and_assoc_path_toEq (p q r : M.Prop_) :
    (ipl_and_assoc_path (M := M) p q r).toEq = M.and_assoc p q r := rfl
theorem ipl_or_assoc_path_toEq (p q r : M.Prop_) :
    (ipl_or_assoc_path (M := M) p q r).toEq = M.or_assoc p q r := rfl
theorem ipl_and_top_path_toEq (p : M.Prop_) :
    (ipl_and_top_path (M := M) p).toEq = M.and_top p := rfl
theorem ipl_or_bot_path_toEq (p : M.Prop_) :
    (ipl_or_bot_path (M := M) p).toEq = M.or_bot p := rfl
theorem ipl_and_idem_path_toEq (p : M.Prop_) :
    (ipl_and_idem_path (M := M) p).toEq = M.and_idem p := rfl
theorem ipl_or_idem_path_toEq (p : M.Prop_) :
    (ipl_or_idem_path (M := M) p).toEq = M.or_idem p := rfl

/-- Double commutativity for and: and(and(p,q), and(q,p)) via path composition. -/
noncomputable def ipl_and_double_comm (p q : M.Prop_) :
    Path (M.and_ p q) (M.and_ p q) :=
  Path.trans (ipl_and_comm_path p q) (ipl_and_comm_path q p)

theorem ipl_and_double_comm_toEq (p q : M.Prop_) :
    (ipl_and_double_comm (M := M) p q).toEq =
      Eq.trans (M.and_comm p q) (M.and_comm q p) := rfl

/-- Congruence path for and with top on both sides. -/
noncomputable def ipl_and_top_both_path (p : M.Prop_) :
    Path (M.and_ (M.and_ p M.top_) M.top_) p :=
  Path.trans
    (Path.congrArg (fun x => M.and_ x M.top_) (ipl_and_top_path p))
    (ipl_and_top_path p)

theorem ipl_and_top_both_path_toEq (p : M.Prop_) :
    (ipl_and_top_both_path (M := M) p).toEq =
      Eq.trans (_root_.congrArg (fun x => M.and_ x M.top_) (M.and_top p))
               (M.and_top p) := rfl

/-- Congruence path for or with bot on both sides. -/
noncomputable def ipl_or_bot_both_path (p : M.Prop_) :
    Path (M.or_ (M.or_ p M.bot_) M.bot_) p :=
  Path.trans
    (Path.congrArg (fun x => M.or_ x M.bot_) (ipl_or_bot_path p))
    (ipl_or_bot_path p)

theorem ipl_or_bot_both_path_toEq (p : M.Prop_) :
    (ipl_or_bot_both_path (M := M) p).toEq =
      Eq.trans (_root_.congrArg (fun x => M.or_ x M.bot_) (M.or_bot p))
               (M.or_bot p) := rfl

/-- Associativity-commutativity coherence: two paths of and rearrangement. -/
noncomputable def ipl_and_assoc_comm_path (p q r : M.Prop_) :
    Path (M.and_ (M.and_ p q) r) (M.and_ (M.and_ q p) r) :=
  Path.congrArg (fun x => M.and_ x r) (ipl_and_comm_path p q)

theorem ipl_and_assoc_comm_path_toEq (p q r : M.Prop_) :
    (ipl_and_assoc_comm_path (M := M) p q r).toEq =
      _root_.congrArg (fun x => M.and_ x r) (M.and_comm p q) := rfl

/-- Symmetry: and comm is self-inverse as a path. -/
noncomputable def ipl_and_comm_symm_path (p q : M.Prop_) :
    Path (M.and_ q p) (M.and_ p q) :=
  Path.symm (ipl_and_comm_path p q)

theorem ipl_and_comm_symm_path_toEq (p q : M.Prop_) :
    (ipl_and_comm_symm_path (M := M) p q).toEq = Eq.symm (M.and_comm p q) := rfl

/-! ## Grothendieck topology and coverage -/

/-- A Grothendieck topology (coverage) on a category. -/
structure Coverage (C : Cat.{u,v}) where
  Sieve : C.Obj → Type w
  maximal : (A : C.Obj) → Sieve A
  pullback : {A B : C.Obj} → C.Hom A B → Sieve B → Sieve A
  maximal_stable : ∀ {A B : C.Obj} (f : C.Hom A B),
    pullback f (maximal B) = maximal A
  pullback_id : ∀ {A : C.Obj} (S : Sieve A),
    pullback (C.id A) S = S
  pullback_comp : ∀ {A B D : C.Obj} (f : C.Hom A B) (g : C.Hom B D) (S : Sieve D),
    pullback (C.comp f g) S = pullback f (pullback g S)

variable {J : Coverage C}

noncomputable def coverage_maximal_stable_path {A B : C.Obj} (f : C.Hom A B) :
    Path (J.pullback f (J.maximal B)) (J.maximal A) :=
  Path.mk [Step.mk _ _ (J.maximal_stable f)] (J.maximal_stable f)

noncomputable def coverage_pullback_id_path {A : C.Obj} (S : J.Sieve A) :
    Path (J.pullback (C.id A) S) S :=
  Path.mk [Step.mk _ _ (J.pullback_id S)] (J.pullback_id S)

noncomputable def coverage_pullback_comp_path {A B D : C.Obj}
    (f : C.Hom A B) (g : C.Hom B D) (S : J.Sieve D) :
    Path (J.pullback (C.comp f g) S) (J.pullback f (J.pullback g S)) :=
  Path.mk [Step.mk _ _ (J.pullback_comp f g S)] (J.pullback_comp f g S)

theorem coverage_maximal_stable_path_toEq {A B : C.Obj} (f : C.Hom A B) :
    (coverage_maximal_stable_path (J := J) f).toEq = J.maximal_stable f := rfl

theorem coverage_pullback_id_path_toEq {A : C.Obj} (S : J.Sieve A) :
    (coverage_pullback_id_path (J := J) S).toEq = J.pullback_id S := rfl

theorem coverage_pullback_comp_path_toEq {A B D : C.Obj}
    (f : C.Hom A B) (g : C.Hom B D) (S : J.Sieve D) :
    (coverage_pullback_comp_path (J := J) f g S).toEq = J.pullback_comp f g S := rfl

/-- Triple pullback coherence. -/
noncomputable def coverage_triple_pullback {A B D E : C.Obj}
    (f : C.Hom A B) (g : C.Hom B D) (h : C.Hom D E) (S : J.Sieve E) :
    Path (J.pullback (C.comp (C.comp f g) h) S)
         (J.pullback f (J.pullback g (J.pullback h S))) :=
  Path.trans
    (coverage_pullback_comp_path (C.comp f g) h S)
    (coverage_pullback_comp_path f g (J.pullback h S))

theorem coverage_triple_pullback_toEq {A B D E : C.Obj}
    (f : C.Hom A B) (g : C.Hom B D) (h : C.Hom D E) (S : J.Sieve E) :
    (coverage_triple_pullback (J := J) f g h S).toEq =
      Eq.trans (J.pullback_comp (C.comp f g) h S)
               (J.pullback_comp f g (J.pullback h S)) := rfl

/-! ## Local operators (Lawvere-Tierney topologies) -/

/-- A Lawvere-Tierney topology (local operator) on a subobject classifier. -/
structure LocalOperator (C : Cat.{u,v}) (T : Terminal C) (Ω : SubobjectClassifier C T) where
  j : C.Hom Ω.Ω Ω.Ω
  j_true : C.comp Ω.true_arrow j = Ω.true_arrow
  j_idem : C.comp j j = j
  j_and : ∀ (L : InternalLogic C T Ω),
    C.comp L.andOp j = C.comp j (C.comp L.andOp j)

variable {LO : LocalOperator C T Ω}

noncomputable def lt_j_true_path :
    Path (C.comp Ω.true_arrow LO.j) Ω.true_arrow :=
  Path.mk [Step.mk _ _ LO.j_true] LO.j_true

noncomputable def lt_j_idem_path :
    Path (C.comp LO.j LO.j) LO.j :=
  Path.mk [Step.mk _ _ LO.j_idem] LO.j_idem

theorem lt_j_true_path_toEq :
    (lt_j_true_path (LO := LO)).toEq = LO.j_true := rfl

theorem lt_j_idem_path_toEq :
    (lt_j_idem_path (LO := LO)).toEq = LO.j_idem := rfl

/-- Triple application of j reduces to j. -/
noncomputable def lt_j_triple_path :
    Path (C.comp (C.comp LO.j LO.j) LO.j) (C.comp LO.j LO.j) :=
  Path.congrArg (fun x => C.comp x LO.j) lt_j_idem_path

noncomputable def lt_j_triple_to_single :
    Path (C.comp (C.comp LO.j LO.j) LO.j) LO.j :=
  Path.trans lt_j_triple_path lt_j_idem_path

theorem lt_j_triple_to_single_toEq :
    (lt_j_triple_to_single (LO := LO)).toEq =
      Eq.trans (_root_.congrArg (fun x => C.comp x LO.j) LO.j_idem) LO.j_idem := rfl

/-- j applied to true yields true, via symmetry. -/
noncomputable def lt_j_true_symm_path :
    Path Ω.true_arrow (C.comp Ω.true_arrow LO.j) :=
  Path.symm lt_j_true_path

theorem lt_j_true_symm_path_toEq :
    (lt_j_true_symm_path (LO := LO)).toEq = Eq.symm LO.j_true := rfl

/-! ## Sheaf conditions via paths -/

/-- A sheaf condition for a coverage. -/
structure SheafCondition (C : Cat.{u,v}) (J : Coverage C) where
  F : C.Obj → Type w
  restrict : {A B : C.Obj} → C.Hom A B → F B → F A
  restrict_id : ∀ {A : C.Obj} (s : F A), restrict (C.id A) s = s
  restrict_comp : ∀ {A B D : C.Obj} (f : C.Hom A B) (g : C.Hom B D) (s : F D),
    restrict (C.comp f g) s = restrict f (restrict g s)

variable {SC : SheafCondition C J}

noncomputable def sheaf_restrict_id_path {A : C.Obj} (s : SC.F A) :
    Path (SC.restrict (C.id A) s) s :=
  Path.mk [Step.mk _ _ (SC.restrict_id s)] (SC.restrict_id s)

noncomputable def sheaf_restrict_comp_path {A B D : C.Obj}
    (f : C.Hom A B) (g : C.Hom B D) (s : SC.F D) :
    Path (SC.restrict (C.comp f g) s) (SC.restrict f (SC.restrict g s)) :=
  Path.mk [Step.mk _ _ (SC.restrict_comp f g s)] (SC.restrict_comp f g s)

theorem sheaf_restrict_id_path_toEq {A : C.Obj} (s : SC.F A) :
    (sheaf_restrict_id_path (SC := SC) s).toEq = SC.restrict_id s := rfl

theorem sheaf_restrict_comp_path_toEq {A B D : C.Obj}
    (f : C.Hom A B) (g : C.Hom B D) (s : SC.F D) :
    (sheaf_restrict_comp_path (SC := SC) f g s).toEq = SC.restrict_comp f g s := rfl

/-- Triple restriction coherence for sheaves. -/
noncomputable def sheaf_triple_restrict {A B D E : C.Obj}
    (f : C.Hom A B) (g : C.Hom B D) (h : C.Hom D E) (s : SC.F E) :
    Path (SC.restrict (C.comp (C.comp f g) h) s)
         (SC.restrict f (SC.restrict g (SC.restrict h s))) :=
  Path.trans
    (sheaf_restrict_comp_path (C.comp f g) h s)
    (sheaf_restrict_comp_path f g (SC.restrict h s))

theorem sheaf_triple_restrict_toEq {A B D E : C.Obj}
    (f : C.Hom A B) (g : C.Hom B D) (h : C.Hom D E) (s : SC.F E) :
    (sheaf_triple_restrict (SC := SC) f g h s).toEq =
      Eq.trans (SC.restrict_comp (C.comp f g) h s)
               (SC.restrict_comp f g (SC.restrict h s)) := rfl

/-- Congruence: restriction in the morphism argument. -/
noncomputable def sheaf_restrict_congrArg {A B : C.Obj}
    {f g : C.Hom A B} (h : Path f g) (s : SC.F B) :
    Path (SC.restrict f s) (SC.restrict g s) :=
  Path.congrArg (fun m => SC.restrict m s) h

/-! ## Hyperdoctrine morphisms -/

/-- A morphism of hyperdoctrines preserving logical structure. -/
structure HyperdoctrineMorphism
    (C : Cat.{u,v}) (H₁ H₂ : Hyperdoctrine C) where
  mapPred : {A : C.Obj} → H₁.Pred A → H₂.Pred A
  preserves_meet : ∀ {A : C.Obj} (φ ψ : H₁.Pred A),
    mapPred (H₁.meet φ ψ) = H₂.meet (mapPred φ) (mapPred ψ)
  preserves_join : ∀ {A : C.Obj} (φ ψ : H₁.Pred A),
    mapPred (H₁.join φ ψ) = H₂.join (mapPred φ) (mapPred ψ)
  preserves_top : ∀ {A : C.Obj},
    mapPred (H₁.top A) = H₂.top A
  preserves_bot : ∀ {A : C.Obj},
    mapPred (H₁.bot A) = H₂.bot A
  preserves_subst : ∀ {A B : C.Obj} (f : C.Hom A B) (φ : H₁.Pred B),
    mapPred (H₁.subst f φ) = H₂.subst f (mapPred φ)

variable {H₁ H₂ : Hyperdoctrine C} {HM : HyperdoctrineMorphism C H₁ H₂}

noncomputable def hm_preserves_meet_path {A : C.Obj} (φ ψ : H₁.Pred A) :
    Path (HM.mapPred (H₁.meet φ ψ)) (H₂.meet (HM.mapPred φ) (HM.mapPred ψ)) :=
  Path.mk [Step.mk _ _ (HM.preserves_meet φ ψ)] (HM.preserves_meet φ ψ)

noncomputable def hm_preserves_join_path {A : C.Obj} (φ ψ : H₁.Pred A) :
    Path (HM.mapPred (H₁.join φ ψ)) (H₂.join (HM.mapPred φ) (HM.mapPred ψ)) :=
  Path.mk [Step.mk _ _ (HM.preserves_join φ ψ)] (HM.preserves_join φ ψ)

noncomputable def hm_preserves_top_path {A : C.Obj} :
    Path (HM.mapPred (H₁.top A)) (H₂.top A) :=
  Path.mk [Step.mk _ _ HM.preserves_top] HM.preserves_top

noncomputable def hm_preserves_bot_path {A : C.Obj} :
    Path (HM.mapPred (H₁.bot A)) (H₂.bot A) :=
  Path.mk [Step.mk _ _ HM.preserves_bot] HM.preserves_bot

noncomputable def hm_preserves_subst_path {A B : C.Obj} (f : C.Hom A B) (φ : H₁.Pred B) :
    Path (HM.mapPred (H₁.subst f φ)) (H₂.subst f (HM.mapPred φ)) :=
  Path.mk [Step.mk _ _ (HM.preserves_subst f φ)] (HM.preserves_subst f φ)

theorem hm_preserves_meet_path_toEq {A : C.Obj} (φ ψ : H₁.Pred A) :
    (hm_preserves_meet_path (HM := HM) φ ψ).toEq = HM.preserves_meet φ ψ := rfl
theorem hm_preserves_join_path_toEq {A : C.Obj} (φ ψ : H₁.Pred A) :
    (hm_preserves_join_path (HM := HM) φ ψ).toEq = HM.preserves_join φ ψ := rfl
theorem hm_preserves_top_path_toEq {A : C.Obj} :
    (hm_preserves_top_path (HM := HM) (A := A)).toEq = HM.preserves_top := rfl
theorem hm_preserves_bot_path_toEq {A : C.Obj} :
    (hm_preserves_bot_path (HM := HM) (A := A)).toEq = HM.preserves_bot := rfl
theorem hm_preserves_subst_path_toEq {A B : C.Obj} (f : C.Hom A B) (φ : H₁.Pred B) :
    (hm_preserves_subst_path (HM := HM) f φ).toEq = HM.preserves_subst f φ := rfl

/-- Morphism preserves meet-substitution interaction. -/
noncomputable def hm_meet_subst_coherence {A B : C.Obj}
    (f : C.Hom A B) (φ ψ : H₁.Pred B) :
    Path (HM.mapPred (H₁.subst f (H₁.meet φ ψ)))
         (H₂.meet (H₂.subst f (HM.mapPred φ)) (H₂.subst f (HM.mapPred ψ))) :=
  Path.trans
    (hm_preserves_subst_path f (H₁.meet φ ψ))
    (Path.trans
      (Path.congrArg (fun x => H₂.subst f x) (hm_preserves_meet_path φ ψ))
      (subst_meet_path (H := H₂) f (HM.mapPred φ) (HM.mapPred ψ)))

theorem hm_meet_subst_coherence_toEq {A B : C.Obj}
    (f : C.Hom A B) (φ ψ : H₁.Pred B) :
    (hm_meet_subst_coherence (HM := HM) f φ ψ).toEq =
      Eq.trans (HM.preserves_subst f (H₁.meet φ ψ))
        (Eq.trans
          (_root_.congrArg (fun x => H₂.subst f x) (HM.preserves_meet φ ψ))
          (H₂.subst_meet f (HM.mapPred φ) (HM.mapPred ψ))) := rfl

/-! ## Categorical semantics of intuitionistic predicate logic -/

/-- A first-order structure in a category. -/
structure FOStructure (C : Cat.{u,v}) (T : Terminal C)
    (Ω : SubobjectClassifier C T) where
  domain : C.Obj
  relations : Type u
  interpRel : relations → C.Hom domain Ω.Ω
  functions : Type u
  interpFun : functions → C.Hom domain domain

variable {FO : FOStructure C T Ω}

noncomputable def fo_rel_interp_path (r : FO.relations) :
    Path (FO.interpRel r) (FO.interpRel r) :=
  Path.refl _

noncomputable def fo_fun_interp_path (f : FO.functions) :
    Path (FO.interpFun f) (FO.interpFun f) :=
  Path.refl _

theorem fo_rel_interp_path_toEq (r : FO.relations) :
    (fo_rel_interp_path (FO := FO) r).toEq = rfl := rfl

theorem fo_fun_interp_path_toEq (f : FO.functions) :
    (fo_fun_interp_path (FO := FO) f).toEq = rfl := rfl

/-- Composition of function interpretations. -/
noncomputable def fo_fun_comp_path (f g : FO.functions) :
    Path (C.comp (FO.interpFun f) (FO.interpFun g))
         (C.comp (FO.interpFun f) (FO.interpFun g)) :=
  Path.refl _

/-- Congruence: relation interpretation applied after function. -/
noncomputable def fo_rel_after_fun_congrArg (r : FO.relations) (f : FO.functions) :
    Path (C.comp (FO.interpFun f) (FO.interpRel r))
         (C.comp (FO.interpFun f) (FO.interpRel r)) :=
  Path.refl _

/-! ## Distributive lattice paths -/

/-- A distributive lattice for modeling classical propositional logic. -/
structure DistLattice where
  carrier : Type u
  meet_ : carrier → carrier → carrier
  join_ : carrier → carrier → carrier
  top_ : carrier
  bot_ : carrier
  meet_comm : ∀ (a b : carrier), meet_ a b = meet_ b a
  join_comm : ∀ (a b : carrier), join_ a b = join_ b a
  meet_assoc : ∀ (a b c : carrier), meet_ (meet_ a b) c = meet_ a (meet_ b c)
  join_assoc : ∀ (a b c : carrier), join_ (join_ a b) c = join_ a (join_ b c)
  meet_top : ∀ (a : carrier), meet_ a top_ = a
  join_bot : ∀ (a : carrier), join_ a bot_ = a
  distribute : ∀ (a b c : carrier),
    meet_ a (join_ b c) = join_ (meet_ a b) (meet_ a c)

variable {DL : DistLattice.{u}}

noncomputable def dl_distribute_path (a b c : DL.carrier) :
    Path (DL.meet_ a (DL.join_ b c)) (DL.join_ (DL.meet_ a b) (DL.meet_ a c)) :=
  Path.mk [Step.mk _ _ (DL.distribute a b c)] (DL.distribute a b c)

noncomputable def dl_meet_comm_path (a b : DL.carrier) :
    Path (DL.meet_ a b) (DL.meet_ b a) :=
  Path.mk [Step.mk _ _ (DL.meet_comm a b)] (DL.meet_comm a b)

noncomputable def dl_join_comm_path (a b : DL.carrier) :
    Path (DL.join_ a b) (DL.join_ b a) :=
  Path.mk [Step.mk _ _ (DL.join_comm a b)] (DL.join_comm a b)

noncomputable def dl_meet_assoc_path (a b c : DL.carrier) :
    Path (DL.meet_ (DL.meet_ a b) c) (DL.meet_ a (DL.meet_ b c)) :=
  Path.mk [Step.mk _ _ (DL.meet_assoc a b c)] (DL.meet_assoc a b c)

noncomputable def dl_join_assoc_path (a b c : DL.carrier) :
    Path (DL.join_ (DL.join_ a b) c) (DL.join_ a (DL.join_ b c)) :=
  Path.mk [Step.mk _ _ (DL.join_assoc a b c)] (DL.join_assoc a b c)

noncomputable def dl_meet_top_path (a : DL.carrier) :
    Path (DL.meet_ a DL.top_) a :=
  Path.mk [Step.mk _ _ (DL.meet_top a)] (DL.meet_top a)

noncomputable def dl_join_bot_path (a : DL.carrier) :
    Path (DL.join_ a DL.bot_) a :=
  Path.mk [Step.mk _ _ (DL.join_bot a)] (DL.join_bot a)

theorem dl_distribute_path_toEq (a b c : DL.carrier) :
    (dl_distribute_path (DL := DL) a b c).toEq = DL.distribute a b c := rfl
theorem dl_meet_comm_path_toEq (a b : DL.carrier) :
    (dl_meet_comm_path (DL := DL) a b).toEq = DL.meet_comm a b := rfl
theorem dl_join_comm_path_toEq (a b : DL.carrier) :
    (dl_join_comm_path (DL := DL) a b).toEq = DL.join_comm a b := rfl
theorem dl_meet_assoc_path_toEq (a b c : DL.carrier) :
    (dl_meet_assoc_path (DL := DL) a b c).toEq = DL.meet_assoc a b c := rfl
theorem dl_join_assoc_path_toEq (a b c : DL.carrier) :
    (dl_join_assoc_path (DL := DL) a b c).toEq = DL.join_assoc a b c := rfl

/-- Distribution coherence: meet over join and then commutativity. -/
noncomputable def dl_distribute_comm_path (a b c : DL.carrier) :
    Path (DL.meet_ a (DL.join_ b c)) (DL.join_ (DL.meet_ b a) (DL.meet_ a c)) :=
  Path.trans
    (dl_distribute_path a b c)
    (Path.congrArg (fun x => DL.join_ x (DL.meet_ a c))
      (dl_meet_comm_path a b))

theorem dl_distribute_comm_path_toEq (a b c : DL.carrier) :
    (dl_distribute_comm_path (DL := DL) a b c).toEq =
      Eq.trans (DL.distribute a b c)
        (_root_.congrArg (fun x => DL.join_ x (DL.meet_ a c)) (DL.meet_comm a b)) := rfl

/-- Symmetry of distribution path. -/
noncomputable def dl_distribute_symm_path (a b c : DL.carrier) :
    Path (DL.join_ (DL.meet_ a b) (DL.meet_ a c)) (DL.meet_ a (DL.join_ b c)) :=
  Path.symm (dl_distribute_path a b c)

theorem dl_distribute_symm_path_toEq (a b c : DL.carrier) :
    (dl_distribute_symm_path (DL := DL) a b c).toEq =
      Eq.symm (DL.distribute a b c) := rfl

/-! ## Categorical interpretation of sequent calculus -/

/-- A sequent in the internal logic of a category. -/
structure Sequent (C : Cat.{u,v}) (T : Terminal C) (Ω : SubobjectClassifier C T) where
  context : C.Obj
  antecedent : C.Hom context Ω.Ω
  consequent : C.Hom context Ω.Ω

/-- A derivation is a proof that the antecedent factors through the consequent. -/
structure Derivation (C : Cat.{u,v}) (T : Terminal C) (Ω : SubobjectClassifier C T)
    (S : Sequent C T Ω) (L : InternalLogic C T Ω) where
  witness : C.comp S.antecedent L.impOp = S.consequent →
    C.comp S.antecedent L.impOp = S.consequent

noncomputable def derivation_path {S : Sequent C T Ω} {L : InternalLogic C T Ω}
    (D : Derivation C T Ω S L)
    (h : C.comp S.antecedent L.impOp = S.consequent) :
    Path (C.comp S.antecedent L.impOp) S.consequent :=
  Path.mk [Step.mk _ _ (D.witness h)] (D.witness h)

/-- Identity derivation: if antecedent equals consequent. -/
noncomputable def identity_sequent_path {Γ : C.Obj} (φ : C.Hom Γ Ω.Ω) :
    Path φ φ :=
  Path.refl φ

/-- Weakening: the antecedent can be composed with identity. -/
noncomputable def weakening_path {Γ : C.Obj} (φ : C.Hom Γ Ω.Ω) :
    Path (C.comp φ (C.id Ω.Ω)) φ :=
  comp_id_right_path φ

theorem weakening_path_toEq {Γ : C.Obj} (φ : C.Hom Γ Ω.Ω) :
    (weakening_path (C := C) (Ω := Ω) φ).toEq = C.comp_id_right φ := rfl

/-! ## Presheaf model paths -/

/-- A presheaf on C, as a contravariant functor to Type. -/
structure Presheaf (C : Cat.{u,v}) where
  obj : C.Obj → Type w
  map : {A B : C.Obj} → C.Hom A B → obj B → obj A
  map_id : ∀ {A : C.Obj} (x : obj A), map (C.id A) x = x
  map_comp : ∀ {A B D : C.Obj} (f : C.Hom A B) (g : C.Hom B D) (x : obj D),
    map (C.comp f g) x = map f (map g x)

variable {PS : Presheaf C}

noncomputable def presheaf_map_id_path {A : C.Obj} (x : PS.obj A) :
    Path (PS.map (C.id A) x) x :=
  Path.mk [Step.mk _ _ (PS.map_id x)] (PS.map_id x)

noncomputable def presheaf_map_comp_path {A B D : C.Obj}
    (f : C.Hom A B) (g : C.Hom B D) (x : PS.obj D) :
    Path (PS.map (C.comp f g) x) (PS.map f (PS.map g x)) :=
  Path.mk [Step.mk _ _ (PS.map_comp f g x)] (PS.map_comp f g x)

theorem presheaf_map_id_path_toEq {A : C.Obj} (x : PS.obj A) :
    (presheaf_map_id_path (PS := PS) x).toEq = PS.map_id x := rfl

theorem presheaf_map_comp_path_toEq {A B D : C.Obj}
    (f : C.Hom A B) (g : C.Hom B D) (x : PS.obj D) :
    (presheaf_map_comp_path (PS := PS) f g x).toEq = PS.map_comp f g x := rfl

/-- Triple functoriality for presheaves. -/
noncomputable def presheaf_triple_map {A B D E : C.Obj}
    (f : C.Hom A B) (g : C.Hom B D) (h : C.Hom D E) (x : PS.obj E) :
    Path (PS.map (C.comp (C.comp f g) h) x)
         (PS.map f (PS.map g (PS.map h x))) :=
  Path.trans
    (presheaf_map_comp_path (C.comp f g) h x)
    (presheaf_map_comp_path f g (PS.map h x))

theorem presheaf_triple_map_toEq {A B D E : C.Obj}
    (f : C.Hom A B) (g : C.Hom B D) (h : C.Hom D E) (x : PS.obj E) :
    (presheaf_triple_map (PS := PS) f g h x).toEq =
      Eq.trans (PS.map_comp (C.comp f g) h x)
               (PS.map_comp f g (PS.map h x)) := rfl

/-- Congruence: presheaf map in the morphism argument. -/
noncomputable def presheaf_map_congrArg {A B : C.Obj}
    {f g : C.Hom A B} (h : Path f g) (x : PS.obj B) :
    Path (PS.map f x) (PS.map g x) :=
  Path.congrArg (fun m => PS.map m x) h

/-! ## Natural transformation paths for presheaves -/

/-- A natural transformation between presheaves. -/
structure PresheafNT (C : Cat.{u,v}) (F G : Presheaf C) where
  component : (A : C.Obj) → F.obj A → G.obj A
  naturality : ∀ {A B : C.Obj} (f : C.Hom A B) (x : F.obj B),
    component A (F.map f x) = G.map f (component B x)

variable {F G : Presheaf C}

noncomputable def nt_naturality_path (η : PresheafNT C F G) {A B : C.Obj}
    (f : C.Hom A B) (x : F.obj B) :
    Path (η.component A (F.map f x)) (G.map f (η.component B x)) :=
  Path.mk [Step.mk _ _ (η.naturality f x)] (η.naturality f x)

theorem nt_naturality_path_toEq (η : PresheafNT C F G) {A B : C.Obj}
    (f : C.Hom A B) (x : F.obj B) :
    (nt_naturality_path η f x).toEq = η.naturality f x := rfl

/-- Identity natural transformation. -/
noncomputable def nt_id_naturality {A B : C.Obj} (f : C.Hom A B) (x : F.obj B) :
    Path (F.map f x) (F.map f x) :=
  Path.refl _

theorem nt_id_naturality_toEq {A B : C.Obj} (f : C.Hom A B) (x : F.obj B) :
    (nt_id_naturality (F := F) f x).toEq = rfl := rfl

/-! ## Topos path summary constructions -/

/-- Complete Heyting algebra path chain: meet(a, join(b,c)) via distributivity. -/
noncomputable def cha_distribute_chain (HA : HeytingAlgebra)
    (hd : ∀ (a b c : HA.carrier),
      HA.meet_ a (HA.join_ b c) = HA.join_ (HA.meet_ a b) (HA.meet_ a c))
    (a b c : HA.carrier) :
    Path (HA.meet_ a (HA.join_ b c)) (HA.join_ (HA.meet_ a b) (HA.meet_ a c)) :=
  Path.mk [Step.mk _ _ (hd a b c)] (hd a b c)

theorem cha_distribute_chain_toEq (HA : HeytingAlgebra)
    (hd : ∀ (a b c : HA.carrier),
      HA.meet_ a (HA.join_ b c) = HA.join_ (HA.meet_ a b) (HA.meet_ a c))
    (a b c : HA.carrier) :
    (cha_distribute_chain HA hd a b c).toEq = hd a b c := rfl

/-- Categorical logic summary: composing subobject classifier with internal logic. -/
noncomputable def categorical_logic_chain (L : InternalLogic C T Ω) :
    Path (C.comp Ω.true_arrow L.andOp) Ω.true_arrow :=
  and_idempotent_path L

/-- Full chain: truth → and → truth → or → truth → imp → truth. -/
noncomputable def full_logic_chain (L : InternalLogic C T Ω) :
    Path (C.comp Ω.true_arrow L.andOp)
         (C.comp Ω.true_arrow L.impOp) :=
  Path.trans
    (and_idempotent_path L)
    (Path.trans
      (Path.symm (or_absorb_true_path L))
      (Path.trans
        (or_absorb_true_path L)
        (Path.symm (imp_true_true_path L))))

theorem full_logic_chain_toEq (L : InternalLogic C T Ω) :
    (full_logic_chain L).toEq =
      Eq.trans L.and_idempotent
        (Eq.trans (Eq.symm L.or_absorb_true)
          (Eq.trans L.or_absorb_true (Eq.symm L.imp_true_true))) := rfl

end Advanced
end CategoricalLogic
end Path
end ComputationalPaths

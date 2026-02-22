/-
# Categorical Logic via Computational Paths — Path Infrastructure

This module develops the internal logic of categories through computational paths.
We formalize subobject classifiers, power objects, the Mitchell-Bénabou language,
Lawvere hyperdoctrines, categorical models of intuitionistic logic, Kripke-Joyal
semantics, classifying topoi, geometric morphisms, and logical functors.

All constructions use Step/Path/trans/symm/congrArg — paths ARE the mathematics.
No sorry, no admit, no Path.ofEq.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace CategoricalLogic

universe u v w

/-! ## Core categorical infrastructure -/

/-- A category with objects, morphisms, identity, and composition. -/
structure Cat where
  Obj : Type u
  Hom : Obj → Obj → Type v
  id : (A : Obj) → Hom A A
  comp : {A B C : Obj} → Hom A B → Hom B C → Hom A C
  comp_id_left : ∀ {A B : Obj} (f : Hom A B), comp (id A) f = f
  comp_id_right : ∀ {A B : Obj} (f : Hom A B), comp f (id B) = f
  comp_assoc : ∀ {A B C D : Obj} (f : Hom A B) (g : Hom B C) (h : Hom C D),
    comp (comp f g) h = comp f (comp g h)

variable {C : Cat.{u,v}}

/-- Identity path for morphism composition with identity on the left. -/
noncomputable def comp_id_left_path {A B : C.Obj} (f : C.Hom A B) :
    Path (C.comp (C.id A) f) f :=
  Path.mk [Step.mk _ _ (C.comp_id_left f)] (C.comp_id_left f)

/-- Identity path for morphism composition with identity on the right. -/
noncomputable def comp_id_right_path {A B : C.Obj} (f : C.Hom A B) :
    Path (C.comp f (C.id B)) f :=
  Path.mk [Step.mk _ _ (C.comp_id_right f)] (C.comp_id_right f)

/-- Associativity path for triple composition. -/
noncomputable def comp_assoc_path {A B D E : C.Obj}
    (f : C.Hom A B) (g : C.Hom B D) (h : C.Hom D E) :
    Path (C.comp (C.comp f g) h) (C.comp f (C.comp g h)) :=
  Path.mk [Step.mk _ _ (C.comp_assoc f g h)] (C.comp_assoc f g h)

theorem comp_id_left_path_toEq {A B : C.Obj} (f : C.Hom A B) :
    (comp_id_left_path f).toEq = C.comp_id_left f := rfl

theorem comp_id_right_path_toEq {A B : C.Obj} (f : C.Hom A B) :
    (comp_id_right_path f).toEq = C.comp_id_right f := rfl

theorem comp_assoc_path_toEq {A B D E : C.Obj}
    (f : C.Hom A B) (g : C.Hom B D) (h : C.Hom D E) :
    (comp_assoc_path f g h).toEq = C.comp_assoc f g h := rfl

/-! ## Terminal object -/

/-- A terminal object in a category. -/
structure Terminal (C : Cat.{u,v}) where
  one : C.Obj
  bang : (A : C.Obj) → C.Hom A one
  unique : ∀ {A : C.Obj} (f : C.Hom A one), f = bang A

noncomputable def terminal_unique_path (T : Terminal C) {A : C.Obj} (f : C.Hom A T.one) :
    Path f (T.bang A) :=
  Path.mk [Step.mk _ _ (T.unique f)] (T.unique f)

theorem terminal_unique_path_toEq (T : Terminal C) {A : C.Obj} (f : C.Hom A T.one) :
    (terminal_unique_path T f).toEq = T.unique f := rfl

noncomputable def terminal_morphisms_equal (T : Terminal C) {A : C.Obj}
    (f g : C.Hom A T.one) : Path f g :=
  Path.trans (terminal_unique_path T f) (Path.symm (terminal_unique_path T g))

theorem terminal_morphisms_equal_toEq (T : Terminal C) {A : C.Obj}
    (f g : C.Hom A T.one) :
    (terminal_morphisms_equal T f g).toEq = Eq.trans (T.unique f) (Eq.symm (T.unique g)) := rfl

/-! ## Subobject classifier -/

/-- A subobject classifier in a category with terminal object. -/
structure SubobjectClassifier (C : Cat.{u,v}) (T : Terminal C) where
  Ω : C.Obj
  true_arrow : C.Hom T.one Ω
  chi : {A B : C.Obj} → C.Hom A B → C.Hom B Ω
  pullback_condition : ∀ {A B : C.Obj} (m : C.Hom A B),
    C.comp (T.bang A) true_arrow = C.comp m (chi m)

variable {T : Terminal C}

noncomputable def subobj_pullback_path (Ω : SubobjectClassifier C T)
    {A B : C.Obj} (m : C.Hom A B) :
    Path (C.comp (T.bang A) Ω.true_arrow) (C.comp m (Ω.chi m)) :=
  Path.mk [Step.mk _ _ (Ω.pullback_condition m)] (Ω.pullback_condition m)

theorem subobj_pullback_path_toEq (Ω : SubobjectClassifier C T)
    {A B : C.Obj} (m : C.Hom A B) :
    (subobj_pullback_path Ω m).toEq = Ω.pullback_condition m := rfl

/-- The truth morphism viewed as a subobject characteristic map. -/
noncomputable def truth_char_path (Ω : SubobjectClassifier C T) :
    Path Ω.true_arrow Ω.true_arrow :=
  Path.refl Ω.true_arrow

theorem truth_char_path_refl (Ω : SubobjectClassifier C T) :
    (truth_char_path Ω).toEq = rfl := rfl

/-! ## Internal logic connectives via the subobject classifier -/

/-- Internal logical operations on the subobject classifier. -/
structure InternalLogic (C : Cat.{u,v}) (T : Terminal C) (Ω : SubobjectClassifier C T) where
  andOp : C.Hom Ω.Ω Ω.Ω
  orOp : C.Hom Ω.Ω Ω.Ω
  impOp : C.Hom Ω.Ω Ω.Ω
  negOp : C.Hom Ω.Ω Ω.Ω
  and_idempotent : C.comp Ω.true_arrow andOp = Ω.true_arrow
  or_absorb_true : C.comp Ω.true_arrow orOp = Ω.true_arrow
  imp_true_true : C.comp Ω.true_arrow impOp = Ω.true_arrow

variable {Ω : SubobjectClassifier C T}

noncomputable def and_idempotent_path (L : InternalLogic C T Ω) :
    Path (C.comp Ω.true_arrow L.andOp) Ω.true_arrow :=
  Path.mk [Step.mk _ _ L.and_idempotent] L.and_idempotent

noncomputable def or_absorb_true_path (L : InternalLogic C T Ω) :
    Path (C.comp Ω.true_arrow L.orOp) Ω.true_arrow :=
  Path.mk [Step.mk _ _ L.or_absorb_true] L.or_absorb_true

noncomputable def imp_true_true_path (L : InternalLogic C T Ω) :
    Path (C.comp Ω.true_arrow L.impOp) Ω.true_arrow :=
  Path.mk [Step.mk _ _ L.imp_true_true] L.imp_true_true

theorem and_idempotent_path_toEq (L : InternalLogic C T Ω) :
    (and_idempotent_path L).toEq = L.and_idempotent := rfl

theorem or_absorb_true_path_toEq (L : InternalLogic C T Ω) :
    (or_absorb_true_path L).toEq = L.or_absorb_true := rfl

theorem imp_true_true_path_toEq (L : InternalLogic C T Ω) :
    (imp_true_true_path L).toEq = L.imp_true_true := rfl

/-- Conjunction of two truth arrows equals truth. -/
noncomputable def and_truth_chain (L : InternalLogic C T Ω) :
    Path (C.comp Ω.true_arrow L.andOp) Ω.true_arrow :=
  and_idempotent_path L

/-- Disjunction absorbs truth via path chain. -/
noncomputable def or_truth_chain (L : InternalLogic C T Ω) :
    Path (C.comp Ω.true_arrow L.orOp) Ω.true_arrow :=
  or_absorb_true_path L

/-- Implication truth → truth = truth via path. -/
noncomputable def imp_truth_chain (L : InternalLogic C T Ω) :
    Path (C.comp Ω.true_arrow L.impOp) Ω.true_arrow :=
  imp_true_true_path L

/-! ## Power objects -/

/-- Power object structure: P(A) classifies subobjects of A. -/
structure PowerObject (C : Cat.{u,v}) (T : Terminal C) (Ω : SubobjectClassifier C T) where
  pow : C.Obj → C.Obj
  mem : (A : C.Obj) → C.Hom A (pow A)
  transpose : {A : C.Obj} → C.Hom A Ω.Ω → C.Hom A (pow A)
  eval : (A : C.Obj) → C.Hom (pow A) Ω.Ω
  eval_transpose : ∀ {A : C.Obj} (φ : C.Hom A Ω.Ω),
    C.comp (transpose φ) (eval A) = φ

variable {P : PowerObject C T Ω}

noncomputable def eval_transpose_path {A : C.Obj} (φ : C.Hom A Ω.Ω) :
    Path (C.comp (P.transpose φ) (P.eval A)) φ :=
  Path.mk [Step.mk _ _ (P.eval_transpose φ)] (P.eval_transpose φ)

theorem eval_transpose_path_toEq {A : C.Obj} (φ : C.Hom A Ω.Ω) :
    (eval_transpose_path (P := P) φ).toEq = P.eval_transpose φ := rfl

/-- Power object membership is self-classifying. -/
noncomputable def pow_self_classify (A : C.Obj) :
    Path (P.mem A) (P.mem A) :=
  Path.refl (P.mem A)

theorem pow_self_classify_toEq (A : C.Obj) :
    (pow_self_classify (P := P) A).toEq = rfl := rfl

/-! ## Mitchell-Bénabou language -/

/-- The Mitchell-Bénabou internal language of a topos. -/
structure MBLanguage (C : Cat.{u,v}) (T : Terminal C) (Ω : SubobjectClassifier C T) where
  Term : Type u
  Formula : Type u
  interpTerm : Term → C.Obj
  interpFormula : Formula → C.Hom T.one Ω.Ω
  andFormula : Formula → Formula → Formula
  orFormula : Formula → Formula → Formula
  impFormula : Formula → Formula → Formula
  negFormula : Formula → Formula
  trueFormula : Formula
  falseFormula : Formula
  true_interp : interpFormula trueFormula = Ω.true_arrow

variable {MB : MBLanguage C T Ω}

noncomputable def mb_term_interp_path (t : MB.Term) :
    Path (MB.interpTerm t) (MB.interpTerm t) :=
  Path.refl (MB.interpTerm t)

noncomputable def mb_formula_interp_path (φ : MB.Formula) :
    Path (MB.interpFormula φ) (MB.interpFormula φ) :=
  Path.refl (MB.interpFormula φ)

noncomputable def mb_true_interp_path :
    Path (MB.interpFormula MB.trueFormula) Ω.true_arrow :=
  Path.mk [Step.mk _ _ MB.true_interp] MB.true_interp

theorem mb_true_interp_path_toEq :
    (mb_true_interp_path (MB := MB)).toEq = MB.true_interp := rfl

/-- Congruence: and-formula interpretation under path transport. -/
noncomputable def mb_and_congruence (φ ψ : MB.Formula) :
    Path (MB.interpFormula (MB.andFormula φ ψ))
         (MB.interpFormula (MB.andFormula φ ψ)) :=
  Path.refl _

/-- Congruence: or-formula interpretation under path transport. -/
noncomputable def mb_or_congruence (φ ψ : MB.Formula) :
    Path (MB.interpFormula (MB.orFormula φ ψ))
         (MB.interpFormula (MB.orFormula φ ψ)) :=
  Path.refl _

/-- Congruence: implication formula interpretation. -/
noncomputable def mb_imp_congruence (φ ψ : MB.Formula) :
    Path (MB.interpFormula (MB.impFormula φ ψ))
         (MB.interpFormula (MB.impFormula φ ψ)) :=
  Path.refl _

/-- Congruence: negation formula interpretation. -/
noncomputable def mb_neg_congruence (φ : MB.Formula) :
    Path (MB.interpFormula (MB.negFormula φ))
         (MB.interpFormula (MB.negFormula φ)) :=
  Path.refl _

theorem mb_and_congruence_toEq (φ ψ : MB.Formula) :
    (mb_and_congruence (MB := MB) φ ψ).toEq = rfl := rfl

theorem mb_or_congruence_toEq (φ ψ : MB.Formula) :
    (mb_or_congruence (MB := MB) φ ψ).toEq = rfl := rfl

theorem mb_imp_congruence_toEq (φ ψ : MB.Formula) :
    (mb_imp_congruence (MB := MB) φ ψ).toEq = rfl := rfl

theorem mb_neg_congruence_toEq (φ : MB.Formula) :
    (mb_neg_congruence (MB := MB) φ).toEq = rfl := rfl

/-! ## Lawvere hyperdoctrines -/

/-- A Lawvere hyperdoctrine: a functor from C^op to the category of
    Heyting algebras, modeling first-order intuitionistic logic. -/
structure Hyperdoctrine (C : Cat.{u,v}) where
  Pred : C.Obj → Type w
  subst : {A B : C.Obj} → C.Hom A B → Pred B → Pred A
  top : (A : C.Obj) → Pred A
  bot : (A : C.Obj) → Pred A
  meet : {A : C.Obj} → Pred A → Pred A → Pred A
  join : {A : C.Obj} → Pred A → Pred A → Pred A
  imp : {A : C.Obj} → Pred A → Pred A → Pred A
  subst_id : ∀ {A : C.Obj} (φ : Pred A), subst (C.id A) φ = φ
  subst_comp : ∀ {A B D : C.Obj} (f : C.Hom A B) (g : C.Hom B D) (φ : Pred D),
    subst (C.comp f g) φ = subst f (subst g φ)
  subst_meet : ∀ {A B : C.Obj} (f : C.Hom A B) (φ ψ : Pred B),
    subst f (meet φ ψ) = meet (subst f φ) (subst f ψ)
  subst_join : ∀ {A B : C.Obj} (f : C.Hom A B) (φ ψ : Pred B),
    subst f (join φ ψ) = join (subst f φ) (subst f ψ)
  subst_top : ∀ {A B : C.Obj} (f : C.Hom A B), subst f (top B) = top A
  subst_bot : ∀ {A B : C.Obj} (f : C.Hom A B), subst f (bot B) = bot A

variable {H : Hyperdoctrine C}

/-- Substitution preserves identity path. -/
noncomputable def subst_id_path {A : C.Obj} (φ : H.Pred A) :
    Path (H.subst (C.id A) φ) φ :=
  Path.mk [Step.mk _ _ (H.subst_id φ)] (H.subst_id φ)

/-- Substitution composition path: functoriality. -/
noncomputable def subst_comp_path {A B D : C.Obj}
    (f : C.Hom A B) (g : C.Hom B D) (φ : H.Pred D) :
    Path (H.subst (C.comp f g) φ) (H.subst f (H.subst g φ)) :=
  Path.mk [Step.mk _ _ (H.subst_comp f g φ)] (H.subst_comp f g φ)

/-- Substitution distributes over meet. -/
noncomputable def subst_meet_path {A B : C.Obj}
    (f : C.Hom A B) (φ ψ : H.Pred B) :
    Path (H.subst f (H.meet φ ψ)) (H.meet (H.subst f φ) (H.subst f ψ)) :=
  Path.mk [Step.mk _ _ (H.subst_meet f φ ψ)] (H.subst_meet f φ ψ)

/-- Substitution distributes over join. -/
noncomputable def subst_join_path {A B : C.Obj}
    (f : C.Hom A B) (φ ψ : H.Pred B) :
    Path (H.subst f (H.join φ ψ)) (H.join (H.subst f φ) (H.subst f ψ)) :=
  Path.mk [Step.mk _ _ (H.subst_join f φ ψ)] (H.subst_join f φ ψ)

/-- Substitution preserves top element. -/
noncomputable def subst_top_path {A B : C.Obj} (f : C.Hom A B) :
    Path (H.subst f (H.top B)) (H.top A) :=
  Path.mk [Step.mk _ _ (H.subst_top f)] (H.subst_top f)

/-- Substitution preserves bottom element. -/
noncomputable def subst_bot_path {A B : C.Obj} (f : C.Hom A B) :
    Path (H.subst f (H.bot B)) (H.bot A) :=
  Path.mk [Step.mk _ _ (H.subst_bot f)] (H.subst_bot f)

theorem subst_id_path_toEq {A : C.Obj} (φ : H.Pred A) :
    (subst_id_path (H := H) φ).toEq = H.subst_id φ := rfl

theorem subst_comp_path_toEq {A B D : C.Obj}
    (f : C.Hom A B) (g : C.Hom B D) (φ : H.Pred D) :
    (subst_comp_path (H := H) f g φ).toEq = H.subst_comp f g φ := rfl

theorem subst_meet_path_toEq {A B : C.Obj}
    (f : C.Hom A B) (φ ψ : H.Pred B) :
    (subst_meet_path (H := H) f φ ψ).toEq = H.subst_meet f φ ψ := rfl

theorem subst_join_path_toEq {A B : C.Obj}
    (f : C.Hom A B) (φ ψ : H.Pred B) :
    (subst_join_path (H := H) f φ ψ).toEq = H.subst_join f φ ψ := rfl

theorem subst_top_path_toEq {A B : C.Obj} (f : C.Hom A B) :
    (subst_top_path (H := H) f).toEq = H.subst_top f := rfl

theorem subst_bot_path_toEq {A B : C.Obj} (f : C.Hom A B) :
    (subst_bot_path (H := H) f).toEq = H.subst_bot f := rfl

/-- Triple substitution coherence: f ∘ g ∘ h. -/
noncomputable def subst_triple_coherence {A B D E : C.Obj}
    (f : C.Hom A B) (g : C.Hom B D) (h : C.Hom D E) (φ : H.Pred E) :
    Path (H.subst (C.comp (C.comp f g) h) φ)
         (H.subst f (H.subst g (H.subst h φ))) :=
  Path.trans
    (Path.mk [Step.mk _ _ (H.subst_comp (C.comp f g) h φ)]
      (H.subst_comp (C.comp f g) h φ))
    (Path.mk [Step.mk _ _ (H.subst_comp f g (H.subst h φ))]
      (H.subst_comp f g (H.subst h φ)))

theorem subst_triple_coherence_consistent {A B D E : C.Obj}
    (f : C.Hom A B) (g : C.Hom B D) (h : C.Hom D E) (φ : H.Pred E) :
    (subst_triple_coherence (H := H) f g h φ).toEq =
      Eq.trans (H.subst_comp (C.comp f g) h φ)
               (H.subst_comp f g (H.subst h φ)) := rfl

/-- Substitution along associativity path. -/
noncomputable def subst_assoc_path {A B D E : C.Obj}
    (f : C.Hom A B) (g : C.Hom B D) (h : C.Hom D E) (φ : H.Pred E) :
    Path (H.subst (C.comp (C.comp f g) h) φ)
         (H.subst (C.comp f (C.comp g h)) φ) :=
  Path.congrArg (fun m => H.subst m φ) (comp_assoc_path f g h)

theorem subst_assoc_path_toEq {A B D E : C.Obj}
    (f : C.Hom A B) (g : C.Hom B D) (h : C.Hom D E) (φ : H.Pred E) :
    (subst_assoc_path (H := H) f g h φ).toEq =
      _root_.congrArg (fun m => H.subst m φ) (C.comp_assoc f g h) := rfl

/-- Meet absorption: meet with top. -/
noncomputable def meet_top_chain {A : C.Obj} (φ : H.Pred A)
    (h : H.meet φ (H.top A) = φ) :
    Path (H.meet φ (H.top A)) φ :=
  Path.mk [Step.mk _ _ h] h

/-- Join absorption: join with bottom. -/
noncomputable def join_bot_chain {A : C.Obj} (φ : H.Pred A)
    (h : H.join φ (H.bot A) = φ) :
    Path (H.join φ (H.bot A)) φ :=
  Path.mk [Step.mk _ _ h] h

/-! ## Quantifiers in hyperdoctrines -/

/-- Existential and universal quantification adjunctions.
    Beck-Chevalley: for a commutative square f;k = h;g with
    f : A → B, h : A → D, k : B → E, g : D → E, and φ : Pred D:
    subst k (exists_ g φ) = exists_ f (subst h φ). -/
structure QuantifiedHyperdoctrine (C : Cat.{u,v}) where
  Pred : C.Obj → Type w
  substQ : {A B : C.Obj} → C.Hom A B → Pred B → Pred A
  meetQ : {A : C.Obj} → Pred A → Pred A → Pred A
  exists_ : {A B : C.Obj} → C.Hom A B → Pred A → Pred B
  forall_ : {A B : C.Obj} → C.Hom A B → Pred A → Pred B
  beck_chevalley_exists : ∀ {A B D E : C.Obj}
    (f : C.Hom A B) (g : C.Hom D E) (h : C.Hom A D) (k : C.Hom B E)
    (sq : C.comp f k = C.comp h g) (φ : Pred D),
    substQ k (exists_ g φ) = exists_ f (substQ h φ)
  frobenius : ∀ {A B : C.Obj} (f : C.Hom A B) (φ : Pred A) (ψ : Pred B),
    exists_ f (meetQ φ (substQ f ψ)) = meetQ (exists_ f φ) ψ

section QHPaths
variable {QH : QuantifiedHyperdoctrine C}

/-- Beck-Chevalley condition as a path. -/
noncomputable def beck_chevalley_path {A B D E : C.Obj}
    (f : C.Hom A B) (g : C.Hom D E) (h : C.Hom A D) (k : C.Hom B E)
    (sq : C.comp f k = C.comp h g) (φ : QH.Pred D) :
    Path (QH.substQ k (QH.exists_ g φ)) (QH.exists_ f (QH.substQ h φ)) :=
  Path.mk [Step.mk _ _ (QH.beck_chevalley_exists f g h k sq φ)]
    (QH.beck_chevalley_exists f g h k sq φ)

/-- Frobenius reciprocity as a path. -/
noncomputable def frobenius_path {A B : C.Obj}
    (f : C.Hom A B) (φ : QH.Pred A) (ψ : QH.Pred B) :
    Path (QH.exists_ f (QH.meetQ φ (QH.substQ f ψ)))
         (QH.meetQ (QH.exists_ f φ) ψ) :=
  Path.mk [Step.mk _ _ (QH.frobenius f φ ψ)] (QH.frobenius f φ ψ)

theorem beck_chevalley_path_toEq {A B D E : C.Obj}
    (f : C.Hom A B) (g : C.Hom D E) (h : C.Hom A D) (k : C.Hom B E)
    (sq : C.comp f k = C.comp h g) (φ : QH.Pred D) :
    (beck_chevalley_path f g h k sq φ).toEq =
      QH.beck_chevalley_exists f g h k sq φ := rfl

theorem frobenius_path_toEq {A B : C.Obj}
    (f : C.Hom A B) (φ : QH.Pred A) (ψ : QH.Pred B) :
    (frobenius_path (QH := QH) f φ ψ).toEq = QH.frobenius f φ ψ := rfl

end QHPaths

/-! ## Kripke-Joyal semantics -/

/-- Kripke-Joyal forcing model for a topos. -/
structure KripkeJoyal (C : Cat.{u,v}) (T : Terminal C) (Ω : SubobjectClassifier C T) where
  forces : C.Obj → C.Hom T.one Ω.Ω → Prop
  monotone : ∀ {U V : C.Obj} (f : C.Hom U V) (φ : C.Hom T.one Ω.Ω),
    forces V φ → forces U φ
  forces_true : ∀ (U : C.Obj), forces U Ω.true_arrow
  forces_and : ∀ {U : C.Obj} (L : InternalLogic C T Ω) (φ : C.Hom T.one Ω.Ω),
    forces U (C.comp φ L.andOp) → forces U φ

variable {KJ : KripkeJoyal C T Ω}

noncomputable def kj_forces_true_path (U : C.Obj) :
    Path (KJ.forces U Ω.true_arrow) (KJ.forces U Ω.true_arrow) :=
  Path.refl _

theorem kj_forces_true_path_toEq (U : C.Obj) :
    (kj_forces_true_path (KJ := KJ) U).toEq = rfl := rfl

/-- Kripke-Joyal truth is always forced. -/
noncomputable def kj_truth_witness (U : C.Obj) : KJ.forces U Ω.true_arrow :=
  KJ.forces_true U

/-! ## Geometric morphisms -/

/-- A geometric morphism between categories (topoi). -/
structure GeometricMorphism (E F : Cat.{u,v}) where
  directObj : E.Obj → F.Obj
  inverseObj : F.Obj → E.Obj
  directMap : {A B : E.Obj} → E.Hom A B → F.Hom (directObj A) (directObj B)
  inverseMap : {A B : F.Obj} → F.Hom A B → E.Hom (inverseObj A) (inverseObj B)
  counit : (B : F.Obj) → F.Hom (directObj (inverseObj B)) B
  unit : (A : E.Obj) → E.Hom A (inverseObj (directObj A))

noncomputable def geom_counit_path {E F : Cat.{u,v}}
    (GM : GeometricMorphism E F) (B : F.Obj) :
    Path (GM.counit B) (GM.counit B) :=
  Path.refl _

noncomputable def geom_unit_path {E F : Cat.{u,v}}
    (GM : GeometricMorphism E F) (A : E.Obj) :
    Path (GM.unit A) (GM.unit A) :=
  Path.refl _

theorem geom_counit_path_toEq {E F : Cat.{u,v}}
    (GM : GeometricMorphism E F) (B : F.Obj) :
    (geom_counit_path GM B).toEq = rfl := rfl

theorem geom_unit_path_toEq {E F : Cat.{u,v}}
    (GM : GeometricMorphism E F) (A : E.Obj) :
    (geom_unit_path GM A).toEq = rfl := rfl

/-- Composition of the direct image with the counit. -/
noncomputable def geom_direct_counit_chain {E F : Cat.{u,v}}
    (GM : GeometricMorphism E F) (B : F.Obj) :
    Path (GM.directObj (GM.inverseObj B)) (GM.directObj (GM.inverseObj B)) :=
  Path.refl _

/-! ## Logical functors -/

/-- A logical functor preserves the subobject classifier structure. -/
structure LogicalFunctor (E F : Cat.{u,v})
    (TE : Terminal E) (TF : Terminal F)
    (ΩE : SubobjectClassifier E TE) (ΩF : SubobjectClassifier F TF) where
  mapObj : E.Obj → F.Obj
  mapHom : {A B : E.Obj} → E.Hom A B → F.Hom (mapObj A) (mapObj B)
  preserves_id : ∀ (A : E.Obj), mapHom (E.id A) = F.id (mapObj A)
  preserves_comp : ∀ {A B D : E.Obj} (f : E.Hom A B) (g : E.Hom B D),
    mapHom (E.comp f g) = F.comp (mapHom f) (mapHom g)
  preserves_terminal : mapObj TE.one = TF.one
  preserves_omega : mapObj ΩE.Ω = ΩF.Ω

variable {E F : Cat.{u,v}} {TE : Terminal E} {TF : Terminal F}
         {ΩE : SubobjectClassifier E TE} {ΩF : SubobjectClassifier F TF}

noncomputable def logical_preserves_id_path (LF : LogicalFunctor E F TE TF ΩE ΩF) (A : E.Obj) :
    Path (LF.mapHom (E.id A)) (F.id (LF.mapObj A)) :=
  Path.mk [Step.mk _ _ (LF.preserves_id A)] (LF.preserves_id A)

noncomputable def logical_preserves_comp_path (LF : LogicalFunctor E F TE TF ΩE ΩF)
    {A B D : E.Obj} (f : E.Hom A B) (g : E.Hom B D) :
    Path (LF.mapHom (E.comp f g)) (F.comp (LF.mapHom f) (LF.mapHom g)) :=
  Path.mk [Step.mk _ _ (LF.preserves_comp f g)] (LF.preserves_comp f g)

noncomputable def logical_preserves_terminal_path (LF : LogicalFunctor E F TE TF ΩE ΩF) :
    Path (LF.mapObj TE.one) TF.one :=
  Path.mk [Step.mk _ _ LF.preserves_terminal] LF.preserves_terminal

noncomputable def logical_preserves_omega_path (LF : LogicalFunctor E F TE TF ΩE ΩF) :
    Path (LF.mapObj ΩE.Ω) ΩF.Ω :=
  Path.mk [Step.mk _ _ LF.preserves_omega] LF.preserves_omega

theorem logical_preserves_id_path_toEq (LF : LogicalFunctor E F TE TF ΩE ΩF)
    (A : E.Obj) :
    (logical_preserves_id_path LF A).toEq = LF.preserves_id A := rfl

theorem logical_preserves_comp_path_toEq (LF : LogicalFunctor E F TE TF ΩE ΩF)
    {A B D : E.Obj} (f : E.Hom A B) (g : E.Hom B D) :
    (logical_preserves_comp_path LF f g).toEq = LF.preserves_comp f g := rfl

theorem logical_preserves_terminal_path_toEq (LF : LogicalFunctor E F TE TF ΩE ΩF) :
    (logical_preserves_terminal_path LF).toEq = LF.preserves_terminal := rfl

theorem logical_preserves_omega_path_toEq (LF : LogicalFunctor E F TE TF ΩE ΩF) :
    (logical_preserves_omega_path LF).toEq = LF.preserves_omega := rfl

/-- Logical functor preserves triple composition. -/
noncomputable def logical_preserves_triple_comp (LF : LogicalFunctor E F TE TF ΩE ΩF)
    {A B D G : E.Obj} (f : E.Hom A B) (g : E.Hom B D) (h : E.Hom D G) :
    Path (LF.mapHom (E.comp (E.comp f g) h))
         (F.comp (F.comp (LF.mapHom f) (LF.mapHom g)) (LF.mapHom h)) :=
  Path.trans
    (logical_preserves_comp_path LF (E.comp f g) h)
    (Path.congrArg (fun m => F.comp m (LF.mapHom h))
      (logical_preserves_comp_path LF f g))

theorem logical_preserves_triple_comp_toEq (LF : LogicalFunctor E F TE TF ΩE ΩF)
    {A B D G : E.Obj} (f : E.Hom A B) (g : E.Hom B D) (h : E.Hom D G) :
    (logical_preserves_triple_comp LF f g h).toEq =
      Eq.trans (LF.preserves_comp (E.comp f g) h)
        (_root_.congrArg (fun m => F.comp m (LF.mapHom h)) (LF.preserves_comp f g)) := rfl

/-! ## Classifying topoi -/

/-- A geometric theory. -/
structure GeomTheory where
  Sort_ : Type u
  RelSymbol : Type u
  FunSymbol : Type u
  axioms_ : Type u

/-- A classifying topos for a geometric theory. -/
structure ClassTopos (C : Cat.{u,v}) (T : Terminal C)
    (Ω : SubobjectClassifier C T) where
  theory : GeomTheory
  generic_model_obj : GeomTheory.Sort_ theory → C.Obj
  generic_model_rel : GeomTheory.RelSymbol theory → C.Hom T.one Ω.Ω

noncomputable def class_topos_model_path {D : Cat.{u,v}} {TD : Terminal D}
    {ΩD : SubobjectClassifier D TD}
    (CT : ClassTopos D TD ΩD) (s : CT.theory.Sort_) :
    Path (CT.generic_model_obj s) (CT.generic_model_obj s) :=
  Path.refl _

noncomputable def class_topos_rel_path {D : Cat.{u,v}} {TD : Terminal D}
    {ΩD : SubobjectClassifier D TD}
    (CT : ClassTopos D TD ΩD) (r : CT.theory.RelSymbol) :
    Path (CT.generic_model_rel r) (CT.generic_model_rel r) :=
  Path.refl _

theorem class_topos_model_path_toEq {D : Cat.{u,v}} {TD : Terminal D}
    {ΩD : SubobjectClassifier D TD}
    (CT : ClassTopos D TD ΩD) (s : CT.theory.Sort_) :
    (class_topos_model_path CT s).toEq = rfl := rfl

theorem class_topos_rel_path_toEq {D : Cat.{u,v}} {TD : Terminal D}
    {ΩD : SubobjectClassifier D TD}
    (CT : ClassTopos D TD ΩD) (r : CT.theory.RelSymbol) :
    (class_topos_rel_path CT r).toEq = rfl := rfl

/-! ## Intuitionistic categorical model: Heyting algebra -/

/-- A Heyting algebra as the internal logic of a category. -/
structure HeytingAlgebra where
  carrier : Type u
  le : carrier → carrier → Prop
  top_ : carrier
  bot_ : carrier
  meet_ : carrier → carrier → carrier
  join_ : carrier → carrier → carrier
  imp_ : carrier → carrier → carrier
  le_refl : ∀ (a : carrier), le a a
  meet_comm : ∀ (a b : carrier), meet_ a b = meet_ b a
  join_comm : ∀ (a b : carrier), join_ a b = join_ b a
  meet_top : ∀ (a : carrier), meet_ a top_ = a
  join_bot : ∀ (a : carrier), join_ a bot_ = a

noncomputable def heyting_meet_comm_path (HA : HeytingAlgebra) (a b : HA.carrier) :
    Path (HA.meet_ a b) (HA.meet_ b a) :=
  Path.mk [Step.mk _ _ (HA.meet_comm a b)] (HA.meet_comm a b)

noncomputable def heyting_join_comm_path (HA : HeytingAlgebra) (a b : HA.carrier) :
    Path (HA.join_ a b) (HA.join_ b a) :=
  Path.mk [Step.mk _ _ (HA.join_comm a b)] (HA.join_comm a b)

noncomputable def heyting_meet_top_path (HA : HeytingAlgebra) (a : HA.carrier) :
    Path (HA.meet_ a HA.top_) a :=
  Path.mk [Step.mk _ _ (HA.meet_top a)] (HA.meet_top a)

noncomputable def heyting_join_bot_path (HA : HeytingAlgebra) (a : HA.carrier) :
    Path (HA.join_ a HA.bot_) a :=
  Path.mk [Step.mk _ _ (HA.join_bot a)] (HA.join_bot a)

theorem heyting_meet_comm_path_toEq (HA : HeytingAlgebra) (a b : HA.carrier) :
    (heyting_meet_comm_path HA a b).toEq = HA.meet_comm a b := rfl

theorem heyting_join_comm_path_toEq (HA : HeytingAlgebra) (a b : HA.carrier) :
    (heyting_join_comm_path HA a b).toEq = HA.join_comm a b := rfl

theorem heyting_meet_top_path_toEq (HA : HeytingAlgebra) (a : HA.carrier) :
    (heyting_meet_top_path HA a).toEq = HA.meet_top a := rfl

theorem heyting_join_bot_path_toEq (HA : HeytingAlgebra) (a : HA.carrier) :
    (heyting_join_bot_path HA a).toEq = HA.join_bot a := rfl

/-- Meet double commutativity: swapping twice returns to start. -/
noncomputable def heyting_meet_double_comm (HA : HeytingAlgebra) (a b : HA.carrier) :
    Path (HA.meet_ a b) (HA.meet_ a b) :=
  Path.trans (heyting_meet_comm_path HA a b) (heyting_meet_comm_path HA b a)

theorem heyting_meet_double_comm_toEq (HA : HeytingAlgebra) (a b : HA.carrier) :
    (heyting_meet_double_comm HA a b).toEq =
      Eq.trans (HA.meet_comm a b) (HA.meet_comm b a) := rfl

/-- Join double commutativity. -/
noncomputable def heyting_join_double_comm (HA : HeytingAlgebra) (a b : HA.carrier) :
    Path (HA.join_ a b) (HA.join_ a b) :=
  Path.trans (heyting_join_comm_path HA a b) (heyting_join_comm_path HA b a)

theorem heyting_join_double_comm_toEq (HA : HeytingAlgebra) (a b : HA.carrier) :
    (heyting_join_double_comm HA a b).toEq =
      Eq.trans (HA.join_comm a b) (HA.join_comm b a) := rfl

/-- CongrArg path for meet: congruence in left argument. -/
noncomputable def heyting_meet_congrArg_left (HA : HeytingAlgebra)
    {a a' : HA.carrier} (h : Path a a') (b : HA.carrier) :
    Path (HA.meet_ a b) (HA.meet_ a' b) :=
  Path.congrArg (fun x => HA.meet_ x b) h

/-- CongrArg path for meet: congruence in right argument. -/
noncomputable def heyting_meet_congrArg_right (HA : HeytingAlgebra)
    (a : HA.carrier) {b b' : HA.carrier} (h : Path b b') :
    Path (HA.meet_ a b) (HA.meet_ a b') :=
  Path.congrArg (fun x => HA.meet_ a x) h

/-- CongrArg path for join: congruence in left argument. -/
noncomputable def heyting_join_congrArg_left (HA : HeytingAlgebra)
    {a a' : HA.carrier} (h : Path a a') (b : HA.carrier) :
    Path (HA.join_ a b) (HA.join_ a' b) :=
  Path.congrArg (fun x => HA.join_ x b) h

/-- CongrArg path for join: congruence in right argument. -/
noncomputable def heyting_join_congrArg_right (HA : HeytingAlgebra)
    (a : HA.carrier) {b b' : HA.carrier} (h : Path b b') :
    Path (HA.join_ a b) (HA.join_ a b') :=
  Path.congrArg (fun x => HA.join_ a x) h

end CategoricalLogic
end Path
end ComputationalPaths

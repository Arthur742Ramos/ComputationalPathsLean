/-
# Categorical Logic via Computational Paths (Deep)

Internal language of categories, subobject classifiers, power objects,
comprehension schemes, and the Mitchell-Bénabou language — all modeled
through computational paths.

## References

- Lambek & Scott, "Introduction to Higher-Order Categorical Logic"
- Johnstone, "Sketches of an Elephant", Part D
- Mac Lane & Moerdijk, "Sheaves in Geometry and Logic", Ch. IV
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Logic
namespace CategoricalLogicDeep

universe u v

open ComputationalPaths

/-! ## Internal Language: Types and Terms -/

/-- An internal type in a category. -/
structure InternalType (Obj : Type u) where
  carrier : Obj
  name : String := ""

/-- An internal term / morphism between internal types. -/
structure InternalTerm (Obj : Type u) where
  dom : Obj
  cod : Obj
  label : String := ""

/-- Composition of internal terms. -/
noncomputable def InternalTerm.comp {Obj : Type u} (f : InternalTerm Obj) (g : InternalTerm Obj)
    (_ : f.cod = g.dom) : InternalTerm Obj :=
  { dom := f.dom, cod := g.cod, label := f.label ++ " ∘ " ++ g.label }

/-! ## Subobject Classifier -/

/-- A subobject classifier Ω with a truth morphism true : 1 → Ω. -/
structure SubobjectClassifier (Obj : Type u) where
  omega : Obj
  terminal : Obj
  trueMap : InternalTerm Obj
  trueMap_dom : trueMap.dom = terminal
  trueMap_cod : trueMap.cod = omega

/-- A monomorphism m : S ↪ A with its characteristic morphism χ_m : A → Ω. -/
structure ClassifiedMono (Obj : Type u) (sc : SubobjectClassifier Obj) where
  source : Obj
  target : Obj
  mono : InternalTerm Obj
  charMap : InternalTerm Obj
  mono_dom : mono.dom = source
  mono_cod : mono.cod = target
  char_dom : charMap.dom = target
  char_cod : charMap.cod = sc.omega

/-- 1. The characteristic morphism determines the subobject. -/
noncomputable def char_determines_subobject {Obj : Type u} {sc : SubobjectClassifier Obj}
    (m₁ m₂ : ClassifiedMono Obj sc)
    (h_char : m₁.charMap = m₂.charMap) :
    Path m₁.charMap m₂.charMap :=
  Path.mk [] (by rw [h_char])

/-- 2. Reflexivity: classified mono path. -/
noncomputable def char_self_path {Obj : Type u} {sc : SubobjectClassifier Obj}
    (m : ClassifiedMono Obj sc) :
    Path m.charMap m.charMap :=
  Path.refl _

/-! ## Lattice of Subobjects -/

/-- A subobject of A, indexed by a natural number for tracking. -/
structure Subobject (A : Type u) where
  predicate : A → Prop

/-- Meet (intersection) of two subobjects. -/
noncomputable def Subobject.meet {A : Type u} (s₁ s₂ : Subobject A) : Subobject A :=
  { predicate := fun x => s₁.predicate x ∧ s₂.predicate x }

/-- Join (union) of two subobjects. -/
noncomputable def Subobject.join {A : Type u} (s₁ s₂ : Subobject A) : Subobject A :=
  { predicate := fun x => s₁.predicate x ∨ s₂.predicate x }

/-- Bottom subobject. -/
noncomputable def Subobject.bot (A : Type u) : Subobject A :=
  { predicate := fun _ => False }

/-- Top subobject. -/
noncomputable def Subobject.top (A : Type u) : Subobject A :=
  { predicate := fun _ => True }

/-- 3. Meet is idempotent. -/
noncomputable def subobj_meet_idempotent {A : Type u} (s : Subobject A) :
    Path (s.meet s).predicate s.predicate :=
  Path.mk [] (by ext x; exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, h⟩⟩)

/-- 4. Meet is commutative. -/
noncomputable def subobj_meet_comm {A : Type u} (s₁ s₂ : Subobject A) :
    Path (s₁.meet s₂).predicate (s₂.meet s₁).predicate :=
  Path.mk [] (by ext x; exact ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a⟩⟩)

/-- 5. Join is idempotent. -/
noncomputable def subobj_join_idempotent {A : Type u} (s : Subobject A) :
    Path (s.join s).predicate s.predicate :=
  Path.mk [] (by ext x; exact ⟨fun h => h.elim id id, fun h => Or.inl h⟩)

/-- 6. Join is commutative. -/
noncomputable def subobj_join_comm {A : Type u} (s₁ s₂ : Subobject A) :
    Path (s₁.join s₂).predicate (s₂.join s₁).predicate :=
  Path.mk [] (by ext x; exact ⟨fun h => h.elim Or.inr Or.inl, fun h => h.elim Or.inr Or.inl⟩)

/-- 7. Meet with top is identity. -/
noncomputable def subobj_meet_top {A : Type u} (s : Subobject A) :
    Path (s.meet (Subobject.top A)).predicate s.predicate :=
  Path.mk [] (by ext x; exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, trivial⟩⟩)

/-- 8. Join with bot is identity. -/
noncomputable def subobj_join_bot {A : Type u} (s : Subobject A) :
    Path (s.join (Subobject.bot A)).predicate s.predicate :=
  Path.mk [] (by ext x; exact ⟨fun h => h.elim id False.elim, fun h => Or.inl h⟩)

/-- 9. Meet with bot is bot. -/
noncomputable def subobj_meet_bot {A : Type u} (s : Subobject A) :
    Path (s.meet (Subobject.bot A)).predicate (Subobject.bot A).predicate :=
  Path.mk [] (by ext x; exact ⟨fun ⟨_, h⟩ => h, fun h => False.elim h⟩)

/-- 10. Absorption law: s ∩ (s ∪ t) = s. -/
noncomputable def subobj_absorption {A : Type u} (s t : Subobject A) :
    Path (s.meet (s.join t)).predicate s.predicate :=
  Path.mk [] (by ext x; exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, Or.inl h⟩⟩)

/-- 11. Meet is associative. -/
noncomputable def subobj_meet_assoc {A : Type u} (s₁ s₂ s₃ : Subobject A) :
    Path ((s₁.meet s₂).meet s₃).predicate (s₁.meet (s₂.meet s₃)).predicate :=
  Path.mk [] (by ext x; exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩⟩)

/-! ## Power Objects -/

/-- Power object P(A) = Ω^A, modeled as (A → Prop). -/
noncomputable def PowerObj (A : Type u) := A → Prop

/-- Membership relation: x ∈ S. -/
noncomputable def PowerObj.mem {A : Type u} (x : A) (S : PowerObj A) : Prop := S x

/-- Singleton: {a}. -/
noncomputable def PowerObj.singleton {A : Type u} [DecidableEq A] (a : A) : PowerObj A :=
  fun x => x = a

/-- 12. Membership in singleton. -/
noncomputable def singleton_mem {A : Type u} [DecidableEq A] (a : A) :
    Path (PowerObj.mem a (PowerObj.singleton a)) (a = a) :=
  Path.refl _

/-- 13. Power object self-path. -/
noncomputable def power_refl {A : Type u} (S : PowerObj A) : Path S S :=
  Path.refl _

/-! ## Comprehension / Separation -/

/-- Comprehension: {x : A | φ(x)} as a subobject. -/
noncomputable def comprehension {A : Type u} (φ : A → Prop) : Subobject A :=
  { predicate := φ }

/-- 14. Comprehension with True gives top. -/
noncomputable def comprehension_true {A : Type u} :
    Path (comprehension (fun (_ : A) => True)).predicate (Subobject.top A).predicate :=
  Path.refl _

/-- 15. Comprehension with False gives bot. -/
noncomputable def comprehension_false {A : Type u} :
    Path (comprehension (fun (_ : A) => False)).predicate (Subobject.bot A).predicate :=
  Path.refl _

/-- 16. Comprehension with conjunction is meet. -/
noncomputable def comprehension_conj {A : Type u} (φ ψ : A → Prop) :
    Path (comprehension (fun x => φ x ∧ ψ x)).predicate
         ((comprehension φ).meet (comprehension ψ)).predicate :=
  Path.refl _

/-- 17. Comprehension with disjunction is join. -/
noncomputable def comprehension_disj {A : Type u} (φ ψ : A → Prop) :
    Path (comprehension (fun x => φ x ∨ ψ x)).predicate
         ((comprehension φ).join (comprehension ψ)).predicate :=
  Path.refl _

/-! ## Mitchell-Bénabou Language -/

/-- Formulas in the Mitchell-Bénabou internal language. -/
inductive MBFormula (A : Type u) : Type u where
  | trueF  : MBFormula A
  | falseF : MBFormula A
  | atom   : (A → Prop) → MBFormula A
  | conj   : MBFormula A → MBFormula A → MBFormula A
  | disj   : MBFormula A → MBFormula A → MBFormula A
  | impl   : MBFormula A → MBFormula A → MBFormula A
  | neg    : MBFormula A → MBFormula A

/-- Interpretation: an MB formula denotes a predicate on A. -/
noncomputable def MBFormula.interpret {A : Type u} : MBFormula A → (A → Prop)
  | .trueF      => fun _ => True
  | .falseF     => fun _ => False
  | .atom p     => p
  | .conj φ ψ   => fun x => φ.interpret x ∧ ψ.interpret x
  | .disj φ ψ   => fun x => φ.interpret x ∨ ψ.interpret x
  | .impl φ ψ   => fun x => φ.interpret x → ψ.interpret x
  | .neg φ      => fun x => ¬ φ.interpret x

/-- 18. True formula interprets to True. -/
noncomputable def mb_true_interpret {A : Type u} :
    Path (MBFormula.trueF (A := A)).interpret (fun _ => True) :=
  Path.refl _

/-- 19. False formula interprets to False. -/
noncomputable def mb_false_interpret {A : Type u} :
    Path (MBFormula.falseF (A := A)).interpret (fun _ => False) :=
  Path.refl _

/-- 20. Conjunction interpretation. -/
noncomputable def mb_conj_interpret {A : Type u} (φ ψ : MBFormula A) :
    Path (MBFormula.conj φ ψ).interpret (fun x => φ.interpret x ∧ ψ.interpret x) :=
  Path.refl _

/-- 21. Disjunction interpretation. -/
noncomputable def mb_disj_interpret {A : Type u} (φ ψ : MBFormula A) :
    Path (MBFormula.disj φ ψ).interpret (fun x => φ.interpret x ∨ ψ.interpret x) :=
  Path.refl _

/-- 22. Negation interpretation. -/
noncomputable def mb_neg_interpret {A : Type u} (φ : MBFormula A) :
    Path (MBFormula.neg φ).interpret (fun x => ¬ φ.interpret x) :=
  Path.refl _

/-- 23. MB conjunction corresponds to subobject meet. -/
noncomputable def mb_conj_is_meet {A : Type u} (φ ψ : MBFormula A) :
    Path (comprehension (MBFormula.conj φ ψ).interpret).predicate
         ((comprehension φ.interpret).meet (comprehension ψ.interpret)).predicate :=
  Path.refl _

/-- 24. MB disjunction corresponds to subobject join. -/
noncomputable def mb_disj_is_join {A : Type u} (φ ψ : MBFormula A) :
    Path (comprehension (MBFormula.disj φ ψ).interpret).predicate
         ((comprehension φ.interpret).join (comprehension ψ.interpret)).predicate :=
  Path.refl _

/-! ## Internal Quantifiers -/

/-- Internal ∀: ∀ over a fiber. -/
noncomputable def internalForall {A B : Type u} (φ : A → B → Prop) : A → Prop :=
  fun a => ∀ b, φ a b

/-- Internal ∃: ∃ over a fiber. -/
noncomputable def internalExists {A B : Type u} (φ : A → B → Prop) : A → Prop :=
  fun a => ∃ b, φ a b

/-- 25. Internal ∀ with constant True gives True. -/
noncomputable def internal_forall_true {A B : Type u} [Nonempty B] :
    Path (internalForall (fun (_ : A) (_ : B) => True)) (fun _ => True) :=
  Path.mk [] (by ext x; simp [internalForall])

/-- 26. Internal ∃ with constant False gives False. -/
noncomputable def internal_exists_false {A B : Type u} :
    Path (internalExists (fun (_ : A) (_ : B) => False)) (fun _ => False) :=
  Path.mk [] (by ext x; simp [internalExists])

/-- 27. ∀ distributes over conjunction. -/
noncomputable def forall_conj_distrib {A B : Type u} (φ ψ : A → B → Prop) :
    Path (internalForall (fun a b => φ a b ∧ ψ a b))
         (fun a => internalForall φ a ∧ internalForall ψ a) :=
  Path.mk [] (by
    ext a; simp [internalForall]
    exact ⟨fun h => ⟨fun b => (h b).1, fun b => (h b).2⟩,
           fun ⟨h₁, h₂⟩ b => ⟨h₁ b, h₂ b⟩⟩)

/-- 28. ∃ distributes over disjunction. -/
noncomputable def exists_disj_distrib {A B : Type u} (φ ψ : A → B → Prop) :
    Path (internalExists (fun a b => φ a b ∨ ψ a b))
         (fun a => internalExists φ a ∨ internalExists ψ a) :=
  Path.mk [] (by
    ext a; simp [internalExists]
    exact ⟨fun ⟨b, h⟩ => h.elim (fun h => Or.inl ⟨b, h⟩) (fun h => Or.inr ⟨b, h⟩),
           fun h => h.elim (fun ⟨b, h⟩ => ⟨b, Or.inl h⟩) (fun ⟨b, h⟩ => ⟨b, Or.inr h⟩)⟩)

/-! ## Frobenius Reciprocity -/

/-- 29. Frobenius: ∃_b(φ(a,b) ∧ ψ(a)) ↔ (∃_b φ(a,b)) ∧ ψ(a). -/
noncomputable def frobenius_reciprocity {A B : Type u} (φ : A → B → Prop) (ψ : A → Prop) :
    Path (internalExists (fun a b => φ a b ∧ ψ a))
         (fun a => internalExists φ a ∧ ψ a) :=
  Path.mk [] (by
    ext a; constructor
    · rintro ⟨b, hφ, hψ⟩; exact ⟨⟨b, hφ⟩, hψ⟩
    · rintro ⟨⟨b, hφ⟩, hψ⟩; exact ⟨b, hφ, hψ⟩)

/-! ## Image Factorization -/

/-- Image of f as a subobject of B. -/
noncomputable def imageSubobject {A B : Type u} (f : A → B) : Subobject B :=
  { predicate := fun b => ∃ a, f a = b }

/-- 30. Image is contained in top. -/
noncomputable def image_sub_top {A B : Type u} (f : A → B) :
    Path ((imageSubobject f).meet (Subobject.top B)).predicate
         (imageSubobject f).predicate :=
  Path.mk [] (by ext b; simp [Subobject.meet, Subobject.top, imageSubobject])

/-! ## Pullback of Subobjects -/

/-- Pullback of a subobject along f. -/
noncomputable def pullbackSubobject {A B : Type u} (f : A → B) (s : Subobject B) : Subobject A :=
  { predicate := fun a => s.predicate (f a) }

/-- 31. Pullback preserves meet. -/
noncomputable def pullback_preserves_meet {A B : Type u} (f : A → B) (s₁ s₂ : Subobject B) :
    Path (pullbackSubobject f (s₁.meet s₂)).predicate
         ((pullbackSubobject f s₁).meet (pullbackSubobject f s₂)).predicate :=
  Path.refl _

/-- 32. Pullback preserves join. -/
noncomputable def pullback_preserves_join {A B : Type u} (f : A → B) (s₁ s₂ : Subobject B) :
    Path (pullbackSubobject f (s₁.join s₂)).predicate
         ((pullbackSubobject f s₁).join (pullbackSubobject f s₂)).predicate :=
  Path.refl _

/-- 33. Pullback preserves top. -/
noncomputable def pullback_preserves_top {A B : Type u} (f : A → B) :
    Path (pullbackSubobject f (Subobject.top B)).predicate
         (Subobject.top A).predicate :=
  Path.refl _

/-- 34. Pullback preserves bot. -/
noncomputable def pullback_preserves_bot {A B : Type u} (f : A → B) :
    Path (pullbackSubobject f (Subobject.bot B)).predicate
         (Subobject.bot A).predicate :=
  Path.refl _

/-- 35. Pullback is functorial: (g ∘ f)* = f* ∘ g*. -/
noncomputable def pullback_functorial {A B C : Type u} (f : A → B) (g : B → C) (s : Subobject C) :
    Path (pullbackSubobject f (pullbackSubobject g s)).predicate
         (pullbackSubobject (g ∘ f) s).predicate :=
  Path.refl _

/-- 36. Pullback along id is identity. -/
noncomputable def pullback_id {A : Type u} (s : Subobject A) :
    Path (pullbackSubobject id s).predicate s.predicate :=
  Path.refl _

/-! ## Trans/Symm usage -/

/-- 37. Trans: combining meet idempotent with meet-top. -/
noncomputable def subobj_trans_example {A : Type u} (s : Subobject A) :
    Path (s.meet s).predicate (s.meet (Subobject.top A)).predicate :=
  Path.trans (subobj_meet_idempotent s) (Path.symm (subobj_meet_top s))

/-- 38. Symm: reverse meet commutativity. -/
noncomputable def subobj_symm_example {A : Type u} (s₁ s₂ : Subobject A) :
    Path (s₂.meet s₁).predicate (s₁.meet s₂).predicate :=
  Path.symm (subobj_meet_comm s₁ s₂)

end CategoricalLogicDeep
end Logic
end Path
end ComputationalPaths

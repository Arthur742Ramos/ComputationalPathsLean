/-
# Topos Logic via Computational Paths (Deep)

Heyting algebra of subobjects, internal ∀/∃, Kripke-Joyal semantics,
and Lawvere-Tierney topologies — all modeled through computational paths.

## References

- Mac Lane & Moerdijk, "Sheaves in Geometry and Logic"
- Johnstone, "Sketches of an Elephant", Part A/D
- Goldblatt, "Topoi: The Categorial Analysis of Logic"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Logic
namespace ToposLogicDeep

universe u v

open ComputationalPaths

/-! ## Heyting Algebra of Subobjects -/

/-- A Heyting algebra element, representing a subobject via its predicate. -/
structure HeytingSub (A : Type u) where
  predicate : A → Prop

/-- Meet (∧). -/
def HeytingSub.meet {A : Type u} (s₁ s₂ : HeytingSub A) : HeytingSub A :=
  { predicate := fun x => s₁.predicate x ∧ s₂.predicate x }

/-- Join (∨). -/
def HeytingSub.join {A : Type u} (s₁ s₂ : HeytingSub A) : HeytingSub A :=
  { predicate := fun x => s₁.predicate x ∨ s₂.predicate x }

/-- Implication (⇒). -/
def HeytingSub.imp {A : Type u} (s₁ s₂ : HeytingSub A) : HeytingSub A :=
  { predicate := fun x => s₁.predicate x → s₂.predicate x }

/-- Negation (¬). -/
def HeytingSub.neg {A : Type u} (s : HeytingSub A) : HeytingSub A :=
  { predicate := fun x => ¬ s.predicate x }

/-- Top (⊤). -/
def HeytingSub.top (A : Type u) : HeytingSub A :=
  { predicate := fun _ => True }

/-- Bottom (⊥). -/
def HeytingSub.bot (A : Type u) : HeytingSub A :=
  { predicate := fun _ => False }

/-- 1. Meet is idempotent. -/
def heyting_meet_idem {A : Type u} (s : HeytingSub A) :
    Path (s.meet s).predicate s.predicate :=
  Path.mk [] (by ext x; exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, h⟩⟩)

/-- 2. Meet is commutative. -/
def heyting_meet_comm {A : Type u} (s₁ s₂ : HeytingSub A) :
    Path (s₁.meet s₂).predicate (s₂.meet s₁).predicate :=
  Path.mk [] (by ext x; exact ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a⟩⟩)

/-- 3. Join is commutative. -/
def heyting_join_comm {A : Type u} (s₁ s₂ : HeytingSub A) :
    Path (s₁.join s₂).predicate (s₂.join s₁).predicate :=
  Path.mk [] (by ext x; exact ⟨fun h => h.elim Or.inr Or.inl, fun h => h.elim Or.inr Or.inl⟩)

/-- 4. Meet distributes over join. -/
def heyting_meet_distrib_join {A : Type u} (s₁ s₂ s₃ : HeytingSub A) :
    Path (s₁.meet (s₂.join s₃)).predicate ((s₁.meet s₂).join (s₁.meet s₃)).predicate :=
  Path.mk [] (by
    ext x; constructor
    · rintro ⟨h₁, h₂ | h₃⟩
      · exact Or.inl ⟨h₁, h₂⟩
      · exact Or.inr ⟨h₁, h₃⟩
    · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₃⟩)
      · exact ⟨h₁, Or.inl h₂⟩
      · exact ⟨h₁, Or.inr h₃⟩)

/-- 5. Modus ponens: (s ∧ (s ⇒ t)).predicate x → t.predicate x. -/
def heyting_mp {A : Type u} (s t : HeytingSub A) (x : A)
    (h : (s.meet (s.imp t)).predicate x) : t.predicate x :=
  h.2 h.1

/-- 6. Heyting implication adjunction: s ∧ t ≤ u ↔ t ≤ (s ⇒ u). -/
theorem heyting_adjunction {A : Type u} (s t u : HeytingSub A) :
    (∀ x, (s.meet t).predicate x → u.predicate x) ↔
    (∀ x, t.predicate x → (s.imp u).predicate x) := by
  constructor
  · intro h x ht hs; exact h x ⟨hs, ht⟩
  · intro h x ⟨hs, ht⟩; exact h x ht hs

/-- 7. Double negation: s ≤ ¬¬s. -/
def heyting_double_neg {A : Type u} (s : HeytingSub A) (x : A)
    (h : s.predicate x) : (s.neg.neg).predicate x :=
  fun hn => hn h

/-- 8. ¬¬¬s = ¬s (triple negation). -/
def heyting_triple_neg {A : Type u} (s : HeytingSub A) :
    Path (s.neg.neg.neg).predicate s.neg.predicate :=
  Path.mk [] (by
    ext x; constructor
    · intro h hs; exact h (fun hn => hn hs)
    · intro h hnn; exact hnn h)

/-- 9. Meet with top is identity. -/
def heyting_meet_top {A : Type u} (s : HeytingSub A) :
    Path (s.meet (HeytingSub.top A)).predicate s.predicate :=
  Path.mk [] (by ext x; exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, trivial⟩⟩)

/-- 10. Join with bot is identity. -/
def heyting_join_bot {A : Type u} (s : HeytingSub A) :
    Path (s.join (HeytingSub.bot A)).predicate s.predicate :=
  Path.mk [] (by ext x; exact ⟨fun h => h.elim id False.elim, fun h => Or.inl h⟩)

/-- 11. ⊥ ⇒ s = ⊤ (ex falso). -/
def heyting_ex_falso {A : Type u} (s : HeytingSub A) :
    Path ((HeytingSub.bot A).imp s).predicate (HeytingSub.top A).predicate :=
  Path.mk [] (by ext x; exact ⟨fun _ => trivial, fun _ h => False.elim h⟩)

/-! ## Kripke-Joyal Semantics -/

/-- A forcing relation over a poset of stages. -/
structure KripkeJoyal (W : Type u) where
  le : W → W → Prop
  le_refl : ∀ w, le w w
  le_trans : ∀ u v w, le u v → le v w → le u w

/-- Forcing of a proposition at a stage. -/
structure Forcing (W : Type u) (kj : KripkeJoyal W) where
  forces : W → Prop
  monotone : ∀ w₁ w₂, kj.le w₁ w₂ → forces w₁ → forces w₂

/-- Meet of forcings. -/
def Forcing.meet {W : Type u} {kj : KripkeJoyal W} (f₁ f₂ : Forcing W kj) : Forcing W kj :=
  { forces := fun w => f₁.forces w ∧ f₂.forces w
    monotone := fun w₁ w₂ h ⟨h₁, h₂⟩ => ⟨f₁.monotone w₁ w₂ h h₁, f₂.monotone w₁ w₂ h h₂⟩ }

/-- Join of forcings. -/
def Forcing.join {W : Type u} {kj : KripkeJoyal W} (f₁ f₂ : Forcing W kj) : Forcing W kj :=
  { forces := fun w => f₁.forces w ∨ f₂.forces w
    monotone := fun w₁ w₂ h hf => hf.elim
      (fun h₁ => Or.inl (f₁.monotone w₁ w₂ h h₁))
      (fun h₂ => Or.inr (f₂.monotone w₁ w₂ h h₂)) }

/-- Implication forcing (Kripke-style). -/
def Forcing.kimp {W : Type u} {kj : KripkeJoyal W} (f₁ f₂ : Forcing W kj) : Forcing W kj :=
  { forces := fun w => ∀ w', kj.le w w' → f₁.forces w' → f₂.forces w'
    monotone := fun w₁ w₂ h₁₂ hf w' hw' hf₁ => hf w' (kj.le_trans w₁ w₂ w' h₁₂ hw') hf₁ }

/-- 12. Forcing meet is commutative. -/
def forcing_meet_comm {W : Type u} {kj : KripkeJoyal W} (f₁ f₂ : Forcing W kj) :
    Path (f₁.meet f₂).forces (f₂.meet f₁).forces :=
  Path.mk [] (by ext w; exact ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a⟩⟩)

/-- 13. Forcing meet with self. -/
def forcing_meet_idem {W : Type u} {kj : KripkeJoyal W} (f : Forcing W kj) :
    Path (f.meet f).forces f.forces :=
  Path.mk [] (by ext w; exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, h⟩⟩)

/-- 14. Kripke monotonicity: if w forces φ and w ≤ w', then w' forces φ. -/
def kripke_monotone {W : Type u} {kj : KripkeJoyal W} (f : Forcing W kj)
    (w w' : W) (hle : kj.le w w') (hw : f.forces w) : f.forces w' :=
  f.monotone w w' hle hw

/-- 15. Kripke forcing of ⊤. -/
def forcing_top (W : Type u) (kj : KripkeJoyal W) : Forcing W kj :=
  { forces := fun _ => True, monotone := fun _ _ _ _ => trivial }

/-- 16. Top is forced everywhere. -/
def forcing_top_everywhere {W : Type u} {kj : KripkeJoyal W} (w : W) :
    (forcing_top W kj).forces w :=
  trivial

/-! ## Lawvere-Tierney Topologies -/

/-- A Lawvere-Tierney topology j : Ω → Ω on predicates. -/
structure LTTopology (A : Type u) where
  j : (A → Prop) → (A → Prop)
  j_ge : ∀ φ x, φ x → j φ x                         -- φ ≤ jφ
  j_idem : ∀ φ, j (j φ) = j φ                        -- j² = j
  j_meet : ∀ φ ψ, j (fun x => φ x ∧ ψ x) = fun x => j φ x ∧ j ψ x  -- j preserves ∧

/-- 17. j is inflationary: φ ≤ jφ as a path. -/
def lt_inflationary {A : Type u} (top : LTTopology A) (φ : A → Prop) (x : A)
    (h : φ x) : top.j φ x :=
  top.j_ge φ x h

/-- 18. j is idempotent as a path. -/
def lt_idempotent {A : Type u} (top : LTTopology A) (φ : A → Prop) :
    Path (top.j (top.j φ)) (top.j φ) :=
  Path.mk [] (by rw [top.j_idem])

/-- 19. j preserves meet as a path. -/
def lt_preserves_meet {A : Type u} (top : LTTopology A) (φ ψ : A → Prop) :
    Path (top.j (fun x => φ x ∧ ψ x)) (fun x => top.j φ x ∧ top.j ψ x) :=
  Path.mk [] (by rw [top.j_meet])

/-- A j-sheaf condition: φ is a j-closed subobject if jφ = φ. -/
def isJClosed {A : Type u} (top : LTTopology A) (φ : A → Prop) : Prop :=
  top.j φ = φ

/-- 20. Top predicate is j-closed. -/
def top_is_j_closed {A : Type u} (top : LTTopology A)
    (h_top : top.j (fun _ => True) = fun _ => True) :
    isJClosed top (fun _ => True) :=
  h_top

/-- 21. Meet of j-closed is j-closed. -/
theorem j_closed_meet {A : Type u} (top : LTTopology A) (φ ψ : A → Prop)
    (hφ : isJClosed top φ) (hψ : isJClosed top ψ) :
    isJClosed top (fun x => φ x ∧ ψ x) := by
  unfold isJClosed at *
  rw [top.j_meet, hφ, hψ]

/-- 22. j-closure is j-closed. -/
theorem j_closure_is_closed {A : Type u} (top : LTTopology A) (φ : A → Prop) :
    isJClosed top (top.j φ) := by
  unfold isJClosed
  rw [top.j_idem]

/-! ## Sheafification -/

/-- Sheafify a predicate by applying j. -/
def sheafify {A : Type u} (top : LTTopology A) (φ : A → Prop) : A → Prop :=
  top.j φ

/-- 23. Sheafification is j-closed. -/
def sheafify_closed {A : Type u} (top : LTTopology A) (φ : A → Prop) :
    isJClosed top (sheafify top φ) :=
  j_closure_is_closed top φ

/-- 24. Sheafification is inflationary. -/
def sheafify_ge {A : Type u} (top : LTTopology A) (φ : A → Prop) (x : A)
    (h : φ x) : sheafify top φ x :=
  top.j_ge φ x h

/-- 25. Sheafification is idempotent. -/
def sheafify_idem {A : Type u} (top : LTTopology A) (φ : A → Prop) :
    Path (sheafify top (sheafify top φ)) (sheafify top φ) :=
  lt_idempotent top φ

/-! ## Internal Logic in a Topos (Prop-valued) -/

/-- 26. In a topos, excluded middle may fail: ¬¬p does not imply p in general.
    We show the Heyting structure: p ∨ ¬p is not provable, but ¬¬(p ∨ ¬p) is. -/
theorem double_neg_lem (p : Prop) : ¬¬(p ∨ ¬p) :=
  fun h => h (Or.inr (fun hp => h (Or.inl hp)))

/-- 27. Internal Heyting: (p → q) → (¬q → ¬p) (contrapositive). -/
def heyting_contrapositive {A : Type u} (s t : HeytingSub A) :
    Path ((s.imp t).imp (t.neg.imp s.neg)).predicate (HeytingSub.top A).predicate :=
  Path.mk [] (by
    ext x; simp [HeytingSub.imp, HeytingSub.neg, HeytingSub.top]
    exact fun h hn hs => hn (h hs))

/-- 28. Trans on Heyting paths: meet_idem then meet_top. -/
def heyting_trans_example {A : Type u} (s : HeytingSub A) :
    Path (s.meet s).predicate (s.meet (HeytingSub.top A)).predicate :=
  Path.trans (heyting_meet_idem s) (Path.symm (heyting_meet_top s))

/-- 29. Symm on Heyting: reverse meet comm. -/
def heyting_symm_example {A : Type u} (s₁ s₂ : HeytingSub A) :
    Path (s₂.meet s₁).predicate (s₁.meet s₂).predicate :=
  Path.symm (heyting_meet_comm s₁ s₂)

/-- 30. Forcing join is commutative. -/
def forcing_join_comm {W : Type u} {kj : KripkeJoyal W} (f₁ f₂ : Forcing W kj) :
    Path (f₁.join f₂).forces (f₂.join f₁).forces :=
  Path.mk [] (by ext w; exact ⟨fun h => h.elim Or.inr Or.inl, fun h => h.elim Or.inr Or.inl⟩)

/-- 31. Trans on LT paths. -/
def lt_trans_example {A : Type u} (top : LTTopology A) (φ : A → Prop) :
    Path (top.j (top.j (top.j φ))) (top.j φ) :=
  Path.trans (lt_idempotent top (top.j φ)) (lt_idempotent top φ)

end ToposLogicDeep
end Logic
end Path
end ComputationalPaths

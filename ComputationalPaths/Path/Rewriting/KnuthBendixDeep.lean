/-
# Deep Knuth-Bendix: Completion as Path Construction

Knuth-Bendix completion formalized via computational paths. Critical pairs
as path divergences, orientation as path direction, completion steps as
new path equalities. All proofs use multiple Path operations (trans, symm,
congrArg, transport).

## Design

All theorems work with Path/Step/trans/symm/congrArg from Core. We avoid
asserting `trans p (symm p) = refl` since step lists differ; instead we
use algebraic identities that hold structurally (assoc, unit, congrArg
distributivity, transport coherence, symm involution).
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Rewriting.KnuthBendixDeep

open ComputationalPaths.Path

universe u

/-! ## Term algebra -/

inductive KBTerm where
  | var (n : Nat) : KBTerm
  | const (n : Nat) : KBTerm
  | unary (f : Nat) (t : KBTerm) : KBTerm
  | binary (f : Nat) (l r : KBTerm) : KBTerm
  deriving DecidableEq, Repr

namespace KBTerm

@[simp] def size : KBTerm → Nat
  | .var _ => 1
  | .const _ => 1
  | .unary _ t => t.size + 1
  | .binary _ l r => l.size + r.size + 1

theorem size_pos (t : KBTerm) : 0 < t.size := by cases t <;> simp <;> omega

@[simp] def weight (w₀ : Nat) : KBTerm → Nat
  | .var _ => w₀
  | .const _ => w₀
  | .unary _ t => t.weight w₀ + w₀
  | .binary _ l r => l.weight w₀ + r.weight w₀ + w₀

theorem weight_pos (w₀ : Nat) (hw : 0 < w₀) (t : KBTerm) : 0 < t.weight w₀ := by
  cases t <;> simp <;> omega

end KBTerm

/-! ## Interpretation -/

structure KBEnv (A : Type u) where
  varVal : Nat → A
  constVal : Nat → A
  unaryOp : Nat → A → A
  binaryOp : Nat → A → A → A

@[simp] def KBTerm.interp {A : Type u} (env : KBEnv A) : KBTerm → A
  | .var n => env.varVal n
  | .const n => env.constVal n
  | .unary f t => env.unaryOp f (t.interp env)
  | .binary f l r => env.binaryOp f (l.interp env) (r.interp env)

/-! ## 1. Associativity of multi-step rewriting chains -/

/-- Three-rule composition is associative. -/
theorem rewrite_chain_assoc {A : Type u} {a b c d : A}
    (r₁ : Path a b) (r₂ : Path b c) (r₃ : Path c d) :
    Path.trans (Path.trans r₁ r₂) r₃ = Path.trans r₁ (Path.trans r₂ r₃) :=
  Path.trans_assoc r₁ r₂ r₃

/-! ## 2. Four-rule chain reassociation -/

theorem rewrite_chain_four {A : Type u} {a b c d e : A}
    (r₁ : Path a b) (r₂ : Path b c) (r₃ : Path c d) (r₄ : Path d e) :
    Path.trans (Path.trans (Path.trans r₁ r₂) r₃) r₄ =
    Path.trans r₁ (Path.trans r₂ (Path.trans r₃ r₄)) := by
  calc Path.trans (Path.trans (Path.trans r₁ r₂) r₃) r₄
      = Path.trans (Path.trans r₁ r₂) (Path.trans r₃ r₄) :=
          Path.trans_assoc (Path.trans r₁ r₂) r₃ r₄
    _ = Path.trans r₁ (Path.trans r₂ (Path.trans r₃ r₄)) :=
          Path.trans_assoc r₁ r₂ (Path.trans r₃ r₄)

/-! ## 3. Anti-homomorphism of symm over composition -/

theorem reverse_chain {A : Type u} {a b c : A}
    (r₁ : Path a b) (r₂ : Path b c) :
    Path.symm (Path.trans r₁ r₂) = Path.trans (Path.symm r₂) (Path.symm r₁) :=
  Path.symm_trans r₁ r₂

/-! ## 4. Triple reverse -/

theorem reverse_chain_three {A : Type u} {a b c d : A}
    (r₁ : Path a b) (r₂ : Path b c) (r₃ : Path c d) :
    Path.symm (Path.trans (Path.trans r₁ r₂) r₃) =
    Path.trans (Path.symm r₃) (Path.trans (Path.symm r₂) (Path.symm r₁)) := by
  calc Path.symm (Path.trans (Path.trans r₁ r₂) r₃)
      = Path.trans (Path.symm r₃) (Path.symm (Path.trans r₁ r₂)) :=
          Path.symm_trans (Path.trans r₁ r₂) r₃
    _ = Path.trans (Path.symm r₃) (Path.trans (Path.symm r₂) (Path.symm r₁)) := by
          rw [Path.symm_trans r₁ r₂]

/-! ## 5. Double reversal is identity -/

theorem double_reverse {A : Type u} {a b : A} (p : Path a b) :
    Path.symm (Path.symm p) = p := Path.symm_symm p

/-! ## 6. congrArg distributes over trans (rule under context) -/

theorem rule_under_context {A B : Type u} {a b c : A}
    (f : A → B) (r₁ : Path a b) (r₂ : Path b c) :
    Path.congrArg f (Path.trans r₁ r₂) =
    Path.trans (Path.congrArg f r₁) (Path.congrArg f r₂) :=
  Path.congrArg_trans f r₁ r₂

/-! ## 7. congrArg commutes with symm (reverse rule under context) -/

theorem reverse_rule_under_context {A B : Type u} {a b : A}
    (f : A → B) (rule : Path a b) :
    Path.congrArg f (Path.symm rule) = Path.symm (Path.congrArg f rule) :=
  Path.congrArg_symm f rule

/-! ## 8. Nested context: congrArg composition -/

theorem nested_context {A B C : Type u} {a b : A}
    (f : A → B) (g : B → C) (rule : Path a b) :
    Path.congrArg g (Path.congrArg f rule) =
    Path.congrArg (fun x => g (f x)) rule :=
  (Path.congrArg_comp g f rule).symm

/-! ## 9. Deep superposition: triple context + distributivity -/

theorem deep_superposition {A B C : Type u} {a b c : A}
    (f : A → B) (g : B → C)
    (r₁ : Path a b) (r₂ : Path b c) :
    Path.congrArg g (Path.congrArg f (Path.trans r₁ r₂)) =
    Path.trans (Path.congrArg (fun x => g (f x)) r₁)
              (Path.congrArg (fun x => g (f x)) r₂) := by
  calc Path.congrArg g (Path.congrArg f (Path.trans r₁ r₂))
      = Path.congrArg g (Path.trans (Path.congrArg f r₁) (Path.congrArg f r₂)) := by
          rw [Path.congrArg_trans f r₁ r₂]
    _ = Path.trans (Path.congrArg g (Path.congrArg f r₁))
                   (Path.congrArg g (Path.congrArg f r₂)) := by
          rw [Path.congrArg_trans g (Path.congrArg f r₁) (Path.congrArg f r₂)]
    _ = Path.trans (Path.congrArg (fun x => g (f x)) r₁)
                   (Path.congrArg (fun x => g (f x)) r₂) := by
          rw [Path.congrArg_comp g f r₁, Path.congrArg_comp g f r₂]

/-! ## 10. Deep superposition with symm -/

theorem deep_superposition_symm {A B C : Type u} {a b : A}
    (f : A → B) (g : B → C) (rule : Path a b) :
    Path.congrArg g (Path.congrArg f (Path.symm rule)) =
    Path.symm (Path.congrArg (fun x => g (f x)) rule) := by
  calc Path.congrArg g (Path.congrArg f (Path.symm rule))
      = Path.congrArg g (Path.symm (Path.congrArg f rule)) := by
          rw [Path.congrArg_symm f rule]
    _ = Path.symm (Path.congrArg g (Path.congrArg f rule)) := by
          rw [Path.congrArg_symm g (Path.congrArg f rule)]
    _ = Path.symm (Path.congrArg (fun x => g (f x)) rule) := by
          rw [Path.congrArg_comp g f rule]

/-! ## 11. Transport along rewrite chain -/

theorem transport_rewrite_chain {A : Type u} {D : A → Sort u}
    {a b c : A} (r₁ : Path a b) (r₂ : Path b c) (x : D a) :
    Path.transport (D := D) (Path.trans r₁ r₂) x =
    Path.transport (D := D) r₂ (Path.transport (D := D) r₁ x) :=
  Path.transport_trans (D := D) r₁ r₂ x

/-! ## 12. Transport along three-rule chain -/

theorem transport_three_chain {A : Type u} {D : A → Sort u}
    {a b c d : A} (r₁ : Path a b) (r₂ : Path b c) (r₃ : Path c d) (x : D a) :
    Path.transport (D := D) (Path.trans (Path.trans r₁ r₂) r₃) x =
    Path.transport (D := D) r₃
      (Path.transport (D := D) r₂ (Path.transport (D := D) r₁ x)) := by
  calc Path.transport (D := D) (Path.trans (Path.trans r₁ r₂) r₃) x
      = Path.transport (D := D) r₃ (Path.transport (D := D) (Path.trans r₁ r₂) x) :=
          Path.transport_trans (D := D) (Path.trans r₁ r₂) r₃ x
    _ = Path.transport (D := D) r₃
          (Path.transport (D := D) r₂ (Path.transport (D := D) r₁ x)) := by
          rw [Path.transport_trans (D := D) r₁ r₂ x]

/-! ## 13. Transport roundtrip via symm -/

theorem transport_roundtrip {A : Type u} {D : A → Sort u}
    {a b : A} (p : Path a b) (x : D a) :
    Path.transport (D := D) (Path.symm p) (Path.transport (D := D) p x) = x :=
  Path.transport_symm_left (D := D) p x

/-! ## 14. Transport roundtrip other direction -/

theorem transport_roundtrip_rev {A : Type u} {D : A → Sort u}
    {a b : A} (p : Path a b) (y : D b) :
    Path.transport (D := D) p (Path.transport (D := D) (Path.symm p) y) = y :=
  Path.transport_symm_right (D := D) p y

/-! ## 15. Critical pair joining: given divergence, the joining toEq agrees -/

theorem cp_toEq_agreement {A : Type u} {a b : A}
    (p q : Path a b) : p.toEq = q.toEq :=
  Subsingleton.elim p.toEq q.toEq

/-! ## 16. Convergent system: any two paths have equal transport action -/

theorem convergent_transport_unique {A : Type u} {D : A → Sort u}
    {a b : A} (p q : Path a b) (x : D a) :
    Path.transport (D := D) p x = Path.transport (D := D) q x := by
  have h : p.toEq = q.toEq := Subsingleton.elim p.toEq q.toEq
  exact Path.transport_of_toEq_eq (D := D) h x

/-! ## 17. Rewrite chain with context switch -/

theorem chain_with_context_switch {A B : Type u} {a b c : A}
    (f : A → B) (r₁ : Path a b) (r₂ : Path b c) :
    Path.trans (Path.congrArg f r₁) (Path.congrArg f r₂) =
    Path.congrArg f (Path.trans r₁ r₂) :=
  (Path.congrArg_trans f r₁ r₂).symm

/-! ## 18. Symmetry of reverse chain under triple congrArg comp -/

theorem symm_triple_congrArg {A B C D : Type u} {a b : A}
    (f : A → B) (g : B → C) (h : C → D) (rule : Path a b) :
    Path.symm (Path.congrArg h (Path.congrArg g (Path.congrArg f rule))) =
    Path.congrArg h (Path.congrArg g (Path.congrArg f (Path.symm rule))) := by
  calc Path.symm (Path.congrArg h (Path.congrArg g (Path.congrArg f rule)))
      = Path.congrArg h (Path.symm (Path.congrArg g (Path.congrArg f rule))) := by
          rw [Path.congrArg_symm h]
    _ = Path.congrArg h (Path.congrArg g (Path.symm (Path.congrArg f rule))) := by
          rw [Path.congrArg_symm g]
    _ = Path.congrArg h (Path.congrArg g (Path.congrArg f (Path.symm rule))) := by
          rw [Path.congrArg_symm f]

/-! ## 19. Four-fold congrArg composition -/

theorem congrArg_four_comp {A B C D : Type u} {a b : A}
    (f : A → B) (g : B → C) (h : C → D) (rule : Path a b) :
    Path.congrArg h (Path.congrArg g (Path.congrArg f rule)) =
    Path.congrArg (fun x => h (g (f x))) rule := by
  calc Path.congrArg h (Path.congrArg g (Path.congrArg f rule))
      = Path.congrArg h (Path.congrArg (fun x => g (f x)) rule) := by
          rw [Path.congrArg_comp g f rule]
    _ = Path.congrArg (fun x => h (g (f x))) rule := by
          rw [Path.congrArg_comp h (fun x => g (f x)) rule]

/-! ## 20. Interreduction: simplifying one rule by another in context -/

theorem interreduction {A B : Type u} {a b c : A}
    (f : A → B) (old : Path a b) (simplifier : Path b c) :
    Path.congrArg f (Path.trans old simplifier) =
    Path.trans (Path.congrArg f old) (Path.congrArg f simplifier) :=
  Path.congrArg_trans f old simplifier

/-! ## 21. Reverse chain through context is context through reverse chain -/

theorem reverse_through_context {A B : Type u} {a b c : A}
    (f : A → B) (r₁ : Path a b) (r₂ : Path b c) :
    Path.symm (Path.congrArg f (Path.trans r₁ r₂)) =
    Path.trans (Path.symm (Path.congrArg f r₂)) (Path.symm (Path.congrArg f r₁)) := by
  calc Path.symm (Path.congrArg f (Path.trans r₁ r₂))
      = Path.symm (Path.trans (Path.congrArg f r₁) (Path.congrArg f r₂)) := by
          rw [Path.congrArg_trans f r₁ r₂]
    _ = Path.trans (Path.symm (Path.congrArg f r₂)) (Path.symm (Path.congrArg f r₁)) :=
          Path.symm_trans (Path.congrArg f r₁) (Path.congrArg f r₂)

/-! ## 22. congrArg preserves refl -/

theorem context_preserves_refl {A B : Type u} (f : A → B) (a : A) :
    Path.congrArg f (Path.refl a) = Path.refl (f a) := by
  simp [Path.congrArg]

/-! ## 23. Completion step: extending path via congrArg + trans -/

theorem completion_step {A B : Type u} {a b c : A}
    (f : A → B) (r₁ : Path a b) (r₂ : Path b c) :
    Path.trans (Path.congrArg f (Path.trans r₁ r₂))
              (Path.symm (Path.congrArg f r₂)) =
    Path.trans (Path.trans (Path.congrArg f r₁) (Path.congrArg f r₂))
              (Path.symm (Path.congrArg f r₂)) := by
  rw [Path.congrArg_trans f r₁ r₂]

/-! ## 24. Transport coherence: composing transport along chain in context -/

theorem transport_context_coherence {A B : Type u}
    {D : B → Sort u} {a b c : A}
    (f : A → B) (r₁ : Path a b) (r₂ : Path b c) (x : D (f a)) :
    Path.transport (D := D) (Path.congrArg f (Path.trans r₁ r₂)) x =
    Path.transport (D := D) (Path.congrArg f r₂)
      (Path.transport (D := D) (Path.congrArg f r₁) x) := by
  calc Path.transport (D := D) (Path.congrArg f (Path.trans r₁ r₂)) x
      = Path.transport (D := D)
          (Path.trans (Path.congrArg f r₁) (Path.congrArg f r₂)) x := by
          rw [Path.congrArg_trans f r₁ r₂]
    _ = Path.transport (D := D) (Path.congrArg f r₂)
          (Path.transport (D := D) (Path.congrArg f r₁) x) :=
          Path.transport_trans (D := D) (Path.congrArg f r₁) (Path.congrArg f r₂) x

/-! ## 25. Transport roundtrip through context -/

theorem transport_context_roundtrip {A B : Type u}
    {D : B → Sort u} {a b : A}
    (f : A → B) (rule : Path a b) (x : D (f a)) :
    Path.transport (D := D) (Path.congrArg f (Path.symm rule))
      (Path.transport (D := D) (Path.congrArg f rule) x) = x := by
  calc Path.transport (D := D) (Path.congrArg f (Path.symm rule))
        (Path.transport (D := D) (Path.congrArg f rule) x)
      = Path.transport (D := D) (Path.symm (Path.congrArg f rule))
          (Path.transport (D := D) (Path.congrArg f rule) x) := by
          rw [Path.congrArg_symm f rule]
    _ = x := Path.transport_symm_left (D := D) (Path.congrArg f rule) x

/-! ## 26. Five-rule reassociation -/

theorem rewrite_chain_five {A : Type u} {a b c d e f : A}
    (r₁ : Path a b) (r₂ : Path b c) (r₃ : Path c d)
    (r₄ : Path d e) (r₅ : Path e f) :
    Path.trans (Path.trans (Path.trans (Path.trans r₁ r₂) r₃) r₄) r₅ =
    Path.trans r₁ (Path.trans r₂ (Path.trans r₃ (Path.trans r₄ r₅))) := by
  calc Path.trans (Path.trans (Path.trans (Path.trans r₁ r₂) r₃) r₄) r₅
      = Path.trans (Path.trans (Path.trans r₁ r₂) r₃) (Path.trans r₄ r₅) :=
          Path.trans_assoc _ r₄ r₅
    _ = Path.trans (Path.trans r₁ r₂) (Path.trans r₃ (Path.trans r₄ r₅)) :=
          Path.trans_assoc _ r₃ _
    _ = Path.trans r₁ (Path.trans r₂ (Path.trans r₃ (Path.trans r₄ r₅))) :=
          Path.trans_assoc r₁ r₂ _

/-! ## 27. Quadruple symm anti-homomorphism -/

theorem reverse_chain_four {A : Type u} {a b c d e : A}
    (r₁ : Path a b) (r₂ : Path b c) (r₃ : Path c d) (r₄ : Path d e) :
    Path.symm (Path.trans (Path.trans (Path.trans r₁ r₂) r₃) r₄) =
    Path.trans (Path.symm r₄)
      (Path.trans (Path.symm r₃) (Path.trans (Path.symm r₂) (Path.symm r₁))) := by
  calc Path.symm (Path.trans (Path.trans (Path.trans r₁ r₂) r₃) r₄)
      = Path.trans (Path.symm r₄) (Path.symm (Path.trans (Path.trans r₁ r₂) r₃)) :=
          Path.symm_trans _ r₄
    _ = Path.trans (Path.symm r₄) (Path.trans (Path.symm r₃) (Path.symm (Path.trans r₁ r₂))) := by
          rw [Path.symm_trans (Path.trans r₁ r₂) r₃]
    _ = Path.trans (Path.symm r₄)
          (Path.trans (Path.symm r₃) (Path.trans (Path.symm r₂) (Path.symm r₁))) := by
          rw [Path.symm_trans r₁ r₂]

/-! ## 28. congrArg distributes over four-fold trans -/

theorem congrArg_four_trans {A B : Type u} {a b c d e : A}
    (f : A → B) (r₁ : Path a b) (r₂ : Path b c) (r₃ : Path c d) (r₄ : Path d e) :
    Path.congrArg f (Path.trans (Path.trans (Path.trans r₁ r₂) r₃) r₄) =
    Path.trans (Path.congrArg f r₁)
      (Path.trans (Path.congrArg f r₂)
        (Path.trans (Path.congrArg f r₃) (Path.congrArg f r₄))) := by
  calc Path.congrArg f (Path.trans (Path.trans (Path.trans r₁ r₂) r₃) r₄)
      = Path.congrArg f (Path.trans r₁ (Path.trans r₂ (Path.trans r₃ r₄))) := by
          rw [rewrite_chain_four r₁ r₂ r₃ r₄]
    _ = Path.trans (Path.congrArg f r₁) (Path.congrArg f (Path.trans r₂ (Path.trans r₃ r₄))) :=
          Path.congrArg_trans f r₁ _
    _ = Path.trans (Path.congrArg f r₁) (Path.trans (Path.congrArg f r₂) (Path.congrArg f (Path.trans r₃ r₄))) := by
          rw [Path.congrArg_trans f r₂ (Path.trans r₃ r₄)]
    _ = Path.trans (Path.congrArg f r₁)
          (Path.trans (Path.congrArg f r₂)
            (Path.trans (Path.congrArg f r₃) (Path.congrArg f r₄))) := by
          rw [Path.congrArg_trans f r₃ r₄]

/-! ## 29. symm_symm through context preserves identity -/

theorem symm_symm_context {A B : Type u} {a b : A}
    (f : A → B) (rule : Path a b) :
    Path.congrArg f (Path.symm (Path.symm rule)) = Path.congrArg f rule := by
  rw [Path.symm_symm rule]

/-! ## 30. Transport along congrArg chain equals transport compose -/

theorem transport_compose_chain {A B : Type u}
    {D : B → Sort u} {a b c : A}
    (f : A → B) (r₁ : Path a b) (r₂ : Path b c) (x : D (f a)) :
    Path.transport (D := D ∘ f) (Path.trans r₁ r₂) x =
    Path.transport (D := D ∘ f) r₂ (Path.transport (D := D ∘ f) r₁ x) :=
  Path.transport_trans (D := D ∘ f) r₁ r₂ x

end ComputationalPaths.Path.Rewriting.KnuthBendixDeep

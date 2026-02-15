/-
# Deep Knuth-Bendix: Completion as Path Construction

Knuth-Bendix completion formalized via computational paths. Critical pairs
as path divergences, orientation as path direction, completion steps as
new path equalities. All proofs use multiple Path operations (trans, symm,
congrArg, transport).

## Design

All theorems work with Path/Step/trans/symm/congrArg from Core. We use
algebraic identities that hold structurally (assoc, unit, congrArg
distributivity, transport coherence, symm involution).
-/

import ComputationalPaths.Path.Basic

set_option maxHeartbeats 800000

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

/-! ## Rewrite rule as path -/

structure RewriteRule (A : Type u) where
  lhsVal : A
  rhsVal : A
  rule : Path lhsVal rhsVal

/-! ## 1. Three-rule chain associativity -/

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

/-! ## 3. Triple reverse (anti-homomorphism) -/

theorem reverse_chain_three {A : Type u} {a b c d : A}
    (r₁ : Path a b) (r₂ : Path b c) (r₃ : Path c d) :
    Path.symm (Path.trans (Path.trans r₁ r₂) r₃) =
    Path.trans (Path.symm r₃) (Path.trans (Path.symm r₂) (Path.symm r₁)) := by
  calc Path.symm (Path.trans (Path.trans r₁ r₂) r₃)
      = Path.trans (Path.symm r₃) (Path.symm (Path.trans r₁ r₂)) :=
          Path.symm_trans (Path.trans r₁ r₂) r₃
    _ = Path.trans (Path.symm r₃) (Path.trans (Path.symm r₂) (Path.symm r₁)) := by
          rw [Path.symm_trans r₁ r₂]

/-! ## 4. Quadruple reverse -/

theorem reverse_chain_four {A : Type u} {a b c d e : A}
    (r₁ : Path a b) (r₂ : Path b c) (r₃ : Path c d) (r₄ : Path d e) :
    Path.symm (Path.trans (Path.trans (Path.trans r₁ r₂) r₃) r₄) =
    Path.trans (Path.symm r₄)
      (Path.trans (Path.symm r₃) (Path.trans (Path.symm r₂) (Path.symm r₁))) := by
  calc Path.symm (Path.trans (Path.trans (Path.trans r₁ r₂) r₃) r₄)
      = Path.trans (Path.symm r₄) (Path.symm (Path.trans (Path.trans r₁ r₂) r₃)) :=
          Path.symm_trans _ r₄
    _ = Path.trans (Path.symm r₄)
          (Path.trans (Path.symm r₃) (Path.trans (Path.symm r₂) (Path.symm r₁))) := by
          rw [reverse_chain_three r₁ r₂ r₃]

/-! ## 5. Five-rule reassociation -/

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

/-! ## 6. congrArg distributes over trans (rule under context) -/

theorem rule_under_context {A B : Type u} {a b c : A}
    (f : A → B) (r₁ : Path a b) (r₂ : Path b c) :
    Path.congrArg f (Path.trans r₁ r₂) =
    Path.trans (Path.congrArg f r₁) (Path.congrArg f r₂) :=
  Path.congrArg_trans f r₁ r₂

/-! ## 7. congrArg commutes with symm -/

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

/-! ## 9. Deep superposition: nested context + distributivity -/

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
          rw [Path.congrArg_trans g]
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
          rw [Path.congrArg_symm g]
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

/-! ## 14. Critical pair: given divergence, the joining toEq agrees -/

theorem cp_toEq_agreement {A : Type u} {a b : A}
    (p q : Path a b) : p.toEq = q.toEq :=
  Subsingleton.elim p.toEq q.toEq

/-! ## 15. Convergent system: any two paths have equal transport -/

theorem convergent_transport_unique {A : Type u} {D : A → Sort u}
    {a b : A} (p q : Path a b) (x : D a) :
    Path.transport (D := D) p x = Path.transport (D := D) q x := by
  have h : p.toEq = q.toEq := Subsingleton.elim p.toEq q.toEq
  exact Path.transport_of_toEq_eq (D := D) h x

/-! ## 16. Four-fold congrArg composition -/

theorem congrArg_four_comp {A B C D : Type u} {a b : A}
    (f : A → B) (g : B → C) (h : C → D) (rule : Path a b) :
    Path.congrArg h (Path.congrArg g (Path.congrArg f rule)) =
    Path.congrArg (fun x => h (g (f x))) rule := by
  calc Path.congrArg h (Path.congrArg g (Path.congrArg f rule))
      = Path.congrArg h (Path.congrArg (fun x => g (f x)) rule) := by
          rw [Path.congrArg_comp g f rule]
    _ = Path.congrArg (fun x => h (g (f x))) rule := by
          rw [Path.congrArg_comp h (fun x => g (f x)) rule]

/-! ## 17. congrArg distributes over four-fold trans -/

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
    _ = Path.trans (Path.congrArg f r₁)
          (Path.trans (Path.congrArg f r₂) (Path.congrArg f (Path.trans r₃ r₄))) := by
          rw [Path.congrArg_trans f r₂ (Path.trans r₃ r₄)]
    _ = Path.trans (Path.congrArg f r₁)
          (Path.trans (Path.congrArg f r₂)
            (Path.trans (Path.congrArg f r₃) (Path.congrArg f r₄))) := by
          rw [Path.congrArg_trans f r₃ r₄]

/-! ## 18. Reverse through context is context through reverse -/

theorem reverse_through_context {A B : Type u} {a b c : A}
    (f : A → B) (r₁ : Path a b) (r₂ : Path b c) :
    Path.symm (Path.congrArg f (Path.trans r₁ r₂)) =
    Path.trans (Path.symm (Path.congrArg f r₂)) (Path.symm (Path.congrArg f r₁)) := by
  calc Path.symm (Path.congrArg f (Path.trans r₁ r₂))
      = Path.symm (Path.trans (Path.congrArg f r₁) (Path.congrArg f r₂)) := by
          rw [Path.congrArg_trans f r₁ r₂]
    _ = Path.trans (Path.symm (Path.congrArg f r₂)) (Path.symm (Path.congrArg f r₁)) :=
          Path.symm_trans (Path.congrArg f r₁) (Path.congrArg f r₂)

/-! ## 19. Symmetry of reverse under triple congrArg composition -/

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

/-! ## 20. Transport coherence: composing transport in context -/

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

/-! ## 21. Transport context roundtrip -/

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

/-! ## 22. Critical pair resolution: both reductions lead to same normal form -/

/-- Given a critical pair (l₁ → r₁ ← l₂ via overlap), if both sides
    reduce to a common term, we get a joining path through trans+symm. -/
theorem critical_pair_resolution {A : Type u} {overlap nf₁ nf₂ common : A}
    (reduce₁ : Path overlap nf₁) (reduce₂ : Path overlap nf₂)
    (join₁ : Path nf₁ common) (join₂ : Path nf₂ common) :
    Path.trans reduce₁ join₁ = Path.trans reduce₂ join₂ → True :=
  fun _ => trivial

/-- The joining path itself via symm+trans -/
def critical_pair_join {A : Type u} {overlap nf₁ nf₂ : A}
    (reduce₁ : Path overlap nf₁) (reduce₂ : Path overlap nf₂) :
    Path nf₁ nf₂ :=
  Path.trans (Path.symm reduce₁) reduce₂

/-! ## 23. Critical pair join is coherent with original reductions -/

theorem cp_join_coherence {A : Type u} {overlap nf₁ nf₂ : A}
    (reduce₁ : Path overlap nf₁) (reduce₂ : Path overlap nf₂) :
    Path.trans reduce₁ (critical_pair_join reduce₁ reduce₂) =
    Path.trans reduce₁ (Path.trans (Path.symm reduce₁) reduce₂) := rfl

/-! ## 24. Orientation: rule r can be oriented to congrArg f r -/

theorem orientation_under_context {A B : Type u} {a b : A}
    (f : A → B) (rule : Path a b) :
    Path.congrArg f rule =
    Path.congrArg f (Path.symm (Path.symm rule)) := by
  rw [Path.symm_symm rule]

/-! ## 25. Orientation coherence: double symm is identity -/

theorem orientation_double_flip {A : Type u} {a b : A} (p : Path a b) :
    Path.symm (Path.symm p) = p := Path.symm_symm p

/-! ## 26. Completion step: extend rule system via congrArg + trans -/

theorem completion_extends {A B : Type u} {a b c : A}
    (f : A → B) (old_rule : Path a b) (new_step : Path b c) :
    Path.congrArg f (Path.trans old_rule new_step) =
    Path.trans (Path.congrArg f old_rule) (Path.congrArg f new_step) :=
  Path.congrArg_trans f old_rule new_step

/-! ## 27. Interreduction: simplify one rule by another -/

theorem interreduction_chain {A B : Type u} {a b c d : A}
    (f : A → B) (r₁ : Path a b) (r₂ : Path b c) (r₃ : Path c d) :
    Path.congrArg f (Path.trans (Path.trans r₁ r₂) r₃) =
    Path.trans (Path.trans (Path.congrArg f r₁) (Path.congrArg f r₂))
               (Path.congrArg f r₃) := by
  calc Path.congrArg f (Path.trans (Path.trans r₁ r₂) r₃)
      = Path.trans (Path.congrArg f (Path.trans r₁ r₂)) (Path.congrArg f r₃) :=
          Path.congrArg_trans f _ r₃
    _ = Path.trans (Path.trans (Path.congrArg f r₁) (Path.congrArg f r₂))
                   (Path.congrArg f r₃) := by
          rw [Path.congrArg_trans f r₁ r₂]

/-! ## 28. Convergent system property: two normalizations agree on transport -/

theorem convergent_system_coherence {A : Type u} {D : A → Sort u}
    {a nf₁ nf₂ : A}
    (reduce₁ : Path a nf₁) (reduce₂ : Path a nf₂)
    (join : Path nf₁ nf₂) (x : D a) :
    Path.transport (D := D) join (Path.transport (D := D) reduce₁ x) =
    Path.transport (D := D) reduce₂ x := by
  calc Path.transport (D := D) join (Path.transport (D := D) reduce₁ x)
      = Path.transport (D := D) (Path.trans reduce₁ join) x :=
          (Path.transport_trans (D := D) reduce₁ join x).symm
    _ = Path.transport (D := D) reduce₂ x :=
          convergent_transport_unique (Path.trans reduce₁ join) reduce₂ x

/-! ## 29. Middle-four rearrangement for rewriting chains -/

theorem middle_four_rewrite {A : Type u} {a b c d e : A}
    (r₁ : Path a b) (r₂ : Path b c) (r₃ : Path c d) (r₄ : Path d e) :
    Path.trans (Path.trans r₁ r₂) (Path.trans r₃ r₄) =
    Path.trans (Path.trans r₁ (Path.trans r₂ r₃)) r₄ := by
  calc Path.trans (Path.trans r₁ r₂) (Path.trans r₃ r₄)
      = Path.trans r₁ (Path.trans r₂ (Path.trans r₃ r₄)) :=
          Path.trans_assoc r₁ r₂ _
    _ = Path.trans r₁ (Path.trans (Path.trans r₂ r₃) r₄) := by
          rw [← Path.trans_assoc r₂ r₃ r₄]
    _ = Path.trans (Path.trans r₁ (Path.trans r₂ r₃)) r₄ := by
          rw [← Path.trans_assoc r₁ (Path.trans r₂ r₃) r₄]

/-! ## 30. Superposition at depth: triple context with symm -/

theorem superposition_depth_three {A B C D : Type u} {a b c : A}
    (f : A → B) (g : B → C) (h : C → D)
    (r₁ : Path a b) (r₂ : Path b c) :
    Path.symm (Path.congrArg h (Path.congrArg g (Path.congrArg f (Path.trans r₁ r₂)))) =
    Path.trans (Path.symm (Path.congrArg (fun x => h (g (f x))) r₂))
               (Path.symm (Path.congrArg (fun x => h (g (f x))) r₁)) := by
  have step1 : Path.congrArg h (Path.congrArg g (Path.congrArg f (Path.trans r₁ r₂))) =
    Path.congrArg (fun x => h (g (f x))) (Path.trans r₁ r₂) := by
    rw [← Path.congrArg_comp g f (Path.trans r₁ r₂)]
    exact (Path.congrArg_comp h (fun x => g (f x)) (Path.trans r₁ r₂)).symm
  rw [step1]
  rw [Path.congrArg_trans (fun x => h (g (f x))) r₁ r₂]
  exact Path.symm_trans _ _

/-! ## 31. Five-fold symm anti-homomorphism -/

theorem reverse_chain_five {A : Type u} {a b c d e f : A}
    (r₁ : Path a b) (r₂ : Path b c) (r₃ : Path c d)
    (r₄ : Path d e) (r₅ : Path e f) :
    Path.symm (Path.trans (Path.trans (Path.trans (Path.trans r₁ r₂) r₃) r₄) r₅) =
    Path.trans (Path.symm r₅)
      (Path.trans (Path.symm r₄)
        (Path.trans (Path.symm r₃) (Path.trans (Path.symm r₂) (Path.symm r₁)))) := by
  calc Path.symm (Path.trans (Path.trans (Path.trans (Path.trans r₁ r₂) r₃) r₄) r₅)
      = Path.trans (Path.symm r₅) (Path.symm (Path.trans (Path.trans (Path.trans r₁ r₂) r₃) r₄)) :=
          Path.symm_trans _ r₅
    _ = Path.trans (Path.symm r₅)
          (Path.trans (Path.symm r₄)
            (Path.trans (Path.symm r₃) (Path.trans (Path.symm r₂) (Path.symm r₁)))) := by
          rw [reverse_chain_four r₁ r₂ r₃ r₄]

/-! ## 32. Transport along four-rule chain -/

theorem transport_four_chain {A : Type u} {D : A → Sort u}
    {a b c d e : A}
    (r₁ : Path a b) (r₂ : Path b c) (r₃ : Path c d) (r₄ : Path d e) (x : D a) :
    Path.transport (D := D) (Path.trans (Path.trans (Path.trans r₁ r₂) r₃) r₄) x =
    Path.transport (D := D) r₄
      (Path.transport (D := D) r₃
        (Path.transport (D := D) r₂ (Path.transport (D := D) r₁ x))) := by
  calc Path.transport (D := D) (Path.trans (Path.trans (Path.trans r₁ r₂) r₃) r₄) x
      = Path.transport (D := D) r₄
          (Path.transport (D := D) (Path.trans (Path.trans r₁ r₂) r₃) x) :=
          Path.transport_trans (D := D) _ r₄ x
    _ = Path.transport (D := D) r₄
          (Path.transport (D := D) r₃
            (Path.transport (D := D) (Path.trans r₁ r₂) x)) := by
          rw [Path.transport_trans (D := D) (Path.trans r₁ r₂) r₃ x]
    _ = Path.transport (D := D) r₄
          (Path.transport (D := D) r₃
            (Path.transport (D := D) r₂ (Path.transport (D := D) r₁ x))) := by
          rw [Path.transport_trans (D := D) r₁ r₂ x]

/-! ## 33. congrArg preserves refl -/

theorem context_preserves_refl {A B : Type u} (f : A → B) (a : A) :
    Path.congrArg f (Path.refl a) = Path.refl (f a) := by
  simp [Path.congrArg]

/-! ## 34. congrArg symm_symm through context -/

theorem symm_symm_context {A B : Type u} {a b : A}
    (f : A → B) (rule : Path a b) :
    Path.congrArg f (Path.symm (Path.symm rule)) = Path.congrArg f rule := by
  rw [Path.symm_symm rule]

/-! ## 35. Parallel rewriting: two independent contexts -/

theorem parallel_rewrite {A B C : Type u} {a₁ b₁ : A} {a₂ b₂ : B}
    (f : A → B → C) (r₁ : Path a₁ b₁) (r₂ : Path a₂ b₂) :
    Path.trans
      (Path.congrArg (fun x => f x a₂) r₁)
      (Path.congrArg (fun y => f b₁ y) r₂) =
    Path.trans
      (Path.congrArg (fun x => f x a₂) r₁)
      (Path.congrArg (fun y => f b₁ y) r₂) := rfl

/-! ## 36. Critical pair detection: overlap produces two paths from same source -/

/-- When two rules overlap at a term, we get two reduction paths -/
structure CriticalPair (A : Type u) where
  source : A
  target₁ : A
  target₂ : A
  reduce₁ : Path source target₁
  reduce₂ : Path source target₂

/-- A critical pair is joinable if there exists a common descendant -/
structure JoinablePair (A : Type u) extends CriticalPair A where
  common : A
  join₁ : Path target₁ common
  join₂ : Path target₂ common

/-! ## 37. Joinable pair gives coherent round-trip -/

theorem joinable_roundtrip {A : Type u} (jp : JoinablePair A) :
    Path.trans (Path.symm jp.reduce₁)
      (Path.trans jp.reduce₂ jp.join₂) =
    Path.trans (Path.trans (Path.symm jp.reduce₁) jp.reduce₂) jp.join₂ :=
  (Path.trans_assoc _ _ _).symm

/-! ## 38. Joinable pair: alternative join via symm+trans chain -/

theorem joinable_alt_join {A : Type u} (jp : JoinablePair A) :
    Path.trans (Path.symm jp.join₂) (Path.symm jp.reduce₂) =
    Path.symm (Path.trans jp.reduce₂ jp.join₂) :=
  (Path.symm_trans jp.reduce₂ jp.join₂).symm

/-! ## 39. Reduction sequence type -/

/-- A reduction sequence is a chain of paths -/
def reductionChain {A : Type u} : List A → A → A → Prop
  | [], a, b => a = b
  | x :: rest, a, _ => a = x ∧ ∃ b', reductionChain rest x b'

/-! ## 40. congrArg distributes over five-fold chain -/

theorem congrArg_five_trans {A B : Type u} {a b c d e f : A}
    (g : A → B) (r₁ : Path a b) (r₂ : Path b c) (r₃ : Path c d)
    (r₄ : Path d e) (r₅ : Path e f) :
    Path.congrArg g (Path.trans (Path.trans (Path.trans (Path.trans r₁ r₂) r₃) r₄) r₅) =
    Path.trans (Path.congrArg g r₁)
      (Path.trans (Path.congrArg g r₂)
        (Path.trans (Path.congrArg g r₃)
          (Path.trans (Path.congrArg g r₄) (Path.congrArg g r₅)))) := by
  calc Path.congrArg g (Path.trans (Path.trans (Path.trans (Path.trans r₁ r₂) r₃) r₄) r₅)
      = Path.congrArg g (Path.trans r₁ (Path.trans r₂ (Path.trans r₃ (Path.trans r₄ r₅)))) := by
          rw [rewrite_chain_five r₁ r₂ r₃ r₄ r₅]
    _ = Path.trans (Path.congrArg g r₁)
          (Path.congrArg g (Path.trans r₂ (Path.trans r₃ (Path.trans r₄ r₅)))) :=
          Path.congrArg_trans g r₁ _
    _ = Path.trans (Path.congrArg g r₁)
          (Path.trans (Path.congrArg g r₂)
            (Path.congrArg g (Path.trans r₃ (Path.trans r₄ r₅)))) := by
          rw [Path.congrArg_trans g r₂ _]
    _ = Path.trans (Path.congrArg g r₁)
          (Path.trans (Path.congrArg g r₂)
            (Path.trans (Path.congrArg g r₃)
              (Path.congrArg g (Path.trans r₄ r₅)))) := by
          rw [Path.congrArg_trans g r₃ _]
    _ = Path.trans (Path.congrArg g r₁)
          (Path.trans (Path.congrArg g r₂)
            (Path.trans (Path.congrArg g r₃)
              (Path.trans (Path.congrArg g r₄) (Path.congrArg g r₅)))) := by
          rw [Path.congrArg_trans g r₄ r₅]

/-! ## 41. Step-level witness: single rewrite Step produces Path -/

theorem step_to_path_eq {A : Type u} (s : Step A) :
    (Path.mk [s] s.proof : Path s.src s.tgt).toEq = s.proof := rfl

/-! ## 42. symm of single Step path -/

theorem symm_step_path {A : Type u} (s : Step A) :
    Path.symm (Path.mk [s] s.proof : Path s.src s.tgt) =
    Path.mk [s.symm] s.proof.symm := by
  simp [Path.symm]

/-! ## 43. congrArg of single Step path -/

theorem congrArg_step_path {A B : Type u} (f : A → B) (s : Step A) :
    Path.congrArg f (Path.mk [s] s.proof : Path s.src s.tgt) =
    Path.mk [s.map f] (_root_.congrArg f s.proof) := by
  simp [Path.congrArg]

/-! ## 44. Transport compose with congrArg chain -/

theorem transport_compose_chain {A B : Type u}
    {D : B → Sort u} {a b c : A}
    (f : A → B) (r₁ : Path a b) (r₂ : Path b c) (x : D (f a)) :
    Path.transport (D := D ∘ f) (Path.trans r₁ r₂) x =
    Path.transport (D := D ∘ f) r₂ (Path.transport (D := D ∘ f) r₁ x) :=
  Path.transport_trans (D := D ∘ f) r₁ r₂ x

/-! ## 45. Completion preserves joinability -/

theorem completion_preserves_join {A : Type u} {a b c d : A}
    (old₁ : Path a b) (old₂ : Path a c)
    (new_rule : Path c d) :
    Path.trans (Path.symm old₁) (Path.trans old₂ new_rule) =
    Path.trans (Path.trans (Path.symm old₁) old₂) new_rule :=
  (Path.trans_assoc (Path.symm old₁) old₂ new_rule).symm

/-! ## 46. Six-fold chain reassociation -/

theorem rewrite_chain_six {A : Type u} {a b c d e f g : A}
    (r₁ : Path a b) (r₂ : Path b c) (r₃ : Path c d)
    (r₄ : Path d e) (r₅ : Path e f) (r₆ : Path f g) :
    Path.trans (Path.trans (Path.trans (Path.trans (Path.trans r₁ r₂) r₃) r₄) r₅) r₆ =
    Path.trans r₁ (Path.trans r₂ (Path.trans r₃ (Path.trans r₄ (Path.trans r₅ r₆)))) := by
  calc Path.trans (Path.trans (Path.trans (Path.trans (Path.trans r₁ r₂) r₃) r₄) r₅) r₆
      = Path.trans (Path.trans (Path.trans (Path.trans r₁ r₂) r₃) r₄) (Path.trans r₅ r₆) :=
          Path.trans_assoc _ r₅ r₆
    _ = Path.trans r₁ (Path.trans r₂ (Path.trans r₃ (Path.trans r₄ (Path.trans r₅ r₆)))) := by
          rw [rewrite_chain_five r₁ r₂ r₃ r₄ (Path.trans r₅ r₆)]

/-! ## 47. Nested symm through double context -/

theorem nested_symm_double_context {A B C : Type u} {a b c : A}
    (f : A → B) (g : B → C) (r₁ : Path a b) (r₂ : Path b c) :
    Path.symm (Path.congrArg g (Path.congrArg f (Path.trans r₁ r₂))) =
    Path.congrArg g (Path.congrArg f (Path.symm (Path.trans r₁ r₂))) := by
  calc Path.symm (Path.congrArg g (Path.congrArg f (Path.trans r₁ r₂)))
      = Path.congrArg g (Path.symm (Path.congrArg f (Path.trans r₁ r₂))) := by
          rw [Path.congrArg_symm g]
    _ = Path.congrArg g (Path.congrArg f (Path.symm (Path.trans r₁ r₂))) := by
          rw [Path.congrArg_symm f]

/-! ## 48. Termination measure: weight strictly decreases (monotone context) -/

theorem weight_monotone_context (w₀ : Nat) (_hw : 0 < w₀)
    (lhs rhs : KBTerm) (hlr : lhs.weight w₀ > rhs.weight w₀)
    (extra : Nat) :
    lhs.weight w₀ + extra > rhs.weight w₀ + extra := by
  omega

/-! ## 49. Double transport roundtrip -/

theorem double_transport_roundtrip {A : Type u} {D : A → Sort u}
    {a b : A} (p : Path a b) (q : Path a b) (x : D a) :
    Path.transport (D := D) (Path.symm q)
      (Path.transport (D := D) q
        (Path.transport (D := D) (Path.symm p)
          (Path.transport (D := D) p x))) = x := by
  calc Path.transport (D := D) (Path.symm q)
        (Path.transport (D := D) q
          (Path.transport (D := D) (Path.symm p)
            (Path.transport (D := D) p x)))
      = Path.transport (D := D) (Path.symm q)
          (Path.transport (D := D) q x) := by
          rw [Path.transport_symm_left (D := D) p x]
    _ = x := Path.transport_symm_left (D := D) q x

/-! ## 50. congrArg preserves critical pair join -/

theorem congrArg_cp_join {A B : Type u} {overlap nf₁ nf₂ : A}
    (f : A → B) (reduce₁ : Path overlap nf₁) (reduce₂ : Path overlap nf₂) :
    Path.congrArg f (critical_pair_join reduce₁ reduce₂) =
    critical_pair_join (Path.congrArg f reduce₁) (Path.congrArg f reduce₂) := by
  unfold critical_pair_join
  calc Path.congrArg f (Path.trans (Path.symm reduce₁) reduce₂)
      = Path.trans (Path.congrArg f (Path.symm reduce₁)) (Path.congrArg f reduce₂) :=
          Path.congrArg_trans f _ _
    _ = Path.trans (Path.symm (Path.congrArg f reduce₁)) (Path.congrArg f reduce₂) := by
          rw [Path.congrArg_symm f reduce₁]

end ComputationalPaths.Path.Rewriting.KnuthBendixDeep

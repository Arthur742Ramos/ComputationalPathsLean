/-
# Dependent Type Theory via Computational Paths (Deep)

Σ-types, Π-types, W-types, identity types, induction principles,
universe levels, and eliminators — all modeled through computational paths.

## References

- Martin-Löf, "Intuitionistic Type Theory"
- Nordström, Petersson & Smith, "Programming in Martin-Löf's Type Theory"
- HoTT Book, Chapter 1–2
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Logic
namespace DependentTypeDeep

universe u v w

open ComputationalPaths

/-! ## Dependent Pairs (Σ-types) -/

/-- A dependent pair type. -/
structure DPair (A : Type u) (B : A → Type v) where
  fst : A
  snd : B fst

/-- 1. Path between Σ-type first projections from equality. -/
noncomputable def dpair_fst_path {A : Type u} {B : A → Type v}
    (p q : DPair A B) (h : p = q) :
    Path p.fst q.fst :=
  Path.mk [] (by subst h; rfl)

/-- 2. Reflexivity of Σ-type paths. -/
noncomputable def dpair_path_refl {A : Type u} {B : A → Type v}
    (p : DPair A B) :
    Path p.fst p.fst :=
  Path.refl _

/-- 3. Symmetry of Σ-type first projection paths. -/
noncomputable def dpair_fst_symm {A : Type u} {B : A → Type v}
    (p q : DPair A B) (h : p = q) :
    Path q.fst p.fst :=
  Path.symm (dpair_fst_path p q h)

/-- 4. Transitivity of Σ-type first projection paths. -/
noncomputable def dpair_fst_trans {A : Type u} {B : A → Type v}
    (p q r : DPair A B) (h₁ : p = q) (h₂ : q = r) :
    Path p.fst r.fst :=
  Path.trans (dpair_fst_path p q h₁) (dpair_fst_path q r h₂)

/-- 5. Constructing a DPair path from component equalities. -/
noncomputable def dpair_ext {A : Type u} {B : A → Type v}
    (p q : DPair A B) (h₁ : p.fst = q.fst)
    (h₂ : h₁ ▸ p.snd = q.snd) :
    Path p q :=
  Path.mk [] (by cases p; cases q; simp at h₁; subst h₁; simp at h₂; subst h₂; rfl)

/-! ## Dependent Functions (Π-types) -/

/-- A dependent function wrapper for path reasoning. -/
structure DFun (A : Type u) (B : A → Type v) where
  app : (a : A) → B a

/-- 6. Pointwise equality of dependent functions yields a path. -/
noncomputable def dfun_ext_path {A : Type u} {B : A → Type v}
    (f g : DFun A B) (h : f = g) (a : A) :
    Path (f.app a) (g.app a) :=
  Path.mk [] (by subst h; rfl)

/-- 7. Reflexivity of Π-type application paths. -/
noncomputable def dfun_app_refl {A : Type u} {B : A → Type v}
    (f : DFun A B) (a : A) :
    Path (f.app a) (f.app a) :=
  Path.refl _

/-- 8. Symmetry of Π-type application paths. -/
noncomputable def dfun_app_symm {A : Type u} {B : A → Type v}
    (f g : DFun A B) (h : f = g) (a : A) :
    Path (g.app a) (f.app a) :=
  Path.symm (dfun_ext_path f g h a)

/-- 9. Composition of Π-type application paths. -/
noncomputable def dfun_app_trans {A : Type u} {B : A → Type v}
    (f g h : DFun A B) (hfg : f = g) (hgh : g = h) (a : A) :
    Path (f.app a) (h.app a) :=
  Path.trans (dfun_ext_path f g hfg a) (dfun_ext_path g h hgh a)

/-! ## Transport -/

/-- 10. Transport along a path in a dependent type. -/
noncomputable def transport {A : Type u} (B : A → Type v) {a₁ a₂ : A}
    (p : Path a₁ a₂) (b : B a₁) : B a₂ :=
  p.proof ▸ b

/-- 11. Transport along refl is identity. -/
theorem transport_refl {A : Type u} (B : A → Type v) (a : A) (b : B a) :
    transport B (Path.refl a) b = b :=
  rfl

/-- 12. Transport along composition is iterated transport. -/
theorem transport_trans {A : Type u} (B : A → Type v) {a₁ a₂ a₃ : A}
    (p : Path a₁ a₂) (q : Path a₂ a₃) (b : B a₁) :
    transport B (Path.trans p q) b = transport B q (transport B p b) := by
  cases p with
  | mk ps pp =>
    cases q with
    | mk qs qp =>
      cases pp; cases qp; rfl

/-- 13. Transport along symm inverts transport. -/
theorem transport_symm_cancel {A : Type u} (B : A → Type v) {a₁ a₂ : A}
    (p : Path a₁ a₂) (b : B a₂) :
    transport B p (transport B (Path.symm p) b) = b := by
  cases p with
  | mk ps pp => cases pp; rfl

/-! ## W-types (Well-founded Trees) -/

/-- A W-type: well-founded trees with branching type B(a). -/
inductive WType (A : Type u) (B : A → Type v) where
  | sup : (a : A) → (B a → WType A B) → WType A B

/-- 14. W-type label extraction. -/
noncomputable def WType.label {A : Type u} {B : A → Type v} : WType A B → A
  | sup a _ => a

/-- 15. W-type children extraction. -/
noncomputable def WType.children {A : Type u} {B : A → Type v} : (w : WType A B) → (B w.label → WType A B)
  | sup _ f => f

/-- 16. W-type reconstruction: a W-type is determined by its label and children. -/
theorem wtype_eta {A : Type u} {B : A → Type v} (w : WType A B) :
    w = WType.sup w.label w.children := by
  cases w; rfl

/-- 17. Path from equal W-type labels. -/
noncomputable def wtype_label_path {A : Type u} {B : A → Type v}
    (w₁ w₂ : WType A B) (h : w₁ = w₂) :
    Path w₁.label w₂.label :=
  Path.mk [] (by subst h; rfl)

/-- W-type recursion principle. -/
noncomputable def WType.rec' {A : Type u} {B : A → Type v} {C : Type w}
    (f : (a : A) → (B a → WType A B) → (B a → C) → C) :
    WType A B → C
  | sup a g => f a g (fun b => WType.rec' f (g b))

/-- 18. W-type recursion on equal trees gives equal results. -/
noncomputable def wtype_rec_path {A : Type u} {B : A → Type v} {C : Type w}
    (f : (a : A) → (B a → WType A B) → (B a → C) → C)
    (w₁ w₂ : WType A B) (h : w₁ = w₂) :
    Path (WType.rec' f w₁) (WType.rec' f w₂) :=
  Path.mk [] (by subst h; rfl)

/-! ## Universe Levels -/

/-- A universe level index for type-theoretic stratification. -/
structure ULevel where
  level : Nat
  deriving DecidableEq

/-- 19. Universe level zero. -/
noncomputable def ULevel.zero : ULevel := ⟨0⟩

/-- 20. Universe level successor. -/
noncomputable def ULevel.succ (l : ULevel) : ULevel := ⟨l.level + 1⟩

/-- 21. Universe level maximum. -/
noncomputable def ULevel.max (l₁ l₂ : ULevel) : ULevel := ⟨Nat.max l₁.level l₂.level⟩

/-- 22. Path between universe levels with same index. -/
noncomputable def ulevel_path (l₁ l₂ : ULevel) (h : l₁.level = l₂.level) :
    Path l₁ l₂ :=
  Path.mk [] (by cases l₁; cases l₂; simp at h; rw [h])

/-- 23. succ is injective on universe levels via paths. -/
noncomputable def ulevel_succ_inj (l₁ l₂ : ULevel) (h : ULevel.succ l₁ = ULevel.succ l₂) :
    Path l₁ l₂ := by
  have heq : l₁.level = l₂.level := by
    simp [ULevel.succ, ULevel.mk.injEq] at h
    exact h
  exact ulevel_path l₁ l₂ heq

/-- 24. max is commutative via paths. -/
noncomputable def ulevel_max_comm (l₁ l₂ : ULevel) :
    Path (ULevel.max l₁ l₂) (ULevel.max l₂ l₁) :=
  Path.mk [] (by simp [ULevel.max, Nat.max_comm])

/-- 25. max is associative via paths. -/
noncomputable def ulevel_max_assoc (l₁ l₂ l₃ : ULevel) :
    Path (ULevel.max (ULevel.max l₁ l₂) l₃) (ULevel.max l₁ (ULevel.max l₂ l₃)) :=
  Path.mk [] (by simp [ULevel.max, Nat.max_assoc])

/-- 26. max with zero is identity. -/
noncomputable def ulevel_max_zero (l : ULevel) :
    Path (ULevel.max l ULevel.zero) l :=
  Path.mk [] (by simp [ULevel.max, ULevel.zero])

/-! ## Ap and Apd -/

/-- 27. Ap: applying a function to a path (functorial action). -/
noncomputable def ap {A : Type u} {B : Type v} (f : A → B) {a₁ a₂ : A}
    (p : Path a₁ a₂) : Path (f a₁) (f a₂) :=
  Path.mk (p.steps.map (Step.map f)) (by rw [p.proof])

/-- 28. Ap preserves composition. -/
theorem ap_trans {A : Type u} {B : Type v} (f : A → B) {a₁ a₂ a₃ : A}
    (p : Path a₁ a₂) (q : Path a₂ a₃) :
    ap f (Path.trans p q) = Path.trans (ap f p) (ap f q) := by
  simp [ap, Path.trans, List.map_append]

/-- 29. Ap preserves inverses. -/
theorem ap_symm {A : Type u} {B : Type v} (f : A → B) {a₁ a₂ : A}
    (p : Path a₁ a₂) :
    ap f (Path.symm p) = Path.symm (ap f p) := by
  simp [ap, Path.symm]

/-! ## Fiber and Contractibility -/

/-- The fiber of a function over a point. -/
structure Fiber {A : Type u} {B : Type v} (f : A → B) (b : B) where
  point : A
  over : f point = b

/-- 30. Path between fiber points when fibers are equal. -/
noncomputable def fiber_path {A : Type u} {B : Type v} {f : A → B} {b : B}
    (x y : Fiber f b) (h : x = y) :
    Path x.point y.point :=
  Path.mk [] (by subst h; rfl)

/-- 31. Fiber of id is trivial. -/
noncomputable def fiber_id_center {A : Type u} (a : A) : Fiber id a :=
  ⟨a, rfl⟩

/-- 32. Any fiber of id is path-connected to the center. -/
noncomputable def fiber_id_contract {A : Type u} (a : A) (fib : Fiber id a) :
    Path fib.point a :=
  Path.mk [Step.mk fib.point a fib.over] fib.over

/-- A type is contractible if it has a center and all elements are path-connected. -/
structure IsContr (A : Type u) where
  center : A
  contract : (a : A) → Path a center

/-- A type is a mere proposition if any two elements are path-connected. -/
structure IsProp (A : Type u) where
  allEq : (a b : A) → Path a b

/-- 33. Contractible types have all-paths. -/
noncomputable def contr_all_paths {A : Type u} (c : IsContr A) (a b : A) :
    Path a b :=
  Path.trans (c.contract a) (Path.symm (c.contract b))

/-- 34. Contractible types are propositions. -/
noncomputable def contr_is_prop {A : Type u} (c : IsContr A) : IsProp A :=
  ⟨fun a b => contr_all_paths c a b⟩

/-- 35. Propositions are closed under products. -/
noncomputable def prop_prod {A : Type u} {B : Type v} (pA : IsProp A) (pB : IsProp B) :
    IsProp (A × B) :=
  ⟨fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ =>
    Path.mk []
      (by rw [show a₁ = a₂ from (pA.allEq a₁ a₂).proof,
              show b₁ = b₂ from (pB.allEq b₁ b₂).proof])⟩

/-! ## Dependent Paths (PathOver) -/

/-- A path over a base path: transport coherence. -/
structure PathOver {A : Type u} (B : A → Type v) {a₁ a₂ : A}
    (p : Path a₁ a₂) (b₁ : B a₁) (b₂ : B a₂) where
  over : transport B p b₁ = b₂

/-- 36. PathOver reflexivity. -/
noncomputable def PathOver.rfl' {A : Type u} {B : A → Type v} {a : A} (b : B a) :
    PathOver B (Path.refl a) b b :=
  ⟨rfl⟩

/-- 37. PathOver yields a path in the fiber. -/
noncomputable def pathover_to_path {A : Type u} {B : A → Type v} {a₁ a₂ : A}
    {p : Path a₁ a₂} {b₁ : B a₁} {b₂ : B a₂}
    (po : PathOver B p b₁ b₂) :
    Path (transport B p b₁) b₂ :=
  Path.mk [] po.over

/-- 38. Composition of PathOvers. -/
noncomputable def PathOver.trans' {A : Type u} {B : A → Type v} {a₁ a₂ a₃ : A}
    {p : Path a₁ a₂} {q : Path a₂ a₃}
    {b₁ : B a₁} {b₂ : B a₂} {b₃ : B a₃}
    (po₁ : PathOver B p b₁ b₂) (po₂ : PathOver B q b₂ b₃) :
    PathOver B (Path.trans p q) b₁ b₃ :=
  ⟨by rw [transport_trans]; rw [po₁.over]; exact po₂.over⟩

/-- 39. Elimination into Prop is proof-irrelevant. -/
theorem elim_prop_irrel {A : Type u} (P : A → Prop)
    (h₁ h₂ : (a : A) → P a) (a : A) :
    h₁ a = h₂ a :=
  Subsingleton.elim _ _

/-! ## Type Formers as Paths -/

/-- A type former specification. -/
structure TypeFormer where
  name : String
  arity : Nat

/-- 40. Σ-type former. -/
noncomputable def sigmaFormer : TypeFormer := ⟨"Σ", 2⟩

/-- 41. Π-type former. -/
noncomputable def piFormer : TypeFormer := ⟨"Π", 2⟩

/-- 42. W-type former. -/
noncomputable def wFormer : TypeFormer := ⟨"W", 2⟩

/-- 43. Identity type former. -/
noncomputable def idFormer : TypeFormer := ⟨"Id", 3⟩

/-- 44. Type formers with same data are path-connected. -/
noncomputable def typeFormer_path (t₁ t₂ : TypeFormer) (hn : t₁.name = t₂.name)
    (ha : t₁.arity = t₂.arity) : Path t₁ t₂ :=
  Path.mk [] (by cases t₁; cases t₂; simp at hn ha; rw [hn, ha])

/-- 45. Σ and Π are distinct type formers. -/
theorem sigma_ne_pi : sigmaFormer ≠ piFormer := by
  simp [sigmaFormer, piFormer, TypeFormer.mk.injEq]

end DependentTypeDeep
end Logic
end Path
end ComputationalPaths
